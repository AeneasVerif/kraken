module

public import LeanQbe.T.Gvn
public import LeanQbe.T.FoldLemmas

/-!
# Correctness of lexical GVN / CSE (`T6`)

* `OpCode.wp_self`: any satisfied `OpCode.wp` delivers outputs that satisfy every other valid
  postcondition of the same opcode & operands (handling deterministic ops, UB `False`, and
  nondeterministic IEEE float NaNs uniformly).
* `gvn_wp`: source `wp` implies GVN-optimized `wp`, proved via `Wf.induct`.
* `gvn_wf`: `Wf` is preserved, proved via `Wf.induct`.
* `Func.gvn_spec`, `Func.gvn_wf`: closed-function specifications.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## Universal self-characterization `OpCode.wp_self` -/

theorem floatResultWp_self (f : Fmt) (res : Float.Model.UnpackedFloat)
    {P : BitVec f.width → Prop} (hw : floatResultWp f res P) :
    floatResultWp f res (fun r => P r ∧ ∀ Q, floatResultWp f res Q → Q r) := by
  unfold floatResultWp at hw ⊢
  split at hw
  · next hnan =>
    simp only [hnan, ↓reduceIte]
    exact fun r hr => ⟨hw r hr, fun Q hQ => hQ r hr⟩
  · next hnan =>
    simp only [hnan, Bool.false_eq_true, ↓reduceIte] at hw ⊢
    exact ⟨hw, fun Q hQ => hQ⟩

theorem liftFloatRel1_self
    (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat) :
    ∀ (t : Ty) (a : Val t) (P : Val t → Prop),
      liftFloatRel1 op t a P →
      liftFloatRel1 op t a (fun r => P r ∧ ∀ Q, liftFloatRel1 op t a Q → Q r)
  | .float f, a, P, hw => floatResultWp_self f (op f.format (unpackFloat f a)) hw
  | .bool, _, _, hw => False.elim hw
  | .bits _, _, _, hw => False.elim hw
  | .pair s u, (a₁, a₂), P, hw => by
    simp only [liftFloatRel1] at hw ⊢
    have h1 := liftFloatRel1_self op s a₁ _ hw
    refine liftFloatRel1_mono op s a₁ _ _ (fun r₁ hr₁ => ?_) h1
    have h2 := liftFloatRel1_self op u a₂ _ hr₁.1
    refine liftFloatRel1_mono op u a₂ _ _ (fun r₂ hr₂ => ?_) h2
    refine ⟨hr₂.1, fun Q hQ => ?_⟩
    exact hr₂.2 (fun y => Q (r₁, y)) (hr₁.2 (fun x => liftFloatRel1 op u a₂ fun y => Q (x, y)) hQ)

theorem liftFloatRel2_self
    (op : Float.Model.Format → Float.Model.UnpackedFloat →
      Float.Model.UnpackedFloat → Float.Model.UnpackedFloat) :
    ∀ (t : Ty) (a b : Val t) (P : Val t → Prop),
      liftFloatRel2 op t a b P →
      liftFloatRel2 op t a b (fun r => P r ∧ ∀ Q, liftFloatRel2 op t a b Q → Q r)
  | .float f, a, b, P, hw =>
    floatResultWp_self f (op f.format (unpackFloat f a) (unpackFloat f b)) hw
  | .bool, _, _, _, hw => False.elim hw
  | .bits _, _, _, _, hw => False.elim hw
  | .pair s u, (a₁, a₂), (b₁, b₂), P, hw => by
    simp only [liftFloatRel2] at hw ⊢
    have h1 := liftFloatRel2_self op s a₁ b₁ _ hw
    refine liftFloatRel2_mono op s a₁ b₁ _ _ (fun r₁ hr₁ => ?_) h1
    have h2 := liftFloatRel2_self op u a₂ b₂ _ hr₁.1
    refine liftFloatRel2_mono op u a₂ b₂ _ _ (fun r₂ hr₂ => ?_) h2
    refine ⟨hr₂.1, fun Q hQ => ?_⟩
    exact hr₂.2 (fun y => Q (r₁, y))
      (hr₁.2 (fun x => liftFloatRel2 op u a₂ b₂ fun y => Q (x, y)) hQ)

theorem liftFloatRel3_self
    (op : Float.Model.Format → Float.Model.UnpackedFloat →
      Float.Model.UnpackedFloat → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat) :
    ∀ (t : Ty) (a b c : Val t) (P : Val t → Prop),
      liftFloatRel3 op t a b c P →
      liftFloatRel3 op t a b c (fun r => P r ∧ ∀ Q, liftFloatRel3 op t a b c Q → Q r)
  | .float f, a, b, c, P, hw =>
    floatResultWp_self f (op f.format (unpackFloat f a) (unpackFloat f b) (unpackFloat f c)) hw
  | .bool, _, _, _, _, hw => False.elim hw
  | .bits _, _, _, _, _, hw => False.elim hw
  | .pair s u, (a₁, a₂), (b₁, b₂), (c₁, c₂), P, hw => by
    simp only [liftFloatRel3] at hw ⊢
    have h1 := liftFloatRel3_self op s a₁ b₁ c₁ _ hw
    refine liftFloatRel3_mono op s a₁ b₁ c₁ _ _ (fun r₁ hr₁ => ?_) h1
    have h2 := liftFloatRel3_self op u a₂ b₂ c₂ _ hr₁.1
    refine liftFloatRel3_mono op u a₂ b₂ c₂ _ _ (fun r₂ hr₂ => ?_) h2
    refine ⟨hr₂.1, fun Q hQ => ?_⟩
    exact hr₂.2 (fun y => Q (r₁, y))
      (hr₁.2 (fun x => liftFloatRel3 op u a₂ b₂ c₂ fun y => Q (x, y)) hQ)

theorem convertFloat_self (src dst : Fmt) (b : BitVec src.width)
    {P : BitVec dst.width → Prop} (hw : convertFloat src dst b P) :
    convertFloat src dst b (fun r => P r ∧ ∀ Q, convertFloat src dst b Q → Q r) := by
  unfold convertFloat at hw ⊢
  cases hu : unpackFloat src b with
  | notANumber =>
    simp only [hu] at hw ⊢
    exact fun r hr => ⟨hw r hr, fun Q hQ => hQ r hr⟩
  | finite _ _ _ _ =>
    simp only [hu] at hw ⊢
    exact ⟨hw, fun Q hQ => hQ⟩
  | infinity _ =>
    simp only [hu] at hw ⊢
    exact ⟨hw, fun Q hQ => hQ⟩
  | zero _ =>
    simp only [hu] at hw ⊢
    exact ⟨hw, fun Q hQ => hQ⟩

private theorem cond_false_self {b : Bool} {rs : List Ty} {r : Tup Val rs}
    (P : Tup Val rs → Prop) (hw : if b then False else P r) :
    if b then False else (P r ∧ ∀ Q : Tup Val rs → Prop, (if b then False else Q r) → Q r) := by
  cases b
  · exact ⟨hw, fun _ hQ => hQ⟩
  · exact False.elim hw

private theorem cond_and_self {c : Prop} {rs : List Ty} {r : Tup Val rs}
    (P : Tup Val rs → Prop) (hw : c ∧ P r) :
    c ∧ P r ∧ ∀ Q : Tup Val rs → Prop, (c ∧ Q r) → Q r :=
  ⟨hw.1, hw.2, fun _ hQ => hQ.2⟩

private theorem cond2_and_self {c₁ c₂ : Prop} {rs : List Ty} {r : Tup Val rs}
    (P : Tup Val rs → Prop) (hw : c₁ ∧ c₂ ∧ P r) :
    c₁ ∧ c₂ ∧ P r ∧ ∀ Q : Tup Val rs → Prop, (c₁ ∧ c₂ ∧ Q r) → Q r :=
  ⟨hw.1, hw.2.1, hw.2.2, fun _ hQ => hQ.2.2⟩

/-- Any satisfied `OpCode.wp` witnesses outputs satisfying every other valid postcondition `Q`. -/
theorem OpCode.wp_self : {sig rs : List Ty} → (c : OpCode sig rs) → (args : Tup Val sig) →
    {P : Tup Val rs → Prop} →
    c.wp args P → c.wp args (fun r => P r ∧ ∀ Q, c.wp args Q → Q r)
  | _, _, .copy _, (_, ()), _, hw => ⟨hw, fun _ hQ => hQ⟩
  | _, _, .add _, (_, _, ()), P, hw => by
    simp only [OpCode.wp_add] at hw ⊢; exact cond_false_self P hw
  | _, _, .sub _, (_, _, ()), P, hw => by
    simp only [OpCode.wp_sub] at hw ⊢; exact cond_false_self P hw
  | _, _, .mul _, (_, _, ()), P, hw => by
    simp only [OpCode.wp_mul] at hw ⊢; exact cond_false_self P hw
  | _, _, .neg _, (_, ()), P, hw => by
    simp only [OpCode.wp_neg] at hw ⊢; exact cond_false_self P hw
  | _, _, .and _, (_, _, ()), _, hw => ⟨hw, fun _ hQ => hQ⟩
  | _, _, .or _, (_, _, ()), _, hw => ⟨hw, fun _ hQ => hQ⟩
  | _, _, .xor _, (_, _, ()), _, hw => ⟨hw, fun _ hQ => hQ⟩
  | _, _, .not _, (_, ()), _, hw => ⟨hw, fun _ hQ => hQ⟩
  | _, _, .ternlog _ _, (_, _, _, ()), _, hw => ⟨hw, fun _ hQ => hQ⟩
  | _, _, .shl _, (_, _, ()), P, hw => by
    simp only [OpCode.wp_shl] at hw ⊢; exact cond_false_self P hw
  | _, _, .lshr _, (_, _, ()), P, hw => by
    simp only [OpCode.wp_lshr] at hw ⊢; exact cond_false_self P hw
  | _, _, .ashr _, (_, _, ()), P, hw => by
    simp only [OpCode.wp_ashr] at hw ⊢; exact cond_false_self P hw
  | _, _, .rotl _, (_, _, ()), P, hw => by
    simp only [OpCode.wp_rotl] at hw ⊢; exact cond_false_self P hw
  | _, _, .rotr _, (_, _, ()), P, hw => by
    simp only [OpCode.wp_rotr] at hw ⊢; exact cond_false_self P hw
  | _, _, .fshl _, (_, _, _, ()), _, hw => ⟨hw, fun _ hQ => hQ⟩
  | _, _, .fshr _, (_, _, _, ()), _, hw => ⟨hw, fun _ hQ => hQ⟩
  | _, _, .bswap _, (_, ()), P, hw => by
    simp only [OpCode.wp_bswap] at hw ⊢; exact cond_false_self P hw
  | _, _, .clz _, (_, ()), _, hw => ⟨hw, fun _ hQ => hQ⟩
  | _, _, .cls _, (_, ()), _, hw => ⟨hw, fun _ hQ => hQ⟩
  | _, _, .rbit _, (_, ()), _, hw => ⟨hw, fun _ hQ => hQ⟩
  | _, _, .ctz _, (_, ()), _, hw => ⟨hw, fun _ hQ => hQ⟩
  | _, _, .popcnt _, (_, ()), _, hw => ⟨hw, fun _ hQ => hQ⟩
  | _, _, .cmp _ _ _ rfl, (_, _, ()), P, hw => by
    simp only [OpCode.wp_cmp, cast_eq] at hw ⊢; exact cond_false_self P hw
  | _, _, .select _, (_, _, _, ()), _, hw => ⟨hw, fun _ hQ => hQ⟩
  | _, _, .blend _ _ rfl, (_, _, _, ()), _, hw => ⟨hw, fun _ hQ => hQ⟩
  | _, _, .zext _ _, (_, ()), P, hw => by
    simp only [OpCode.wp_zext] at hw ⊢; exact cond_and_self P hw
  | _, _, .sext _ _, (_, ()), P, hw => by
    simp only [OpCode.wp_sext] at hw ⊢; exact cond_and_self P hw
  | _, _, .trunc _ _, (_, ()), P, hw => by
    simp only [OpCode.wp_trunc] at hw ⊢; exact cond_and_self P hw
  | _, _, .ofBool _, (_, ()), _, hw => ⟨hw, fun _ hQ => hQ⟩
  | _, _, .addc _, (_, _, _, ()), _, hw => ⟨hw, fun _ hQ => hQ⟩
  | _, _, .subb _, (_, _, _, ()), _, hw => ⟨hw, fun _ hQ => hQ⟩
  | _, _, .umulw _, (_, _, ()), _, hw => ⟨hw, fun _ hQ => hQ⟩
  | _, _, .smulw _, (_, _, ()), _, hw => ⟨hw, fun _ hQ => hQ⟩
  | _, _, .udiv _, (_, _, ()), P, hw => by
    simp only [OpCode.wp_udiv] at hw ⊢; exact cond_and_self P hw
  | _, _, .sdiv _, (_, _, ()), P, hw => by
    simp only [OpCode.wp_sdiv] at hw ⊢; exact cond_and_self P hw
  | _, _, .urem _, (_, _, ()), P, hw => by
    simp only [OpCode.wp_urem] at hw ⊢; exact cond_and_self P hw
  | _, _, .srem _, (_, _, ()), P, hw => by
    simp only [OpCode.wp_srem] at hw ⊢; exact cond_and_self P hw
  | _, _, .udiv0 _, (_, _, ()), _, hw => ⟨hw, fun _ hQ => hQ⟩
  | _, _, .sdiv0 _, (_, _, ()), _, hw => ⟨hw, fun _ hQ => hQ⟩
  | _, _, .mkpair _ _, (_, _, ()), _, hw => ⟨hw, fun _ hQ => hQ⟩
  | _, _, .unpair _ _, (_, ()), _, hw => ⟨hw, fun _ hQ => hQ⟩
  | _, _, .bitcast _ _ _, (_, ()), _, hw => ⟨hw, fun _ hQ => hQ⟩
  | _, _, .shufd _ _, (_, ()), P, hw => by
    simp only [OpCode.wp_shufd] at hw ⊢; exact cond2_and_self P hw
  | _, _, .shufb _, (_, _, ()), P, hw => by
    simp only [OpCode.wp_shufb] at hw ⊢; exact cond2_and_self P hw
  | _, _, .alignr _ _, (_, _, ()), P, hw => by
    simp only [OpCode.wp_alignr] at hw ⊢; exact cond2_and_self P hw
  | _, _, .blendw _ _, (_, _, ()), P, hw => by
    simp only [OpCode.wp_blendw] at hw ⊢; exact cond2_and_self P hw
  | _, _, .sha256rnds2, (_, _, _, ()), _, hw => ⟨hw, fun _ hQ => hQ⟩
  | _, _, .sha256msg1, (_, _, ()), _, hw => ⟨hw, fun _ hQ => hQ⟩
  | _, _, .sha256msg2, (_, _, ()), _, hw => ⟨hw, fun _ hQ => hQ⟩
  | _, _, .fadd t, (a, b, ()), P, hw => by
    simp only [OpCode.wp_fadd] at hw ⊢
    cases ht : t.isFloatTree
    · simp only [ht, Bool.not_false, ↓reduceIte] at hw
    · simp only [ht, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw ⊢
      have h1 := liftFloatRel2_self Float.Model.UnpackedFloat.add t a b (fun r => P (r, ())) hw
      refine liftFloatRel2_mono Float.Model.UnpackedFloat.add t a b _ _ (fun r hr => ?_) h1
      exact ⟨hr.1, fun Q hQ => hr.2 (fun x => Q (x, ())) hQ⟩
  | _, _, .fsub t, (a, b, ()), P, hw => by
    simp only [OpCode.wp_fsub] at hw ⊢
    cases ht : t.isFloatTree
    · simp only [ht, Bool.not_false, ↓reduceIte] at hw
    · simp only [ht, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw ⊢
      have h1 := liftFloatRel2_self Float.Model.UnpackedFloat.sub t a b (fun r => P (r, ())) hw
      refine liftFloatRel2_mono Float.Model.UnpackedFloat.sub t a b _ _ (fun r hr => ?_) h1
      exact ⟨hr.1, fun Q hQ => hr.2 (fun x => Q (x, ())) hQ⟩
  | _, _, .fmul t, (a, b, ()), P, hw => by
    simp only [OpCode.wp_fmul] at hw ⊢
    cases ht : t.isFloatTree
    · simp only [ht, Bool.not_false, ↓reduceIte] at hw
    · simp only [ht, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw ⊢
      have h1 := liftFloatRel2_self Float.Model.UnpackedFloat.mul t a b (fun r => P (r, ())) hw
      refine liftFloatRel2_mono Float.Model.UnpackedFloat.mul t a b _ _ (fun r hr => ?_) h1
      exact ⟨hr.1, fun Q hQ => hr.2 (fun x => Q (x, ())) hQ⟩
  | _, _, .fdiv t, (a, b, ()), P, hw => by
    simp only [OpCode.wp_fdiv] at hw ⊢
    cases ht : t.isFloatTree
    · simp only [ht, Bool.not_false, ↓reduceIte] at hw
    · simp only [ht, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw ⊢
      have h1 := liftFloatRel2_self Float.Model.UnpackedFloat.div t a b (fun r => P (r, ())) hw
      refine liftFloatRel2_mono Float.Model.UnpackedFloat.div t a b _ _ (fun r hr => ?_) h1
      exact ⟨hr.1, fun Q hQ => hr.2 (fun x => Q (x, ())) hQ⟩
  | _, _, .ffma t, (a, b, c, ()), P, hw => by
    simp only [OpCode.wp_ffma] at hw ⊢
    cases ht : t.isFloatTree
    · simp only [ht, Bool.not_false, ↓reduceIte] at hw
    · simp only [ht, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw ⊢
      have h1 := liftFloatRel3_self Float.Model.UnpackedFloat.fma t a b c (fun r => P (r, ())) hw
      refine liftFloatRel3_mono Float.Model.UnpackedFloat.fma t a b c _ _ (fun r hr => ?_) h1
      exact ⟨hr.1, fun Q hQ => hr.2 (fun x => Q (x, ())) hQ⟩
  | _, _, .fsqrt t, (a, ()), P, hw => by
    simp only [OpCode.wp_fsqrt] at hw ⊢
    cases ht : t.isFloatTree
    · simp only [ht, Bool.not_false, ↓reduceIte] at hw
    · simp only [ht, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw ⊢
      have h1 := liftFloatRel1_self Float.Model.UnpackedFloat.sqrt t a (fun r => P (r, ())) hw
      refine liftFloatRel1_mono Float.Model.UnpackedFloat.sqrt t a _ _ (fun r hr => ?_) h1
      exact ⟨hr.1, fun Q hQ => hr.2 (fun x => Q (x, ())) hQ⟩
  | _, _, .fneg _, (_, ()), P, hw => by
    simp only [OpCode.wp_fneg] at hw ⊢; exact cond_false_self P hw
  | _, _, .fabs _, (_, ()), P, hw => by
    simp only [OpCode.wp_fabs] at hw ⊢; exact cond_false_self P hw
  | _, _, .fcmp _ _ _ rfl, (_, _, ()), P, hw => by
    simp only [OpCode.wp_fcmp, cast_eq] at hw ⊢; exact cond_false_self P hw
  | _, _, .fptoui f n, (a, ()), P, hw => by
    simp only [OpCode.wp_fptoui] at hw ⊢
    cases htr : truncToInt (unpackFloat f a) with
    | none => simp only [htr] at hw
    | some z =>
      simp only [htr] at hw ⊢
      exact ⟨hw.1, hw.2.1, hw.2.2, fun _ hQ => hQ.2.2⟩
  | _, _, .fptosi f n, (a, ()), P, hw => by
    simp only [OpCode.wp_fptosi] at hw ⊢
    refine ⟨hw.1, ?_⟩
    have hw2 := hw.2
    cases htr : truncToInt (unpackFloat f a) with
    | none => simp only [htr] at hw2
    | some z =>
      simp only [htr] at hw2 ⊢
      exact ⟨hw2.1, hw2.2.1, hw2.2.2, fun _ hQ => hQ.2.2.2⟩
  | _, _, .uitofp _ _, (_, ()), _, hw => ⟨hw, fun _ hQ => hQ⟩
  | _, _, .sitofp _ _, (_, ()), _, hw => ⟨hw, fun _ hQ => hQ⟩
  | _, _, .fcvt f g, (a, ()), P, hw => by
    simp only [OpCode.wp_fcvt] at hw ⊢
    have h1 := convertFloat_self f g a hw
    exact convertFloat_mono f g a (fun r hr =>
      ⟨hr.1, fun Q hQ => hr.2 (fun x => Q (x, ())) hQ⟩) h1

/-! ## Valuation updates, `GoodG`, `GoodT`, and `GvnTbl.find_mem` -/

def Arg.gev (ρ : (t : Ty) → Nat → Val t) {t : Ty} : Arg K t → Val t
  | .var i => ρ t i
  | .imm c => c

def tupGev (ρ : (t : Ty) → Nat → Val t) : {ts : List Ty} → Tup (Arg K) ts → Tup Val ts
  | [], () => ()
  | _ :: _, (a, as) => (a.gev ρ, tupGev ρ as)

def Arg.KeyLt (b : Nat) {t : Ty} : Arg K t → Prop
  | .var i => i < b
  | .imm _ => True

def TupKeyLt (b : Nat) : {ts : List Ty} → Tup (Arg K) ts → Prop
  | [], () => True
  | _ :: _, (a, as) => a.KeyLt b ∧ TupKeyLt b as

theorem Arg.KeyLt.mono {b b' : Nat} (h : b ≤ b') {t : Ty} {a : Arg K t} :
    a.KeyLt b → a.KeyLt b' := by
  cases a with
  | var _ => exact fun hlt => Nat.lt_of_lt_of_le hlt h
  | imm _ => exact id

theorem TupKeyLt.mono {b b' : Nat} (h : b ≤ b') :
    {ts : List Ty} → {as : Tup (Arg K) ts} → TupKeyLt b as → TupKeyLt b' as
  | [], (), _ => trivial
  | _ :: _, (_, _), ⟨ha, has⟩ => ⟨ha.mono h, TupKeyLt.mono h has⟩

theorem Arg.gev_fupd (ρ : (t : Ty) → Nat → Val t) {b : Nat} {u : Ty} (v : Val u)
    {t : Ty} {a : Arg K t} (hlt : a.KeyLt b) :
    a.gev (fupd ρ b v) = a.gev ρ := by
  cases a with
  | var _ => exact fupd_ne ρ v (Nat.ne_of_lt hlt)
  | imm _ => rfl

theorem Arg.gev_fupdTup (ρ : (t : Ty) → Nat → Val t) {b : Nat}
    {ts : List Ty} (xs : Tup Val ts) {t : Ty} {a : Arg K t} (hlt : a.KeyLt b) :
    a.gev (fupdTup ρ b xs) = a.gev ρ := by
  cases a with
  | var _ => exact fupdTup_lt ρ xs hlt
  | imm _ => rfl

theorem tupGev_fupdTup (ρ : (t : Ty) → Nat → Val t) {b : Nat} {ts : List Ty} (xs : Tup Val ts) :
    {sig : List Ty} → {as : Tup (Arg K) sig} → TupKeyLt b as →
    tupGev (fupdTup ρ b xs) as = tupGev ρ as
  | [], (), _ => rfl
  | _ :: _, (_, _), ⟨ha, has⟩ =>
    Prod.ext (Arg.gev_fupdTup ρ xs ha) (tupGev_fupdTup ρ xs has)

def gvalVals : {ts : List Ty} → Tup (GVal Val) ts → Tup Val ts
  | [], () => ()
  | _ :: _, ((v, _), xs) => (v, gvalVals xs)

def TupGValGood (ρ : (t : Ty) → Nat → Val t) (b : Nat) :
    {ts : List Ty} → Tup (GVal Val) ts → Prop
  | [], () => True
  | t :: _, ((v, id), xs) => id < b ∧ ρ t id = v ∧ TupGValGood ρ b xs

theorem TupGValGood.upd {ρ : (t : Ty) → Nat → Val t} {b : Nat}
    {ts : List Ty} (ys : Tup Val ts) :
    {rs : List Ty} → {gs : Tup (GVal Val) rs} →
    TupGValGood ρ b gs → TupGValGood (fupdTup ρ b ys) (b + ts.length) gs
  | [], (), _ => trivial
  | _ :: _, ((_, _), _), ⟨hlt, heq, hgs⟩ =>
    ⟨by omega, (fupdTup_lt ρ ys hlt).trans heq, TupGValGood.upd ys hgs⟩

theorem GvnBucket.find_mem :
    {V : Ty → Type} → (bkt : GvnBucket V) → {sig rs : List Ty} → {code : OpCode sig rs} →
    {args : Tup (Arg K) sig} → {res : Tup (GVal V) rs} →
    GvnBucket.find bkt sig rs code args = some res →
    ⟨⟨sig, rs, code, args⟩, res⟩ ∈ bkt
  | _, [], _, _, _, _, _, h => nomatch h
  | _, ⟨k', v⟩ :: rest, sig, rs, code, args, res, h => by
    simp only [GvnBucket.find] at h
    cases hk : gvnKeyDecEq k' ⟨sig, rs, code, args⟩ with
    | isTrue heq =>
      rw [hk] at h
      dsimp only at h
      cases h
      subst heq
      exact List.mem_cons_self
    | isFalse _ =>
      rw [hk] at h
      dsimp only at h
      exact List.mem_cons_of_mem _ (GvnBucket.find_mem rest h)

def GvnTrie.All {V : Ty → Type} (P : GvnEntry V → Prop) : GvnTrie V → Prop
  | .empty => True
  | .node b e o => (∀ x ∈ b, P x) ∧ GvnTrie.All P e ∧ GvnTrie.All P o

theorem GvnTrie.All.mono {V : Ty → Type} {P Q : GvnEntry V → Prop}
    (h : ∀ x, P x → Q x) : {t : GvnTrie V} → t.All P → t.All Q
  | .empty, _ => trivial
  | .node _ _ _, ⟨hb, he, ho⟩ => ⟨fun x hx => h x (hb x hx), he.mono h, ho.mono h⟩

theorem GvnTrie.All.get {V : Ty → Type} {P : GvnEntry V → Prop} :
    ∀ (t : GvnTrie V) (fuel n : Nat), t.All P → ∀ x ∈ GvnTrie.get t fuel n, P x
  | .empty, _, _, _, _, hx => by cases hx
  | .node _ _ _, 0, _, ⟨hb, _, _⟩, x, hx => hb x hx
  | .node _ _ _, _ + 1, 0, ⟨hb, _, _⟩, x, hx => hb x hx
  | .node _ e o, fuel + 1, n + 1, ⟨_, he, ho⟩, x, hx => by
    simp only [GvnTrie.get] at hx
    split at hx
    · exact GvnTrie.All.get e fuel (n / 2) he x hx
    · exact GvnTrie.All.get o fuel (n / 2) ho x hx

theorem GvnTrie.All.insert {V : Ty → Type} {P : GvnEntry V → Prop} :
    ∀ (t : GvnTrie V) (fuel n : Nat) (entry : GvnEntry V),
      t.All P → P entry → (GvnTrie.insert t fuel n entry).All P
  | .empty, 0, _, _, _, hp => by
    simp only [GvnTrie.insert, GvnTrie.All]
    refine ⟨(fun x hx => by cases hx with | head => exact hp | tail _ hx => nomatch hx), trivial, trivial⟩
  | .node _ _ _, 0, _, _, ⟨hb, he, ho⟩, hp => by
    simp only [GvnTrie.insert, GvnTrie.All]
    refine ⟨(fun x hx => by cases hx with | head => exact hp | tail _ hx => exact hb x hx), he, ho⟩
  | .empty, _ + 1, 0, _, _, hp => by
    simp only [GvnTrie.insert, GvnTrie.All]
    refine ⟨(fun x hx => by cases hx with | head => exact hp | tail _ hx => nomatch hx), trivial, trivial⟩
  | .node _ _ _, _ + 1, 0, _, ⟨hb, he, ho⟩, hp => by
    simp only [GvnTrie.insert, GvnTrie.All]
    refine ⟨(fun x hx => by cases hx with | head => exact hp | tail _ hx => exact hb x hx), he, ho⟩
  | .empty, fuel + 1, n + 1, entry, _, hp => by
    simp only [GvnTrie.insert]
    split <;> simp only [GvnTrie.All]
    · refine ⟨(fun _ hx => nomatch hx), GvnTrie.All.insert .empty fuel (n / 2) entry trivial hp, trivial⟩
    · refine ⟨(fun _ hx => nomatch hx), trivial, GvnTrie.All.insert .empty fuel (n / 2) entry trivial hp⟩
  | .node _ e o, fuel + 1, n + 1, entry, ⟨hb, he, ho⟩, hp => by
    simp only [GvnTrie.insert]
    split <;> simp only [GvnTrie.All]
    · exact ⟨hb, GvnTrie.All.insert e fuel (n / 2) entry he hp, ho⟩
    · exact ⟨hb, he, GvnTrie.All.insert o fuel (n / 2) entry ho hp⟩

theorem GvnTbl.find_mem {V : Ty → Type} (tbl : GvnTbl V) {sig rs : List Ty}
    {code : OpCode sig rs} {args : Tup (Arg K) sig} {res : Tup (GVal V) rs}
    (h : tbl.find sig rs code args = some res) :
    ⟨⟨sig, rs, code, args⟩, res⟩ ∈ GvnTrie.get tbl 16 (gvnHash code args) := by
  unfold GvnTbl.find at h
  exact GvnBucket.find_mem _ h

def GoodG (ρ : (t : Ty) → Nat → Val t) (b : Nat) (G : Ctx (GVal Val) Val) : Prop :=
  ∀ p ∈ G, p.2.1.1 = p.2.2 ∧ p.2.1.2 < b ∧ ρ p.1 p.2.1.2 = p.2.2

theorem GoodG.cons {ρ : (t : Ty) → Nat → Val t} {b : Nat} {G : Ctx (GVal Val) Val}
    (hG : GoodG ρ b G) {t : Ty} {g : GVal Val t} {v : Val t}
    (h1 : g.1 = v) (h2 : g.2 < b) (h3 : ρ t g.2 = v) :
    GoodG ρ b (⟨t, g, v⟩ :: G)
  | _, .head _ => ⟨h1, h2, h3⟩
  | _, .tail _ hp => hG _ hp

theorem GoodG.upd_all {ρ : (t : Ty) → Nat → Val t} {b : Nat} {G : Ctx (GVal Val) Val}
    (hG : GoodG ρ b G) {ts : List Ty} (xs : Tup Val ts) :
    GoodG (fupdTup ρ b xs) (b + ts.length) G := by
  intro p hp
  obtain ⟨h1, h2, h3⟩ := hG p hp
  exact ⟨h1, by omega, (fupdTup_lt ρ xs h2).trans h3⟩

theorem GoodG.append {ρ : (t : Ty) → Nat → Val t} {b : Nat} {G₁ G₂ : Ctx (GVal Val) Val}
    (h1 : GoodG ρ b G₁) (h2 : GoodG ρ b G₂) : GoodG ρ b (G₁ ++ G₂) := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact h1 p hp
  · exact h2 p hp

private theorem GoodG.freshGVals_only (ρ : (t : Ty) → Nat → Val t) :
    {ts : List Ty} → (xs : Tup Val ts) → (b : Nat) →
    GoodG (fupdTup ρ b xs) (b + ts.length) (Tup.zip (freshGVals ts xs b) xs)
  | [], (), _ => fun _ hp => nomatch hp
  | _ :: ts, (x, xs), b => by
    simp only [freshGVals, Tup.zip, fupdTup, List.length_cons]
    intro p hp
    cases hp with
    | head =>
      dsimp only
      refine ⟨rfl, by omega, ?_⟩
      rw [fupdTup_lt (fupd ρ b x) xs (by omega), fupd_eq]
    | tail _ hp =>
      have ih := GoodG.freshGVals_only (fupd ρ b x) xs (b + 1) p hp
      rw [show b + 1 + ts.length = b + (ts.length + 1) by omega] at ih
      exact ih

theorem GoodG.freshGVals {ρ : (t : Ty) → Nat → Val t} {b : Nat} {G : Ctx (GVal Val) Val}
    (hG : GoodG ρ b G) {ts : List Ty} (xs : Tup Val ts) :
    GoodG (fupdTup ρ b xs) (b + ts.length) (Tup.zip (freshGVals ts xs b) xs ++ G) :=
  (GoodG.freshGVals_only ρ xs b).append (hG.upd_all xs)

theorem GoodG.freshOne {ρ : (t : Ty) → Nat → Val t} {b : Nat} {G : Ctx (GVal Val) Val}
    (hG : GoodG ρ b G) {t : Ty} (v : Val t) :
    GoodG (fupd ρ b v) (b + 1) (⟨t, (v, b), v⟩ :: G) :=
  (hG.upd_all (ts := [t]) (v, ())).cons rfl (Nat.lt_succ_self b)
    (by simp [fupdTup, fupd_eq])

theorem GoodG.append_tup_gval {ρ : (t : Ty) → Nat → Val t} {b : Nat} {G : Ctx (GVal Val) Val}
    (hG : GoodG ρ b G) :
    {rs : List Ty} → {gs : Tup (GVal Val) rs} →
    TupGValGood ρ b gs → GoodG ρ b (Tup.zip gs (gvalVals gs) ++ G)
  | [], (), _ => hG
  | _ :: _, ((_, _), _), ⟨hlt, heq, hgs⟩ =>
    (GoodG.append_tup_gval hG hgs).cons rfl hlt heq

theorem TupGValGood.freshGVals (ρ : (t : Ty) → Nat → Val t) :
    {ts : List Ty} → (xs : Tup Val ts) → (b : Nat) →
    TupGValGood (fupdTup ρ b xs) (b + ts.length) (freshGVals ts xs b)
  | [], (), _ => trivial
  | _ :: ts, (x, xs), b => by
    unfold LeanQbe.T.freshGVals
    simp only [TupGValGood, fupdTup, List.length_cons]
    refine ⟨by omega, ?_, ?_⟩
    · rw [fupdTup_lt (fupd ρ b x) xs (by omega), fupd_eq]
    · have ih := TupGValGood.freshGVals (fupd ρ b x) xs (b + 1)
      rw [show b + 1 + ts.length = b + (ts.length + 1) by omega] at ih
      exact ih

theorem gvalVals_freshGVals :
    {ts : List Ty} → (xs : Tup Val ts) → (b : Nat) → gvalVals (freshGVals ts xs b) = xs
  | [], (), _ => rfl
  | _ :: _, (_, _), b => Prod.ext rfl (gvalVals_freshGVals _ (b + 1))

theorem ArgRel.gout_val {ρ : (t : Ty) → Nat → Val t} {b : Nat} {G : Ctx (GVal Val) Val}
    (hG : GoodG ρ b G) {t : Ty} {a₁ : Arg (GVal Val) t} {a₂ : Arg Val t} :
    ArgRel G t a₁ a₂ → a₁.gout.val = a₂.val
  | .var h => (hG _ h).1
  | .imm _ => rfl

theorem ArgRel.gkey_lt {ρ : (t : Ty) → Nat → Val t} {b : Nat} {G : Ctx (GVal Val) Val}
    (hG : GoodG ρ b G) {t : Ty} {a₁ : Arg (GVal Val) t} {a₂ : Arg Val t} :
    ArgRel G t a₁ a₂ → a₁.gkey.KeyLt b
  | .var h => (hG _ h).2.1
  | .imm _ => trivial

theorem ArgRel.gkey_ev {ρ : (t : Ty) → Nat → Val t} {b : Nat} {G : Ctx (GVal Val) Val}
    (hG : GoodG ρ b G) {t : Ty} {a₁ : Arg (GVal Val) t} {a₂ : Arg Val t} :
    ArgRel G t a₁ a₂ → a₁.gkey.gev ρ = a₂.val
  | .var h => (hG _ h).2.2
  | .imm _ => rfl

theorem TRel.gout_vals {ρ : (t : Ty) → Nat → Val t} {b : Nat} {G : Ctx (GVal Val) Val}
    (hG : GoodG ρ b G) :
    {ts : List Ty} → {as₁ : Tup (Arg (GVal Val)) ts} → {as₂ : Tup (Arg Val) ts} →
    TRel (ArgRel G) as₁ as₂ → vals (tupGOut as₁) = vals as₂
  | [], (), (), .nil => rfl
  | _ :: _, (_, _), (_, _), .cons h hs => Prod.ext (h.gout_val hG) (TRel.gout_vals hG hs)

theorem TRel.gkey_lt {ρ : (t : Ty) → Nat → Val t} {b : Nat} {G : Ctx (GVal Val) Val}
    (hG : GoodG ρ b G) :
    {ts : List Ty} → {as₁ : Tup (Arg (GVal Val)) ts} → {as₂ : Tup (Arg Val) ts} →
    TRel (ArgRel G) as₁ as₂ → TupKeyLt b (tupGKey as₁)
  | [], (), (), .nil => trivial
  | _ :: _, (_, _), (_, _), .cons h hs => ⟨h.gkey_lt hG, TRel.gkey_lt hG hs⟩

theorem TRel.gkey_vals {ρ : (t : Ty) → Nat → Val t} {b : Nat} {G : Ctx (GVal Val) Val}
    (hG : GoodG ρ b G) :
    {ts : List Ty} → {as₁ : Tup (Arg (GVal Val)) ts} → {as₂ : Tup (Arg Val) ts} →
    TRel (ArgRel G) as₁ as₂ → tupGev ρ (tupGKey as₁) = vals as₂
  | [], (), (), .nil => rfl
  | _ :: _, (_, _), (_, _), .cons h hs => Prod.ext (h.gkey_ev hG) (TRel.gkey_vals hG hs)

def GoodEntry (ρ : (t : Ty) → Nat → Val t) (b : Nat) (e : GvnEntry Val) : Prop :=
  TupKeyLt b e.1.2.2.2 ∧
  TupGValGood ρ b e.2 ∧
  ∀ P : Tup Val e.1.2.1 → Prop, e.1.2.2.1.wp (tupGev ρ e.1.2.2.2) P → P (gvalVals e.2)

def GoodT (ρ : (t : Ty) → Nat → Val t) (b : Nat) (tbl : GvnTbl Val) : Prop :=
  tbl.All (GoodEntry ρ b)

theorem GoodT.upd_all {ρ : (t : Ty) → Nat → Val t} {b : Nat} {tbl : GvnTbl Val}
    (hT : GoodT ρ b tbl) {ts : List Ty} (xs : Tup Val ts) :
    GoodT (fupdTup ρ b xs) (b + ts.length) tbl := by
  refine hT.mono fun ⟨⟨sig, rs, code, kArgs⟩, cached⟩ ⟨hlt, hgs, hwp⟩ => ?_
  refine ⟨hlt.mono (Nat.le_add_right _ _), hgs.upd xs, fun P hP => ?_⟩
  dsimp only at hP ⊢
  rw [tupGev_fupdTup ρ xs hlt] at hP
  exact hwp P hP

/-! ## `gvn_wp` via `Wf.induct` -/

theorem gvnB_get {V₁ : Ty → Type} {L₁ : List Ty → Type} {rs : List Ty} (b : Nat) (tbl : GvnTbl V₁) :
    {sig : List (List Ty)} → {ts : List Ty} → (bs : Blocks (GVal V₁) L₁ rs sig) →
    (i : Member ts sig) → (xs : Tup V₁ ts) →
    (gvnB b tbl bs).get i xs = gvn (b + ts.length) tbl (bs.get i (freshGVals ts xs b))
  | _, _, .cons _ _, .here, _ => rfl
  | _, _, .cons _ bs, .there i, xs => gvnB_get b tbl bs i xs

/-- Weakest-precondition preservation for `gvn`, proved via `Wf.induct`. -/
theorem gvn_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx (GVal Val) Val} {D : Ctx Cont Cont}
    {e₁ : Expr (GVal Val) Cont rs} {e₂ : Expr Val Cont rs}
    (hwf : Wf G D e₁ e₂) :
    (∀ p ∈ D, p.2.1 = p.2.2) →
    ∀ b ρ tbl, GoodG ρ b G → GoodT ρ b tbl → ∀ m, wp Γ Q X e₂ m → wp Γ Q X (gvn b tbl e₁) m := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop _ ih =>
    intro hD b ρ tbl hG hT m hw
    simp only [wp] at hw
    cases hop with
    | @mk sig _ code args₁ args₂ hargs =>
      dsimp only [Op.wp] at hw
      simp only [gvn]
      cases hfind : tbl.find sig ts code (tupGKey args₁) with
      | some cached =>
        dsimp only
        have hmem := GvnTbl.find_mem tbl hfind
        obtain ⟨_, hgs, hwp⟩ := GvnTrie.All.get tbl 16 (gvnHash code (tupGKey args₁)) hT _ hmem
        dsimp only at hgs hwp
        rw [← hargs.gkey_vals hG] at hw
        exact ih cached (gvalVals cached) hD b ρ tbl (hG.append_tup_gval hgs) hT m
          (hwp (fun ys => wp Γ Q X (k₂ ys) m) hw)
      | none =>
        dsimp only [wp, Op.wp]
        have hw' := OpCode.wp_self code (vals args₂) hw
        rw [← hargs.gout_vals hG] at hw'
        refine OpCode.wp_mono code _ (fun xs ⟨hk2, hself⟩ => ?_) hw'
        have hlt := hargs.gkey_lt hG
        have hkev := hargs.gkey_vals hG
        refine ih (freshGVals ts xs b) xs hD (b + ts.length) (fupdTup ρ b xs) _
          (hG.freshGVals xs) ?_ m hk2
        unfold GvnTbl.insert
        refine GvnTrie.All.insert tbl 16 _ _ (hT.upd_all xs) ?_
        refine ⟨hlt.mono (Nat.le_add_right _ _), TupGValGood.freshGVals ρ xs b, fun P hP => ?_⟩
        dsimp only at hP ⊢
        rw [tupGev_fupdTup ρ xs hlt, hkev, ← hargs.gout_vals hG] at hP
        rw [gvalVals_freshGVals]
        exact hself P hP
  | load t ha _ ih =>
    intro hD b ρ tbl hG hT m hw
    simp only [wp, gvn] at hw ⊢
    rcases hw with ⟨v, hv, hk⟩
    exact ⟨v, ha.gout_val hG ▸ hv,
      ih (v, b) v hD (b + 1) (fupd ρ b v) tbl (hG.freshOne v)
        (by simpa [fupdTup] using hT.upd_all (ts := [t]) (v, ())) m hk⟩
  | store hv ha _ ih =>
    intro hD b ρ tbl hG hT m hw
    simp only [wp, gvn] at hw ⊢
    rw [ha.gout_val hG, hv.gout_val hG]
    exact ⟨hw.1, ih hD b ρ tbl hG hT _ hw.2⟩
  | call f hargs _ ih =>
    intro hD b ρ tbl hG hT m hw
    simp only [wp, gvn] at hw ⊢
    rcases hw with ⟨P, E, hΓ, hP, hE⟩
    rw [hargs.gout_vals hG]
    exact ⟨P, E, hΓ, fun r m' hp =>
      ih (freshGVals _ r b) r hD (b + _) (fupdTup ρ b r) tbl (hG.freshGVals r)
        (hT.upd_all r) m' (hP r m' hp), hE⟩
  | jnz hc _ _ iht ihe =>
    intro hD b ρ tbl hG hT m hw
    simp only [wp, gvn] at hw ⊢
    rw [hc.gout_val hG]
    exact ⟨fun h => iht hD b ρ tbl hG hT m (hw.1 h), fun h => ihe hD b ρ tbl hG hT m (hw.2 h)⟩
  | jump hj hargs =>
    intro hD b ρ tbl hG _ m hw
    have hj' := hD _ hj; dsimp only at hj'
    simp only [wp, gvn] at hw ⊢
    rw [hj', hargs.gout_vals hG]
    exact hw
  | ret hvs =>
    intro _ b ρ tbl hG _ m hw
    simp only [wp, gvn] at hw ⊢
    rw [hvs.gout_vals hG]
    exact hw
  | exit f hargs =>
    intro _ b ρ tbl hG _ m hw
    simp only [wp, gvn] at hw ⊢
    rw [hargs.gout_vals hG]
    exact hw
  | hlt =>
    intro _ _ _ _ _ _ _ hw
    exact hw
  | @group G D sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro hD b ρ tbl hG hT m hw
    simp only [wp, gvn] at hw ⊢
    intro Js hclosed
    refine ihk Js Js (tup_zip_self_eq hD Js) b ρ tbl hG hT m (hw Js ?_)
    rw [closed_iff] at hclosed ⊢
    intro ts i xs m' hb
    have hgvn := ihb Js Js i (freshGVals ts xs b) xs (tup_zip_self_eq hD Js)
      (b + ts.length) (fupdTup ρ b xs) tbl (hG.freshGVals xs) (hT.upd_all xs) m' hb
    rw [← gvnB_get b tbl (b₁ Js) i xs] at hgvn
    exact hclosed i xs m' hgvn

/-! ## Relational well-formedness for `gvn` (`RelG`, `RelT`, `gvn_wf`) -/

section
variable {V₁ V₂ : Ty → Type}

def RelGVal (G' : Ctx V₁ V₂) (t : Ty) (g₁ : GVal V₁ t) (g₂ : GVal V₂ t) : Prop :=
  ⟨t, g₁.1, g₂.1⟩ ∈ G' ∧ g₁.2 = g₂.2

theorem RelGVal.weaken {G₁ G₂ : Ctx V₁ V₂} (hsub : ∀ p ∈ G₁, p ∈ G₂)
    {t : Ty} {g₁ : GVal V₁ t} {g₂ : GVal V₂ t} (h : RelGVal G₁ t g₁ g₂) : RelGVal G₂ t g₁ g₂ :=
  ⟨hsub _ h.1, h.2⟩

def RelG (G' : Ctx V₁ V₂) (G : Ctx (GVal V₁) (GVal V₂)) : Prop :=
  ∀ p ∈ G, RelGVal G' p.1 p.2.1 p.2.2

theorem RelG.cons {G' : Ctx V₁ V₂} {G : Ctx (GVal V₁) (GVal V₂)} (hG : RelG G' G)
    {t : Ty} {g₁ : GVal V₁ t} {g₂ : GVal V₂ t} (hg : RelGVal G' t g₁ g₂) :
    RelG G' (⟨t, g₁, g₂⟩ :: G)
  | _, .head _ => hg
  | _, .tail _ hp => hG _ hp

theorem RelG.append {G' : Ctx V₁ V₂} {G H : Ctx (GVal V₁) (GVal V₂)}
    (h1 : RelG G' G) (h2 : RelG G' H) : RelG G' (H ++ G) := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact h2 p hp
  · exact h1 p hp

theorem RelG.weaken {G' G'' : Ctx V₁ V₂} {G : Ctx (GVal V₁) (GVal V₂)}
    (hG : RelG G' G) (hsub : ∀ p ∈ G', p ∈ G'') : RelG G'' G :=
  fun p hp => (hG p hp).weaken hsub

theorem RelG.append_tup {G' : Ctx V₁ V₂} {G : Ctx (GVal V₁) (GVal V₂)} (hG : RelG G' G) :
    {ts : List Ty} → {r₁ : Tup (GVal V₁) ts} → {r₂ : Tup (GVal V₂) ts} →
    TRel (RelGVal G') r₁ r₂ → RelG G' (Tup.zip r₁ r₂ ++ G)
  | [], (), (), .nil => hG
  | _ :: _, (_, _), (_, _), .cons h hs => (RelG.append_tup hG hs).cons h

private theorem RelG.freshGVals_only :
    {ts : List Ty} → (xs₁ : Tup V₁ ts) → (xs₂ : Tup V₂ ts) → (b : Nat) →
    RelG (Tup.zip xs₁ xs₂) (Tup.zip (freshGVals ts xs₁ b) (freshGVals ts xs₂ b))
  | [], (), (), _ => fun _ hp => nomatch hp
  | _ :: _, (_, xs₁), (_, xs₂), b => by
    simp only [freshGVals, Tup.zip]
    intro p hp
    cases hp with
    | head => exact ⟨List.mem_cons_self, rfl⟩
    | tail _ hp =>
      exact (RelG.freshGVals_only xs₁ xs₂ (b + 1) p hp).weaken fun _ hq =>
        List.mem_cons_of_mem _ hq

theorem RelG.freshGVals {G' : Ctx V₁ V₂} {G : Ctx (GVal V₁) (GVal V₂)} (hG : RelG G' G)
    {ts : List Ty} (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts) (b : Nat) :
    RelG (Tup.zip xs₁ xs₂ ++ G')
      (Tup.zip (freshGVals ts xs₁ b) (freshGVals ts xs₂ b) ++ G) :=
  (hG.weaken fun _ hq => List.mem_append_right _ hq).append
    ((RelG.freshGVals_only xs₁ xs₂ b).weaken fun _ hq => List.mem_append_left G' hq)

theorem RelG.freshOne {G' : Ctx V₁ V₂} {G : Ctx (GVal V₁) (GVal V₂)} (hG : RelG G' G)
    {t : Ty} (v₁ : V₁ t) (v₂ : V₂ t) (b : Nat) :
    RelG (⟨t, v₁, v₂⟩ :: G') (⟨t, (v₁, b), (v₂, b)⟩ :: G) :=
  (hG.weaken fun _ hq => List.mem_cons_of_mem _ hq).cons ⟨List.mem_cons_self, rfl⟩

theorem TRel.weaken_gval {G₁ G₂ : Ctx V₁ V₂} (hsub : ∀ p ∈ G₁, p ∈ G₂) :
    {ts : List Ty} → {r₁ : Tup (GVal V₁) ts} → {r₂ : Tup (GVal V₂) ts} →
    TRel (RelGVal G₁) r₁ r₂ → TRel (RelGVal G₂) r₁ r₂
  | [], (), (), .nil => .nil
  | _ :: _, (_, _), (_, _), .cons h hs => .cons (h.weaken hsub) (TRel.weaken_gval hsub hs)

theorem TRel.freshGVals_rel {G' : Ctx V₁ V₂} :
    {ts : List Ty} → (xs₁ : Tup V₁ ts) → (xs₂ : Tup V₂ ts) → (b : Nat) →
    TRel (RelGVal (Tup.zip xs₁ xs₂ ++ G')) (freshGVals ts xs₁ b) (freshGVals ts xs₂ b)
  | [], (), (), _ => .nil
  | _ :: _, (_, xs₁), (_, xs₂), b => by
    simp only [freshGVals, Tup.zip, List.cons_append]
    exact .cons ⟨List.mem_cons_self, rfl⟩
      (TRel.weaken_gval (fun _ hq => List.mem_cons_of_mem _ hq)
        (TRel.freshGVals_rel (G' := G') xs₁ xs₂ (b + 1)))

theorem ArgRel.gout {G' : Ctx V₁ V₂} {G : Ctx (GVal V₁) (GVal V₂)} (hG : RelG G' G)
    {t : Ty} {a₁ : Arg (GVal V₁) t} {a₂ : Arg (GVal V₂) t} :
    ArgRel G t a₁ a₂ → ArgRel G' t a₁.gout a₂.gout
  | .var h => .var (hG _ h).1
  | .imm c => .imm c

theorem ArgRel.gkey_eq {G' : Ctx V₁ V₂} {G : Ctx (GVal V₁) (GVal V₂)} (hG : RelG G' G)
    {t : Ty} {a₁ : Arg (GVal V₁) t} {a₂ : Arg (GVal V₂) t} :
    ArgRel G t a₁ a₂ → a₁.gkey = a₂.gkey
  | .var h => congrArg Arg.var (hG _ h).2
  | .imm _ => rfl

theorem TRel.gout {G' : Ctx V₁ V₂} {G : Ctx (GVal V₁) (GVal V₂)} (hG : RelG G' G) :
    {ts : List Ty} → {as₁ : Tup (Arg (GVal V₁)) ts} → {as₂ : Tup (Arg (GVal V₂)) ts} →
    TRel (ArgRel G) as₁ as₂ → TRel (ArgRel G') (tupGOut as₁) (tupGOut as₂)
  | [], (), (), .nil => .nil
  | _ :: _, (_, _), (_, _), .cons h hs => .cons (h.gout hG) (TRel.gout hG hs)

theorem TRel.gkey_eq {G' : Ctx V₁ V₂} {G : Ctx (GVal V₁) (GVal V₂)} (hG : RelG G' G) :
    {ts : List Ty} → {as₁ : Tup (Arg (GVal V₁)) ts} → {as₂ : Tup (Arg (GVal V₂)) ts} →
    TRel (ArgRel G) as₁ as₂ → tupGKey as₁ = tupGKey as₂
  | [], (), (), .nil => rfl
  | _ :: _, (_, _), (_, _), .cons h hs =>
    Prod.ext (h.gkey_eq hG) (TRel.gkey_eq hG hs)

inductive RelBucket (G' : Ctx V₁ V₂) : GvnBucket V₁ → GvnBucket V₂ → Prop
  | nil : RelBucket G' [] []
  | cons (k : GvnKey) {v₁ : Tup (GVal V₁) k.2.1} {v₂ : Tup (GVal V₂) k.2.1}
      {r₁ : GvnBucket V₁} {r₂ : GvnBucket V₂} :
      TRel (RelGVal G') v₁ v₂ → RelBucket G' r₁ r₂ → RelBucket G' (⟨k, v₁⟩ :: r₁) (⟨k, v₂⟩ :: r₂)

theorem RelBucket.weaken {G₁ G₂ : Ctx V₁ V₂} (hsub : ∀ p ∈ G₁, p ∈ G₂) :
    {b₁ : GvnBucket V₁} → {b₂ : GvnBucket V₂} → RelBucket G₁ b₁ b₂ → RelBucket G₂ b₁ b₂
  | _, _, .nil => .nil
  | _, _, .cons k hv hr => .cons k (hv.weaken_gval hsub) (hr.weaken hsub)

inductive RelT (G' : Ctx V₁ V₂) : GvnTbl V₁ → GvnTbl V₂ → Prop
  | empty : RelT G' .empty .empty
  | node {b₁ : GvnBucket V₁} {b₂ : GvnBucket V₂} {e₁ o₁ : GvnTrie V₁}
      {e₂ o₂ : GvnTrie V₂} :
      RelBucket G' b₁ b₂ → RelT G' e₁ e₂ → RelT G' o₁ o₂ →
      RelT G' (.node b₁ e₁ o₁) (.node b₂ e₂ o₂)

theorem RelT.weaken {G₁ G₂ : Ctx V₁ V₂} (hsub : ∀ p ∈ G₁, p ∈ G₂) :
    {t₁ : GvnTbl V₁} → {t₂ : GvnTbl V₂} → RelT G₁ t₁ t₂ → RelT G₂ t₁ t₂
  | _, _, .empty => .empty
  | _, _, .node hb he ho => .node (hb.weaken hsub) (he.weaken hsub) (ho.weaken hsub)

theorem RelT.get {G' : Ctx V₁ V₂} :
    {t₁ : GvnTbl V₁} → {t₂ : GvnTbl V₂} → RelT G' t₁ t₂ →
    ∀ (fuel n : Nat), RelBucket G' (GvnTrie.get t₁ fuel n) (GvnTrie.get t₂ fuel n)
  | _, _, .empty, _, _ => .nil
  | _, _, .node hb _ _, 0, _ => hb
  | _, _, .node hb _ _, _ + 1, 0 => hb
  | _, _, .node _ he ho, fuel + 1, n + 1 => by
    simp only [GvnTrie.get]
    split
    · exact RelT.get he fuel (n / 2)
    · exact RelT.get ho fuel (n / 2)

theorem RelT.insert {G' : Ctx V₁ V₂} :
    ∀ {t₁ : GvnTbl V₁} {t₂ : GvnTbl V₂} (fuel n : Nat)
      (k : GvnKey) {v₁ : Tup (GVal V₁) k.2.1} {v₂ : Tup (GVal V₂) k.2.1},
      RelT G' t₁ t₂ → TRel (RelGVal G') v₁ v₂ →
      RelT G' (GvnTrie.insert t₁ fuel n ⟨k, v₁⟩) (GvnTrie.insert t₂ fuel n ⟨k, v₂⟩)
  | _, _, 0, _, k, _, _, .empty, hv => .node (.cons k hv .nil) .empty .empty
  | _, _, 0, _, k, _, _, .node hb he ho, hv => .node (.cons k hv hb) he ho
  | _, _, _ + 1, 0, k, _, _, .empty, hv => .node (.cons k hv .nil) .empty .empty
  | _, _, _ + 1, 0, k, _, _, .node hb he ho, hv => .node (.cons k hv hb) he ho
  | _, _, fuel + 1, n + 1, k, _, _, .empty, hv => by
    simp only [GvnTrie.insert]
    split
    · exact .node .nil (RelT.insert fuel (n / 2) k .empty hv) .empty
    · exact .node .nil .empty (RelT.insert fuel (n / 2) k .empty hv)
  | _, _, fuel + 1, n + 1, k, _, _, .node hb he ho, hv => by
    simp only [GvnTrie.insert]
    split
    · exact .node hb (RelT.insert fuel (n / 2) k he hv) ho
    · exact .node hb he (RelT.insert fuel (n / 2) k ho hv)

inductive GvnFindRel (G' : Ctx V₁ V₂) (rs : List Ty) :
    Option (Tup (GVal V₁) rs) → Option (Tup (GVal V₂) rs) → Prop
  | none : GvnFindRel G' rs none none
  | some {r₁ : Tup (GVal V₁) rs} {r₂ : Tup (GVal V₂) rs} :
      TRel (RelGVal G') r₁ r₂ → GvnFindRel G' rs (some r₁) (some r₂)

theorem RelBucket.find_rel {G' : Ctx V₁ V₂} :
    {b₁ : GvnBucket V₁} → {b₂ : GvnBucket V₂} → RelBucket G' b₁ b₂ →
    (sig rs : List Ty) → (code : OpCode sig rs) → (args : Tup (Arg K) sig) →
    GvnFindRel G' rs (GvnBucket.find b₁ sig rs code args) (GvnBucket.find b₂ sig rs code args)
  | _, _, .nil, _, _, _, _ => .none
  | _, _, .cons k hv hr, sig, rs, code, args => by
    simp only [GvnBucket.find]
    cases hk : gvnKeyDecEq k ⟨sig, rs, code, args⟩ with
    | isTrue heq =>
      dsimp only
      subst heq
      exact .some hv
    | isFalse _ =>
      dsimp only
      exact hr.find_rel sig rs code args

theorem RelT.find_rel {G' : Ctx V₁ V₂} {t₁ : GvnTbl V₁} {t₂ : GvnTbl V₂} (hT : RelT G' t₁ t₂)
    (sig rs : List Ty) (code : OpCode sig rs) (args : Tup (Arg K) sig) :
    GvnFindRel G' rs (t₁.find sig rs code args) (t₂.find sig rs code args) := by
  unfold GvnTbl.find
  exact RelBucket.find_rel (hT.get 16 (gvnHash code args)) sig rs code args

end

/-- Well-formedness preservation for `gvn`, proved via `Wf.induct`. -/
theorem gvn_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx (GVal V₁) (GVal V₂)} {D : Ctx L₁ L₂}
    {e₁ : Expr (GVal V₁) L₁ rs} {e₂ : Expr (GVal V₂) L₂ rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ {G' : Ctx V₁ V₂}, RelG G' G → ∀ b tbl₁ tbl₂, RelT G' tbl₁ tbl₂ →
      Wf G' D (gvn b tbl₁ e₁) (gvn b tbl₂ e₂) := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop _ ih =>
    intro G' hG b tbl₁ tbl₂ hT
    cases hop with
    | @mk sig _ code args₁ args₂ hargs =>
      have hkey : tupGKey args₁ = tupGKey args₂ := TRel.gkey_eq hG hargs
      have hfind := hT.find_rel sig ts code (tupGKey args₂)
      simp only [gvn]
      rw [hkey]
      generalize hfl1 : tbl₁.find sig ts code (tupGKey args₂) = r₁ at hfind
      generalize hfl2 : tbl₂.find sig ts code (tupGKey args₂) = r₂ at hfind
      cases hfind with
      | some hr => exact ih _ _ (hG.append_tup hr) b tbl₁ tbl₂ hT
      | none =>
        refine .let_ (.mk code (TRel.gout hG hargs)) fun xs₁ xs₂ => ?_
        have hsub : ∀ p ∈ G', p ∈ (Tup.zip xs₁ xs₂ ++ G') := fun _ hq => List.mem_append_right _ hq
        refine ih _ _ (hG.freshGVals xs₁ xs₂ b) (b + ts.length) _ _ ?_
        unfold GvnTbl.insert
        exact RelT.insert 16 (gvnHash code (tupGKey args₂)) ⟨sig, ts, code, tupGKey args₂⟩
          (hT.weaken hsub) (TRel.freshGVals_rel xs₁ xs₂ b)
  | load t ha _ ih =>
    intro G' hG b tbl₁ tbl₂ hT
    refine .load t (ha.gout hG) fun v₁ v₂ => ?_
    exact ih _ _ (hG.freshOne v₁ v₂ b) (b + 1) tbl₁ tbl₂
      (hT.weaken fun _ hq => List.mem_cons_of_mem _ hq)
  | store hv ha _ ih =>
    intro G' hG b tbl₁ tbl₂ hT
    exact .store (hv.gout hG) (ha.gout hG) (ih hG b tbl₁ tbl₂ hT)
  | call f hargs _ ih =>
    intro G' hG b tbl₁ tbl₂ hT
    refine .call f (TRel.gout hG hargs) fun xs₁ xs₂ => ?_
    exact ih _ _ (hG.freshGVals xs₁ xs₂ b) (b + _) tbl₁ tbl₂
      (hT.weaken fun _ hq => List.mem_append_right _ hq)
  | jnz hc _ _ iht ihe =>
    intro G' hG b tbl₁ tbl₂ hT
    exact .jnz (hc.gout hG) (iht hG b tbl₁ tbl₂ hT) (ihe hG b tbl₁ tbl₂ hT)
  | jump hj hargs =>
    intro G' hG _ _ _ _
    exact .jump hj (TRel.gout hG hargs)
  | ret hvs =>
    intro G' hG _ _ _ _
    exact .ret (TRel.gout hG hvs)
  | exit f hargs =>
    intro G' hG _ _ _ _
    exact .exit f (TRel.gout hG hargs)
  | hlt =>
    intro _ _ _ _ _ _
    exact .hlt
  | @group G D sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro G' hG b tbl₁ tbl₂ hT
    refine .group (fun Js₁ Js₂ => WfB.of_get fun i xs₁ xs₂ => ?_)
      (fun Js₁ Js₂ => ihk Js₁ Js₂ hG b tbl₁ tbl₂ hT)
    rw [gvnB_get, gvnB_get]
    exact ihb Js₁ Js₂ i _ _ (hG.freshGVals xs₁ xs₂ b) (b + _) tbl₁ tbl₂
      (hT.weaken fun _ hq => List.mem_append_right _ hq)

/-! ## Closed functions -/

theorem Func.gvn_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) : (Func.gvn f).Wf := by
  intro V₁ V₂ L₁ L₂ xs₁ xs₂
  have hwf := hf (GVal V₁) (GVal V₂) L₁ L₂ (freshGVals as xs₁ 0) (freshGVals as xs₂ 0)
  have hrel : RelG (Tup.zip xs₁ xs₂)
      (Tup.zip (freshGVals as xs₁ 0) (freshGVals as xs₂ 0)) := by
    simpa using RelG.freshGVals (G := []) (G' := []) (fun _ hp => nomatch hp) xs₁ xs₂ 0
  exact LeanQbe.T.gvn_wf hwf hrel as.length .empty .empty .empty

/-- GVN/CSE refines function contracts: any source contract holds on `Func.gvn f`. -/
theorem Func.gvn_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.gvn f) xs m Q X := by
  have hwf := hf (GVal Val) Val Cont Cont (freshGVals as xs 0) xs
  have hgood : GoodG (fupdTup (fun _ _ => default) 0 xs) as.length
      (Tup.zip (freshGVals as xs 0) xs) := by
    simpa using GoodG.freshGVals (ρ := fun _ _ => default) (b := 0) (G := [])
      (fun _ hp => nomatch hp) xs
  exact LeanQbe.T.gvn_wp hwf (fun _ hp => nomatch hp) as.length _ .empty hgood
    trivial m h

end LeanQbe.T
