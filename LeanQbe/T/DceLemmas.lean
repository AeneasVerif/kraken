module

public import LeanQbe.T.Dce
public import LeanQbe.T.OptUtilLemmas

/-!
# Soundness and Relational Well-Formedness of Dead-Code Elimination (`T6`, `O-M2`)

* `OpCode.wp_exists`: any satisfied `OpCode.wp` guarantees existence of output tuples (exhibiting
  the canonical quiet NaN witness via `isFloatNaN_packedNaN` when quantifiers arise from NaNs,
  and discharging undefined behavior by `False.elim`).
* `dceWith_wp` and `dceWith_wf`, both proved via `Wf.induct`, with `dce_wp` / `dce_wf`
  specialized to `(true, false)`.
* `Func.dceWith_wf` / `Func.dceWith_spec`, plus `Func.dce_wf`, `Func.dce_spec`,
  `Func.deadLoadElim_wf`, and `Func.deadLoadElim_spec` for closed functions.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## `OpCode.wp_exists`: witness existence for dropped pure operations -/

private theorem floatResultWp_exists (f : Fmt) (res : Float.Model.UnpackedFloat)
    (P : BitVec f.width → Prop) (hw : floatResultWp f res P) :
    ∃ r : BitVec f.width, P r := by
  simp only [floatResultWp] at hw
  split at hw
  · exact ⟨(Float.Model.UnpackedFloat.packedNaN f.format).cast (Fmt.format_numBits f),
      hw _ (isFloatNaN_packedNaN f)⟩
  · exact ⟨_, hw⟩

private theorem liftFloatRel1_exists
    (op : Float.Model.Format → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat)
    (t : Ty) (ht : t.isFloatTree = true) (a : Val t) (P : Val t → Prop)
    (hw : liftFloatRel1 op t a P) : ∃ r : Val t, P r :=
  liftFloatRel1_pred op
    (fun t _ P => t.isFloatTree = true → ∃ r : Val t, P r)
    (fun _ _ _ _ h hp ht => let ⟨r, hr⟩ := hp ht; ⟨r, h r hr⟩)
    (fun f _ P hw _ => floatResultWp_exists f _ P hw)
    (fun _ _ _ _ _ hm ht => by
      simp only [Ty.isFloatTree, Bool.and_eq_true] at ht
      obtain ⟨r₁, hr₁⟩ := hm ht.1
      obtain ⟨r₂, hr₂⟩ := hr₁ ht.2
      exact ⟨(r₁, r₂), hr₂⟩)
    t a P hw ht

private theorem liftFloatRel2_exists
    (op : Float.Model.Format → Float.Model.UnpackedFloat →
      Float.Model.UnpackedFloat → Float.Model.UnpackedFloat)
    (t : Ty) (ht : t.isFloatTree = true) (a b : Val t) (P : Val t → Prop)
    (hw : liftFloatRel2 op t a b P) : ∃ r : Val t, P r :=
  liftFloatRel2_pred op
    (fun t _ _ P => t.isFloatTree = true → ∃ r : Val t, P r)
    (fun _ _ _ _ _ h hp ht => let ⟨r, hr⟩ := hp ht; ⟨r, h r hr⟩)
    (fun f _ _ P hw _ => floatResultWp_exists f _ P hw)
    (fun _ _ _ _ _ _ _ hm ht => by
      simp only [Ty.isFloatTree, Bool.and_eq_true] at ht
      obtain ⟨r₁, hr₁⟩ := hm ht.1
      obtain ⟨r₂, hr₂⟩ := hr₁ ht.2
      exact ⟨(r₁, r₂), hr₂⟩)
    t a b P hw ht

private theorem liftFloatRel3_exists
    (op : Float.Model.Format → Float.Model.UnpackedFloat →
      Float.Model.UnpackedFloat → Float.Model.UnpackedFloat → Float.Model.UnpackedFloat)
    (t : Ty) (ht : t.isFloatTree = true) (a b c : Val t) (P : Val t → Prop)
    (hw : liftFloatRel3 op t a b c P) : ∃ r : Val t, P r :=
  liftFloatRel3_pred op
    (fun t _ _ _ P => t.isFloatTree = true → ∃ r : Val t, P r)
    (fun _ _ _ _ _ _ h hp ht => let ⟨r, hr⟩ := hp ht; ⟨r, h r hr⟩)
    (fun f _ _ _ P hw _ => floatResultWp_exists f _ P hw)
    (fun _ _ _ _ _ _ _ _ _ hm ht => by
      simp only [Ty.isFloatTree, Bool.and_eq_true] at ht
      obtain ⟨r₁, hr₁⟩ := hm ht.1
      obtain ⟨r₂, hr₂⟩ := hr₁ ht.2
      exact ⟨(r₁, r₂), hr₂⟩)
    t a b c P hw ht

private theorem convertFloat_exists (src dst : Fmt) (a : BitVec src.width)
    (P : BitVec dst.width → Prop) (hw : convertFloat src dst a P) :
    ∃ r : BitVec dst.width, P r := by
  simp only [convertFloat] at hw
  cases hu : unpackFloat src a with
  | notANumber =>
    simp only [hu] at hw
    exact ⟨(Float.Model.UnpackedFloat.packedNaN dst.format).cast (Fmt.format_numBits dst),
      hw _ (isFloatNaN_packedNaN dst)⟩
  | finite _ _ _ _ => simp only [hu] at hw; exact ⟨_, hw⟩
  | infinity _ => simp only [hu] at hw; exact ⟨_, hw⟩
  | zero _ => simp only [hu] at hw; exact ⟨_, hw⟩

private theorem of_hasFloat_exists {t : Ty} {rs : List Ty} {r : Tup Val rs}
    {P : Tup Val rs → Prop} (h : if t.hasFloat then False else P r) : ∃ x, P x := by
  cases hb : t.hasFloat
  · simp only [hb, Bool.false_eq_true, ↓reduceIte] at h; exact ⟨r, h⟩
  · simp only [hb, ↓reduceIte] at h

private theorem of_isFloatTree_exists {t : Ty} {rs : List Ty} {r : Tup Val rs}
    {P : Tup Val rs → Prop} (h : if !t.isFloatTree then False else P r) : ∃ x, P x := by
  cases hb : t.isFloatTree
  · simp only [hb, Bool.not_false, ↓reduceIte] at h
  · simp only [hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h; exact ⟨r, h⟩

private theorem liftFloatRel2_exists_ite
    (op : Float.Model.Format → Float.Model.UnpackedFloat →
      Float.Model.UnpackedFloat → Float.Model.UnpackedFloat)
    {t : Ty} {a b : Val t} {P : Tup Val [t] → Prop}
    (h : if !t.isFloatTree then False else liftFloatRel2 op t a b fun x => P (x, ())) :
    ∃ r : Tup Val [t], P r := by
  cases ht : t.isFloatTree
  · simp only [ht, Bool.not_false, ↓reduceIte] at h
  · simp only [ht, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨r, hr⟩ := liftFloatRel2_exists op t ht a b (fun x => P (x, ())) h
    exact ⟨(r, ()), hr⟩

/-- Any satisfied `OpCode.wp` witnesses an output tuple satisfying `P` (using a canonical
quiet NaN when NaNs quantify universally over `isFloatNaN`, and `False.elim` on UB). -/
theorem OpCode.wp_exists : {sig rs : List Ty} → (c : OpCode sig rs) → (args : Tup Val sig) →
    {P : Tup Val rs → Prop} → c.wp args P → ∃ r : Tup Val rs, P r
  | _, _, .add _, (_, _, ()), _, hw =>
    of_hasFloat_exists (by simp only [OpCode.wp_add] at hw; exact hw)
  | _, _, .sub _, (_, _, ()), _, hw =>
    of_hasFloat_exists (by simp only [OpCode.wp_sub] at hw; exact hw)
  | _, _, .mul _, (_, _, ()), _, hw =>
    of_hasFloat_exists (by simp only [OpCode.wp_mul] at hw; exact hw)
  | _, _, .neg _, (_, ()), _, hw =>
    of_hasFloat_exists (by simp only [OpCode.wp_neg] at hw; exact hw)
  | _, _, .shl _, (_, _, ()), _, hw =>
    of_hasFloat_exists (by simp only [OpCode.wp_shl] at hw; exact hw)
  | _, _, .lshr _, (_, _, ()), _, hw =>
    of_hasFloat_exists (by simp only [OpCode.wp_lshr] at hw; exact hw)
  | _, _, .ashr _, (_, _, ()), _, hw =>
    of_hasFloat_exists (by simp only [OpCode.wp_ashr] at hw; exact hw)
  | _, _, .rotl _, (_, _, ()), _, hw =>
    of_hasFloat_exists (by simp only [OpCode.wp_rotl] at hw; exact hw)
  | _, _, .rotr _, (_, _, ()), _, hw =>
    of_hasFloat_exists (by simp only [OpCode.wp_rotr] at hw; exact hw)
  | _, _, .bswap t, (_, ()), _, hw => by
    simp only [OpCode.wp_bswap] at hw
    cases hb : t.bswapOk
    · simp only [hb, Bool.not_false, ↓reduceIte] at hw
    · simp only [hb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw; exact ⟨_, hw⟩
  | _, _, .cmp _ _ _ rfl, (_, _, ()), _, hw =>
    of_hasFloat_exists (by simp only [OpCode.wp_cmp, cast_eq] at hw; exact hw)
  | _, _, .zext _ _, (_, ()), _, hw => by simp only [OpCode.wp_zext] at hw; exact ⟨_, hw.2⟩
  | _, _, .sext _ _, (_, ()), _, hw => by simp only [OpCode.wp_sext] at hw; exact ⟨_, hw.2⟩
  | _, _, .trunc _ _, (_, ()), _, hw => by simp only [OpCode.wp_trunc] at hw; exact ⟨_, hw.2⟩
  | _, _, .udiv _, (_, _, ()), _, hw => by simp only [OpCode.wp_udiv] at hw; exact ⟨_, hw.2⟩
  | _, _, .sdiv _, (_, _, ()), _, hw => by simp only [OpCode.wp_sdiv] at hw; exact ⟨_, hw.2⟩
  | _, _, .urem _, (_, _, ()), _, hw => by simp only [OpCode.wp_urem] at hw; exact ⟨_, hw.2⟩
  | _, _, .srem _, (_, _, ()), _, hw => by simp only [OpCode.wp_srem] at hw; exact ⟨_, hw.2⟩
  | _, _, .shufd _ _, (_, ()), _, hw => by simp only [OpCode.wp_shufd] at hw; exact ⟨_, hw.2.2⟩
  | _, _, .shufb _, (_, _, ()), _, hw => by simp only [OpCode.wp_shufb] at hw; exact ⟨_, hw.2.2⟩
  | _, _, .alignr _ _, (_, _, ()), _, hw => by simp only [OpCode.wp_alignr] at hw; exact ⟨_, hw.2.2⟩
  | _, _, .blendw _ _, (_, _, ()), _, hw => by simp only [OpCode.wp_blendw] at hw; exact ⟨_, hw.2.2⟩
  | _, _, .fadd _, (_, _, ()), _, hw =>
    liftFloatRel2_exists_ite _ (by simp only [OpCode.wp_fadd] at hw; exact hw)
  | _, _, .fsub _, (_, _, ()), _, hw =>
    liftFloatRel2_exists_ite _ (by simp only [OpCode.wp_fsub] at hw; exact hw)
  | _, _, .fmul _, (_, _, ()), _, hw =>
    liftFloatRel2_exists_ite _ (by simp only [OpCode.wp_fmul] at hw; exact hw)
  | _, _, .fdiv _, (_, _, ()), _, hw =>
    liftFloatRel2_exists_ite _ (by simp only [OpCode.wp_fdiv] at hw; exact hw)
  | _, _, .ffma t, (a, b, c, ()), P, hw => by
    simp only [OpCode.wp_ffma] at hw
    cases ht : t.isFloatTree
    · simp only [ht, Bool.not_false, ↓reduceIte] at hw
    · simp only [ht, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw
      obtain ⟨r, hr⟩ := liftFloatRel3_exists Float.Model.UnpackedFloat.fma t ht a b c
        (fun x => P (x, ())) hw
      exact ⟨(r, ()), hr⟩
  | _, _, .fsqrt t, (a, ()), P, hw => by
    simp only [OpCode.wp_fsqrt] at hw
    cases ht : t.isFloatTree
    · simp only [ht, Bool.not_false, ↓reduceIte] at hw
    · simp only [ht, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hw
      obtain ⟨r, hr⟩ := liftFloatRel1_exists Float.Model.UnpackedFloat.sqrt t ht a
        (fun x => P (x, ())) hw
      exact ⟨(r, ()), hr⟩
  | _, _, .fneg _, (_, ()), _, hw =>
    of_isFloatTree_exists (by simp only [OpCode.wp_fneg] at hw; exact hw)
  | _, _, .fabs _, (_, ()), _, hw =>
    of_isFloatTree_exists (by simp only [OpCode.wp_fabs] at hw; exact hw)
  | _, _, .fcmp _ _ _ rfl, (_, _, ()), _, hw =>
    of_isFloatTree_exists (by simp only [OpCode.wp_fcmp, cast_eq] at hw; exact hw)
  | _, _, .fptoui f n, (a, ()), _, hw => by
    simp only [OpCode.wp_fptoui] at hw
    cases htr : truncToInt (unpackFloat f a) with
    | none => simp only [htr] at hw
    | some _ => simp only [htr] at hw; exact ⟨_, hw.2.2⟩
  | _, _, .fptosi f n, (a, ()), _, hw => by
    simp only [OpCode.wp_fptosi] at hw
    have hw2 := hw.2
    cases htr : truncToInt (unpackFloat f a) with
    | none => simp only [htr] at hw2
    | some _ => simp only [htr] at hw2; exact ⟨_, hw2.2.2⟩
  | _, _, .fcvt f g, (a, ()), P, hw => by
    simp only [OpCode.wp_fcvt] at hw
    obtain ⟨r, hr⟩ := convertFloat_exists f g a (fun x => P (x, ())) hw
    exact ⟨(r, ()), hr⟩
  | _, _, .copy _, (_, ()), _, hw | _, _, .and _, (_, _, ()), _, hw
  | _, _, .or _, (_, _, ()), _, hw | _, _, .xor _, (_, _, ()), _, hw
  | _, _, .not _, (_, ()), _, hw | _, _, .ternlog _ _, (_, _, _, ()), _, hw
  | _, _, .fshl _, (_, _, _, ()), _, hw | _, _, .fshr _, (_, _, _, ()), _, hw
  | _, _, .clz _, (_, ()), _, hw | _, _, .cls _, (_, ()), _, hw
  | _, _, .rbit _, (_, ()), _, hw | _, _, .ctz _, (_, ()), _, hw
  | _, _, .popcnt _, (_, ()), _, hw | _, _, .select _, (_, _, _, ()), _, hw
  | _, _, .blend _ _ rfl, (_, _, _, ()), _, hw => ⟨_, hw⟩
  | _, _, .ofBool _, (_, ()), _, hw
  | _, _, .addc _, (_, _, _, ()), _, hw | _, _, .subb _, (_, _, _, ()), _, hw
  | _, _, .umulw _, (_, _, ()), _, hw | _, _, .smulw _, (_, _, ()), _, hw
  | _, _, .udiv0 _, (_, _, ()), _, hw | _, _, .sdiv0 _, (_, _, ()), _, hw
  | _, _, .mkpair _ _, (_, _, ()), _, hw | _, _, .unpair _ _, (_, ()), _, hw
  | _, _, .bitcast _ _ _, (_, ()), _, hw | _, _, .sha256rnds2, (_, _, _, ()), _, hw
  | _, _, .sha256msg1, (_, _, ()), _, hw | _, _, .sha256msg2, (_, _, ()), _, hw
  | _, _, .uitofp _ _, (_, ()), _, hw | _, _, .sitofp _ _, (_, ()), _, hw => ⟨_, hw⟩

/-! ## Block liveness and sweep access lemmas -/

theorem liveVarsBWith_sub (dropLets dropLoads : Bool) {rs : List Ty} (b : Nat) :
    {sig : List (List Ty)} → (bk : Blocks K KL0 rs sig) → {ts : List Ty} → (i : Member ts sig) →
    TrieSub (liveVarsWith dropLets dropLoads (b + ts.length) (bk.get i (Tup.levels ts b))).1
      (liveVarsBWith dropLets dropLoads b bk).1
  | _ :: _, .cons _ _, _, .here =>
    TrieSub.union_left _ _
  | _ :: _, .cons _ tl, _, .there i =>
    TrieSub.trans (liveVarsBWith_sub dropLets dropLoads b tl i) (TrieSub.union_right _ _)

theorem dceSweepB_liveVarsBWith_get (dropLets dropLoads : Bool)
    {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (b : Nat) :
    {sig : List (List Ty)} → (bk : Blocks K KL0 rs sig) → (bs : Blocks (OptV V) L rs sig) →
    ∀ {ts : List Ty} (i : Member ts sig) (xs : Tup V ts),
    (dceSweepB (liveVarsBWith dropLets dropLoads b bk).2 bs).get i xs =
      dceSweep (liveVarsWith dropLets dropLoads (b + ts.length) (bk.get i (Tup.levels ts b))).2
        (bs.get i (someTup ts xs))
  | _ :: _, .cons _ _, .cons _ _, _, .here, _ => rfl
  | _ :: _, .cons _ bkt, .cons _ bst, _, .there i', xs =>
    dceSweepB_liveVarsBWith_get dropLets dropLoads b bkt bst i' xs

/-! ## `dceWith_wp` and `dceWith_wf` via `Wf.induct` -/

/-- Weakest-precondition preservation for `dceSweep`, proved via `Wf.induct`. -/
theorem dceWith_wp (dropLets dropLoads : Bool) {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx (OptV Val) Val} {D : Ctx Cont Cont}
    {e₁ : Expr (OptV Val) Cont rs} {e₂ : Expr Val Cont rs}
    (hwf : Wf G D e₁ e₂) :
    (∀ p ∈ D, p.2.1 = p.2.2) →
    SomeEq G →
    ∀ {Gk : Ctx K (OptV Val)} {Dk : Ctx KL0 Cont} (b : Nat) (ek : Expr K KL0 rs),
      Wf Gk Dk ek e₁ → NoneDead (liveVarsWith dropLets dropLoads b ek).1 Gk →
      ∀ m, wp Γ Q X e₂ m →
        wp Γ Q X (dceSweep (liveVarsWith dropLets dropLoads b ek).2 e₁) m := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop₁₂ _ ih =>
    intro hD hG Gk Dk b ek hwk hnd m hw
    rcases hwk.rhs_let with ⟨opk, kk, rfl, hopk, hkk⟩
    cases hop₁₂ with
    | @mk sig _ code args₁ args₂ hargs₁₂ =>
      cases hopk with
      | @mk _ _ _ argsk _ hargsk =>
        simp only [liveVarsWith] at hnd ⊢
        cases hkeep : (!dropLets || anyLive b ts.length
            (liveVarsWith dropLets dropLoads (b + ts.length) (kk (Tup.levels ts b))).1) with
        | true =>
          simp only [hkeep, ↓reduceIte] at hnd ⊢
          simp only [dceSweep, wp, Op.wp] at hw ⊢
          have hvals : vals (argsSweep args₁) = vals args₂ :=
            argsSweep_vals_of_inSet hnd hG hargsk hargs₁₂
              (ArgsInSet.addArgKeys argsk _)
          rw [hvals]
          refine OpCode.wp_mono code (vals args₂) (fun xs hkx => ?_) hw
          have hsub : TrieSub
              (liveVarsWith dropLets dropLoads (b + ts.length) (kk (Tup.levels ts b))).1
              (addArgKeys argsk
                (liveVarsWith dropLets dropLoads (b + ts.length) (kk (Tup.levels ts b))).1) :=
            TrieSub.addArgKeys argsk _
          exact ih (someTup ts xs) xs hD (SomeEq.append_some hG xs)
            (b + ts.length) (kk (Tup.levels ts b))
            (hkk (Tup.levels ts b) (someTup ts xs))
            (NoneDead.append_some (NoneDead.sub hsub hnd) (Tup.levels ts b) xs) m hkx
        | false =>
          simp only [hkeep, Bool.false_eq_true, ↓reduceIte] at hnd ⊢
          have hal : anyLive b ts.length
              (liveVarsWith dropLets dropLoads (b + ts.length) (kk (Tup.levels ts b))).1 =
              false := by
            cases dropLets <;> simp at hkeep ⊢; exact hkeep
          simp only [dceSweep]
          simp only [wp, Op.wp] at hw
          obtain ⟨xs₂, hxs₂⟩ := OpCode.wp_exists code (vals args₂) hw
          exact ih (noneTup ts) xs₂ hD (SomeEq.append_none hG xs₂)
            (b + ts.length) (kk (Tup.levels ts b))
            (hkk (Tup.levels ts b) (noneTup ts))
            (NoneDead.append_none hnd b (anyLive_eq_false ts.length b _ hal)) m hxs₂
  | load t ha _ ih =>
    intro hD hG Gk Dk b ek hwk hnd m hw
    rcases hwk.rhs_load with ⟨ak, kk, rfl, hak, hkk⟩
    simp only [liveVarsWith] at hnd ⊢
    rcases hw with ⟨v, hv, hk⟩
    cases hkeep : (!dropLoads ||
        ((liveVarsWith dropLets dropLoads (b + 1) (kk b)).1.find? b).isSome) with
    | true =>
      simp only [hkeep, ↓reduceIte] at hnd ⊢
      simp only [dceSweep, wp]
      have hval := argSweep_val_of_inSet hnd hG hak ha (Arg.InSet.addArgKey ak _)
      rw [hval]
      refine ⟨v, hv, ?_⟩
      have hsub : TrieSub (liveVarsWith dropLets dropLoads (b + 1) (kk b)).1
          (addArgKey ak (liveVarsWith dropLets dropLoads (b + 1) (kk b)).1) :=
        TrieSub.addArgKey ak _
      exact ih (some v) v hD (SomeEq.cons_some hG v) (b + 1) (kk b) (hkk b (some v))
        (NoneDead.cons_some (NoneDead.sub hsub hnd) b v) m hk
    | false =>
      simp only [hkeep, Bool.false_eq_true, ↓reduceIte] at hnd ⊢
      have hmem : ((liveVarsWith dropLets dropLoads (b + 1) (kk b)).1.find? b).isSome =
          false := by
        cases dropLoads <;> simp at hkeep ⊢; exact hkeep
      simp only [dceSweep]
      exact ih none v hD (SomeEq.cons_none hG v) (b + 1) (kk b) (hkk b none)
        (NoneDead.cons_none hnd b hmem) m hk
  | store hv ha _ ih =>
    intro hD hG Gk Dk b ek hwk hnd m hw
    rcases hwk.rhs_store with ⟨vk, ak, kk, rfl, hvk, hak, hkk⟩
    simp only [liveVarsWith] at hnd ⊢
    simp only [dceSweep, wp] at hw ⊢
    have hvval := argSweep_val_of_inSet hnd hG hvk hv (Arg.InSet.addArgKey vk _)
    have haval := argSweep_val_of_inSet hnd hG hak ha
      ((Arg.InSet.addArgKey ak _).mono (TrieSub.addArgKey vk _))
    rw [hvval, haval]
    refine ⟨hw.1, ?_⟩
    have hsub : TrieSub (liveVarsWith dropLets dropLoads b kk).1
        (addArgKey vk (addArgKey ak (liveVarsWith dropLets dropLoads b kk).1)) :=
      TrieSub.trans (TrieSub.addArgKey ak _) (TrieSub.addArgKey vk _)
    exact ih hD hG b kk hkk (hnd.sub hsub) _ hw.2
  | @call _ _ f _ bs _ _ _ _ hargs _ ih =>
    intro hD hG Gk Dk b ek hwk hnd m hw
    rcases hwk.rhs_call with ⟨argsk, kk, rfl, hargsk, hkk⟩
    simp only [liveVarsWith] at hnd ⊢
    simp only [dceSweep, wp] at hw ⊢
    rcases hw with ⟨P, E, hΓ, hP, hE⟩
    have hvals := argsSweep_vals_of_inSet hnd hG hargsk hargs (ArgsInSet.addArgKeys argsk _)
    rw [hvals]
    refine ⟨P, E, hΓ, fun r m' hp => ?_, hE⟩
    have hsub : TrieSub (liveVarsWith dropLets dropLoads (b + bs.length) (kk (Tup.levels bs b))).1
        (addArgKeys argsk
          (liveVarsWith dropLets dropLoads (b + bs.length) (kk (Tup.levels bs b))).1) :=
      TrieSub.addArgKeys argsk _
    exact ih (someTup bs r) r hD (SomeEq.append_some hG r) (b + bs.length) (kk (Tup.levels bs b))
      (hkk (Tup.levels bs b) (someTup bs r))
      (NoneDead.append_some (NoneDead.sub hsub hnd) (Tup.levels bs b) r) m' (hP r m' hp)
  | jnz hc _ _ iht ihe =>
    intro hD hG Gk Dk b ek hwk hnd m hw
    rcases hwk.rhs_jnz with ⟨ck, tk, ek', rfl, hck, htk, hek⟩
    simp only [liveVarsWith] at hnd ⊢
    simp only [dceSweep, wp] at hw ⊢
    have hval := argSweep_val_of_inSet hnd hG hck hc (Arg.InSet.addArgKey ck _)
    rw [hval]
    have hsub_t : TrieSub (liveVarsWith dropLets dropLoads b tk).1
        (addArgKey ck (trieUnion (liveVarsWith dropLets dropLoads b tk).1
          (liveVarsWith dropLets dropLoads b ek').1)) :=
      TrieSub.trans (TrieSub.union_left _ _) (TrieSub.addArgKey ck _)
    have hsub_e : TrieSub (liveVarsWith dropLets dropLoads b ek').1
        (addArgKey ck (trieUnion (liveVarsWith dropLets dropLoads b tk).1
          (liveVarsWith dropLets dropLoads b ek').1)) :=
      TrieSub.trans (TrieSub.union_right _ _) (TrieSub.addArgKey ck _)
    exact ⟨fun h => iht hD hG b tk htk (hnd.sub hsub_t) m (hw.1 h),
           fun h => ihe hD hG b ek' hek (hnd.sub hsub_e) m (hw.2 h)⟩
  | jump hj hargs =>
    intro hD hG Gk Dk b ek hwk hnd m hw
    rcases hwk.rhs_jump with ⟨jk, argsk, rfl, _, hargsk⟩
    have hj' := hD _ hj; dsimp only at hj'
    simp only [liveVarsWith] at hnd ⊢
    simp only [dceSweep, wp] at hw ⊢
    have hvals := argsSweep_vals_of_inSet hnd hG hargsk hargs (ArgsInSet.addArgKeys argsk _)
    rw [hj', hvals]
    exact hw
  | ret hvs =>
    intro _ hG Gk Dk b ek hwk hnd m hw
    rcases hwk.rhs_ret with ⟨vsk, rfl, hvsk⟩
    simp only [liveVarsWith] at hnd ⊢
    simp only [dceSweep, wp] at hw ⊢
    have hvals := argsSweep_vals_of_inSet hnd hG hvsk hvs (ArgsInSet.addArgKeys vsk _)
    rw [hvals]
    exact hw
  | exit f hargs =>
    intro _ hG Gk Dk b ek hwk hnd m hw
    rcases hwk.rhs_exit with ⟨argsk, rfl, hargsk⟩
    simp only [liveVarsWith] at hnd ⊢
    simp only [dceSweep, wp] at hw ⊢
    have hvals := argsSweep_vals_of_inSet hnd hG hargsk hargs (ArgsInSet.addArgKeys argsk _)
    rw [hvals]
    exact hw
  | hlt =>
    intro _ _ _ _ _ _ hwk _ _ hw
    rw [hwk.rhs_hlt]
    exact hw
  | @group G D sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro hD hG Gk Dk b ek hwk hnd m hw
    rcases hwk.rhs_group with ⟨bk, kk, rfl, hbk, hkk⟩
    simp only [liveVarsWith] at hnd ⊢
    simp only [dceSweep, wp] at hw ⊢
    intro Js hclosed
    have hsub_k : TrieSub (liveVarsWith dropLets dropLoads b (kk (Tup.units sig))).1
        (trieUnion (liveVarsBWith dropLets dropLoads b (bk (Tup.units sig))).1
          (liveVarsWith dropLets dropLoads b (kk (Tup.units sig))).1) :=
      TrieSub.union_right _ _
    refine ihk Js Js (tup_zip_self_eq hD Js) hG b (kk (Tup.units sig)) (hkk (Tup.units sig) Js)
      (hnd.sub hsub_k) m (hw Js ?_)
    rw [closed_iff] at hclosed ⊢
    intro ts i xs m' hb'
    apply hclosed i xs m'
    rw [dceSweepB_liveVarsBWith_get dropLets dropLoads b (bk (Tup.units sig)) (b₁ Js) i xs]
    have hsub_b :
        TrieSub (liveVarsWith dropLets dropLoads (b + ts.length)
            ((bk (Tup.units sig)).get i (Tup.levels ts b))).1
          (trieUnion (liveVarsBWith dropLets dropLoads b (bk (Tup.units sig))).1
            (liveVarsWith dropLets dropLoads b (kk (Tup.units sig))).1) :=
      TrieSub.trans (liveVarsBWith_sub dropLets dropLoads b (bk (Tup.units sig)) i)
        (TrieSub.union_left _ _)
    exact ihb Js Js i (someTup ts xs) xs (tup_zip_self_eq hD Js) (SomeEq.append_some hG xs)
      (b + ts.length) ((bk (Tup.units sig)).get i (Tup.levels ts b))
      ((hbk (Tup.units sig) Js).get i (Tup.levels ts b) (someTup ts xs))
      (NoneDead.append_some (NoneDead.sub hsub_b hnd) (Tup.levels ts b) xs) m' hb'

/-- Well-formedness preservation for `dceSweep`, proved via `Wf.induct`. -/
theorem dceWith_wf (dropLets dropLoads : Bool)
    {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx (OptV V₁) (OptV V₂)} {D : Ctx L₁ L₂}
    {e₁ : Expr (OptV V₁) L₁ rs} {e₂ : Expr (OptV V₂) L₂ rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ {G' : Ctx V₁ V₂}, DceRel G G' →
    ∀ {Gk : Ctx K (OptV V₁)} {Dk : Ctx KL0 L₁} (b : Nat) (ek : Expr K KL0 rs),
      Wf Gk Dk ek e₁ → NoneDead (liveVarsWith dropLets dropLoads b ek).1 Gk →
      Wf G' D (dceSweep (liveVarsWith dropLets dropLoads b ek).2 e₁)
        (dceSweep (liveVarsWith dropLets dropLoads b ek).2 e₂) := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop₁₂ _ ih =>
    intro G' hrel Gk Dk b ek hwk hnd
    rcases hwk.rhs_let with ⟨opk, kk, rfl, hopk, hkk⟩
    cases hop₁₂ with
    | @mk sig _ code args₁ args₂ hargs₁₂ =>
      cases hopk with
      | @mk _ _ _ argsk _ hargsk =>
        simp only [liveVarsWith] at hnd ⊢
        cases hkeep : (!dropLets || anyLive b ts.length
            (liveVarsWith dropLets dropLoads (b + ts.length) (kk (Tup.levels ts b))).1) with
        | true =>
          simp only [hkeep, ↓reduceIte] at hnd ⊢
          simp only [dceSweep]
          refine .let_ (.mk code (TRel.argsSweep_of_inSet hnd hrel hargsk hargs₁₂
            (ArgsInSet.addArgKeys argsk _))) fun xs₁ xs₂ => ?_
          have hsub : TrieSub
              (liveVarsWith dropLets dropLoads (b + ts.length) (kk (Tup.levels ts b))).1
              (addArgKeys argsk
                (liveVarsWith dropLets dropLoads (b + ts.length) (kk (Tup.levels ts b))).1) :=
            TrieSub.addArgKeys argsk _
          exact ih (someTup ts xs₁) (someTup ts xs₂) (DceRel.append_some hrel xs₁ xs₂)
            (b + ts.length) (kk (Tup.levels ts b))
            (hkk (Tup.levels ts b) (someTup ts xs₁))
            (NoneDead.append_some (NoneDead.sub hsub hnd) (Tup.levels ts b) xs₁)
        | false =>
          simp only [hkeep, Bool.false_eq_true, ↓reduceIte] at hnd ⊢
          have hal : anyLive b ts.length
              (liveVarsWith dropLets dropLoads (b + ts.length) (kk (Tup.levels ts b))).1 =
              false := by
            cases dropLets <;> simp at hkeep ⊢; exact hkeep
          simp only [dceSweep]
          exact ih (noneTup ts) (noneTup ts) (DceRel.append_none hrel)
            (b + ts.length) (kk (Tup.levels ts b))
            (hkk (Tup.levels ts b) (noneTup ts))
            (NoneDead.append_none hnd b (anyLive_eq_false ts.length b _ hal))
  | load t ha _ ih =>
    intro G' hrel Gk Dk b ek hwk hnd
    rcases hwk.rhs_load with ⟨ak, kk, rfl, hak, hkk⟩
    simp only [liveVarsWith] at hnd ⊢
    cases hkeep : (!dropLoads ||
        ((liveVarsWith dropLets dropLoads (b + 1) (kk b)).1.find? b).isSome) with
    | true =>
      simp only [hkeep, ↓reduceIte] at hnd ⊢
      simp only [dceSweep]
      refine .load t (argSweep_rel_of_inSet hnd hrel hak ha (Arg.InSet.addArgKey ak _))
        fun v₁ v₂ => ?_
      have hsub : TrieSub (liveVarsWith dropLets dropLoads (b + 1) (kk b)).1
          (addArgKey ak (liveVarsWith dropLets dropLoads (b + 1) (kk b)).1) :=
        TrieSub.addArgKey ak _
      exact ih (some v₁) (some v₂) (DceRel.cons_some hrel v₁ v₂) (b + 1) (kk b)
        (hkk b (some v₁)) (NoneDead.cons_some (NoneDead.sub hsub hnd) b v₁)
    | false =>
      simp only [hkeep, Bool.false_eq_true, ↓reduceIte] at hnd ⊢
      have hmem : ((liveVarsWith dropLets dropLoads (b + 1) (kk b)).1.find? b).isSome =
          false := by
        cases dropLoads <;> simp at hkeep ⊢; exact hkeep
      simp only [dceSweep]
      exact ih none none (DceRel.cons_none hrel) (b + 1) (kk b) (hkk b none)
        (NoneDead.cons_none hnd b hmem)
  | store hv ha _ ih =>
    intro G' hrel Gk Dk b ek hwk hnd
    rcases hwk.rhs_store with ⟨vk, ak, kk, rfl, hvk, hak, hkk⟩
    simp only [liveVarsWith] at hnd ⊢
    simp only [dceSweep]
    have hsub : TrieSub (liveVarsWith dropLets dropLoads b kk).1
        (addArgKey vk (addArgKey ak (liveVarsWith dropLets dropLoads b kk).1)) :=
      TrieSub.trans (TrieSub.addArgKey ak _) (TrieSub.addArgKey vk _)
    exact .store (argSweep_rel_of_inSet hnd hrel hvk hv (Arg.InSet.addArgKey vk _))
      (argSweep_rel_of_inSet hnd hrel hak ha
        ((Arg.InSet.addArgKey ak _).mono (TrieSub.addArgKey vk _)))
      (ih hrel b kk hkk (hnd.sub hsub))
  | @call _ _ f _ bs _ _ _ _ hargs _ ih =>
    intro G' hrel Gk Dk b ek hwk hnd
    rcases hwk.rhs_call with ⟨argsk, kk, rfl, hargsk, hkk⟩
    simp only [liveVarsWith] at hnd ⊢
    simp only [dceSweep]
    refine .call f (TRel.argsSweep_of_inSet hnd hrel hargsk hargs (ArgsInSet.addArgKeys argsk _))
      fun xs₁ xs₂ => ?_
    have hsub : TrieSub (liveVarsWith dropLets dropLoads (b + bs.length) (kk (Tup.levels bs b))).1
        (addArgKeys argsk
          (liveVarsWith dropLets dropLoads (b + bs.length) (kk (Tup.levels bs b))).1) :=
      TrieSub.addArgKeys argsk _
    exact ih (someTup bs xs₁) (someTup bs xs₂) (DceRel.append_some hrel xs₁ xs₂)
      (b + bs.length) (kk (Tup.levels bs b)) (hkk (Tup.levels bs b) (someTup bs xs₁))
      (NoneDead.append_some (NoneDead.sub hsub hnd) (Tup.levels bs b) xs₁)
  | jnz hc _ _ iht ihe =>
    intro G' hrel Gk Dk b ek hwk hnd
    rcases hwk.rhs_jnz with ⟨ck, tk, ek', rfl, hck, htk, hek⟩
    simp only [liveVarsWith] at hnd ⊢
    simp only [dceSweep]
    have hsub_t : TrieSub (liveVarsWith dropLets dropLoads b tk).1
        (addArgKey ck (trieUnion (liveVarsWith dropLets dropLoads b tk).1
          (liveVarsWith dropLets dropLoads b ek').1)) :=
      TrieSub.trans (TrieSub.union_left _ _) (TrieSub.addArgKey ck _)
    have hsub_e : TrieSub (liveVarsWith dropLets dropLoads b ek').1
        (addArgKey ck (trieUnion (liveVarsWith dropLets dropLoads b tk).1
          (liveVarsWith dropLets dropLoads b ek').1)) :=
      TrieSub.trans (TrieSub.union_right _ _) (TrieSub.addArgKey ck _)
    exact .jnz (argSweep_rel_of_inSet hnd hrel hck hc (Arg.InSet.addArgKey ck _))
      (iht hrel b tk htk (hnd.sub hsub_t))
      (ihe hrel b ek' hek (hnd.sub hsub_e))
  | jump hj hargs =>
    intro G' hrel Gk Dk b ek hwk hnd
    rcases hwk.rhs_jump with ⟨jk, argsk, rfl, _, hargsk⟩
    simp only [liveVarsWith] at hnd ⊢
    simp only [dceSweep]
    exact .jump hj (TRel.argsSweep_of_inSet hnd hrel hargsk hargs (ArgsInSet.addArgKeys argsk _))
  | ret hvs =>
    intro G' hrel Gk Dk b ek hwk hnd
    rcases hwk.rhs_ret with ⟨vsk, rfl, hvsk⟩
    simp only [liveVarsWith] at hnd ⊢
    simp only [dceSweep]
    exact .ret (TRel.argsSweep_of_inSet hnd hrel hvsk hvs (ArgsInSet.addArgKeys vsk _))
  | exit f hargs =>
    intro G' hrel Gk Dk b ek hwk hnd
    rcases hwk.rhs_exit with ⟨argsk, rfl, hargsk⟩
    simp only [liveVarsWith] at hnd ⊢
    simp only [dceSweep]
    exact .exit f (TRel.argsSweep_of_inSet hnd hrel hargsk hargs (ArgsInSet.addArgKeys argsk _))
  | hlt =>
    intro _ _ _ _ _ ek hwk _
    rw [hwk.rhs_hlt]
    exact .hlt
  | @group G D sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro G' hrel Gk Dk b ek hwk hnd
    rcases hwk.rhs_group with ⟨bk, kk, rfl, hbk, hkk⟩
    simp only [liveVarsWith] at hnd ⊢
    simp only [dceSweep]
    have hsub_k : TrieSub (liveVarsWith dropLets dropLoads b (kk (Tup.units sig))).1
        (trieUnion (liveVarsBWith dropLets dropLoads b (bk (Tup.units sig))).1
          (liveVarsWith dropLets dropLoads b (kk (Tup.units sig))).1) :=
      TrieSub.union_right _ _
    refine .group (fun Js₁ Js₂ => WfB.of_get fun {ts} i xs₁ xs₂ => ?_)
      (fun Js₁ Js₂ => ihk Js₁ Js₂ hrel b (kk (Tup.units sig)) (hkk (Tup.units sig) Js₁)
        (hnd.sub hsub_k))
    rw [dceSweepB_liveVarsBWith_get dropLets dropLoads b (bk (Tup.units sig)) (b₁ Js₁) i xs₁,
        dceSweepB_liveVarsBWith_get dropLets dropLoads b (bk (Tup.units sig)) (b₂ Js₂) i xs₂]
    have hsub_b :
        TrieSub (liveVarsWith dropLets dropLoads (b + ts.length)
            ((bk (Tup.units sig)).get i (Tup.levels ts b))).1
          (trieUnion (liveVarsBWith dropLets dropLoads b (bk (Tup.units sig))).1
            (liveVarsWith dropLets dropLoads b (kk (Tup.units sig))).1) :=
      TrieSub.trans (liveVarsBWith_sub dropLets dropLoads b (bk (Tup.units sig)) i)
        (TrieSub.union_left _ _)
    exact ihb Js₁ Js₂ i (someTup ts xs₁) (someTup ts xs₂) (DceRel.append_some hrel xs₁ xs₂)
      (b + ts.length) ((bk (Tup.units sig)).get i (Tup.levels ts b))
      ((hbk (Tup.units sig) Js₁).get i (Tup.levels ts b) (someTup ts xs₁))
      (NoneDead.append_some (NoneDead.sub hsub_b hnd) _ _)

theorem dce_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx (OptV Val) Val} {D : Ctx Cont Cont}
    {e₁ : Expr (OptV Val) Cont rs} {e₂ : Expr Val Cont rs}
    (hwf : Wf G D e₁ e₂) :
    (∀ p ∈ D, p.2.1 = p.2.2) →
    SomeEq G →
    ∀ {Gk : Ctx K (OptV Val)} {Dk : Ctx KL0 Cont} (b : Nat) (ek : Expr K KL0 rs),
      Wf Gk Dk ek e₁ → NoneDead (liveVarsWith true false b ek).1 Gk →
      ∀ m, wp Γ Q X e₂ m → wp Γ Q X (dceSweep (liveVarsWith true false b ek).2 e₁) m :=
  dceWith_wp true false hwf

theorem dce_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx (OptV V₁) (OptV V₂)} {D : Ctx L₁ L₂}
    {e₁ : Expr (OptV V₁) L₁ rs} {e₂ : Expr (OptV V₂) L₂ rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ {G' : Ctx V₁ V₂}, DceRel G G' →
    ∀ {Gk : Ctx K (OptV V₁)} {Dk : Ctx KL0 L₁} (b : Nat) (ek : Expr K KL0 rs),
      Wf Gk Dk ek e₁ → NoneDead (liveVarsWith true false b ek).1 Gk →
      Wf G' D (dceSweep (liveVarsWith true false b ek).2 e₁)
        (dceSweep (liveVarsWith true false b ek).2 e₂) :=
  dceWith_wf true false hwf

/-! ## Closed functions -/

private theorem NoneDead.fresh_nil {V : Ty → Type} (s : Trie Unit) {as : List Ty} (xs : Tup V as) :
    NoneDead s (Tup.zip (Tup.levels as 0) (someTup as xs)) := by
  rw [← List.append_nil (Tup.zip (Tup.levels as 0) (someTup as xs))]
  exact NoneDead.append_some (Gk := []) (fun {_ _ _} hm => nomatch hm) (Tup.levels as 0) xs

theorem Func.dceWith_wf (dropLets dropLoads : Bool) {as rs : List Ty} {f : Func as rs}
    (hf : f.Wf) : (Func.dceWith dropLets dropLoads f).Wf := by
  intro V₁ V₂ L₁ L₂ xs₁ xs₂
  have hrel : DceRel (Tup.zip (someTup as xs₁) (someTup as xs₂)) (Tup.zip xs₁ xs₂) := by
    rw [← List.append_nil (Tup.zip (someTup as xs₁) (someTup as xs₂)),
        ← List.append_nil (Tup.zip xs₁ xs₂)]
    exact DceRel.append_some (G := []) (G' := []) (fun {_ _ _} hm => nomatch hm) xs₁ xs₂
  exact LeanQbe.T.dceWith_wf dropLets dropLoads
    (hf (OptV V₁) (OptV V₂) L₁ L₂ (someTup as xs₁) (someTup as xs₂))
    hrel as.length (f K KL0 (Tup.levels as 0))
    (hf K (OptV V₁) KL0 L₁ (Tup.levels as 0) (someTup as xs₁)) (NoneDead.fresh_nil _ xs₁)

theorem Func.dceWith_spec (dropLets dropLoads : Bool) {as rs : List Ty} {f : Func as rs}
    (hf : f.Wf) {Γ : Env} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.dceWith dropLets dropLoads f) xs m Q X := by
  have hG : SomeEq (Tup.zip (someTup as xs) xs) := by
    rw [← List.append_nil (Tup.zip (someTup as xs) xs)]
    exact SomeEq.append_some (G := []) (fun {_ _ _} hm => nomatch hm) xs
  exact LeanQbe.T.dceWith_wp dropLets dropLoads
    (hf (OptV Val) Val Cont Cont (someTup as xs) xs)
    (fun _ hm => nomatch hm) hG as.length (f K KL0 (Tup.levels as 0))
    (hf K (OptV Val) KL0 Cont (Tup.levels as 0) (someTup as xs)) (NoneDead.fresh_nil _ xs) m h

theorem Func.dce_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) : (Func.dce f).Wf :=
  Func.dceWith_wf true false hf

/-- DCE refines function contracts: any source contract holds on `Func.dce f`. -/
theorem Func.dce_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.dce f) xs m Q X :=
  Func.dceWith_spec true false hf h

theorem Func.deadLoadElim_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) :
    (Func.deadLoadElim f).Wf :=
  Func.dceWith_wf false true hf

/-- Dead-load elimination refines function contracts: any source contract holds on
`Func.deadLoadElim f`. -/
theorem Func.deadLoadElim_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.deadLoadElim f) xs m Q X :=
  Func.dceWith_spec false true hf h

end LeanQbe.T

