module

public import LeanQbe.T.Dce
public import LeanQbe.T.OptUtil
public import LeanQbe.T.WfLemmas
public import LeanQbe.T.WPLemmas

/-!
# Soundness and Relational Well-Formedness of Dead-Code Elimination (`T6`)

* `Trie Unit` / `trieUnion` liveness correctness (`TrieSub`, `anyLive_eq_false`, `addArgKeys`
  lemmas).
* `OpCode.wp_exists`: any satisfied `OpCode.wp` guarantees existence of output tuples (exhibiting
  the canonical quiet NaN witness via `isFloatNaN_packedNaN` when quantifiers arise from NaNs,
  and discharging undefined behavior by `False.elim`).
* `dce_wp` and `dce_wf`, both proved via `Wf.induct`.
* `Func.dce_wf` and `Func.dce_spec` for closed functions.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## `Trie Unit`, `trieUnion`, `anyLive`, and `addArgKeys` lemmas -/

theorem find?_trieUnion : ∀ (t₁ t₂ : Trie Unit) (x : Nat),
    (trieUnion t₁ t₂).find? x = (t₁.find? x).or (t₂.find? x)
  | .empty, t₂, x => by simp [trieUnion]
  | .node _ _ _, .empty, _ => by simp [trieUnion]
  | .node (some ()) _ _, .node _ _ _, 0 => rfl
  | .node none _ _, .node _ _ _, 0 => rfl
  | .node (some ()) e₁ o₁, .node _ e₂ o₂, x + 1 => by
    simp only [trieUnion, Trie.find?]
    split <;> exact find?_trieUnion _ _ (x / 2)
  | .node none e₁ o₁, .node _ e₂ o₂, x + 1 => by
    simp only [trieUnion, Trie.find?]
    split <;> exact find?_trieUnion _ _ (x / 2)

theorem trieMem_union_left {t₁ t₂ : Trie Unit} {x : Nat}
    (h : (t₁.find? x).isSome = true) : ((trieUnion t₁ t₂).find? x).isSome = true := by
  rw [find?_trieUnion]; cases h₁ : t₁.find? x <;> simp_all

theorem trieMem_union_right {t₁ t₂ : Trie Unit} {x : Nat}
    (h : (t₂.find? x).isSome = true) : ((trieUnion t₁ t₂).find? x).isSome = true := by
  rw [find?_trieUnion]; cases h₁ : t₁.find? x <;> simp_all

/-- Subset relation on `Trie Unit` liveness sets. -/
def TrieSub (s₁ s₂ : Trie Unit) : Prop :=
  ∀ x : Nat, (s₁.find? x).isSome = true → (s₂.find? x).isSome = true

theorem TrieSub.refl (s : Trie Unit) : TrieSub s s := fun _ h => h

theorem TrieSub.trans {s₁ s₂ s₃ : Trie Unit} (h12 : TrieSub s₁ s₂) (h23 : TrieSub s₂ s₃) :
    TrieSub s₁ s₃ :=
  fun x hx => h23 x (h12 x hx)

theorem TrieSub.insert (s : Trie Unit) (i : Nat) : TrieSub s (s.insert i ()) := by
  intro x hx
  rw [Trie.find?_insert]
  split <;> simp [hx]

theorem TrieSub.union_left (s₁ s₂ : Trie Unit) : TrieSub s₁ (trieUnion s₁ s₂) :=
  fun _ h => trieMem_union_left h

theorem TrieSub.union_right (s₁ s₂ : Trie Unit) : TrieSub s₂ (trieUnion s₁ s₂) :=
  fun _ h => trieMem_union_right h

theorem TrieSub.addArgKey {t : Ty} (a : Arg K t) (s : Trie Unit) :
    TrieSub s (LeanQbe.T.addArgKey a s) := by
  cases a with
  | var i => exact TrieSub.insert s i
  | imm _ => exact TrieSub.refl s

theorem TrieSub.addArgKeys :
    {ts : List Ty} → (as : Tup (Arg K) ts) → (s : Trie Unit) →
    TrieSub s (LeanQbe.T.addArgKeys as s)
  | [], (), s => TrieSub.refl s
  | _ :: _, (a, as), s =>
    TrieSub.trans (TrieSub.addArgKeys as s)
      (TrieSub.addArgKey a (LeanQbe.T.addArgKeys as s))

theorem anyLive_eq_false :
    ∀ (k b : Nat) (s : Trie Unit), anyLive b k s = false →
      ∀ i, b ≤ i → i < b + k → (s.find? i).isSome = false
  | 0, _, _, _, _, h1, h2 => by omega
  | k + 1, b, s, h, i, h1, h2 => by
    simp only [anyLive, Bool.or_eq_false_iff] at h
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · exact h.1
    · exact anyLive_eq_false k (b + 1) s h.2 i hlt (by omega)

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

theorem liveVarsB_sub {rs : List Ty} (b : Nat) :
    {sig : List (List Ty)} → (bk : Blocks K KL0 rs sig) → {ts : List Ty} → (i : Member ts sig) →
    TrieSub (liveVars (b + ts.length) (bk.get i (Tup.levels ts b))).1 (liveVarsB b bk).1
  | _ :: _, .cons _ _, _, .here =>
    TrieSub.union_left _ _
  | _ :: _, .cons _ tl, _, .there i =>
    TrieSub.trans (liveVarsB_sub b tl i) (TrieSub.union_right _ _)

theorem dceSweepB_liveVarsB_get {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} (b : Nat) :
    {sig : List (List Ty)} → (bk : Blocks K KL0 rs sig) → (bs : Blocks (OptV V) L rs sig) →
    ∀ {ts : List Ty} (i : Member ts sig) (xs : Tup V ts),
    (dceSweepB (liveVarsB b bk).2 bs).get i xs =
      dceSweep (liveVars (b + ts.length) (bk.get i (Tup.levels ts b))).2 (bs.get i (someTup ts xs))
  | _ :: _, .cons _ _, .cons _ _, _, .here, _ => rfl
  | _ :: _, .cons _ bkt, .cons _ bst, _, .there i', xs =>
    dceSweepB_liveVarsB_get b bkt bst i' xs

/-! ## Invariants `NoneDead`, `SomeEq`, and `DceRel` -/

/-- Every dropped (`none`) binder level in `Gk` is absent from liveness set `s`. -/
def NoneDead {V : Ty → Type} (s : Trie Unit) (Gk : Ctx K (OptV V)) : Prop :=
  ∀ {t : Ty} {k : Nat} {o : OptV V t}, ⟨t, k, o⟩ ∈ Gk → o = none → (s.find? k).isSome = false

theorem NoneDead.sub {V : Ty → Type} {s₁ s₂ : Trie Unit} {Gk : Ctx K (OptV V)}
    (hsub : TrieSub s₁ s₂) (hnd : NoneDead s₂ Gk) : NoneDead s₁ Gk := by
  intro t k o hm ho
  cases hmem : (s₁.find? k).isSome with
  | false => rfl
  | true =>
    have hmem2 := hsub k hmem
    have hf := hnd hm ho
    rw [hf] at hmem2
    cases hmem2

theorem NoneDead.cons_some {V : Ty → Type} {s : Trie Unit} {Gk : Ctx K (OptV V)}
    (hnd : NoneDead s Gk) {t : Ty} (k : Nat) (v : V t) :
    NoneDead s (⟨t, k, some v⟩ :: Gk) := by
  intro t' k' o hm ho
  cases hm with
  | head => cases ho
  | tail _ hm' => exact hnd hm' ho

theorem NoneDead.append_some {V : Ty → Type} {s : Trie Unit} {Gk : Ctx K (OptV V)}
    (hnd : NoneDead s Gk) :
    {ts : List Ty} → (ks : Tup K ts) → (xs : Tup V ts) →
    NoneDead s (Tup.zip ks (someTup ts xs) ++ Gk)
  | [], (), () => hnd
  | _ :: _, (k, ks), (x, xs) => NoneDead.cons_some (NoneDead.append_some hnd ks xs) k x

theorem NoneDead.append_none {V : Ty → Type} {s : Trie Unit} {Gk : Ctx K (OptV V)}
    (hnd : NoneDead s Gk) :
    {ts : List Ty} → (b : Nat) → (∀ i, b ≤ i → i < b + ts.length → (s.find? i).isSome = false) →
    NoneDead s (Tup.zip (Tup.levels ts b) (noneTup (V := V) ts) ++ Gk)
  | [], _, _ => hnd
  | _ :: ts, b, hfalse => by
    simp only [Tup.levels, noneTup, Tup.zip, List.cons_append]
    intro hm ho
    cases hm with
    | head => exact hfalse _ (Nat.le_refl _) (by simp)
    | tail _ hm' =>
      exact NoneDead.append_none hnd (b + 1)
        (fun i hi1 hi2 =>
          hfalse i (Nat.le_of_succ_le hi1) (by simp only [List.length_cons] at hi2 ⊢; omega))
        hm' ho

/-- Every kept (`some`) binder in `G` agrees with its semantic value in `Val`. -/
def SomeEq (G : Ctx (OptV Val) Val) : Prop :=
  ∀ {t : Ty} {o : OptV Val t} {v : Val t}, ⟨t, o, v⟩ ∈ G → ∀ w, o = some w → w = v

theorem SomeEq.cons_some {G : Ctx (OptV Val) Val} (hG : SomeEq G) {t : Ty} (v : Val t) :
    SomeEq (⟨t, some v, v⟩ :: G) := by
  intro t' o' v' hm w hw
  cases hm with
  | head => injection hw with h; exact h.symm
  | tail _ hm' => exact hG hm' w hw

theorem SomeEq.append_some {G : Ctx (OptV Val) Val} (hG : SomeEq G) :
    {ts : List Ty} → (xs : Tup Val ts) → SomeEq (Tup.zip (someTup ts xs) xs ++ G)
  | [], () => hG
  | _ :: _, (x, xs) => SomeEq.cons_some (SomeEq.append_some hG xs) x

theorem SomeEq.append_none {G : Ctx (OptV Val) Val} (hG : SomeEq G) :
    {ts : List Ty} → (xs : Tup Val ts) → SomeEq (Tup.zip (noneTup ts) xs ++ G)
  | [], () => hG
  | _ :: ts, (_, xs) => by
    simp only [noneTup, Tup.zip, List.cons_append]
    intro hm w hw
    cases hm with
    | head => cases hw
    | tail _ hm' => exact SomeEq.append_none hG xs hm' w hw

/-- Lockstep `Option` binder invariant for `dce_wf`: either both sides were dropped (`none, none`)
or both sides are kept (`some v₁, some v₂`) and related in `G'`. -/
def DceRel {V₁ V₂ : Ty → Type} (G : Ctx (OptV V₁) (OptV V₂)) (G' : Ctx V₁ V₂) : Prop :=
  ∀ {t : Ty} {o₁ : OptV V₁ t} {o₂ : OptV V₂ t}, ⟨t, o₁, o₂⟩ ∈ G →
    (o₁ = none ∧ o₂ = none) ∨ ∃ v₁ v₂, o₁ = some v₁ ∧ o₂ = some v₂ ∧ ⟨t, v₁, v₂⟩ ∈ G'

theorem DceRel.weaken {V₁ V₂ : Ty → Type} {G : Ctx (OptV V₁) (OptV V₂)} {G₁ G₂ : Ctx V₁ V₂}
    (hsub : ∀ p ∈ G₁, p ∈ G₂) (hrel : DceRel G G₁) : DceRel G G₂ := by
  intro t o₁ o₂ hm
  rcases hrel hm with h | ⟨v₁, v₂, h1, h2, hmem⟩
  · exact Or.inl h
  · exact Or.inr ⟨v₁, v₂, h1, h2, hsub _ hmem⟩

theorem DceRel.cons_some {V₁ V₂ : Ty → Type} {G : Ctx (OptV V₁) (OptV V₂)} {G' : Ctx V₁ V₂}
    (hrel : DceRel G G') {t : Ty} (v₁ : V₁ t) (v₂ : V₂ t) :
    DceRel (⟨t, some v₁, some v₂⟩ :: G) (⟨t, v₁, v₂⟩ :: G') := by
  intro t' o₁ o₂ hm
  cases hm with
  | head => exact Or.inr ⟨v₁, v₂, rfl, rfl, List.mem_cons_self⟩
  | tail _ hm' =>
    exact (hrel.weaken (fun _ hp => List.mem_cons_of_mem _ hp)) hm'

theorem DceRel.append_some {V₁ V₂ : Ty → Type} {G : Ctx (OptV V₁) (OptV V₂)} {G' : Ctx V₁ V₂}
    (hrel : DceRel G G') :
    {ts : List Ty} → (xs₁ : Tup V₁ ts) → (xs₂ : Tup V₂ ts) →
    DceRel (Tup.zip (someTup ts xs₁) (someTup ts xs₂) ++ G) (Tup.zip xs₁ xs₂ ++ G')
  | [], (), () => hrel
  | _ :: _, (x₁, xs₁), (x₂, xs₂) => DceRel.cons_some (DceRel.append_some hrel xs₁ xs₂) x₁ x₂

theorem DceRel.append_none {V₁ V₂ : Ty → Type} {G : Ctx (OptV V₁) (OptV V₂)} {G' : Ctx V₁ V₂}
    (hrel : DceRel G G') :
    {ts : List Ty} → DceRel (Tup.zip (noneTup (V := V₁) ts) (noneTup (V := V₂) ts) ++ G) G'
  | [] => hrel
  | _ :: ts => by
    simp only [noneTup, Tup.zip, List.cons_append]
    intro hm
    cases hm with
    | head => exact Or.inl ⟨rfl, rfl⟩
    | tail _ hm' => exact DceRel.append_none hrel hm'

/-! ## Operand liveness predicates and transport lemmas -/

def Arg.InSet (s : Trie Unit) {t : Ty} : Arg K t → Prop
  | .var k => (s.find? k).isSome = true
  | .imm _ => True

theorem Arg.InSet.mono {s₁ s₂ : Trie Unit} (hsub : TrieSub s₁ s₂) {t : Ty} {a : Arg K t} :
    a.InSet s₁ → a.InSet s₂ := by
  cases a with
  | var k => exact hsub k
  | imm _ => exact fun _ => trivial

theorem Arg.InSet.addArgKey {t : Ty} (a : Arg K t) (s : Trie Unit) : a.InSet (addArgKey a s) := by
  cases a with
  | var k => simp [Arg.InSet, LeanQbe.T.addArgKey]
  | imm _ => trivial

def ArgsInSet (s : Trie Unit) : {ts : List Ty} → Tup (Arg K) ts → Prop
  | [], () => True
  | _ :: _, (a, as) => a.InSet s ∧ ArgsInSet s as

theorem ArgsInSet.mono {s₁ s₂ : Trie Unit} (hsub : TrieSub s₁ s₂) :
    {ts : List Ty} → {as : Tup (Arg K) ts} → ArgsInSet s₁ as → ArgsInSet s₂ as
  | [], (), _ => trivial
  | _ :: _, (_, _), ⟨ha, has⟩ => ⟨ha.mono hsub, ArgsInSet.mono hsub has⟩

theorem ArgsInSet.addArgKeys :
    {ts : List Ty} → (as : Tup (Arg K) ts) → (s : Trie Unit) →
    ArgsInSet (LeanQbe.T.addArgKeys as s) as
  | [], (), _ => trivial
  | _ :: _, (a, as), s =>
    ⟨Arg.InSet.addArgKey a (LeanQbe.T.addArgKeys as s),
     ArgsInSet.mono (TrieSub.addArgKey a (LeanQbe.T.addArgKeys as s))
       (ArgsInSet.addArgKeys as s)⟩

theorem argSweep_val_of_inSet {s : Trie Unit} {Gk : Ctx K (OptV Val)} {G : Ctx (OptV Val) Val}
    (hnd : NoneDead s Gk) (hG : SomeEq G)
    {t : Ty} {ak : Arg K t} {a₁ : Arg (OptV Val) t} {a₂ : Arg Val t}
    (hk : ArgRel Gk t ak a₁) (h12 : ArgRel G t a₁ a₂) (hin : ak.InSet s) :
    (argSweep a₁).val = a₂.val := by
  cases h12 with
  | imm c => rfl
  | var hm12 =>
    cases hk with
    | var hmk =>
      rename_i o v k
      cases o with
      | some w =>
        have hw : w = v := hG hm12 w rfl
        subst hw
        rfl
      | none =>
        have hfalse := hnd hmk rfl
        have hkmem : (s.find? k).isSome = true := hin
        rw [hfalse] at hkmem
        cases hkmem

theorem argsSweep_vals_of_inSet {s : Trie Unit} {Gk : Ctx K (OptV Val)} {G : Ctx (OptV Val) Val}
    (hnd : NoneDead s Gk) (hG : SomeEq G) :
    {ts : List Ty} → {aks : Tup (Arg K) ts} → {as₁ : Tup (Arg (OptV Val)) ts} →
    {as₂ : Tup (Arg Val) ts} →
    TRel (ArgRel Gk) aks as₁ → TRel (ArgRel G) as₁ as₂ → ArgsInSet s aks →
    vals (argsSweep as₁) = vals as₂
  | [], (), (), (), .nil, .nil, _ => rfl
  | _ :: _, (_, _), (_, _), (_, _), .cons hka hkas, .cons h12a h12as, ⟨ha, has⟩ =>
    Prod.ext (argSweep_val_of_inSet hnd hG hka h12a ha)
      (argsSweep_vals_of_inSet hnd hG hkas h12as has)

theorem argSweep_rel_of_inSet {V₁ V₂ : Ty → Type} {s : Trie Unit}
    {Gk : Ctx K (OptV V₁)} {G : Ctx (OptV V₁) (OptV V₂)} {G' : Ctx V₁ V₂}
    (hnd : NoneDead s Gk) (hrel : DceRel G G')
    {t : Ty} {ak : Arg K t} {a₁ : Arg (OptV V₁) t} {a₂ : Arg (OptV V₂) t}
    (hk : ArgRel Gk t ak a₁) (h12 : ArgRel G t a₁ a₂) (hin : ak.InSet s) :
    ArgRel G' t (argSweep a₁) (argSweep a₂) := by
  cases h12 with
  | imm c => exact .imm c
  | var hm12 =>
    cases hk with
    | var hmk =>
      rename_i o₁ o₂ k
      rcases hrel hm12 with ⟨h1, _⟩ | ⟨v₁, v₂, h1, h2, hmem⟩
      · subst h1
        have hfalse := hnd hmk rfl
        have hkmem : (s.find? k).isSome = true := hin
        rw [hfalse] at hkmem
        cases hkmem
      · subst h1 h2
        exact .var hmem

theorem TRel.argsSweep_of_inSet {V₁ V₂ : Ty → Type} {s : Trie Unit}
    {Gk : Ctx K (OptV V₁)} {G : Ctx (OptV V₁) (OptV V₂)} {G' : Ctx V₁ V₂}
    (hnd : NoneDead s Gk) (hrel : DceRel G G') :
    {ts : List Ty} → {aks : Tup (Arg K) ts} → {as₁ : Tup (Arg (OptV V₁)) ts} →
    {as₂ : Tup (Arg (OptV V₂)) ts} →
    TRel (ArgRel Gk) aks as₁ → TRel (ArgRel G) as₁ as₂ → ArgsInSet s aks →
    TRel (ArgRel G') (argsSweep as₁) (argsSweep as₂)
  | [], (), (), (), .nil, .nil, _ => .nil
  | _ :: _, (_, _), (_, _), (_, _), .cons hka hkas, .cons h12a h12as, ⟨ha, has⟩ =>
    .cons (argSweep_rel_of_inSet hnd hrel hka h12a ha)
      (TRel.argsSweep_of_inSet hnd hrel hkas h12as has)

/-! ## `dce_wp` and `dce_wf` via `Wf.induct` -/

/-- Weakest-precondition preservation for `dceSweep`, proved via `Wf.induct`. -/
theorem dce_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx (OptV Val) Val} {D : Ctx Cont Cont}
    {e₁ : Expr (OptV Val) Cont rs} {e₂ : Expr Val Cont rs}
    (hwf : Wf G D e₁ e₂) :
    (∀ p ∈ D, p.2.1 = p.2.2) →
    SomeEq G →
    ∀ {Gk : Ctx K (OptV Val)} {Dk : Ctx KL0 Cont} (b : Nat) (ek : Expr K KL0 rs),
      Wf Gk Dk ek e₁ → NoneDead (liveVars b ek).1 Gk →
      ∀ m, wp Γ Q X e₂ m → wp Γ Q X (dceSweep (liveVars b ek).2 e₁) m := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop₁₂ _ ih =>
    intro hD hG Gk Dk b ek hwk hnd m hw
    rcases hwk.rhs_let with ⟨opk, kk, rfl, hopk, hkk⟩
    cases hop₁₂ with
    | @mk sig _ code args₁ args₂ hargs₁₂ =>
      cases hopk with
      | @mk _ _ _ argsk _ hargsk =>
        simp only [liveVars] at hnd ⊢
        cases hal : anyLive b ts.length (liveVars (b + ts.length) (kk (Tup.levels ts b))).1 with
        | true =>
          simp only [hal, ↓reduceIte] at hnd ⊢
          simp only [dceSweep, wp, Op.wp] at hw ⊢
          have hvals : vals (argsSweep args₁) = vals args₂ :=
            argsSweep_vals_of_inSet hnd hG hargsk hargs₁₂
              (ArgsInSet.addArgKeys argsk _)
          rw [hvals]
          refine OpCode.wp_mono code (vals args₂) (fun xs hkx => ?_) hw
          have hsub : TrieSub (liveVars (b + ts.length) (kk (Tup.levels ts b))).1
              (addArgKeys argsk (liveVars (b + ts.length) (kk (Tup.levels ts b))).1) :=
            TrieSub.addArgKeys argsk _
          exact ih (someTup ts xs) xs hD (SomeEq.append_some hG xs)
            (b + ts.length) (kk (Tup.levels ts b))
            (hkk (Tup.levels ts b) (someTup ts xs))
            (NoneDead.append_some (NoneDead.sub hsub hnd) (Tup.levels ts b) xs) m hkx
        | false =>
          simp only [hal, Bool.false_eq_true, ↓reduceIte] at hnd ⊢
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
    simp only [liveVars] at hnd ⊢
    simp only [dceSweep, wp] at hw ⊢
    rcases hw with ⟨v, hv, hk⟩
    have hval := argSweep_val_of_inSet hnd hG hak ha (Arg.InSet.addArgKey ak _)
    rw [hval]
    refine ⟨v, hv, ?_⟩
    have hsub : TrieSub (liveVars (b + 1) (kk b)).1 (addArgKey ak (liveVars (b + 1) (kk b)).1) :=
      TrieSub.addArgKey ak _
    exact ih (some v) v hD (SomeEq.cons_some hG v) (b + 1) (kk b) (hkk b (some v))
      (NoneDead.cons_some (NoneDead.sub hsub hnd) b v) m hk
  | store hv ha _ ih =>
    intro hD hG Gk Dk b ek hwk hnd m hw
    rcases hwk.rhs_store with ⟨vk, ak, kk, rfl, hvk, hak, hkk⟩
    simp only [liveVars] at hnd ⊢
    simp only [dceSweep, wp] at hw ⊢
    have hvval := argSweep_val_of_inSet hnd hG hvk hv (Arg.InSet.addArgKey vk _)
    have haval := argSweep_val_of_inSet hnd hG hak ha
      ((Arg.InSet.addArgKey ak _).mono (TrieSub.addArgKey vk _))
    rw [hvval, haval]
    refine ⟨hw.1, ?_⟩
    have hsub : TrieSub (liveVars b kk).1 (addArgKey vk (addArgKey ak (liveVars b kk).1)) :=
      TrieSub.trans (TrieSub.addArgKey ak _) (TrieSub.addArgKey vk _)
    exact ih hD hG b kk hkk (hnd.sub hsub) _ hw.2
  | @call _ _ f _ bs _ _ _ _ hargs _ ih =>
    intro hD hG Gk Dk b ek hwk hnd m hw
    rcases hwk.rhs_call with ⟨argsk, kk, rfl, hargsk, hkk⟩
    simp only [liveVars] at hnd ⊢
    simp only [dceSweep, wp] at hw ⊢
    rcases hw with ⟨P, E, hΓ, hP, hE⟩
    have hvals := argsSweep_vals_of_inSet hnd hG hargsk hargs (ArgsInSet.addArgKeys argsk _)
    rw [hvals]
    refine ⟨P, E, hΓ, fun r m' hp => ?_, hE⟩
    have hsub : TrieSub (liveVars (b + bs.length) (kk (Tup.levels bs b))).1
        (addArgKeys argsk (liveVars (b + bs.length) (kk (Tup.levels bs b))).1) :=
      TrieSub.addArgKeys argsk _
    exact ih (someTup bs r) r hD (SomeEq.append_some hG r) (b + bs.length) (kk (Tup.levels bs b))
      (hkk (Tup.levels bs b) (someTup bs r))
      (NoneDead.append_some (NoneDead.sub hsub hnd) (Tup.levels bs b) r) m' (hP r m' hp)
  | jnz hc _ _ iht ihe =>
    intro hD hG Gk Dk b ek hwk hnd m hw
    rcases hwk.rhs_jnz with ⟨ck, tk, ek', rfl, hck, htk, hek⟩
    simp only [liveVars] at hnd ⊢
    simp only [dceSweep, wp] at hw ⊢
    have hval := argSweep_val_of_inSet hnd hG hck hc (Arg.InSet.addArgKey ck _)
    rw [hval]
    have hsub_t : TrieSub (liveVars b tk).1
        (addArgKey ck (trieUnion (liveVars b tk).1 (liveVars b ek').1)) :=
      TrieSub.trans (TrieSub.union_left _ _) (TrieSub.addArgKey ck _)
    have hsub_e : TrieSub (liveVars b ek').1
        (addArgKey ck (trieUnion (liveVars b tk).1 (liveVars b ek').1)) :=
      TrieSub.trans (TrieSub.union_right _ _) (TrieSub.addArgKey ck _)
    exact ⟨fun h => iht hD hG b tk htk (hnd.sub hsub_t) m (hw.1 h),
           fun h => ihe hD hG b ek' hek (hnd.sub hsub_e) m (hw.2 h)⟩
  | jump hj hargs =>
    intro hD hG Gk Dk b ek hwk hnd m hw
    rcases hwk.rhs_jump with ⟨jk, argsk, rfl, _, hargsk⟩
    have hj' := hD _ hj; dsimp only at hj'
    simp only [liveVars] at hnd ⊢
    simp only [dceSweep, wp] at hw ⊢
    have hvals := argsSweep_vals_of_inSet hnd hG hargsk hargs (ArgsInSet.addArgKeys argsk _)
    rw [hj', hvals]
    exact hw
  | ret hvs =>
    intro _ hG Gk Dk b ek hwk hnd m hw
    rcases hwk.rhs_ret with ⟨vsk, rfl, hvsk⟩
    simp only [liveVars] at hnd ⊢
    simp only [dceSweep, wp] at hw ⊢
    have hvals := argsSweep_vals_of_inSet hnd hG hvsk hvs (ArgsInSet.addArgKeys vsk _)
    rw [hvals]
    exact hw
  | exit f hargs =>
    intro _ hG Gk Dk b ek hwk hnd m hw
    rcases hwk.rhs_exit with ⟨argsk, rfl, hargsk⟩
    simp only [liveVars] at hnd ⊢
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
    simp only [liveVars] at hnd ⊢
    simp only [dceSweep, wp] at hw ⊢
    intro Js hclosed
    have hsub_k : TrieSub (liveVars b (kk (Tup.units sig))).1
        (trieUnion (liveVarsB b (bk (Tup.units sig))).1 (liveVars b (kk (Tup.units sig))).1) :=
      TrieSub.union_right _ _
    refine ihk Js Js (tup_zip_self_eq hD Js) hG b (kk (Tup.units sig)) (hkk (Tup.units sig) Js)
      (hnd.sub hsub_k) m (hw Js ?_)
    rw [closed_iff] at hclosed ⊢
    intro ts i xs m' hb'
    apply hclosed i xs m'
    rw [dceSweepB_liveVarsB_get b (bk (Tup.units sig)) (b₁ Js) i xs]
    have hsub_b :
        TrieSub (liveVars (b + ts.length) ((bk (Tup.units sig)).get i (Tup.levels ts b))).1
          (trieUnion (liveVarsB b (bk (Tup.units sig))).1
            (liveVars b (kk (Tup.units sig))).1) :=
      TrieSub.trans (liveVarsB_sub b (bk (Tup.units sig)) i) (TrieSub.union_left _ _)
    exact ihb Js Js i (someTup ts xs) xs (tup_zip_self_eq hD Js) (SomeEq.append_some hG xs)
      (b + ts.length) ((bk (Tup.units sig)).get i (Tup.levels ts b))
      ((hbk (Tup.units sig) Js).get i (Tup.levels ts b) (someTup ts xs))
      (NoneDead.append_some (NoneDead.sub hsub_b hnd) (Tup.levels ts b) xs) m' hb'

/-- Well-formedness preservation for `dceSweep`, proved via `Wf.induct`. -/
theorem dce_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx (OptV V₁) (OptV V₂)} {D : Ctx L₁ L₂}
    {e₁ : Expr (OptV V₁) L₁ rs} {e₂ : Expr (OptV V₂) L₂ rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ {G' : Ctx V₁ V₂}, DceRel G G' →
    ∀ {Gk : Ctx K (OptV V₁)} {Dk : Ctx KL0 L₁} (b : Nat) (ek : Expr K KL0 rs),
      Wf Gk Dk ek e₁ → NoneDead (liveVars b ek).1 Gk →
      Wf G' D (dceSweep (liveVars b ek).2 e₁) (dceSweep (liveVars b ek).2 e₂) := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop₁₂ _ ih =>
    intro G' hrel Gk Dk b ek hwk hnd
    rcases hwk.rhs_let with ⟨opk, kk, rfl, hopk, hkk⟩
    cases hop₁₂ with
    | @mk sig _ code args₁ args₂ hargs₁₂ =>
      cases hopk with
      | @mk _ _ _ argsk _ hargsk =>
        simp only [liveVars] at hnd ⊢
        cases hal : anyLive b ts.length (liveVars (b + ts.length) (kk (Tup.levels ts b))).1 with
        | true =>
          simp only [hal, ↓reduceIte] at hnd ⊢
          simp only [dceSweep]
          refine .let_ (.mk code (TRel.argsSweep_of_inSet hnd hrel hargsk hargs₁₂
            (ArgsInSet.addArgKeys argsk _))) fun xs₁ xs₂ => ?_
          have hsub : TrieSub (liveVars (b + ts.length) (kk (Tup.levels ts b))).1
              (addArgKeys argsk (liveVars (b + ts.length) (kk (Tup.levels ts b))).1) :=
            TrieSub.addArgKeys argsk _
          exact ih (someTup ts xs₁) (someTup ts xs₂) (DceRel.append_some hrel xs₁ xs₂)
            (b + ts.length) (kk (Tup.levels ts b))
            (hkk (Tup.levels ts b) (someTup ts xs₁))
            (NoneDead.append_some (NoneDead.sub hsub hnd) (Tup.levels ts b) xs₁)
        | false =>
          simp only [hal, Bool.false_eq_true, ↓reduceIte] at hnd ⊢
          simp only [dceSweep]
          exact ih (noneTup ts) (noneTup ts) (DceRel.append_none hrel)
            (b + ts.length) (kk (Tup.levels ts b))
            (hkk (Tup.levels ts b) (noneTup ts))
            (NoneDead.append_none hnd b (anyLive_eq_false ts.length b _ hal))
  | load t ha _ ih =>
    intro G' hrel Gk Dk b ek hwk hnd
    rcases hwk.rhs_load with ⟨ak, kk, rfl, hak, hkk⟩
    simp only [liveVars] at hnd ⊢
    simp only [dceSweep]
    refine .load t (argSweep_rel_of_inSet hnd hrel hak ha (Arg.InSet.addArgKey ak _))
      fun v₁ v₂ => ?_
    have hsub : TrieSub (liveVars (b + 1) (kk b)).1 (addArgKey ak (liveVars (b + 1) (kk b)).1) :=
      TrieSub.addArgKey ak _
    exact ih (some v₁) (some v₂) (DceRel.cons_some hrel v₁ v₂) (b + 1) (kk b)
      (hkk b (some v₁)) (NoneDead.cons_some (NoneDead.sub hsub hnd) b v₁)
  | store hv ha _ ih =>
    intro G' hrel Gk Dk b ek hwk hnd
    rcases hwk.rhs_store with ⟨vk, ak, kk, rfl, hvk, hak, hkk⟩
    simp only [liveVars] at hnd ⊢
    simp only [dceSweep]
    have hsub : TrieSub (liveVars b kk).1 (addArgKey vk (addArgKey ak (liveVars b kk).1)) :=
      TrieSub.trans (TrieSub.addArgKey ak _) (TrieSub.addArgKey vk _)
    exact .store (argSweep_rel_of_inSet hnd hrel hvk hv (Arg.InSet.addArgKey vk _))
      (argSweep_rel_of_inSet hnd hrel hak ha
        ((Arg.InSet.addArgKey ak _).mono (TrieSub.addArgKey vk _)))
      (ih hrel b kk hkk (hnd.sub hsub))
  | @call _ _ f _ bs _ _ _ _ hargs _ ih =>
    intro G' hrel Gk Dk b ek hwk hnd
    rcases hwk.rhs_call with ⟨argsk, kk, rfl, hargsk, hkk⟩
    simp only [liveVars] at hnd ⊢
    simp only [dceSweep]
    refine .call f (TRel.argsSweep_of_inSet hnd hrel hargsk hargs (ArgsInSet.addArgKeys argsk _))
      fun xs₁ xs₂ => ?_
    have hsub : TrieSub (liveVars (b + bs.length) (kk (Tup.levels bs b))).1
        (addArgKeys argsk (liveVars (b + bs.length) (kk (Tup.levels bs b))).1) :=
      TrieSub.addArgKeys argsk _
    exact ih (someTup bs xs₁) (someTup bs xs₂) (DceRel.append_some hrel xs₁ xs₂)
      (b + bs.length) (kk (Tup.levels bs b)) (hkk (Tup.levels bs b) (someTup bs xs₁))
      (NoneDead.append_some (NoneDead.sub hsub hnd) (Tup.levels bs b) xs₁)
  | jnz hc _ _ iht ihe =>
    intro G' hrel Gk Dk b ek hwk hnd
    rcases hwk.rhs_jnz with ⟨ck, tk, ek', rfl, hck, htk, hek⟩
    simp only [liveVars] at hnd ⊢
    simp only [dceSweep]
    have hsub_t : TrieSub (liveVars b tk).1
        (addArgKey ck (trieUnion (liveVars b tk).1 (liveVars b ek').1)) :=
      TrieSub.trans (TrieSub.union_left _ _) (TrieSub.addArgKey ck _)
    have hsub_e : TrieSub (liveVars b ek').1
        (addArgKey ck (trieUnion (liveVars b tk).1 (liveVars b ek').1)) :=
      TrieSub.trans (TrieSub.union_right _ _) (TrieSub.addArgKey ck _)
    exact .jnz (argSweep_rel_of_inSet hnd hrel hck hc (Arg.InSet.addArgKey ck _))
      (iht hrel b tk htk (hnd.sub hsub_t))
      (ihe hrel b ek' hek (hnd.sub hsub_e))
  | jump hj hargs =>
    intro G' hrel Gk Dk b ek hwk hnd
    rcases hwk.rhs_jump with ⟨jk, argsk, rfl, _, hargsk⟩
    simp only [liveVars] at hnd ⊢
    simp only [dceSweep]
    exact .jump hj (TRel.argsSweep_of_inSet hnd hrel hargsk hargs (ArgsInSet.addArgKeys argsk _))
  | ret hvs =>
    intro G' hrel Gk Dk b ek hwk hnd
    rcases hwk.rhs_ret with ⟨vsk, rfl, hvsk⟩
    simp only [liveVars] at hnd ⊢
    simp only [dceSweep]
    exact .ret (TRel.argsSweep_of_inSet hnd hrel hvsk hvs (ArgsInSet.addArgKeys vsk _))
  | exit f hargs =>
    intro G' hrel Gk Dk b ek hwk hnd
    rcases hwk.rhs_exit with ⟨argsk, rfl, hargsk⟩
    simp only [liveVars] at hnd ⊢
    simp only [dceSweep]
    exact .exit f (TRel.argsSweep_of_inSet hnd hrel hargsk hargs (ArgsInSet.addArgKeys argsk _))
  | hlt =>
    intro _ _ _ _ _ ek hwk _
    rw [hwk.rhs_hlt]
    exact .hlt
  | @group G D sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro G' hrel Gk Dk b ek hwk hnd
    rcases hwk.rhs_group with ⟨bk, kk, rfl, hbk, hkk⟩
    simp only [liveVars] at hnd ⊢
    simp only [dceSweep]
    have hsub_k : TrieSub (liveVars b (kk (Tup.units sig))).1
        (trieUnion (liveVarsB b (bk (Tup.units sig))).1 (liveVars b (kk (Tup.units sig))).1) :=
      TrieSub.union_right _ _
    refine .group (fun Js₁ Js₂ => WfB.of_get fun {ts} i xs₁ xs₂ => ?_)
      (fun Js₁ Js₂ => ihk Js₁ Js₂ hrel b (kk (Tup.units sig)) (hkk (Tup.units sig) Js₁)
        (hnd.sub hsub_k))
    rw [dceSweepB_liveVarsB_get b (bk (Tup.units sig)) (b₁ Js₁) i xs₁,
        dceSweepB_liveVarsB_get b (bk (Tup.units sig)) (b₂ Js₂) i xs₂]
    have hsub_b :
        TrieSub (liveVars (b + ts.length) ((bk (Tup.units sig)).get i (Tup.levels ts b))).1
          (trieUnion (liveVarsB b (bk (Tup.units sig))).1
            (liveVars b (kk (Tup.units sig))).1) :=
      TrieSub.trans (liveVarsB_sub b (bk (Tup.units sig)) i) (TrieSub.union_left _ _)
    exact ihb Js₁ Js₂ i (someTup ts xs₁) (someTup ts xs₂) (DceRel.append_some hrel xs₁ xs₂)
      (b + ts.length) ((bk (Tup.units sig)).get i (Tup.levels ts b))
      ((hbk (Tup.units sig) Js₁).get i (Tup.levels ts b) (someTup ts xs₁))
      (NoneDead.append_some (NoneDead.sub hsub_b hnd) _ _)

/-! ## Closed functions -/

theorem Func.dce_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) : (Func.dce f).Wf := by
  intro V₁ V₂ L₁ L₂ xs₁ xs₂
  have hwk := hf K (OptV V₁) KL0 L₁ (Tup.levels as 0) (someTup as xs₁)
  have hwf := hf (OptV V₁) (OptV V₂) L₁ L₂ (someTup as xs₁) (someTup as xs₂)
  have hnd : NoneDead (liveVars as.length (f K KL0 (Tup.levels as 0))).1
      (Tup.zip (Tup.levels as 0) (someTup as xs₁)) := by
    rw [← List.append_nil (Tup.zip (Tup.levels as 0) (someTup as xs₁))]
    exact NoneDead.append_some (V := V₁)
      (s := (liveVars as.length (f K KL0 (Tup.levels as 0))).1) (Gk := [])
      (fun {_ _ _} hm => nomatch hm) (Tup.levels as 0) xs₁
  have hrel : DceRel (Tup.zip (someTup as xs₁) (someTup as xs₂)) (Tup.zip xs₁ xs₂) := by
    rw [← List.append_nil (Tup.zip (someTup as xs₁) (someTup as xs₂)),
        ← List.append_nil (Tup.zip xs₁ xs₂)]
    exact DceRel.append_some (G := []) (G' := []) (fun {_ _ _} hm => nomatch hm) xs₁ xs₂
  exact LeanQbe.T.dce_wf hwf hrel as.length (f K KL0 (Tup.levels as 0)) hwk hnd

/-- DCE refines function contracts: any source contract holds on `Func.dce f`. -/
theorem Func.dce_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.dce f) xs m Q X := by
  have hwk := hf K (OptV Val) KL0 Cont (Tup.levels as 0) (someTup as xs)
  have hwf := hf (OptV Val) Val Cont Cont (someTup as xs) xs
  have hnd : NoneDead (liveVars as.length (f K KL0 (Tup.levels as 0))).1
      (Tup.zip (Tup.levels as 0) (someTup as xs)) := by
    rw [← List.append_nil (Tup.zip (Tup.levels as 0) (someTup as xs))]
    exact NoneDead.append_some (V := Val)
      (s := (liveVars as.length (f K KL0 (Tup.levels as 0))).1) (Gk := [])
      (fun {_ _ _} hm => nomatch hm) (Tup.levels as 0) xs
  have hG : SomeEq (Tup.zip (someTup as xs) xs) := by
    rw [← List.append_nil (Tup.zip (someTup as xs) xs)]
    exact SomeEq.append_some (G := []) (fun {_ _ _} hm => nomatch hm) xs
  exact LeanQbe.T.dce_wp hwf (fun _ hm => nomatch hm) hG as.length
    (f K KL0 (Tup.levels as 0)) hwk hnd m h

end LeanQbe.T

