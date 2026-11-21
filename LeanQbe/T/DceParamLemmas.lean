module

public import LeanQbe.T.DceParam
public import LeanQbe.T.DceLemmas

/-!
# Soundness and Relational Well-Formedness of `Func.dceP`

Proves WP refinement and relational well-formedness for dead `.group` block-parameter elimination:
* `dceP_wp`: `Wf.induct` proof extending `dceWith_wp` with mask-guided `.jump` operand narrowing
  and `widenCont` projection at `.group` continuations (via `closed_sweepBP`).
* `dceP_wf`: `Wf.induct` proof extending `dceWith_wf` with `LblOk2` / `MaskOk` / `wfb_sweepBP`.
* `Func.dcePWith_wf`, `Func.dcePWith_spec`, `Func.dceP_wf`, `Func.dceP_spec`: closed-function
  correctness, falling back to `Func.dceWith_{wf,spec}` if a multi-round plan check fails.
* `liveVarsP_leaf_ok`: the `rounds = 0` plan (`.leaf`) unconditionally passes validation.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

namespace DceParam

/-! ## Masked liveness transport -/

/-- Kept (`true`-masked) jump operand keys are present in liveness set `s`. -/
def ArgsInSetM (s : Trie Unit) : {ts : List Ty} → Mask ts → Tup (Arg K) ts → Prop
  | [], _, _ => True
  | _ :: _, (true, m), (a, as) => a.InSet s ∧ ArgsInSetM s m as
  | _ :: _, (false, m), (_, as) => ArgsInSetM s m as

theorem ArgsInSetM.mono {s₁ s₂ : Trie Unit} (hsub : TrieSub s₁ s₂) :
    {ts : List Ty} → {m : Mask ts} → {as : Tup (Arg K) ts} →
    ArgsInSetM s₁ m as → ArgsInSetM s₂ m as
  | [], _, _, _ => trivial
  | _ :: _, (true, _), (_, _), ⟨ha, has⟩ => ⟨ha.mono hsub, ArgsInSetM.mono hsub has⟩
  | _ :: ts, (false, m), (_, as), h =>
    ArgsInSetM.mono (ts := ts) (m := m) (as := as) hsub h

theorem ArgsInSetM.addMasked :
    {ts : List Ty} → (m : Mask ts) → (as : Tup (Arg K) ts) → (s : Trie Unit) →
    ArgsInSetM (addMasked m as s) m as
  | [], _, _, _ => trivial
  | _ :: _, (true, m), (a, as), s =>
    ⟨Arg.InSet.addArgKey a _,
     ArgsInSetM.mono (TrieSub.addArgKey a _) (ArgsInSetM.addMasked m as s)⟩
  | _ :: _, (false, m), (_, as), s => ArgsInSetM.addMasked m as s

theorem vals_tupNarrow : (ts : List Ty) → (m : Mask ts) → (args : Tup (Arg Val) ts) →
    vals (tupNarrow ts m args) = tupNarrow ts m (vals args)
  | [], _, _ => rfl
  | _ :: ts, (true, m), (_, as) => Prod.ext rfl (vals_tupNarrow ts m as)
  | _ :: ts, (false, m), (_, as) => vals_tupNarrow ts m as

/-- Kept jump operands preserve their semantic value through `argsSweep`. -/
theorem narrow_argsSweep_vals {s : Trie Unit} {Gk : Ctx K (OptV Val)} {G : Ctx (OptV Val) Val}
    (hnd : NoneDead s Gk) (hG : SomeEq G) :
    {ts : List Ty} → (m mk : Mask ts) → maskLe m mk = true →
    {aks : Tup (Arg K) ts} → {as₁ : Tup (Arg (OptV Val)) ts} → {as₂ : Tup (Arg Val) ts} →
    TRel (ArgRel Gk) aks as₁ → TRel (ArgRel G) as₁ as₂ → ArgsInSetM s mk aks →
    tupNarrow ts m (vals (argsSweep as₁)) = tupNarrow ts m (vals as₂)
  | [], _, _, _, _, _, _, _, _, _ => rfl
  | _ :: _, (true, m), (true, mk), hle, (_, _), (_, _), (_, _), .cons hka hkas, .cons h12a h12as,
      ⟨ha, has⟩ =>
    Prod.ext (argSweep_val_of_inSet hnd hG hka h12a ha)
      (narrow_argsSweep_vals hnd hG m mk (by simpa [maskLe] using hle) hkas h12as has)
  | _ :: _, (true, _), (false, _), hle, _, _, _, _, _, _ => by simp [maskLe] at hle
  | _ :: _, (false, m), (true, mk), hle, (_, _), (_, _), (_, _), .cons _ hkas, .cons _ h12as,
      ⟨_, has⟩ =>
    narrow_argsSweep_vals hnd hG m mk (by simpa [maskLe] using hle) hkas h12as has
  | _ :: _, (false, m), (false, mk), hle, (_, _), (_, _), (_, _), .cons _ hkas, .cons _ h12as,
      has =>
    narrow_argsSweep_vals hnd hG m mk (by simpa [maskLe] using hle) hkas h12as has

/-! ## Label invariants -/

/-- Source continuation of a narrowed target continuation: project away dropped parameters. -/
def widenCont (ts : List Ty) (m : Mask ts) (J' : Cont (narrow ts m)) : Cont ts :=
  fun xs mem => J' (tupNarrow ts m xs) mem

/-- Label relation for WP refinement: each sweep label denotes `widenCont ts m l`. -/
def LblRel : (ts : List Ty) → NLabel Cont ts → Cont ts → Prop
  | ts, .mk m l, j => j = widenCont ts m l

/-- Context-wide label invariant for `dceP_wp`. -/
def LblOk (D : Ctx (NLabel Cont) Cont) : Prop := ∀ p ∈ D, LblRel p.1 p.2.1 p.2.2

/-- Lift a tuple of narrowed target continuations back to the unnarrowed `sig`. -/
def widenConts : (sig : List (List Ty)) → (ms : Tup Mask sig) → Tup Cont (narrowSig sig ms) →
    Tup Cont sig
  | [], _, _ => ()
  | ts :: sig, (m, ms), (J, Js) => (widenCont ts m J, widenConts sig ms Js)

theorem LblOk.append_wrap {D : Ctx (NLabel Cont) Cont} (hD : LblOk D) :
    (sig : List (List Ty)) → (ms : Tup Mask sig) → (Js' : Tup Cont (narrowSig sig ms)) →
    LblOk (Tup.zip (wrapLabels sig ms Js') (widenConts sig ms Js') ++ D)
  | [], _, _ => hD
  | _ :: sig, (_, ms), (_, Js) => by
    intro p hp
    simp only [wrapLabels, widenConts, Tup.zip, List.cons_append] at hp
    cases hp with
    | head => rfl
    | tail _ hp => exact LblOk.append_wrap hD sig ms Js p hp

/-- Pre-scan/sweep label mask agreement: every sweep-kept parameter was assumed live. -/
def MaskRel {L : List Ty → Type} : (ts : List Ty) → KLM ts → NLabel L ts → Prop
  | _, mk, .mk m _ => maskLe m mk = true

/-- Context-wide mask agreement between `KLM` and `NLabel L`. -/
def MaskOk {L : List Ty → Type} (Dk : Ctx KLM (NLabel L)) : Prop :=
  ∀ p ∈ Dk, MaskRel p.1 p.2.1 p.2.2

/-- Block-tuple companion of `maskLe`. -/
def masksLe : {sig : List (List Ty)} → Tup Mask sig → Tup Mask sig → Bool
  | [], _, _ => true
  | _ :: _, (m, ms), (g, gs) => maskLe m g && masksLe ms gs

theorem MaskOk.append_wrap {L : List Ty → Type} {Dk : Ctx KLM (NLabel L)} (hD : MaskOk Dk) :
    (sig : List (List Ty)) → (gms ms : Tup Mask sig) → masksLe ms gms = true →
    (Js' : Tup L (narrowSig sig ms)) →
    MaskOk (Tup.zip (f := KLM) gms (wrapLabels sig ms Js') ++ Dk)
  | [], _, _, _, _ => hD
  | _ :: sig, (_, gms), (_, ms), hle, (_, Js) => by
    simp only [masksLe, Bool.and_eq_true] at hle
    intro p hp
    simp only [wrapLabels, Tup.zip, List.cons_append] at hp
    cases hp with
    | head => exact hle.1
    | tail _ hp => exact MaskOk.append_wrap hD sig gms ms hle.2 Js p hp

/-! ## Binder invariants under `tupWiden` -/

theorem SomeEq.append_widen {G : Ctx (OptV Val) Val} (hG : SomeEq G) :
    (ts : List Ty) → (m : Mask ts) → (xs : Tup Val ts) →
    SomeEq (Tup.zip (tupWiden ts m (tupNarrow ts m xs)) xs ++ G)
  | [], _, _ => hG
  | _ :: ts, (true, m), (x, xs) => SomeEq.cons_some (SomeEq.append_widen hG ts m xs) x
  | _ :: ts, (false, m), (x, xs) => SomeEq.cons_none (SomeEq.append_widen hG ts m xs) x

/-- Every dropped position of `m` (levels `b, b+1, ...`) is absent from `s`. -/
def MaskDead (s : Trie Unit) : (ts : List Ty) → Nat → Mask ts → Prop
  | [], _, _ => True
  | _ :: ts, b, (x, m) => (x = false → (s.find? b).isSome = false) ∧ MaskDead s ts (b + 1) m

theorem maskDead_liveMask (s : Trie Unit) :
    (ts : List Ty) → (b : Nat) → MaskDead s ts b (maskOf ts (liveMask b ts.length s))
  | [], _ => trivial
  | _ :: ts, b => ⟨fun h => h, maskDead_liveMask s ts (b + 1)⟩

theorem NoneDead.append_widen {V : Ty → Type} {s : Trie Unit} {Gk : Ctx K (OptV V)}
    (hnd : NoneDead s Gk) :
    (ts : List Ty) → (b : Nat) → (m : Mask ts) → MaskDead s ts b m →
    (ys : Tup V (narrow ts m)) →
    NoneDead s (Tup.zip (Tup.levels ts b) (tupWiden ts m ys) ++ Gk)
  | [], _, _, _, _ => hnd
  | _ :: ts, b, (true, m), hm, (y, ys) =>
    NoneDead.cons_some (NoneDead.append_widen hnd ts (b + 1) m hm.2 ys) b y
  | _ :: ts, b, (false, m), hm, ys =>
    NoneDead.cons_none (NoneDead.append_widen hnd ts (b + 1) m hm.2 ys) b (hm.1 rfl)

/-! ## Block access for the plan and the sweep -/

/-- Advance `PBlocks` to the suffix starting at block index `i`. -/
def PBlocks.drop : {ts : List Ty} → {sig : List (List Ty)} → PBlocks → Member ts sig → PBlocks
  | _, _, g, .here => g
  | _, _, g, .there i => PBlocks.drop g.tl i

theorem liveVarsBP_drop (dl dld : Bool) {rs : List Ty} (b : Nat) :
    {sig : List (List Ty)} → (g : PBlocks) → (bk : Blocks K KLM rs sig) → {ts : List Ty} →
    (i : Member ts sig) →
    ((liveVarsBP dl dld g b bk).2.1.drop i).hd =
        (liveVarsP dl dld (g.drop i).hd (b + ts.length) (bk.get i (Tup.levels ts b))).2.1 ∧
    ((liveVarsBP dl dld g b bk).2.1.drop i).mask =
        liveMask b ts.length
          (liveVarsP dl dld (g.drop i).hd (b + ts.length) (bk.get i (Tup.levels ts b))).1 ∧
    TrieSub (liveVarsP dl dld (g.drop i).hd (b + ts.length) (bk.get i (Tup.levels ts b))).1
        (liveVarsBP dl dld g b bk).1 ∧
    ((liveVarsBP dl dld g b bk).2.2 = true →
        (liveVarsP dl dld (g.drop i).hd (b + ts.length) (bk.get i (Tup.levels ts b))).2.2 = true)
  | _ :: _, _, .cons _ _, _, .here =>
    ⟨rfl, rfl, TrieSub.union_left _ _, fun h => by
      simp only [liveVarsBP, Bool.and_eq_true] at h; exact h.1.2⟩
  | _ :: _, g, .cons _ tl, _, .there i =>
    have ih := liveVarsBP_drop dl dld b g.tl tl i
    ⟨ih.1, ih.2.1, TrieSub.trans ih.2.2.1 (TrieSub.union_right _ _), fun h => by
      simp only [liveVarsBP, Bool.and_eq_true] at h; exact ih.2.2.2 h.2⟩

theorem liveVarsBP_masksLe (dl dld : Bool) {rs : List Ty} (b : Nat) :
    {sig : List (List Ty)} → (g : PBlocks) → (bk : Blocks K KLM rs sig) →
    (liveVarsBP dl dld g b bk).2.2 = true →
    masksLe ((liveVarsBP dl dld g b bk).2.1.masksOf sig) (g.masksOf sig) = true
  | [], _, .nil, _ => rfl
  | _ :: _, g, .cons _ tl, h => by
    simp only [liveVarsBP, Bool.and_eq_true] at h
    simp only [masksLe, PBlocks.masksOf, PBlocks.mask, PBlocks.tl, Bool.and_eq_true]
    exact ⟨h.1.1, liveVarsBP_masksLe dl dld b g.tl tl h.2⟩

/-- Transport `Closed` across the narrowed signature by structural recursion on the blocks. -/
theorem closed_sweepBP {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} :
    {sig : List (List Ty)} → (kbs : PBlocks) →
    (bs₁ : Blocks (OptV Val) (NLabel Cont) rs sig) → (bs₂ : Blocks Val Cont rs sig) →
    (Js' : Tup Cont (narrowSig sig (kbs.masksOf sig))) →
    (∀ {ts} (i : Member ts sig) (xs : Tup Val ts) m, wp Γ Q X (bs₂.get i xs) m →
      wp Γ Q X (dceSweepP (kbs.drop i).hd
        (bs₁.get i (tupWiden ts (maskOf ts (kbs.drop i).mask)
          (tupNarrow ts (maskOf ts (kbs.drop i).mask) xs)))) m) →
    Closed Γ Q X (dceSweepBP kbs bs₁) Js' →
    Closed Γ Q X bs₂ (widenConts sig (kbs.masksOf sig) Js')
  | [], _, .nil, .nil, _, _, _ => trivial
  | _ :: _, kbs, .cons _ bs₁, .cons _ bs₂, (_, Js), hstep, hc =>
    ⟨fun xs m hw => hc.1 _ m (hstep .here xs m hw),
     closed_sweepBP kbs.tl bs₁ bs₂ Js (fun i => hstep (.there i)) hc.2⟩

/-! ## `dceP_wp`: weakest-precondition preservation -/

/-- Weakest-precondition preservation for `dceSweepP`, proved via `Wf.induct`. -/
theorem dceP_wp (dl dld : Bool) {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx (OptV Val) Val} {D : Ctx (NLabel Cont) Cont}
    {e₁ : Expr (OptV Val) (NLabel Cont) rs} {e₂ : Expr Val Cont rs}
    (hwf : Wf G D e₁ e₂) :
    LblOk D →
    SomeEq G →
    ∀ {Gk : Ctx K (OptV Val)} {Dk : Ctx KLM (NLabel Cont)} (g : PTree) (b : Nat)
      (ek : Expr K KLM rs),
      Wf Gk Dk ek e₁ → MaskOk Dk → (liveVarsP dl dld g b ek).2.2 = true →
      NoneDead (liveVarsP dl dld g b ek).1 Gk →
      ∀ m, wp Γ Q X e₂ m → wp Γ Q X (dceSweepP (liveVarsP dl dld g b ek).2.1 e₁) m := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop₁₂ _ ih =>
    intro hD hG Gk Dk g b ek hwk hMk hok hnd m hw
    rcases hwk.rhs_let with ⟨opk, kk, rfl, hopk, hkk⟩
    cases hop₁₂ with
    | @mk sig _ code args₁ args₂ hargs₁₂ =>
      cases hopk with
      | @mk _ _ _ argsk _ hargsk =>
        simp only [liveVarsP] at hnd hok ⊢
        cases hkeep : (!dl || anyLive b ts.length
            (liveVarsP dl dld g.sub1 (b + ts.length) (kk (Tup.levels ts b))).1) with
        | true =>
          simp only [hkeep, ↓reduceIte] at hnd hok ⊢
          simp only [dceSweepP, wp, Op.wp] at hw ⊢
          have hvals : vals (argsSweep args₁) = vals args₂ :=
            argsSweep_vals_of_inSet hnd hG hargsk hargs₁₂ (ArgsInSet.addArgKeys argsk _)
          rw [hvals]
          refine OpCode.wp_mono code (vals args₂) (fun xs hkx => ?_) hw
          exact ih (someTup ts xs) xs hD (SomeEq.append_some hG xs) g.sub1
            (b + ts.length) (kk (Tup.levels ts b))
            (hkk (Tup.levels ts b) (someTup ts xs)) hMk hok
            (NoneDead.append_some_addArgKeys argsk b xs hnd) m hkx
        | false =>
          simp only [hkeep, Bool.false_eq_true, ↓reduceIte] at hnd hok ⊢
          simp only [dceSweepP]
          simp only [wp, Op.wp] at hw
          obtain ⟨xs₂, hxs₂⟩ := OpCode.wp_exists code (vals args₂) hw
          exact ih (noneTup ts) xs₂ hD (SomeEq.append_none hG xs₂) g.sub1
            (b + ts.length) (kk (Tup.levels ts b))
            (hkk (Tup.levels ts b) (noneTup ts)) hMk hok
            (NoneDead.append_none_of_not_keep b hkeep hnd) m hxs₂
  | load t ha _ ih =>
    intro hD hG Gk Dk g b ek hwk hMk hok hnd m hw
    rcases hwk.rhs_load with ⟨ak, kk, rfl, hak, hkk⟩
    simp only [liveVarsP] at hnd hok ⊢
    rcases hw with ⟨v, hv, hk⟩
    cases hkeep : (!dld ||
        ((liveVarsP dl dld g.sub1 (b + 1) (kk b)).1.find? b).isSome) with
    | true =>
      simp only [hkeep, ↓reduceIte] at hnd hok ⊢
      simp only [dceSweepP, wp]
      have hval := argSweep_val_of_inSet hnd hG hak ha (Arg.InSet.addArgKey ak _)
      rw [hval]
      refine ⟨v, hv, ?_⟩
      exact ih (some v) v hD (SomeEq.cons_some hG v) g.sub1 (b + 1) (kk b) (hkk b (some v))
        hMk hok (NoneDead.cons_some_addArgKey ak b v hnd) m hk
    | false =>
      simp only [hkeep, Bool.false_eq_true, ↓reduceIte] at hnd hok ⊢
      simp only [dceSweepP]
      exact ih none v hD (SomeEq.cons_none hG v) g.sub1 (b + 1) (kk b) (hkk b none) hMk hok
        (NoneDead.cons_none_of_not_keep b hkeep hnd) m hk
  | store hv ha _ ih =>
    intro hD hG Gk Dk g b ek hwk hMk hok hnd m hw
    rcases hwk.rhs_store with ⟨vk, ak, kk, rfl, hvk, hak, hkk⟩
    simp only [liveVarsP] at hnd hok ⊢
    simp only [dceSweepP, wp] at hw ⊢
    have hvval := argSweep_val_of_inSet hnd hG hvk hv (Arg.InSet.addArgKey vk _)
    have haval := argSweep_val_of_inSet hnd hG hak ha (Arg.InSet.addArgKey2 vk ak _)
    rw [hvval, haval]
    exact ⟨hw.1, ih hD hG g.sub1 b kk hkk hMk hok (NoneDead.sub_addArgKey2 vk ak hnd) _ hw.2⟩
  | @call _ _ f _ bs _ _ _ _ hargs _ ih =>
    intro hD hG Gk Dk g b ek hwk hMk hok hnd m hw
    rcases hwk.rhs_call with ⟨argsk, kk, rfl, hargsk, hkk⟩
    simp only [liveVarsP] at hnd hok ⊢
    simp only [dceSweepP, wp] at hw ⊢
    rcases hw with ⟨P, E, hΓ, hP, hE⟩
    have hvals := argsSweep_vals_of_inSet hnd hG hargsk hargs (ArgsInSet.addArgKeys argsk _)
    rw [hvals]
    refine ⟨P, E, hΓ, fun r m' hp => ?_, hE⟩
    exact ih (someTup bs r) r hD (SomeEq.append_some hG r) g.sub1 (b + bs.length)
      (kk (Tup.levels bs b)) (hkk (Tup.levels bs b) (someTup bs r)) hMk hok
      (NoneDead.append_some_addArgKeys argsk b r hnd) m' (hP r m' hp)
  | jnz hc _ _ iht ihe =>
    intro hD hG Gk Dk g b ek hwk hMk hok hnd m hw
    rcases hwk.rhs_jnz with ⟨ck, tk, ek', rfl, hck, htk, hek⟩
    simp only [liveVarsP, Bool.and_eq_true] at hnd hok ⊢
    simp only [dceSweepP, wp] at hw ⊢
    have hval := argSweep_val_of_inSet hnd hG hck hc (Arg.InSet.addArgKey ck _)
    rw [hval]
    exact ⟨fun h => iht hD hG g.subT b tk htk hMk hok.1
              (NoneDead.sub_union_left_addArgKey ck hnd) m (hw.1 h),
           fun h => ihe hD hG g.subE b ek' hek hMk hok.2
              (NoneDead.sub_union_right_addArgKey ck hnd) m (hw.2 h)⟩
  | @jump G D ts j₁ j₂ args₁ args₂ hj hargs =>
    intro hD hG Gk Dk g b ek hwk hMk hok hnd m hw
    rcases hwk.rhs_jump with ⟨mk, argsk, rfl, hjk, hargsk⟩
    have hrel := hD _ hj
    have hmrel := hMk _ hjk
    cases j₁ with
    | mk msk l =>
      simp only [LblRel] at hrel
      simp only [MaskRel] at hmrel
      subst hrel
      simp only [liveVarsP] at hnd ⊢
      simp only [dceSweepP, wp, widenCont] at hw ⊢
      rw [vals_tupNarrow, narrow_argsSweep_vals hnd hG msk mk hmrel hargsk hargs
        (ArgsInSetM.addMasked mk argsk _)]
      exact hw
  | ret hvs =>
    intro _ hG Gk Dk g b ek hwk _ _ hnd m hw
    rcases hwk.rhs_ret with ⟨vsk, rfl, hvsk⟩
    simp only [liveVarsP] at hnd ⊢
    simp only [dceSweepP, wp] at hw ⊢
    rw [argsSweep_vals_of_inSet hnd hG hvsk hvs (ArgsInSet.addArgKeys vsk _)]
    exact hw
  | exit f hargs =>
    intro _ hG Gk Dk g b ek hwk _ _ hnd m hw
    rcases hwk.rhs_exit with ⟨argsk, rfl, hargsk⟩
    simp only [liveVarsP] at hnd ⊢
    simp only [dceSweepP, wp] at hw ⊢
    rw [argsSweep_vals_of_inSet hnd hG hargsk hargs (ArgsInSet.addArgKeys argsk _)]
    exact hw
  | hlt =>
    intro _ _ _ _ _ _ _ hwk _ _ _ _ hw
    rw [hwk.rhs_hlt]
    exact hw
  | @group G D sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro hD hG Gk Dk g b ek hwk hMk hok hnd m hw
    rcases hwk.rhs_group with ⟨bk, kk, rfl, hbk, hkk⟩
    simp only [liveVarsP, Bool.and_eq_true] at hnd hok ⊢
    simp only [dceSweepP, wp] at hw ⊢
    intro Js' hclosed
    have hMk' := MaskOk.append_wrap hMk sig (g.subB.masksOf sig) _
      (liveVarsBP_masksLe dl dld b g.subB (bk (g.subB.masksOf sig)) hok.1) Js'
    have hD' := LblOk.append_wrap hD sig _ Js'
    refine ihk _ _ hD' hG g.subK b (kk (g.subB.masksOf sig)) (hkk _ _) hMk' hok.2
      (hnd.sub (TrieSub.union_right _ _)) m (hw _ ?_)
    refine closed_sweepBP _ _ _ Js' (fun {ts} i xs m' hb' => ?_) hclosed
    obtain ⟨hhd, hmask, hsubi, hoki⟩ :=
      liveVarsBP_drop dl dld b g.subB (bk (g.subB.masksOf sig)) i
    rw [hhd, hmask]
    exact ihb _ _ i _ xs hD' (SomeEq.append_widen hG ts _ xs) (g.subB.drop i).hd
      (b + ts.length) ((bk (g.subB.masksOf sig)).get i (Tup.levels ts b))
      ((hbk _ _).get i (Tup.levels ts b) _) hMk' (hoki hok.1)
      (NoneDead.append_widen
        (NoneDead.sub (TrieSub.trans hsubi (TrieSub.union_left _ _)) hnd) ts b _
        (maskDead_liveMask _ ts b) _) m' hb'

/-! ## `dceP_wf`: relational well-formedness preservation -/

section WfP
variable {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}

/-- Two sweep labels are related iff they carry the same mask and related narrowed labels. -/
inductive LblRel2 (D' : Ctx L₁ L₂) : (ts : List Ty) → NLabel L₁ ts → NLabel L₂ ts → Prop
  | mk {ts : List Ty} (m : Mask ts) {l₁ : L₁ (narrow ts m)} {l₂ : L₂ (narrow ts m)} :
      ⟨narrow ts m, l₁, l₂⟩ ∈ D' → LblRel2 D' ts (.mk m l₁) (.mk m l₂)

/-- Context-wide pairwise sweep-label invariant for `dceP_wf`. -/
def LblOk2 (D : Ctx (NLabel L₁) (NLabel L₂)) (D' : Ctx L₁ L₂) : Prop :=
  ∀ p ∈ D, LblRel2 D' p.1 p.2.1 p.2.2

theorem LblRel2.weaken {D₁ D₂ : Ctx L₁ L₂} (h : ∀ p ∈ D₁, p ∈ D₂) {ts : List Ty}
    {j₁ : NLabel L₁ ts} {j₂ : NLabel L₂ ts} : LblRel2 D₁ ts j₁ j₂ → LblRel2 D₂ ts j₁ j₂
  | .mk m hm => .mk m (h _ hm)

theorem LblOk2.append_wrap {D : Ctx (NLabel L₁) (NLabel L₂)} {D' : Ctx L₁ L₂}
    (hD : LblOk2 D D') :
    (sig : List (List Ty)) → (ms : Tup Mask sig) → (Js₁ : Tup L₁ (narrowSig sig ms)) →
    (Js₂ : Tup L₂ (narrowSig sig ms)) →
    LblOk2 (Tup.zip (wrapLabels sig ms Js₁) (wrapLabels sig ms Js₂) ++ D) (Tup.zip Js₁ Js₂ ++ D')
  | [], _, _, _ => hD
  | _ :: sig, (m, ms), (_, Js₁), (_, Js₂) => by
    intro p hp
    simp only [wrapLabels, Tup.zip, List.cons_append] at hp ⊢
    cases hp with
    | head => exact .mk m List.mem_cons_self
    | tail _ hp =>
      exact (LblOk2.append_wrap hD sig ms Js₁ Js₂ p hp).weaken
        (fun _ h => List.mem_cons_of_mem _ h)

theorem TRel.narrow_argsSweep {s : Trie Unit}
    {Gk : Ctx K (OptV V₁)} {G : Ctx (OptV V₁) (OptV V₂)} {G' : Ctx V₁ V₂}
    (hnd : NoneDead s Gk) (hrel : DceRel G G') :
    {ts : List Ty} → (m mk : Mask ts) → maskLe m mk = true →
    {aks : Tup (Arg K) ts} → {as₁ : Tup (Arg (OptV V₁)) ts} → {as₂ : Tup (Arg (OptV V₂)) ts} →
    TRel (ArgRel Gk) aks as₁ → TRel (ArgRel G) as₁ as₂ → ArgsInSetM s mk aks →
    TRel (ArgRel G') (tupNarrow ts m (argsSweep as₁)) (tupNarrow ts m (argsSweep as₂))
  | [], _, _, _, _, _, _, _, _, _ => .nil
  | _ :: _, (true, m), (true, mk), hle, (_, _), (_, _), (_, _), .cons hka hkas, .cons h12a h12as,
      ⟨ha, has⟩ =>
    .cons (argSweep_rel_of_inSet hnd hrel hka h12a ha)
      (TRel.narrow_argsSweep hnd hrel m mk (by simpa [maskLe] using hle) hkas h12as has)
  | _ :: _, (true, _), (false, _), hle, _, _, _, _, _, _ => by simp [maskLe] at hle
  | _ :: _, (false, m), (true, mk), hle, (_, _), (_, _), (_, _), .cons _ hkas, .cons _ h12as,
      ⟨_, has⟩ =>
    TRel.narrow_argsSweep hnd hrel m mk (by simpa [maskLe] using hle) hkas h12as has
  | _ :: _, (false, m), (false, mk), hle, (_, _), (_, _), (_, _), .cons _ hkas, .cons _ h12as,
      has =>
    TRel.narrow_argsSweep hnd hrel m mk (by simpa [maskLe] using hle) hkas h12as has

theorem DceRel.append_widen {G : Ctx (OptV V₁) (OptV V₂)} {G' : Ctx V₁ V₂} (hrel : DceRel G G') :
    (ts : List Ty) → (m : Mask ts) → (ys₁ : Tup V₁ (narrow ts m)) → (ys₂ : Tup V₂ (narrow ts m)) →
    DceRel (Tup.zip (tupWiden ts m ys₁) (tupWiden ts m ys₂) ++ G) (Tup.zip ys₁ ys₂ ++ G')
  | [], _, _, _ => hrel
  | _ :: ts, (true, m), (y₁, ys₁), (y₂, ys₂) =>
    DceRel.cons_some (DceRel.append_widen hrel ts m ys₁ ys₂) y₁ y₂
  | _ :: ts, (false, m), ys₁, ys₂ => DceRel.cons_none (DceRel.append_widen hrel ts m ys₁ ys₂)

theorem wfb_sweepBP {rs : List Ty} {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} :
    {sig : List (List Ty)} → (kbs : PBlocks) →
    (bs₁ : Blocks (OptV V₁) (NLabel L₁) rs sig) → (bs₂ : Blocks (OptV V₂) (NLabel L₂) rs sig) →
    (∀ {ts} (i : Member ts sig) (ys₁ : Tup V₁ (narrow ts (maskOf ts (kbs.drop i).mask)))
        (ys₂ : Tup V₂ (narrow ts (maskOf ts (kbs.drop i).mask))),
      Wf (Tup.zip ys₁ ys₂ ++ G') D'
        (dceSweepP (kbs.drop i).hd (bs₁.get i (tupWiden ts _ ys₁)))
        (dceSweepP (kbs.drop i).hd (bs₂.get i (tupWiden ts _ ys₂)))) →
    WfB G' D' (dceSweepBP kbs bs₁) (dceSweepBP kbs bs₂)
  | [], _, .nil, .nil, _ => .nil
  | _ :: _, kbs, .cons _ bs₁, .cons _ bs₂, h =>
    .cons (fun ys₁ ys₂ => h .here ys₁ ys₂)
      (wfb_sweepBP kbs.tl bs₁ bs₂ (fun i => h (.there i)))

/-- Relational well-formedness preservation for `dceSweepP`, proved via `Wf.induct`. -/
theorem dceP_wf (dl dld : Bool) {rs : List Ty}
    {G : Ctx (OptV V₁) (OptV V₂)} {D : Ctx (NLabel L₁) (NLabel L₂)}
    {e₁ : Expr (OptV V₁) (NLabel L₁) rs} {e₂ : Expr (OptV V₂) (NLabel L₂) rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂}, DceRel G G' → LblOk2 D D' →
    ∀ {Gk : Ctx K (OptV V₁)} {Dk : Ctx KLM (NLabel L₁)} (g : PTree) (b : Nat)
      (ek : Expr K KLM rs),
      Wf Gk Dk ek e₁ → MaskOk Dk → (liveVarsP dl dld g b ek).2.2 = true →
      NoneDead (liveVarsP dl dld g b ek).1 Gk →
      Wf G' D' (dceSweepP (liveVarsP dl dld g b ek).2.1 e₁)
        (dceSweepP (liveVarsP dl dld g b ek).2.1 e₂) := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop₁₂ _ ih =>
    intro G' D' hrel hD Gk Dk g b ek hwk hMk hok hnd
    rcases hwk.rhs_let with ⟨opk, kk, rfl, hopk, hkk⟩
    cases hop₁₂ with
    | @mk sig _ code args₁ args₂ hargs₁₂ =>
      cases hopk with
      | @mk _ _ _ argsk _ hargsk =>
        simp only [liveVarsP] at hnd hok ⊢
        cases hkeep : (!dl || anyLive b ts.length
            (liveVarsP dl dld g.sub1 (b + ts.length) (kk (Tup.levels ts b))).1) with
        | true =>
          simp only [hkeep, ↓reduceIte] at hnd hok ⊢
          simp only [dceSweepP]
          refine .let_ (.mk code (TRel.argsSweep_of_inSet hnd hrel hargsk hargs₁₂
            (ArgsInSet.addArgKeys argsk _))) fun xs₁ xs₂ => ?_
          exact ih (someTup ts xs₁) (someTup ts xs₂) (DceRel.append_some hrel xs₁ xs₂) hD g.sub1
            (b + ts.length) (kk (Tup.levels ts b))
            (hkk (Tup.levels ts b) (someTup ts xs₁)) hMk hok
            (NoneDead.append_some_addArgKeys argsk b xs₁ hnd)
        | false =>
          simp only [hkeep, Bool.false_eq_true, ↓reduceIte] at hnd hok ⊢
          simp only [dceSweepP]
          exact ih (noneTup ts) (noneTup ts) (DceRel.append_none hrel) hD g.sub1
            (b + ts.length) (kk (Tup.levels ts b))
            (hkk (Tup.levels ts b) (noneTup ts)) hMk hok
            (NoneDead.append_none_of_not_keep b hkeep hnd)
  | load t ha _ ih =>
    intro G' D' hrel hD Gk Dk g b ek hwk hMk hok hnd
    rcases hwk.rhs_load with ⟨ak, kk, rfl, hak, hkk⟩
    simp only [liveVarsP] at hnd hok ⊢
    cases hkeep : (!dld ||
        ((liveVarsP dl dld g.sub1 (b + 1) (kk b)).1.find? b).isSome) with
    | true =>
      simp only [hkeep, ↓reduceIte] at hnd hok ⊢
      simp only [dceSweepP]
      refine .load t (argSweep_rel_of_inSet hnd hrel hak ha (Arg.InSet.addArgKey ak _))
        fun v₁ v₂ => ?_
      exact ih (some v₁) (some v₂) (DceRel.cons_some hrel v₁ v₂) hD g.sub1 (b + 1) (kk b)
        (hkk b (some v₁)) hMk hok (NoneDead.cons_some_addArgKey ak b v₁ hnd)
    | false =>
      simp only [hkeep, Bool.false_eq_true, ↓reduceIte] at hnd hok ⊢
      simp only [dceSweepP]
      exact ih none none (DceRel.cons_none hrel) hD g.sub1 (b + 1) (kk b) (hkk b none) hMk hok
        (NoneDead.cons_none_of_not_keep b hkeep hnd)
  | store hv ha _ ih =>
    intro G' D' hrel hD Gk Dk g b ek hwk hMk hok hnd
    rcases hwk.rhs_store with ⟨vk, ak, kk, rfl, hvk, hak, hkk⟩
    simp only [liveVarsP] at hnd hok ⊢
    simp only [dceSweepP]
    exact .store (argSweep_rel_of_inSet hnd hrel hvk hv (Arg.InSet.addArgKey vk _))
      (argSweep_rel_of_inSet hnd hrel hak ha (Arg.InSet.addArgKey2 vk ak _))
      (ih hrel hD g.sub1 b kk hkk hMk hok (NoneDead.sub_addArgKey2 vk ak hnd))
  | @call _ _ f _ bs _ _ _ _ hargs _ ih =>
    intro G' D' hrel hD Gk Dk g b ek hwk hMk hok hnd
    rcases hwk.rhs_call with ⟨argsk, kk, rfl, hargsk, hkk⟩
    simp only [liveVarsP] at hnd hok ⊢
    simp only [dceSweepP]
    refine .call f (TRel.argsSweep_of_inSet hnd hrel hargsk hargs (ArgsInSet.addArgKeys argsk _))
      fun xs₁ xs₂ => ?_
    exact ih (someTup bs xs₁) (someTup bs xs₂) (DceRel.append_some hrel xs₁ xs₂) hD g.sub1
      (b + bs.length) (kk (Tup.levels bs b)) (hkk (Tup.levels bs b) (someTup bs xs₁)) hMk hok
      (NoneDead.append_some_addArgKeys argsk b xs₁ hnd)
  | jnz hc _ _ iht ihe =>
    intro G' D' hrel hD Gk Dk g b ek hwk hMk hok hnd
    rcases hwk.rhs_jnz with ⟨ck, tk, ek', rfl, hck, htk, hek⟩
    simp only [liveVarsP, Bool.and_eq_true] at hnd hok ⊢
    simp only [dceSweepP]
    exact .jnz (argSweep_rel_of_inSet hnd hrel hck hc (Arg.InSet.addArgKey ck _))
      (iht hrel hD g.subT b tk htk hMk hok.1 (NoneDead.sub_union_left_addArgKey ck hnd))
      (ihe hrel hD g.subE b ek' hek hMk hok.2 (NoneDead.sub_union_right_addArgKey ck hnd))
  | @jump G D ts j₁ j₂ args₁ args₂ hj hargs =>
    intro G' D' hrel hD Gk Dk g b ek hwk hMk hok hnd
    rcases hwk.rhs_jump with ⟨mk, argsk, rfl, hjk, hargsk⟩
    have hl : LblRel2 D' ts j₁ j₂ := hD _ hj
    have hmrel : MaskRel ts mk j₁ := hMk _ hjk
    cases hl with
    | mk msk hmem =>
      simp only [MaskRel] at hmrel
      simp only [liveVarsP] at hnd ⊢
      simp only [dceSweepP]
      exact .jump hmem (TRel.narrow_argsSweep hnd hrel msk mk hmrel hargsk hargs
        (ArgsInSetM.addMasked mk argsk _))
  | ret hvs =>
    intro G' D' hrel _ Gk Dk g b ek hwk _ _ hnd
    rcases hwk.rhs_ret with ⟨vsk, rfl, hvsk⟩
    simp only [liveVarsP] at hnd ⊢
    simp only [dceSweepP]
    exact .ret (TRel.argsSweep_of_inSet hnd hrel hvsk hvs (ArgsInSet.addArgKeys vsk _))
  | exit f hargs =>
    intro G' D' hrel _ Gk Dk g b ek hwk _ _ hnd
    rcases hwk.rhs_exit with ⟨argsk, rfl, hargsk⟩
    simp only [liveVarsP] at hnd ⊢
    simp only [dceSweepP]
    exact .exit f (TRel.argsSweep_of_inSet hnd hrel hargsk hargs (ArgsInSet.addArgKeys argsk _))
  | hlt =>
    intro _ _ _ _ _ _ _ _ ek hwk _ _ _
    rw [hwk.rhs_hlt]
    exact .hlt
  | @group G D sig b₁ b₂ k₁ k₂ _ _ ihb ihk =>
    intro G' D' hrel hD Gk Dk g b ek hwk hMk hok hnd
    rcases hwk.rhs_group with ⟨bk, kk, rfl, hbk, hkk⟩
    simp only [liveVarsP, Bool.and_eq_true] at hnd hok ⊢
    simp only [dceSweepP]
    refine .group (fun Js₁ Js₂ => ?_) (fun Js₁ Js₂ => ?_)
    · have hMk' := MaskOk.append_wrap hMk sig (g.subB.masksOf sig) _
        (liveVarsBP_masksLe dl dld b g.subB (bk (g.subB.masksOf sig)) hok.1) Js₁
      have hD' := LblOk2.append_wrap hD sig _ Js₁ Js₂
      refine wfb_sweepBP _ _ _ (fun {ts} i ys₁ ys₂ => ?_)
      obtain ⟨hhd, hmask, hsubi, hoki⟩ :=
        liveVarsBP_drop dl dld b g.subB (bk (g.subB.masksOf sig)) i
      have hmd : MaskDead
          (liveVarsP dl dld (g.subB.drop i).hd (b + ts.length)
            ((bk (g.subB.masksOf sig)).get i (Tup.levels ts b))).1 ts b
          (maskOf ts (((liveVarsBP dl dld g.subB b
            (bk (g.subB.masksOf sig))).2.1.drop i).mask)) := by
        rw [hmask]; exact maskDead_liveMask _ ts b
      rw [hhd]
      exact ihb _ _ i _ _ (DceRel.append_widen hrel ts _ ys₁ ys₂) hD' (g.subB.drop i).hd
        (b + ts.length) ((bk (g.subB.masksOf sig)).get i (Tup.levels ts b))
        ((hbk _ _).get i (Tup.levels ts b) _) hMk' (hoki hok.1)
        (NoneDead.append_widen
          (NoneDead.sub (TrieSub.trans hsubi (TrieSub.union_left _ _)) hnd) ts b _ hmd _)
    · have hMk' := MaskOk.append_wrap hMk sig (g.subB.masksOf sig) _
        (liveVarsBP_masksLe dl dld b g.subB (bk (g.subB.masksOf sig)) hok.1) Js₁
      exact ihk _ _ hrel (LblOk2.append_wrap hD sig _ Js₁ Js₂) g.subK b
        (kk (g.subB.masksOf sig)) (hkk _ _) hMk' hok.2 (hnd.sub (TrieSub.union_right _ _))

end WfP

/-! ## Single-round (`rounds = 0`, `.leaf` guess) validation lemma -/

theorem maskLe_top : {ts : List Ty} → (m : Mask ts) → maskLe m (maskOf ts []) = true
  | [], _ => rfl
  | _ :: _, (x, m) => by
    cases x <;> simp [maskLe, maskOf, maskLe_top m]

mutual
/-- The `.leaf` ("keep all") plan always passes `liveVarsP` validation. -/
theorem liveVarsP_leaf_ok (dl dld : Bool) {rs : List Ty} :
    (b : Nat) → (e : Expr K KLM rs) → (liveVarsP dl dld .leaf b e).2.2 = true
  | b, .let_ (ts := ts) _ k => by
    have ih := liveVarsP_leaf_ok dl dld (b + ts.length) (k (Tup.levels ts b))
    simp only [liveVarsP, PTree.sub1]
    by_cases hc : (!dl || anyLive b ts.length
        (liveVarsP dl dld PTree.leaf (b + ts.length) (k (Tup.levels ts b))).1) = true
    · simp only [hc, ↓reduceIte]; exact ih
    · simp only [hc]; exact ih
  | b, .load _ _ k => by
    have ih := liveVarsP_leaf_ok dl dld (b + 1) (k b)
    simp only [liveVarsP, PTree.sub1]
    by_cases hc :
        (!dld || ((liveVarsP dl dld PTree.leaf (b + 1) (k b)).1.find? b).isSome) = true
    · simp only [hc, ↓reduceIte]; exact ih
    · simp only [hc]; exact ih
  | b, .store _ _ k => by
    simp only [liveVarsP, PTree.sub1]
    exact liveVarsP_leaf_ok dl dld b k
  | b, .call _ (bs := bs) _ k => by
    simp only [liveVarsP, PTree.sub1]
    exact liveVarsP_leaf_ok dl dld (b + bs.length) (k (Tup.levels bs b))
  | b, .jnz _ t e => by
    simp only [liveVarsP, PTree.subT, PTree.subE, Bool.and_eq_true]
    exact ⟨liveVarsP_leaf_ok dl dld b t, liveVarsP_leaf_ok dl dld b e⟩
  | _, .jump _ _ => rfl
  | _, .ret _ => rfl
  | _, .exit _ _ => rfl
  | _, .hlt => rfl
  | b, .group bodies k => by
    simp only [liveVarsP, PTree.subB, PTree.subK, Bool.and_eq_true]
    exact ⟨liveVarsBP_nil_ok dl dld b (bodies _), liveVarsP_leaf_ok dl dld b (k _)⟩

/-- Block-list companion of `liveVarsP_leaf_ok`. -/
theorem liveVarsBP_nil_ok (dl dld : Bool) {rs : List Ty} (b : Nat) :
    {sig : List (List Ty)} → (bs : Blocks K KLM rs sig) →
    (liveVarsBP dl dld .nil b bs).2.2 = true
  | _, .nil => rfl
  | _, .cons (ts := ts) hd tl => by
    simp only [liveVarsBP, PBlocks.hd, PBlocks.tl, PBlocks.mask, Bool.and_eq_true]
    exact ⟨⟨maskLe_top _, liveVarsP_leaf_ok dl dld (b + ts.length) (hd (Tup.levels ts b))⟩,
      liveVarsBP_nil_ok dl dld b tl⟩
end

end DceParam

/-! ## Closed functions -/

open DceParam in
/-- `Func.dcePWith` preserves relational well-formedness. -/
theorem Func.dcePWith_wf (dl dld : Bool) (rounds : Nat := 0) {as rs : List Ty} {f : Func as rs}
    (hf : f.Wf) : (Func.dcePWith dl dld rounds f).Wf := by
  unfold Func.dcePWith
  dsimp only
  split
  · rename_i hok
    intro V₁ V₂ L₁ L₂ xs₁ xs₂
    exact DceParam.dceP_wf dl dld
      (hf (OptV V₁) (OptV V₂) (NLabel L₁) (NLabel L₂) (someTup as xs₁) (someTup as xs₂))
      (DceRel.fresh_nil xs₁ xs₂) (fun _ hm => nomatch hm) _ as.length
      (f K KLM (Tup.levels as 0))
      (hf K (OptV V₁) KLM (NLabel L₁) (Tup.levels as 0) (someTup as xs₁))
      (fun _ hm => nomatch hm) hok (NoneDead.fresh_nil _ xs₁)
  · exact Func.dceWith_wf dl dld hf

open DceParam in
/-- `Func.dcePWith` refines function contracts: any source contract holds on
`Func.dcePWith dl dld rounds f`. -/
theorem Func.dcePWith_spec (dl dld : Bool) (rounds : Nat := 0) {as rs : List Ty} {f : Func as rs}
    (hf : f.Wf) {Γ : Env} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.dcePWith dl dld rounds f) xs m Q X := by
  unfold Func.dcePWith
  dsimp only
  split
  · rename_i hok
    exact DceParam.dceP_wp dl dld (hf (OptV Val) Val (NLabel Cont) Cont (someTup as xs) xs)
      (fun _ hm => nomatch hm) (SomeEq.fresh_nil xs) _ as.length (f K KLM (Tup.levels as 0))
      (hf K (OptV Val) KLM (NLabel Cont) (Tup.levels as 0) (someTup as xs))
      (fun _ hm => nomatch hm) hok (NoneDead.fresh_nil _ xs) m h
  · exact Func.dceWith_spec dl dld hf h

/-- `Func.dceP` preserves relational well-formedness. -/
theorem Func.dceP_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) (rounds : Nat := 0) :
    (Func.dceP f rounds).Wf :=
  Func.dcePWith_wf true false rounds hf

/-- `Func.dceP` refines function contracts: any source contract holds on `Func.dceP f rounds`. -/
theorem Func.dceP_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) (rounds : Nat := 0) :
    Func.spec Γ (Func.dceP f rounds) xs m Q X :=
  Func.dcePWith_spec true false rounds hf h

end LeanQbe.T
