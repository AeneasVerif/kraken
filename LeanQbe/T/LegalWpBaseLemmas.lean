module

public import LeanQbe.T.LegalWfBaseLemmas

/-!
# Legalization semantic preservation base and tree lemmas (`T5`, Part 1)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## Section 4: Semantic preservation (`Func.legal_wp` / `Func.legal_spec`) -/

section LegalWp

/-- Lift a source return postcondition `Q : Post rs` to the legalized return tuple. -/
def legalPost (target : LegalTarget) {rs : List Ty} (Q : Post rs) : Post (target.legalSig rs) :=
  fun ys m => ∃ xs : Tup Val rs, encodeTup target rs xs = ys ∧ Q xs m

/-- Lift a source abnormal-exit postcondition `X : XPost` across legalized exit signatures. -/
def legalXPost (target : LegalTarget) (X : XPost) : XPost :=
  fun g cs' ys m => ∃ (cs : List Ty) (hcs : target.legalSig cs = cs') (xs : Tup Val cs),
    cast (congrArg (Tup Val) hcs) (encodeTup target cs xs) = ys ∧ X g cs xs m

/-- Simulation relation between source callee environment `Γsrc` and target environment `Γtgt`. -/
def EnvRefines (target : LegalTarget) (Γsrc Γtgt : Env) : Prop :=
  ∀ f as bs xs m P E,
    Γsrc f as bs xs m P E →
    Γtgt f (target.legalSig as) (target.legalSig bs) (encodeTup target as xs) m
      (legalPost target P) (legalXPost target E)

/-- Canonical legalized environment transforming every source contract via `encodeTup` / `legalPost` /
`legalXPost` (with consequence closure matching `wp_env_mono`). -/
def legalEnv (target : LegalTarget) (Γ : Env) : Env :=
  fun f as' bs' xs' m' Q' X' =>
    ∃ (as bs : List Ty) (has : target.legalSig as = as') (hbs : target.legalSig bs = bs')
      (xs : Tup Val as) (P : Post bs) (E : XPost),
      cast (congrArg (Tup Val) has) (encodeTup target as xs) = xs' ∧
      (∀ r m, legalPost target P r m → Q' (cast (congrArg (Tup Val) hbs) r) m) ∧
      (∀ g cs ys m, legalXPost target E g cs ys m → X' g cs ys m) ∧
      Γ f as bs xs m' P E

theorem envRefines_legalEnv (target : LegalTarget) (Γ : Env) : EnvRefines target Γ (legalEnv target Γ) :=
  fun _ as bs xs _ P E h => ⟨as, bs, rfl, rfl, xs, P, E, rfl, fun _ _ hp => hp, fun _ _ _ _ hx => hx, h⟩

theorem valsTup_eq_vals : ∀ {ts : List Ty} (xs : Tup (Arg Val) ts), valsTup xs = vals xs
  | [], () => rfl
  | _ :: _, (a, as) => congrArg (a.val, ·) (valsTup_eq_vals as)

@[simp] theorem valsTup_single {t : Ty} (a : Arg Val t) :
    valsTup (ts := [t]) (a, ()) = (a.val, ()) := rfl

@[simp] theorem val_castArgBits {m n : Nat} (h : m = n) (x : Arg Val (.bits m)) :
    (castArgBits h x).val = h ▸ x.val := by
  subst h; rfl

@[simp] theorem setWidth_cast_bits {m n k : Nat} (h : m = n) (x : BitVec m) :
    (h ▸ x : BitVec n).setWidth k = x.setWidth k := by
  subst h; rfl

theorem cast_eq_setWidth {m n : Nat} (h : m = n) (x : BitVec m) :
    (h ▸ x : BitVec n) = x.setWidth n := by
  subst h; simp [BitVec.setWidth_eq]

theorem setWidth_eq_cast {m n : Nat} (h : m = n) (x : BitVec m) :
    (x.setWidth n, ()) = cast (by rw [h]) (x, ()) := by
  subst h; simp [BitVec.setWidth_eq]

theorem cast_cast_eq {α β : Type} (h₁ : α = β) (h₂ : β = α) (x : α) :
    cast h₂ (cast h₁ x) = x := by
  subst h₁; rfl

theorem cast_inj {α β : Type} (h : α = β) {x y : α} (heq : cast h x = cast h y) : x = y := by
  subst h; exact heq

@[simp] theorem leafVals_pair (target : LegalTarget) (a b : Ty) (p : Val (.pair a b)) :
    leafVals target (.pair a b) p = tupAppend (leafVals target a p.1) (leafVals target b p.2) := rfl

theorem tupSplit_valsTup {as bs : List Ty} (fx : Tup (Arg Val) (as ++ bs)) :
    tupSplit (valsTup fx) = (valsTup (tupSplit (as := as) (bs := bs) fx).1,
      valsTup (tupSplit (as := as) (bs := bs) fx).2) := by
  have h := congrArg valsTup (tupAppend_tupSplit fx)
  rw [valsTup_tupAppend] at h
  rw [← h, tupSplit_tupAppend]

theorem encodeVal_pair_packed (target : LegalTarget) {a b : Ty}
    (h : target.keepsPacked (.pair a b) = true) (p : Val (.pair a b)) :
    encodeVal target (.pair a b) p =
      cast (by simp [LegalTarget.legalTys, h]) (show Tup Val [.pair a b] from (p, ())) := by
  simp only [encodeVal, h, ↓reduceDIte]

theorem encodeVal_pair_split (target : LegalTarget) {a b : Ty}
    (h : target.keepsPacked (.pair a b) = false) (p : Val (.pair a b)) :
    encodeVal target (.pair a b) p =
      cast (by simp [LegalTarget.legalTys, h])
        (tupAppend (encodeVal target a p.1) (encodeVal target b p.2)) := by
  simp only [encodeVal, h, Bool.false_eq_true, ↓reduceDIte]

theorem valsTup_packedToTup_encode (target : LegalTarget) {a b : Ty}
    (h : target.keepsPacked (.pair a b) = true)
    {xs : Tup (Arg Val) (target.legalTys (.pair a b))} {p : Val (.pair a b)}
    (hxs : valsTup xs = encodeVal target (.pair a b) p) :
    valsTup (packedToTup h xs) = (p, ()) := by
  rw [valsTup_packedToTup h, hxs, encodeVal_pair_packed target h, cast_cast_eq]

theorem valsTup_splitToTup_encode (target : LegalTarget) {a b : Ty}
    (h : target.keepsPacked (.pair a b) = false)
    {xs : Tup (Arg Val) (target.legalTys (.pair a b))} {p : Val (.pair a b)}
    (hxs : valsTup xs = encodeVal target (.pair a b) p) :
    valsTup (splitToTup h xs) = tupAppend (encodeVal target a p.1) (encodeVal target b p.2) := by
  rw [valsTup_splitToTup h, hxs, encodeVal_pair_split target h, cast_cast_eq]

theorem valsTup_tupToPacked_encode (target : LegalTarget) {a b : Ty}
    (h : target.keepsPacked (.pair a b) = true)
    {xs : Tup (Arg Val) [.pair a b]} {p : Val (.pair a b)} (hxs : valsTup xs = (p, ())) :
    valsTup (tupToPacked h xs) = encodeVal target (.pair a b) p := by
  rw [valsTup_tupToPacked h, hxs, encodeVal_pair_packed target h]

theorem valsTup_tupToSplit_encode (target : LegalTarget) {a b : Ty}
    (h : target.keepsPacked (.pair a b) = false)
    {xs : Tup (Arg Val) (target.legalTys a ++ target.legalTys b)} {p : Val (.pair a b)}
    (hxs : valsTup xs = tupAppend (encodeVal target a p.1) (encodeVal target b p.2)) :
    valsTup (tupToSplit h xs) = encodeVal target (.pair a b) p := by
  rw [valsTup_tupToSplit h, hxs, encodeVal_pair_split target h]

theorem supportsTy_mask (target : LegalTarget) : ∀ (t : Ty), target.supportsTy t.mask = true
  | .bool | .bits _ | .float _ => rfl
  | .pair a b => by simp [LegalTarget.supportsTy, supportsTy_mask target a, supportsTy_mask target b]

theorem legalTys_eq_singleton_of_isLegalTy (target : LegalTarget) :
    ∀ {t : Ty}, target.isLegalTy t = true → target.legalTys t = [t]
  | .bool, _ => rfl
  | .bits n, ht => by
    have hmem : n ∈ target.bitWidths := by simpa [LegalTarget.isLegalTy] using ht
    simp [LegalTarget.legalTys, widenWidth_eq_self_of_mem target hmem]
  | .float _, _ => rfl
  | .pair a b, ht => by
    have hp : target.keepsPacked (.pair a b) = true := by simpa [LegalTarget.isLegalTy] using ht
    simp [LegalTarget.legalTys, hp]

theorem encodeVal_self (target : LegalTarget) :
    ∀ {t : Ty} (ht : target.isLegalTy t = true) (v : Val t),
      encodeVal target t v =
        cast (congrArg (Tup Val) (legalTys_eq_singleton_of_isLegalTy target ht).symm)
          (show Tup Val [t] from (v, ()))
  | .bool, _, _ => rfl
  | .bits n, ht, v => by
    have hmem : n ∈ target.bitWidths := by simpa [LegalTarget.isLegalTy] using ht
    have hw : target.widenWidth n = n := widenWidth_eq_self_of_mem target hmem
    dsimp only [encodeVal, LegalTarget.legalTys]
    exact setWidth_eq_cast hw.symm v
  | .float _, _, _ => rfl
  | .pair a b, ht, v => by
    have hp : target.keepsPacked (.pair a b) = true := by simpa [LegalTarget.isLegalTy] using ht
    exact encodeVal_pair_packed target hp v

theorem encodeVal_inj (target : LegalTarget) :
    ∀ {t : Ty}, target.supportsTy t = true → Function.Injective (encodeVal target t)
  | .bool, _, a, b, h => congrArg Prod.fst h
  | .bits n, ht, a, b, h => by
    have hle := le_widenWidth_of_supports ht
    have h1 : a.setWidth (target.widenWidth n) = b.setWidth (target.widenWidth n) :=
      congrArg Prod.fst h
    have h' := congrArg (BitVec.setWidth n) h1
    simpa [BitVec.setWidth_setWidth_of_le _ hle, BitVec.setWidth_eq] using h'
  | .float _, _, a, b, h => congrArg Prod.fst h
  | .pair a b, ht, p₁, p₂, h => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    by_cases hp : target.keepsPacked (.pair a b) = true
    · rw [encodeVal_pair_packed target hp p₁, encodeVal_pair_packed target hp p₂] at h
      exact congrArg Prod.fst (cast_inj (congrArg (Tup Val) (by simp [LegalTarget.legalTys, hp])) h)
    · have hf := Bool.eq_false_iff.mpr hp
      rw [encodeVal_pair_split target hf p₁, encodeVal_pair_split target hf p₂] at h
      have h' := cast_inj (congrArg (Tup Val) (by simp [LegalTarget.legalTys, hf])) h
      have hsp := congrArg tupSplit h'
      simp only [tupSplit_tupAppend, Prod.mk.injEq] at hsp
      exact Prod.ext (encodeVal_inj target ht.1 hsp.1) (encodeVal_inj target ht.2 hsp.2)

theorem tupAppend_inj {α : Type} {f : α → Type} :
    {as bs : List α} → {x₁ x₂ : Tup f as} → {y₁ y₂ : Tup f bs} →
    tupAppend x₁ y₁ = tupAppend x₂ y₂ → x₁ = x₂ ∧ y₁ = y₂
  | [], _, (), (), _, _, h => ⟨rfl, h⟩
  | _ :: _, _, (_, _), (_, _), _, _, h => by
    have h1 : _ = _ := congrArg Prod.fst h
    have ih := tupAppend_inj (congrArg Prod.snd h)
    exact ⟨Prod.ext h1 ih.1, ih.2⟩

theorem encodeTup_inj (target : LegalTarget) :
    ∀ {ts : List Ty}, ts.all target.supportsTy = true → Function.Injective (encodeTup target ts)
  | [], _, (), (), _ => rfl
  | _ :: _, ht, (_, _), (_, _), h => by
    simp only [List.all_cons, Bool.and_eq_true] at ht
    simp only [encodeTup] at h
    obtain ⟨h1, h2⟩ := tupAppend_inj h
    exact Prod.ext (encodeVal_inj target ht.1 h1) (encodeTup_inj target ht.2 h2)

private theorem encodeTup_one_of_eq {t : Ty} {l : List Ty} (hl : l = [t])
    (heq : l ++ [] = [t]) (v : Val t) (z : Tup Val l)
    (hz : z = cast (congrArg (Tup Val) hl.symm) (show Tup Val [t] from (v, ()))) :
    tupAppend z () = cast (congrArg (Tup Val) heq.symm) (show Tup Val [t] from (v, ())) := by
  subst hl; rw [hz]; rfl

theorem encodeTup_singleton_eq_cast (target : LegalTarget) {t : Ty} (ht : target.isLegalTy t = true)
    (heq : target.legalSig [t] = [t]) (v : Val t) :
    encodeTup target [t] (v, ()) = cast (congrArg (Tup Val) heq.symm) (show Tup Val [t] from (v, ())) :=
  encodeTup_one_of_eq (legalTys_eq_singleton_of_isLegalTy target ht) heq v (encodeVal target t v)
    (encodeVal_self target ht v)

theorem legalPost_of_isLegal (target : LegalTarget) {t : Ty} (ht : target.isLegalTy t = true)
    (Q : Post [t]) (y : Val t) (m : Mem 64)
    (heq : target.legalSig [t] = [t] := by
      simp [LegalTarget.legalSig, legalTys_eq_singleton_of_isLegalTy target ht]) :
    legalPost target Q (cast (congrArg (Tup Val) heq.symm) (show Tup Val [t] from (y, ()))) m ↔
      Q (y, ()) m := by
  have h1 := encodeTup_singleton_eq_cast target ht heq
  constructor
  · rintro ⟨⟨x, ⟨⟩⟩, hx, hq⟩
    rw [h1 x] at hx
    have hx' := cast_inj (congrArg (Tup Val) heq.symm) hx
    have hxy : x = y := congrArg Prod.fst hx'
    subst hxy; exact hq
  · intro hq
    exact ⟨(y, ()), h1 y, hq⟩

/-! ### Value and label relations for `legalExpr_wp` -/

/-- Value context invariant during `legalExpr_wp`. -/
def CGoodWp (target : LegalTarget) (G : Ctx Val (LVar target Val)) : Prop :=
  ∀ t v lv, ⟨t, v, lv⟩ ∈ G → valsTup lv = encodeVal target t v

/-- Label context invariant during `legalExpr_wp`. -/
def DGoodWp (target : LegalTarget) (D : Ctx Cont (LLab target Cont)) : Prop :=
  ∀ ts j₁ j₂, ⟨ts, j₁, j₂⟩ ∈ D → ∀ xs m, j₁ xs m → j₂ (encodeTup target ts xs) m

theorem CGoodWp.weaken {target : LegalTarget} {G G' : Ctx Val (LVar target Val)}
    (hG : ∀ p ∈ G', p ∈ G) (hc : CGoodWp target G) : CGoodWp target G' :=
  fun t v lv hm => hc t v lv (hG _ hm)

theorem valsTup_legalArg (target : LegalTarget) {G : Ctx Val (LVar target Val)} (hc : CGoodWp target G)
    {t : Ty} {a : Arg Val t} {la : Arg (LVar target Val) t} (ha : ArgRel G t a la) :
    valsTup (legalArg target la) = encodeVal target t a.val := by
  cases ha with
  | var hm => exact hc _ _ _ hm
  | imm c => simp [legalArg, Arg.val]

theorem valsTup_joinArgs (target : LegalTarget) {G : Ctx Val (LVar target Val)} (hc : CGoodWp target G) :
    {ts : List Ty} → {as : Tup (Arg Val) ts} → {las : Tup (Arg (LVar target Val)) ts} →
    TRel (ArgRel G) as las → valsTup (joinArgs target las) = encodeTup target ts (valsTup as)
  | [], (), (), .nil => rfl
  | _ :: _, (_, _), (_, _), .cons ha has => by
    dsimp only [joinArgs, encodeTup, LegalTarget.legalSig]
    rw [valsTup_tupAppend, valsTup_legalArg target hc ha, valsTup_joinArgs target hc has,
      valsTup_cons]

theorem CGoodWp.pushTRel (target : LegalTarget) {G : Ctx Val (LVar target Val)} (hc : CGoodWp target G) :
    {ts : List Ty} → {xs : Tup Val ts} → {lxs : Tup (LVar target Val) ts} →
    TRel (fun t x lv => valsTup lv = encodeVal target t x) xs lxs →
    CGoodWp target (Tup.zip xs lxs ++ G)
  | [], (), (), .nil, _, _, _, hm => hc _ _ _ hm
  | _ :: _, (_, _), (_, _), .cons hx hxs, t, v, lv, hm => by
    simp only [Tup.zip, List.cons_append] at hm
    rcases List.mem_cons.1 hm with hhead | htail
    · cases hhead; exact hx
    · exact CGoodWp.pushTRel target hc hxs t v lv htail

theorem CGoodWp.pushSplit (target : LegalTarget) {G : Ctx Val (LVar target Val)} (hc : CGoodWp target G) :
    (ts : List Ty) → (xs : Tup Val ts) →
    CGoodWp target (Tup.zip xs (splitParams target ts (encodeTup target ts xs)) ++ G)
  | [], (), _, _, _, hm => hc _ _ _ hm
  | _ :: us, (x, xs), _, _, _, hm => by
    simp only [encodeTup, splitParams, tupSplit_tupAppend, Tup.zip, List.cons_append] at hm
    rcases List.mem_cons.1 hm with hhead | htail
    · cases hhead; simp [varsTup_valsTup]
    · exact CGoodWp.pushSplit target hc us xs _ _ _ htail

/-- Lift target continuations into source continuations via `encodeTup`. -/
def unlegalTupCont (target : LegalTarget) :
    {sig : List (List Ty)} → Tup Cont (sig.map target.legalSig) → Tup Cont sig
  | [], () => ()
  | ts :: _, (j, js) => (fun xs m => j (encodeTup target ts xs) m, unlegalTupCont target js)

theorem unlegalTupCont_get (target : LegalTarget) :
    {sig : List (List Ty)} → (Js : Tup Cont (sig.map target.legalSig)) →
    {ts : List Ty} → (i : Member ts sig) → (xs : Tup Val ts) → (m : Mem 64) →
    (unlegalTupCont target Js).get i xs m = (Js.get (Member.map target.legalSig i)) (encodeTup target ts xs) m
  | _ :: _, (_, _), _, .here, _, _ => rfl
  | _ :: _, (_, Js), _, .there i, xs, m => unlegalTupCont_get target Js i xs m

theorem DGoodWp.pushUnlegal (target : LegalTarget) {D : Ctx Cont (LLab target Cont)} (hd : DGoodWp target D) :
    {sig : List (List Ty)} → (Js : Tup Cont (sig.map target.legalSig)) →
    DGoodWp target (Tup.zip (unlegalTupCont target Js) (tupLiftMap target.legalSig Cont Js) ++ D)
  | [], (), _, _, _, hm, xs, m, hj => hd _ _ _ hm xs m hj
  | _ :: _, (_, js), _, _, _, hm, xs, m, hj => by
    simp only [unlegalTupCont, tupLiftMap, Tup.zip, List.cons_append] at hm
    rcases List.mem_cons.1 hm with hhead | htail
    · cases hhead; exact hj
    · exact DGoodWp.pushUnlegal target hd js _ _ _ htail xs m hj

theorem legalBlocks_get (target : LegalTarget) {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {sig : List (List Ty)} → (bs : Blocks (LVar target V) (LLab target L) rs sig) →
    {ts : List Ty} → (i : Member ts sig) → (xs : Tup V (target.legalSig ts)) →
    (legalBlocks target bs).get (Member.map target.legalSig i) xs =
      legalExpr target (bs.get i (splitParams target ts xs))
  | _ :: _, .cons _ _, _, .here, _ => rfl
  | _ :: _, .cons _ bs, _, .there i, xs => legalBlocks_get target bs i xs

theorem toTBlocks_get (target : LegalTarget) {rs : List Ty} :
    {sig : List (List Ty)} → (bs : Blocks K KL rs sig) →
    {ts : List Ty} → (i : Member ts sig) → (nv nl : Nat) →
    (toTBlocks bs nv nl).supportsSource target = true →
    ts.all target.supportsTy = true ∧
      (toTFlat (bs.get i (Tup.levels ts nv)) (nv + ts.length) nl).supportsSource target = true
  | _ :: _, .cons _ _, _, .here, _, _, h => by
    simp only [toTBlocks, TBlocks.supportsSource, Bool.and_eq_true] at h
    exact ⟨h.1.1, h.1.2⟩
  | _ :: _, .cons _ bs, _, .there i, nv, nl, h => by
    simp only [toTBlocks, TBlocks.supportsSource, Bool.and_eq_true] at h
    exact toTBlocks_get target bs i nv nl h.2

/-! ### Bridge helper `_wp` theorems (`unpack*` / `pack*` / `splitLegalToLeaves`) -/

private theorem unpackToLeaves_wp (target : LegalTarget) {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} :
    ∀ (t : Ty), target.supportsTy t = true → (a : Arg Val t) →
      {k : Tup (Arg Val) (target.leafTys t) → Expr Val Cont rs} → {m : Mem 64} →
      (∀ fx, valsTup fx = leafVals target t a.val → wp Γ Q X (k fx) m) →
      wp Γ Q X (unpackToLeaves target t a k) m
  | .bool, _, a, k, _, hk => hk (a, ()) rfl
  | .bits n, ht, a, k, _, hk => by
    have hnw : n ≤ target.widenWidth n := le_widenWidth_of_supports ht
    dsimp only [unpackToLeaves]
    split
    · next heq =>
      refine hk _ ?_
      dsimp only [LegalTarget.leafTys]
      rw [valsTup_single, val_castArgBits, leafVals, cast_eq_setWidth heq]
    · simp only [wp, Op.wp, OpCode.wp]
      exact ⟨hnw, hk _ rfl⟩
  | .float _, _, a, k, _, hk => hk (a, ()) rfl
  | .pair a b, ht, p, k, m, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    cases p with
    | imm c =>
      dsimp only [unpackToLeaves]
      exact hk (leafImm target (.pair a b) c) (by rw [valsTup_leafImm]; rfl)
    | var v =>
      dsimp only [unpackToLeaves, wp, Op.wp, OpCode.wp]
      exact unpackToLeaves_wp target a ht.1 (.var v.1) (fun fx1 h1 =>
        unpackToLeaves_wp target b ht.2 (.var v.2) (fun fx2 h2 =>
          hk (tupAppend fx1 fx2) (by
            dsimp only [LegalTarget.leafTys]
            rw [valsTup_tupAppend, h1, h2]
            rfl)))

theorem unpackToLegal_wp (target : LegalTarget) {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} :
    ∀ (t : Ty), target.supportsTy t = true → (a : Arg Val t) →
      {k : Tup (Arg Val) (target.legalTys t) → Expr Val Cont rs} → {m : Mem 64} →
      (∀ fx, valsTup fx = encodeVal target t a.val → wp Γ Q X (k fx) m) →
      wp Γ Q X (unpackToLegal target t a k) m
  | .bool, _, a, k, _, hk => hk (a, ()) rfl
  | .bits n, ht, a, k, _, hk => by
    have hnw : n ≤ target.widenWidth n := le_widenWidth_of_supports ht
    dsimp only [unpackToLegal]
    split
    · next heq =>
      refine hk _ ?_
      dsimp only [LegalTarget.legalTys]
      rw [valsTup_single, val_castArgBits, encodeVal, cast_eq_setWidth heq]
    · simp only [wp, Op.wp, OpCode.wp]
      exact ⟨hnw, hk _ rfl⟩
  | .float _, _, a, k, _, hk => hk (a, ()) rfl
  | .pair a b, ht, p, k, m, hk => by
    dsimp only [unpackToLegal]
    split
    · next hp =>
      exact hk (tupToPacked hp (p, ())) (valsTup_tupToPacked_encode target hp rfl)
    · next hp =>
      have hf := Bool.eq_false_iff.mpr hp
      simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
      cases p with
      | imm c => exact hk (encodeImm target (.pair a b) c) (by rw [valsTup_encodeImm]; rfl)
      | var v =>
        dsimp only [wp, Op.wp, OpCode.wp]
        exact unpackToLegal_wp target a ht.1 (.var v.1) (fun fx1 h1 =>
          unpackToLegal_wp target b ht.2 (.var v.2) (fun fx2 h2 =>
            hk (tupToSplit hf (tupAppend fx1 fx2))
              (valsTup_tupToSplit_encode target hf (by rw [valsTup_tupAppend, h1, h2]; rfl))))

theorem packFromLegal_wp (target : LegalTarget) {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} :
    ∀ (t : Ty), target.supportsTy t = true → (la : Tup (Arg Val) (target.legalTys t)) →
      (x : Val t) → valsTup la = encodeVal target t x →
      {k : Arg Val t → Expr Val Cont rs} → {m : Mem 64} →
      (∀ r, r.val = x → wp Γ Q X (k r) m) →
      wp Γ Q X (packFromLegal target t la k) m
  | .bool, _, (a, ()), x, hla, k, _, hk => hk a (congrArg Prod.fst hla)
  | .bits n, ht, (a, ()), x, hla, k, _, hk => by
    have hnw : n ≤ target.widenWidth n := le_widenWidth_of_supports ht
    have ha : a.val = x.setWidth (target.widenWidth n) := congrArg Prod.fst hla
    dsimp only [packFromLegal]
    split
    · next heq =>
      refine hk _ ?_
      rw [val_castArgBits, ha, cast_eq_setWidth heq.symm, BitVec.setWidth_setWidth_of_le _ hnw, BitVec.setWidth_eq]
    · simp only [wp, Op.wp, OpCode.wp]
      refine ⟨hnw, hk _ ?_⟩
      change (a.val).setWidth n = x
      rw [ha, BitVec.setWidth_setWidth_of_le _ hnw, BitVec.setWidth_eq]
  | .float _, _, (a, ()), x, hla, k, _, hk => hk a (congrArg Prod.fst hla)
  | .pair a b, ht, xs, p, hxs, k, m, hk => by
    dsimp only [packFromLegal]
    split
    · next hp =>
      exact hk _ (congrArg Prod.fst (valsTup_packedToTup_encode target hp hxs))
    · next hp =>
      have hf := Bool.eq_false_iff.mpr hp
      simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
      have hsp := valsTup_splitToTup_encode target hf hxs
      have h12 := congrArg tupSplit hsp
      simp only [tupSplit_valsTup, tupSplit_tupAppend] at h12
      exact packFromLegal_wp target a ht.1 (tupSplit (splitToTup hf xs)).1 p.1 (congrArg Prod.fst h12)
        (fun va hva => packFromLegal_wp target b ht.2 (tupSplit (splitToTup hf xs)).2 p.2
          (congrArg Prod.snd h12) (fun vb hvb =>
            by
              dsimp only [wp, Op.wp, OpCode.wp]
              exact hk _ (Prod.ext hva hvb)))

theorem splitLegalToLeaves_wp (target : LegalTarget) {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} :
    ∀ (t : Ty), target.supportsTy t = true → (xs : Tup (Arg Val) (target.legalTys t)) →
      (x : Val t) → valsTup xs = encodeVal target t x →
      {k : Tup (Arg Val) (target.leafTys t) → Expr Val Cont rs} → {m : Mem 64} →
      (∀ fx, valsTup fx = leafVals target t x → wp Γ Q X (k fx) m) →
      wp Γ Q X (splitLegalToLeaves target t xs k) m
  | .bool, _, xs, _, hxs, k, _, hk => hk xs hxs
  | .bits _, _, xs, _, hxs, k, _, hk => hk xs hxs
  | .float _, _, xs, _, hxs, k, _, hk => hk xs hxs
  | .pair a b, ht, xs, p, hxs, k, m, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    dsimp only [splitLegalToLeaves]
    split
    · next hp =>
      have h' : (packedToTup hp xs).1.val = p := congrArg Prod.fst (valsTup_packedToTup_encode target hp hxs)
      exact unpackToLeaves_wp target (.pair a b) (by simp [LegalTarget.supportsTy, ht]) _
        (fun fx hfx => hk fx (by rw [hfx, h']))
    · next hp =>
      have hf := Bool.eq_false_iff.mpr hp
      have hsp := valsTup_splitToTup_encode target hf hxs
      have h12 := congrArg tupSplit hsp
      simp only [tupSplit_valsTup, tupSplit_tupAppend] at h12
      exact splitLegalToLeaves_wp target a ht.1 _ p.1 (congrArg Prod.fst h12) (fun fa hfa =>
        splitLegalToLeaves_wp target b ht.2 _ p.2 (congrArg Prod.snd h12) (fun fb hfb =>
          hk (tupAppend fa fb) (by
            dsimp only [LegalTarget.leafTys]
            rw [valsTup_tupAppend, hfa, hfb]
            rfl)))

theorem packLeavesToLegal_wp (target : LegalTarget) {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} :
    ∀ (t : Ty), target.supportsTy t = true → (fx : Tup (Arg Val) (target.leafTys t)) →
      (x : Val t) → valsTup fx = leafVals target t x →
      {k : Tup (Arg Val) (target.legalTys t) → Expr Val Cont rs} → {m : Mem 64} →
      (∀ res, valsTup res = encodeVal target t x → wp Γ Q X (k res) m) →
      wp Γ Q X (packLeavesToLegal target t fx k) m
  | .bool, _, fx, _, hfx, k, _, hk => hk fx hfx
  | .bits _, _, fx, _, hfx, k, _, hk => hk fx hfx
  | .float _, _, fx, _, hfx, k, _, hk => hk fx hfx
  | .pair a b, ht, fx, p, hfx, k, m, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    dsimp only [LegalTarget.leafTys] at fx hfx
    dsimp only [packLeavesToLegal]
    have h12 := congrArg (tupSplit (as := target.leafTys a) (bs := target.leafTys b)) hfx
    rw [leafVals_pair, tupSplit_tupAppend, tupSplit_valsTup] at h12
    have h1 : valsTup (tupSplit (as := target.leafTys a) (bs := target.leafTys b) fx).1 = leafVals target a p.1 :=
      congrArg Prod.fst h12
    have h2 : valsTup (tupSplit (as := target.leafTys a) (bs := target.leafTys b) fx).2 = leafVals target b p.2 :=
      congrArg Prod.snd h12
    split
    · next hp =>
      exact packLeavesToLegal_wp target a ht.1 _ p.1 h1 (fun la hla =>
        packLeavesToLegal_wp target b ht.2 _ p.2 h2 (fun lb hlb =>
          packFromLegal_wp target a ht.1 la p.1 hla (fun va hva =>
            packFromLegal_wp target b ht.2 lb p.2 hlb (fun vb hvb =>
              by
                dsimp only [wp, Op.wp, OpCode.wp]
                exact hk _ (valsTup_tupToPacked_encode target hp
                  (by rw [valsTup_single]; exact congrArg (·, ()) (Prod.ext hva hvb)))))))
    · next hp =>
      have hf := Bool.eq_false_iff.mpr hp
      exact packLeavesToLegal_wp target a ht.1 _ p.1 h1 (fun la hla =>
        packLeavesToLegal_wp target b ht.2 _ p.2 h2 (fun lb hlb =>
          hk _ (valsTup_tupToSplit_encode target hf
            (by rw [valsTup_tupAppend, hla, hlb]))))

/-! ### Scalar BitVec widening, masking, sign-extension, ternary logic, and bool-op `_wp` helpers -/

private theorem lowMask_and {n w : Nat} (hnw : n ≤ w) (x : BitVec w) :
    x &&& lowMask n w = (x.setWidth n).setWidth w := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, lowMask, BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_allOnes, BitVec.getLsbD_setWidth]
  by_cases hin : i < n
  · have hiw : w - n + i < w := by omega
    simp [hi, hin, hiw]
  · have hiw : ¬ (w - n + i < w) := by omega
    simp [hi, hin, hiw]

private theorem bitVec0_eq_zero (x : BitVec 0) : x = 0#0 := Subsingleton.elim _ _

private theorem setWidth_zero_setWidth {w : Nat} (x : BitVec w) :
    (x.setWidth 0).setWidth w = 0#w := by
  rw [bitVec0_eq_zero (x.setWidth 0)]; rfl

theorem emitMaskToN_wp {target_Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {n w : Nat} (hnw : n ≤ w) {x : Arg Val (.bits w)} {v : BitVec w} (hx : x.val = v)
    {k : Arg Val (.bits w) → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r, r.val = (v.setWidth n).setWidth w → wp target_Γ Q X (k r) m) :
    wp target_Γ Q X (emitMaskToN n w x k) m := by
  dsimp only [emitMaskToN]
  by_cases hn0 : n = 0
  · subst hn0
    simp only [beq_self_eq_true, ↓reduceIte]
    exact hk _ (setWidth_zero_setWidth v).symm
  · have hn0' : (n == 0) = false := beq_false_of_ne hn0
    simp only [hn0', Bool.false_eq_true, ↓reduceIte]
    by_cases hwn : w ≤ n
    · have heq : n = w := Nat.le_antisymm hnw hwn
      subst heq
      simp only [hwn, ↓reduceIte]
      exact hk x (by rw [hx, BitVec.setWidth_eq, BitVec.setWidth_eq])
    · simp only [hwn, ↓reduceIte, wp, Op.wp, OpCode.wp]
      exact hk _ (by change x.val &&& lowMask n w = _; rw [hx, lowMask_and hnw])

private theorem signExtend_eq_shl_ashr {n w : Nat} (hn0 : 0 < n) (hnw : n < w) (a : BitVec n) :
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

theorem emitSextToW_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {n w : Nat} (hn0 : 0 < n) (hnw : n ≤ w) {x : Arg Val (.bits w)} {a : BitVec n}
    (hx : x.val = a.setWidth w) {k : Arg Val (.bits w) → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r, r.val = a.signExtend w → wp Γ Q X (k r) m) :
    wp Γ Q X (emitSextToW n w x k) m := by
  dsimp only [emitSextToW]
  by_cases hle : w ≤ n
  · have heq : n = w := Nat.le_antisymm hnw hle
    subst heq
    have hcond : (n == 0 || decide (n ≤ n)) = true := by
      simp only [Nat.le_refl, decide_true, Bool.or_true]
    simp only [hcond]
    exact hk x (by rw [hx, BitVec.setWidth_eq, BitVec.signExtend_eq])
  · have hnwl : n < w := by omega
    have hn0f : (n == 0) = false := beq_false_of_ne (by omega)
    have hcond : (n == 0 || decide (w ≤ n)) = false := by
      simp only [hn0f, Bool.false_or, decide_eq_false hle]
    simp only [hcond, Bool.false_eq_true, ↓reduceIte]
    dsimp only [wp, Op.wp, OpCode.wp, vals, lift2, Arg.val_imm]
    have hpow : w < 2 ^ w := @Nat.lt_pow_self w 2 (by decide)
    have hsh_mod : (BitVec.ofNat w (w - n)).toNat % w = w - n := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans (by omega) hpow), Nat.mod_eq_of_lt (by omega)]
    refine hk _ ?_
    change (x.val <<< ((BitVec.ofNat w (w - n)).toNat % w)).sshiftRight
      ((BitVec.ofNat w (w - n)).toNat % w) = a.signExtend w
    rw [hx, hsh_mod]
    exact signExtend_eq_shl_ashr hn0 hnwl a

theorem emitCountMod_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {n w : Nat} (hn0 : 0 < n) (hnw : n < w) {c : Arg Val (.bits w)} {b : BitVec n}
    (hc : c.val = b.setWidth w) {k : Arg Val (.bits w) → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r, r.val = BitVec.ofNat w (b.toNat % n) → wp Γ Q X (k r) m) :
    wp Γ Q X (emitCountMod n w c k) m := by
  have h2nw : 2 ^ n < 2 ^ w := Nat.pow_lt_pow_right (by omega) hnw
  have hcn : c.val.toNat = b.toNat := by
    rw [hc, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans b.isLt h2nw)]
  cases c with
  | imm cb =>
    dsimp only [emitCountMod]
    exact hk _ (by dsimp only [Arg.val] at hcn ⊢; rw [hcn])
  | var _ =>
    dsimp only [emitCountMod, wp, Op.wp, OpCode.wp, vals]
    have hpow : w < 2 ^ w := @Nat.lt_pow_self w 2 (by decide)
    have hn_lt : n < 2 ^ w := Nat.lt_trans hnw hpow
    have hof_nat : (BitVec.ofNat w n).toNat = n := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn_lt]
    refine ⟨?_, hk _ ?_⟩
    · intro h0
      dsimp only [Arg.val_imm] at h0
      have h0' := congrArg BitVec.toNat h0
      rw [hof_nat] at h0'
      exact Nat.ne_of_gt hn0 h0'
    · apply BitVec.eq_of_toNat_eq
      dsimp only [Arg.val] at hcn ⊢
      rw [BitVec.toNat_umod, hcn, hof_nat, BitVec.toNat_ofNat]
      symm
      exact Nat.mod_eq_of_lt (Nat.lt_trans (Nat.lt_trans (Nat.mod_lt _ hn0) hnw) hpow)

private theorem boolCmp_spec (o : CmpOp) (a b : Bool) :
    (match o with
     | .eq => !(a ^^ b)
     | .ne => a ^^ b
     | .ult | .sgt => !a && b
     | .ule | .sge => !a || b
     | .ugt | .slt => a && !b
     | .uge | .sle => a || !b) = o.evalBool a b := by
  cases o <;> cases a <;> cases b <;> rfl

private theorem emitBoolCmp_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (o : CmpOp) (a b : Arg Val .bool) {k : Arg Val .bool → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r, r.val = o.evalBool a.val b.val → wp Γ Q X (k r) m) :
    wp Γ Q X (emitBoolCmp o a b k) m := by
  have hsp := boolCmp_spec o a.val b.val
  cases o <;> dsimp only [emitBoolCmp, wp, Op.wp, OpCode.wp, vals, lift1, lift2] at * <;>
    exact hk _ hsp

private theorem emitBoolSelect_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (c a b : Arg Val .bool) {k : Arg Val .bool → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r, r.val = (if c.val then a.val else b.val) → wp Γ Q X (k r) m) :
    wp Γ Q X (emitBoolSelect c a b k) m := by
  dsimp only [emitBoolSelect, wp, Op.wp, OpCode.wp, vals, lift1, lift2]
  exact hk _ (by cases c.val <;> cases a.val <;> cases b.val <;> rfl)

private theorem list_drop_range8 :
    ∀ idx < 8, (List.range 8).drop idx = idx :: (List.range 8).drop (idx + 1)
  | 0, _ => rfl | 1, _ => rfl | 2, _ => rfl | 3, _ => rfl
  | 4, _ => rfl | 5, _ => rfl | 6, _ => rfl | 7, _ => rfl

private theorem ite_arg_val {t : Ty}
    (c : Prop) [Decidable c] (a b : Arg Val t) :
    (if c then a else b).val = if c then a.val else b.val := by
  by_cases h : c
  · rw [ite_eq_left h, ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right h]

private theorem emitTernlogBits_go_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {w : Nat}
    (a b c na nb nc : Arg Val (.bits w))
    (hna : na.val = ~~~a.val) (hnb : nb.val = ~~~b.val) (hnc : nc.val = ~~~c.val)
    (imm : BitVec 8) :
    ∀ (d idx : Nat), idx + d = 8 →
      ∀ (acc : Option (Arg Val (.bits w)))
        {k : Arg Val (.bits w) → Expr Val Cont rs} {m : Mem 64},
        (∀ r, r.val =
          ((List.range 8).drop idx).foldl (fun cur i =>
            if imm.getLsbD i then
              cur ||| ((if i / 4 % 2 == 1 then a.val else na.val) &&&
                       (if i / 2 % 2 == 1 then b.val else nb.val) &&&
                       (if i % 2 == 1 then c.val else nc.val))
            else cur) (match acc with | some v => v.val | none => 0#w) →
          wp Γ Q X (k r) m) →
        wp Γ Q X (emitTernlogBits.go w imm k idx acc a b c na nb nc) m
  | 0, idx, hd, acc, k, _, hk => by
    have hge : idx ≥ 8 := by omega
    have hdrop : (List.range 8).drop idx = [] := List.drop_eq_nil_of_le (by simp; omega)
    rw [emitTernlogBits.go.eq_def, ite_eq_left hge]
    cases acc with
    | none => exact hk (.imm 0#w) (by simp [hdrop])
    | some v => exact hk v (by simp [hdrop])
  | d + 1, idx, hd, acc, k, m, hk => by
    have hlt : ¬ (idx ≥ 8) := by omega
    have hdrop := list_drop_range8 idx (by omega)
    rw [emitTernlogBits.go.eq_def, ite_eq_right hlt]
    by_cases himm : imm.getLsbD idx = true
    · rw [ite_eq_left himm]
      dsimp only [wp, Op.wp, OpCode.wp, vals, lift2]
      cases acc with
      | none =>
        refine emitTernlogBits_go_wp a b c na nb nc hna hnb hnc imm d (idx + 1) (by omega)
          (some (.var _)) fun r hr => hk r ?_
        rw [hr, hdrop]
        simp [himm, lift2, ite_arg_val]
      | some prev =>
        dsimp only [wp, Op.wp, OpCode.wp, vals, lift2]
        refine emitTernlogBits_go_wp a b c na nb nc hna hnb hnc imm d (idx + 1) (by omega)
          (some (.var _)) fun r hr => hk r ?_
        rw [hr, hdrop]
        simp [himm, lift2, ite_arg_val]
    · rw [ite_eq_right himm]
      refine emitTernlogBits_go_wp a b c na nb nc hna hnb hnc imm d (idx + 1) (by omega) acc
        fun r hr => hk r ?_
      rw [hr, hdrop]
      simp [himm]

private theorem ternaryLogic_allOnes {w : Nat} (a b c : BitVec w) :
    ternaryLogic a b c 0xff#8 = BitVec.allOnes w := by
  ext i hi
  rw [show (0xff#8 : BitVec 8) = BitVec.allOnes 8 from rfl]
  simp only [← BitVec.getLsbD_eq_getElem, ternaryLogic, BitVec.getLsbD_allOnes, hi, decide_true]
  rw [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  simp only [List.foldl_cons, List.foldl_nil]
  cases ha : a[i] <;> cases hb : b[i] <;> cases hc : c[i] <;>
    simp [hi, ha, hb, hc]

private theorem ternaryLogic_zero {w : Nat} (a b c : BitVec w) :
    ternaryLogic a b c 0#8 = 0#w := by
  simp [ternaryLogic, List.range_succ]

theorem emitTernlogBits_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {w : Nat}
    (a b c : Arg Val (.bits w)) (imm : BitVec 8)
    {k : Arg Val (.bits w) → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r, r.val = ternaryLogic a.val b.val c.val imm → wp Γ Q X (k r) m) :
    wp Γ Q X (emitTernlogBits w a b c imm k) m := by
  dsimp only [emitTernlogBits]
  by_cases h0 : (imm == 0#8) = true
  · rw [ite_eq_left h0]
    have himm : imm = 0#8 := beq_iff_eq.mp h0
    subst himm
    exact hk (.imm 0#w) (ternaryLogic_zero a.val b.val c.val).symm
  · rw [ite_eq_right h0]
    by_cases hff : (imm == 0xff#8) = true
    · rw [ite_eq_left hff]
      have himm : imm = 0xff#8 := beq_iff_eq.mp hff
      subst himm
      exact hk (.imm (BitVec.allOnes w)) (ternaryLogic_allOnes a.val b.val c.val).symm
    · rw [ite_eq_right hff]
      dsimp only [wp, Op.wp, OpCode.wp, vals, lift1]
      exact emitTernlogBits_go_wp a b c (.var _) (.var _) (.var _) rfl rfl rfl imm 8 0 rfl none
        fun r hr => hk r (by simpa [ternaryLogic] using hr)

private theorem emitTernlogBool_go_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (a b c na nb nc : Arg Val .bool)
    (hna : na.val = !a.val) (hnb : nb.val = !b.val) (hnc : nc.val = !c.val)
    (imm : BitVec 8) :
    ∀ (d idx : Nat), idx + d = 8 →
      ∀ (acc : Option (Arg Val .bool))
        {k : Arg Val .bool → Expr Val Cont rs} {m : Mem 64},
        (∀ r, r.val =
          ((List.range 8).drop idx).foldl (fun cur i =>
            if imm.getLsbD i then
              cur || ((if i / 4 % 2 == 1 then a.val else na.val) &&
                      (if i / 2 % 2 == 1 then b.val else nb.val) &&
                      (if i % 2 == 1 then c.val else nc.val))
            else cur) (match acc with | some v => v.val | none => false) →
          wp Γ Q X (k r) m) →
        wp Γ Q X (emitTernlogBool.go imm k idx acc a b c na nb nc) m
  | 0, idx, hd, acc, k, _, hk => by
    have hge : idx ≥ 8 := by omega
    have hdrop : (List.range 8).drop idx = [] := List.drop_eq_nil_of_le (by simp; omega)
    rw [emitTernlogBool.go.eq_def, ite_eq_left hge]
    cases acc with
    | none => exact hk (.imm false) (by simp [hdrop])
    | some v => exact hk v (by simp [hdrop])
  | d + 1, idx, hd, acc, k, m, hk => by
    have hlt : ¬ (idx ≥ 8) := by omega
    have hdrop := list_drop_range8 idx (by omega)
    rw [emitTernlogBool.go.eq_def, ite_eq_right hlt]
    by_cases himm : imm.getLsbD idx = true
    · rw [ite_eq_left himm]
      dsimp only [wp, Op.wp, OpCode.wp, vals, lift2]
      cases acc with
      | none =>
        refine emitTernlogBool_go_wp a b c na nb nc hna hnb hnc imm d (idx + 1) (by omega)
          (some (.var _)) fun r hr => hk r ?_
        rw [hr, hdrop]
        simp [himm, lift2, ite_arg_val]
      | some prev =>
        dsimp only [wp, Op.wp, OpCode.wp, vals, lift2]
        refine emitTernlogBool_go_wp a b c na nb nc hna hnb hnc imm d (idx + 1) (by omega)
          (some (.var _)) fun r hr => hk r ?_
        rw [hr, hdrop]
        simp [himm, lift2, ite_arg_val]
    · rw [ite_eq_right himm]
      refine emitTernlogBool_go_wp a b c na nb nc hna hnb hnc imm d (idx + 1) (by omega) acc
        fun r hr => hk r ?_
      rw [hr, hdrop]
      simp [himm]

theorem emitTernlogBool_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (a b c : Arg Val .bool) (imm : BitVec 8)
    {k : Arg Val .bool → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r, r.val = ternaryLogicBool a.val b.val c.val imm → wp Γ Q X (k r) m) :
    wp Γ Q X (emitTernlogBool a b c imm k) m := by
  dsimp only [emitTernlogBool]
  by_cases h0 : (imm == 0#8) = true
  · rw [ite_eq_left h0]
    have himm : imm = 0#8 := beq_iff_eq.mp h0
    subst himm
    exact hk (.imm false) (by simp [ternaryLogicBool])
  · rw [ite_eq_right h0]
    by_cases hff : (imm == 0xff#8) = true
    · rw [ite_eq_left hff]
      have himm : imm = 0xff#8 := beq_iff_eq.mp hff
      subst himm
      exact hk (.imm true) (by
        have h : ∀ va vb vc : Bool, ternaryLogicBool va vb vc 0xff#8 = true := by decide
        exact (h a.val b.val c.val).symm)
    · rw [ite_eq_right hff]
      dsimp only [wp, Op.wp, OpCode.wp, vals, lift1]
      refine emitTernlogBool_go_wp a b c (.var _) (.var _) (.var _) rfl rfl rfl imm 8 0 rfl none
        fun r hr => hk r ?_
      have hfold : ∀ (va vb vc : Bool) (imm : BitVec 8),
          ([0, 1, 2, 3, 4, 5, 6, 7].foldl (fun cur i =>
            if imm.getLsbD i then
              cur || ((if i / 4 % 2 == 1 then va else !va) &&
                      (if i / 2 % 2 == 1 then vb else !vb) &&
                      (if i % 2 == 1 then vc else !vc))
            else cur) false) = ternaryLogicBool va vb vc imm := by
        intro va vb vc imm
        cases va <;> cases vb <;> cases vc <;> simp [ternaryLogicBool]
      rw [hr, show (List.range 8).drop 0 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
      exact hfold a.val b.val c.val imm

/-! ### BitVec widening arithmetic, shift, bit-manipulation, comparison, and conversion lemmas -/

private theorem toNat_setWidth_of_le {n w : Nat} (hnw : n ≤ w) (a : BitVec n) :
    (a.setWidth w).toNat = a.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt]
  exact Nat.lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by decide : 0 < 2) hnw)

private theorem setWidth_inj_of_le {n w : Nat} (hnw : n ≤ w) {a b : BitVec n}
    (h : a.setWidth w = b.setWidth w) : a = b := by
  apply BitVec.eq_of_toNat_eq
  rw [← toNat_setWidth_of_le hnw a, ← toNat_setWidth_of_le hnw b, h]

private theorem setWidth_setWidth_lowMask {n w : Nat} (hnw : n ≤ w) (x : BitVec w) :
    (x.setWidth n).setWidth w = x &&& lowMask n w :=
  (lowMask_and hnw x).symm

private theorem setWidth_add_of_le {n w : Nat} (hnw : n ≤ w) (a b : BitVec n) :
    (a.setWidth w + b.setWidth w) &&& lowMask n w = (a + b).setWidth w := by
  rw [lowMask_and hnw]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_add,
    toNat_setWidth_of_le hnw a, toNat_setWidth_of_le hnw b]
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hnw)

private theorem setWidth_mul_of_le {n w : Nat} (hnw : n ≤ w) (a b : BitVec n) :
    (a.setWidth w * b.setWidth w) &&& lowMask n w = (a * b).setWidth w := by
  rw [lowMask_and hnw]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_mul, BitVec.toNat_mul,
    toNat_setWidth_of_le hnw a, toNat_setWidth_of_le hnw b]
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hnw)

private theorem setWidth_sub_of_le {n w : Nat} (hnw : n ≤ w) (a b : BitVec n) :
    (a.setWidth w - b.setWidth w) &&& lowMask n w = (a - b).setWidth w := by
  rw [lowMask_and hnw]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_sub,
    toNat_setWidth_of_le hnw a, toNat_setWidth_of_le hnw b]
  have hdvd : 2 ^ n ∣ 2 ^ w := Nat.pow_dvd_pow 2 hnw
  rcases hdvd with ⟨k, hk⟩
  have hkpos : 0 < k := Nat.pos_of_ne_zero fun hk0 => by
    rw [hk0, Nat.mul_zero] at hk
    exact Nat.ne_of_gt (Nat.two_pow_pos w) hk
  have ha : a.toNat < 2 ^ n := a.isLt
  have hb : b.toNat < 2 ^ n := b.isLt
  have hk1 : 2 ^ n * k = 2 ^ n * (k - 1) + 2 ^ n := by
    calc 2 ^ n * k = 2 ^ n * (k - 1 + 1) := by rw [Nat.sub_add_cancel hkpos]
      _ = 2 ^ n * (k - 1) + 2 ^ n := Nat.mul_add_one _ _
  have h1 : 2 ^ w - b.toNat + a.toNat = (k - 1) * 2 ^ n + (2 ^ n - b.toNat + a.toNat) := by
    rw [hk, hk1, Nat.mul_comm (2 ^ n) (k - 1)]
    omega
  rw [Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hnw), h1, Nat.mul_comm (k - 1), Nat.mul_add_mod]

private theorem setWidth_neg_of_le {n w : Nat} (hnw : n ≤ w) (a : BitVec n) :
    (-(a.setWidth w)) &&& lowMask n w = (-a).setWidth w := by
  have hz : (0#n).setWidth w = 0#w := BitVec.setWidth_zero w n
  have hsub := setWidth_sub_of_le hnw 0#n a
  rw [hz] at hsub
  simpa using hsub

private theorem setWidth_and_of_le {n w : Nat} (a b : BitVec n) :
    a.setWidth w &&& b.setWidth w = (a &&& b).setWidth w := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_and, BitVec.getLsbD_setWidth, hi,
    decide_true, Bool.true_and]

private theorem setWidth_or_of_le {n w : Nat} (a b : BitVec n) :
    a.setWidth w ||| b.setWidth w = (a ||| b).setWidth w := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_or, BitVec.getLsbD_setWidth, hi,
    decide_true, Bool.true_and]

private theorem setWidth_xor_of_le {n w : Nat} (a b : BitVec n) :
    a.setWidth w ^^^ b.setWidth w = (a ^^^ b).setWidth w := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_xor, BitVec.getLsbD_setWidth, hi,
    decide_true, Bool.true_and]

private theorem setWidth_not_of_le {n w : Nat} (hnw : n ≤ w) (a : BitVec n) :
    (~~~(a.setWidth w)) &&& lowMask n w = (~~~a).setWidth w := by
  rw [lowMask_and hnw]
  congr 1
  ext i hi
  have hiw : i < w := Nat.lt_of_lt_of_le hi hnw
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_setWidth, BitVec.getLsbD_not, hi, hiw,
    decide_true, Bool.true_and]

private theorem setWidth_shl_of_lt {n w : Nat} (hnw : n < w) (a : BitVec n) (s : Nat) :
    ((a.setWidth w) <<< s) &&& lowMask n w = (a <<< s).setWidth w := by
  rw [lowMask_and (Nat.le_of_lt hnw)]
  congr 1
  ext i hi
  have hiw : i < w := Nat.lt_trans hi hnw
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft,
    hi, hiw, decide_true, Bool.true_and]
  have hlt : decide (i - s < w) = true := decide_eq_true (by omega)
  simp only [hlt, Bool.true_and]

private theorem setWidth_lshr_of_le {n w : Nat} (hnw : n ≤ w) (a : BitVec n) (s : Nat) :
    (a.setWidth w) >>> s = (a >>> s).setWidth w := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth, hi]
  by_cases his : s + i < n
  · have hisw : s + i < w := Nat.lt_of_lt_of_le his hnw
    simp [his, hisw]
  · have hfalse : a.getLsbD (s + i) = false := BitVec.getLsbD_of_ge a (s + i) (by omega)
    simp [hfalse]

private theorem msb_signExtend_of_pos_le {n w : Nat} (hn0 : 0 < n) (hnw : n ≤ w) (a : BitVec n) :
    (a.signExtend w).msb = a.msb := by
  rw [BitVec.msb_eq_getLsbD_last, BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_signExtend]
  have hw0 : w - 1 < w := by omega
  have hnot : ¬ (w - 1 < n) ∨ n = w := by omega
  rcases hnot with hge | rfl
  · simp [hw0, hge, BitVec.msb_eq_getLsbD_last]
  · simp [hw0]

private theorem setWidth_ashr_signExtend_of_lt {n w : Nat} (hn0 : 0 < n) (hnw : n < w)
    (a : BitVec n) (s : Nat) :
    ((a.signExtend w).sshiftRight s) &&& lowMask n w = (a.sshiftRight s).setWidth w := by
  rw [lowMask_and (Nat.le_of_lt hnw)]
  congr 1
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_setWidth, BitVec.getLsbD_sshiftRight,
    BitVec.getLsbD_signExtend, hi, decide_true, Bool.true_and]
  rw [msb_signExtend_of_pos_le hn0 (Nat.le_of_lt hnw) a]
  have hnw1 : decide (w ≤ i) = false := decide_eq_false (by omega)
  have hnw2 : decide (n ≤ i) = false := decide_eq_false (by omega)
  by_cases hsn : s + i < n
  · have hsw : s + i < w := Nat.lt_trans hsn hnw
    simp [hnw1, hnw2, hsn, hsw]
  · by_cases hsw : s + i < w <;> simp [hnw1, hnw2, hsn, hsw]

private theorem setWidth_rotl_of_lt {n w : Nat} (hn0 : 0 < n) (hnw : n < w)
    (a b : BitVec n) :
    let s := b.toNat % n
    (((a.setWidth w) <<< s) ||| ((a.setWidth w) >>> (n - s))) &&& lowMask n w =
      (a.rotateLeft (b.toNat % n)).setWidth w := by
  intro s
  have hsn : s < n := Nat.mod_lt _ hn0
  rw [lowMask_and (Nat.le_of_lt hnw)]
  congr 1
  ext i hi
  have hiw : i < w := Nat.lt_trans hi hnw
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_setWidth, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_rotateLeft,
    hi, hiw, decide_true, Bool.true_and]
  by_cases his : i < s
  · have h2 : n - s + i < n := by omega
    have h3 : n - s + i < w := Nat.lt_trans h2 hnw
    dsimp only [s] at his h3 ⊢
    simp [his, h3]
  · have hisn : i - s < n := by omega
    have hisw : i - s < w := Nat.lt_trans hisn hnw
    have hge : n ≤ n - s + i := by omega
    have hfalse : a.getLsbD (n - s + i) = false := BitVec.getLsbD_of_ge a (n - s + i) hge
    dsimp only [s] at his hisw hfalse ⊢
    simp [his, hisw, hfalse]

private theorem setWidth_rotr_of_lt {n w : Nat} (hn0 : 0 < n) (hnw : n < w)
    (a b : BitVec n) :
    let s := b.toNat % n
    (((a.setWidth w) >>> s) ||| ((a.setWidth w) <<< (n - s))) &&& lowMask n w =
      (a.rotateRight (b.toNat % n)).setWidth w := by
  intro s
  have hsn : s < n := Nat.mod_lt _ hn0
  rw [lowMask_and (Nat.le_of_lt hnw)]
  congr 1
  ext i hi
  have hiw : i < w := Nat.lt_trans hi hnw
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_setWidth, BitVec.getLsbD_or,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_rotateRight,
    hi, hiw, decide_true, Bool.true_and]
  by_cases hsi : s + i < n
  · have hlt : i < n - s := by omega
    have hsw : s + i < w := Nat.lt_trans hsi hnw
    dsimp only [s] at hlt hsw ⊢
    simp [hlt, hsw]
  · have hns : ¬ (i < n - s) := by omega
    have hge : n ≤ s + i := by omega
    have hfalse : a.getLsbD (s + i) = false := BitVec.getLsbD_of_ge a (s + i) hge
    have hsub : i - (n - s) < n := by omega
    have hsubw : i - (n - s) < w := Nat.lt_trans hsub hnw
    dsimp only [s] at hns hfalse hsubw ⊢
    simp [hns, hfalse, hsubw]

private theorem countMod_toNat_mod {n w : Nat} (hn0 : 0 < n) (hnw : n < w) (b : BitVec n) :
    (BitVec.ofNat w (b.toNat % n)).toNat % w = b.toNat % n := by
  have hpow : w < 2 ^ w := @Nat.lt_pow_self w 2 (by decide)
  have hb : b.toNat % n < n := Nat.mod_lt _ hn0
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hb (Nat.lt_trans hnw hpow)),
    Nat.mod_eq_of_lt (Nat.lt_trans hb hnw)]

private theorem ofNat_sub_toNat_mod {n w s : Nat} (hnw : n < w) (hs : s < n) :
    (BitVec.ofNat w n - BitVec.ofNat w s).toNat % w = n - s := by
  have hpow : w < 2 ^ w := @Nat.lt_pow_self w 2 (by decide)
  have h1 : (BitVec.ofNat w n).toNat = n := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h2 : (BitVec.ofNat w s).toNat = s := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hdiff : (BitVec.ofNat w n - BitVec.ofNat w s).toNat = n - s := by
    rw [BitVec.toNat_sub, h1, h2]
    have hsplit : 2 ^ w - s + n = 2 ^ w + (n - s) := by omega
    rw [hsplit, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  rw [hdiff, Nat.mod_eq_of_lt (by omega)]

theorem legalBitsArith_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost} {n : Nat} (hn : target.supportsTy (.bits n) = true)
    (c : OpCode [.bits n, .bits n] [.bits n])
    (hc : match c with
      | .add _ | .sub _ | .mul _ | .and _ | .or _ | .xor _
      | .shl _ | .lshr _ | .ashr _ | .rotl _ | .rotr _ => True
      | _ => False)
    (a' b' : Arg Val (.bits (target.widenWidth n))) (a b : BitVec n)
    (ha : a'.val = a.setWidth (target.widenWidth n))
    (hb : b'.val = b.setWidth (target.widenWidth n))
    {k : Arg Val (.bits (target.widenWidth n)) → Expr Val Cont rs} {m : Mem 64}
    (hk : Op.wp ⟨c, ((Arg.imm a : Arg Val (.bits n)), Arg.imm b, ())⟩
      (fun (res, ()) => ∀ r, r.val = res.setWidth (target.widenWidth n) → wp Γ Q X (k r) m)) :
    wp Γ Q X (legalBitsArith target n c a' b' k) m := by
  have hnw : n ≤ target.widenWidth n := le_widenWidth_of_supports hn
  dsimp only [legalBitsArith]
  by_cases hn0 : n = 0
  · subst hn0
    have ha0 : a = 0#0 := bitVec0_eq_zero a
    have hb0 : b = 0#0 := bitVec0_eq_zero b
    subst ha0; subst hb0
    simp only [beq_self_eq_true, ↓reduceIte]
    have h0 : ∀ v : BitVec 0, v.setWidth (target.widenWidth 0) = 0#(target.widenWidth 0) :=
      fun v => by rw [bitVec0_eq_zero v, BitVec.setWidth_zero _ 0]
    cases c <;> try exact hc.elim
    all_goals
      dsimp only [Op.wp, OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, vals, Arg.val_imm, lift2] at hk
      exact hk (.imm 0#(target.widenWidth 0)) (by simp [h0])
  · have hn0pos : 0 < n := Nat.pos_of_ne_zero hn0
    have hn0f : (n == 0) = false := beq_false_of_ne hn0
    simp only [hn0f, Bool.false_eq_true, ↓reduceIte]
    cases c with
    | add _ =>
      dsimp only [Op.wp, OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, vals, Arg.val_imm, lift2] at hk
      simp only [wp, Op.wp, OpCode.wp, op2, vals, lift2]
      refine emitMaskToN_wp hnw rfl fun r hr => hk r ?_
      rw [hr, ← lowMask_and hnw]
      change (a'.val + b'.val) &&& lowMask n (target.widenWidth n) = _
      rw [ha, hb, setWidth_add_of_le hnw]
    | sub _ =>
      dsimp only [Op.wp, OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, vals, Arg.val_imm, lift2] at hk
      simp only [wp, Op.wp, OpCode.wp, op2, vals, lift2]
      refine emitMaskToN_wp hnw rfl fun r hr => hk r ?_
      rw [hr, ← lowMask_and hnw]
      change (a'.val - b'.val) &&& lowMask n (target.widenWidth n) = _
      rw [ha, hb, setWidth_sub_of_le hnw]
    | mul _ =>
      dsimp only [Op.wp, OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, vals, Arg.val_imm, lift2] at hk
      simp only [wp, Op.wp, OpCode.wp, op2, vals, lift2]
      refine emitMaskToN_wp hnw rfl fun r hr => hk r ?_
      rw [hr, ← lowMask_and hnw]
      change (a'.val * b'.val) &&& lowMask n (target.widenWidth n) = _
      rw [ha, hb, setWidth_mul_of_le hnw]
    | and _ =>
      dsimp only [Op.wp, OpCode.wp, vals, Arg.val_imm, lift2] at hk
      simp only [wp, Op.wp, OpCode.wp, op2, vals, lift2]
      exact hk _ (by change a'.val &&& b'.val = _; rw [ha, hb, setWidth_and_of_le])
    | or _ =>
      dsimp only [Op.wp, OpCode.wp, vals, Arg.val_imm, lift2] at hk
      simp only [wp, Op.wp, OpCode.wp, op2, vals, lift2]
      exact hk _ (by change a'.val ||| b'.val = _; rw [ha, hb, setWidth_or_of_le])
    | xor _ =>
      dsimp only [Op.wp, OpCode.wp, vals, Arg.val_imm, lift2] at hk
      simp only [wp, Op.wp, OpCode.wp, op2, vals, lift2]
      exact hk _ (by change a'.val ^^^ b'.val = _; rw [ha, hb, setWidth_xor_of_le])
    | shl _ =>
      dsimp only [Op.wp, OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, vals, Arg.val_imm, lift2] at hk
      by_cases heq : n = target.widenWidth n
      · have hbeq : (n == target.widenWidth n) = true := beq_iff_eq.mpr heq
        simp only [hbeq, ↓reduceIte, wp, Op.wp, OpCode.wp, op2, vals, lift2]
        revert a' b' ha hb k hk
        rw [← heq]
        intro a' b' ha hb k hk
        rw [BitVec.setWidth_eq] at ha hb hk
        exact hk _ (by change a'.val <<< (b'.val.toNat % n) = _; rw [ha, hb])
      · have hlt : n < target.widenWidth n := Nat.lt_of_le_of_ne hnw heq
        have hf : (n == target.widenWidth n) = false := beq_false_of_ne heq
        simp only [hf, Bool.false_eq_true, ↓reduceIte]
        refine emitCountMod_wp hn0pos hlt hb fun cm hcm => ?_
        dsimp only [wp, Op.wp, OpCode.wp, vals, lift2]
        refine emitMaskToN_wp hnw rfl fun r hr => hk r ?_
        rw [hr, ← lowMask_and hnw]
        change (a'.val <<< (cm.val.toNat % target.widenWidth n)) &&&
          lowMask n (target.widenWidth n) = _
        rw [ha, hcm, countMod_toNat_mod hn0pos hlt b]
        exact setWidth_shl_of_lt hlt a (b.toNat % n)
    | lshr _ =>
      dsimp only [Op.wp, OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, vals, Arg.val_imm, lift2] at hk
      by_cases heq : n = target.widenWidth n
      · have hbeq : (n == target.widenWidth n) = true := beq_iff_eq.mpr heq
        simp only [hbeq, ↓reduceIte, wp, Op.wp, OpCode.wp, op2, vals, lift2]
        revert a' b' ha hb k hk
        rw [← heq]
        intro a' b' ha hb k hk
        rw [BitVec.setWidth_eq] at ha hb hk
        exact hk _ (by change a'.val >>> (b'.val.toNat % n) = _; rw [ha, hb])
      · have hlt : n < target.widenWidth n := Nat.lt_of_le_of_ne hnw heq
        have hf : (n == target.widenWidth n) = false := beq_false_of_ne heq
        simp only [hf, Bool.false_eq_true, ↓reduceIte]
        refine emitCountMod_wp hn0pos hlt hb fun cm hcm => ?_
        dsimp only [wp, Op.wp, OpCode.wp, vals, lift2]
        exact hk _ (by
          change a'.val >>> (cm.val.toNat % target.widenWidth n) = _
          rw [ha, hcm, countMod_toNat_mod hn0pos hlt b, setWidth_lshr_of_le hnw])
    | ashr _ =>
      dsimp only [Op.wp, OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, vals, Arg.val_imm, lift2] at hk
      by_cases heq : n = target.widenWidth n
      · have hbeq : (n == target.widenWidth n) = true := beq_iff_eq.mpr heq
        simp only [hbeq, ↓reduceIte, wp, Op.wp, OpCode.wp, op2, vals, lift2]
        revert a' b' ha hb k hk
        rw [← heq]
        intro a' b' ha hb k hk
        rw [BitVec.setWidth_eq] at ha hb hk
        exact hk _ (by change a'.val.sshiftRight (b'.val.toNat % n) = _; rw [ha, hb])
      · have hlt : n < target.widenWidth n := Nat.lt_of_le_of_ne hnw heq
        have hf : (n == target.widenWidth n) = false := beq_false_of_ne heq
        simp only [hf, Bool.false_eq_true, ↓reduceIte]
        refine emitCountMod_wp hn0pos hlt hb fun cm hcm =>
          emitSextToW_wp hn0pos hnw ha fun sa hsa => ?_
        dsimp only [wp, Op.wp, OpCode.wp, vals, lift2]
        refine emitMaskToN_wp hnw rfl fun r hr => hk r ?_
        rw [hr, ← lowMask_and hnw]
        change (sa.val.sshiftRight (cm.val.toNat % target.widenWidth n)) &&&
          lowMask n (target.widenWidth n) = _
        rw [hsa, hcm, countMod_toNat_mod hn0pos hlt b]
        exact setWidth_ashr_signExtend_of_lt hn0pos hlt a (b.toNat % n)
    | rotl _ =>
      dsimp only [Op.wp, OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, vals, Arg.val_imm, lift2] at hk
      by_cases heq : n = target.widenWidth n
      · have hbeq : (n == target.widenWidth n) = true := beq_iff_eq.mpr heq
        simp only [hbeq, ↓reduceIte, wp, Op.wp, OpCode.wp, op2, vals, lift2]
        revert a' b' ha hb k hk
        rw [← heq]
        intro a' b' ha hb k hk
        rw [BitVec.setWidth_eq] at ha hb hk
        exact hk _ (by change a'.val.rotateLeft (b'.val.toNat % n) = _; rw [ha, hb])
      · have hlt : n < target.widenWidth n := Nat.lt_of_le_of_ne hnw heq
        have hf : (n == target.widenWidth n) = false := beq_false_of_ne heq
        simp only [hf, Bool.false_eq_true, ↓reduceIte]
        refine emitCountMod_wp hn0pos hlt hb fun cm hcm => ?_
        dsimp only [wp, Op.wp, OpCode.wp, vals, lift2, Arg.val_imm]
        refine emitMaskToN_wp hnw rfl fun r hr => hk r ?_
        rw [hr, ← lowMask_and hnw]
        change ((a'.val <<< (cm.val.toNat % target.widenWidth n)) |||
          (a'.val >>> ((BitVec.ofNat (target.widenWidth n) n - cm.val).toNat % target.widenWidth n))) &&&
          lowMask n (target.widenWidth n) = (a.rotateLeft (b.toNat % n)).setWidth (target.widenWidth n)
        rw [ha, hcm, countMod_toNat_mod hn0pos hlt b,
          ofNat_sub_toNat_mod hlt (Nat.mod_lt _ hn0pos)]
        exact setWidth_rotl_of_lt hn0pos hlt a b
    | rotr _ =>
      dsimp only [Op.wp, OpCode.wp, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, vals, Arg.val_imm, lift2] at hk
      by_cases heq : n = target.widenWidth n
      · have hbeq : (n == target.widenWidth n) = true := beq_iff_eq.mpr heq
        simp only [hbeq, ↓reduceIte, wp, Op.wp, OpCode.wp, op2, vals, lift2]
        revert a' b' ha hb k hk
        rw [← heq]
        intro a' b' ha hb k hk
        rw [BitVec.setWidth_eq] at ha hb hk
        exact hk _ (by change a'.val.rotateRight (b'.val.toNat % n) = _; rw [ha, hb])
      · have hlt : n < target.widenWidth n := Nat.lt_of_le_of_ne hnw heq
        have hf : (n == target.widenWidth n) = false := beq_false_of_ne heq
        simp only [hf, Bool.false_eq_true, ↓reduceIte]
        refine emitCountMod_wp hn0pos hlt hb fun cm hcm => ?_
        dsimp only [wp, Op.wp, OpCode.wp, vals, lift2, Arg.val_imm]
        refine emitMaskToN_wp hnw rfl fun r hr => hk r ?_
        rw [hr, ← lowMask_and hnw]
        change ((a'.val >>> (cm.val.toNat % target.widenWidth n)) |||
          (a'.val <<< ((BitVec.ofNat (target.widenWidth n) n - cm.val).toNat % target.widenWidth n))) &&&
          lowMask n (target.widenWidth n) = (a.rotateRight (b.toNat % n)).setWidth (target.widenWidth n)
        rw [ha, hcm, countMod_toNat_mod hn0pos hlt b,
          ofNat_sub_toNat_mod hlt (Nat.mod_lt _ hn0pos)]
        exact setWidth_rotr_of_lt hn0pos hlt a b
    | _ => exact hc.elim

/-! ### Signed/unsigned compare widening, byte swap, uniform vector shift/rotate, and tree `_wp` lemmas -/

theorem signExtend_eq_setWidth_of_msb_false {n w : Nat} (_hnw : n ≤ w)
    {a : BitVec n} (hm : a.msb = false) :
    a.signExtend w = a.setWidth w := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_signExtend, BitVec.getLsbD_setWidth,
    hi, decide_true, Bool.true_and]
  by_cases hin : i < n
  · simp [hin]
  · have hfa : a.getLsbD i = false := BitVec.getLsbD_of_ge a i (by omega)
    simp [hin, hm, hfa]

private theorem not_signExtend_of_pos_le {n w : Nat} (_hn0 : 0 < n) (_hnw : n ≤ w)
    {a : BitVec n} (hm : a.msb = true) :
    ~~~(a.signExtend w) = (~~~a).setWidth w := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_not, BitVec.getLsbD_signExtend,
    BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  by_cases hin : i < n
  · simp [hin]
  · simp [hin, hm]

private theorem toNat_not_add {w : Nat} (x : BitVec w) :
    x.toNat + (~~~x).toNat = 2 ^ w - 1 := by
  have h : x + ~~~x = BitVec.allOnes w := BitVec.add_not_self x
  have hn := congrArg BitVec.toNat h
  rw [BitVec.toNat_add, BitVec.toNat_allOnes] at hn
  have h1 : x.toNat < 2 ^ w := x.isLt
  have h2 : (~~~x).toNat < 2 ^ w := (~~~x).isLt
  by_cases hlt : x.toNat + (~~~x).toNat < 2 ^ w
  · rw [Nat.mod_eq_of_lt hlt] at hn
    exact hn
  · have hm : (x.toNat + (~~~x).toNat) % 2 ^ w = x.toNat + (~~~x).toNat - 2 ^ w := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hm] at hn
    omega

private theorem two_mul_toNat_lt_iff_msb_false {n : Nat} (hn0 : 0 < n) (a : BitVec n) :
    2 * a.toNat < 2 ^ n ↔ a.msb = false := by
  have h2n : 2 ^ n = 2 * 2 ^ (n - 1) := by
    calc 2 ^ n = 2 ^ (n - 1 + 1) := by rw [Nat.sub_add_cancel hn0]
      _ = 2 ^ (n - 1) * 2 := Nat.pow_succ _ _
      _ = 2 * 2 ^ (n - 1) := Nat.mul_comm _ _
  rw [BitVec.msb_eq_decide, h2n]
  constructor
  · intro h; simp only [decide_eq_false_iff_not]; omega
  · intro h; simp only [decide_eq_false_iff_not] at h; omega

private theorem toInt_signExtend_of_pos_le {n w : Nat} (hn0 : 0 < n) (hnw : n ≤ w) (a : BitVec n) :
    (a.signExtend w).toInt = a.toInt := by
  have hw0 : 0 < w := Nat.lt_of_lt_of_le hn0 hnw
  rw [BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond]
  by_cases hm : a.msb = true
  · have hms : (a.signExtend w).msb = true := by rwa [msb_signExtend_of_pos_le hn0 hnw]
    have hna : ¬ (2 * a.toNat < 2 ^ n) := by
      rw [two_mul_toNat_lt_iff_msb_false hn0, hm]; decide
    have hns : ¬ (2 * (a.signExtend w).toNat < 2 ^ w) := by
      rw [two_mul_toNat_lt_iff_msb_false hw0, hms]; decide
    simp only [hna, hns, ↓reduceIte]
    have hnot := not_signExtend_of_pos_le hn0 hnw hm
    have h1 := toNat_not_add (a.signExtend w)
    have h2 := toNat_not_add a
    rw [hnot, toNat_setWidth_of_le hnw] at h1
    omega
  · have hmf : a.msb = false := Bool.eq_false_iff.mpr hm
    have hms : (a.signExtend w).msb = false := by rwa [msb_signExtend_of_pos_le hn0 hnw]
    have hna : 2 * a.toNat < 2 ^ n := (two_mul_toNat_lt_iff_msb_false hn0 a).2 hmf
    have hns : 2 * (a.signExtend w).toNat < 2 ^ w :=
      (two_mul_toNat_lt_iff_msb_false hw0 (a.signExtend w)).2 hms
    simp only [hna, hns, ↓reduceIte]
    rw [signExtend_eq_setWidth_of_msb_false hnw hmf, toNat_setWidth_of_le hnw]

private theorem evalBits_setWidth_unsigned {n w : Nat} (hnw : n ≤ w) (o : CmpOp)
    (ho : match o with | .slt | .sle | .sgt | .sge => False | _ => True)
    (a b : BitVec n) :
    o.evalBits (a.setWidth w) (b.setWidth w) = o.evalBits a b := by
  cases o with
  | eq => simp only [CmpOp.evalBits]; exact decide_eq_decide.2 ⟨setWidth_inj_of_le hnw, congrArg _⟩
  | ne => simp only [CmpOp.evalBits]; exact decide_eq_decide.2 (not_congr ⟨setWidth_inj_of_le hnw, congrArg _⟩)
  | ult | ule | ugt | uge =>
    simp only [CmpOp.evalBits, BitVec.ult, BitVec.ule, toNat_setWidth_of_le hnw]
  | _ => exact ho.elim

private theorem evalBits_signExtend_signed {n w : Nat} (hn0 : 0 < n) (hnw : n ≤ w) (o : CmpOp)
    (ho : match o with | .slt | .sle | .sgt | .sge => True | _ => False) (a b : BitVec n) :
    o.evalBits (a.signExtend w) (b.signExtend w) = o.evalBits a b := by
  cases o with
  | slt | sgt => simp only [CmpOp.evalBits, BitVec.slt, toInt_signExtend_of_pos_le hn0 hnw]
  | sle | sge => simp only [CmpOp.evalBits, BitVec.sle, toInt_signExtend_of_pos_le hn0 hnw]
  | _ => exact ho.elim

private theorem getLsbD_bswapBits_go {w : Nat} :
    ∀ (m : Nat) (x : BitVec w) {i : Nat}, i < 8 * m →
      (bswapBits.go x m).getLsbD i = x.getLsbD (8 * (m - 1 - i / 8) + i % 8)
  | 0, _, _, hi => by omega
  | m + 1, x, i, hi => by
    dsimp only [bswapBits.go]
    rw [BitVec.getLsbD_cast, BitVec.getLsbD_append]
    by_cases hi8 : i < 8
    · have hq : i / 8 = 0 := Nat.div_eq_of_lt hi8
      have hr : i % 8 = i := Nat.mod_eq_of_lt hi8
      simp only [hi8, ↓reduceIte, hq, hr, Nat.sub_zero, Nat.add_sub_cancel]
      rw [BitVec.getLsbD_extractLsb']
      simp [hi8]
    · have hi8' : ¬ (i < 8) := hi8
      have him : i - 8 < 8 * m := by omega
      have ih := getLsbD_bswapBits_go m x him
      have hq : i / 8 = (i - 8) / 8 + 1 := by omega
      have hr : i % 8 = (i - 8) % 8 := by omega
      have hsub : m + 1 - 1 - i / 8 = m - 1 - (i - 8) / 8 := by omega
      simp only [hi8', ↓reduceIte, ih, hsub, ← hr]

private theorem bswapBits_8 (x : BitVec 8) : bswapBits x = x := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, bswapBits, BitVec.getLsbD_setWidth, hi, decide_true,
    Bool.true_and]
  rw [getLsbD_bswapBits_go 1 x hi]
  have hq : i / 8 = 0 := Nat.div_eq_of_lt hi
  have hr : i % 8 = i := Nat.mod_eq_of_lt hi
  simp [hq, hr]

private theorem setWidth_bswap_of_lt {n w : Nat} (_hn0 : 0 < n) (hnw : n < w)
    (hn8 : n % 8 = 0) (hw8 : w % 8 = 0) (a : BitVec n) :
    (bswapBits (a.setWidth w)) >>> (w - n) = (bswapBits a).setWidth w := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth,
    bswapBits, hi, decide_true, Bool.true_and]
  by_cases hin : i < n
  · have hni : w - n + i < w := by omega
    have hnw8 : w - n + i < 8 * (w / 8) := by omega
    have hin8 : i < 8 * (n / 8) := by omega
    rw [decide_eq_true hni, decide_eq_true hin, Bool.true_and, Bool.true_and,
      getLsbD_bswapBits_go (w / 8) (a.setWidth w) hnw8,
      getLsbD_bswapBits_go (n / 8) a hin8]
    have hidx_eq : 8 * (w / 8 - 1 - (w - n + i) / 8) + (w - n + i) % 8 =
        8 * (n / 8 - 1 - i / 8) + i % 8 := by omega
    have hlt_w : 8 * (n / 8 - 1 - i / 8) + i % 8 < w := by omega
    rw [hidx_eq, BitVec.getLsbD_setWidth, decide_eq_true hlt_w, Bool.true_and]
  · have hge : ¬ (w - n + i < w) := by omega
    simp [decide_eq_false hge, decide_eq_false hin]

private theorem rotateRight_sub_eq_rotateLeft {w s : Nat} (hs0 : 0 < s) (hs : s < w) (x : BitVec w) :
    x.rotateRight (w - s) = x.rotateLeft s := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_rotateRight, BitVec.getLsbD_rotateLeft,
    hi, decide_true, Bool.true_and]
  have h1 : s % w = s := Nat.mod_eq_of_lt hs
  have h2 : (w - s) % w = w - s := Nat.mod_eq_of_lt (by omega)
  have h3 : w - (w - s) = s := by omega
  rw [h1, h2, h3]

private theorem rotateRight_and_allOnes_shl_eq_shl {w s : Nat} (hs0 : 0 < s) (hs : s < w) (x : BitVec w) :
    x.rotateRight (w - s) &&& (BitVec.allOnes w <<< s) = x <<< s := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_and, BitVec.getLsbD_rotateRight,
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes, hi, decide_true, Bool.true_and]
  have h2 : (w - s) % w = w - s := Nat.mod_eq_of_lt (by omega)
  have h3 : w - (w - s) = s := by omega
  rw [h2, h3]
  by_cases his : i < s
  · simp [his]
  · have hisw : i - s < w := by omega
    simp [his, hisw]

private theorem uniformShiftLeaf?_hasFloat_false :
    ∀ (t : Ty) (c : Val t) {w s : Nat}, uniformShiftLeaf? t c = some (w, s) → t.hasFloat = false
  | .bool, _, _, _, h => by simp [uniformShiftLeaf?] at h
  | .float _, _, _, _, h => by simp [uniformShiftLeaf?] at h
  | .bits _, _, _, _, _ => rfl
  | .pair a b, (x, y), w, s, h => by
    simp only [uniformShiftLeaf?] at h
    cases ha : uniformShiftLeaf? a x with
    | none => simp [ha] at h
    | some pa =>
      cases hb : uniformShiftLeaf? b y with
      | none => simp [ha, hb] at h
      | some pb =>
        have hfa := uniformShiftLeaf?_hasFloat_false a x ha
        have hfb := uniformShiftLeaf?_hasFloat_false b y hb
        simp [Ty.hasFloat, hfa, hfb]

private theorem uniformShiftLeaf?_lt :
    ∀ (t : Ty) (c : Val t) {w s : Nat}, uniformShiftLeaf? t c = some (w, s) → 0 < w ∧ s < w
  | .bool, _, _, _, h => by simp [uniformShiftLeaf?] at h
  | .float _, _, _, _, h => by simp [uniformShiftLeaf?] at h
  | .bits n, x, w, s, h => by
    simp only [uniformShiftLeaf?] at h
    by_cases hn0 : n = 0
    · simp [hn0] at h
    · have hf : (n == 0) = false := beq_false_of_ne hn0
      simp only [hf, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      have hpos : 0 < n := Nat.pos_of_ne_zero hn0
      exact ⟨hpos, Nat.mod_lt _ hpos⟩
  | .pair a b, (x, y), w, s, h => by
    simp only [uniformShiftLeaf?] at h
    cases ha : uniformShiftLeaf? a x with
    | none => simp [ha] at h
    | some pa =>
      cases hb : uniformShiftLeaf? b y with
      | none => simp [ha, hb] at h
      | some pb =>
        simp only [ha, hb, Bind.bind, Option.bind] at h
        by_cases hc : (pa.1 == pb.1 && pa.2 == pb.2) = true
        · simp only [hc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact uniformShiftLeaf?_lt a x ha
        · simp [hc] at h

private theorem bv_rotateLeft_zero {n : Nat} (x : BitVec n) : x.rotateLeft 0 = x := by
  ext i hi
  simp [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_rotateLeft, hi]

private theorem uniformShiftLeaf?_zero_rotl :
    ∀ (t : Ty) (x c : Val t) {w : Nat}, uniformShiftLeaf? t c = some (w, 0) →
      lift2 (fun {n} x y => x.rotateLeft (y.toNat % n)) (fun x _ => x) t x c = x
  | .bool, _, _, _, h => by simp [uniformShiftLeaf?] at h
  | .float _, _, _, _, h => by simp [uniformShiftLeaf?] at h
  | .bits n, x, c, w, h => by
    simp only [uniformShiftLeaf?] at h
    by_cases hn0 : n = 0
    · simp [hn0] at h
    · have hf : (n == 0) = false := beq_false_of_ne hn0
      simp only [hf, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, hc0⟩
      simp [lift2, hc0, bv_rotateLeft_zero]
  | .pair a b, (x1, x2), (c1, c2), w, h => by
    simp only [uniformShiftLeaf?] at h
    cases ha : uniformShiftLeaf? a c1 with
    | none => simp [ha] at h
    | some pa =>
      cases hb : uniformShiftLeaf? b c2 with
      | none => simp [ha, hb] at h
      | some pb =>
        simp only [ha, hb, Bind.bind, Option.bind] at h
        by_cases hc : (pa.1 == pb.1 && pa.2 == pb.2) = true
        · simp only [hc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          rcases hc with ⟨hweq, hseq⟩
          rcases h with ⟨rfl, h0⟩
          have ha' : uniformShiftLeaf? a c1 = some (pa.1, 0) := by
            rw [ha]; congr 1; exact Prod.ext rfl h0
          have hb' : uniformShiftLeaf? b c2 = some (pa.1, 0) := by
            rw [hb]; congr 1; exact Prod.ext hweq.symm (hseq.symm.trans h0)
          exact Prod.ext (uniformShiftLeaf?_zero_rotl a x1 c1 ha')
            (uniformShiftLeaf?_zero_rotl b x2 c2 hb')
        · simp [hc] at h

private theorem uniformShiftLeaf?_zero_shl :
    ∀ (t : Ty) (x c : Val t) {w : Nat}, uniformShiftLeaf? t c = some (w, 0) →
      lift2 (fun {n} x y => x <<< (y.toNat % n)) (fun x _ => x) t x c = x
  | .bool, _, _, _, h => by simp [uniformShiftLeaf?] at h
  | .float _, _, _, _, h => by simp [uniformShiftLeaf?] at h
  | .bits n, x, c, w, h => by
    simp only [uniformShiftLeaf?] at h
    by_cases hn0 : n = 0
    · simp [hn0] at h
    · have hf : (n == 0) = false := beq_false_of_ne hn0
      simp only [hf, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, hc0⟩
      simp [lift2, hc0]
  | .pair a b, (x1, x2), (c1, c2), w, h => by
    simp only [uniformShiftLeaf?] at h
    cases ha : uniformShiftLeaf? a c1 with
    | none => simp [ha] at h
    | some pa =>
      cases hb : uniformShiftLeaf? b c2 with
      | none => simp [ha, hb] at h
      | some pb =>
        simp only [ha, hb, Bind.bind, Option.bind] at h
        by_cases hc : (pa.1 == pb.1 && pa.2 == pb.2) = true
        · simp only [hc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, h0⟩
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          rcases hc with ⟨hweq, hseq⟩
          have ha' : uniformShiftLeaf? a c1 = some (pa.1, 0) := by
            rw [ha]; congr 1; exact Prod.ext rfl h0
          have hb' : uniformShiftLeaf? b c2 = some (pa.1, 0) := by
            rw [hb]; congr 1; exact Prod.ext hweq.symm (hseq.symm.trans h0)
          exact Prod.ext (uniformShiftLeaf?_zero_shl a x1 c1 ha')
            (uniformShiftLeaf?_zero_shl b x2 c2 hb')
        · simp [hc] at h

private theorem uniformShiftLeaf?_splat_rotl :
    ∀ (t : Ty) (x c : Val t) {w s : Nat}, uniformShiftLeaf? t c = some (w, s) → 0 < s →
      lift2 (fun {n} x y => x.rotateLeft (y.toNat % n)) (fun x _ => x) t x c =
        lift2 (fun {n} x y => x.rotateRight (y.toNat % n)) (fun x _ => x) t x
          (splatBits w (BitVec.ofNat w (w - s)) t)
  | .bool, _, _, _, _, h, _ => by simp [uniformShiftLeaf?] at h
  | .float _, _, _, _, _, h, _ => by simp [uniformShiftLeaf?] at h
  | .bits n, x, c, w, s, h, hs => by
    have ⟨hwpos, hsw⟩ := uniformShiftLeaf?_lt (.bits n) c h
    simp only [uniformShiftLeaf?] at h
    by_cases hn0 : n = 0
    · simp [hn0] at h
    · have hf : (n == 0) = false := beq_false_of_ne hn0
      simp only [hf, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simp only [lift2, splatBits, dite_true]
      have hpow : n < 2 ^ n := @Nat.lt_pow_self n 2 (by decide)
      have hsub_lt : n - c.toNat % n < 2 ^ n := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hpow
      have hmod : (BitVec.ofNat n (n - c.toNat % n)).toNat % n = n - c.toNat % n := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsub_lt, Nat.mod_eq_of_lt (by omega)]
      rw [hmod]
      exact (rotateRight_sub_eq_rotateLeft hs hsw x).symm
  | .pair a b, (x1, x2), (c1, c2), w, s, h, hs => by
    simp only [uniformShiftLeaf?] at h
    cases ha : uniformShiftLeaf? a c1 with
    | none => simp [ha] at h
    | some pa =>
      cases hb : uniformShiftLeaf? b c2 with
      | none => simp [ha, hb] at h
      | some pb =>
        simp only [ha, hb, Bind.bind, Option.bind] at h
        by_cases hc : (pa.1 == pb.1 && pa.2 == pb.2) = true
        · simp only [hc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          rcases hc with ⟨hweq, hseq⟩
          have hb' : uniformShiftLeaf? b c2 = some (pa.1, pa.2) := by
            rw [hb]; congr 1; exact Prod.ext hweq.symm hseq.symm
          exact Prod.ext (uniformShiftLeaf?_splat_rotl a x1 c1 ha hs)
            (uniformShiftLeaf?_splat_rotl b x2 c2 hb' hs)
        · simp [hc] at h

private theorem uniformShiftLeaf?_splat_shl :
    ∀ (t : Ty) (x c : Val t) {w s : Nat}, uniformShiftLeaf? t c = some (w, s) → 0 < s →
      lift2 (fun {n} x y => x <<< (y.toNat % n)) (fun x _ => x) t x c =
        lift2 (· &&& ·) (· && ·) t
          (lift2 (fun {n} x y => x.rotateRight (y.toNat % n)) (fun x _ => x) t x
            (splatBits w (BitVec.ofNat w (w - s)) t))
          (splatBits w (BitVec.allOnes w <<< s) t)
  | .bool, _, _, _, _, h, _ => by simp [uniformShiftLeaf?] at h
  | .float _, _, _, _, _, h, _ => by simp [uniformShiftLeaf?] at h
  | .bits n, x, c, w, s, h, hs => by
    have ⟨hwpos, hsw⟩ := uniformShiftLeaf?_lt (.bits n) c h
    simp only [uniformShiftLeaf?] at h
    by_cases hn0 : n = 0
    · simp [hn0] at h
    · have hf : (n == 0) = false := beq_false_of_ne hn0
      simp only [hf, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simp only [lift2, splatBits, dite_true]
      have hpow : n < 2 ^ n := @Nat.lt_pow_self n 2 (by decide)
      have hsub_lt : n - c.toNat % n < 2 ^ n := Nat.lt_of_le_of_lt (Nat.sub_le _ _) hpow
      have hmod : (BitVec.ofNat n (n - c.toNat % n)).toNat % n = n - c.toNat % n := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsub_lt, Nat.mod_eq_of_lt (by omega)]
      rw [hmod]
      exact (rotateRight_and_allOnes_shl_eq_shl hs hsw x).symm
  | .pair a b, (x1, x2), (c1, c2), w, s, h, hs => by
    simp only [uniformShiftLeaf?] at h
    cases ha : uniformShiftLeaf? a c1 with
    | none => simp [ha] at h
    | some pa =>
      cases hb : uniformShiftLeaf? b c2 with
      | none => simp [ha, hb] at h
      | some pb =>
        simp only [ha, hb, Bind.bind, Option.bind] at h
        by_cases hc : (pa.1 == pb.1 && pa.2 == pb.2) = true
        · simp only [hc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          rcases hc with ⟨hweq, hseq⟩
          have hb' : uniformShiftLeaf? b c2 = some (pa.1, pa.2) := by
            rw [hb]; congr 1; exact Prod.ext hweq.symm hseq.symm
          exact Prod.ext (uniformShiftLeaf?_splat_shl a x1 c1 ha hs)
            (uniformShiftLeaf?_splat_shl b x2 c2 hb' hs)
        · simp [hc] at h

/-! ### Relational tree weakest-precondition specs -/

def TreeRel1 (onB : Bool → (Bool → Prop) → Prop)
    (onBits : ∀ n, BitVec n → (BitVec n → Prop) → Prop)
    (onF : ∀ (f : Fmt), BitVec f.width → (BitVec f.width → Prop) → Prop) :
    (u : Ty) → Val u → (Val u → Prop) → Prop
  | .bool, x, post => onB x post
  | .bits n, x, post => onBits n x post
  | .float f, x, post => onF f x post
  | .pair a b, p, post =>
    TreeRel1 onB onBits onF a p.1 fun r1 =>
    TreeRel1 onB onBits onF b p.2 fun r2 => post (r1, r2)

theorem TreeRel1.mono {onB onBits onF}
    (hB : ∀ x {p q : Bool → Prop}, (∀ r, p r → q r) → onB x p → onB x q)
    (hBits : ∀ n x {p q : BitVec n → Prop}, (∀ r, p r → q r) → onBits n x p → onBits n x q)
    (hF : ∀ (f : Fmt) x {p q : BitVec f.width → Prop}, (∀ r, p r → q r) → onF f x p → onF f x q) :
    ∀ {u : Ty} {x : Val u} {p q : Val u → Prop}, (∀ r, p r → q r) →
      TreeRel1 onB onBits onF u x p → TreeRel1 onB onBits onF u x q
  | .bool, _, _, _, hpq, h => hB _ hpq h
  | .bits n, _, _, _, hpq, h => hBits n _ hpq h
  | .float f, _, _, _, hpq, h => hF f _ hpq h
  | .pair a b, (_, _), _, _, hpq, h =>
    TreeRel1.mono (u := a) hB hBits hF (fun r1 h2 =>
      TreeRel1.mono (u := b) hB hBits hF (fun r2 hr2 => hpq (r1, r2) hr2) h2) h

def TreeRel2 (onB : Bool → Bool → (Bool → Prop) → Prop)
    (onBits : ∀ n, BitVec n → BitVec n → (BitVec n → Prop) → Prop)
    (onF : ∀ (f : Fmt), BitVec f.width → BitVec f.width → (BitVec f.width → Prop) → Prop) :
    (u : Ty) → Val u → Val u → (Val u → Prop) → Prop
  | .bool, x, y, post => onB x y post
  | .bits n, x, y, post => onBits n x y post
  | .float f, x, y, post => onF f x y post
  | .pair a b, p, q, post =>
    TreeRel2 onB onBits onF a p.1 q.1 fun r1 =>
    TreeRel2 onB onBits onF b p.2 q.2 fun r2 => post (r1, r2)

theorem TreeRel2.mono {onB onBits onF}
    (hB : ∀ x y {p q : Bool → Prop}, (∀ r, p r → q r) → onB x y p → onB x y q)
    (hBits : ∀ n x y {p q : BitVec n → Prop}, (∀ r, p r → q r) → onBits n x y p → onBits n x y q)
    (hF : ∀ (f : Fmt) x y {p q : BitVec f.width → Prop}, (∀ r, p r → q r) → onF f x y p → onF f x y q) :
    ∀ {u : Ty} {x y : Val u} {p q : Val u → Prop}, (∀ r, p r → q r) →
      TreeRel2 onB onBits onF u x y p → TreeRel2 onB onBits onF u x y q
  | .bool, _, _, _, _, hpq, h => hB _ _ hpq h
  | .bits n, _, _, _, _, hpq, h => hBits n _ _ hpq h
  | .float f, _, _, _, _, hpq, h => hF f _ _ hpq h
  | .pair a b, (_, _), (_, _), _, _, hpq, h =>
    TreeRel2.mono (u := a) hB hBits hF (fun r1 h2 =>
      TreeRel2.mono (u := b) hB hBits hF (fun r2 hr2 => hpq (r1, r2) hr2) h2) h

def TreeRel3 (onB : Bool → Bool → Bool → (Bool → Prop) → Prop)
    (onBits : ∀ n, BitVec n → BitVec n → BitVec n → (BitVec n → Prop) → Prop)
    (onF : ∀ (f : Fmt), BitVec f.width → BitVec f.width → BitVec f.width → (BitVec f.width → Prop) → Prop) :
    (u : Ty) → Val u → Val u → Val u → (Val u → Prop) → Prop
  | .bool, x, y, z, post => onB x y z post
  | .bits n, x, y, z, post => onBits n x y z post
  | .float f, x, y, z, post => onF f x y z post
  | .pair a b, p, q, r, post =>
    TreeRel3 onB onBits onF a p.1 q.1 r.1 fun r1 =>
    TreeRel3 onB onBits onF b p.2 q.2 r.2 fun r2 => post (r1, r2)

theorem TreeRel3.mono {onB onBits onF}
    (hB : ∀ x y z {p q : Bool → Prop}, (∀ r, p r → q r) → onB x y z p → onB x y z q)
    (hBits : ∀ n x y z {p q : BitVec n → Prop}, (∀ r, p r → q r) → onBits n x y z p → onBits n x y z q)
    (hF : ∀ (f : Fmt) x y z {p q : BitVec f.width → Prop}, (∀ r, p r → q r) → onF f x y z p → onF f x y z q) :
    ∀ {u : Ty} {x y z : Val u} {p q : Val u → Prop}, (∀ r, p r → q r) →
      TreeRel3 onB onBits onF u x y z p → TreeRel3 onB onBits onF u x y z q
  | .bool, _, _, _, _, _, hpq, h => hB _ _ _ hpq h
  | .bits n, _, _, _, _, _, hpq, h => hBits n _ _ _ hpq h
  | .float f, _, _, _, _, _, hpq, h => hF f _ _ _ hpq h
  | .pair a b, (_, _), (_, _), (_, _), _, _, hpq, h =>
    TreeRel3.mono (u := a) hB hBits hF (fun r1 h2 =>
      TreeRel3.mono (u := b) hB hBits hF (fun r2 hr2 => hpq (r1, r2) hr2) h2) h

private theorem legalUnaryTree_goS_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost}
    (onBool : Arg Val .bool → (Arg Val .bool → Expr Val Cont rs) → Expr Val Cont rs)
    (onBits : (n : Nat) → Arg Val (.bits (target.widenWidth n)) →
      (Arg Val (.bits (target.widenWidth n)) → Expr Val Cont rs) → Expr Val Cont rs)
    (onFloat : (f : Fmt) → Arg Val (.float f) →
      (Arg Val (.float f) → Expr Val Cont rs) → Expr Val Cont rs)
    {onB : Bool → (Bool → Prop) → Prop}
    {onBi : ∀ n, BitVec n → (BitVec n → Prop) → Prop}
    {onF : ∀ (f : Fmt), BitVec f.width → (BitVec f.width → Prop) → Prop}
    (hB : ∀ x' x k m, x'.val = x →
      onB x (fun res => ∀ r, r.val = res → wp Γ Q X (k r) m) → wp Γ Q X (onBool x' k) m)
    (hBi : ∀ n, target.supportsTy (.bits n) = true → ∀ x' x k m,
      x'.val = x.setWidth (target.widenWidth n) →
      onBi n x (fun res => ∀ r, r.val = res.setWidth (target.widenWidth n) → wp Γ Q X (k r) m) →
      wp Γ Q X (onBits n x' k) m)
    (hF : ∀ (f : Fmt), target.supportsTy (.float f) = true → ∀ x' x k m, x'.val = x →
      onF f x (fun res => ∀ r, r.val = res → wp Γ Q X (k r) m) → wp Γ Q X (onFloat f x' k) m)
    (hB_m : ∀ x {p q : Bool → Prop}, (∀ r, p r → q r) → onB x p → onB x q)
    (hBi_m : ∀ n x {p q : BitVec n → Prop}, (∀ r, p r → q r) → onBi n x p → onBi n x q)
    (hF_m : ∀ (f : Fmt) x {p q : BitVec f.width → Prop}, (∀ r, p r → q r) → onF f x p → onF f x q) :
    ∀ (u : Ty), target.supportsTy u = true →
      ∀ (fx : Tup (Arg Val) (target.leafTys u)) (x : Val u), valsTup fx = leafVals target u x →
        ∀ (k : Tup (Arg Val) (target.leafTys u) → Expr Val Cont rs) (m : Mem 64),
          TreeRel1 onB onBi onF u x (fun res =>
            ∀ fres, valsTup fres = leafVals target u res → wp Γ Q X (k fres) m) →
          wp Γ Q X (legalUnaryTree.goS target onBool onBits onFloat u fx k) m
  | .bool, _, (x', ()), x, hx, k, m, hk =>
    hB x' x (fun r => k (r, ())) m (congrArg Prod.fst hx)
      (hB_m x (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .bits n, ht, (x', ()), x, hx, k, m, hk =>
    hBi n ht x' x (fun r => k (r, ())) m (congrArg Prod.fst hx)
      (hBi_m n x (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .float f, ht, (x', ()), x, hx, k, m, hk =>
    hF f ht x' x (fun r => k (r, ())) m (congrArg Prod.fst hx)
      (hF_m f x (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .pair u1 u2, ht, fx, x, hx, k, m, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    dsimp only [LegalTarget.leafTys] at fx hx
    dsimp only [legalUnaryTree.goS]
    have h12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hx
    rw [leafVals_pair, tupSplit_tupAppend, tupSplit_valsTup] at h12
    refine legalUnaryTree_goS_wp target onBool onBits onFloat hB hBi hF hB_m hBi_m hF_m u1 ht.1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).1 x.1
      (congrArg Prod.fst h12) _ m ?_
    refine TreeRel1.mono hB_m hBi_m hF_m (fun r1 hr1 fres1 hres1 => ?_) hk
    refine legalUnaryTree_goS_wp target onBool onBits onFloat hB hBi hF hB_m hBi_m hF_m u2 ht.2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).2 x.2
      (congrArg Prod.snd h12) _ m ?_
    refine TreeRel1.mono hB_m hBi_m hF_m (fun r2 hr2 fres2 hres2 => ?_) hr1
    exact hr2 (tupAppend fres1 fres2) (by
      dsimp only [LegalTarget.leafTys]
      rw [leafVals_pair, valsTup_tupAppend, hres1, hres2])

theorem legalUnaryTree_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost}
    (mkCode : (u : Ty) → OpCode [u] [u])
    (vecSupported : (u : Ty) → Bool)
    (onBool : Arg Val .bool → (Arg Val .bool → Expr Val Cont rs) → Expr Val Cont rs)
    (onBits : (n : Nat) → Arg Val (.bits (target.widenWidth n)) →
      (Arg Val (.bits (target.widenWidth n)) → Expr Val Cont rs) → Expr Val Cont rs)
    (onFloat : (f : Fmt) → Arg Val (.float f) →
      (Arg Val (.float f) → Expr Val Cont rs) → Expr Val Cont rs)
    {onB : Bool → (Bool → Prop) → Prop}
    {onBi : ∀ n, BitVec n → (BitVec n → Prop) → Prop}
    {onF : ∀ (f : Fmt), BitVec f.width → (BitVec f.width → Prop) → Prop}
    (hB : ∀ x' x k m, x'.val = x →
      onB x (fun res => ∀ r, r.val = res → wp Γ Q X (k r) m) → wp Γ Q X (onBool x' k) m)
    (hBi : ∀ n, target.supportsTy (.bits n) = true → ∀ x' x k m,
      x'.val = x.setWidth (target.widenWidth n) →
      onBi n x (fun res => ∀ r, r.val = res.setWidth (target.widenWidth n) → wp Γ Q X (k r) m) →
      wp Γ Q X (onBits n x' k) m)
    (hF : ∀ (f : Fmt), target.supportsTy (.float f) = true → ∀ x' x k m, x'.val = x →
      onF f x (fun res => ∀ r, r.val = res → wp Γ Q X (k r) m) → wp Γ Q X (onFloat f x' k) m)
    (hVec : ∀ u, target.keepsPacked u = true → vecSupported u = true → target.supportsTy u = true →
      ∀ x (p : Val u → Prop), TreeRel1 onB onBi onF u x p →
        OpCode.wp (mkCode u) (x, ()) (fun (res, ()) => p res))
    (hB_m : ∀ x {p q : Bool → Prop}, (∀ r, p r → q r) → onB x p → onB x q)
    (hBi_m : ∀ n x {p q : BitVec n → Prop}, (∀ r, p r → q r) → onBi n x p → onBi n x q)
    (hF_m : ∀ (f : Fmt) x {p q : BitVec f.width → Prop}, (∀ r, p r → q r) → onF f x p → onF f x q) :
    ∀ (t : Ty), target.supportsTy t = true → (xs : Tup (Arg Val) (target.legalTys t)) →
      (x : Val t) → valsTup xs = encodeVal target t x →
      (k : Tup (Arg Val) (target.legalTys t) → Expr Val Cont rs) → (m : Mem 64) →
      TreeRel1 onB onBi onF t x (fun res =>
        ∀ fres, valsTup fres = encodeVal target t res → wp Γ Q X (k fres) m) →
      wp Γ Q X (legalUnaryTree target mkCode vecSupported onBool onBits onFloat t xs k) m
  | .bool, _, (x', ()), x, hx, k, m, hk =>
    hB x' x (fun r => k (r, ())) m (congrArg Prod.fst hx)
      (hB_m x (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .bits n, ht, (x', ()), x, hx, k, m, hk =>
    hBi n ht x' x (fun r => k (r, ())) m (congrArg Prod.fst hx)
      (hBi_m n x (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .float f, ht, (x', ()), x, hx, k, m, hk =>
    hF f ht x' x (fun r => k (r, ())) m (congrArg Prod.fst hx)
      (hF_m f x (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .pair t1 t2, ht, xs, p, hxs, k, m, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    dsimp only [legalUnaryTree]
    split
    · next hp =>
      have hxt := congrArg Prod.fst (valsTup_packedToTup_encode target hp hxs)
      simp only [valsTup, Tup.map] at hxt
      by_cases hvs : vecSupported (.pair t1 t2) = true
      · rw [ite_eq_left hvs]
        dsimp only [wp, Op.wp, vals, op1]
        rw [hxt]
        exact OpCode.wp_mono (mkCode (.pair t1 t2)) (p, ())
          (fun (res, ()) hres =>
            hres (tupToPacked hp (.var res, ()))
              (valsTup_tupToPacked_encode target hp (by rw [valsTup_single]; rfl)))
          (hVec (.pair t1 t2) hp hvs (by simp [LegalTarget.supportsTy, ht]) p _ hk)
      · rw [ite_eq_right hvs]
        refine splitLegalToLeaves_wp target (.pair t1 t2) (by simp [LegalTarget.supportsTy, ht]) xs p hxs fun fx hfx => ?_
        refine legalUnaryTree_goS_wp target onBool onBits onFloat hB hBi hF hB_m hBi_m hF_m (.pair t1 t2)
          (by simp [LegalTarget.supportsTy, ht]) fx p hfx _ m ?_
        refine TreeRel1.mono hB_m hBi_m hF_m (fun res hres fres hfres => ?_) hk
        exact packLeavesToLegal_wp target (.pair t1 t2) (by simp [LegalTarget.supportsTy, ht]) fres res hfres hres
    · next hp =>
      have hf := Bool.eq_false_iff.mpr hp
      have hsp := valsTup_splitToTup_encode target hf hxs
      have h12 := congrArg tupSplit hsp
      simp only [tupSplit_valsTup, tupSplit_tupAppend] at h12
      refine legalUnaryTree_wp target mkCode vecSupported onBool onBits onFloat
        hB hBi hF hVec hB_m hBi_m hF_m t1 ht.1 (tupSplit (splitToTup hf xs)).1 p.1
        (congrArg Prod.fst h12) _ m ?_
      refine TreeRel1.mono hB_m hBi_m hF_m (fun r1 hr1 res1 hres1 => ?_) hk
      refine legalUnaryTree_wp target mkCode vecSupported onBool onBits onFloat
        hB hBi hF hVec hB_m hBi_m hF_m t2 ht.2 (tupSplit (splitToTup hf xs)).2 p.2
        (congrArg Prod.snd h12) _ m ?_
      refine TreeRel1.mono hB_m hBi_m hF_m (fun r2 hr2 res2 hres2 => ?_) hr1
      exact hr2 (tupToSplit hf (tupAppend res1 res2))
        (valsTup_tupToSplit_encode target hf (by rw [valsTup_tupAppend, hres1, hres2]))

private theorem treeRel1_bswap {onB : Bool → (Bool → Prop) → Prop}
    {onBi : ∀ n, BitVec n → (BitVec n → Prop) → Prop}
    {onF : ∀ (f : Fmt), BitVec f.width → (BitVec f.width → Prop) → Prop}
    (hBi : ∀ n (a : BitVec n) (p : BitVec n → Prop), n % 8 = 0 → p (bswapBits a) → onBi n a p) :
    ∀ (u : Ty), u.bswapOk = true → ∀ (x : Val u) (p : Val u → Prop),
      p (lift1 bswapBits id u x) → TreeRel1 onB onBi onF u x p
  | .bool, hu, _, _, _ => by simp [Ty.bswapOk] at hu
  | .float _, hu, _, _, _ => by simp [Ty.bswapOk] at hu
  | .bits n, hu, x, p, hp => hBi n x p (beq_iff_eq.mp (by simpa [Ty.bswapOk] using hu)) hp
  | .pair a b, hu, (x1, x2), p, hp => by
    simp only [Ty.bswapOk, Bool.and_eq_true] at hu
    exact treeRel1_bswap hBi a hu.1 x1 _ (treeRel1_bswap hBi b hu.2 x2 _ hp)

theorem legalBswapTree_wp (target : LegalTarget) (hv : target.valid = true)
    {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (t : Ty) (ht : target.supportsTy t = true) (hb : t.bswapOk = true)
    (xs : Tup (Arg Val) (target.legalTys t)) (x : Val t) (hxs : valsTup xs = encodeVal target t x)
    {k : Tup (Arg Val) (target.legalTys t) → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ res, valsTup res = encodeVal target t (lift1 bswapBits id t x) → wp Γ Q X (k res) m) :
    wp Γ Q X (legalBswapTree target t xs k) m := by
  dsimp only [legalBswapTree]
  simp only [show (!t.bswapOk) = false by simp [hb], Bool.false_eq_true, ↓reduceIte]
  let onB := fun (_ : Bool) (_ : Bool → Prop) => False
  let onBi := fun (n : Nat) (a : BitVec n) (post : BitVec n → Prop) =>
    n % 8 = 0 ∧ post (bswapBits a)
  let onF := fun (f : Fmt) (_ : BitVec f.width) (_ : BitVec f.width → Prop) => False
  have hB : ∀ (x' : Arg Val .bool) (x : Bool) (k : Arg Val .bool → Expr Val Cont rs) (m : Mem 64), x'.val = x →
      onB x (fun res => ∀ (r : Arg Val .bool), r.val = res → wp Γ Q X (k r) m) → wp Γ Q X (.hlt) m :=
    fun _ _ _ _ _ h => False.elim h
  have hBi : ∀ (n : Nat), target.supportsTy (.bits n) = true →
      ∀ (x' : Arg Val (.bits (target.widenWidth n))) (x : BitVec n)
        (k : Arg Val (.bits (target.widenWidth n)) → Expr Val Cont rs) (m : Mem 64),
      x'.val = x.setWidth (target.widenWidth n) →
      onBi n x (fun res => ∀ (r : Arg Val (.bits (target.widenWidth n))),
        r.val = res.setWidth (target.widenWidth n) → wp Γ Q X (k r) m) →
      wp Γ Q X (
        if n == 0 then k (.imm 0#(target.widenWidth n))
        else if n == 8 then k x'
        else if n == target.widenWidth n then
          .let_ (op1 (.bswap (.bits (target.widenWidth n))) x') fun bw => k (.var bw.1)
        else if target.widenWidth n % 8 == 0 then
          .let_ (op1 (.bswap (.bits (target.widenWidth n))) x') fun bw =>
          .let_ (op2 (.lshr (.bits (target.widenWidth n))) (.var bw.1)
            (.imm (BitVec.ofNat (target.widenWidth n) (target.widenWidth n - n)))) fun r =>
          k (.var r.1)
        else .hlt) m := by
    intro n hsn x' a k' m' hax ⟨hn8, hk'⟩
    have hnw := le_widenWidth_of_supports hsn
    have hwSpec := valid_bitWidth_spec hv (widenWidth_mem_of_supports hsn)
    by_cases hn0 : n = 0
    · subst hn0
      simp only [beq_self_eq_true, ↓reduceIte]
      have ha0 : a = 0#0 := bitVec0_eq_zero a
      subst ha0
      exact hk' _ (by rw [bitVec0_eq_zero (bswapBits 0#0), BitVec.setWidth_zero]; rfl)
    · have hn0pos : 0 < n := Nat.pos_of_ne_zero hn0
      have hn0f : (n == 0) = false := beq_false_of_ne hn0
      simp only [hn0f, Bool.false_eq_true, ↓reduceIte]
      by_cases hn8eq : n = 8
      · subst hn8eq
        simp only [beq_self_eq_true, ↓reduceIte]
        exact hk' x' (by rw [hax, bswapBits_8])
      · have hn8f : (n == 8) = false := beq_false_of_ne hn8eq
        simp only [hn8f, Bool.false_eq_true, ↓reduceIte]
        by_cases heq : n = target.widenWidth n
        · have hbeq : (n == target.widenWidth n) = true := beq_iff_eq.mpr heq
          simp only [hbeq, ↓reduceIte, wp, Op.wp, OpCode.wp, op1, vals, lift1, Ty.bswapOk]
          have hw8t : (target.widenWidth n % 8 == 0) = true := beq_iff_eq.mpr hwSpec.2.1
          simp only [hw8t, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          revert x' a k' hax hk'
          rw [← heq]
          intro x' a k' hax hk'
          rw [BitVec.setWidth_eq] at hax hk'
          exact hk' _ (by change bswapBits x'.val = _; rw [hax])
        · have hlt : n < target.widenWidth n := Nat.lt_of_le_of_ne hnw heq
          have hneqf : (n == target.widenWidth n) = false := beq_false_of_ne heq
          have hw8t : (target.widenWidth n % 8 == 0) = true := beq_iff_eq.mpr hwSpec.2.1
          simp only [hneqf, Bool.false_eq_true, ↓reduceIte, hw8t, wp, Op.wp, OpCode.wp, op1, op2,
            vals, lift1, lift2, Ty.bswapOk, Bool.not_true]
          have hpow : target.widenWidth n < 2 ^ target.widenWidth n :=
            @Nat.lt_pow_self (target.widenWidth n) 2 (by decide)
          have hsub_lt : target.widenWidth n - n < 2 ^ target.widenWidth n :=
            Nat.lt_of_le_of_lt (Nat.sub_le _ _) hpow
          have hsh : (BitVec.ofNat (target.widenWidth n) (target.widenWidth n - n)).toNat %
              target.widenWidth n = target.widenWidth n - n := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsub_lt, Nat.mod_eq_of_lt (by omega)]
          exact hk' _ (by
            change (bswapBits x'.val) >>> ((BitVec.ofNat (target.widenWidth n)
              (target.widenWidth n - n)).toNat % target.widenWidth n) = _
            rw [hax, hsh, setWidth_bswap_of_lt hn0pos hlt hn8 hwSpec.2.1])
  have hF : ∀ (f : Fmt), target.supportsTy (.float f) = true →
      ∀ (x' : Arg Val (.float f)) (x : BitVec f.width)
        (k : Arg Val (.float f) → Expr Val Cont rs) (m : Mem 64), x'.val = x →
      onF f x (fun res => ∀ (r : Arg Val (.float f)), r.val = res → wp Γ Q X (k r) m) → wp Γ Q X (.hlt) m :=
    fun _ _ _ _ _ _ _ h => False.elim h
  have hVec : ∀ u, target.keepsPacked u = true → false = true → target.supportsTy u = true →
      ∀ x (p : Val u → Prop), TreeRel1 onB onBi onF u x p →
        OpCode.wp (.bswap u) (x, ()) (fun (res, ()) => p res) :=
    fun _ _ hc => by cases hc
  exact legalUnaryTree_wp target .bswap (fun _ => false) (fun _ _ => .hlt)
    (fun n x cont =>
      if n == 0 then cont (.imm 0#(target.widenWidth n))
      else if n == 8 then cont x
      else if n == target.widenWidth n then
        .let_ (op1 (.bswap (.bits (target.widenWidth n))) x) fun bw => cont (.var bw.1)
      else if target.widenWidth n % 8 == 0 then
        .let_ (op1 (.bswap (.bits (target.widenWidth n))) x) fun bw =>
        .let_ (op2 (.lshr (.bits (target.widenWidth n))) (.var bw.1)
          (.imm (BitVec.ofNat (target.widenWidth n) (target.widenWidth n - n)))) fun r =>
        cont (.var r.1)
      else .hlt)
    (fun _ _ _ => .hlt)
    hB hBi hF hVec (fun _ _ _ _ h => False.elim h) (fun n _ _ _ h1 h2 => ⟨h2.1, h1 _ h2.2⟩)
    (fun _ _ _ _ _ h => False.elim h)
    t ht xs x hxs k m
    (treeRel1_bswap (fun _ _ _ hn8 hp => ⟨hn8, hp⟩) t hb x _ hk)

private theorem legalTernaryTree_goS_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost}
    (onBool : Arg Val .bool → Arg Val .bool → Arg Val .bool →
      (Arg Val .bool → Expr Val Cont rs) → Expr Val Cont rs)
    (onBits : (n : Nat) → Arg Val (.bits (target.widenWidth n)) → Arg Val (.bits (target.widenWidth n)) →
      Arg Val (.bits (target.widenWidth n)) →
      (Arg Val (.bits (target.widenWidth n)) → Expr Val Cont rs) → Expr Val Cont rs)
    (onFloat : (f : Fmt) → Arg Val (.float f) → Arg Val (.float f) → Arg Val (.float f) →
      (Arg Val (.float f) → Expr Val Cont rs) → Expr Val Cont rs)
    {onB : Bool → Bool → Bool → (Bool → Prop) → Prop}
    {onBi : ∀ n, BitVec n → BitVec n → BitVec n → (BitVec n → Prop) → Prop}
    {onF : ∀ (f : Fmt), BitVec f.width → BitVec f.width → BitVec f.width → (BitVec f.width → Prop) → Prop}
    (hB : ∀ a' b' c' a b c k m, a'.val = a → b'.val = b → c'.val = c →
      onB a b c (fun res => ∀ r, r.val = res → wp Γ Q X (k r) m) →
      wp Γ Q X (onBool a' b' c' k) m)
    (hBi : ∀ n, target.supportsTy (.bits n) = true → ∀ a' b' c' a b c k m,
      a'.val = a.setWidth (target.widenWidth n) → b'.val = b.setWidth (target.widenWidth n) →
      c'.val = c.setWidth (target.widenWidth n) →
      onBi n a b c (fun res => ∀ r, r.val = res.setWidth (target.widenWidth n) → wp Γ Q X (k r) m) →
      wp Γ Q X (onBits n a' b' c' k) m)
    (hF : ∀ (f : Fmt), target.supportsTy (.float f) = true → ∀ a' b' c' a b c k m,
      a'.val = a → b'.val = b → c'.val = c →
      onF f a b c (fun res => ∀ r, r.val = res → wp Γ Q X (k r) m) →
      wp Γ Q X (onFloat f a' b' c' k) m)
    (hB_m : ∀ x y z {p q : Bool → Prop}, (∀ r, p r → q r) → onB x y z p → onB x y z q)
    (hBi_m : ∀ n x y z {p q : BitVec n → Prop}, (∀ r, p r → q r) → onBi n x y z p → onBi n x y z q)
    (hF_m : ∀ (f : Fmt) x y z {p q : BitVec f.width → Prop}, (∀ r, p r → q r) → onF f x y z p → onF f x y z q) :
    ∀ (u : Ty), target.supportsTy u = true →
      ∀ (fx fy fz : Tup (Arg Val) (target.leafTys u)) (x y z : Val u),
        valsTup fx = leafVals target u x → valsTup fy = leafVals target u y →
        valsTup fz = leafVals target u z →
        ∀ (k : Tup (Arg Val) (target.leafTys u) → Expr Val Cont rs) (m : Mem 64),
          TreeRel3 onB onBi onF u x y z (fun res =>
            ∀ fres, valsTup fres = leafVals target u res → wp Γ Q X (k fres) m) →
          wp Γ Q X (legalTernaryTree.goS target onBool onBits onFloat u fx fy fz k) m
  | .bool, _, (a', ()), (b', ()), (c', ()), a, b, c, ha, hb, hc, k, m, hk =>
    hB a' b' c' a b c (fun r => k (r, ())) m
      (congrArg Prod.fst ha) (congrArg Prod.fst hb) (congrArg Prod.fst hc)
      (hB_m a b c (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .bits n, ht, (a', ()), (b', ()), (c', ()), a, b, c, ha, hb, hc, k, m, hk =>
    hBi n ht a' b' c' a b c (fun r => k (r, ())) m
      (congrArg Prod.fst ha) (congrArg Prod.fst hb) (congrArg Prod.fst hc)
      (hBi_m n a b c (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .float f, ht, (a', ()), (b', ()), (c', ()), a, b, c, ha, hb, hc, k, m, hk =>
    hF f ht a' b' c' a b c (fun r => k (r, ())) m
      (congrArg Prod.fst ha) (congrArg Prod.fst hb) (congrArg Prod.fst hc)
      (hF_m f a b c (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .pair u1 u2, ht, fx, fy, fz, x, y, z, hx, hy, hz, k, m, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    dsimp only [LegalTarget.leafTys] at fx fy fz hx hy hz
    dsimp only [legalTernaryTree.goS]
    have hx12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hx
    have hy12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hy
    have hz12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hz
    rw [leafVals_pair, tupSplit_tupAppend, tupSplit_valsTup] at hx12 hy12 hz12
    refine legalTernaryTree_goS_wp target onBool onBits onFloat hB hBi hF hB_m hBi_m hF_m u1 ht.1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fy).1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fz).1
      x.1 y.1 z.1 (congrArg Prod.fst hx12) (congrArg Prod.fst hy12) (congrArg Prod.fst hz12) _ m ?_
    refine TreeRel3.mono hB_m hBi_m hF_m (fun r1 hr1 fres1 hres1 => ?_) hk
    refine legalTernaryTree_goS_wp target onBool onBits onFloat hB hBi hF hB_m hBi_m hF_m u2 ht.2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fy).2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fz).2
      x.2 y.2 z.2 (congrArg Prod.snd hx12) (congrArg Prod.snd hy12) (congrArg Prod.snd hz12) _ m ?_
    refine TreeRel3.mono hB_m hBi_m hF_m (fun r2 hr2 fres2 hres2 => ?_) hr1
    exact hr2 (tupAppend fres1 fres2) (by
      dsimp only [LegalTarget.leafTys]
      rw [leafVals_pair, valsTup_tupAppend, hres1, hres2])

theorem legalTernaryTree_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost}
    (mkCode : (u : Ty) → OpCode [u, u, u] [u])
    (vecSupported : (u : Ty) → Bool)
    (onBool : Arg Val .bool → Arg Val .bool → Arg Val .bool →
      (Arg Val .bool → Expr Val Cont rs) → Expr Val Cont rs)
    (onBits : (n : Nat) → Arg Val (.bits (target.widenWidth n)) → Arg Val (.bits (target.widenWidth n)) →
      Arg Val (.bits (target.widenWidth n)) →
      (Arg Val (.bits (target.widenWidth n)) → Expr Val Cont rs) → Expr Val Cont rs)
    (onFloat : (f : Fmt) → Arg Val (.float f) → Arg Val (.float f) → Arg Val (.float f) →
      (Arg Val (.float f) → Expr Val Cont rs) → Expr Val Cont rs)
    {onB : Bool → Bool → Bool → (Bool → Prop) → Prop}
    {onBi : ∀ n, BitVec n → BitVec n → BitVec n → (BitVec n → Prop) → Prop}
    {onF : ∀ (f : Fmt), BitVec f.width → BitVec f.width → BitVec f.width → (BitVec f.width → Prop) → Prop}
    (hB : ∀ a' b' c' a b c k m, a'.val = a → b'.val = b → c'.val = c →
      onB a b c (fun res => ∀ r, r.val = res → wp Γ Q X (k r) m) →
      wp Γ Q X (onBool a' b' c' k) m)
    (hBi : ∀ n, target.supportsTy (.bits n) = true → ∀ a' b' c' a b c k m,
      a'.val = a.setWidth (target.widenWidth n) → b'.val = b.setWidth (target.widenWidth n) →
      c'.val = c.setWidth (target.widenWidth n) →
      onBi n a b c (fun res => ∀ r, r.val = res.setWidth (target.widenWidth n) → wp Γ Q X (k r) m) →
      wp Γ Q X (onBits n a' b' c' k) m)
    (hF : ∀ (f : Fmt), target.supportsTy (.float f) = true → ∀ a' b' c' a b c k m,
      a'.val = a → b'.val = b → c'.val = c →
      onF f a b c (fun res => ∀ r, r.val = res → wp Γ Q X (k r) m) →
      wp Γ Q X (onFloat f a' b' c' k) m)
    (hVec : ∀ u, target.keepsPacked u = true → vecSupported u = true → target.supportsTy u = true →
      ∀ x y z (p : Val u → Prop), TreeRel3 onB onBi onF u x y z p →
        OpCode.wp (mkCode u) (x, y, z, ()) (fun (res, ()) => p res))
    (hB_m : ∀ x y z {p q : Bool → Prop}, (∀ r, p r → q r) → onB x y z p → onB x y z q)
    (hBi_m : ∀ n x y z {p q : BitVec n → Prop}, (∀ r, p r → q r) → onBi n x y z p → onBi n x y z q)
    (hF_m : ∀ (f : Fmt) x y z {p q : BitVec f.width → Prop}, (∀ r, p r → q r) → onF f x y z p → onF f x y z q) :
    ∀ (t : Ty), target.supportsTy t = true →
      (xs ys zs : Tup (Arg Val) (target.legalTys t)) → (x y z : Val t) →
      valsTup xs = encodeVal target t x → valsTup ys = encodeVal target t y →
      valsTup zs = encodeVal target t z →
      (k : Tup (Arg Val) (target.legalTys t) → Expr Val Cont rs) → (m : Mem 64) →
      TreeRel3 onB onBi onF t x y z (fun res =>
        ∀ fres, valsTup fres = encodeVal target t res → wp Γ Q X (k fres) m) →
      wp Γ Q X (legalTernaryTree target mkCode vecSupported onBool onBits onFloat t xs ys zs k) m
  | .bool, _, (a', ()), (b', ()), (c', ()), a, b, c, ha, hb, hc, k, m, hk =>
    hB a' b' c' a b c (fun r => k (r, ())) m
      (congrArg Prod.fst ha) (congrArg Prod.fst hb) (congrArg Prod.fst hc)
      (hB_m a b c (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .bits n, ht, (a', ()), (b', ()), (c', ()), a, b, c, ha, hb, hc, k, m, hk =>
    hBi n ht a' b' c' a b c (fun r => k (r, ())) m
      (congrArg Prod.fst ha) (congrArg Prod.fst hb) (congrArg Prod.fst hc)
      (hBi_m n a b c (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .float f, ht, (a', ()), (b', ()), (c', ()), a, b, c, ha, hb, hc, k, m, hk =>
    hF f ht a' b' c' a b c (fun r => k (r, ())) m
      (congrArg Prod.fst ha) (congrArg Prod.fst hb) (congrArg Prod.fst hc)
      (hF_m f a b c (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .pair t1 t2, ht, xs, ys, zs, px, py, pz, hxs, hys, hzs, k, m, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    dsimp only [legalTernaryTree]
    split
    · next hp =>
      have hxt := congrArg Prod.fst (valsTup_packedToTup_encode target hp hxs)
      have hyt := congrArg Prod.fst (valsTup_packedToTup_encode target hp hys)
      have hzt := congrArg Prod.fst (valsTup_packedToTup_encode target hp hzs)
      simp only [valsTup, Tup.map] at hxt hyt hzt
      by_cases hvs : vecSupported (.pair t1 t2) = true
      · rw [ite_eq_left hvs]
        dsimp only [wp, Op.wp, vals, op3]
        rw [hxt, hyt, hzt]
        exact OpCode.wp_mono (mkCode (.pair t1 t2)) (px, py, pz, ())
          (fun (res, ()) hres =>
            hres (tupToPacked hp (.var res, ()))
              (valsTup_tupToPacked_encode target hp (by rw [valsTup_single]; rfl)))
          (hVec (.pair t1 t2) hp hvs (by simp [LegalTarget.supportsTy, ht]) px py pz _ hk)
      · rw [ite_eq_right hvs]
        refine splitLegalToLeaves_wp target (.pair t1 t2) (by simp [LegalTarget.supportsTy, ht]) xs px hxs fun fx hfx =>
          splitLegalToLeaves_wp target (.pair t1 t2) (by simp [LegalTarget.supportsTy, ht]) ys py hys fun fy hfy =>
          splitLegalToLeaves_wp target (.pair t1 t2) (by simp [LegalTarget.supportsTy, ht]) zs pz hzs fun fz hfz => ?_
        refine legalTernaryTree_goS_wp target onBool onBits onFloat hB hBi hF hB_m hBi_m hF_m
          (.pair t1 t2) (by simp [LegalTarget.supportsTy, ht]) fx fy fz px py pz hfx hfy hfz _ m ?_
        refine TreeRel3.mono hB_m hBi_m hF_m (fun res hres fres hfres => ?_) hk
        exact packLeavesToLegal_wp target (.pair t1 t2) (by simp [LegalTarget.supportsTy, ht]) fres res hfres hres
    · next hp =>
      have hf := Bool.eq_false_iff.mpr hp
      have hx12 := congrArg tupSplit (valsTup_splitToTup_encode target hf hxs)
      have hy12 := congrArg tupSplit (valsTup_splitToTup_encode target hf hys)
      have hz12 := congrArg tupSplit (valsTup_splitToTup_encode target hf hzs)
      simp only [tupSplit_valsTup, tupSplit_tupAppend] at hx12 hy12 hz12
      refine legalTernaryTree_wp target mkCode vecSupported onBool onBits onFloat
        hB hBi hF hVec hB_m hBi_m hF_m t1 ht.1
        (tupSplit (splitToTup hf xs)).1 (tupSplit (splitToTup hf ys)).1 (tupSplit (splitToTup hf zs)).1
        px.1 py.1 pz.1 (congrArg Prod.fst hx12) (congrArg Prod.fst hy12) (congrArg Prod.fst hz12) _ m ?_
      refine TreeRel3.mono hB_m hBi_m hF_m (fun r1 hr1 res1 hres1 => ?_) hk
      refine legalTernaryTree_wp target mkCode vecSupported onBool onBits onFloat
        hB hBi hF hVec hB_m hBi_m hF_m t2 ht.2
        (tupSplit (splitToTup hf xs)).2 (tupSplit (splitToTup hf ys)).2 (tupSplit (splitToTup hf zs)).2
        px.2 py.2 pz.2 (congrArg Prod.snd hx12) (congrArg Prod.snd hy12) (congrArg Prod.snd hz12) _ m ?_
      refine TreeRel3.mono hB_m hBi_m hF_m (fun r2 hr2 res2 hres2 => ?_) hr1
      exact hr2 (tupToSplit hf (tupAppend res1 res2))
        (valsTup_tupToSplit_encode target hf (by rw [valsTup_tupAppend, hres1, hres2]))

private theorem legalBinTree_goS_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost}
    (onBool : Arg Val .bool → Arg Val .bool → (Arg Val .bool → Expr Val Cont rs) → Expr Val Cont rs)
    (onBits : (n : Nat) → Arg Val (.bits (target.widenWidth n)) → Arg Val (.bits (target.widenWidth n)) →
      (Arg Val (.bits (target.widenWidth n)) → Expr Val Cont rs) → Expr Val Cont rs)
    (onFloat : (f : Fmt) → Arg Val (.float f) → Arg Val (.float f) →
      (Arg Val (.float f) → Expr Val Cont rs) → Expr Val Cont rs)
    {onB : Bool → Bool → (Bool → Prop) → Prop}
    {onBi : ∀ n, BitVec n → BitVec n → (BitVec n → Prop) → Prop}
    {onF : ∀ (f : Fmt), BitVec f.width → BitVec f.width → (BitVec f.width → Prop) → Prop}
    (hB : ∀ a' b' a b k m, a'.val = a → b'.val = b →
      onB a b (fun res => ∀ r, r.val = res → wp Γ Q X (k r) m) → wp Γ Q X (onBool a' b' k) m)
    (hBi : ∀ n, target.supportsTy (.bits n) = true → ∀ a' b' a b k m,
      a'.val = a.setWidth (target.widenWidth n) → b'.val = b.setWidth (target.widenWidth n) →
      onBi n a b (fun res => ∀ r, r.val = res.setWidth (target.widenWidth n) → wp Γ Q X (k r) m) →
      wp Γ Q X (onBits n a' b' k) m)
    (hF : ∀ (f : Fmt), target.supportsTy (.float f) = true → ∀ a' b' a b k m, a'.val = a → b'.val = b →
      onF f a b (fun res => ∀ r, r.val = res → wp Γ Q X (k r) m) → wp Γ Q X (onFloat f a' b' k) m)
    (hB_m : ∀ x y {p q : Bool → Prop}, (∀ r, p r → q r) → onB x y p → onB x y q)
    (hBi_m : ∀ n x y {p q : BitVec n → Prop}, (∀ r, p r → q r) → onBi n x y p → onBi n x y q)
    (hF_m : ∀ (f : Fmt) x y {p q : BitVec f.width → Prop}, (∀ r, p r → q r) → onF f x y p → onF f x y q) :
    ∀ (u : Ty), target.supportsTy u = true →
      ∀ (fx fy : Tup (Arg Val) (target.leafTys u)) (x y : Val u),
        valsTup fx = leafVals target u x → valsTup fy = leafVals target u y →
        ∀ (k : Tup (Arg Val) (target.leafTys u) → Expr Val Cont rs) (m : Mem 64),
          TreeRel2 onB onBi onF u x y (fun res =>
            ∀ fres, valsTup fres = leafVals target u res → wp Γ Q X (k fres) m) →
          wp Γ Q X (legalBinTree.goS target onBool onBits onFloat u fx fy k) m
  | .bool, _, (a', ()), (b', ()), a, b, ha, hb, k, m, hk =>
    hB a' b' a b (fun r => k (r, ())) m (congrArg Prod.fst ha) (congrArg Prod.fst hb)
      (hB_m a b (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .bits n, ht, (a', ()), (b', ()), a, b, ha, hb, k, m, hk =>
    hBi n ht a' b' a b (fun r => k (r, ())) m (congrArg Prod.fst ha) (congrArg Prod.fst hb)
      (hBi_m n a b (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .float f, ht, (a', ()), (b', ()), a, b, ha, hb, k, m, hk =>
    hF f ht a' b' a b (fun r => k (r, ())) m (congrArg Prod.fst ha) (congrArg Prod.fst hb)
      (hF_m f a b (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .pair u1 u2, ht, fx, fy, x, y, hx, hy, k, m, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    dsimp only [LegalTarget.leafTys] at fx fy hx hy
    dsimp only [legalBinTree.goS]
    have hx12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hx
    have hy12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hy
    rw [leafVals_pair, tupSplit_tupAppend, tupSplit_valsTup] at hx12 hy12
    refine legalBinTree_goS_wp target onBool onBits onFloat hB hBi hF hB_m hBi_m hF_m u1 ht.1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fy).1
      x.1 y.1 (congrArg Prod.fst hx12) (congrArg Prod.fst hy12) _ m ?_
    refine TreeRel2.mono hB_m hBi_m hF_m (fun r1 hr1 fres1 hres1 => ?_) hk
    refine legalBinTree_goS_wp target onBool onBits onFloat hB hBi hF hB_m hBi_m hF_m u2 ht.2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fy).2
      x.2 y.2 (congrArg Prod.snd hx12) (congrArg Prod.snd hy12) _ m ?_
    refine TreeRel2.mono hB_m hBi_m hF_m (fun r2 hr2 fres2 hres2 => ?_) hr1
    exact hr2 (tupAppend fres1 fres2) (by
      dsimp only [LegalTarget.leafTys]
      rw [leafVals_pair, valsTup_tupAppend, hres1, hres2])

theorem legalBinTree_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost}
    (mkCode : (u : Ty) → OpCode [u, u] [u])
    (vecSupported : (u : Ty) → Bool → Bool)
    (onBool : Arg Val .bool → Arg Val .bool → (Arg Val .bool → Expr Val Cont rs) → Expr Val Cont rs)
    (onBits : (n : Nat) → Arg Val (.bits (target.widenWidth n)) → Arg Val (.bits (target.widenWidth n)) →
      (Arg Val (.bits (target.widenWidth n)) → Expr Val Cont rs) → Expr Val Cont rs)
    (onFloat : (f : Fmt) → Arg Val (.float f) → Arg Val (.float f) →
      (Arg Val (.float f) → Expr Val Cont rs) → Expr Val Cont rs)
    (uniformImmRhs : (u : Ty) → Arg (LVar target Val) u → Bool)
    {onB : Bool → Bool → (Bool → Prop) → Prop}
    {onBi : ∀ n, BitVec n → BitVec n → (BitVec n → Prop) → Prop}
    {onF : ∀ (f : Fmt), BitVec f.width → BitVec f.width → (BitVec f.width → Prop) → Prop}
    (hB : ∀ a' b' a b k m, a'.val = a → b'.val = b →
      onB a b (fun res => ∀ r, r.val = res → wp Γ Q X (k r) m) → wp Γ Q X (onBool a' b' k) m)
    (hBi : ∀ n, target.supportsTy (.bits n) = true → ∀ a' b' a b k m,
      a'.val = a.setWidth (target.widenWidth n) → b'.val = b.setWidth (target.widenWidth n) →
      onBi n a b (fun res => ∀ r, r.val = res.setWidth (target.widenWidth n) → wp Γ Q X (k r) m) →
      wp Γ Q X (onBits n a' b' k) m)
    (hF : ∀ (f : Fmt), target.supportsTy (.float f) = true → ∀ a' b' a b k m, a'.val = a → b'.val = b →
      onF f a b (fun res => ∀ r, r.val = res → wp Γ Q X (k r) m) → wp Γ Q X (onFloat f a' b' k) m)
    (hVec : ∀ u unif, target.keepsPacked u = true → vecSupported u unif = true →
      target.supportsTy u = true → ∀ x y (p : Val u → Prop),
        TreeRel2 onB onBi onF u x y p → OpCode.wp (mkCode u) (x, y, ()) (fun (res, ()) => p res))
    (hRotl : ∀ u c w s, opShiftKind (mkCode u) = some true → uniformShiftLeaf? u c = some (w, s) →
      target.supportsTy u = true → ∀ x (p : Val u → Prop), TreeRel2 onB onBi onF u x c p →
        if s == 0 then p x
        else OpCode.wp (.rotr u) (x, splatBits w (BitVec.ofNat w (w - s)) u, ()) (fun (r, ()) => p r))
    (hShl : ∀ u c w s, opShiftKind (mkCode u) = some false → uniformShiftLeaf? u c = some (w, s) →
      target.supportsTy u = true → ∀ x (p : Val u → Prop), TreeRel2 onB onBi onF u x c p →
        if s == 0 then p x
        else OpCode.wp (.rotr u) (x, splatBits w (BitVec.ofNat w (w - s)) u, ()) (fun (rt, ()) =>
          OpCode.wp (.and u) (rt, splatBits w (BitVec.allOnes w <<< s) u, ()) (fun (r, ()) => p r)))
    (hB_m : ∀ x y {p q : Bool → Prop}, (∀ r, p r → q r) → onB x y p → onB x y q)
    (hBi_m : ∀ n x y {p q : BitVec n → Prop}, (∀ r, p r → q r) → onBi n x y p → onBi n x y q)
    (hF_m : ∀ f x y {p q : BitVec f.width → Prop}, (∀ r, p r → q r) → onF f x y p → onF f x y q) :
    ∀ (t : Ty), target.supportsTy t = true →
      (xs ys : Tup (Arg Val) (target.legalTys t)) → (rawRhs : Option (Arg (LVar target Val) t)) →
      (x y : Val t) → valsTup xs = encodeVal target t x → valsTup ys = encodeVal target t y →
      (∀ c, rawRhs = some (.imm c) → y = c) →
      (k : Tup (Arg Val) (target.legalTys t) → Expr Val Cont rs) → (m : Mem 64) →
      TreeRel2 onB onBi onF t x y (fun res =>
        ∀ fres, valsTup fres = encodeVal target t res → wp Γ Q X (k fres) m) →
      wp Γ Q X (legalBinTree target mkCode vecSupported onBool onBits onFloat uniformImmRhs t xs ys rawRhs k) m
  | .bool, _, (a', ()), (b', ()), _, a, b, ha, hb, _, k, m, hk =>
    hB a' b' a b (fun r => k (r, ())) m (congrArg Prod.fst ha) (congrArg Prod.fst hb)
      (hB_m a b (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .bits n, ht, (a', ()), (b', ()), _, a, b, ha, hb, _, k, m, hk =>
    hBi n ht a' b' a b (fun r => k (r, ())) m (congrArg Prod.fst ha) (congrArg Prod.fst hb)
      (hBi_m n a b (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .float f, ht, (a', ()), (b', ()), _, a, b, ha, hb, _, k, m, hk =>
    hF f ht a' b' a b (fun r => k (r, ())) m (congrArg Prod.fst ha) (congrArg Prod.fst hb)
      (hF_m f a b (fun res hr r hrv => hr (r, ()) (congrArg (·, ()) hrv)) hk)
  | .pair t1 t2, ht, xs, ys, rawRhs, px, py, hxs, hys, hraw, k, m, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    have ht_pair : target.supportsTy (.pair t1 t2) = true := by simp [LegalTarget.supportsTy, ht]
    dsimp only [legalBinTree]
    split
    · next hp =>
      have hxt := congrArg Prod.fst (valsTup_packedToTup_encode target hp hxs)
      have hyt := congrArg Prod.fst (valsTup_packedToTup_encode target hp hys)
      simp only [valsTup, Tup.map] at hxt hyt
      have hscalar : wp Γ Q X (
          splitLegalToLeaves target (.pair t1 t2) xs fun fx =>
          splitLegalToLeaves target (.pair t1 t2) ys fun fy =>
          legalBinTree.goS target onBool onBits onFloat (.pair t1 t2) fx fy fun fres =>
            packLeavesToLegal target (.pair t1 t2) fres k) m := by
        refine splitLegalToLeaves_wp target (.pair t1 t2) ht_pair xs px hxs fun fx hfx =>
          splitLegalToLeaves_wp target (.pair t1 t2) ht_pair ys py hys fun fy hfy => ?_
        refine legalBinTree_goS_wp target onBool onBits onFloat hB hBi hF hB_m hBi_m hF_m
          (.pair t1 t2) ht_pair fx fy px py hfx hfy _ m ?_
        refine TreeRel2.mono hB_m hBi_m hF_m (fun res hres fres hfres => ?_) hk
        exact packLeavesToLegal_wp target (.pair t1 t2) ht_pair fres res hfres hres
      cases hrr : rawRhs with
      | none =>
        by_cases hvs : vecSupported (.pair t1 t2)
            (checkUniformImmShift (.pair t1 t2) (mkCode (.pair t1 t2)) (packedToTup hp ys).1) = true
        · simp only [hvs, ↓reduceIte, wp, Op.wp, vals, op2]
          rw [hxt, hyt]
          exact OpCode.wp_mono (mkCode (.pair t1 t2)) (px, py, ())
            (fun (res, ()) hres =>
              hres (tupToPacked hp (.var res, ()))
                (valsTup_tupToPacked_encode target hp (by rw [valsTup_single]; rfl)))
            (hVec (.pair t1 t2) _ hp hvs ht_pair px py _ hk)
        · have hvsf : vecSupported (.pair t1 t2)
              (checkUniformImmShift (.pair t1 t2) (mkCode (.pair t1 t2)) (packedToTup hp ys).1) = false :=
            Bool.eq_false_iff.mpr hvs
          simp only [hvsf, Bool.false_eq_true, ↓reduceIte]
          cases opShiftKind (mkCode (.pair t1 t2)) with
          | none => exact hscalar
          | some b => cases b <;> exact hscalar
      | some r =>
        by_cases hvs : vecSupported (.pair t1 t2)
            (checkUniformImmShift (.pair t1 t2) (mkCode (.pair t1 t2)) (packedToTup hp ys).1) = true
        · simp only [hvs, ↓reduceIte, wp, Op.wp, vals, op2]
          rw [hxt, hyt]
          exact OpCode.wp_mono (mkCode (.pair t1 t2)) (px, py, ())
            (fun (res, ()) hres =>
              hres (tupToPacked hp (.var res, ()))
                (valsTup_tupToPacked_encode target hp (by rw [valsTup_single]; rfl)))
            (hVec (.pair t1 t2) _ hp hvs ht_pair px py _ hk)
        · have hvsf : vecSupported (.pair t1 t2)
              (checkUniformImmShift (.pair t1 t2) (mkCode (.pair t1 t2)) (packedToTup hp ys).1) = false :=
            Bool.eq_false_iff.mpr hvs
          simp only [hvsf, Bool.false_eq_true, ↓reduceIte]
          cases hsk : opShiftKind (mkCode (.pair t1 t2)) with
          | none => exact hscalar
          | some b =>
            cases r with
            | var _ => cases b <;> exact hscalar
            | imm c =>
              have hpy : py = c := hraw c hrr
              subst hpy
              cases b with
              | true =>
                dsimp only
                cases hus : uniformShiftLeaf? (.pair t1 t2) py with
                | none => exact hscalar
                | some p =>
                  rcases p with ⟨w, s⟩
                  dsimp only
                  have hrl := hRotl (.pair t1 t2) py w s hsk hus ht_pair px _ hk
                  by_cases hs0 : (s == 0) = true
                  · rw [ite_eq_left hs0]
                    simp only [hs0, ↓reduceIte] at hrl
                    exact hrl (tupToPacked hp (packedToTup hp xs))
                      (valsTup_tupToPacked_encode target hp (valsTup_packedToTup_encode target hp hxs))
                  · rw [ite_eq_right hs0]
                    have hs0' : (s == 0) = false := Bool.eq_false_iff.mpr hs0
                    simp only [hs0', Bool.false_eq_true, ↓reduceIte] at hrl
                    by_cases hsup : target.vecIntOpSupported (.rotr (.pair t1 t2)) (.pair t1 t2) true = true
                    · rw [ite_eq_left hsup]
                      dsimp only [wp, Op.wp, vals, op2, Arg.val_imm]
                      rw [hxt]
                      exact OpCode.wp_mono (.rotr (.pair t1 t2)) _ (fun (r, ()) hr =>
                        hr (tupToPacked hp (.var r, ()))
                          (valsTup_tupToPacked_encode target hp (by rw [valsTup_single]; rfl))) hrl
                    · rw [ite_eq_right hsup]
                      exact hscalar
              | false =>
                dsimp only
                cases hus : uniformShiftLeaf? (.pair t1 t2) py with
                | none => exact hscalar
                | some p =>
                  rcases p with ⟨w, s⟩
                  dsimp only
                  have hsh := hShl (.pair t1 t2) py w s hsk hus ht_pair px _ hk
                  by_cases hs0 : (s == 0) = true
                  · rw [ite_eq_left hs0]
                    simp only [hs0, ↓reduceIte] at hsh
                    exact hsh (tupToPacked hp (packedToTup hp xs))
                      (valsTup_tupToPacked_encode target hp (valsTup_packedToTup_encode target hp hxs))
                  · rw [ite_eq_right hs0]
                    have hs0' : (s == 0) = false := Bool.eq_false_iff.mpr hs0
                    simp only [hs0', Bool.false_eq_true, ↓reduceIte] at hsh
                    by_cases hsup : (target.vecIntOpSupported (.rotr (.pair t1 t2)) (.pair t1 t2) true &&
                        target.vecIntOpSupported (.and (.pair t1 t2)) (.pair t1 t2) false) = true
                    · rw [ite_eq_left hsup]
                      dsimp only [wp, Op.wp, vals, op2, Arg.val_imm]
                      rw [hxt]
                      exact OpCode.wp_mono (.rotr (.pair t1 t2)) _ (fun (rt, ()) hrt =>
                        OpCode.wp_mono (.and (.pair t1 t2)) _ (fun (r, ()) hr =>
                          hr (tupToPacked hp (.var r, ()))
                            (valsTup_tupToPacked_encode target hp (by rw [valsTup_single]; rfl))) hrt) hsh
                    · rw [ite_eq_right hsup]
                      exact hscalar
    · next hp =>
      have hf := Bool.eq_false_iff.mpr hp
      have hx12 := congrArg tupSplit (valsTup_splitToTup_encode target hf hxs)
      have hy12 := congrArg tupSplit (valsTup_splitToTup_encode target hf hys)
      simp only [tupSplit_valsTup, tupSplit_tupAppend] at hx12 hy12
      refine legalBinTree_wp target mkCode vecSupported onBool onBits onFloat uniformImmRhs
        hB hBi hF hVec hRotl hShl hB_m hBi_m hF_m t1 ht.1
        (tupSplit (splitToTup hf xs)).1 (tupSplit (splitToTup hf ys)).1 none px.1 py.1
        (congrArg Prod.fst hx12) (congrArg Prod.fst hy12) (fun _ h => by cases h) _ m ?_
      refine TreeRel2.mono hB_m hBi_m hF_m (fun r1 hr1 res1 hres1 => ?_) hk
      refine legalBinTree_wp target mkCode vecSupported onBool onBits onFloat uniformImmRhs
        hB hBi hF hVec hRotl hShl hB_m hBi_m hF_m t2 ht.2
        (tupSplit (splitToTup hf xs)).2 (tupSplit (splitToTup hf ys)).2 none px.2 py.2
        (congrArg Prod.snd hx12) (congrArg Prod.snd hy12) (fun _ h => by cases h) _ m ?_
      refine TreeRel2.mono hB_m hBi_m hF_m (fun r2 hr2 res2 hres2 => ?_) hr1
      exact hr2 (tupToSplit hf (tupAppend res1 res2))
        (valsTup_tupToSplit_encode target hf (by rw [valsTup_tupAppend, hres1, hres2]))

private theorem legalCmpBits_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost} (o : CmpOp) {n : Nat} (hn : target.supportsTy (.bits n) = true)
    (a' b' : Arg Val (.bits (target.widenWidth n))) (a b : BitVec n)
    (ha : a'.val = a.setWidth (target.widenWidth n))
    (hb : b'.val = b.setWidth (target.widenWidth n))
    {k : Arg Val .bool → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r, r.val = o.evalBits a b → wp Γ Q X (k r) m) :
    wp Γ Q X (
      if n == 0 then k (.imm (o.evalBits 0#0 0#0))
      else if n == target.widenWidth n then
        .let_ (op2 (.cmp o (.bits (target.widenWidth n))) a' b') fun r => k (.var r.1)
      else
        if (match o with | .slt | .sle | .sgt | .sge => true | _ => false) then
          emitSextToW n (target.widenWidth n) a' fun sa =>
            emitSextToW n (target.widenWidth n) b' fun sb =>
              .let_ (op2 (.cmp o (.bits (target.widenWidth n))) sa sb) fun r => k (.var r.1)
        else .let_ (op2 (.cmp o (.bits (target.widenWidth n))) a' b') fun r => k (.var r.1)) m := by
  have hnw := le_widenWidth_of_supports hn
  by_cases hn0 : n = 0
  · subst hn0
    simp only [beq_self_eq_true, ↓reduceIte]
    rw [bitVec0_eq_zero a, bitVec0_eq_zero b] at hk
    exact hk _ rfl
  · have hn0pos : 0 < n := Nat.pos_of_ne_zero hn0
    have hn0f : (n == 0) = false := beq_false_of_ne hn0
    simp only [hn0f, Bool.false_eq_true, ↓reduceIte]
    by_cases heq : n = target.widenWidth n
    · have hbeq : (n == target.widenWidth n) = true := beq_iff_eq.mpr heq
      simp only [hbeq, ↓reduceIte, wp, Op.wp, OpCode.wp, op2, vals, Ty.hasFloat,
        Bool.false_eq_true, liftCmp]
      revert a' b' ha hb hk
      rw [← heq]
      intro a' b' ha hb hk
      rw [BitVec.setWidth_eq] at ha hb
      exact hk _ (by change o.evalBits a'.val b'.val = _; rw [ha, hb])
    · have hneqf : (n == target.widenWidth n) = false := beq_false_of_ne heq
      simp only [hneqf, Bool.false_eq_true, ↓reduceIte]
      cases o <;> simp only [↓reduceIte, Bool.false_eq_true]
      · exact hk _ (by change CmpOp.evalBits .eq a'.val b'.val = _; rw [ha, hb]; exact evalBits_setWidth_unsigned hnw .eq trivial a b)
      · exact hk _ (by change CmpOp.evalBits .ne a'.val b'.val = _; rw [ha, hb]; exact evalBits_setWidth_unsigned hnw .ne trivial a b)
      · exact hk _ (by change CmpOp.evalBits .ult a'.val b'.val = _; rw [ha, hb]; exact evalBits_setWidth_unsigned hnw .ult trivial a b)
      · exact hk _ (by change CmpOp.evalBits .ule a'.val b'.val = _; rw [ha, hb]; exact evalBits_setWidth_unsigned hnw .ule trivial a b)
      · exact hk _ (by change CmpOp.evalBits .ugt a'.val b'.val = _; rw [ha, hb]; exact evalBits_setWidth_unsigned hnw .ugt trivial a b)
      · exact hk _ (by change CmpOp.evalBits .uge a'.val b'.val = _; rw [ha, hb]; exact evalBits_setWidth_unsigned hnw .uge trivial a b)
      · refine emitSextToW_wp hn0pos hnw ha fun sa hsa => emitSextToW_wp hn0pos hnw hb fun sb hsb => ?_
        simp only [wp, Op.wp, OpCode.wp, op2, vals, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, liftCmp]
        exact hk _ (by change CmpOp.evalBits .slt sa.val sb.val = _; rw [hsa, hsb]; exact evalBits_signExtend_signed hn0pos hnw .slt trivial a b)
      · refine emitSextToW_wp hn0pos hnw ha fun sa hsa => emitSextToW_wp hn0pos hnw hb fun sb hsb => ?_
        simp only [wp, Op.wp, OpCode.wp, op2, vals, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, liftCmp]
        exact hk _ (by change CmpOp.evalBits .sle sa.val sb.val = _; rw [hsa, hsb]; exact evalBits_signExtend_signed hn0pos hnw .sle trivial a b)
      · refine emitSextToW_wp hn0pos hnw ha fun sa hsa => emitSextToW_wp hn0pos hnw hb fun sb hsb => ?_
        simp only [wp, Op.wp, OpCode.wp, op2, vals, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, liftCmp]
        exact hk _ (by change CmpOp.evalBits .sgt sa.val sb.val = _; rw [hsa, hsb]; exact evalBits_signExtend_signed hn0pos hnw .sgt trivial a b)
      · refine emitSextToW_wp hn0pos hnw ha fun sa hsa => emitSextToW_wp hn0pos hnw hb fun sb hsb => ?_
        simp only [wp, Op.wp, OpCode.wp, op2, vals, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, liftCmp]
        exact hk _ (by change CmpOp.evalBits .sge sa.val sb.val = _; rw [hsa, hsb]; exact evalBits_signExtend_signed hn0pos hnw .sge trivial a b)

private theorem legalCmpTree_goMask_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost} (o : CmpOp) :
    ∀ (u : Ty), target.supportsTy u = true → u.hasFloat = false →
      (fx fy : Tup (Arg Val) (target.leafTys u)) → (x y : Val u) →
      valsTup fx = leafVals target u x → valsTup fy = leafVals target u y →
      (k : Tup (Arg Val) (target.leafTys u.mask) → Expr Val Cont rs) → (m : Mem 64) →
      (∀ res, valsTup res = leafVals target u.mask (liftCmp o.evalBits o.evalBool u x y) →
        wp Γ Q X (k res) m) →
      wp Γ Q X (legalCmpTree.goMask target o u fx fy k) m
  | .bool, _, _, (a', ()), (b', ()), a, b, ha, hb, k, m, hk => by
    dsimp only [LegalTarget.leafTys, Ty.mask, leafVals] at ha hb
    rw [valsTup_single] at ha hb
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at ha hb
    dsimp only [legalCmpTree.goMask]
    by_cases hbc : target.boolCmp = true
    · rw [ite_eq_left hbc]
      simp only [wp, Op.wp, OpCode.wp, op2, vals, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, liftCmp]
      exact hk _ (by
        dsimp only [Ty.mask, LegalTarget.leafTys, leafVals]
        rw [valsTup_single]
        exact congrArg (·, ()) (by change o.evalBool a'.val b'.val = _; rw [ha, hb]; rfl))
    · rw [ite_eq_right hbc]
      refine emitBoolCmp_wp o a' b' fun r hr => hk (r, ()) ?_
      dsimp only [Ty.mask, LegalTarget.leafTys, leafVals]
      rw [valsTup_single, hr, ha, hb]; rfl
  | .bits n, ht, _, (a', ()), (b', ()), a, b, ha, hb, k, m, hk => by
    dsimp only [LegalTarget.leafTys, leafVals] at ha hb
    rw [valsTup_single] at ha hb
    dsimp only [Ty.mask, LegalTarget.leafTys] at k hk ⊢
    dsimp only [legalCmpTree.goMask]
    refine legalCmpBits_wp target o ht a' b' a b (congrArg Prod.fst ha) (congrArg Prod.fst hb)
      (k := fun r => k (r, ())) ?_
    intro r hr; exact hk (r, ()) (by dsimp only [leafVals]; rw [valsTup_single, hr]; rfl)
  | .float _, _, hf, _, _, _, _, _, _, _, _, _ => by simp [Ty.hasFloat] at hf
  | .pair u1 u2, ht, hf, fx, fy, px, py, hx, hy, k, m, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    simp only [Ty.hasFloat, Bool.or_eq_false_iff] at hf
    dsimp only [LegalTarget.leafTys] at fx fy hx hy
    dsimp only [legalCmpTree.goMask]
    have hx12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hx
    have hy12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hy
    rw [leafVals_pair, tupSplit_tupAppend, tupSplit_valsTup] at hx12 hy12
    refine legalCmpTree_goMask_wp target o u1 ht.1 hf.1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fy).1 px.1 py.1
      (congrArg Prod.fst hx12) (congrArg Prod.fst hy12) _ m fun m1 hm1 => ?_
    refine legalCmpTree_goMask_wp target o u2 ht.2 hf.2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fy).2 px.2 py.2
      (congrArg Prod.snd hx12) (congrArg Prod.snd hy12) _ m fun m2 hm2 => ?_
    exact hk (tupAppend m1 m2) (by
      dsimp only [Ty.mask, LegalTarget.leafTys]
      rw [leafVals_pair, valsTup_tupAppend, hm1, hm2]; rfl)

theorem legalCmpTree_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost} (o : CmpOp) :
    ∀ (t : Ty), target.supportsTy t = true → t.hasFloat = false →
      (xs ys : Tup (Arg Val) (target.legalTys t)) → (x y : Val t) →
      valsTup xs = encodeVal target t x → valsTup ys = encodeVal target t y →
      (k : Tup (Arg Val) (target.legalTys t.mask) → Expr Val Cont rs) → (m : Mem 64) →
      (∀ res, valsTup res = encodeVal target t.mask (liftCmp o.evalBits o.evalBool t x y) →
        wp Γ Q X (k res) m) →
      wp Γ Q X (legalCmpTree target o t xs ys k) m
  | .bool, _, _, (a', ()), (b', ()), a, b, ha, hb, k, m, hk => by
    dsimp only [LegalTarget.legalTys, LegalTarget.leafTys, Ty.mask, encodeVal] at ha hb
    rw [valsTup_single] at ha hb
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at ha hb
    dsimp only [legalCmpTree]
    by_cases hbc : target.boolCmp = true
    · rw [ite_eq_left hbc]
      simp only [wp, Op.wp, OpCode.wp, op2, vals, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, liftCmp]
      exact hk _ (by
        dsimp only [Ty.mask, LegalTarget.legalTys, LegalTarget.leafTys, encodeVal]
        rw [valsTup_single]
        exact congrArg (·, ()) (by change o.evalBool a'.val b'.val = _; rw [ha, hb]; rfl))
    · rw [ite_eq_right hbc]
      refine emitBoolCmp_wp o a' b' fun r hr => hk (r, ()) ?_
      dsimp only [Ty.mask, LegalTarget.legalTys, LegalTarget.leafTys, encodeVal]
      rw [valsTup_single, hr, ha, hb]; rfl
  | .bits n, ht, _, (a', ()), (b', ()), a, b, ha, hb, k, m, hk => by
    dsimp only [LegalTarget.legalTys, LegalTarget.leafTys, encodeVal] at ha hb
    rw [valsTup_single] at ha hb
    dsimp only [Ty.mask, LegalTarget.legalTys, LegalTarget.leafTys] at k hk ⊢
    dsimp only [legalCmpTree]
    refine legalCmpBits_wp target o ht a' b' a b (congrArg Prod.fst ha) (congrArg Prod.fst hb)
      (k := fun r => k (r, ())) ?_
    intro r hr; exact hk (r, ()) (by dsimp only [encodeVal]; rw [valsTup_single, hr]; rfl)
  | .float _, _, hf, _, _, _, _, _, _, _, _, _ => by simp [Ty.hasFloat] at hf
  | .pair t1 t2, ht, hf, xs, ys, px, py, hxs, hys, k, m, hk => by
    have htp : target.supportsTy (.pair t1 t2) = true := ht
    dsimp only [legalCmpTree]
    refine splitLegalToLeaves_wp target (.pair t1 t2) htp xs px hxs fun fx hfx =>
      splitLegalToLeaves_wp target (.pair t1 t2) htp ys py hys fun fy hfy => ?_
    refine legalCmpTree_goMask_wp target o (.pair t1 t2) htp hf fx fy px py hfx hfy _ m fun mres hmres => ?_
    exact packLeavesToLegal_wp target (Ty.mask (.pair t1 t2)) (supportsTy_mask target (.pair t1 t2))
      mres (liftCmp o.evalBits o.evalBool (.pair t1 t2) px py) hmres hk

private theorem op3_select_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {t : Ty} (c' : Arg Val .bool) (c : Bool) (hc : c'.val = c)
    (a' b' : Arg Val t) (a b : Val t) (ha : a'.val = a) (hb : b'.val = b)
    (k : Arg Val t → Expr Val Cont rs) (m : Mem 64)
    (hk : ∀ r, r.val = (if c then a else b) → wp Γ Q X (k r) m) :
    wp Γ Q X (.let_ (op3 (.select t) c' a' b') fun r => k (.var r.1)) m := by
  cases c' <;> cases a' <;> cases b' <;>
    · dsimp only [wp, Op.wp, OpCode.wp, op3, vals, Arg.val] at hc ha hb ⊢
      cases c <;> simp_all [Arg.val]

private theorem legalSelectTree_goSel_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost} (c' : Arg Val .bool) (c : Bool) (hc : c'.val = c) :
    ∀ (u : Ty), target.supportsTy u = true →
      (fx fy : Tup (Arg Val) (target.leafTys u)) → (x y : Val u) →
      valsTup fx = leafVals target u x → valsTup fy = leafVals target u y →
      (k : Tup (Arg Val) (target.leafTys u) → Expr Val Cont rs) → (m : Mem 64) →
      (∀ res, valsTup res = leafVals target u (if c then x else y) → wp Γ Q X (k res) m) →
      wp Γ Q X (legalSelectTree.goSel target c' u fx fy k) m
  | .bool, _, (a', ()), (b', ()), a, b, ha, hb, k, m, hk => by
    dsimp only [LegalTarget.leafTys, leafVals] at ha hb k hk ⊢
    rw [valsTup_single] at ha hb
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at ha hb
    dsimp only [legalSelectTree.goSel]
    by_cases hbs : target.boolSelect = true
    · rw [ite_eq_left hbs]
      exact op3_select_wp c' c hc a' b' a b ha hb (fun r => k (r, ())) m fun r hr =>
        hk (r, ()) (by rw [valsTup_single, hr])
    · rw [ite_eq_right hbs]
      refine emitBoolSelect_wp c' a' b' fun r hr => hk (r, ()) ?_
      rw [valsTup_single, hr, hc, ha, hb]
  | .bits n, _, (a', ()), (b', ()), a, b, ha, hb, k, m, hk => by
    dsimp only [LegalTarget.leafTys, leafVals] at ha hb k hk ⊢
    rw [valsTup_single] at ha hb
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at ha hb
    dsimp only [legalSelectTree.goSel]
    exact op3_select_wp c' c hc a' b' (a.setWidth (target.widenWidth n)) (b.setWidth (target.widenWidth n))
      ha hb (fun r => k (r, ())) m fun r hr =>
      hk (r, ()) (by rw [valsTup_single, hr]; cases c <;> rfl)
  | .float f, _, (a', ()), (b', ()), a, b, ha, hb, k, m, hk => by
    dsimp only [LegalTarget.leafTys, leafVals] at ha hb k hk ⊢
    rw [valsTup_single] at ha hb
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at ha hb
    dsimp only [legalSelectTree.goSel]
    exact op3_select_wp c' c hc a' b' a b ha hb (fun r => k (r, ())) m fun r hr =>
      hk (r, ()) (by rw [valsTup_single, hr])
  | .pair u1 u2, ht, fx, fy, px, py, hx, hy, k, m, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    dsimp only [LegalTarget.leafTys] at fx fy hx hy
    dsimp only [legalSelectTree.goSel]
    have hx12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hx
    have hy12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hy
    rw [leafVals_pair, tupSplit_tupAppend, tupSplit_valsTup] at hx12 hy12
    refine legalSelectTree_goSel_wp target c' c hc u1 ht.1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fy).1 px.1 py.1
      (congrArg Prod.fst hx12) (congrArg Prod.fst hy12) _ m fun r1 hr1 => ?_
    refine legalSelectTree_goSel_wp target c' c hc u2 ht.2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fy).2 px.2 py.2
      (congrArg Prod.snd hx12) (congrArg Prod.snd hy12) _ m fun r2 hr2 => ?_
    exact hk (tupAppend r1 r2) (by
      dsimp only [LegalTarget.leafTys]
      rw [leafVals_pair, valsTup_tupAppend, hr1, hr2]
      cases c <;> rfl)

theorem legalSelectTree_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost} (c' : Arg Val .bool) (c : Bool) (hc : c'.val = c) :
    ∀ (t : Ty), target.supportsTy t = true →
      (xs ys : Tup (Arg Val) (target.legalTys t)) → (x y : Val t) →
      valsTup xs = encodeVal target t x → valsTup ys = encodeVal target t y →
      (k : Tup (Arg Val) (target.legalTys t) → Expr Val Cont rs) → (m : Mem 64) →
      (∀ res, valsTup res = encodeVal target t (if c then x else y) → wp Γ Q X (k res) m) →
      wp Γ Q X (legalSelectTree target c' t xs ys k) m
  | .bool, _, (a', ()), (b', ()), a, b, ha, hb, k, m, hk => by
    dsimp only [LegalTarget.legalTys, LegalTarget.leafTys, encodeVal] at ha hb k hk ⊢
    rw [valsTup_single] at ha hb
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at ha hb
    dsimp only [legalSelectTree]
    by_cases hbs : target.boolSelect = true
    · rw [ite_eq_left hbs]
      exact op3_select_wp c' c hc a' b' a b ha hb (fun r => k (r, ())) m fun r hr =>
        hk (r, ()) (by rw [valsTup_single, hr])
    · rw [ite_eq_right hbs]
      refine emitBoolSelect_wp c' a' b' fun r hr => hk (r, ()) ?_
      rw [valsTup_single, hr, hc, ha, hb]
  | .bits n, _, (a', ()), (b', ()), a, b, ha, hb, k, m, hk => by
    dsimp only [LegalTarget.legalTys, LegalTarget.leafTys, encodeVal] at ha hb k hk ⊢
    rw [valsTup_single] at ha hb
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at ha hb
    dsimp only [legalSelectTree]
    exact op3_select_wp c' c hc a' b' (a.setWidth (target.widenWidth n)) (b.setWidth (target.widenWidth n))
      ha hb (fun r => k (r, ())) m fun r hr =>
      hk (r, ()) (by rw [valsTup_single, hr]; cases c <;> rfl)
  | .float f, _, (a', ()), (b', ()), a, b, ha, hb, k, m, hk => by
    dsimp only [LegalTarget.legalTys, LegalTarget.leafTys, encodeVal] at ha hb k hk ⊢
    rw [valsTup_single] at ha hb
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at ha hb
    dsimp only [legalSelectTree]
    exact op3_select_wp c' c hc a' b' a b ha hb (fun r => k (r, ())) m fun r hr =>
      hk (r, ()) (by rw [valsTup_single, hr])
  | .pair t1 t2, ht, xs, ys, px, py, hxs, hys, k, m, hk => by
    have htp : target.supportsTy (.pair t1 t2) = true := ht
    dsimp only [legalSelectTree]
    refine splitLegalToLeaves_wp target (.pair t1 t2) htp xs px hxs fun fx hfx =>
      splitLegalToLeaves_wp target (.pair t1 t2) htp ys py hys fun fy hfy => ?_
    refine legalSelectTree_goSel_wp target c' c hc (.pair t1 t2) htp fx fy px py hfx hfy _ m fun fres hfres => ?_
    exact packLeavesToLegal_wp target (.pair t1 t2) htp fres (if c then px else py) hfres hk

private theorem legalBlendTree_goBlend_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost} :
    ∀ (u : Ty), target.supportsTy u = true →
      (fm : Tup (Arg Val) (target.leafTys u.mask)) →
      (fx fy : Tup (Arg Val) (target.leafTys u)) →
      (msk : Val u.mask) → (x y : Val u) →
      valsTup fm = leafVals target u.mask msk →
      valsTup fx = leafVals target u x → valsTup fy = leafVals target u y →
      (k : Tup (Arg Val) (target.leafTys u) → Expr Val Cont rs) → (m : Mem 64) →
      (∀ res, valsTup res = leafVals target u (blendV u msk x y) → wp Γ Q X (k res) m) →
      wp Γ Q X (legalBlendTree.goBlend target u fm fx fy k) m
  | .bool, _, (c', ()), (a', ()), (b', ()), c, a, b, hc, ha, hb, k, m, hk => by
    dsimp only [Ty.mask, LegalTarget.leafTys, leafVals] at hc ha hb k hk ⊢
    rw [valsTup_single] at hc ha hb
    replace hc := congrArg Prod.fst hc
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at hc ha hb
    dsimp only [legalBlendTree.goBlend]
    by_cases hbs : target.boolSelect = true
    · rw [ite_eq_left hbs]
      exact op3_select_wp c' c hc a' b' a b ha hb (fun r => k (r, ())) m fun r hr =>
        hk (r, ()) (by rw [valsTup_single, hr]; rfl)
    · rw [ite_eq_right hbs]
      refine emitBoolSelect_wp c' a' b' fun r hr => hk (r, ()) ?_
      rw [valsTup_single, hr, hc, ha, hb]; rfl
  | .bits n, _, (c', ()), (a', ()), (b', ()), c, a, b, hc, ha, hb, k, m, hk => by
    dsimp only [Ty.mask, LegalTarget.leafTys, leafVals] at hc ha hb k hk ⊢
    rw [valsTup_single] at hc ha hb
    replace hc := congrArg Prod.fst hc
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at hc ha hb
    dsimp only [legalBlendTree.goBlend]
    exact op3_select_wp c' c hc a' b' (a.setWidth (target.widenWidth n)) (b.setWidth (target.widenWidth n))
      ha hb (fun r => k (r, ())) m fun r hr =>
      hk (r, ()) (by rw [valsTup_single, hr]; cases c <;> rfl)
  | .float f, _, (c', ()), (a', ()), (b', ()), c, a, b, hc, ha, hb, k, m, hk => by
    dsimp only [Ty.mask, LegalTarget.leafTys, leafVals] at hc ha hb k hk ⊢
    rw [valsTup_single] at hc ha hb
    replace hc := congrArg Prod.fst hc
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at hc ha hb
    dsimp only [legalBlendTree.goBlend]
    exact op3_select_wp c' c hc a' b' a b ha hb (fun r => k (r, ())) m fun r hr =>
      hk (r, ()) (by rw [valsTup_single, hr]; rfl)
  | .pair u1 u2, ht, fm, fx, fy, msk, px, py, hm, hx, hy, k, m, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    dsimp only [Ty.mask, LegalTarget.leafTys] at fm fx fy hm hx hy
    dsimp only [legalBlendTree.goBlend]
    have hm12 := congrArg (tupSplit (as := target.leafTys u1.mask) (bs := target.leafTys u2.mask)) hm
    have hx12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hx
    have hy12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hy
    rw [leafVals_pair, tupSplit_tupAppend, tupSplit_valsTup] at hm12 hx12 hy12
    refine legalBlendTree_goBlend_wp target u1 ht.1
      (tupSplit (as := target.leafTys u1.mask) (bs := target.leafTys u2.mask) fm).1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fy).1 msk.1 px.1 py.1
      (congrArg Prod.fst hm12) (congrArg Prod.fst hx12) (congrArg Prod.fst hy12) _ m fun r1 hr1 => ?_
    refine legalBlendTree_goBlend_wp target u2 ht.2
      (tupSplit (as := target.leafTys u1.mask) (bs := target.leafTys u2.mask) fm).2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fy).2 msk.2 px.2 py.2
      (congrArg Prod.snd hm12) (congrArg Prod.snd hx12) (congrArg Prod.snd hy12) _ m fun r2 hr2 => ?_
    exact hk (tupAppend r1 r2) (by
      dsimp only [LegalTarget.leafTys]
      rw [leafVals_pair, valsTup_tupAppend, hr1, hr2]; rfl)

theorem legalBlendTree_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost} :
    ∀ (t : Ty), target.supportsTy t = true →
      (ms : Tup (Arg Val) (target.legalTys t.mask)) →
      (xs ys : Tup (Arg Val) (target.legalTys t)) →
      (msk : Val t.mask) → (x y : Val t) →
      valsTup ms = encodeVal target t.mask msk →
      valsTup xs = encodeVal target t x → valsTup ys = encodeVal target t y →
      (k : Tup (Arg Val) (target.legalTys t) → Expr Val Cont rs) → (m : Mem 64) →
      (∀ res, valsTup res = encodeVal target t (blendV t msk x y) → wp Γ Q X (k res) m) →
      wp Γ Q X (legalBlendTree target t ms xs ys k) m
  | .bool, _, (c', ()), (a', ()), (b', ()), c, a, b, hc, ha, hb, k, m, hk => by
    dsimp only [Ty.mask, LegalTarget.legalTys, LegalTarget.leafTys, encodeVal] at hc ha hb k hk ⊢
    rw [valsTup_single] at hc ha hb
    replace hc := congrArg Prod.fst hc
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at hc ha hb
    dsimp only [legalBlendTree]
    by_cases hbs : target.boolSelect = true
    · rw [ite_eq_left hbs]
      exact op3_select_wp c' c hc a' b' a b ha hb (fun r => k (r, ())) m fun r hr =>
        hk (r, ()) (by rw [valsTup_single, hr]; rfl)
    · rw [ite_eq_right hbs]
      refine emitBoolSelect_wp c' a' b' fun r hr => hk (r, ()) ?_
      rw [valsTup_single, hr, hc, ha, hb]; rfl
  | .bits n, _, (c', ()), (a', ()), (b', ()), c, a, b, hc, ha, hb, k, m, hk => by
    dsimp only [Ty.mask, LegalTarget.legalTys, LegalTarget.leafTys, encodeVal] at hc ha hb k hk ⊢
    rw [valsTup_single] at hc ha hb
    replace hc := congrArg Prod.fst hc
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at hc ha hb
    dsimp only [legalBlendTree]
    exact op3_select_wp c' c hc a' b' (a.setWidth (target.widenWidth n)) (b.setWidth (target.widenWidth n))
      ha hb (fun r => k (r, ())) m fun r hr =>
      hk (r, ()) (by rw [valsTup_single, hr]; cases c <;> rfl)
  | .float f, _, (c', ()), (a', ()), (b', ()), c, a, b, hc, ha, hb, k, m, hk => by
    dsimp only [Ty.mask, LegalTarget.legalTys, LegalTarget.leafTys, encodeVal] at hc ha hb k hk ⊢
    rw [valsTup_single] at hc ha hb
    replace hc := congrArg Prod.fst hc
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at hc ha hb
    dsimp only [legalBlendTree]
    exact op3_select_wp c' c hc a' b' a b ha hb (fun r => k (r, ())) m fun r hr =>
      hk (r, ()) (by rw [valsTup_single, hr]; rfl)
  | .pair t1 t2, ht, ms, xs, ys, msk, px, py, hms, hxs, hys, k, m, hk => by
    have htp : target.supportsTy (.pair t1 t2) = true := ht
    dsimp only [legalBlendTree]
    refine splitLegalToLeaves_wp target (Ty.mask (.pair t1 t2)) (supportsTy_mask target (.pair t1 t2))
        ms msk hms fun fm hfm =>
      splitLegalToLeaves_wp target (.pair t1 t2) htp xs px hxs fun fx hfx =>
      splitLegalToLeaves_wp target (.pair t1 t2) htp ys py hys fun fy hfy => ?_
    refine legalBlendTree_goBlend_wp target (.pair t1 t2) htp fm fx fy msk px py hfm hfx hfy _ m fun fres hfres => ?_
    exact packLeavesToLegal_wp target (.pair t1 t2) htp fres (blendV (.pair t1 t2) msk px py) hfres hk

private theorem legalFCmpTree_goFCmp_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost} (o : FCmpOp) :
    ∀ (u : Ty), target.supportsTy u = true → u.isFloatTree = true →
      (fx fy : Tup (Arg Val) (target.leafTys u)) → (x y : Val u) →
      valsTup fx = leafVals target u x → valsTup fy = leafVals target u y →
      (k : Tup (Arg Val) (target.leafTys u.mask) → Expr Val Cont rs) → (m : Mem 64) →
      (∀ res, valsTup res = leafVals target u.mask (liftFCmp o u x y) →
        wp Γ Q X (k res) m) →
      wp Γ Q X (legalFCmpTree.goFCmp target o u fx fy k) m
  | .bool, _, hf, _, _, _, _, _, _, _, _, _ => by simp [Ty.isFloatTree] at hf
  | .bits _, _, hf, _, _, _, _, _, _, _, _, _ => by simp [Ty.isFloatTree] at hf
  | .float f, _, _, (a', ()), (b', ()), a, b, ha, hb, k, m, hk => by
    dsimp only [LegalTarget.leafTys, leafVals] at ha hb
    rw [valsTup_single] at ha hb
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at ha hb
    simp only [legalFCmpTree.goFCmp, wp, Op.wp, OpCode.wp, op2, vals, Ty.isFloatTree,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte, liftFCmp]
    exact hk _ (by
      dsimp only [Ty.mask, LegalTarget.leafTys, leafVals]
      rw [valsTup_single]
      exact congrArg (·, ()) (by
        change fcmpLeaf o f a'.val b'.val = _
        rw [ha, hb]; rfl))
  | .pair u1 u2, ht, hf, fx, fy, px, py, hx, hy, k, m, hk => by
    simp only [LegalTarget.supportsTy, Bool.and_eq_true] at ht
    simp only [Ty.isFloatTree, Bool.and_eq_true] at hf
    dsimp only [LegalTarget.leafTys] at fx fy hx hy
    dsimp only [legalFCmpTree.goFCmp]
    have hx12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hx
    have hy12 := congrArg (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2)) hy
    rw [leafVals_pair, tupSplit_tupAppend, tupSplit_valsTup] at hx12 hy12
    refine legalFCmpTree_goFCmp_wp target o u1 ht.1 hf.1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).1
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fy).1 px.1 py.1
      (congrArg Prod.fst hx12) (congrArg Prod.fst hy12) _ m fun m1 hm1 => ?_
    refine legalFCmpTree_goFCmp_wp target o u2 ht.2 hf.2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fx).2
      (tupSplit (as := target.leafTys u1) (bs := target.leafTys u2) fy).2 px.2 py.2
      (congrArg Prod.snd hx12) (congrArg Prod.snd hy12) _ m fun m2 hm2 => ?_
    exact hk (tupAppend m1 m2) (by
      dsimp only [Ty.mask, LegalTarget.leafTys]
      rw [leafVals_pair, valsTup_tupAppend, hm1, hm2]; rfl)

theorem legalFCmpTree_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost} (o : FCmpOp) :
    ∀ (t : Ty), target.supportsTy t = true → t.isFloatTree = true →
      (xs ys : Tup (Arg Val) (target.legalTys t)) → (x y : Val t) →
      valsTup xs = encodeVal target t x → valsTup ys = encodeVal target t y →
      (k : Tup (Arg Val) (target.legalTys t.mask) → Expr Val Cont rs) → (m : Mem 64) →
      (∀ res, valsTup res = encodeVal target t.mask (liftFCmp o t x y) →
        wp Γ Q X (k res) m) →
      wp Γ Q X (legalFCmpTree target o t xs ys k) m
  | .bool, _, hf, _, _, _, _, _, _, _, _, _ => by simp [Ty.isFloatTree] at hf
  | .bits _, _, hf, _, _, _, _, _, _, _, _, _ => by simp [Ty.isFloatTree] at hf
  | .float f, _, _, (a', ()), (b', ()), a, b, ha, hb, k, m, hk => by
    dsimp only [LegalTarget.legalTys, LegalTarget.leafTys, encodeVal] at ha hb
    rw [valsTup_single] at ha hb
    replace ha := congrArg Prod.fst ha
    replace hb := congrArg Prod.fst hb
    dsimp only at ha hb
    simp only [legalFCmpTree, wp, Op.wp, OpCode.wp, op2, vals, Ty.isFloatTree,
      Bool.not_true, Bool.false_eq_true, ↓reduceIte, liftFCmp]
    exact hk _ (by
      dsimp only [Ty.mask, LegalTarget.legalTys, LegalTarget.leafTys, encodeVal]
      rw [valsTup_single]
      exact congrArg (·, ()) (by
        change fcmpLeaf o f a'.val b'.val = _
        rw [ha, hb]; rfl))
  | .pair t1 t2, ht, hf, xs, ys, px, py, hxs, hys, k, m, hk => by
    have htp : target.supportsTy (.pair t1 t2) = true := ht
    dsimp only [legalFCmpTree]
    refine splitLegalToLeaves_wp target (.pair t1 t2) htp xs px hxs fun fx hfx =>
      splitLegalToLeaves_wp target (.pair t1 t2) htp ys py hys fun fy hfy => ?_
    refine legalFCmpTree_goFCmp_wp target o (.pair t1 t2) htp hf fx fy px py hfx hfy _ m fun mres hmres => ?_
    exact packLeavesToLegal_wp target (Ty.mask (.pair t1 t2)) (supportsTy_mask target (.pair t1 t2))
      mres (liftFCmp o (.pair t1 t2) px py) hmres hk

theorem op1_bitcast_wp_top {t u : Ty} (h : t.size = u.size) (a : Val t)
    (post : Tup Val [u] → Prop) :
    OpCode.wp (.bitcast t u h) (a, ()) post = post (ofBits u (BitVec.cast h (toBits t a)), ()) := rfl

theorem legalFloatBit2_wp (target : LegalTarget) {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost}
    (mkOp : (w : Nat) → OpCode [.bits w, .bits w] [.bits w])
    (mkFOp : (f : Fmt) → OpCode [.float f, .float f] [.float f])
    (f : Fmt) (g : BitVec f.width → BitVec f.width → BitVec f.width)
    (hF : ∀ (a b : BitVec f.width) post, OpCode.wp (mkFOp f) (a, b, ()) post ↔ post (g a b, ()))
    (hB : ∀ (a b : BitVec f.width) post, OpCode.wp (mkOp f.width) (a, b, ()) post ↔ post (g a b, ()))
    (x' y' : Arg Val (.float f)) (x y : BitVec f.width)
    (hx : x'.val = x) (hy : y'.val = y)
    {k : Arg Val (.float f) → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r, r.val = g x y → wp Γ Q X (k r) m) :
    wp Γ Q X (legalFloatBit2 target mkOp mkFOp f x' y' k) m := by
  dsimp only [legalFloatBit2]
  by_cases hsb : target.scalarFloatBitwise = true
  · rw [ite_eq_left hsb]
    dsimp only [wp, Op.wp, op2, vals]
    rw [hx, hy, hF]
    exact hk _ rfl
  · rw [ite_eq_right hsb]
    dsimp only [wp, Op.wp, op1, op2, vals]
    rw [op1_bitcast_wp_top, op1_bitcast_wp_top]
    dsimp only [Arg.val_var, toBits, ofBits]
    simp only [BitVec.cast_eq]
    rw [hB x'.val y'.val]
    rw [op1_bitcast_wp_top]
    dsimp only [toBits, ofBits]
    simp only [BitVec.cast_eq]
    exact hk _ (by change g x'.val y'.val = _; rw [hx, hy])


end LegalWp

end LeanQbe.T
