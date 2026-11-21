module

public import LeanQbe.T.LegalWfBaseLemmas
public import LeanQbe.T.LegalEmit

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

/-- Canonical legalized environment transforming every source contract via `encodeTup` / `legalPost`
  /
`legalXPost` (with consequence closure matching `wp_env_mono`). -/
def legalEnv (target : LegalTarget) (Γ : Env) : Env :=
  fun f as' bs' xs' m' Q' X' =>
    ∃ (as bs : List Ty) (has : target.legalSig as = as') (hbs : target.legalSig bs = bs')
      (xs : Tup Val as) (P : Post bs) (E : XPost),
      cast (congrArg (Tup Val) has) (encodeTup target as xs) = xs' ∧
      (∀ r m, legalPost target P r m → Q' (cast (congrArg (Tup Val) hbs) r) m) ∧
      (∀ g cs ys m, legalXPost target E g cs ys m → X' g cs ys m) ∧
      Γ f as bs xs m' P E

theorem envRefines_legalEnv (target : LegalTarget) (Γ : Env) :
  EnvRefines target Γ (legalEnv target Γ) :=
  fun _ as bs xs _ P E h =>
    ⟨as, bs, rfl, rfl, xs, P, E, rfl, fun _ _ hp => hp, fun _ _ _ _ hx => hx, h⟩

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
  | .pair a b => by
      simp [LegalTarget.supportsTy, supportsTy_mask target a, supportsTy_mask target b]

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
    encodeTup target [t] (v, ()) = cast (congrArg (Tup Val) heq.symm)
      (show Tup Val [t] from (v, ())) :=
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

theorem valsTup_legalArg (target : LegalTarget) {G : Ctx Val (LVar target Val)}
  (hc : CGoodWp target G)
    {t : Ty} {a : Arg Val t} {la : Arg (LVar target Val) t} (ha : ArgRel G t a la) :
    valsTup (legalArg target la) = encodeVal target t a.val := by
  cases ha with
  | var hm => exact hc _ _ _ hm
  | imm c => simp [legalArg, Arg.val]

theorem valsTup_joinArgs (target : LegalTarget) {G : Ctx Val (LVar target Val)}
  (hc : CGoodWp target G) :
    {ts : List Ty} → {as : Tup (Arg Val) ts} → {las : Tup (Arg (LVar target Val)) ts} →
    TRel (ArgRel G) as las → valsTup (joinArgs target las) = encodeTup target ts (valsTup as)
  | [], (), (), .nil => rfl
  | _ :: _, (_, _), (_, _), .cons ha has => by
    dsimp only [joinArgs, encodeTup, LegalTarget.legalSig]
    rw [valsTup_tupAppend, valsTup_legalArg target hc ha, valsTup_joinArgs target hc has,
      valsTup_cons]

theorem CGoodWp.pushTRel (target : LegalTarget) {G : Ctx Val (LVar target Val)}
  (hc : CGoodWp target G) :
    {ts : List Ty} → {xs : Tup Val ts} → {lxs : Tup (LVar target Val) ts} →
    TRel (fun t x lv => valsTup lv = encodeVal target t x) xs lxs →
    CGoodWp target (Tup.zip xs lxs ++ G)
  | [], (), (), .nil, _, _, _, hm => hc _ _ _ hm
  | _ :: _, (_, _), (_, _), .cons hx hxs, t, v, lv, hm => by
    simp only [Tup.zip, List.cons_append] at hm
    rcases List.mem_cons.1 hm with hhead | htail
    · cases hhead; exact hx
    · exact CGoodWp.pushTRel target hc hxs t v lv htail

theorem CGoodWp.pushSplit (target : LegalTarget) {G : Ctx Val (LVar target Val)}
  (hc : CGoodWp target G) :
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
    (unlegalTupCont target Js).get i xs m = (Js.get (Member.map target.legalSig i))
      (encodeTup target ts xs) m
  | _ :: _, (_, _), _, .here, _, _ => rfl
  | _ :: _, (_, Js), _, .there i, xs, m => unlegalTupCont_get target Js i xs m

theorem DGoodWp.pushUnlegal (target : LegalTarget) {D : Ctx Cont (LLab target Cont)}
  (hd : DGoodWp target D) :
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

private theorem unpackToLeaves_wp (target : LegalTarget) {Γ : Env} {rs : List Ty} {Q : Post rs}
  {X : XPost} :
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
      rw [val_castArgBits, ha, cast_eq_setWidth heq.symm, BitVec.setWidth_setWidth_of_le _ hnw,
        BitVec.setWidth_eq]
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
      exact packFromLegal_wp target a ht.1 (tupSplit (splitToTup hf xs)).1 p.1
        (congrArg Prod.fst h12)
        (fun va hva => packFromLegal_wp target b ht.2 (tupSplit (splitToTup hf xs)).2 p.2
          (congrArg Prod.snd h12) (fun vb hvb =>
            by
              dsimp only [wp, Op.wp, OpCode.wp]
              exact hk _ (Prod.ext hva hvb)))

theorem splitLegalToLeaves_wp (target : LegalTarget) {Γ : Env} {rs : List Ty} {Q : Post rs}
  {X : XPost} :
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
      have h' : (packedToTup hp xs).1.val = p :=
        congrArg Prod.fst (valsTup_packedToTup_encode target hp hxs)
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

theorem packLeavesToLegal_wp (target : LegalTarget) {Γ : Env} {rs : List Ty} {Q : Post rs}
  {X : XPost} :
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
    have h1 : valsTup (tupSplit (as := target.leafTys a) (bs := target.leafTys b) fx).1 = leafVals
      target a p.1 :=
      congrArg Prod.fst h12
    have h2 : valsTup (tupSplit (as := target.leafTys a) (bs := target.leafTys b) fx).2 = leafVals
      target b p.2 :=
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

theorem emitMaskToN_wp {target_Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {n w : Nat} (hnw : n ≤ w) {x : Arg Val (.bits w)} {v : BitVec w} (hx : x.val = v)
    {k : Arg Val (.bits w) → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r, r.val = (v.setWidth n).setWidth w → wp target_Γ Q X (k r) m) :
    wp target_Γ Q X (emitMaskToN n w x k) m :=
  (maskToNEmit_bundle (.withWidth w) List.mem_cons_self hnw).wp_eq (x, ())
    (fun r hr => hk r (hx ▸ hr)) (maskToNEmit_eq_emitMaskToN n w x k)

theorem emitSextToW_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {n w : Nat} (hn0 : 0 < n) (hnw : n ≤ w) {x : Arg Val (.bits w)} {a : BitVec n}
    (hx : x.val = a.setWidth w) {k : Arg Val (.bits w) → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r, r.val = a.signExtend w → wp Γ Q X (k r) m) :
    wp Γ Q X (emitSextToW n w x k) m :=
  (sextToWEmit_bundle (.withWidth w) List.mem_cons_self hn0 hnw).wp_eq (x, ()) ⟨a, hx, hk⟩
    (sextToWEmit_eq_emitSextToW n w x k)

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

theorem emitBoolCmp_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (o : CmpOp) (a b : Arg Val .bool) {k : Arg Val .bool → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r, r.val = o.evalBool a.val b.val → wp Γ Q X (k r) m) :
    wp Γ Q X (emitBoolCmp o a b k) m :=
  (boolCmpEmit_bundle .aarch64 o).wp_eq (a, b, ()) hk (boolCmpEmit_eq_emitBoolCmp o a b k)

theorem emitBoolSelect_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (c a b : Arg Val .bool) {k : Arg Val .bool → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r, r.val = (if c.val then a.val else b.val) → wp Γ Q X (k r) m) :
    wp Γ Q X (emitBoolSelect c a b k) m :=
  (boolSelectEmit_bundle .aarch64).wp_eq (c, a, b, ()) hk rfl

theorem emitTernlogBits_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {w : Nat}
    (a b c : Arg Val (.bits w)) (imm : BitVec 8)
    {k : Arg Val (.bits w) → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r, r.val = ternaryLogic a.val b.val c.val imm → wp Γ Q X (k r) m) :
    wp Γ Q X (emitTernlogBits w a b c imm k) m :=
  (ternlogBitsEmit_bundle (.withWidth w) List.mem_cons_self imm).wp_eq (a, b, c, ()) hk
    (ternlogBitsEmit_eq_emitTernlogBits w imm a b c k)

theorem emitTernlogBool_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (a b c : Arg Val .bool) (imm : BitVec 8)
    {k : Arg Val .bool → Expr Val Cont rs} {m : Mem 64}
    (hk : ∀ r, r.val = ternaryLogicBool a.val b.val c.val imm → wp Γ Q X (k r) m) :
    wp Γ Q X (emitTernlogBool a b c imm k) m :=
  (ternlogBoolEmit_bundle .aarch64 imm).wp_eq (a, b, c, ()) hk
    (ternlogBoolEmit_eq_emitTernlogBool imm a b c k)


end LegalWp

end LeanQbe.T
