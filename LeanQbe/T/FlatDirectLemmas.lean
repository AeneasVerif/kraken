module

public import LeanQbe.T.FlatDirect
public import LeanQbe.T.FlatLemmas
public import LeanQbe.T.PassFlatKit
public import LeanQbe.T.Trie

/-!
# Foundational `TFlat` Round-Trip, `TrieCtxMatch`, `Ext`, and `supportsSource` Lemmas

* `FlatCtxMatch`, `denote_toTFlat_eq`, `Func.renorm_eq_self`: exact PHOAS-to-`TFlat`-to-PHOAS
  identity for any `Func.Wf` function (using `funext`, within `std3`).
* `CtxLevels`, `toTFlat_denote_eq`, `reifyFunc_denoteFunc_eq`, `Func.renorm_denoteFunc`: exact
  `TFlat`-to-PHOAS-to-`TFlat` identity under `wfCheck = true`.
* `TrieCtxMatch` & `TrieProjMatch`: reusable de Bruijn level `Trie` ↔ index `List` kits shared
  across first-order passes and `RegaFlat`.
* `TFlat.ext_eq_fn_ext` & `TFlatFn.supportsSource_eq`: exact simulation for `TFlat.ext` and
  `TFlatFn.supportsSource`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

/-! ## PHOAS → `TFlat` → PHOAS identity (`denote_toTFlat_eq`, `Func.renorm_eq_self`) -/

/-- Context correspondence relating de Bruijn level binders `G : Ctx (fun _ => Nat) f` to the
runtime environment `vs` (`0` = newest binder). -/
@[expose] def FlatCtxMatch {α : Type} {f : α → Type}
    (look : List ((a : α) × f a) → (a : α) → Nat → Option (f a))
    (G : Ctx (fun _ => Nat) f) (vs : List ((a : α) × f a)) : Prop :=
  ∀ p ∈ G, p.2.1 < vs.length ∧ look vs p.1 (vs.length - 1 - p.2.1) = some p.2.2

namespace FlatCtxMatch

theorem mono {α : Type} {f : α → Type}
    {look : List ((a : α) × f a) → (a : α) → Nat → Option (f a)}
    {G₁ G₂ : Ctx (fun _ => Nat) f} {vs : List ((a : α) × f a)}
    (hsub : ∀ p ∈ G₂, p ∈ G₁) (h : FlatCtxMatch look G₁ vs) : FlatCtxMatch look G₂ vs :=
  fun p hp => h p (hsub p hp)

theorem empty {α : Type} {f : α → Type}
    {look : List ((a : α) × f a) → (a : α) → Nat → Option (f a)} :
    FlatCtxMatch look [] [] :=
  fun _ hp => nomatch hp

theorem cons {α : Type} {f : α → Type}
    {look : List ((a : α) × f a) → (a : α) → Nat → Option (f a)}
    (hlook_head : ∀ a (x : f a) vs, look (⟨a, x⟩ :: vs) a 0 = some x)
    (hlook_tail : ∀ a (x : f a) vs b idx, look (⟨a, x⟩ :: vs) b (idx + 1) = look vs b idx)
    {G : Ctx (fun _ => Nat) f} {vs : List ((a : α) × f a)}
    (hvs : FlatCtxMatch look G vs) (a : α) (x : f a) :
    FlatCtxMatch look (⟨a, vs.length, x⟩ :: G) (⟨a, x⟩ :: vs) := by
  intro p hp
  rcases List.mem_cons.1 hp with rfl | hp
  · refine ⟨Nat.lt_succ_self _, ?_⟩
    simp only [List.length_cons, Nat.add_sub_cancel, Nat.sub_self]
    exact hlook_head a x vs
  · obtain ⟨hlt, hl⟩ := hvs p hp
    dsimp only at hlt
    refine ⟨Nat.lt_succ_of_lt hlt, ?_⟩
    have hidx : (⟨a, x⟩ :: vs).length - 1 - p.2.1 = (vs.length - 1 - p.2.1) + 1 := by
      rw [List.length_cons]; omega
    rw [hidx, hlook_tail]
    exact hl

theorem pushTup {α : Type} {f : α → Type}
    {look : List ((a : α) × f a) → (a : α) → Nat → Option (f a)}
    (hlook_head : ∀ a (x : f a) vs, look (⟨a, x⟩ :: vs) a 0 = some x)
    (hlook_tail : ∀ a (x : f a) vs b idx, look (⟨a, x⟩ :: vs) b (idx + 1) = look vs b idx) :
    {as : List α} → (xs : Tup f as) → {G : Ctx (fun _ => Nat) f} →
    {vs : List ((a : α) × f a)} → FlatCtxMatch look G vs →
    FlatCtxMatch look (Tup.zip (Tup.levels as vs.length) xs ++ G) (LeanQbe.T.pushTup xs vs)
  | [], (), _, _, hvs => by
    dsimp only [Tup.zip]; simp only [List.nil_append]; exact hvs
  | a :: _, (x, xs), _, _, hvs => by
    have h1 := cons hlook_head hlook_tail hvs a x
    have h2 := pushTup hlook_head hlook_tail xs h1
    simp only [List.length_cons] at h2
    refine h2.mono fun p hp => ?_
    dsimp only [Tup.levels, Tup.zip] at hp ⊢
    simp only [List.cons_append, List.mem_append, List.mem_cons] at hp ⊢
    rcases hp with rfl | hp | hp
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl hp
    · exact Or.inr (Or.inr hp)

end FlatCtxMatch

private theorem lookupV_head' {V : Ty → Type} (t : Ty) (v : V t) (vs : List ((u : Ty) × V u)) :
    lookupV (⟨t, v⟩ :: vs) t 0 = some v := by
  dsimp only [lookupV, listGet?]; exact PassFlatKit.castTy_self t v

private theorem lookupL_head' {L : List Ty → Type} (ts : List Ty) (l : L ts)
    (ls : List ((us : List Ty) × L us)) :
    lookupL (⟨ts, l⟩ :: ls) ts 0 = some l := by
  dsimp only [lookupL, listGet?]; exact PassFlatKit.castListTy_self ts l

private theorem flatCtxMatch_pushTupV {V : Ty → Type} {G : Ctx K V} {vs : List ((t : Ty) × V t)}
    (hvs : FlatCtxMatch lookupV G vs) {as : List Ty} (xs : Tup V as) :
    FlatCtxMatch lookupV (Tup.zip (Tup.levels as vs.length) xs ++ G) (pushTup xs vs) :=
  FlatCtxMatch.pushTup lookupV_head' (fun _ _ _ _ _ => rfl) xs hvs

private theorem flatCtxMatch_pushTupL {L : List Ty → Type} {D : Ctx KL L}
    {ls : List ((ts : List Ty) × L ts)} (hls : FlatCtxMatch lookupL D ls)
    {sig : List (List Ty)} (Js : Tup L sig) :
    FlatCtxMatch lookupL (Tup.zip (Tup.levels sig ls.length) Js ++ D) (pushTup Js ls) :=
  FlatCtxMatch.pushTup lookupL_head' (fun _ _ _ _ _ => rfl) Js hls

private theorem denoteArg_idxArg_flat {V : Ty → Type} {G : Ctx K V} {vs : List ((t : Ty) × V t)}
    (hvs : FlatCtxMatch lookupV G vs) {t : Ty} {a₁ : Arg K t} {a₂ : Arg V t}
    (ha : ArgRel G t a₁ a₂) :
    denoteArg vs (idxArg vs.length a₁) = some a₂ := by
  cases ha with
  | @var lvl v hm =>
    obtain ⟨hlt, hl⟩ := hvs _ hm
    dsimp only [idxArg]; simp only [hlt, ↓reduceIte]; dsimp only [denoteArg]; rw [hl]
  | imm c => rfl

private theorem denoteArgs_idxArgs_flat {V : Ty → Type} {G : Ctx K V} {vs : List ((t : Ty) × V t)}
    (hvs : FlatCtxMatch lookupV G vs) :
    {ts : List Ty} → {as₁ : Tup (Arg K) ts} → {as₂ : Tup (Arg V) ts} →
    TRel (ArgRel G) as₁ as₂ →
    denoteArgs vs (idxArgs vs.length as₁) = some as₂
  | [], (), (), .nil => rfl
  | _ :: _, (_, _), (_, _), .cons h hs => by
    dsimp only [idxArgs, denoteArgs]
    rw [denoteArg_idxArg_flat hvs h, denoteArgs_idxArgs_flat hvs hs]

private theorem blocks_eq_of_get {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {sig : List (List Ty)} → {bs₁ bs₂ : Blocks V L rs sig} →
    (∀ {ts} (i : Member ts sig) (xs : Tup V ts), bs₁.get i xs = bs₂.get i xs) →
    bs₁ = bs₂
  | _, .nil, .nil, _ => rfl
  | _ :: _, .cons f₁ bt₁, .cons f₂ bt₂, h => by
    have hf : f₁ = f₂ := funext fun xs => h .here xs
    have hbt : bt₁ = bt₂ := blocks_eq_of_get fun i xs => h (.there i) xs
    rw [hf, hbt]

/-- Exact PHOAS-to-`TFlat`-to-PHOAS identity under relational `Wf` and `FlatCtxMatch`. -/
theorem denote_toTFlat_eq {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    {G : Ctx K V} {D : Ctx KL L} {e₁ : Expr K KL rs} {e₂ : Expr V L rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ (vs : List ((t : Ty) × V t)) (ls : List ((ts : List Ty) × L ts)),
      FlatCtxMatch lookupV G vs → FlatCtxMatch lookupL D ls →
      denote V L (toTFlat e₁ vs.length ls.length) vs ls = e₂ := by
  induction hwf using Wf.induct with
  | @let_ G D ts op₁ op₂ k₁ k₂ hop _ ih =>
    intro vs ls hvs hls
    cases hop with
    | @mk _ _ code args₁ args₂ hargs =>
      dsimp only [toTFlat, denote]
      rw [denoteArgs_idxArgs_flat hvs hargs]
      dsimp only
      refine congrArg (Expr.let_ _) (funext fun xs => ?_)
      have hlen : vs.length + ts.length = (pushTup xs vs).length := by
        rw [pushTup_length xs vs, Nat.add_comm]
      rw [hlen]
      exact ih (Tup.levels ts vs.length) xs (pushTup xs vs) ls
        (flatCtxMatch_pushTupV hvs xs) hls
  | load t ha _ ih =>
    intro vs ls hvs hls
    dsimp only [toTFlat, denote]
    rw [denoteArg_idxArg_flat hvs ha]
    dsimp only
    refine congrArg (Expr.load t _) (funext fun v => ?_)
    exact ih vs.length v (⟨t, v⟩ :: vs) ls
      (FlatCtxMatch.cons lookupV_head' (fun _ _ _ _ _ => rfl) hvs t v) hls
  | store hv ha _ ih =>
    intro vs ls hvs hls
    dsimp only [toTFlat, denote]
    rw [denoteArg_idxArg_flat hvs hv, denoteArg_idxArg_flat hvs ha]
    dsimp only
    rw [ih vs ls hvs hls]
  | call f hargs _ ih =>
    intro vs ls hvs hls
    dsimp only [toTFlat, denote]
    rw [denoteArgs_idxArgs_flat hvs hargs]
    dsimp only
    refine congrArg (Expr.call f _) (funext fun xs => ?_)
    have hk := ih (Tup.levels _ vs.length) xs (pushTup xs vs) ls (flatCtxMatch_pushTupV hvs xs) hls
    rwa [pushTup_length xs vs] at hk
  | jnz hc _ _ iht ihe =>
    intro vs ls hvs hls
    dsimp only [toTFlat, denote]
    rw [denoteArg_idxArg_flat hvs hc]
    dsimp only
    rw [iht vs ls hvs hls, ihe vs ls hvs hls]
  | jump hj hargs =>
    intro vs ls hvs hls
    obtain ⟨hlt, hl⟩ := hls _ hj
    dsimp only [toTFlat]; simp only [hlt, ↓reduceIte]; dsimp only [denote]
    rw [hl, denoteArgs_idxArgs_flat hvs hargs]
  | ret hvs' =>
    intro vs ls hvs _
    dsimp only [toTFlat, denote]
    rw [denoteArgs_idxArgs_flat hvs hvs']
  | exit f hargs =>
    intro vs ls hvs _
    dsimp only [toTFlat, denote]
    rw [denoteArgs_idxArgs_flat hvs hargs]
  | hlt =>
    intro _ _ _ _; rfl
  | @group _ _ sig _ b₂ _ k₂ _ _ ihb ihk =>
    intro vs ls hvs hls
    dsimp only [toTFlat, denote]
    refine congr (congrArg (Expr.group (sig := sig)) (funext fun Js => ?_)) (funext fun Js => ?_)
    · refine blocks_eq_of_get fun {ts} i xs => ?_
      rw [denoteB_toTBlocks_get]
      have hlv : vs.length + ts.length = (pushTup xs vs).length := by
        rw [pushTup_length xs vs, Nat.add_comm]
      have hll : ls.length + sig.length = (pushTup Js ls).length := by
        rw [pushTup_length Js ls, Nat.add_comm]
      rw [hlv, hll]
      exact ihb (Tup.levels sig ls.length) Js i (Tup.levels ts vs.length) xs
        (pushTup xs vs) (pushTup Js ls) (flatCtxMatch_pushTupV hvs xs)
        (flatCtxMatch_pushTupL hls Js)
    · have hll : ls.length + sig.length = (pushTup Js ls).length := by
        rw [pushTup_length Js ls, Nat.add_comm]
      rw [hll]
      exact ihk (Tup.levels sig ls.length) Js vs (pushTup Js ls) hvs (flatCtxMatch_pushTupL hls Js)

/-- Any well-formed closed function equals its own `Func.renorm`. -/
theorem Func.renorm_eq_self {as rs : List Ty} {f : Func as rs} (hf : f.Wf) :
    Func.renorm f = f := by
  funext V L xs
  have hwf := hf K V KL L (Tup.levels as 0) xs
  have hvs : FlatCtxMatch lookupV (Tup.zip (Tup.levels as 0) xs) (pushTup xs []) := by
    simpa [List.append_nil] using
      flatCtxMatch_pushTupV (V := V) (G := []) (vs := []) FlatCtxMatch.empty xs
  have hls : FlatCtxMatch lookupL ([] : Ctx KL L) [] := FlatCtxMatch.empty
  have hd := denote_toTFlat_eq hwf (pushTup xs []) [] hvs hls
  simpa [Func.renorm, denoteFunc, reifyFunc, pushTup_length] using hd

/-! ## `TFlat` → PHOAS → `TFlat` identity (`toTFlat_denote_eq`, `reifyFunc_denoteFunc_eq`) -/

/-- Level invariant on a `K`/`KL` context: index `i` holds de Bruijn level `vs.length - 1 - i`. -/
@[expose] def CtxLevels {α : Type} (vs : List ((a : α) × (fun _ => Nat) a)) : Prop :=
  ∀ i a lvl, listGet? vs i = some ⟨a, lvl⟩ → lvl = vs.length - 1 - i

theorem CtxLevels.nil {α : Type} : CtxLevels (α := α) [] :=
  fun _ _ _ h => nomatch h

theorem CtxLevels.cons {α : Type} {vs : List ((a : α) × (fun _ => Nat) a)}
    (h : CtxLevels vs) (a : α) :
    CtxLevels (⟨a, vs.length⟩ :: vs) := by
  intro i a' lvl hget
  cases i with
  | zero =>
    dsimp only [listGet?] at hget
    cases hget
    simp [List.length_cons]
  | succ i' =>
    dsimp only [listGet?] at hget
    have hl := h i' a' lvl hget
    simp only [List.length_cons, Nat.add_sub_cancel]
    rw [hl, Nat.sub_sub, Nat.add_comm 1 i', ← Nat.sub_sub]

theorem CtxLevels.pushTup {α : Type} :
    {ts : List α} → {vs : List ((a : α) × (fun _ => Nat) a)} →
    CtxLevels vs → CtxLevels (pushTup (Tup.levels ts vs.length) vs)
  | [], _, h => h
  | a :: _, vs, h => CtxLevels.pushTup (vs := ⟨a, vs.length⟩ :: vs) (h.cons a)

theorem ctxTypes_listGet? {α : Type} {f : α → Type} :
    {Γ : List α} → {vs : List ((a : α) × f a)} → CtxTypes Γ vs →
    ∀ {i : Nat} {a : α}, listGet? Γ i = some a →
    ∃ v : f a, listGet? vs i = some ⟨a, v⟩ ∧ i < vs.length
  | [], [], .nil, _, _, h => nomatch h
  | a :: _, ⟨_, v⟩ :: vs, .cons _, 0, _, h => by
    dsimp only [listGet?] at h; cases h
    exact ⟨v, rfl, Nat.zero_lt_succ _⟩
  | _ :: _, _ :: _, .cons hrest, i + 1, _, h => by
    obtain ⟨v, hg, hlt⟩ := ctxTypes_listGet? hrest h
    exact ⟨v, hg, Nat.succ_lt_succ hlt⟩

theorem checkArg_eq_true_iff {Γ : List Ty} {t : Ty} {idx : Nat} :
    checkArg Γ t (.var idx) = true ↔ listGet? Γ idx = some t := by
  dsimp only [checkArg]
  cases h : listGet? Γ idx with
  | none => simp
  | some t' =>
    cases hdec : tyDecEq t' t with
    | isFalse hne => simp [hdec]; exact hne
    | isTrue heq => subst heq; simp [hdec]

theorem checkJump_eq_true_iff {Δ : List (List Ty)} {ts : List Ty} {j : Nat} :
    (match listGet? Δ j with
     | some ts' => match listTyDecEq ts' ts with | isTrue _ => true | isFalse _ => false
     | none => false) = true ↔ listGet? Δ j = some ts := by
  cases h : listGet? Δ j with
  | none => simp
  | some ts' =>
    cases hdec : listTyDecEq ts' ts with
    | isFalse hne => simp [hdec]; exact hne
    | isTrue heq => subst heq; simp [hdec]

private theorem denoteArg_idxArg_inv {Γ : List Ty} {vs : List ((t : Ty) × K t)}
    (hΓ : CtxTypes Γ vs) (hvl : CtxLevels vs) {t : Ty} (a : Arg K t)
    (hc : checkArg Γ t a = true) :
    ∃ a', denoteArg vs a = some a' ∧ idxArg vs.length a' = a := by
  cases a with
  | imm c => exact ⟨.imm c, rfl, rfl⟩
  | var idx =>
    dsimp only [K] at idx
    have hgetΓ := checkArg_eq_true_iff.mp hc
    obtain ⟨lvl, hgetvs, hlt⟩ := ctxTypes_listGet? hΓ hgetΓ
    dsimp only [K] at lvl
    have hlvl : lvl = vs.length - 1 - idx := hvl idx t lvl hgetvs
    have hden : denoteArg vs (.var (t := t) idx) = some (.var (t := t) lvl) := by
      dsimp only [denoteArg, lookupV]
      rw [hgetvs]; dsimp only
      rw [PassFlatKit.castTy_self]
    refine ⟨.var lvl, hden, ?_⟩
    subst hlvl
    have hlt' : vs.length - 1 - idx < vs.length := by omega
    have hinv : vs.length - 1 - (vs.length - 1 - idx) = idx := by omega
    simp [idxArg, hlt', hinv]

private theorem denoteArgs_idxArgs_inv {Γ : List Ty} {vs : List ((t : Ty) × K t)}
    (hΓ : CtxTypes Γ vs) (hvl : CtxLevels vs) :
    {ts : List Ty} → (as : Tup (Arg K) ts) → checkArgs Γ as = true →
    ∃ as', denoteArgs vs as = some as' ∧ idxArgs vs.length as' = as
  | [], (), _ => ⟨(), rfl, rfl⟩
  | _ :: _, (a, as), hc => by
    dsimp only [checkArgs] at hc; simp only [Bool.and_eq_true] at hc
    obtain ⟨a', ha, hia⟩ := denoteArg_idxArg_inv hΓ hvl a hc.1
    obtain ⟨as', has, hias⟩ := denoteArgs_idxArgs_inv hΓ hvl as hc.2
    exact ⟨(a', as'), by dsimp only [denoteArgs]; rw [ha, has], by
      dsimp only [idxArgs]; rw [hia, hias]⟩

mutual
/-- Exact `TFlat`-to-PHOAS-to-`TFlat` round-trip identity under `wfCheck = true`. -/
theorem toTFlat_denote_eq {rs : List Ty} :
    (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × K t)} → {ls : List ((ts : List Ty) × KL ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels vs → CtxLevels ls →
    tf.wfCheck Γ Δ = true →
    toTFlat (denote K KL tf vs ls) vs.length ls.length = tf
  | .let_ (ts := ts) ⟨code, args⟩ k, Γ, Δ, vs, ls, hΓ, hΔ, hvl, hll, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨args', hda, hidx⟩ := denoteArgs_idxArgs_inv hΓ hvl args hwf.1
    dsimp only [denote]; rw [hda]; dsimp only [toTFlat]
    have hk := toTFlat_denote_eq k (CtxTypes.push (Tup.levels ts vs.length) hΓ) hΔ
      (hvl.pushTup) hll hwf.2
    rw [pushTup_length (Tup.levels ts vs.length) vs] at hk
    rw [hidx, hk]
  | .load t a k, Γ, Δ, vs, ls, hΓ, hΔ, hvl, hll, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨a', hda, hidx⟩ := denoteArg_idxArg_inv hΓ hvl a hwf.1
    dsimp only [denote]; rw [hda]; dsimp only [toTFlat]
    have hk := toTFlat_denote_eq k (.cons hΓ) hΔ (hvl.cons t) hll hwf.2
    rw [List.length_cons] at hk
    rw [hidx, hk]
  | .store v a k, Γ, Δ, vs, ls, hΓ, hΔ, hvl, hll, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨v', hdv, hidxv⟩ := denoteArg_idxArg_inv hΓ hvl v hwf.1.1
    obtain ⟨a', hda, hidxa⟩ := denoteArg_idxArg_inv hΓ hvl a hwf.1.2
    dsimp only [denote]; rw [hdv, hda]; dsimp only [toTFlat]
    rw [hidxv, hidxa, toTFlat_denote_eq k hΓ hΔ hvl hll hwf.2]
  | .call f bs args k, Γ, Δ, vs, ls, hΓ, hΔ, hvl, hll, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨args', hda, hidx⟩ := denoteArgs_idxArgs_inv hΓ hvl args hwf.1
    dsimp only [denote]; rw [hda]; dsimp only [toTFlat]
    have hk := toTFlat_denote_eq k (CtxTypes.push (Tup.levels bs vs.length) hΓ) hΔ
      (hvl.pushTup) hll hwf.2
    rw [pushTup_length (Tup.levels bs vs.length) vs] at hk
    rw [hidx, hk]
  | .jnz c t e, Γ, Δ, vs, ls, hΓ, hΔ, hvl, hll, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨c', hdc, hidx⟩ := denoteArg_idxArg_inv hΓ hvl c hwf.1.1
    dsimp only [denote]; rw [hdc]; dsimp only [toTFlat]
    rw [hidx, toTFlat_denote_eq t hΓ hΔ hvl hll hwf.1.2,
      toTFlat_denote_eq e hΓ hΔ hvl hll hwf.2]
  | .jump (ts := ts) j args, Γ, Δ, vs, ls, hΓ, hΔ, hvl, hll, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    have hgetΔ := checkJump_eq_true_iff.mp hwf.1
    obtain ⟨lvl, hgetls, hlt⟩ := ctxTypes_listGet? hΔ hgetΔ
    dsimp only [KL] at lvl
    have hlvl : lvl = ls.length - 1 - j := hll j ts lvl hgetls
    have hlk : lookupL ls ts j = some lvl := by
      dsimp only [lookupL]; rw [hgetls]; dsimp only; rw [PassFlatKit.castListTy_self]
    obtain ⟨args', hda, hidx⟩ := denoteArgs_idxArgs_inv hΓ hvl args hwf.2
    dsimp only [denote]; rw [hlk, hda]; dsimp only [toTFlat]
    subst hlvl
    have hlt' : ls.length - 1 - j < ls.length := by omega
    have hinv : ls.length - 1 - (ls.length - 1 - j) = j := by omega
    simp [hlt', hinv, hidx]
  | .ret vs', Γ, _, vs, _, hΓ, _, hvl, _, hwf => by
    obtain ⟨vs'', hdv, hidx⟩ := denoteArgs_idxArgs_inv hΓ hvl vs' hwf
    dsimp only [denote]; rw [hdv]; dsimp only [toTFlat]; rw [hidx]
  | .exit f args, Γ, _, vs, _, hΓ, _, hvl, _, hwf => by
    obtain ⟨args', hda, hidx⟩ := denoteArgs_idxArgs_inv hΓ hvl args hwf
    dsimp only [denote]; rw [hda]; dsimp only [toTFlat]; rw [hidx]
  | .hlt, _, _, _, _, _, _, _, _, _ => rfl
  | .group (sig := sig) bodies k, Γ, Δ, vs, ls, hΓ, hΔ, hvl, hll, hwf => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote, toTFlat]
    have hb := toTBlocks_denoteB_eq bodies hΓ (CtxTypes.push (Tup.levels sig ls.length) hΔ)
      hvl hll.pushTup hwf.1
    have hk := toTFlat_denote_eq k hΓ (CtxTypes.push (Tup.levels sig ls.length) hΔ)
      hvl hll.pushTup hwf.2
    rw [pushTup_length (Tup.levels sig ls.length) ls] at hb hk
    rw [hb, hk]

/-- Block-list companion of `toTFlat_denote_eq`. -/
theorem toTBlocks_denoteB_eq {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × K t)} → {ls : List ((ts : List Ty) × KL ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → CtxLevels vs → CtxLevels ls →
    tb.wfCheck Γ Δ = true →
    toTBlocks (denoteB K KL tb vs ls) vs.length ls.length = tb
  | _, .nil, _, _, _, _, _, _, _, _, _ => rfl
  | _, .cons (ts := ts) b bs, Γ, Δ, vs, ls, hΓ, hΔ, hvl, hll, hwf => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denoteB, toTBlocks]
    have hb := toTFlat_denote_eq b (CtxTypes.push (Tup.levels ts vs.length) hΓ) hΔ
      hvl.pushTup hll hwf.1
    rw [pushTup_length (Tup.levels ts vs.length) vs] at hb
    rw [hb, toTBlocks_denoteB_eq bs hΓ hΔ hvl hll hwf.2]
end

/-- Exact closed `TFlat`-to-`Func`-to-`TFlat` round-trip identity under `wfCheck = true`. -/
theorem reifyFunc_denoteFunc_eq {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    reifyFunc (denoteFunc (as := as) tf) = tf := by
  have hlen : (pushTup (Tup.levels as 0) []).length = as.length := by
    rw [pushTup_length]; simp
  have h := toTFlat_denote_eq tf (CtxTypes.push (Tup.levels as 0) .nil) .nil
    (CtxLevels.pushTup CtxLevels.nil) CtxLevels.nil hwf
  simpa [reifyFunc, denoteFunc, hlen] using h

/-- `Func.renorm (denoteFunc tf) = denoteFunc tf` under `wfCheck = true` (zero axioms!). -/
theorem Func.renorm_denoteFunc {as rs : List Ty} (tf : TFlat rs)
    (hwf : tf.wfCheck (pushTypes as []) [] = true) :
    Func.renorm (denoteFunc (as := as) tf) = denoteFunc (as := as) tf := by
  dsimp only [Func.renorm]
  rw [reifyFunc_denoteFunc_eq tf hwf]

/-! ## Shared `Trie` environment correspondence kits (`TrieCtxMatch`, `TrieProjMatch`) -/

/-- Insert a type-tagged tuple `xs` into a `Trie` keyed by increasing de Bruijn level starting
at `depth` (matching `pushTup` index layout). -/
@[expose] def insertTupTrie {α : Type} {f : α → Type} (depth : Nat)
    (env : Trie ((a : α) × f a)) : {ts : List α} → Tup f ts → Trie ((a : α) × f a)
  | [], () => env
  | a :: _, (x, xs) => insertTupTrie (depth + 1) (env.insert depth ⟨a, x⟩) xs

/-- Agreement between a de Bruijn level `Trie` environment of depth `depth` and a de Bruijn
index `List` context `vs` (`0` = newest element). -/
@[expose] def TrieCtxMatch {α : Type} {f : α → Type}
    (depth : Nat) (env : Trie ((a : α) × f a)) (vs : List ((a : α) × f a)) : Prop :=
  depth = vs.length ∧
    ∀ idx, idx < vs.length → env.find? (depth - 1 - idx) = listGet? vs idx

namespace TrieCtxMatch

theorem empty {α : Type} {f : α → Type} :
    TrieCtxMatch (α := α) (f := f) 0 .empty [] :=
  ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem cons {α : Type} {f : α → Type} {depth : Nat} {env : Trie ((a : α) × f a)}
    {vs : List ((a : α) × f a)} (h : TrieCtxMatch depth env vs) (a : α) (x : f a) :
    TrieCtxMatch (depth + 1) (env.insert depth ⟨a, x⟩) (⟨a, x⟩ :: vs) := by
  refine ⟨by rw [h.1, List.length_cons], fun idx hidx => ?_⟩
  cases idx with
  | zero =>
    have hkey : depth + 1 - 1 - 0 = depth := by omega
    rw [hkey, Trie.find?_insert_self]
    rfl
  | succ i =>
    simp only [List.length_cons, Nat.succ_lt_succ_iff] at hidx
    have hkey : depth + 1 - 1 - (i + 1) = depth - 1 - i := by omega
    have hne : depth - 1 - i ≠ depth := by have := h.1; omega
    rw [hkey, Trie.find?_insert_ne _ _ hne]
    exact h.2 i hidx

theorem pushTup {α : Type} {f : α → Type} :
    {ts : List α} → (xs : Tup f ts) → {depth : Nat} →
    {env : Trie ((a : α) × f a)} → {vs : List ((a : α) × f a)} →
    TrieCtxMatch depth env vs →
    TrieCtxMatch (depth + ts.length) (insertTupTrie depth env xs) (LeanQbe.T.pushTup xs vs)
  | [], (), _, _, _, h => h
  | a :: ts, (x, xs), depth, env, vs, h => by
    dsimp only [insertTupTrie, LeanQbe.T.pushTup]
    have h1 := TrieCtxMatch.pushTup xs (h.cons a x)
    have hlen : depth + (a :: ts).length = depth + 1 + ts.length := by
      simp only [List.length_cons]; omega
    rwa [hlen]

theorem lookupV_eq {Γ : List Ty} {f : Ty → Type} {depth : Nat}
    {env : Trie ((t : Ty) × f t)} {vs : List ((t : Ty) × f t)}
    (hΓ : CtxTypes Γ vs) (hm : TrieCtxMatch depth env vs) {t : Ty} {idx : Nat}
    (hc : checkArg Γ t (.var idx) = true) :
    (match env.find? (depth - 1 - idx) with
     | some ⟨t', v⟩ => castTy t' t v
     | none => none) = lookupV vs t idx := by
  obtain ⟨_, hgetvs, hlt⟩ := ctxTypes_listGet? hΓ (checkArg_eq_true_iff.mp hc)
  rw [hm.2 idx hlt]
  rfl

end TrieCtxMatch

/-- Projected variant of `TrieCtxMatch` for unboxed `Trie β` payloads (such as `Trie Nat` in
`RegaFlat`), storing `proj a x` at level `depth`. -/
@[expose] def TrieProjMatch {α : Type} {f : α → Type} {β : Type} (proj : (a : α) → f a → β)
    (depth : Nat) (env : Trie β) (vs : List ((a : α) × f a)) : Prop :=
  depth = vs.length ∧
    ∀ idx, idx < vs.length →
      env.find? (depth - 1 - idx) = (listGet? vs idx).map (fun p => proj p.1 p.2)

namespace TrieProjMatch

theorem empty {α : Type} {f : α → Type} {β : Type} (proj : (a : α) → f a → β) :
    TrieProjMatch proj 0 .empty ([] : List ((a : α) × f a)) :=
  ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem cons {α : Type} {f : α → Type} {β : Type} {proj : (a : α) → f a → β}
    {depth : Nat} {env : Trie β} {vs : List ((a : α) × f a)}
    (h : TrieProjMatch proj depth env vs) (a : α) (x : f a) :
    TrieProjMatch proj (depth + 1) (env.insert depth (proj a x)) (⟨a, x⟩ :: vs) := by
  refine ⟨by rw [h.1, List.length_cons], fun idx hidx => ?_⟩
  cases idx with
  | zero =>
    have hkey : depth + 1 - 1 - 0 = depth := by omega
    rw [hkey, Trie.find?_insert_self]
    rfl
  | succ i =>
    simp only [List.length_cons, Nat.succ_lt_succ_iff] at hidx
    have hkey : depth + 1 - 1 - (i + 1) = depth - 1 - i := by omega
    have hne : depth - 1 - i ≠ depth := by have := h.1; omega
    rw [hkey, Trie.find?_insert_ne _ _ hne]
    exact h.2 i hidx

theorem find?_var_eq {α : Type} {Γ : List α} {f : α → Type} {β : Type} {proj : (a : α) → f a → β}
    {depth : Nat} {env : Trie β} {vs : List ((a : α) × f a)}
    (hΓ : CtxTypes Γ vs) (hm : TrieProjMatch proj depth env vs) {a : α} {idx : Nat}
    (hget : listGet? Γ idx = some a) :
    ∃ x : f a, listGet? vs idx = some ⟨a, x⟩ ∧ env.find? (depth - 1 - idx) = some (proj a x) := by
  obtain ⟨x, hgetvs, hlt⟩ := ctxTypes_listGet? hΓ hget
  refine ⟨x, hgetvs, ?_⟩
  rw [hm.2 idx hlt, hgetvs]
  rfl

end TrieProjMatch

/-! ## `TFlat.ext_eq_fn_ext` and `TFlatFn.supportsSource_eq` -/

private theorem lookupV_unit_isSome {Γ : List Ty}
    {vs : List ((t : Ty) × (fun _ => Unit) t)}
    (hΓ : CtxTypes Γ vs) {t : Ty} {idx : Nat} (hc : checkArg Γ t (.var idx) = true) :
    lookupV vs t idx = some () := by
  obtain ⟨u, hget, _⟩ := ctxTypes_listGet? hΓ (checkArg_eq_true_iff.mp hc)
  cases u
  dsimp only [lookupV]; rw [hget]; dsimp only; rw [PassFlatKit.castTy_self]

mutual
theorem exprExtAux_denote_eq {rs : List Ty} :
    (tf : TFlat rs) → {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × (fun _ => Unit) t)} →
    {ls : List ((ts : List Ty) × (fun _ => Unit) ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → tf.wfCheck Γ Δ = true →
    ∀ cs xs,
      Expr.extAux (denote (fun _ => Unit) (fun _ => Unit) tf vs ls) cs xs = tf.extAux cs xs
  | .let_ op k, _, _, vs, ls, hΓ, hΔ, hwf, cs, xs => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.1)
    dsimp only [denote]; rw [ha]; dsimp only [Expr.extAux, TFlat.extAux]
    exact exprExtAux_denote_eq k (CtxTypes.push (Tup.units _) hΓ) hΔ hwf.2 cs xs
  | .load t a k, _, _, vs, ls, hΓ, hΔ, hwf, cs, xs => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨a', ha⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1)
    dsimp only [denote]; rw [ha]; dsimp only [Expr.extAux, TFlat.extAux]
    exact exprExtAux_denote_eq k (.cons hΓ) hΔ hwf.2 cs xs
  | .store v a k, _, _, vs, ls, hΓ, hΔ, hwf, cs, xs => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨v', hv⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.1)
    obtain ⟨a', ha⟩ := Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.2)
    dsimp only [denote]; rw [hv, ha]; dsimp only [Expr.extAux, TFlat.extAux]
    exact exprExtAux_denote_eq k hΓ hΔ hwf.2 cs xs
  | .call f bs args k, _, _, vs, ls, hΓ, hΔ, hwf, cs, xs => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.1)
    dsimp only [denote]; rw [ha]; dsimp only [Expr.extAux, TFlat.extAux]
    exact exprExtAux_denote_eq k (CtxTypes.push (Tup.units bs) hΓ) hΔ hwf.2 _ xs
  | .jnz c t e, _, _, vs, ls, hΓ, hΔ, hwf, cs, xs => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    cases c with
    | imm b =>
      dsimp only [denote, denoteArg, Expr.extAux, TFlat.extAux]
      cases b with
      | true => exact exprExtAux_denote_eq t hΓ hΔ hwf.1.2 cs xs
      | false => exact exprExtAux_denote_eq e hΓ hΔ hwf.2 cs xs
    | var i =>
      dsimp only [denote, denoteArg]
      rw [lookupV_unit_isSome hΓ hwf.1.1]
      dsimp only [Expr.extAux, TFlat.extAux]
      have he := exprExtAux_denote_eq e hΓ hΔ hwf.2 cs xs
      rw [he]
      exact exprExtAux_denote_eq t hΓ hΔ hwf.1.2 _ _
  | .jump (ts := ts) j args, _, _, vs, ls, hΓ, hΔ, hwf, cs, xs => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    obtain ⟨j', hj⟩ := Option.isSome_iff_exists.1 (lookupL_isSome_of_check hΔ hwf.1)
    obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.2)
    dsimp only [denote]; rw [hj, ha]; rfl
  | .ret vs', _, _, vs, _, hΓ, _, hwf, cs, xs => by
    obtain ⟨vs'', hv⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf)
    dsimp only [denote]; rw [hv]; rfl
  | .exit f args, _, _, vs, _, hΓ, _, hwf, cs, xs => by
    obtain ⟨args', ha⟩ := Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf)
    dsimp only [denote]; rw [ha]; rfl
  | .hlt, _, _, _, _, _, _, _, _, _ => rfl
  | .group (sig := sig) bodies k, Γ, Δ, vs, ls, hΓ, hΔ, hwf, cs, xs => by
    dsimp only [TFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denote, Expr.extAux, TFlat.extAux]
    have hk := exprExtAux_denote_eq k hΓ (CtxTypes.push (Tup.units sig) hΔ) hwf.2 cs xs
    rw [hk]
    exact blocksExtAux_denoteB_eq bodies hΓ (CtxTypes.push (Tup.units sig) hΔ) hwf.1 _ _

/-- Block-list companion of `exprExtAux_denote_eq`. -/
theorem blocksExtAux_denoteB_eq {rs : List Ty} :
    {sig : List (List Ty)} → (tb : TBlocks rs sig) →
    {Γ : List Ty} → {Δ : List (List Ty)} →
    {vs : List ((t : Ty) × (fun _ => Unit) t)} →
    {ls : List ((ts : List Ty) × (fun _ => Unit) ts)} →
    CtxTypes Γ vs → CtxTypes Δ ls → tb.wfCheck Γ Δ = true →
    ∀ cs xs,
      Blocks.extAux (denoteB (fun _ => Unit) (fun _ => Unit) tb vs ls) cs xs = tb.extAux cs xs
  | _, .nil, _, _, _, _, _, _, _, _, _ => rfl
  | _, .cons (ts := ts) b bs, Γ, Δ, vs, ls, hΓ, hΔ, hwf, cs, xs => by
    dsimp only [TBlocks.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
    dsimp only [denoteB, Blocks.extAux, TBlocks.extAux]
    have hb := exprExtAux_denote_eq b (CtxTypes.push (Tup.units ts) hΓ) hΔ hwf.1 cs xs
    rw [hb]
    exact blocksExtAux_denoteB_eq bs hΓ hΔ hwf.2 _ _
end

/-- `TFlat.ext f.body` equals `Fn.ext f.toFn` whenever `f.wfCheck = true`. -/
theorem TFlat.ext_eq_fn_ext (f : TFlatFn) (hwf : f.wfCheck = true) :
    TFlat.ext f.body = Fn.ext f.toFn := by
  dsimp only [TFlat.ext, Fn.ext, TFlatFn.toFn, denoteFunc]
  have h := exprExtAux_denote_eq f.body (CtxTypes.push (Tup.units f.as) .nil) .nil hwf [] []
  rw [h]

/-- `f.toFn.body.supportsSource lt` equals `f.supportsSource lt` whenever `f.wfCheck = true`. -/
theorem TFlatFn.supportsSource_eq (lt : LegalTarget) (f : TFlatFn)
    (hwf : f.wfCheck = true) :
    f.toFn.body.supportsSource lt = f.supportsSource lt := by
  have h := reifyFunc_denoteFunc_eq (as := f.as) f.body hwf
  dsimp only [reifyFunc, denoteFunc] at h
  dsimp only [Func.supportsSource, TFlatFn.supportsSource, TFlatFn.toFn, denoteFunc]
  rw [h]

end LeanQbe.T
