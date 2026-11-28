module

public import LeanQbe.T.Bedrock2.Phoas
public import LeanQbe.T.Flat
public import LeanQbe.T.FlatDirectLemmas
public import LeanQbe.T.FlatLemmas

/-!
# First-Order De Bruijn Mirror (`BFlat`) and `FlatLemmas` Triad

Promotes the first-order de Bruijn mirror of structured Bedrock2 (`BFlat rs`),
reusing `LeanQbe.T.K`, `idxArg`/`idxArgs`, `pushTup`/`pushTypes`, `lookupV`,
`denoteArg`/`denoteArgs`, `checkArg`/`checkArgs`, `CtxRel`, `CtxTypes`, `FlatCtxMatch`,
and `t_kernel_rfl`:

1. `toBFlat` / `BFlat.denote` / `BFlat.wfCheck` / `BFlat.noHlt` / `BFlat.wp`
2. `BFlat.denote_wf` & `BFlat.denote_noHlt_of_wfCheck`
3. `FuncB.wf_of_denote` / `FuncB.wf_of_reify` / `t_b2_wf_reify`
4. `BFlat.wp_iff_denote_wp` / `BFlat.denote_wp_iff` / `FuncB.renorm_wp_iff` / `FuncB.reify_wp_iff`
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Bedrock2

open LeanQbe.T
open Kraken.Bedrock2 (anybytes split)

/-- Typed first-order de Bruijn mirror of `Cmd` over `LeanQbe.T.K` (`0` = newest binder). -/
inductive BFlat : List Ty → Type
  | ret {rs : List Ty} (vs : Tup (Arg K) rs) : BFlat rs
  | let_ {rs ts : List Ty} (op : Op K ts) (k : BFlat rs) : BFlat rs
  | load {rs : List Ty} (t : Ty) (a : Arg K i64) (k : BFlat rs) : BFlat rs
  | store {rs : List Ty} {t : Ty} (v : Arg K t) (a : Arg K i64) (k : BFlat rs) : BFlat rs
  | call {rs : List Ty} (f : Sym) {as : List Ty} (bs : List Ty)
      (args : Tup (Arg K) as) (k : BFlat rs) : BFlat rs
  | interact {rs : List Ty} (action : Sym) {as : List Ty} (bs : List Ty)
      (args : Tup (Arg K) as) (k : BFlat rs) : BFlat rs
  | stackalloc {rs : List Ty} (nbytes : Nat) (body : BFlat rs) : BFlat rs
  | seq {rs : List Ty} (mid : List Ty) (c₁ : BFlat mid) (c₂ : BFlat rs) : BFlat rs
  | cond {rs : List Ty} (c : Arg K .bool) (t e : BFlat rs) : BFlat rs
  | while_ {rs : List Ty} (st : List Ty) (init : Tup (Arg K) st) (test : BFlat [.bool])
      (body : BFlat st) (k : BFlat rs) : BFlat rs
  | hlt {rs : List Ty} : BFlat rs

/-- Total reification of `Cmd K rs` into `BFlat rs` at value depth `nv`. -/
def toBFlat : {rs : List Ty} → Cmd K rs → Nat → BFlat rs
  | _, .ret vs, nv => .ret (idxArgs nv vs)
  | _, .let_ (ts := ts) op k, nv =>
      .let_ ⟨op.code, idxArgs nv op.args⟩ (toBFlat (k (Tup.levels ts nv)) (nv + ts.length))
  | _, .load t a k, nv => .load t (idxArg nv a) (toBFlat (k nv) (nv + 1))
  | _, .store v a k, nv => .store (idxArg nv v) (idxArg nv a) (toBFlat k nv)
  | _, .call f (bs := bs) args k, nv =>
      .call f bs (idxArgs nv args) (toBFlat (k (Tup.levels bs nv)) (nv + bs.length))
  | _, .interact action (bs := bs) args k, nv =>
      .interact action bs (idxArgs nv args) (toBFlat (k (Tup.levels bs nv)) (nv + bs.length))
  | _, .stackalloc nbytes body, nv =>
      .stackalloc nbytes (toBFlat (body nv) (nv + 1))
  | _, .seq (mid := mid) c₁ c₂, nv =>
      .seq mid (toBFlat c₁ nv) (toBFlat (c₂ (Tup.levels mid nv)) (nv + mid.length))
  | _, .cond c t e, nv => .cond (idxArg nv c) (toBFlat t nv) (toBFlat e nv)
  | _, .while_ (st := st) init test body k, nv =>
      let lvls := Tup.levels st nv
      let nv' := nv + st.length
      .while_ st (idxArgs nv init) (toBFlat (test lvls) nv')
        (toBFlat (body lvls) nv') (toBFlat (k lvls) nv')
  | _, .hlt, _ => .hlt

/-- Denote `BFlat rs` back into `Cmd V rs`; out-of-scope or mistyped indices map to `.hlt`. -/
def BFlat.denote (V : Ty → Type) :
    {rs : List Ty} → BFlat rs → List ((t : Ty) × V t) → Cmd V rs
  | _, .ret vs', vs =>
      match denoteArgs vs vs' with
      | some vs'' => .ret vs''
      | none => .hlt
  | _, .let_ op k, vs =>
      match denoteArgs vs op.args with
      | some args' => .let_ ⟨op.code, args'⟩ fun xs => k.denote V (pushTup xs vs)
      | none => .hlt
  | _, .load t a k, vs =>
      match denoteArg vs a with
      | some a' => .load t a' fun v => k.denote V (⟨t, v⟩ :: vs)
      | none => .hlt
  | _, .store v a k, vs =>
      match denoteArg vs v, denoteArg vs a with
      | some v', some a' => .store v' a' (k.denote V vs)
      | _, _ => .hlt
  | _, .call f bs args k, vs =>
      match denoteArgs vs args with
      | some args' => .call f (bs := bs) args' fun xs => k.denote V (pushTup xs vs)
      | none => .hlt
  | _, .interact action bs args k, vs =>
      match denoteArgs vs args with
      | some args' => .interact action (bs := bs) args' fun xs => k.denote V (pushTup xs vs)
      | none => .hlt
  | _, .stackalloc nbytes body, vs =>
      .stackalloc nbytes fun a => body.denote V (⟨i64, a⟩ :: vs)
  | _, .seq _ c₁ c₂, vs =>
      .seq (c₁.denote V vs) fun xs => c₂.denote V (pushTup xs vs)
  | _, .cond c t e, vs =>
      match denoteArg vs c with
      | some c' => .cond c' (t.denote V vs) (e.denote V vs)
      | none => .hlt
  | _, .while_ _ init test body k, vs =>
      match denoteArgs vs init with
      | some init' =>
          .while_ init'
            (fun xs => test.denote V (pushTup xs vs))
            (fun xs => body.denote V (pushTup xs vs))
            (fun xs => k.denote V (pushTup xs vs))
      | none => .hlt
  | _, .hlt, _ => .hlt

/-- Total computable scope/type checker for `BFlat rs` under value type context `Γ`. -/
def BFlat.wfCheck : {rs : List Ty} → BFlat rs → List Ty → Bool
  | _, .ret vs, Γ => checkArgs Γ vs
  | _, .let_ (ts := ts) op k, Γ => checkArgs Γ op.args && k.wfCheck (pushTypes ts Γ)
  | _, .load t a k, Γ => checkArg Γ i64 a && k.wfCheck (t :: Γ)
  | _, .store (t := t) v a k, Γ => checkArg Γ t v && checkArg Γ i64 a && k.wfCheck Γ
  | _, .call _ bs args k, Γ => checkArgs Γ args && k.wfCheck (pushTypes bs Γ)
  | _, .interact _ bs args k, Γ => checkArgs Γ args && k.wfCheck (pushTypes bs Γ)
  | _, .stackalloc _ body, Γ => body.wfCheck (i64 :: Γ)
  | _, .seq mid c₁ c₂, Γ => c₁.wfCheck Γ && c₂.wfCheck (pushTypes mid Γ)
  | _, .cond c t e, Γ => checkArg Γ .bool c && t.wfCheck Γ && e.wfCheck Γ
  | _, .while_ st init test body k, Γ =>
      let Γ' := pushTypes st Γ
      checkArgs Γ init && test.wfCheck Γ' && body.wfCheck Γ' && k.wfCheck Γ'
  | _, .hlt, _ => true

/-- True iff `BFlat rs` contains no explicit `.hlt` node. -/
def BFlat.noHlt : {rs : List Ty} → BFlat rs → Bool
  | _, .ret _ => true
  | _, .let_ _ k => k.noHlt
  | _, .load _ _ k => k.noHlt
  | _, .store _ _ k => k.noHlt
  | _, .call _ _ _ k => k.noHlt
  | _, .interact _ _ _ k => k.noHlt
  | _, .stackalloc _ body => body.noHlt
  | _, .seq _ c₁ c₂ => c₁.noHlt && c₂.noHlt
  | _, .cond _ t e => t.noHlt && e.noHlt
  | _, .while_ _ _ test body k => test.noHlt && body.noHlt && k.noHlt
  | _, .hlt => false

/-- Reify a closed `FuncB as rs` into its first-order de Bruijn `BFlat rs`. -/
def reifyFuncB {as rs : List Ty} (f : FuncB as rs) : BFlat rs :=
  toBFlat (f K (Tup.levels as 0)) as.length

/-- Denote a `BFlat rs` back into a closed PHOAS `FuncB as rs`. -/
def denoteFuncB {as rs : List Ty} (bf : BFlat rs) : FuncB as rs :=
  fun V xs => bf.denote V (pushTup xs [])

/-- Reification-denotation round-trip flattening nested PHOAS closures. -/
def FuncB.renorm {as rs : List Ty} (f : FuncB as rs) : FuncB as rs :=
  denoteFuncB (reifyFuncB f)

/-- Total computable scope/type check of `reifyFuncB f`. -/
def FuncB.checkBFlat {as rs : List Ty} (f : FuncB as rs) : Bool :=
  (reifyFuncB f).wfCheck (pushTypes as [])

/-! ### Direct first-order `BFlat.wp` -/

/-- Direct first-order weakest precondition on `BFlat rs` over concrete de Bruijn env `vs`. -/
def BFlat.wp (ext : ExtSpecB) (Γ : EnvB) :
    {rs : List Ty} → Nat → PostB rs → BFlat rs → List ((t : Ty) × Val t) →
    TraceB → Mem 64 → Prop
  | _, _, Q, .ret vs', vs, t, m =>
      match denoteArgs vs vs' with
      | some vs'' => Q (vals vs'') t m
      | none => False
  | _, B, Q, .let_ op k, vs, t, m =>
      match denoteArgs vs op.args with
      | some args' =>
          (⟨op.code, args'⟩ : Op Val _).wp (fun r => k.wp ext Γ B Q (pushTup r vs) t m)
      | none => False
  | _, B, Q, .load ty a k, vs, t, m =>
      match denoteArg vs a with
      | some a' => ∃ v, loadVal m ty a'.val = some v ∧ k.wp ext Γ B Q (⟨ty, v⟩ :: vs) t m
      | none => False
  | _, B, Q, .store (t := ty) v a k, vs, t, m =>
      match denoteArg vs v, denoteArg vs a with
      | some v', some a' =>
          storeOk m ty a'.val ∧ k.wp ext Γ B Q vs t (storeMem m ty a'.val v'.val)
      | _, _ => False
  | _, B, Q, .call f (as := as) bs args k, vs, t, m =>
      match denoteArgs vs args with
      | some args' =>
          ∃ (P : PostB bs), Γ f as bs B (vals args') t m P ∧
            ∀ r t' m', P r t' m' → k.wp ext Γ B Q (pushTup r vs) t' m'
      | none => False
  | _, B, Q, .interact action (as := as) bs args k, vs, t, m =>
      match denoteArgs vs args with
      | some args' =>
          ∃ (mKeep mGive : Mem 64) (mid : Mem 64 → Tup Val bs → Prop),
            split m mKeep mGive ∧
            ext t mGive action as bs (vals args') mid ∧
            ∀ mReceive res, mid mReceive res →
              ∀ m', split m' mKeep mReceive →
                k.wp ext Γ B Q (pushTup res vs)
                  (⟨as, bs, mGive, action, vals args', mReceive, res⟩ :: t) m'
      | none => False
  | _, B, Q, .stackalloc nbytes body, vs, t, mSmall =>
      nbytes ≤ B ∧
      ∀ (a : BitVec 64) (mStack mCombined : Mem 64),
        anybytes a nbytes mStack → split mCombined mSmall mStack →
        body.wp ext Γ (B - nbytes)
          (fun res t' mCombined' =>
            ∃ mSmall' mStack', anybytes a nbytes mStack' ∧
              split mCombined' mSmall' mStack' ∧ Q res t' mSmall')
          (⟨i64, a⟩ :: vs) t mCombined
  | _, B, Q, .seq _ c₁ c₂, vs, t, m =>
      c₁.wp ext Γ B (fun mid t' m' => c₂.wp ext Γ B Q (pushTup mid vs) t' m') vs t m
  | _, B, Q, .cond c tBr eBr, vs, t, m =>
      match denoteArg vs c with
      | some c' =>
          (c'.val = true → tBr.wp ext Γ B Q vs t m) ∧
          (c'.val = false → eBr.wp ext Γ B Q vs t m)
      | none => False
  | _, B, Q, .while_ st init test body k, vs, t, m =>
      match denoteArgs vs init with
      | some init' =>
          ∀ (I : Tup Val st → TraceB → Mem 64 → Prop),
            (∀ s t' m',
              BFlat.wp ext Γ (rs := [.bool]) B
                (fun (b, ()) t₁ m₁ =>
                  (b = true → body.wp ext Γ B I (pushTup s vs) t₁ m₁) ∧
                  (b = false → k.wp ext Γ B Q (pushTup s vs) t₁ m₁))
                test (pushTup s vs) t' m' →
              I s t' m') →
            I (vals init') t m
      | none => False
  | _, _, _, .hlt, _, _, _ => False

/-! ### `FlatLemmas` Triad: `(a) denote_wf`, `(b) wf_of_reify`, `(c) denote_wp_iff` -/

/-- (a) Every denotation of a `BFlat` across related contexts is `Cmd.Wf`-related. -/
theorem BFlat.denote_wf {V₁ V₂ : Ty → Type} :
    {rs : List Ty} → (bf : BFlat rs) → {G : Ctx V₁ V₂} →
    {vs₁ : List ((t : Ty) × V₁ t)} → {vs₂ : List ((t : Ty) × V₂ t)} →
    CtxRel G vs₁ vs₂ → Cmd.Wf G (bf.denote V₁ vs₁) (bf.denote V₂ vs₂)
  | _, .ret vs', _, vs₁, vs₂, hvs => by
      have hr := denoteArgs_rel hvs vs'
      dsimp only [BFlat.denote]
      cases e₁ : denoteArgs vs₁ vs' <;> cases e₂ : denoteArgs vs₂ vs' <;>
        rw [e₁, e₂] at hr <;> dsimp only [ORel] at hr ⊢
      · exact .hlt
      · exact .ret hr
  | _, .let_ op k, _, vs₁, vs₂, hvs => by
      have hr := denoteArgs_rel hvs op.args
      dsimp only [BFlat.denote]
      cases e₁ : denoteArgs vs₁ op.args <;> cases e₂ : denoteArgs vs₂ op.args <;>
        rw [e₁, e₂] at hr <;> dsimp only [ORel] at hr ⊢
      · exact .hlt
      · exact .let_ (.mk op.code hr) fun xs₁ xs₂ =>
          BFlat.denote_wf k (ctxRel_pushTup xs₁ xs₂ hvs)
  | _, .load t a k, _, vs₁, vs₂, hvs => by
      have hr := denoteArg_rel hvs a
      dsimp only [BFlat.denote]
      cases e₁ : denoteArg vs₁ a <;> cases e₂ : denoteArg vs₂ a <;>
        rw [e₁, e₂] at hr <;> dsimp only [ORel] at hr ⊢
      · exact .hlt
      · exact .load t hr fun v₁ v₂ =>
          BFlat.denote_wf k
            (.cons List.mem_cons_self (hvs.mono fun _ hp => List.mem_cons_of_mem _ hp))
  | _, .store v a k, _, vs₁, vs₂, hvs => by
      have hv := denoteArg_rel hvs v
      have ha := denoteArg_rel hvs a
      dsimp only [BFlat.denote]
      cases e₁ : denoteArg vs₁ v <;> cases e₂ : denoteArg vs₂ v <;> rw [e₁, e₂] at hv <;>
        dsimp only [ORel] at hv ⊢ <;>
        cases f₁ : denoteArg vs₁ a <;> cases f₂ : denoteArg vs₂ a <;> rw [f₁, f₂] at ha <;>
        dsimp only [ORel] at ha ⊢ <;>
        first | exact .hlt | exact .store hv ha (BFlat.denote_wf k hvs)
  | _, .call f _ args k, _, vs₁, vs₂, hvs => by
      have hr := denoteArgs_rel hvs args
      dsimp only [BFlat.denote]
      cases e₁ : denoteArgs vs₁ args <;> cases e₂ : denoteArgs vs₂ args <;>
        rw [e₁, e₂] at hr <;> dsimp only [ORel] at hr ⊢
      · exact .hlt
      · exact .call f hr fun xs₁ xs₂ => BFlat.denote_wf k (ctxRel_pushTup xs₁ xs₂ hvs)
  | _, .interact act _ args k, _, vs₁, vs₂, hvs => by
      have hr := denoteArgs_rel hvs args
      dsimp only [BFlat.denote]
      cases e₁ : denoteArgs vs₁ args <;> cases e₂ : denoteArgs vs₂ args <;>
        rw [e₁, e₂] at hr <;> dsimp only [ORel] at hr ⊢
      · exact .hlt
      · exact .interact act hr fun xs₁ xs₂ => BFlat.denote_wf k (ctxRel_pushTup xs₁ xs₂ hvs)
  | _, .stackalloc nbytes body, _, _, _, hvs =>
      .stackalloc nbytes fun a₁ a₂ =>
        BFlat.denote_wf body
          (.cons List.mem_cons_self (hvs.mono fun _ hp => List.mem_cons_of_mem _ hp))
  | _, .seq _ c₁ c₂, _, _, _, hvs =>
      .seq (BFlat.denote_wf c₁ hvs) fun xs₁ xs₂ =>
        BFlat.denote_wf c₂ (ctxRel_pushTup xs₁ xs₂ hvs)
  | _, .cond c t e, _, vs₁, vs₂, hvs => by
      have hr := denoteArg_rel hvs c
      dsimp only [BFlat.denote]
      cases e₁ : denoteArg vs₁ c <;> cases e₂ : denoteArg vs₂ c <;>
        rw [e₁, e₂] at hr <;> dsimp only [ORel] at hr ⊢
      · exact .hlt
      · exact .cond hr (BFlat.denote_wf t hvs) (BFlat.denote_wf e hvs)
  | _, .while_ _ init test body k, _, vs₁, vs₂, hvs => by
      have hr := denoteArgs_rel hvs init
      dsimp only [BFlat.denote]
      cases e₁ : denoteArgs vs₁ init <;> cases e₂ : denoteArgs vs₂ init <;>
        rw [e₁, e₂] at hr <;> dsimp only [ORel] at hr ⊢
      · exact .hlt
      · exact .while_ hr
          (fun xs₁ xs₂ => BFlat.denote_wf test (ctxRel_pushTup xs₁ xs₂ hvs))
          (fun xs₁ xs₂ => BFlat.denote_wf body (ctxRel_pushTup xs₁ xs₂ hvs))
          (fun xs₁ xs₂ => BFlat.denote_wf k (ctxRel_pushTup xs₁ xs₂ hvs))
  | _, .hlt, _, _, _, _ => .hlt

/-- Structural predicate stating that a `Cmd` contains no `.hlt` node. -/
inductive Cmd.NoHlt {V : Ty → Type} : {rs : List Ty} → Cmd V rs → Prop
  | ret {rs vs} : Cmd.NoHlt (rs := rs) (.ret vs)
  | let_ {rs ts op k} : (∀ xs, Cmd.NoHlt (k xs)) → Cmd.NoHlt (rs := rs) (.let_ (ts := ts) op k)
  | load {rs t a k} : (∀ v, Cmd.NoHlt (k v)) → Cmd.NoHlt (rs := rs) (.load t a k)
  | store {rs t v a k} : Cmd.NoHlt k → Cmd.NoHlt (rs := rs) (.store (t := t) v a k)
  | call {rs f as bs args k} : (∀ xs, Cmd.NoHlt (k xs)) →
      Cmd.NoHlt (rs := rs) (.call f (as := as) (bs := bs) args k)
  | interact {rs act as bs args k} : (∀ xs, Cmd.NoHlt (k xs)) →
      Cmd.NoHlt (rs := rs) (.interact act (as := as) (bs := bs) args k)
  | stackalloc {rs n body} : (∀ a, Cmd.NoHlt (body a)) →
      Cmd.NoHlt (rs := rs) (.stackalloc n body)
  | seq {rs mid c₁ c₂} : Cmd.NoHlt c₁ → (∀ xs, Cmd.NoHlt (c₂ xs)) →
      Cmd.NoHlt (rs := rs) (.seq (mid := mid) c₁ c₂)
  | cond {rs c t e} : Cmd.NoHlt t → Cmd.NoHlt e → Cmd.NoHlt (rs := rs) (.cond c t e)
  | while_ {rs st init test body k} :
      (∀ xs, Cmd.NoHlt (test xs)) → (∀ xs, Cmd.NoHlt (body xs)) →
      (∀ xs, Cmd.NoHlt (k xs)) →
      Cmd.NoHlt (rs := rs) (.while_ (st := st) init test body k)

/-- If `bf.wfCheck Γ = true` and `bf.noHlt = true`, `BFlat.denote` never falls back to `.hlt`. -/
theorem BFlat.denote_noHlt_of_wfCheck {V : Ty → Type} :
    {rs : List Ty} → (bf : BFlat rs) → {Γ : List Ty} → {vs : List ((t : Ty) × V t)} →
    CtxTypes Γ vs → bf.wfCheck Γ = true → bf.noHlt = true →
    Cmd.NoHlt (bf.denote V vs)
  | _, .ret vs', _, vs, hΓ, hwf, _ => by
      dsimp only [BFlat.wfCheck] at hwf
      rcases Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf) with ⟨vs'', hv⟩
      dsimp only [BFlat.denote]; rw [hv]; exact .ret
  | _, .let_ op k, _, vs, hΓ, hwf, hno => by
      dsimp only [BFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      dsimp only [BFlat.noHlt] at hno
      rcases Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.1) with ⟨a', ha⟩
      dsimp only [BFlat.denote]; rw [ha]
      exact .let_ fun xs => BFlat.denote_noHlt_of_wfCheck k (CtxTypes.push xs hΓ) hwf.2 hno
  | _, .load t a k, _, vs, hΓ, hwf, hno => by
      dsimp only [BFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      dsimp only [BFlat.noHlt] at hno
      rcases Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1) with ⟨a', ha⟩
      dsimp only [BFlat.denote]; rw [ha]
      exact .load fun v => BFlat.denote_noHlt_of_wfCheck k (.cons hΓ) hwf.2 hno
  | _, .store v a k, _, vs, hΓ, hwf, hno => by
      dsimp only [BFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      dsimp only [BFlat.noHlt] at hno
      rcases Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.1) with ⟨v', hv⟩
      rcases Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.2) with ⟨a', ha⟩
      dsimp only [BFlat.denote]; rw [hv, ha]
      exact .store (BFlat.denote_noHlt_of_wfCheck k hΓ hwf.2 hno)
  | _, .call f _ args k, _, vs, hΓ, hwf, hno => by
      dsimp only [BFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      dsimp only [BFlat.noHlt] at hno
      rcases Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.1) with ⟨a', ha⟩
      dsimp only [BFlat.denote]; rw [ha]
      exact .call fun xs => BFlat.denote_noHlt_of_wfCheck k (CtxTypes.push xs hΓ) hwf.2 hno
  | _, .interact act _ args k, _, vs, hΓ, hwf, hno => by
      dsimp only [BFlat.wfCheck] at hwf; simp only [Bool.and_eq_true] at hwf
      dsimp only [BFlat.noHlt] at hno
      rcases Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.1) with ⟨a', ha⟩
      dsimp only [BFlat.denote]; rw [ha]
      exact .interact fun xs => BFlat.denote_noHlt_of_wfCheck k (CtxTypes.push xs hΓ) hwf.2 hno
  | _, .stackalloc _ body, _, _, hΓ, hwf, hno =>
      .stackalloc fun a => BFlat.denote_noHlt_of_wfCheck body (.cons hΓ) hwf hno
  | _, .seq _ c₁ c₂, _, _, hΓ, hwf, hno => by
      dsimp only [BFlat.wfCheck, BFlat.noHlt] at hwf hno
      simp only [Bool.and_eq_true] at hwf hno
      exact .seq (BFlat.denote_noHlt_of_wfCheck c₁ hΓ hwf.1 hno.1)
        fun xs => BFlat.denote_noHlt_of_wfCheck c₂ (CtxTypes.push xs hΓ) hwf.2 hno.2
  | _, .cond c t e, _, vs, hΓ, hwf, hno => by
      dsimp only [BFlat.wfCheck, BFlat.noHlt] at hwf hno
      simp only [Bool.and_eq_true] at hwf hno
      rcases Option.isSome_iff_exists.1 (denoteArg_isSome_of_checkArg hΓ hwf.1.1) with ⟨c', hc⟩
      dsimp only [BFlat.denote]; rw [hc]
      exact .cond (BFlat.denote_noHlt_of_wfCheck t hΓ hwf.1.2 hno.1)
        (BFlat.denote_noHlt_of_wfCheck e hΓ hwf.2 hno.2)
  | _, .while_ _ init test body k, _, vs, hΓ, hwf, hno => by
      dsimp only [BFlat.wfCheck, BFlat.noHlt] at hwf hno
      simp only [Bool.and_eq_true] at hwf hno
      rcases Option.isSome_iff_exists.1 (denoteArgs_isSome_of_checkArgs hΓ hwf.1.1.1) with
        ⟨i', hi⟩
      dsimp only [BFlat.denote]; rw [hi]
      exact .while_
        (fun xs => BFlat.denote_noHlt_of_wfCheck test (CtxTypes.push xs hΓ) hwf.1.1.2 hno.1.1)
        (fun xs => BFlat.denote_noHlt_of_wfCheck body (CtxTypes.push xs hΓ) hwf.1.2 hno.1.2)
        (fun xs => BFlat.denote_noHlt_of_wfCheck k (CtxTypes.push xs hΓ) hwf.2 hno.2)
  | _, .hlt, _, _, _, _, hno => by dsimp only [BFlat.noHlt] at hno; cases hno

/-- (b) A closed `FuncB` equal to the denotation of some `BFlat rs` is `FuncB.Wf`. -/
theorem FuncB.wf_of_denote {as rs : List Ty} {f : FuncB as rs} (bf : BFlat rs)
    (h : f = fun V xs => bf.denote V (pushTup xs [])) : FuncB.Wf f := by
  intro V₁ V₂ xs₁ xs₂
  have h₁ : f V₁ xs₁ = bf.denote V₁ (pushTup xs₁ []) := congrFun (congrFun h V₁) xs₁
  have h₂ : f V₂ xs₂ = bf.denote V₂ (pushTup xs₂ []) := congrFun (congrFun h V₂) xs₂
  rw [h₁, h₂]
  exact BFlat.denote_wf bf
    ((ctxRel_pushTup xs₁ xs₂ (.nil (G := []))).mono fun _ hp => by simpa using hp)

/-- A closed `FuncB` equal to the denotation of its own `toBFlat` reification is `FuncB.Wf`. -/
theorem FuncB.wf_of_reify {as rs : List Ty} {f : FuncB as rs}
    (h : f = fun V xs => (toBFlat (f K (Tup.levels as 0)) as.length).denote V (pushTup xs [])) :
    FuncB.Wf f :=
  FuncB.wf_of_denote (toBFlat (f K (Tup.levels as 0)) as.length) h

/-- Prove `FuncB.Wf f` for a closed concrete function by reification + kernel `rfl`
(reusing `LeanQbe.T.t_kernel_rfl`). -/
macro "t_b2_wf_reify" : tactic =>
  `(tactic| (refine FuncB.wf_of_reify ?_; t_kernel_rfl))

/-- First-order `BFlat.wp` agrees identically with `Cmd.wp` of `BFlat.denote`. -/
theorem BFlat.wp_iff_denote_wp {ext : ExtSpecB} {Γ : EnvB} :
    {rs : List Ty} → (bf : BFlat rs) → ∀ (B : Nat) (Q : PostB rs)
    (vs : List ((t : Ty) × Val t)) (t : TraceB) (m : Mem 64),
    bf.wp ext Γ B Q vs t m ↔ Cmd.wp ext Γ B Q (bf.denote Val vs) t m
  | _, .ret vs', _, _, vs, _, _ => by
      dsimp only [BFlat.wp, BFlat.denote]
      cases denoteArgs vs vs' <;> rfl
  | _, .let_ op k, B, Q, vs, t, m => by
      dsimp only [BFlat.wp, BFlat.denote]
      cases denoteArgs vs op.args with
      | none => rfl
      | some args' =>
          dsimp only [Cmd.wp]
          exact ⟨Op.wp_mono fun r hr => (BFlat.wp_iff_denote_wp k B Q (pushTup r vs) t m).1 hr,
            Op.wp_mono fun r hr => (BFlat.wp_iff_denote_wp k B Q (pushTup r vs) t m).2 hr⟩
  | _, .load ty a k, B, Q, vs, t, m => by
      dsimp only [BFlat.wp, BFlat.denote]
      cases denoteArg vs a with
      | none => rfl
      | some a' =>
          dsimp only [Cmd.wp]
          exact exists_congr fun v =>
            and_congr_right fun _ => BFlat.wp_iff_denote_wp k B Q (⟨ty, v⟩ :: vs) t m
  | _, .store v a k, B, Q, vs, t, m => by
      dsimp only [BFlat.wp, BFlat.denote]
      cases denoteArg vs v <;> cases denoteArg vs a <;> dsimp only [Cmd.wp]
      · rfl
      · rfl
      · rfl
      · exact and_congr_right fun _ => BFlat.wp_iff_denote_wp k B Q vs t _
  | _, .call _ _ args k, B, Q, vs, t, m => by
      dsimp only [BFlat.wp, BFlat.denote]
      cases denoteArgs vs args with
      | none => rfl
      | some args' =>
          dsimp only [Cmd.wp]
          exact exists_congr fun P => and_congr_right fun _ =>
            forall₃_congr fun r t' m' =>
              imp_congr_right fun _ => BFlat.wp_iff_denote_wp k B Q (pushTup r vs) t' m'
  | _, .interact _ _ args k, B, Q, vs, t, m => by
      dsimp only [BFlat.wp, BFlat.denote]
      cases denoteArgs vs args with
      | none => rfl
      | some args' =>
          dsimp only [Cmd.wp]
          exact exists₃_congr fun _ _ _ => and_congr_right fun _ => and_congr_right fun _ =>
            forall₂_congr fun _ res => imp_congr_right fun _ => forall_congr' fun m' =>
              imp_congr_right fun _ => BFlat.wp_iff_denote_wp k B Q (pushTup res vs) _ m'
  | _, .stackalloc nbytes body, B, Q, vs, t, mSmall => by
      dsimp only [BFlat.wp, BFlat.denote, Cmd.wp]
      exact and_congr_right fun _ => forall₃_congr fun a _ mComb =>
        imp_congr_right fun _ => imp_congr_right fun _ =>
          BFlat.wp_iff_denote_wp body (B - nbytes) _ (⟨i64, a⟩ :: vs) t mComb
  | _, .seq _ c₁ c₂, B, Q, vs, t, m => by
      dsimp only [BFlat.wp, BFlat.denote, Cmd.wp]
      rw [BFlat.wp_iff_denote_wp c₁ B _ vs t m]
      exact ⟨Cmd.wp_mono (fun mid t' m' h =>
          (BFlat.wp_iff_denote_wp c₂ B Q (pushTup mid vs) t' m').1 h) _ t m,
        Cmd.wp_mono (fun mid t' m' h =>
          (BFlat.wp_iff_denote_wp c₂ B Q (pushTup mid vs) t' m').2 h) _ t m⟩
  | _, .cond c tBr eBr, B, Q, vs, t, m => by
      dsimp only [BFlat.wp, BFlat.denote]
      cases denoteArg vs c with
      | none => rfl
      | some c' =>
          dsimp only [Cmd.wp]
          exact and_congr
            (imp_congr_right fun _ => BFlat.wp_iff_denote_wp tBr B Q vs t m)
            (imp_congr_right fun _ => BFlat.wp_iff_denote_wp eBr B Q vs t m)
  | _, .while_ _ init test body k, B, Q, vs, t, m => by
      dsimp only [BFlat.wp, BFlat.denote]
      cases denoteArgs vs init with
      | none => rfl
      | some init' =>
          dsimp only [Cmd.wp]
          refine forall_congr' fun I => imp_congr_left <|
            forall₃_congr fun s t' m' => imp_congr_left ?_
          rw [BFlat.wp_iff_denote_wp test B _ (pushTup s vs) t' m']
          exact ⟨Cmd.wp_mono (fun (b, ()) t₁ m₁ ⟨ht, hf⟩ =>
              ⟨fun hb => (BFlat.wp_iff_denote_wp body B I (pushTup s vs) t₁ m₁).1 (ht hb),
               fun hb => (BFlat.wp_iff_denote_wp k B Q (pushTup s vs) t₁ m₁).1 (hf hb)⟩) _ t' m',
            Cmd.wp_mono (fun (b, ()) t₁ m₁ ⟨ht, hf⟩ =>
              ⟨fun hb => (BFlat.wp_iff_denote_wp body B I (pushTup s vs) t₁ m₁).2 (ht hb),
               fun hb => (BFlat.wp_iff_denote_wp k B Q (pushTup s vs) t₁ m₁).2 (hf hb)⟩) _ t' m'⟩
  | _, .hlt, _, _, _, _, _ => Iff.rfl

private theorem lookupV_head_b {V : Ty → Type} (t : Ty) (v : V t) (vs : List ((u : Ty) × V u)) :
    lookupV (⟨t, v⟩ :: vs) t 0 = some v := by
  dsimp only [lookupV, listGet?]; exact PassFlatKit.castTy_self t v

private theorem flatCtxMatch_pushTupV {V : Ty → Type} {G : Ctx K V} {vs : List ((t : Ty) × V t)}
    (hvs : FlatCtxMatch lookupV G vs) {as : List Ty} (xs : Tup V as) :
    FlatCtxMatch lookupV (Tup.zip (Tup.levels as vs.length) xs ++ G) (pushTup xs vs) :=
  FlatCtxMatch.pushTup lookupV_head_b (fun _ _ _ _ _ => rfl) xs hvs

private theorem flatCtxMatch_consV {G : Ctx K Val} {vs : List ((t : Ty) × Val t)}
    (hvs : FlatCtxMatch lookupV G vs) (t : Ty) (v : Val t) :
    FlatCtxMatch lookupV (⟨t, vs.length, v⟩ :: G) (⟨t, v⟩ :: vs) :=
  flatCtxMatch_pushTupV hvs (as := [t]) (v, ())

private theorem denoteArg_idxArg_b {V : Ty → Type} {G : Ctx K V} {vs : List ((t : Ty) × V t)}
    (hvs : FlatCtxMatch lookupV G vs) {t : Ty} {a₁ : Arg K t} {a₂ : Arg V t}
    (ha : ArgRel G t a₁ a₂) :
    denoteArg vs (idxArg vs.length a₁) = some a₂ := by
  cases ha with
  | @var lvl v hm =>
    obtain ⟨hlt, hl⟩ := hvs _ hm
    dsimp only [idxArg]; simp only [hlt, ↓reduceIte]; dsimp only [denoteArg]; rw [hl]
  | imm c => rfl

private theorem denoteArgs_idxArgs_b {V : Ty → Type} {G : Ctx K V} {vs : List ((t : Ty) × V t)}
    (hvs : FlatCtxMatch lookupV G vs) :
    {ts : List Ty} → {as₁ : Tup (Arg K) ts} → {as₂ : Tup (Arg V) ts} →
    TRel (ArgRel G) as₁ as₂ →
    denoteArgs vs (idxArgs vs.length as₁) = some as₂
  | [], (), (), .nil => rfl
  | _ :: _, (_, _), (_, _), .cons h hs => by
    dsimp only [idxArgs, denoteArgs]; rw [denoteArg_idxArg_b hvs h, denoteArgs_idxArgs_b hvs hs]

/-- (c) Reification-denotation round-trip preserves `Cmd.wp` identically under `Cmd.Wf`. -/
theorem BFlat.denote_wp_iff {ext : ExtSpecB} {Γ : EnvB} {rs : List Ty}
    {G : Ctx K Val} {c₁ : Cmd K rs} {c₂ : Cmd Val rs}
    (hwf : Cmd.Wf G c₁ c₂) :
    ∀ (vs : List ((t : Ty) × Val t)), FlatCtxMatch lookupV G vs →
    ∀ (B : Nat) (Q : PostB rs) (t : TraceB) (m : Mem 64),
    Cmd.wp ext Γ B Q ((toBFlat c₁ vs.length).denote Val vs) t m ↔
      Cmd.wp ext Γ B Q c₂ t m := by
  induction hwf with
  | ret hvs' =>
      intro vs hvs _ _ _ _
      have hda := denoteArgs_idxArgs_b hvs hvs'
      dsimp only [toBFlat, BFlat.denote]; rw [hda]
  | let_ hop _ ih =>
      intro vs hvs B Q t m
      cases hop with | mk code hargs =>
      have hda := denoteArgs_idxArgs_b hvs hargs
      dsimp only [toBFlat, BFlat.denote]; rw [hda]; dsimp only [Cmd.wp]
      refine ⟨Op.wp_mono fun r hr => ?_, Op.wp_mono fun r hr => ?_⟩
      · have hk := (ih (Tup.levels _ vs.length) r (pushTup r vs)
          (flatCtxMatch_pushTupV hvs r) B Q t m).1
        rw [pushTup_length r vs] at hk; exact hk hr
      · have hk := (ih (Tup.levels _ vs.length) r (pushTup r vs)
          (flatCtxMatch_pushTupV hvs r) B Q t m).2
        rw [pushTup_length r vs] at hk; exact hk hr
  | load ty ha _ ih =>
      intro vs hvs B Q t m
      have hda := denoteArg_idxArg_b hvs ha
      dsimp only [toBFlat, BFlat.denote]; rw [hda]; dsimp only [Cmd.wp]
      exact exists_congr fun v => and_congr_right fun _ =>
        ih vs.length v (⟨ty, v⟩ :: vs) (flatCtxMatch_consV hvs ty v) B Q t m
  | store hv ha _ ih =>
      intro vs hvs B Q t _
      have hdv := denoteArg_idxArg_b hvs hv
      have hda := denoteArg_idxArg_b hvs ha
      dsimp only [toBFlat, BFlat.denote]; rw [hdv, hda]; dsimp only [Cmd.wp]
      exact and_congr_right fun _ => ih vs hvs B Q t _
  | call _ hargs _ ih =>
      intro vs hvs B Q t m
      have hda := denoteArgs_idxArgs_b hvs hargs
      dsimp only [toBFlat, BFlat.denote]; rw [hda]; dsimp only [Cmd.wp]
      exact exists_congr fun P => and_congr_right fun _ =>
        forall₃_congr fun r t' m' => imp_congr_right fun _ => by
          have hk := ih (Tup.levels _ vs.length) r (pushTup r vs)
            (flatCtxMatch_pushTupV hvs r) B Q t' m'
          rwa [pushTup_length r vs] at hk
  | interact _ hargs _ ih =>
      intro vs hvs B Q t m
      have hda := denoteArgs_idxArgs_b hvs hargs
      dsimp only [toBFlat, BFlat.denote]; rw [hda]; dsimp only [Cmd.wp]
      exact exists₃_congr fun _ _ _ => and_congr_right fun _ => and_congr_right fun _ =>
        forall₂_congr fun _ res => imp_congr_right fun _ => forall_congr' fun m' =>
          imp_congr_right fun _ => by
            simpa [pushTup_length] using
              ih (Tup.levels _ vs.length) res (pushTup res vs)
                (flatCtxMatch_pushTupV hvs res) B Q _ m'
  | stackalloc nbytes _ ih =>
      intro vs hvs B Q t mSmall
      dsimp only [toBFlat, BFlat.denote, Cmd.wp]
      exact and_congr_right fun _ => forall₃_congr fun a _ mComb =>
        imp_congr_right fun _ => imp_congr_right fun _ =>
          ih vs.length a (⟨i64, a⟩ :: vs) (flatCtxMatch_consV hvs i64 a) (B - nbytes) _ t mComb
  | seq _ _ ih₁ ih₂ =>
      intro vs hvs B Q t m
      dsimp only [toBFlat, BFlat.denote, Cmd.wp]
      rw [ih₁ vs hvs B _ t m]
      refine ⟨Cmd.wp_mono (fun mid t' m' hm => ?_) _ t m,
        Cmd.wp_mono (fun mid t' m' hm => ?_) _ t m⟩
      · have hk := (ih₂ (Tup.levels _ vs.length) mid (pushTup mid vs)
          (flatCtxMatch_pushTupV hvs mid) B Q t' m').1
        rw [pushTup_length mid vs] at hk; exact hk hm
      · have hk := (ih₂ (Tup.levels _ vs.length) mid (pushTup mid vs)
          (flatCtxMatch_pushTupV hvs mid) B Q t' m').2
        rw [pushTup_length mid vs] at hk; exact hk hm
  | cond hc _ _ iht ihe =>
      intro vs hvs B Q t m
      have hdc := denoteArg_idxArg_b hvs hc
      dsimp only [toBFlat, BFlat.denote]; rw [hdc]; dsimp only [Cmd.wp]
      exact and_congr
        (imp_congr_right fun _ => iht vs hvs B Q t m)
        (imp_congr_right fun _ => ihe vs hvs B Q t m)
  | while_ hinit _ _ _ iht ihb ihk =>
      intro vs hvs B Q t m
      have hdi := denoteArgs_idxArgs_b hvs hinit
      dsimp only [toBFlat, BFlat.denote]; rw [hdi]; dsimp only [Cmd.wp]
      refine forall_congr' fun I => imp_congr_left <|
        forall₃_congr fun s t' m' => imp_congr_left ?_
      have htm : ∀ P,
          Cmd.wp ext Γ B P ((toBFlat _ (vs.length + _)).denote Val (pushTup s vs)) t' m' ↔
            Cmd.wp ext Γ B P _ t' m' := fun P => by
        simpa [pushTup_length] using
          iht (Tup.levels _ vs.length) s (pushTup s vs) (flatCtxMatch_pushTupV hvs s) B P t' m'
      rw [htm]
      have hbm : ∀ t₁ m₁,
          Cmd.wp ext Γ B I ((toBFlat _ (vs.length + _)).denote Val (pushTup s vs)) t₁ m₁ ↔
            Cmd.wp ext Γ B I _ t₁ m₁ := fun t₁ m₁ => by
        simpa [pushTup_length] using
          ihb (Tup.levels _ vs.length) s (pushTup s vs) (flatCtxMatch_pushTupV hvs s) B I t₁ m₁
      have hkm : ∀ t₁ m₁,
          Cmd.wp ext Γ B Q ((toBFlat _ (vs.length + _)).denote Val (pushTup s vs)) t₁ m₁ ↔
            Cmd.wp ext Γ B Q _ t₁ m₁ := fun t₁ m₁ => by
        simpa [pushTup_length] using
          ihk (Tup.levels _ vs.length) s (pushTup s vs) (flatCtxMatch_pushTupV hvs s) B Q t₁ m₁
      exact ⟨Cmd.wp_mono (fun (b, ()) t₁ m₁ ⟨ht, hf⟩ =>
          ⟨fun hb => (hbm t₁ m₁).1 (ht hb), fun hb => (hkm t₁ m₁).1 (hf hb)⟩) _ t' m',
        Cmd.wp_mono (fun (b, ()) t₁ m₁ ⟨ht, hf⟩ =>
          ⟨fun hb => (hbm t₁ m₁).2 (ht hb), fun hb => (hkm t₁ m₁).2 (hf hb)⟩) _ t' m'⟩
  | hlt => intro _ _ _ _ _ _; rfl

/-- Closed-function reification-denotation round-trip preserves `FuncB.wp` iff. -/
theorem FuncB.renorm_wp_iff {as rs : List Ty} {ext : ExtSpecB} {Γ : EnvB}
    {f : FuncB as rs} (h : f.Wf) (B : Nat) (xs : Tup Val as) (t : TraceB) (m : Mem 64)
    (Q : PostB rs) :
    FuncB.wp ext Γ (FuncB.renorm f) B xs t m Q ↔ FuncB.wp ext Γ f B xs t m Q := by
  have hwf := h K Val (Tup.levels as 0) xs
  have hvs : FlatCtxMatch lookupV (Tup.zip (Tup.levels as 0) xs) (pushTup xs []) := by
    simpa [List.append_nil] using
      (flatCtxMatch_pushTupV (G := ([] : Ctx K Val)) (vs := []) FlatCtxMatch.empty xs)
  have hd := BFlat.denote_wp_iff (ext := ext) (Γ := Γ) hwf (pushTup xs []) hvs B Q t m
  simpa [FuncB.wp, FuncB.renorm, denoteFuncB, reifyFuncB, pushTup_length] using hd

/-- Direct first-order `BFlat.wp` on `reifyFuncB f` agrees with `FuncB.wp` on any `FuncB.Wf` `f`. -/
theorem FuncB.reify_wp_iff {as rs : List Ty} {ext : ExtSpecB} {Γ : EnvB}
    {f : FuncB as rs} (h : f.Wf) (B : Nat) (xs : Tup Val as) (t : TraceB) (m : Mem 64)
    (Q : PostB rs) :
    (reifyFuncB f).wp ext Γ B Q (pushTup xs []) t m ↔ FuncB.wp ext Γ f B xs t m Q :=
  (BFlat.wp_iff_denote_wp (reifyFuncB f) B Q (pushTup xs []) t m).trans
    (FuncB.renorm_wp_iff h B xs t m Q)

end LeanQbe.T.Bedrock2
