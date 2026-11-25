module

public import LeanQbe.T.Bedrock2.Phoas
public import LeanQbe.T.WPLemmas
public import LeanQbe.T.WfLemmas

/-!
# Sound Lowering of Structured Bedrock2 (`Cmd` / `FuncB`) to `LeanQbe.T`

Lowers structured Bedrock2 into real `LeanQbe.T.Expr` / `Func` with **zero** new `Expr`
constructors:

1. **Pure (`NoStackNoIO`) fragment:** Identical linear-size lowering (`seq` ↦ single-block
   forward `Expr.group` + `jump`, `cond` ↦ `Expr.jnz`, `while_` ↦ `loop1` + test join
   `group`), proving `Cmd.toExpr_wp_iff` and `FuncB.toFunc_wp_iff` (`toFunc_wp_iff`).
2. **Full language (`stackalloc` + `interact`):** Models `stackalloc nbytes` via paired
   `cfg.allocSym` / `cfg.freeSym` `.call`s (with a single join `group` so reclamation runs
   once after `body` without duplicating `onRet`), and `interact action` via `.call
   (cfg.ioSym action)`, proving:
   * `Cmd.toExprWith_wf` / `FuncB.toFunc_wf` (`toFunc_wf`) unconditionally for ALL `FuncB`;
   * `Cmd.toExprWith_wp_sound` / `FuncB.toFunc_wp_sound` (`Cmd.wp` → `LeanQbe.T.wp` under
     `Env.ofBedrock2Sound`, for arbitrary trace-dependent `ext` / `Γ` / `Q` and `B < 2 ^ 64`);
   * `Cmd.toExprWith_wpUnbounded_iff` / `FuncB.toFunc_wpUnbounded_iff` (exact `↔` across the
     entire language under trace-independence and `LowerEnvValid`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Bedrock2

open LeanQbe.T
open Kraken.Bedrock2 (anybytes split)

/-- Symbol configuration for lowering `stackalloc` and `interact` to `LeanQbe.T.Expr.call`
without adding new `Expr` constructors. -/
structure LowerCfg where
  allocSym : Sym := "__b2_stackalloc"
  freeSym : Sym := "__b2_stackfree"
  ioSym : Sym → Sym := id

/-- Default symbol configuration for `Cmd.toExpr` / `FuncB.toFunc`. -/
def LowerCfg.default : LowerCfg := {}

/-- Pure structured fragment: no `stackalloc` and no `interact`. -/
inductive Cmd.NoStackNoIO {V : Ty → Type} : {rs : List Ty} → Cmd V rs → Prop
  | ret {rs vs} : Cmd.NoStackNoIO (rs := rs) (.ret vs)
  | let_ {rs ts op k} : (∀ xs, Cmd.NoStackNoIO (k xs)) →
      Cmd.NoStackNoIO (rs := rs) (.let_ (ts := ts) op k)
  | load {rs t a k} : (∀ v, Cmd.NoStackNoIO (k v)) →
      Cmd.NoStackNoIO (rs := rs) (.load t a k)
  | store {rs t v a k} : Cmd.NoStackNoIO k →
      Cmd.NoStackNoIO (rs := rs) (.store (t := t) v a k)
  | call {rs f as bs args k} : (∀ xs, Cmd.NoStackNoIO (k xs)) →
      Cmd.NoStackNoIO (rs := rs) (.call f (as := as) (bs := bs) args k)
  | seq {rs mid c₁ c₂} : Cmd.NoStackNoIO c₁ → (∀ xs, Cmd.NoStackNoIO (c₂ xs)) →
      Cmd.NoStackNoIO (rs := rs) (.seq (mid := mid) c₁ c₂)
  | cond {rs c t e} : Cmd.NoStackNoIO t → Cmd.NoStackNoIO e →
      Cmd.NoStackNoIO (rs := rs) (.cond c t e)
  | while_ {rs st init test body k} :
      (∀ xs, Cmd.NoStackNoIO (test xs)) →
      (∀ xs, Cmd.NoStackNoIO (body xs)) →
      (∀ xs, Cmd.NoStackNoIO (k xs)) →
      Cmd.NoStackNoIO (rs := rs) (.while_ (st := st) init test body k)
  | hlt {rs} : Cmd.NoStackNoIO (rs := rs) .hlt

/-- Linear-size lowering of `Cmd V mid` into `LeanQbe.T.Expr V L rs` with return
continuation `onRet`:
* `seq` ↦ one-block forward `Expr.group` + `jump`;
* `cond` ↦ `Expr.jnz`;
* `while_` ↦ `LeanQbe.T.loop1` + test join `Expr.group` + `jnz` + `jump`;
* `interact` ↦ `.call (cfg.ioSym action)`;
* `stackalloc` ↦ `.call cfg.allocSym` + join `Expr.group` + `.call cfg.freeSym`. -/
def Cmd.toExprWith {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (cfg : LowerCfg := LowerCfg.default) :
    {mid : List Ty} → Cmd V mid → (Tup (Arg V) mid → Expr V L rs) → Expr V L rs
  | _, .ret vs, onRet => onRet vs
  | _, .let_ op k, onRet => .let_ op fun xs => (k xs).toExprWith cfg onRet
  | _, .load t a k, onRet => .load t a fun v => (k v).toExprWith cfg onRet
  | _, .store v a k, onRet => .store v a (k.toExprWith cfg onRet)
  | _, .call f args k, onRet => .call f args fun xs => (k xs).toExprWith cfg onRet
  | _, .interact action args k, onRet =>
      .call (cfg.ioSym action) args fun xs => (k xs).toExprWith cfg onRet
  | mid, .stackalloc nbytes body, onRet =>
      if nbytes < 2 ^ 64 then
        .call cfg.allocSym (as := [i64]) (bs := [i64]) (.imm (BitVec.ofNat 64 nbytes), ())
          fun (a, ()) =>
            .group (sig := [mid])
              (fun _ =>
                .cons
                  (fun xs =>
                    .call cfg.freeSym (as := [i64, i64]) (bs := [])
                      (.var a, .imm (BitVec.ofNat 64 nbytes), ())
                      fun () => onRet (Tup.toArgs xs))
                  .nil)
              (fun Js => (body a).toExprWith cfg (fun vs => .jump Js.1 vs))
      else .hlt
  | _, .seq (mid := mid) c₁ c₂, onRet =>
      .group (sig := [mid])
        (fun _ => .cons (fun xs => (c₂ xs).toExprWith cfg onRet) .nil)
        (fun Js => c₁.toExprWith cfg (fun vs => .jump Js.1 vs))
  | _, .cond c t e, onRet => .jnz c (t.toExprWith cfg onRet) (e.toExprWith cfg onRet)
  | _, .while_ (st := st) init test body k, onRet =>
      loop1 (ts := st)
        (fun jLoop s =>
          .group (sig := [[.bool]])
            (fun _ =>
              .cons
                (fun (b, ()) =>
                  .jnz (.var b)
                    ((body s).toExprWith cfg (fun s' => .jump jLoop s'))
                    ((k s).toExprWith cfg onRet))
                .nil)
            (fun Js => (test s).toExprWith cfg (fun b => .jump Js.1 b)))
        (fun jLoop => .jump jLoop init)
  | _, .hlt, _ => .hlt

/-- Top-level lowering `Cmd V rs → LeanQbe.T.Expr V L rs`. -/
def Cmd.toExpr {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (c : Cmd V rs) (cfg : LowerCfg := LowerCfg.default) : Expr V L rs :=
  c.toExprWith cfg .ret

/-- Lower a closed `FuncB as rs` to `LeanQbe.T.Func as rs`. -/
def FuncB.toFunc {as rs : List Ty} (f : FuncB as rs)
    (cfg : LowerCfg := LowerCfg.default) : Func as rs :=
  fun V _ xs => (f V xs).toExpr cfg

/-- Alias matching `ToFunc` naming convention. -/
abbrev toFunc := @FuncB.toFunc

private theorem tup_toArgs_rel {V₁ V₂ : Ty → Type} {G : Ctx V₁ V₂} :
    {ts : List Ty} → {xs₁ : Tup V₁ ts} → {xs₂ : Tup V₂ ts} →
    (∀ {t : Ty} {v₁ : V₁ t} {v₂ : V₂ t}, ⟨t, v₁, v₂⟩ ∈ Tup.zip xs₁ xs₂ → ⟨t, v₁, v₂⟩ ∈ G) →
    TRel (ArgRel G) (Tup.toArgs xs₁) (Tup.toArgs xs₂)
  | [], (), (), _ => .nil
  | _ :: _, (_, _), (_, _), h =>
      .cons (.var (h List.mem_cons_self))
        (tup_toArgs_rel fun hp => h (List.mem_cons_of_mem _ hp))

/-- Lowering preserves relational well-formedness (`Cmd.Wf → LeanQbe.T.Wf`) across ALL
`Cmd` constructors, including `stackalloc` and `interact`. -/
theorem Cmd.toExprWith_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {cfg : LowerCfg} :
    {mid : List Ty} → {G : Ctx V₁ V₂} → {c₁ : Cmd V₁ mid} → {c₂ : Cmd V₂ mid} →
    Cmd.Wf G c₁ c₂ →
    ∀ {D : Ctx L₁ L₂}
      {onRet₁ : Tup (Arg V₁) mid → Expr V₁ L₁ rs}
      {onRet₂ : Tup (Arg V₂) mid → Expr V₂ L₂ rs},
    (∀ {G' D' vs₁ vs₂}, (∀ p ∈ G, p ∈ G') → (∀ p ∈ D, p ∈ D') →
      TRel (ArgRel G') vs₁ vs₂ → LeanQbe.T.Wf G' D' (onRet₁ vs₁) (onRet₂ vs₂)) →
    LeanQbe.T.Wf G D (c₁.toExprWith cfg onRet₁) (c₂.toExprWith cfg onRet₂)
  | _, _, _, _, .ret hvs, _, _, _, hon => hon (fun _ hp => hp) (fun _ hp => hp) hvs
  | _, _, _, _, .let_ hop hk, _, _, _, hon =>
      .let_ hop fun x₁ x₂ =>
        Cmd.toExprWith_wf (hk x₁ x₂) fun hG hD =>
          hon (fun _ hp => hG _ (List.mem_append_right _ hp)) hD
  | _, _, _, _, .load t ha hk, _, _, _, hon =>
      .load t ha fun v₁ v₂ =>
        Cmd.toExprWith_wf (hk v₁ v₂) fun hG hD =>
          hon (fun _ hp => hG _ (List.mem_cons_of_mem _ hp)) hD
  | _, _, _, _, .store hv ha hk, _, _, _, hon =>
      .store hv ha (Cmd.toExprWith_wf hk hon)
  | _, _, _, _, .call f hargs hk, _, _, _, hon =>
      .call f hargs fun x₁ x₂ =>
        Cmd.toExprWith_wf (hk x₁ x₂) fun hG hD =>
          hon (fun _ hp => hG _ (List.mem_append_right _ hp)) hD
  | _, _, _, _, .interact act hargs hk, _, _, _, hon =>
      .call (cfg.ioSym act) hargs fun x₁ x₂ =>
        Cmd.toExprWith_wf (hk x₁ x₂) fun hG hD =>
          hon (fun _ hp => hG _ (List.mem_append_right _ hp)) hD
  | _, _, _, _, .stackalloc nbytes hbody, _, _, _, hon => by
      dsimp only [Cmd.toExprWith]
      split
      · refine .call cfg.allocSym (.cons (.imm _) .nil) fun (a₁, ()) (a₂, ()) => ?_
        refine .group (fun _ _ => .cons (fun xs₁ xs₂ => ?_) .nil) (fun _ _ => ?_)
        · refine .call cfg.freeSym
            (.cons (.var (List.mem_append_right _ List.mem_cons_self))
              (.cons (.imm _) .nil)) fun () () => ?_
          exact hon
            (fun _ hp => List.mem_append_right _ (List.mem_append_right _
              (List.mem_cons_of_mem _ hp)))
            (fun _ hp => List.mem_append_right _ hp)
            (tup_toArgs_rel fun hp => List.mem_append_right _ (List.mem_append_left _ hp))
        · exact Cmd.toExprWith_wf (hbody a₁ a₂) fun _ hD hvs =>
            .jump (hD _ (List.mem_append_left _ List.mem_cons_self)) hvs
      · exact .hlt
  | _, _, _, _, .seq hc₁ hc₂, _, _, _, hon =>
      .group
        (fun _ _ => .cons (fun x₁ x₂ =>
          Cmd.toExprWith_wf (hc₂ x₁ x₂) fun hG hD =>
            hon (fun _ hp => hG _ (List.mem_append_right _ hp))
              (fun _ hp => hD _ (List.mem_append_right _ hp))) .nil)
        (fun _ _ =>
          Cmd.toExprWith_wf hc₁ fun _ hD hvs =>
            .jump (hD _ (List.mem_append_left _ List.mem_cons_self)) hvs)
  | _, _, _, _, .cond hc ht he, _, _, _, hon =>
      .jnz hc (Cmd.toExprWith_wf ht hon) (Cmd.toExprWith_wf he hon)
  | _, _, _, _, .while_ hinit htest hbody hk, _, _, _, hon =>
      .group
        (fun _ _ => .cons (fun s₁ s₂ =>
          .group
            (fun _ _ => .cons (fun (_, ()) (_, ()) =>
              .jnz (.var List.mem_cons_self)
                (Cmd.toExprWith_wf ((hbody s₁ s₂).weaken
                    fun _ hp => List.mem_cons_of_mem _ hp)
                  fun _ hD hvs =>
                    .jump (hD _ (List.mem_append_right _
                      (List.mem_append_left _ List.mem_cons_self))) hvs)
                (Cmd.toExprWith_wf ((hk s₁ s₂).weaken
                    fun _ hp => List.mem_cons_of_mem _ hp)
                  fun hG hD =>
                    hon (fun _ hp => hG _ (List.mem_cons_of_mem _
                          (List.mem_append_right _ hp)))
                      (fun _ hp => hD _ (List.mem_append_right _
                          (List.mem_append_right _ hp)))))
              .nil)
            (fun _ _ =>
              Cmd.toExprWith_wf (htest s₁ s₂) fun _ hD hvs =>
                .jump (hD _ (List.mem_append_left _ List.mem_cons_self)) hvs))
          .nil)
        (fun _ _ => .jump (List.mem_append_left _ List.mem_cons_self) hinit)
  | _, _, _, _, .hlt, _, _, _, _ => .hlt

theorem FuncB.toFunc_wf {as rs : List Ty} {f : FuncB as rs} (h : f.Wf)
    (cfg : LowerCfg := LowerCfg.default) :
    (f.toFunc cfg).Wf :=
  fun V₁ V₂ _ _ xs₁ xs₂ => Cmd.toExprWith_wf (h V₁ V₂ xs₁ xs₂) fun _ _ hvs => .ret hvs

/-- Alias matching `toFunc_wf` naming convention. -/
theorem toFunc_wf {as rs : List Ty} {f : FuncB as rs} (h : f.Wf)
    (cfg : LowerCfg := LowerCfg.default) :
    (toFunc f cfg).Wf :=
  FuncB.toFunc_wf h cfg

/-! ### Exact equivalence on the pure (`NoStackNoIO`) fragment -/

/-- Exact semantic preservation of `Cmd.toExprWith` on the pure (`NoStackNoIO`) fragment. -/
theorem Cmd.toExprWith_wp_iff {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {cfg : LowerCfg} {mid : List Ty} {c : Cmd Val mid} (h : c.NoStackNoIO) :
    ∀ (onRet : Tup (Arg Val) mid → Expr Val Cont rs) (R : Post mid),
    (∀ vs m, LeanQbe.T.wp Γ Q X (onRet vs) m ↔ R (vals vs) m) →
    ∀ (B : Nat) (t : TraceB) (m : Mem 64),
    LeanQbe.T.wp Γ Q X (c.toExprWith cfg onRet) m ↔
      Cmd.wp extEmpty (EnvB.ofTEnv Γ X) B (fun vs _ m' => R vs m') c t m := by
  induction h with
  | ret =>
      intro onRet R hon _ _ m
      exact hon _ m
  | let_ _ ih =>
      intro onRet R hon B t m
      dsimp only [Cmd.toExprWith, LeanQbe.T.wp, Cmd.wp]
      exact ⟨Op.wp_mono fun r hr => (ih r onRet R hon B t m).1 hr,
        Op.wp_mono fun r hr => (ih r onRet R hon B t m).2 hr⟩
  | load _ ih =>
      intro onRet R hon B t m
      dsimp only [Cmd.toExprWith, LeanQbe.T.wp, Cmd.wp]
      exact exists_congr fun v => and_congr_right fun _ => ih v onRet R hon B t m
  | store _ ih =>
      intro onRet R hon B t _
      dsimp only [Cmd.toExprWith, LeanQbe.T.wp, Cmd.wp]
      exact and_congr_right fun _ => ih onRet R hon B t _
  | call _ ih =>
      intro onRet R hon B t m
      dsimp only [Cmd.toExprWith, LeanQbe.T.wp, Cmd.wp, EnvB.ofTEnv]
      constructor
      · rintro ⟨P', E, hΓ, hP', hE⟩
        refine ⟨fun r t' m' => t' = t ∧ P' r m',
          ⟨P', E, hΓ, fun r m' hp => ⟨rfl, hp⟩, hE⟩, ?_⟩
        rintro r t' m' ⟨ht, hp⟩
        subst ht
        exact (ih r onRet R hon B t' m').1 (hP' r m' hp)
      · rintro ⟨P, ⟨P', E, hΓ, hPP', hE⟩, hk⟩
        refine ⟨P', E, hΓ, fun r m' hp => ?_, hE⟩
        exact (ih r onRet R hon B t m').2 (hk r t m' (hPP' r m' hp))
  | @seq _ mid' c₁ c₂ _ _ ih₁ ih₂ =>
      intro onRet R hon B t m
      dsimp only [Cmd.toExprWith, LeanQbe.T.wp, Closed, Cmd.wp]
      let J₀ : Cont mid' := fun xs m' => LeanQbe.T.wp Γ Q X ((c₂ xs).toExprWith cfg onRet) m'
      constructor
      · intro hgrp
        have h1 := hgrp (J₀, ()) ⟨fun _ _ h => h, trivial⟩
        have hc1 := (ih₁ (fun vs => .jump J₀ vs) J₀ (fun _ _ => Iff.rfl) B t m).1 h1
        exact Cmd.wp_mono (fun xs t' m' hj => (ih₂ xs onRet R hon B t' m').1 hj) _ t m hc1
      · intro hc1 ⟨J, ⟨⟩⟩ ⟨hJ, _⟩
        have hc1' := Cmd.wp_mono
          (fun xs t' m' hc2 => hJ xs m' ((ih₂ xs onRet R hon B t' m').2 hc2)) _ t m hc1
        exact (ih₁ (fun vs => .jump J vs) J (fun _ _ => Iff.rfl) B t m).2 hc1'
  | cond _ _ iht ihe =>
      intro onRet R hon B t m
      dsimp only [Cmd.toExprWith, LeanQbe.T.wp, Cmd.wp]
      exact and_congr
        (imp_congr_right fun _ => iht onRet R hon B t m)
        (imp_congr_right fun _ => ihe onRet R hon B t m)
  | @while_ _ st init test body k _ _ _ iht ihb ihk =>
      intro onRet R hon B t m
      dsimp only [Cmd.toExprWith, loop1, LeanQbe.T.wp, Closed, Cmd.wp]
      have hinner : ∀ (J : Cont st) (s : Tup Val st) (t' : TraceB) (m' : Mem 64),
          (∀ Hs : Tup Cont [[.bool]],
            ((∀ (b : Tup Val [.bool]) m₁,
              ((b.1 = true →
                  LeanQbe.T.wp Γ Q X ((body s).toExprWith cfg (fun s' => .jump J s')) m₁) ∧
               (b.1 = false →
                  LeanQbe.T.wp Γ Q X ((k s).toExprWith cfg onRet) m₁)) → Hs.1 b m₁) ∧
              True) →
            LeanQbe.T.wp Γ Q X ((test s).toExprWith cfg (fun b => .jump Hs.1 b)) m') ↔
          Cmd.wp extEmpty (EnvB.ofTEnv Γ X) (rs := [.bool]) B
            (fun (b, ()) t₁ m₁ =>
              (b = true → Cmd.wp extEmpty (EnvB.ofTEnv Γ X) B
                (fun s' _ m₂ => J s' m₂) (body s) t₁ m₁) ∧
              (b = false → Cmd.wp extEmpty (EnvB.ofTEnv Γ X) B
                (fun vs _ m₂ => R vs m₂) (k s) t₁ m₁))
            (test s) t' m' := by
        intro J s t' m'
        let H₀ : Cont [.bool] := fun b m₁ =>
          (b.1 = true → LeanQbe.T.wp Γ Q X ((body s).toExprWith cfg (fun s' => .jump J s')) m₁) ∧
          (b.1 = false → LeanQbe.T.wp Γ Q X ((k s).toExprWith cfg onRet) m₁)
        constructor
        · intro hH
          have ht1 := hH (H₀, ()) ⟨fun _ _ h => h, trivial⟩
          have ht2 := (iht s (fun b => .jump H₀ b) H₀ (fun _ _ => Iff.rfl) B t' m').1 ht1
          refine Cmd.wp_mono (fun (b, ()) t₁ m₁ ⟨hb1, hb2⟩ => ⟨fun hb => ?_, fun hb => ?_⟩)
            (test s) t' m' ht2
          · exact (ihb s (fun s' => .jump J s') J (fun _ _ => Iff.rfl) B t₁ m₁).1 (hb1 hb)
          · exact (ihk s onRet R hon B t₁ m₁).1 (hb2 hb)
        · intro ht ⟨H, ⟨⟩⟩ ⟨hH, _⟩
          have ht' : Cmd.wp extEmpty (EnvB.ofTEnv Γ X) B (fun b _ m₁ => H b m₁) (test s) t' m' := by
            refine Cmd.wp_mono (fun (b, ()) t₁ m₁ ⟨hb1, hb2⟩ => hH (b, ()) m₁ ⟨?_, ?_⟩)
              (test s) t' m' ht
            · intro hb
              exact (ihb s (fun s' => .jump J s') J (fun _ _ => Iff.rfl) B t₁ m₁).2 (hb1 hb)
            · intro hb
              exact (ihk s onRet R hon B t₁ m₁).2 (hb2 hb)
          exact (iht s (fun b => .jump H b) H (fun _ _ => Iff.rfl) B t' m').2 ht'
      constructor
      · intro hloop I hI
        let J : Cont st := fun s m' => ∀ t', I s t' m'
        have hcl : (∀ s m',
            (∀ Hs : Tup Cont [[.bool]],
              ((∀ b m₁,
                ((b.1 = true →
                    LeanQbe.T.wp Γ Q X ((body s).toExprWith cfg (fun s' => .jump J s')) m₁) ∧
                 (b.1 = false →
                    LeanQbe.T.wp Γ Q X ((k s).toExprWith cfg onRet) m₁)) → Hs.1 b m₁) ∧
                True) →
              LeanQbe.T.wp Γ Q X ((test s).toExprWith cfg (fun b => .jump Hs.1 b)) m') → J s m') ∧
            True := by
          refine ⟨fun s m' hs t' => hI s t' m' ?_, trivial⟩
          have ht := (hinner J s t' m').1 hs
          exact Cmd.wp_mono (fun (b, ()) t₁ m₁ ⟨hb1, hb2⟩ =>
            ⟨fun hb => Cmd.wp_mono (fun s' t₂ m₂ hj => hj t₂) (body s) t₁ m₁ (hb1 hb), hb2⟩)
            (test s) t' m' ht
        exact hloop (J, ()) hcl t
      · intro hwhile ⟨J, ⟨⟩⟩ ⟨hJ, _⟩
        refine hwhile (fun s _ m' => J s m') fun s t' m' ht => ?_
        exact hJ s m' ((hinner J s t' m').2 ht)
  | hlt => intro _ _ _ _ _ _; exact Iff.rfl

/-- Top-level pure lowering equivalence: `LeanQbe.T.wp` of `c.toExpr` is equivalent to
`Cmd.wpPure` of `c` on the pure (`NoStackNoIO`) fragment. -/
theorem Cmd.toExpr_wp_iff {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {cfg : LowerCfg} {c : Cmd Val rs} (h : c.NoStackNoIO) (m : Mem 64) :
    LeanQbe.T.wp Γ Q X (c.toExpr cfg) m ↔ Cmd.wpPure Γ Q X c m := by
  constructor
  · intro hw
    exact ⟨0, (Cmd.toExprWith_wp_iff h .ret Q (fun _ _ => Iff.rfl) 0 [] m).1 hw⟩
  · rintro ⟨B, hB⟩
    exact (Cmd.toExprWith_wp_iff h .ret Q (fun _ _ => Iff.rfl) B [] m).2 hB

/-- Closed-function lowering correctness: `Func.wp` of `f.toFunc` equals `FuncB.wpPure f`. -/
theorem FuncB.toFunc_wp_iff {as rs : List Ty} {Γ : Env} {f : FuncB as rs}
    (h : ∀ xs : Tup Val as, (f Val xs).NoStackNoIO)
    (xs : Tup Val as) (m : Mem 64) (Q : Post rs) (X : XPost)
    (cfg : LowerCfg := LowerCfg.default) :
    Func.wp Γ (f.toFunc cfg) xs m Q X ↔ FuncB.wpPure Γ f xs m Q X :=
  Cmd.toExpr_wp_iff (h xs) m

/-- Alias matching `toFunc_wp_iff` naming convention. -/
theorem toFunc_wp_iff {as rs : List Ty} {Γ : Env} {f : FuncB as rs}
    (h : ∀ xs : Tup Val as, (f Val xs).NoStackNoIO)
    (xs : Tup Val as) (m : Mem 64) (Q : Post rs) (X : XPost)
    (cfg : LowerCfg := LowerCfg.default) :
    Func.wp Γ (toFunc f cfg) xs m Q X ↔ FuncB.wpPure Γ f xs m Q X :=
  FuncB.toFunc_wp_iff h xs m Q X cfg

/-! ### Full `stackalloc` + `interact` Lowering Contracts & Equivalence -/

/-- `LeanQbe.T.Env` modeling `cfg.allocSym` (`anybytes` + `split`), `cfg.freeSym`
(reclamation), `cfg.ioSym` (external `ExtSpecB` at existential trace), and user callees `Γ`
(at existential budget `< 2 ^ 64` and existential trace). Requires zero symbol-disjointness
hypotheses for soundness `Cmd.wp → LeanQbe.T.wp`. -/
def Env.ofBedrock2Sound (cfg : LowerCfg) (ext : ExtSpecB) (Γ : EnvB) : Env :=
  fun sym as bs args m P E =>
    (∀ g cs xs m', ¬ E g cs xs m') ∧
    ((sym = cfg.allocSym ∧ ∃ (h1 : as = [i64]) (h2 : bs = [i64]),
        ∀ a mStack mComb, anybytes a (h1 ▸ args).1.toNat mStack →
          split mComb m mStack → P (h2 ▸ (a, ())) mComb) ∨
     (sym = cfg.freeSym ∧ ∃ (h1 : as = [i64, i64]) (h2 : bs = []),
        ∃ mSmall' mStack', anybytes (h1 ▸ args).1 (h1 ▸ args).2.1.toNat mStack' ∧
          split m mSmall' mStack' ∧ P (h2 ▸ ()) mSmall') ∨
     (∃ action, sym = cfg.ioSym action ∧
        ∃ t : TraceB, ∃ mKeep mGive mid,
          split m mKeep mGive ∧ ext t mGive action as bs args mid ∧
          ∀ mRec res, mid mRec res → ∀ m', split m' mKeep mRec → P res m') ∨
     (∃ (B : Nat) (t : TraceB) (P' : PostB bs),
        B < 2 ^ 64 ∧ Γ sym as bs B args t m P' ∧ ∀ r t' m', P' r t' m' → P r m'))

/-- Full soundness of `Cmd.toExprWith` for **all** Bedrock2 commands (including `stackalloc`
and `interact`, and arbitrary trace-dependent `ext`, `Γ`, `Q_B`) whenever `B < 2 ^ 64`. -/
theorem Cmd.toExprWith_wp_sound {ext : ExtSpecB} {Γ : EnvB} {cfg : LowerCfg}
    {rs : List Ty} {Q : Post rs} {X : XPost} {mid : List Ty} :
    (c : Cmd Val mid) → ∀ {B : Nat}, B < 2 ^ 64 →
    ∀ (onRet : Tup (Arg Val) mid → Expr Val Cont rs) (R : PostB mid),
    (∀ vs t' m', R (vals vs) t' m' →
      LeanQbe.T.wp (Env.ofBedrock2Sound cfg ext Γ) Q X (onRet vs) m') →
    ∀ (t : TraceB) (m : Mem 64),
    Cmd.wp ext Γ B R c t m →
    LeanQbe.T.wp (Env.ofBedrock2Sound cfg ext Γ) Q X (c.toExprWith cfg onRet) m
  | .ret vs, _, _, _, _, hon, t, m, h => hon vs t m h
  | .let_ _ k, _, hB, onRet, R, hon, t, m, h =>
      Op.wp_mono (fun r hr => Cmd.toExprWith_wp_sound (k r) hB onRet R hon t m hr) h
  | .load _ _ k, _, hB, onRet, R, hon, t, m, h => by
      rcases h with ⟨v, hv, hk⟩
      exact ⟨v, hv, Cmd.toExprWith_wp_sound (k v) hB onRet R hon t m hk⟩
  | .store _ _ k, _, hB, onRet, R, hon, t, _, h => by
      rcases h with ⟨hok, hk⟩
      exact ⟨hok, Cmd.toExprWith_wp_sound k hB onRet R hon t _ hk⟩
  | .call f _ k, B, hB, onRet, R, hon, t, m, h => by
      rcases h with ⟨P', hcall, hk⟩
      exact ⟨fun r m' => ∃ t', P' r t' m', fun _ _ _ _ => False,
        ⟨fun _ _ _ _ h => h, Or.inr (Or.inr (Or.inr ⟨B, t, P', hB, hcall,
          fun r t' m' hp => ⟨t', hp⟩⟩))⟩,
        fun r m' ⟨t', hp⟩ => Cmd.toExprWith_wp_sound (k r) hB onRet R hon t' m' (hk r t' m' hp),
        fun _ _ _ _ hf => hf.elim⟩
  | .interact action _ k, _, hB, onRet, R, hon, t, m, h => by
      rcases h with ⟨mKeep, mGive, mid, hsp, hx, hk⟩
      exact ⟨fun res m' => ∃ mRec, mid mRec res ∧ split m' mKeep mRec, fun _ _ _ _ => False,
        ⟨fun _ _ _ _ h => h, Or.inr (Or.inr (Or.inl ⟨action, rfl, t, mKeep, mGive, mid,
          hsp, hx, fun mRec res hm m' hsp' => ⟨mRec, hm, hsp'⟩⟩))⟩,
        fun res m' ⟨mRec, hm, hsp'⟩ =>
          Cmd.toExprWith_wp_sound (k res) hB onRet R hon _ m' (hk mRec res hm m' hsp'),
        fun _ _ _ _ hf => hf.elim⟩
  | .stackalloc nbytes body, B, hB, onRet, R, hon, t, mSmall, h => by
      rcases h with ⟨hle, hbody⟩
      have hlt64 : nbytes < 2 ^ 64 := Nat.lt_of_le_of_lt hle hB
      have htoNat : (BitVec.ofNat 64 nbytes).toNat = nbytes := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]
      dsimp only [Cmd.toExprWith]
      simp only [hlt64, ↓reduceIte]
      refine ⟨fun (a, ()) mComb => ∃ mStack, anybytes a nbytes mStack ∧ split mComb mSmall mStack,
        fun _ _ _ _ => False,
        ⟨fun _ _ _ _ h => h, Or.inl ⟨rfl, rfl, rfl, fun a mStack mComb hany hsp =>
          ⟨mStack, htoNat ▸ hany, hsp⟩⟩⟩, ?_, fun _ _ _ _ hf => hf.elim⟩
      rintro ⟨a, ⟨⟩⟩ mComb ⟨mStack, hany, hsp⟩ ⟨J, ⟨⟩⟩ ⟨hJ, _⟩
      have hsubB : B - nbytes < 2 ^ 64 := by omega
      refine Cmd.toExprWith_wp_sound (body a) hsubB (fun vs => .jump J vs)
        (fun vs _ mComb' => J vs mComb')
        (fun _ _ _ hj => hj) t mComb ?_
      refine Cmd.wp_mono (fun vs t' mComb' ⟨mSmall', mStack', ha', hs', hq⟩ => ?_)
        (body a) t mComb (hbody a mStack mComb hany hsp)
      refine hJ vs mComb' ⟨fun () mS => LeanQbe.T.wp (Env.ofBedrock2Sound cfg ext Γ) Q X
          (onRet (Tup.toArgs vs)) mS, fun _ _ _ _ => False,
        ⟨fun _ _ _ _ h => h, Or.inr (Or.inl ⟨rfl, rfl, rfl, mSmall', mStack',
          htoNat.symm ▸ ha', hs', ?_⟩)⟩,
        fun () _ h => h, fun _ _ _ _ hf => hf.elim⟩
      have hvs : vals (Tup.toArgs vs) = vs := vals_toArgs vs
      exact hon (Tup.toArgs vs) t' mSmall' (by rw [hvs]; exact hq)
  | .seq c₁ c₂, _, hB, onRet, R, hon, t, m, h => by
      dsimp only [Cmd.toExprWith, LeanQbe.T.wp, Closed]
      intro ⟨J, ⟨⟩⟩ ⟨hJ, _⟩
      refine Cmd.toExprWith_wp_sound c₁ hB (fun vs => .jump J vs)
        (fun vs _ m' => J vs m') (fun _ _ _ hj => hj) t m ?_
      exact Cmd.wp_mono (fun mid t' m' hm =>
        hJ mid m' (Cmd.toExprWith_wp_sound (c₂ mid) hB onRet R hon t' m' hm)) c₁ t m h
  | .cond _ tBr eBr, _, hB, onRet, R, hon, t, m, h => by
      rcases h with ⟨ht, he⟩
      exact ⟨fun hc => Cmd.toExprWith_wp_sound tBr hB onRet R hon t m (ht hc),
        fun hc => Cmd.toExprWith_wp_sound eBr hB onRet R hon t m (he hc)⟩
  | .while_ _ test body k, _, hB, onRet, R, hon, t, m, h => by
      dsimp only [Cmd.toExprWith, loop1, LeanQbe.T.wp, Closed]
      intro ⟨J, ⟨⟩⟩ ⟨hJ, _⟩
      refine h (fun s _ m' => J s m') fun s t' m' ht => hJ s m' ?_
      intro ⟨H, ⟨⟩⟩ ⟨hH, _⟩
      refine Cmd.toExprWith_wp_sound (test s) hB (fun b => .jump H b)
        (fun b _ m₁ => H b m₁) (fun _ _ _ hh => hh) t' m' ?_
      refine Cmd.wp_mono (fun (b, ()) t₁ m₁ ⟨hb1, hb2⟩ => hH (b, ()) m₁ ⟨?_, ?_⟩) (test s) t' m' ht
      · intro hb
        exact Cmd.toExprWith_wp_sound (body s) hB (fun s' => .jump J s')
          (fun s' _ m₂ => J s' m₂) (fun _ _ _ hj => hj) t₁ m₁ (hb1 hb)
      · intro hb
        exact Cmd.toExprWith_wp_sound (k s) hB onRet R hon t₁ m₁ (hb2 hb)
  | .hlt, _, _, _, _, _, _, _, h => h.elim

/-- Closed-function full lowering soundness (including `stackalloc` and `interact`). -/
theorem FuncB.toFunc_wp_sound {as rs : List Ty} {ext : ExtSpecB} {Γ : EnvB}
    {f : FuncB as rs} {B : Nat} (hB : B < 2 ^ 64) (xs : Tup Val as) (t : TraceB) (m : Mem 64)
    {Q : PostB rs} {Q' : Post rs} (X : XPost)
    (hQ : ∀ vs t' m', Q vs t' m' → Q' vs m')
    (hw : FuncB.wp ext Γ f B xs t m Q) (cfg : LowerCfg := LowerCfg.default) :
    Func.wp (Env.ofBedrock2Sound cfg ext Γ) (f.toFunc cfg) xs m Q' X :=
  Cmd.toExprWith_wp_sound (f Val xs) hB .ret Q (fun vs t' m' h => hQ (vals vs) t' m' h) t m hw

/-! ### Trace-independent exact `↔` for full `Cmd` (including `stackalloc` & `interact`) -/

/-- Trace-independence of an `ExtSpecB`. -/
def ExtSpecB.TraceIndep (ext : ExtSpecB) : Prop :=
  ∀ t₁ t₂ mGive a as bs args mid, ext t₁ mGive a as bs args mid → ext t₂ mGive a as bs args mid

/-- Unbudgeted lifting of `LeanQbe.T.Env` (plus exit postcondition `X`) for `Cmd.wpUnbounded`. -/
def EnvB.ofTEnvU (Γ : Env) (X : XPost) :
    Sym → (as rs : List Ty) → Tup Val as → TraceB → Mem 64 → PostB rs → Prop :=
  fun f as bs args t m P =>
    ∃ (P' : Post bs) (E : XPost),
      Γ f as bs args m P' E ∧
      (∀ r m', P' r m' → P r t m') ∧
      (∀ g cs xs m', E g cs xs m' → X g cs xs m')

/-- Trace-independent `LeanQbe.T.Env` extending `(Γ, X)` with `stackalloc` (`cfg.allocSym` /
`cfg.freeSym`) and `interact` (`cfg.ioSym`). -/
def Env.ofBedrock2 (cfg : LowerCfg) (ext : ExtSpecB) (Γ : Env) : Env :=
  fun sym as bs args m P E =>
    (sym = cfg.allocSym ∧ ∃ (h1 : as = [i64]) (h2 : bs = [i64]),
      (∀ g cs xs m', ¬ E g cs xs m') ∧
      ∀ a mStack mComb, anybytes a (h1 ▸ args).1.toNat mStack →
        split mComb m mStack → P (h2 ▸ (a, ())) mComb) ∨
    (sym = cfg.freeSym ∧ ∃ (h1 : as = [i64, i64]) (h2 : bs = []),
      (∀ g cs xs m', ¬ E g cs xs m') ∧
      ∃ mSmall' mStack', anybytes (h1 ▸ args).1 (h1 ▸ args).2.1.toNat mStack' ∧
        split m mSmall' mStack' ∧ P (h2 ▸ ()) mSmall') ∨
    (∃ action, sym = cfg.ioSym action ∧
      (∀ g cs xs m', ¬ E g cs xs m') ∧
      ∀ t : TraceB, ∃ mKeep mGive mid,
        split m mKeep mGive ∧ ext t mGive action as bs args mid ∧
        ∀ mRec res, mid mRec res → ∀ m', split m' mKeep mRec → P res m') ∨
    Γ sym as bs args m P E

/-- Disjointness conditions ensuring `cfg.allocSym`, `cfg.freeSym`, `cfg.ioSym`, and user
function symbols in `Γ` do not collide in `Env.ofBedrock2`. -/
structure LowerEnvValid (cfg : LowerCfg) (ext : ExtSpecB) (Γ : Env) : Prop where
  alloc_ne_free : cfg.allocSym ≠ cfg.freeSym
  alloc_ne_io : ∀ a, cfg.allocSym ≠ cfg.ioSym a
  free_ne_io : ∀ a, cfg.freeSym ≠ cfg.ioSym a
  io_inj : ∀ a₁ a₂, cfg.ioSym a₁ = cfg.ioSym a₂ → a₁ = a₂
  alloc_not_user : ∀ as bs args m P E, ¬ Γ cfg.allocSym as bs args m P E
  free_not_user : ∀ as bs args m P E, ¬ Γ cfg.freeSym as bs args m P E
  io_not_user : ∀ a as bs args m P E, ¬ Γ (cfg.ioSym a) as bs args m P E
  user_not_ext : ∀ f t mGive as bs args mid,
    (∃ args' m' P' E', Γ f as bs args' m' P' E') → ∀ a, f = cfg.ioSym a →
      ¬ ext t mGive a as bs args mid

/-- Syntactic disjointness of user `.call` targets in `c` from `cfg.allocSym`, `cfg.freeSym`,
and `cfg.ioSym _`. -/
inductive Cmd.CallsDisjoint (cfg : LowerCfg) {V : Ty → Type} : {rs : List Ty} → Cmd V rs → Prop
  | ret {rs vs} : Cmd.CallsDisjoint cfg (rs := rs) (.ret vs)
  | let_ {rs ts op k} : (∀ xs, Cmd.CallsDisjoint cfg (k xs)) →
      Cmd.CallsDisjoint cfg (rs := rs) (.let_ (ts := ts) op k)
  | load {rs t a k} : (∀ v, Cmd.CallsDisjoint cfg (k v)) →
      Cmd.CallsDisjoint cfg (rs := rs) (.load t a k)
  | store {rs t v a k} : Cmd.CallsDisjoint cfg k →
      Cmd.CallsDisjoint cfg (rs := rs) (.store (t := t) v a k)
  | call {rs f as bs args k} :
      f ≠ cfg.allocSym → f ≠ cfg.freeSym → (∀ a, f ≠ cfg.ioSym a) →
      (∀ xs, Cmd.CallsDisjoint cfg (k xs)) →
      Cmd.CallsDisjoint cfg (rs := rs) (.call f (as := as) (bs := bs) args k)
  | interact {rs act as bs args k} : (∀ xs, Cmd.CallsDisjoint cfg (k xs)) →
      Cmd.CallsDisjoint cfg (rs := rs) (.interact act (as := as) (bs := bs) args k)
  | stackalloc {rs n body} : (∀ a, Cmd.CallsDisjoint cfg (body a)) →
      Cmd.CallsDisjoint cfg (rs := rs) (.stackalloc n body)
  | seq {rs mid c₁ c₂} : Cmd.CallsDisjoint cfg c₁ → (∀ xs, Cmd.CallsDisjoint cfg (c₂ xs)) →
      Cmd.CallsDisjoint cfg (rs := rs) (.seq (mid := mid) c₁ c₂)
  | cond {rs c t e} : Cmd.CallsDisjoint cfg t → Cmd.CallsDisjoint cfg e →
      Cmd.CallsDisjoint cfg (rs := rs) (.cond c t e)
  | while_ {rs st init test body k} :
      (∀ xs, Cmd.CallsDisjoint cfg (test xs)) →
      (∀ xs, Cmd.CallsDisjoint cfg (body xs)) →
      (∀ xs, Cmd.CallsDisjoint cfg (k xs)) →
      Cmd.CallsDisjoint cfg (rs := rs) (.while_ (st := st) init test body k)
  | hlt {rs} : Cmd.CallsDisjoint cfg (rs := rs) .hlt

private theorem wpUnbounded_trace_indep {ext : ExtSpecB} {Γ : Env} {X : XPost}
    (hext : ext.TraceIndep) :
    {rs : List Ty} → (c : Cmd Val rs) →
    ∀ {Q : Tup Val rs → Mem 64 → Prop} (t₁ t₂ : TraceB) (m : Mem 64),
    Cmd.wpUnbounded ext (EnvB.ofTEnvU Γ X) (fun vs _ m' => Q vs m') c t₁ m →
    Cmd.wpUnbounded ext (EnvB.ofTEnvU Γ X) (fun vs _ m' => Q vs m') c t₂ m
  | _, .ret _, _, _, _, _, h => h
  | _, .let_ _ k, _, t₁, t₂, m, h =>
      Op.wp_mono (fun r hr => wpUnbounded_trace_indep hext (k r) t₁ t₂ m hr) h
  | _, .load _ _ k, _, t₁, t₂, m, h => by
      rcases h with ⟨v, hv, hk⟩
      exact ⟨v, hv, wpUnbounded_trace_indep hext (k v) t₁ t₂ m hk⟩
  | _, .store _ _ k, _, t₁, t₂, _, h => by
      rcases h with ⟨hok, hk⟩
      exact ⟨hok, wpUnbounded_trace_indep hext k t₁ t₂ _ hk⟩
  | _, .call _ _ k, _, t₁, t₂, m, h => by
      rcases h with ⟨P, ⟨P', E', hΓ, hP', hE'⟩, hk⟩
      exact ⟨fun r _ m' => P' r m', ⟨P', E', hΓ, fun _ _ hp => hp, hE'⟩,
        fun r t' m' hp =>
          wpUnbounded_trace_indep hext (k r) t₁ t' m' (hk r t₁ m' (hP' r m' hp))⟩
  | _, .interact _ _ k, _, t₁, t₂, m, h => by
      rcases h with ⟨mKeep, mGive, mid, hsp, hx, hk⟩
      exact ⟨mKeep, mGive, mid, hsp, hext t₁ t₂ _ _ _ _ _ _ hx,
        fun mRec res hm m' hsp' =>
          wpUnbounded_trace_indep hext (k res) _ _ m' (hk mRec res hm m' hsp')⟩
  | _, .stackalloc _ body, _, t₁, t₂, _, h => by
      rcases h with ⟨hlt, hbody⟩
      exact ⟨hlt, fun a mStack mComb hany hsp =>
        wpUnbounded_trace_indep hext (body a) t₁ t₂ mComb (hbody a mStack mComb hany hsp)⟩
  | _, .seq c₁ c₂, Q, t₁, t₂, m, h => by
      refine Cmd.wpUnbounded_mono (fun mid t' m' hm => ?_) c₁ t₂ m
        (wpUnbounded_trace_indep hext c₁
          (Q := fun mid m' => ∀ t'', Cmd.wpUnbounded ext (EnvB.ofTEnvU Γ X)
            (fun vs _ m'' => Q vs m'') (c₂ mid) t'' m')
          t₁ t₂ m ?_)
      · exact hm t'
      · exact Cmd.wpUnbounded_mono (fun mid t' m' hm t'' =>
          wpUnbounded_trace_indep hext (c₂ mid) t' t'' m' hm) c₁ t₁ m h
  | _, .cond _ tBr eBr, _, t₁, t₂, m, h => by
      rcases h with ⟨ht, he⟩
      exact ⟨fun hc => wpUnbounded_trace_indep hext tBr t₁ t₂ m (ht hc),
        fun hc => wpUnbounded_trace_indep hext eBr t₁ t₂ m (he hc)⟩
  | _, .while_ _ test body k, Q, t₁, t₂, m, h => by
      intro I hI
      refine h (fun s _ m' => ∀ t', I s t' m') (fun s t' m' ht t'' => hI s t'' m' ?_) t₂
      have ht' := wpUnbounded_trace_indep hext (test s)
        (Q := fun x m₁ =>
          (x.1 = true → ∀ t₂, Cmd.wpUnbounded ext (EnvB.ofTEnvU Γ X)
            (fun s' _ m₂ => ∀ t₃, I s' t₃ m₂) (body s) t₂ m₁) ∧
          (x.1 = false → ∀ t₂, Cmd.wpUnbounded ext (EnvB.ofTEnvU Γ X)
            (fun vs _ m₂ => Q vs m₂) (k s) t₂ m₁))
        t' t'' m'
        (Cmd.wpUnbounded_mono (fun (b, ()) t₁ m₁ ⟨hb1, hb2⟩ =>
          ⟨fun hb t₂ => wpUnbounded_trace_indep hext (body s) t₁ t₂ m₁ (hb1 hb),
           fun hb t₂ => wpUnbounded_trace_indep hext (k s) t₁ t₂ m₁ (hb2 hb)⟩)
          (test s) t' m' ht)
      exact Cmd.wpUnbounded_mono (fun (b, ()) t₁ m₁ ⟨hb1, hb2⟩ =>
        ⟨fun hb => Cmd.wpUnbounded_mono (fun s' t₃ m₂ h => h t₃) (body s) t₁ m₁ (hb1 hb t₁),
         fun hb => hb2 hb t₁⟩) (test s) t'' m' ht'
  | _, .hlt, _, _, _, _, h => h

/-- Exact bidirectional equivalence between `LeanQbe.T.wp` and `Cmd.wpUnbounded` for the
**entire** Bedrock2 command language (including `stackalloc` and `interact`), under
trace-independence of `ext` and symbol disjointness (`LowerEnvValid` + `CallsDisjoint`). -/
theorem Cmd.toExprWith_wpUnbounded_iff {ext : ExtSpecB} {Γ : Env} {rs : List Ty}
    {Q : Post rs} {X : XPost} {cfg : LowerCfg}
    (hext : ext.TraceIndep) (hval : LowerEnvValid cfg ext Γ)
    {mid : List Ty} {c : Cmd Val mid} (hc : c.CallsDisjoint cfg) :
    ∀ (onRet : Tup (Arg Val) mid → Expr Val Cont rs) (R : Post mid),
    (∀ vs m, LeanQbe.T.wp (Env.ofBedrock2 cfg ext Γ) Q X (onRet vs) m ↔ R (vals vs) m) →
    ∀ (t : TraceB) (m : Mem 64),
    LeanQbe.T.wp (Env.ofBedrock2 cfg ext Γ) Q X (c.toExprWith cfg onRet) m ↔
      Cmd.wpUnbounded ext (EnvB.ofTEnvU Γ X) (fun vs _ m' => R vs m') c t m := by
  induction hc with
  | ret =>
      intro onRet R hon _ m
      exact hon _ m
  | let_ _ ih =>
      intro onRet R hon t m
      dsimp only [Cmd.toExprWith, LeanQbe.T.wp, Cmd.wpUnbounded]
      exact ⟨Op.wp_mono fun r hr => (ih r onRet R hon t m).1 hr,
        Op.wp_mono fun r hr => (ih r onRet R hon t m).2 hr⟩
  | load _ ih =>
      intro onRet R hon t m
      dsimp only [Cmd.toExprWith, LeanQbe.T.wp, Cmd.wpUnbounded]
      exact exists_congr fun v => and_congr_right fun _ => ih v onRet R hon t m
  | store _ ih =>
      intro onRet R hon t _
      dsimp only [Cmd.toExprWith, LeanQbe.T.wp, Cmd.wpUnbounded]
      exact and_congr_right fun _ => ih onRet R hon t _
  | @call _ f as bs args k hna hnf hnio _ ih =>
      intro onRet R hon t m
      dsimp only [Cmd.toExprWith, LeanQbe.T.wp, Cmd.wpUnbounded, Env.ofBedrock2, EnvB.ofTEnvU]
      constructor
      · rintro ⟨P', E', hΓ, hP', hE'⟩
        rcases hΓ with ⟨hf, _⟩ | ⟨hf, _⟩ | ⟨act, hf, _⟩ | hΓ
        · exact absurd hf hna
        · exact absurd hf hnf
        · exact absurd hf (hnio act)
        · refine ⟨fun r _ m' => P' r m', ⟨P', E', hΓ, fun _ _ hp => hp, hE'⟩, ?_⟩
          intro r t' m' hp
          exact (ih r onRet R hon t' m').1 (hP' r m' hp)
      · rintro ⟨P, ⟨P', E', hΓ, hPP', hE'⟩, hk⟩
        refine ⟨P', E', Or.inr (Or.inr (Or.inr hΓ)), fun r m' hp => ?_, hE'⟩
        exact (ih r onRet R hon t m').2 (hk r t m' (hPP' r m' hp))
  | @interact _ act as bs args k _ ih =>
      intro onRet R hon t m
      dsimp only [Cmd.toExprWith, LeanQbe.T.wp, Cmd.wpUnbounded, Env.ofBedrock2]
      constructor
      · rintro ⟨P', E', hΓ, hP', _⟩
        rcases hΓ with ⟨ha, _⟩ | ⟨ha, _⟩ | ⟨act', ha, _, hio⟩ | hΓ
        · exact absurd ha.symm (hval.alloc_ne_io act)
        · exact absurd ha.symm (hval.free_ne_io act)
        · obtain rfl := hval.io_inj _ _ ha
          obtain ⟨mKeep, mGive, mid', hsp, hx, hrec⟩ := hio t
          refine ⟨mKeep, mGive, mid', hsp, hx, fun mRec res hm m' hsp' => ?_⟩
          exact (ih res onRet R hon _ m').1 (hP' res m' (hrec mRec res hm m' hsp'))
        · exact absurd hΓ (hval.io_not_user act _ _ _ _ _ _)
      · rintro ⟨mKeep, mGive, mid', hsp, hx, hk⟩
        refine ⟨fun res m' => ∃ mRec, mid' mRec res ∧ split m' mKeep mRec, fun _ _ _ _ => False,
          Or.inr (Or.inr (Or.inl ⟨act, rfl, fun _ _ _ _ h => h, fun t' =>
            ⟨mKeep, mGive, mid', hsp, hext t t' mGive act as bs (vals args) mid' hx,
              fun mRec res hm m' hsp' => ⟨mRec, hm, hsp'⟩⟩⟩)),
          fun res m' ⟨mRec, hm, hsp'⟩ => ?_, fun _ _ _ _ hf => hf.elim⟩
        exact (ih res onRet R hon _ m').2 (hk mRec res hm m' hsp')
  | @stackalloc mid' nbytes body _ ih =>
      intro onRet R hon t mSmall
      dsimp only [Cmd.toExprWith, Cmd.wpUnbounded]
      by_cases hlt64 : nbytes < 2 ^ 64
      · have htoNat : (BitVec.ofNat 64 nbytes).toNat = nbytes := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64]
        split
        · dsimp only [LeanQbe.T.wp, Closed, Env.ofBedrock2]
          constructor
          · rintro ⟨P', E', hΓ, hP', _⟩
            rcases hΓ with ⟨_, _, _, _, halloc⟩ | ⟨heq, _⟩ | ⟨act, heq, _⟩ | hΓ
            · refine ⟨hlt64, fun a mStack mComb hany hsp => ?_⟩
              have hp := halloc a mStack mComb (htoNat.symm ▸ hany) hsp
              have hgrp := hP' (a, ()) mComb hp
              let J : Cont mid' := fun vs mComb' =>
                ∃ mSmall' mStack', anybytes a nbytes mStack' ∧
                  split mComb' mSmall' mStack' ∧ R vs mSmall'
              have hcl :
                  Closed (Env.ofBedrock2 cfg ext Γ) Q X
                    (Blocks.cons (fun (xs : Tup Val mid') =>
                      .call cfg.freeSym (as := [i64, i64]) (bs := [])
                        (.var a, .imm (BitVec.ofNat 64 nbytes), ())
                        fun () => onRet (Tup.toArgs xs)) .nil)
                    (J, ()) := by
                refine ⟨fun xs mComb' ⟨P'', E'', hΓ', hP'', _⟩ => ?_, trivial⟩
                rcases hΓ' with ⟨heq, _⟩ | ⟨_, _, _, _, mSmall', mStack', ha', hs', hp''⟩ |
                    ⟨act, heq, _⟩ | hΓ'
                · exact absurd heq.symm hval.alloc_ne_free
                · have hret := (hon (Tup.toArgs xs) mSmall').1 (hP'' () mSmall' hp'')
                  rw [vals_toArgs] at hret
                  exact ⟨mSmall', mStack', htoNat ▸ ha', hs', hret⟩
                · exact absurd heq (hval.free_ne_io act)
                · exact absurd hΓ' (hval.free_not_user _ _ _ _ _ _)
              have hb := hgrp (J, ()) hcl
              exact (ih a (fun vs => .jump J vs) J (fun _ _ => Iff.rfl) t mComb).1 hb
            · exact absurd heq hval.alloc_ne_free
            · exact absurd heq (hval.alloc_ne_io act)
            · exact absurd hΓ (hval.alloc_not_user _ _ _ _ _ _)
          · rintro ⟨_, hbody⟩
            refine ⟨fun (a, ()) mComb =>
                ∃ mStack, anybytes a nbytes mStack ∧ split mComb mSmall mStack,
              fun _ _ _ _ => False,
              Or.inl ⟨rfl, rfl, rfl, fun _ _ _ _ h => h, fun a mStack mComb hany hsp =>
                ⟨mStack, htoNat ▸ hany, hsp⟩⟩, ?_, fun _ _ _ _ hf => hf.elim⟩
            rintro ⟨a, ⟨⟩⟩ mComb ⟨mStack, hany, hsp⟩ ⟨J, ⟨⟩⟩ ⟨hJ, _⟩
            have hb := (ih a (fun vs => .jump J vs) J (fun _ _ => Iff.rfl) t mComb).2
            refine hb (Cmd.wpUnbounded_mono
              (fun vs t' mComb' ⟨mSmall', mStack', ha', hs', hq⟩ => ?_)
              (body a) t mComb (hbody a mStack mComb hany hsp))
            refine hJ vs mComb' ⟨fun () mS =>
                LeanQbe.T.wp (Env.ofBedrock2 cfg ext Γ) Q X (onRet (Tup.toArgs vs)) mS,
              fun _ _ _ _ => False,
              Or.inr (Or.inl ⟨rfl, rfl, rfl, fun _ _ _ _ h => h, mSmall', mStack',
                htoNat.symm ▸ ha', hs', ?_⟩),
              fun () _ h => h, fun _ _ _ _ hf => hf.elim⟩
            have hvs : vals (Tup.toArgs vs) = vs := vals_toArgs vs
            exact (hon (Tup.toArgs vs) mSmall').2 (by rw [hvs]; exact hq)
        · contradiction
      · split
        · contradiction
        · exact ⟨fun h => h.elim, fun ⟨h, _⟩ => absurd h hlt64⟩
  | @seq _ mid' c₁ c₂ _ _ ih₁ ih₂ =>
      intro onRet R hon t m
      dsimp only [Cmd.toExprWith, LeanQbe.T.wp, Closed, Cmd.wpUnbounded]
      let J₀ : Cont mid' := fun xs m' =>
        LeanQbe.T.wp (Env.ofBedrock2 cfg ext Γ) Q X ((c₂ xs).toExprWith cfg onRet) m'
      constructor
      · intro hgrp
        have h1 := hgrp (J₀, ()) ⟨fun _ _ h => h, trivial⟩
        have hc1 := (ih₁ (fun vs => .jump J₀ vs) J₀ (fun _ _ => Iff.rfl) t m).1 h1
        exact Cmd.wpUnbounded_mono (fun xs t' m' hj => (ih₂ xs onRet R hon t' m').1 hj) _ t m hc1
      · intro hc1 ⟨J, ⟨⟩⟩ ⟨hJ, _⟩
        have hc1' := Cmd.wpUnbounded_mono
          (fun xs t' m' hc2 => hJ xs m' ((ih₂ xs onRet R hon t' m').2 hc2)) _ t m hc1
        exact (ih₁ (fun vs => .jump J vs) J (fun _ _ => Iff.rfl) t m).2 hc1'
  | cond _ _ iht ihe =>
      intro onRet R hon t m
      dsimp only [Cmd.toExprWith, LeanQbe.T.wp, Cmd.wpUnbounded]
      exact and_congr
        (imp_congr_right fun _ => iht onRet R hon t m)
        (imp_congr_right fun _ => ihe onRet R hon t m)
  | @while_ _ st init test body k _ _ _ iht ihb ihk =>
      intro onRet R hon t m
      dsimp only [Cmd.toExprWith, loop1, LeanQbe.T.wp, Closed, Cmd.wpUnbounded]
      have hinner : ∀ (J : Cont st) (s : Tup Val st) (t' : TraceB) (m' : Mem 64),
          (∀ Hs : Tup Cont [[.bool]],
            ((∀ (b : Tup Val [.bool]) m₁,
              ((b.1 = true → LeanQbe.T.wp (Env.ofBedrock2 cfg ext Γ) Q X
                  ((body s).toExprWith cfg (fun s' => .jump J s')) m₁) ∧
               (b.1 = false → LeanQbe.T.wp (Env.ofBedrock2 cfg ext Γ) Q X
                  ((k s).toExprWith cfg onRet) m₁)) → Hs.1 b m₁) ∧
              True) →
            LeanQbe.T.wp (Env.ofBedrock2 cfg ext Γ) Q X
              ((test s).toExprWith cfg (fun b => .jump Hs.1 b)) m') ↔
          Cmd.wpUnbounded ext (EnvB.ofTEnvU Γ X) (rs := [.bool])
            (fun (b, ()) t₁ m₁ =>
              (b = true → Cmd.wpUnbounded ext (EnvB.ofTEnvU Γ X)
                (fun s' _ m₂ => J s' m₂) (body s) t₁ m₁) ∧
              (b = false → Cmd.wpUnbounded ext (EnvB.ofTEnvU Γ X)
                (fun vs _ m₂ => R vs m₂) (k s) t₁ m₁))
            (test s) t' m' := by
        intro J s t' m'
        let H₀ : Cont [.bool] := fun b m₁ =>
          (b.1 = true → LeanQbe.T.wp (Env.ofBedrock2 cfg ext Γ) Q X
              ((body s).toExprWith cfg (fun s' => .jump J s')) m₁) ∧
          (b.1 = false → LeanQbe.T.wp (Env.ofBedrock2 cfg ext Γ) Q X
              ((k s).toExprWith cfg onRet) m₁)
        constructor
        · intro hH
          have ht1 := hH (H₀, ()) ⟨fun _ _ h => h, trivial⟩
          have ht2 := (iht s (fun b => .jump H₀ b) H₀ (fun _ _ => Iff.rfl) t' m').1 ht1
          refine Cmd.wpUnbounded_mono (fun (b, ()) t₁ m₁ ⟨hb1, hb2⟩ => ⟨fun hb => ?_, fun hb => ?_⟩)
            (test s) t' m' ht2
          · exact (ihb s (fun s' => .jump J s') J (fun _ _ => Iff.rfl) t₁ m₁).1 (hb1 hb)
          · exact (ihk s onRet R hon t₁ m₁).1 (hb2 hb)
        · intro ht ⟨H, ⟨⟩⟩ ⟨hH, _⟩
          have ht' : Cmd.wpUnbounded ext (EnvB.ofTEnvU Γ X)
              (fun b _ m₁ => H b m₁) (test s) t' m' := by
            refine Cmd.wpUnbounded_mono
              (fun (b, ()) t₁ m₁ ⟨hb1, hb2⟩ => hH (b, ()) m₁ ⟨?_, ?_⟩)
              (test s) t' m' ht
            · intro hb
              exact (ihb s (fun s' => .jump J s') J (fun _ _ => Iff.rfl) t₁ m₁).2 (hb1 hb)
            · intro hb
              exact (ihk s onRet R hon t₁ m₁).2 (hb2 hb)
          exact (iht s (fun b => .jump H b) H (fun _ _ => Iff.rfl) t' m').2 ht'
      constructor
      · intro hloop I hI
        let J : Cont st := fun s m' => ∀ t', I s t' m'
        have hcl : (∀ s m',
            (∀ Hs : Tup Cont [[.bool]],
              ((∀ b m₁,
                ((b.1 = true → LeanQbe.T.wp (Env.ofBedrock2 cfg ext Γ) Q X
                    ((body s).toExprWith cfg (fun s' => .jump J s')) m₁) ∧
                 (b.1 = false → LeanQbe.T.wp (Env.ofBedrock2 cfg ext Γ) Q X
                    ((k s).toExprWith cfg onRet) m₁)) → Hs.1 b m₁) ∧
                True) →
              LeanQbe.T.wp (Env.ofBedrock2 cfg ext Γ) Q X
                ((test s).toExprWith cfg (fun b => .jump Hs.1 b)) m') → J s m') ∧
            True := by
          refine ⟨fun s m' hs t' => hI s t' m' ?_, trivial⟩
          have ht := (hinner J s t' m').1 hs
          exact Cmd.wpUnbounded_mono (fun (b, ()) t₁ m₁ ⟨hb1, hb2⟩ =>
            ⟨fun hb => Cmd.wpUnbounded_mono
              (fun s' t₂ m₂ hj => hj t₂) (body s) t₁ m₁ (hb1 hb), hb2⟩)
            (test s) t' m' ht
        exact hloop (J, ()) hcl t
      · intro hwhile ⟨J, ⟨⟩⟩ ⟨hJ, _⟩
        refine hwhile (fun s _ m' => J s m') fun s t' m' ht => ?_
        exact hJ s m' ((hinner J s t' m').2 ht)
  | hlt => intro _ _ _ _ _; exact Iff.rfl

/-- Top-level exact equivalence on the entire Bedrock2 language (`stackalloc` + `interact`). -/
theorem FuncB.toFunc_wpUnbounded_iff {as rs : List Ty} {ext : ExtSpecB} {Γ : Env}
    {f : FuncB as rs} (hext : ext.TraceIndep) (cfg : LowerCfg := LowerCfg.default)
    (hval : LowerEnvValid cfg ext Γ)
    (hc : ∀ xs : Tup Val as, (f Val xs).CallsDisjoint cfg)
    (xs : Tup Val as) (t : TraceB) (m : Mem 64) (Q : Post rs) (X : XPost) :
    Func.wp (Env.ofBedrock2 cfg ext Γ) (f.toFunc cfg) xs m Q X ↔
      FuncB.wpUnbounded ext (EnvB.ofTEnvU Γ X) f xs t m (fun vs _ m' => Q vs m') :=
  Cmd.toExprWith_wpUnbounded_iff hext hval (hc xs) .ret Q (fun _ _ => Iff.rfl) t m

end LeanQbe.T.Bedrock2
