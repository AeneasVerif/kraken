module

public import LeanQbe.T.IfOptLemmas2
import LeanQbe.T.OpsLemmas
import LeanQbe.T.PassEnvKit

/-!
# Correctness of `ifOpt`

Main `WP`, `Wf`, `callsOk`, and `Func.ifOpt` specifications atop `LeanQbe.T.IfOptLemmas2`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

open IfOptImpl

namespace IfOptImpl

/-! ## `callsOk` preservation helpers -/

private theorem mkPairIValArg_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {a b : Ty} (next : Nat) {x : Arg (IVal (fun _ => Unit)) a}
    {y : Arg (IVal (fun _ => Unit)) b}
    {cont : Nat → Arg (IVal (fun _ => Unit)) (.pair a b) →
      Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hcont : ∀ next' r, (cont next' r).callsOk allowed exits) :
    (mkPairIValArg next x y cont).callsOk allowed exits := by
  dsimp only [mkPairIValArg]
  cases iout x <;> cases iout y <;> exact hcont _ _

private theorem splitPairIVal_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {a b : Ty} (next : Nat) (p : Arg (IVal (fun _ => Unit)) (.pair a b))
    {cont : Nat → Arg (IVal (fun _ => Unit)) a → Arg (IVal (fun _ => Unit)) b →
      Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hcont : ∀ next' a₁ b₁, (cont next' a₁ b₁).callsOk allowed exits) :
    (splitPairIVal next p cont).callsOk allowed exits := by
  dsimp only [splitPairIVal]
  cases iout p <;> exact hcont _ _ _

private theorem emitSelectTyIVal_callsOk {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} (c : Arg (fun _ => Unit) .bool) :
    (t : Ty) → (next : Nat) →
    (aT aE : Arg (IVal (fun _ => Unit)) t) →
    {cont : Nat → Arg (IVal (fun _ => Unit)) t → Expr (fun _ => Unit) (fun _ => Unit) rs} →
    (∀ next' r, (cont next' r).callsOk allowed exits) →
    (emitSelectTyIVal c t next aT aE cont).callsOk allowed exits
  | .bool, next, aT, aE, cont, hcont
  | .bits _, next, aT, aE, cont, hcont => by
    dsimp only [emitSelectTyIVal]
    cases fKeyBeq (ikey aT) (ikey aE) <;> exact hcont _ _
  | .float _, next, aT, _, cont, hcont => hcont next aT
  | .pair a b, next, aT, aE, cont, hcont => by
    dsimp only [emitSelectTyIVal]
    cases fKeyBeq (ikey aT) (ikey aE)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine splitPairIVal_callsOk next aT fun _ _ _ => ?_
      refine splitPairIVal_callsOk _ aE fun _ _ _ => ?_
      refine emitSelectTyIVal_callsOk c a _ _ _ fun _ _ => ?_
      refine emitSelectTyIVal_callsOk c b _ _ _ fun _ _ => ?_
      exact mkPairIValArg_callsOk _ hcont
    · exact hcont next aT

private theorem emitSelectTupIVal_callsOk {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} (c : Arg (fun _ => Unit) .bool) :
    (ts : List Ty) → (next : Nat) →
    (asT asE : Tup (Arg (IVal (fun _ => Unit))) ts) →
    {cont : Nat → Tup (Arg (IVal (fun _ => Unit))) ts → Expr (fun _ => Unit) (fun _ => Unit) rs} →
    (∀ next' sel, (cont next' sel).callsOk allowed exits) →
    (emitSelectTupIVal c ts next asT asE cont).callsOk allowed exits
  | [], next, (), (), _, hcont => hcont next ()
  | t :: ts, next, (aT, asT), (aE, asE), _, hcont =>
    emitSelectTyIVal_callsOk c t next aT aE fun _ r =>
      emitSelectTupIVal_callsOk c ts _ asT asE fun next' sel => hcont next' (r, sel)

private theorem emitSelectTy_callsOk {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} (c : Arg (fun _ => Unit) .bool) (t : Ty) (next : Nat)
    (aT aE : Arg (IVal (fun _ => Unit)) t)
    {cont : Nat → Arg (fun _ => Unit) t → Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hcont : ∀ next' r, (cont next' r).callsOk allowed exits) :
    (emitSelectTy c t next aT aE cont).callsOk allowed exits :=
  emitSelectTyIVal_callsOk c t next aT aE fun next' r => hcont next' (iout r)

private theorem emitSelectTup_callsOk {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} (c : Arg (fun _ => Unit) .bool) (ts : List Ty) (next : Nat)
    (asT asE : Tup (Arg (IVal (fun _ => Unit))) ts)
    {cont : Tup (Arg (fun _ => Unit)) ts → Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hcont : ∀ sel, (cont sel).callsOk allowed exits) :
    (emitSelectTup c ts next asT asE cont).callsOk allowed exits :=
  emitSelectTupIVal_callsOk c ts next asT asE fun _ sel => hcont (tupIOut sel)

private theorem hoistStoreTail_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    (jTs : List Ty) :
    ∀ (p : StoreTail) (next : Nat) {e : Expr (IVal (fun _ => Unit)) (JLabel (fun _ => Unit)) rs}
      {cont : Nat → Tup (Arg (IVal (fun _ => Unit))) jTs →
        Expr (fun _ => Unit) (fun _ => Unit) rs},
    (∀ next' args, (cont next' args).callsOk allowed exits) →
    (hoistStoreTail jTs p next e cont).callsOk allowed exits
  | .jump, next, .jump _ _, cont, hcont => by
    dsimp only [hoistStoreTail]
    cases listTyDecEq _ jTs
    · exact trivial
    · exact hcont _ _
  | .ret, next, .ret _, cont, hcont => by
    dsimp only [hoistStoreTail]
    cases listTyDecEq rs jTs
    · exact trivial
    · exact hcont _ _
  | .let_ rest, next, .let_ _ _, cont, hcont =>
    hoistStoreTail_callsOk jTs rest _ hcont
  | .jump, _, .let_ _ _, _, _ | .jump, _, .load _ _ _, _, _ | .jump, _, .store _ _ _, _, _
  | .jump, _, .call _ _ _, _, _ | .jump, _, .jnz _ _ _, _, _ | .jump, _, .ret _, _, _
  | .jump, _, .exit _ _, _, _ | .jump, _, .hlt, _, _ | .jump, _, .group _ _, _, _
  | .ret, _, .let_ _ _, _, _ | .ret, _, .load _ _ _, _, _ | .ret, _, .store _ _ _, _, _
  | .ret, _, .call _ _ _, _, _ | .ret, _, .jnz _ _ _, _, _ | .ret, _, .jump _ _, _, _
  | .ret, _, .exit _ _, _, _ | .ret, _, .hlt, _, _ | .ret, _, .group _ _, _, _
  | .let_ _, _, .load _ _ _, _, _ | .let_ _, _, .store _ _ _, _, _
  | .let_ _, _, .call _ _ _, _, _ | .let_ _, _, .jnz _ _ _, _, _ | .let_ _, _, .jump _ _, _, _
  | .let_ _, _, .ret _, _, _ | .let_ _, _, .exit _ _, _, _ | .let_ _, _, .hlt, _, _
  | .let_ _, _, .group _ _, _, _ => trivial

private theorem hoistStoreStep_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    (jTs : List Ty) (st : Ty) :
    ∀ (p : StoreStep) (next : Nat) (loads : List ((t : Ty) × IVal (fun _ => Unit) t))
      {e : Expr (IVal (fun _ => Unit)) (JLabel (fun _ => Unit)) rs}
      {cont : Nat → List ((t : Ty) × IVal (fun _ => Unit) t) →
        Arg (IVal (fun _ => Unit)) st → Arg (IVal (fun _ => Unit)) i64 →
        Tup (Arg (IVal (fun _ => Unit))) jTs → Expr (fun _ => Unit) (fun _ => Unit) rs},
    (∀ next' loads' v a args, (cont next' loads' v a args).callsOk allowed exits) →
    (hoistStoreStep jTs st p next loads e cont).callsOk allowed exits
  | .let_ rest, next, loads, .let_ _ _, cont, hcont =>
    hoistStoreStep_callsOk jTs st rest _ loads hcont
  | .loadEmit rest, next, loads, .load t _ _, cont, hcont => by
    dsimp only [hoistStoreStep]
    exact hoistStoreStep_callsOk jTs st rest (next + 1) (loads ++ [⟨t, (.var (), .var next)⟩]) hcont
  | .loadReuse slot rest, next, loads, .load t _ _, cont, hcont => by
    dsimp only [hoistStoreStep]
    cases loads[slot]? with
    | none => exact trivial
    | some entry =>
      rcases entry with ⟨t', _⟩
      dsimp only
      cases tyDecEq t' t with
      | isFalse _ => exact trivial
      | isTrue _ => exact hoistStoreStep_callsOk jTs st rest next loads hcont
  | .store tail, next, loads, .store (t := st') _ _ _, cont, hcont => by
    dsimp only [hoistStoreStep]
    cases tyDecEq st' st with
    | isFalse _ => exact trivial
    | isTrue _ =>
      exact hoistStoreTail_callsOk jTs tail next fun next' args => hcont next' loads _ _ args
  | .let_ _, _, _, .load _ _ _, _, _ | .let_ _, _, _, .store _ _ _, _, _
  | .let_ _, _, _, .call _ _ _, _, _ | .let_ _, _, _, .jnz _ _ _, _, _
  | .let_ _, _, _, .jump _ _, _, _ | .let_ _, _, _, .ret _, _, _
  | .let_ _, _, _, .exit _ _, _, _ | .let_ _, _, _, .hlt, _, _
  | .let_ _, _, _, .group _ _, _, _
  | .loadEmit _, _, _, .let_ _ _, _, _ | .loadEmit _, _, _, .store _ _ _, _, _
  | .loadEmit _, _, _, .call _ _ _, _, _ | .loadEmit _, _, _, .jnz _ _ _, _, _
  | .loadEmit _, _, _, .jump _ _, _, _ | .loadEmit _, _, _, .ret _, _, _
  | .loadEmit _, _, _, .exit _ _, _, _ | .loadEmit _, _, _, .hlt, _, _
  | .loadEmit _, _, _, .group _ _, _, _
  | .loadReuse _ _, _, _, .let_ _ _, _, _ | .loadReuse _ _, _, _, .store _ _ _, _, _
  | .loadReuse _ _, _, _, .call _ _ _, _, _ | .loadReuse _ _, _, _, .jnz _ _ _, _, _
  | .loadReuse _ _, _, _, .jump _ _, _, _ | .loadReuse _ _, _, _, .ret _, _, _
  | .loadReuse _ _, _, _, .exit _ _, _, _ | .loadReuse _ _, _, _, .hlt, _, _
  | .loadReuse _ _, _, _, .group _ _, _, _
  | .store _, _, _, .let_ _ _, _, _ | .store _, _, _, .load _ _ _, _, _
  | .store _, _, _, .call _ _ _, _, _ | .store _, _, _, .jnz _ _ _, _, _
  | .store _, _, _, .jump _ _, _, _ | .store _, _, _, .ret _, _, _
  | .store _, _, _, .exit _ _, _, _ | .store _, _, _, .hlt, _, _
  | .store _, _, _, .group _ _, _, _ => trivial

private theorem hoistStoreArms_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    (jTs : List Ty) (sp : StoreDiamondPlan) (next : Nat)
    (c : Arg (IVal (fun _ => Unit)) .bool)
    (t e : Expr (IVal (fun _ => Unit)) (JLabel (fun _ => Unit)) rs)
    {fin : Tup (Arg (fun _ => Unit)) jTs → Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hfin : ∀ sel, (fin sel).callsOk allowed exits) :
    (hoistStoreArms jTs sp next c t e fin).callsOk allowed exits :=
  hoistStoreStep_callsOk jTs sp.storeTy sp.armT next [] fun next₁ loads₁ vT _ argsT =>
    hoistStoreStep_callsOk jTs sp.storeTy sp.armE next₁ loads₁ fun next₂ _ vE _ argsE =>
      emitSelectTy_callsOk (iout c) sp.storeTy next₂ vT vE fun next₃ _ =>
        emitSelectTup_callsOk (iout c) jTs next₃ argsT argsE hfin

private theorem hoistArm_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    (jTs : List Ty) :
    ∀ (p : ArmPlan) (next : Nat) {e : Expr (IVal (fun _ => Unit)) (JLabel (fun _ => Unit)) rs}
      {cont : Nat → Tup (Arg (IVal (fun _ => Unit))) jTs →
        Expr (fun _ => Unit) (fun _ => Unit) rs},
    (∀ next' args, (cont next' args).callsOk allowed exits) →
    (hoistArm jTs p next e cont).callsOk allowed exits
  | .jump, next, .jump _ _, cont, hcont => by
    dsimp only [hoistArm]
    cases listTyDecEq _ jTs
    · exact trivial
    · exact hcont _ _
  | .ret, next, .ret _, cont, hcont => by
    dsimp only [hoistArm]
    cases listTyDecEq rs jTs
    · exact trivial
    · exact hcont _ _
  | .let_ rest, next, .let_ _ _, cont, hcont =>
    hoistArm_callsOk jTs rest _ hcont
  | .jnz pT pE, next, .jnz c t e, cont, hcont =>
    hoistArm_callsOk jTs pT next (e := t) fun next₁ _ =>
      hoistArm_callsOk jTs pE next₁ (e := e) fun next₂ _ =>
        emitSelectTupIVal_callsOk (iout c) jTs next₂ _ _ hcont
  | .jump, _, .let_ _ _, _, _ | .jump, _, .load _ _ _, _, _ | .jump, _, .store _ _ _, _, _
  | .jump, _, .call _ _ _, _, _ | .jump, _, .jnz _ _ _, _, _ | .jump, _, .ret _, _, _
  | .jump, _, .exit _ _, _, _ | .jump, _, .hlt, _, _ | .jump, _, .group _ _, _, _
  | .ret, _, .let_ _ _, _, _ | .ret, _, .load _ _ _, _, _ | .ret, _, .store _ _ _, _, _
  | .ret, _, .call _ _ _, _, _ | .ret, _, .jnz _ _ _, _, _ | .ret, _, .jump _ _, _, _
  | .ret, _, .exit _ _, _, _ | .ret, _, .hlt, _, _ | .ret, _, .group _ _, _, _
  | .let_ _, _, .load _ _ _, _, _ | .let_ _, _, .store _ _ _, _, _ | .let_ _, _, .call _ _ _, _, _
  | .let_ _, _, .jnz _ _ _, _, _ | .let_ _, _, .jump _ _, _, _ | .let_ _, _, .ret _, _, _
  | .let_ _, _, .exit _ _, _, _ | .let_ _, _, .hlt, _, _ | .let_ _, _, .group _ _, _, _
  | .jnz _ _, _, .let_ _ _, _, _ | .jnz _ _, _, .load _ _ _, _, _
  | .jnz _ _, _, .store _ _ _, _, _ | .jnz _ _, _, .call _ _ _, _, _
  | .jnz _ _, _, .jump _ _, _, _ | .jnz _ _, _, .ret _, _, _ | .jnz _ _, _, .exit _ _, _, _
  | .jnz _ _, _, .hlt, _, _ | .jnz _ _, _, .group _ _, _, _ => trivial

private theorem hoistJnzArms_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    (jTs : List Ty) (pT pE : ArmPlan) (next : Nat) (c : Arg (IVal (fun _ => Unit)) .bool)
    (t e : Expr (IVal (fun _ => Unit)) (JLabel (fun _ => Unit)) rs)
    {fin : Tup (Arg (fun _ => Unit)) jTs → Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hfin : ∀ sel, (fin sel).callsOk allowed exits) :
    (hoistJnzArms jTs pT pE next c t e fin).callsOk allowed exits :=
  hoistArm_callsOk jTs pT next fun next₁ _ =>
    hoistArm_callsOk jTs pE next₁ fun next₂ _ =>
      emitSelectTupIVal_callsOk (iout c) jTs next₂ _ _ fun _ _ => hfin _

private theorem hoistDiamond_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {jTs : List Ty} (jLbl : Unit) :
    ∀ (plan : DiamondPlan) (next : Nat) {G : Ctx (IVal (fun _ => Unit)) (fun _ => Unit)}
      {D : Ctx (JLabel (fun _ => Unit)) (fun _ => Unit)}
      {e₁ : Expr (IVal (fun _ => Unit)) (JLabel (fun _ => Unit)) rs}
      {e₂ : Expr (fun _ => Unit) (fun _ => Unit) rs},
    Wf G D e₁ e₂ → HasDiamondShape jTs plan e₂ → e₂.callsOk allowed exits →
    (hoistDiamond (jTs := jTs) jLbl plan next e₁).callsOk allowed exits
  | .jnz pT pE, next, _, _, _, _, hwf, _, _ => by
    cases hwf with
    | jnz _ _ _ =>
      dsimp only [hoistDiamond]
      exact hoistJnzArms_callsOk jTs pT pE next _ _ _ fun _ => trivial
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => trivial
  | .jnzStore sp, next, _, _, _, _, hwf, _, _ => by
    cases hwf with
    | jnz _ _ _ =>
      dsimp only [hoistDiamond]
      exact hoistStoreArms_callsOk jTs sp next _ _ _ fun _ => trivial
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => trivial
  | .let_ rest, next, _, _, _, _, hwf, hsh, hc => by
    cases hwf with
    | let_ _ hk =>
      exact hoistDiamond_callsOk jLbl rest (next + _)
        (hk (freshIVals _ (Tup.units _) next) (Tup.units _))
        (hsh (Tup.units _)) hc
    | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsh
  | .load rest, next, _, _, _, _, hwf, hsh, hc => by
    cases hwf with
    | load _ _ hk =>
      exact hoistDiamond_callsOk jLbl rest (next + 1)
        (hk (.var (), .var next) ()) (hsh ()) hc
    | let_ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsh
  | .store rest, next, _, _, _, _, hwf, hsh, hc => by
    cases hwf with
    | store _ _ hk => exact hoistDiamond_callsOk jLbl rest next hk hsh hc
    | let_ _ _ | load _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsh
  | .call rest, next, _, _, _, _, hwf, hsh, hc => by
    cases hwf with
    | call _ _ hk =>
      exact ⟨hc.1, hoistDiamond_callsOk jLbl rest (next + _)
        (hk (freshIVals _ (Tup.units _) next) (Tup.units _))
        (hsh (Tup.units _)) hc.2⟩
    | let_ _ _ | load _ _ _ | store _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsh

private theorem ifOptB_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    (bitsOnly : Bool) (depth next : Nat) :
    {sig : List (List Ty)} →
    (bs : Blocks (IVal (fun _ => Unit)) (JLabel (fun _ => Unit)) rs sig) →
    (∀ {ts} (i : Member ts sig) xs,
      (ifOptWith bitsOnly depth (next + ts.length) (bs.get i (freshIVals ts xs next))).callsOk
        allowed exits) →
    (ifOptBWith bitsOnly depth next bs).callsOk allowed exits
  | _, .nil, _ => trivial
  | _, .cons _ bs, h =>
    ⟨h .here (Tup.units _), ifOptB_callsOk bitsOnly depth next bs fun i => h (.there i)⟩

private theorem ifOptWith_group_true_eq {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (depth next : Nat) {sig : List (List Ty)}
    (b : Tup (JLabel L) sig → Blocks (IVal V) (JLabel L) rs sig)
    (k : Tup (JLabel L) sig → Expr (IVal V) (JLabel L) rs) :
    ifOptWith true depth next (.group b k) =
      .group
        (fun Js => ifOptBWith true (depth + sig.length) next (b (tagLabels depth Js)))
        (fun Js => ifOptWith true (depth + sig.length) next (k (tagLabels depth Js))) := by
  cases sig with
  | nil => rfl
  | cons _ s => cases s <;> rfl

/-! ## Diamond hoisting `WP` and jump normalization -/

theorem hoistDiamond_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {jTs : List Ty}
    (j : Cont jTs) :
    ∀ (plan : DiamondPlan) (next : Nat) {ρ : FEnv} {G : Ctx (IVal Val) Val}
      {D : Ctx (JLabel Cont) Cont} {e₁ : Expr (IVal Val) (JLabel Cont) rs}
      {e₂ : Expr Val Cont rs},
    Wf G D e₁ e₂ → DiamondSpec j next ρ plan e₂ → IGood ρ next G → ∀ m,
    wp Γ Q X e₂ m → wp Γ Q X (hoistDiamond j plan next e₁) m
  | .jnz pT pE, next, ρ, _, _, _, _, hwf, hsp, hG, m, hwp => by
    cases hwf with
    | jnz hc ht he =>
      rcases hsp with ⟨hsel, hspT, hspE⟩
      dsimp only [hoistDiamond]
      exact hoistJnzArms_wp (.jump j) hsel pT pE next hc ht he hspT hspE hG hwp fun sel hs => hs
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsp
  | .jnzStore sp, next, ρ, _, _, _, _, hwf, hsp, hG, m, hwp => by
    cases hwf with
    | jnz hc ht he =>
      rcases hsp with ⟨hsel, hsp'⟩
      dsimp only [hoistDiamond]
      exact hoistStoreArms_wp (.jump j) hsel sp next hc ht he hsp' hG hwp fun sel _ hs => hs
    | let_ _ _ | load _ _ _ | store _ _ _ | call _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsp
  | .let_ rest, next, ρ, _, _, _, _, hwf, hsp, hG, m, hwp => by
    cases hwf with
    | let_ hop hk =>
      cases hop with
      | @mk _ _ code _ args₂ hargs =>
        dsimp only [hoistDiamond, wp, Op.wp] at hwp ⊢
        rw [TRel.iout_vals hG hargs]
        exact OpCode.wp_mono code (vals args₂) (fun r hr =>
          hoistDiamond_wp j rest (next + _) (hk (freshIVals _ r next) r)
            (hsp r) (hG.freshIVals r) m hr) hwp
    | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsp
  | .load rest, next, ρ, _, _, _, _, hwf, hsp, hG, m, hwp => by
    cases hwf with
    | load t ha hk =>
      dsimp only [hoistDiamond, wp] at hwp ⊢
      rcases hwp with ⟨v, hv, hk2⟩
      rw [argRel_iout_val hG ha]
      exact ⟨v, hv, hoistDiamond_wp j rest (next + 1) (hk (.var v, .var next) v)
        (hsp v) (hG.freshOne v) m hk2⟩
    | let_ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsp
  | .store rest, next, ρ, _, _, _, _, hwf, hsp, hG, m, hwp => by
    cases hwf with
    | store hv ha hk =>
      dsimp only [hoistDiamond, wp] at hwp ⊢
      rw [argRel_iout_val hG hv, argRel_iout_val hG ha]
      exact ⟨hwp.1, hoistDiamond_wp j rest next hk hsp hG _ hwp.2⟩
    | let_ _ _ | load _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsp
  | .call rest, next, ρ, _, _, _, _, hwf, hsp, hG, m, hwp => by
    cases hwf with
    | call f hargs hk =>
      dsimp only [hoistDiamond, wp] at hwp ⊢
      rcases hwp with ⟨P, E, hΓ, hP, hE⟩
      rw [TRel.iout_vals hG hargs]
      exact ⟨P, E, hΓ, fun r m' hp =>
        hoistDiamond_wp j rest (next + _) (hk (freshIVals _ r next) r)
          (hsp r) (hG.freshIVals r) m' (hP r m' hp), hE⟩
    | let_ _ _ | load _ _ _ | store _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _ | hlt
    | group _ _ => exact False.elim hsp

theorem ifOpt_jump_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} (rs : List Ty)
    {G : Ctx (IVal V₁) (IVal V₂)} {D : Ctx (JLabel L₁) (JLabel L₂)}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} {ts : List Ty}
    {j₁ : JLabel L₁ ts} {j₂ : JLabel L₂ ts}
    {args₁ : Tup (Arg (IVal V₁)) ts} {args₂ : Tup (Arg (IVal V₂)) ts}
    (hj : ⟨ts, j₁, j₂⟩ ∈ D) (hargs : TRel (ArgRel G) args₁ args₂)
    (hG : IRelG G' G) (hD : TagD D D') (bitsOnly : Bool) (depth next : Nat) :
    Wf G' D' (ifOptWith bitsOnly depth next (.jump (rs := rs) j₁ args₁))
             (ifOptWith bitsOnly depth next (.jump (rs := rs) j₂ args₂)) := by
  have hj' := hD _ hj
  cases j₁ <;> cases j₂ <;> dsimp only [ifOptWith, unwrapJLabel] <;> simp_all
  · exact .jump hj' (trel_iout hG hargs)
  · exact .jump hj'.2 (trel_iout hG hargs)

theorem ifOpt_jump_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx (IVal Val) Val} {D : Ctx (JLabel Cont) Cont} {ts : List Ty}
    {j₁ : JLabel Cont ts} {j₂ : Cont ts}
    {args₁ : Tup (Arg (IVal Val)) ts} {args₂ : Tup (Arg Val) ts}
    (hj : ⟨ts, j₁, j₂⟩ ∈ D) (hargs : TRel (ArgRel G) args₁ args₂)
    {ρ : FEnv} {bitsOnly : Bool} {depth next : Nat} (hD : TagContD depth D) (hG : IGood ρ next G)
    {m : Mem 64} (hw : wp Γ Q X (.jump j₂ args₂) m) :
    wp Γ Q X (ifOptWith bitsOnly depth next (.jump j₁ args₁)) m := by
  have hj' := hD.1 _ hj
  cases j₁ with
  | outer l =>
    dsimp only at hj'
    dsimp only [ifOptWith, unwrapJLabel, wp] at hw ⊢
    rw [hj', TRel.iout_vals hG hargs]
    exact hw
  | tag _ l =>
    dsimp only at hj'
    dsimp only [ifOptWith, unwrapJLabel, wp] at hw ⊢
    rw [hj'.2, TRel.iout_vals hG hargs]
    exact hw
  | loc _ => exact False.elim hj'

end IfOptImpl

/-! ## `ifOptWith` `Wf`, `WP`, `callsOk`, and `Func` theorems -/

private theorem iKeyEq_freshIVals_mem {V₁ V₂ : Ty → Type} :
    {ts : List Ty} → (n : Nat) → (xs₁ : Tup V₁ ts) → (xs₂ : Tup V₂ ts) →
    ∀ p ∈ Tup.zip (freshIVals ts xs₁ n) (freshIVals ts xs₂ n), p.2.1.2 = p.2.2.2
  | [], _, (), (), _, hp => nomatch hp
  | _ :: _, n, (_, xs₁), (_, xs₂), p, hp => by
    cases hp with
    | head => rfl
    | tail _ hp => exact iKeyEq_freshIVals_mem (n + 1) xs₁ xs₂ p hp

private theorem iKeyEq_freshIVals {V₁ V₂ : Ty → Type} {G : Ctx (IVal V₁) (IVal V₂)}
    (hG : IKeyEq G) (ts : List Ty) (xs₁ : Tup V₁ ts) (xs₂ : Tup V₂ ts) (n : Nat) :
    IKeyEq (Tup.zip (freshIVals ts xs₁ n) (freshIVals ts xs₂ n) ++ G) := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact iKeyEq_freshIVals_mem n xs₁ xs₂ p hp
  · exact hG p hp

private theorem tryPureJnzDiamond_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx (IVal V₁) (IVal V₂)} {D : Ctx (JLabel L₁) (JLabel L₂)}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} {next : Nat}
    {c₁ : Arg (IVal V₁) .bool} {c₂ : Arg (IVal V₂) .bool}
    {t₁ e₁ : Expr (IVal V₁) (JLabel L₁) rs} {t₂ e₂ : Expr (IVal V₂) (JLabel L₂) rs}
    (hc : ArgRel G .bool c₁ c₂) (ht : Wf G D t₁ t₂) (he : Wf G D e₁ e₂)
    (hG : IRelG G' G) (hD : TagD D D') {r₁ : Expr V₁ L₁ rs}
    (h1 : tryPureJnzDiamond true next c₁ t₁ e₁ = some r₁) :
    ∃ r₂, tryPureJnzDiamond true next c₂ t₂ e₂ = some r₂ ∧ Wf G' D' r₁ r₂ := by
  dsimp only [tryPureJnzDiamond] at h1 ⊢
  rcases findFirstJump_eq_of_wf hD 8 ht with ⟨hf1, hf2⟩ | ⟨jTs, jId, l₁, l₂, hf1, hf2, hl⟩
  · rw [hf1] at h1; rw [hf2]; dsimp only at h1 ⊢
    cases hsel : isSelectSigWith true rs with
    | false => rw [hsel] at h1; simp at h1
    | true =>
      rw [hsel] at h1; simp only [↓reduceIte] at h1 ⊢
      rw [checkArm_eq_of_wf .ret ht (TagD.checkArm_compat hD) 2 4 next,
          checkArm_eq_of_wf .ret he (TagD.checkArm_compat hD) 2 4 next] at h1
      cases h1t : checkArm .ret 2 4 next t₂ with
      | none => rw [h1t] at h1; simp at h1
      | some resT =>
        cases h1e : checkArm .ret 2 4 next e₂ with
        | none => rw [h1t, h1e] at h1; simp at h1
        | some resE =>
          rw [h1t, h1e] at h1
          simp only [Option.some.injEq] at h1
          subst h1
          exact ⟨_, rfl, hoistJnzArms_wf rs _ _ next hc ht he
            (hasArmShape_of_checkArm .ret ht.symm h1t)
            (hasArmShape_of_checkArm .ret he.symm h1e) hG fun _ _ _ _ hsel' => .ret hsel'⟩
  · rw [hf1] at h1; rw [hf2]; dsimp only at h1 ⊢
    cases hsel : isSelectSigWith true jTs with
    | false => rw [hsel] at h1; simp at h1
    | true =>
      rw [hsel] at h1; simp only [↓reduceIte] at h1 ⊢
      rw [checkArm_eq_of_wf (.tag jId jTs) ht (TagD.checkArm_compat hD) 2 4 next,
          checkArm_eq_of_wf (.tag jId jTs) he (TagD.checkArm_compat hD) 2 4 next] at h1
      cases h1t : checkArm (.tag jId jTs) 2 4 next t₂ with
      | none => rw [h1t] at h1; simp at h1
      | some resT =>
        cases h1e : checkArm (.tag jId jTs) 2 4 next e₂ with
        | none => rw [h1t, h1e] at h1; simp at h1
        | some resE =>
          rw [h1t, h1e] at h1
          simp only [Option.some.injEq] at h1
          subst h1
          exact ⟨_, rfl, hoistJnzArms_wf jTs _ _ next hc ht he
            (hasArmShape_of_checkArm (.tag jId jTs) ht.symm h1t)
            (hasArmShape_of_checkArm (.tag jId jTs) he.symm h1e) hG
            fun _ _ _ _ hsel' => .jump hl hsel'⟩

private theorem tryStoreJnzDiamond_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx (IVal V₁) (IVal V₂)} {D : Ctx (JLabel L₁) (JLabel L₂)}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} {next : Nat}
    {c₁ : Arg (IVal V₁) .bool} {c₂ : Arg (IVal V₂) .bool}
    {t₁ e₁ : Expr (IVal V₁) (JLabel L₁) rs} {t₂ e₂ : Expr (IVal V₂) (JLabel L₂) rs}
    (hc : ArgRel G .bool c₁ c₂) (ht : Wf G D t₁ t₂) (he : Wf G D e₁ e₂)
    (hG : IRelG G' G) (hD : TagD D D') (hKey : IKeyEq G) {r₁ : Expr V₁ L₁ rs}
    (h1 : tryStoreJnzDiamond true next c₁ t₁ e₁ = some r₁) :
    ∃ r₂, tryStoreJnzDiamond true next c₂ t₂ e₂ = some r₂ ∧ Wf G' D' r₁ r₂ := by
  dsimp only [tryStoreJnzDiamond] at h1 ⊢
  rcases findFirstJumpStore_eq_of_wf hD 16 ht with ⟨hf1, hf2⟩ | ⟨jTs, jId, l₁, l₂, hf1, hf2, hl⟩
  · rw [hf1] at h1; rw [hf2]; dsimp only at h1 ⊢
    cases hsel : isSelectSigWith true rs with
    | false => rw [hsel] at h1; simp at h1
    | true =>
      rw [hsel] at h1; simp only [↓reduceIte] at h1 ⊢
      rw [checkStoreArms_eq_of_wf true .ret next ht he hKey (TagD.checkArm_compat hD)] at h1
      cases hsp : checkStoreArms true .ret next t₂ e₂ with
      | none => rw [hsp] at h1; simp at h1
      | some sp =>
        rw [hsp] at h1
        rw [Option.map_some] at h1
        have h1' := Option.some.inj h1
        subst h1'
        have hsh := hasStoreStepShapes_of_checkStoreArms true .ret next ht.symm he.symm hsp
        exact ⟨_, rfl,
          hoistStoreArms_wf rs sp next hc ht he hsh.1 hsh.2 hG fun _ _ _ _ hsel' => .ret hsel'⟩
  · rw [hf1] at h1; rw [hf2]; dsimp only at h1 ⊢
    cases hsel : isSelectSigWith true jTs with
    | false => rw [hsel] at h1; simp at h1
    | true =>
      rw [hsel] at h1; simp only [↓reduceIte] at h1 ⊢
      rw [checkStoreArms_eq_of_wf true (.tag jId jTs) next ht he hKey
        (TagD.checkArm_compat hD)] at h1
      cases hsp : checkStoreArms true (.tag jId jTs) next t₂ e₂ with
      | none => rw [hsp] at h1; simp at h1
      | some sp =>
        rw [hsp] at h1
        rw [Option.map_some] at h1
        have h1' := Option.some.inj h1
        subst h1'
        have hsh :=
          hasStoreStepShapes_of_checkStoreArms true (.tag jId jTs) next ht.symm he.symm hsp
        exact ⟨_, rfl, hoistStoreArms_wf jTs sp next hc ht he hsh.1 hsh.2 hG
          fun _ _ _ _ hsel' => .jump hl hsel'⟩

private theorem tryPureJnzDiamond_none_eq {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {rs : List Ty} {G : Ctx (IVal V₁) (IVal V₂)} {D : Ctx (JLabel L₁) (JLabel L₂)}
    {D' : Ctx L₁ L₂} (next : Nat) {c₁ : Arg (IVal V₁) .bool} {c₂ : Arg (IVal V₂) .bool}
    {t₁ e₁ : Expr (IVal V₁) (JLabel L₁) rs} {t₂ e₂ : Expr (IVal V₂) (JLabel L₂) rs}
    (ht : Wf G D t₁ t₂) (he : Wf G D e₁ e₂) (hD : TagD D D')
    (h1 : tryPureJnzDiamond true next c₁ t₁ e₁ = none) :
    tryPureJnzDiamond true next c₂ t₂ e₂ = none := by
  dsimp only [tryPureJnzDiamond] at h1 ⊢
  rcases findFirstJump_eq_of_wf hD 8 ht with ⟨hf1, hf2⟩ | ⟨jTs, jId, _, _, hf1, hf2, _⟩
  · rw [hf1] at h1; rw [hf2]; dsimp only at h1 ⊢
    cases hsel : isSelectSigWith true rs with
    | false => rfl
    | true =>
      rw [hsel] at h1; simp only [↓reduceIte] at h1 ⊢
      rw [checkArm_eq_of_wf .ret ht (TagD.checkArm_compat hD) 2 4 next,
          checkArm_eq_of_wf .ret he (TagD.checkArm_compat hD) 2 4 next] at h1
      cases h1t : checkArm .ret 2 4 next t₂ with
      | none => rfl
      | some _ =>
        cases h1e : checkArm .ret 2 4 next e₂ with
        | none => rfl
        | some _ => rw [h1t, h1e] at h1; simp at h1
  · rw [hf1] at h1; rw [hf2]; dsimp only at h1 ⊢
    cases hsel : isSelectSigWith true jTs with
    | false => rfl
    | true =>
      rw [hsel] at h1; simp only [↓reduceIte] at h1 ⊢
      rw [checkArm_eq_of_wf (.tag jId jTs) ht (TagD.checkArm_compat hD) 2 4 next,
          checkArm_eq_of_wf (.tag jId jTs) he (TagD.checkArm_compat hD) 2 4 next] at h1
      cases h1t : checkArm (.tag jId jTs) 2 4 next t₂ with
      | none => rfl
      | some _ =>
        cases h1e : checkArm (.tag jId jTs) 2 4 next e₂ with
        | none => rfl
        | some _ => rw [h1t, h1e] at h1; simp at h1

private theorem tryStoreJnzDiamond_none_eq {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {rs : List Ty} {G : Ctx (IVal V₁) (IVal V₂)} {D : Ctx (JLabel L₁) (JLabel L₂)}
    {D' : Ctx L₁ L₂} (next : Nat) {c₁ : Arg (IVal V₁) .bool} {c₂ : Arg (IVal V₂) .bool}
    {t₁ e₁ : Expr (IVal V₁) (JLabel L₁) rs} {t₂ e₂ : Expr (IVal V₂) (JLabel L₂) rs}
    (ht : Wf G D t₁ t₂) (he : Wf G D e₁ e₂) (hD : TagD D D') (hKey : IKeyEq G)
    (h1 : tryStoreJnzDiamond true next c₁ t₁ e₁ = none) :
    tryStoreJnzDiamond true next c₂ t₂ e₂ = none := by
  dsimp only [tryStoreJnzDiamond] at h1 ⊢
  rcases findFirstJumpStore_eq_of_wf hD 16 ht with ⟨hf1, hf2⟩ | ⟨jTs, jId, _, _, hf1, hf2, _⟩
  · rw [hf1] at h1; rw [hf2]; dsimp only at h1 ⊢
    cases hsel : isSelectSigWith true rs with
    | false => rfl
    | true =>
      rw [hsel] at h1; simp only [↓reduceIte] at h1 ⊢
      rw [checkStoreArms_eq_of_wf true .ret next ht he hKey (TagD.checkArm_compat hD)] at h1
      cases hsp : checkStoreArms true .ret next t₂ e₂ with
      | none => rfl
      | some _ => rw [hsp] at h1; simp at h1
  · rw [hf1] at h1; rw [hf2]; dsimp only at h1 ⊢
    cases hsel : isSelectSigWith true jTs with
    | false => rfl
    | true =>
      rw [hsel] at h1; simp only [↓reduceIte] at h1 ⊢
      rw [checkStoreArms_eq_of_wf true (.tag jId jTs) next ht he hKey
        (TagD.checkArm_compat hD)] at h1
      cases hsp : checkStoreArms true (.tag jId jTs) next t₂ e₂ with
      | none => rfl
      | some _ => rw [hsp] at h1; simp at h1

private theorem ifOptWith_wf_aux {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (bitsOnly : Bool) {G : Ctx (IVal V₁) (IVal V₂)} {D : Ctx (JLabel L₁) (JLabel L₂)}
    {e₁ : Expr (IVal V₁) (JLabel L₁) rs} {e₂ : Expr (IVal V₂) (JLabel L₂) rs}
    (hwf : Wf G D e₁ e₂) :
    IKeyEq G → ∀ {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂},
      IRelG G' G → TagD D D' → ∀ depth next,
        Wf G' D' (ifOptWith bitsOnly depth next e₁) (ifOptWith bitsOnly depth next e₂) := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
    intro hKey G' D' hG hD depth next
    cases hop with
    | mk code hargs =>
      exact .let_ (.mk code (trel_iout hG hargs)) fun xs₁ xs₂ =>
        ih _ _ (iKeyEq_freshIVals hKey _ xs₁ xs₂ next) (hG.freshIVals xs₁ xs₂ next) hD depth
          (next + _)
  | load t ha _ ih =>
    intro hKey G' D' hG hD depth next
    exact .load t (argRel_iout hG ha) fun v₁ v₂ =>
      ih _ _ (IKeyEq.oneSame hKey _ _ (.var next)) (hG.freshOne v₁ v₂ next) hD depth (next + 1)
  | store hv ha _ ih =>
    intro hKey G' D' hG hD depth next
    exact .store (argRel_iout hG hv) (argRel_iout hG ha) (ih hKey hG hD depth next)
  | call f hargs _ ih =>
    intro hKey G' D' hG hD depth next
    exact .call f (trel_iout hG hargs) fun xs₁ xs₂ =>
      ih _ _ (iKeyEq_freshIVals hKey _ xs₁ xs₂ next) (hG.freshIVals xs₁ xs₂ next) hD depth
        (next + _)
  | @jnz _ _ c₁ c₂ t₁ t₂ e₁' e₂' hc ht he iht ihe =>
    intro hKey G' D' hG hD depth next
    dsimp only [ifOptWith]
    cases bitsOnly
    · exact .jnz (argRel_iout hG hc) (iht hKey hG hD depth next) (ihe hKey hG hD depth next)
    · dsimp only [tryJnzDiamond]
      have hfb : Wf G' D' (.jnz (iout c₁) (ifOptWith true depth next t₁)
          (ifOptWith true depth next e₁'))
          (.jnz (iout c₂) (ifOptWith true depth next t₂) (ifOptWith true depth next e₂')) :=
        .jnz (argRel_iout hG hc) (iht hKey hG hD depth next) (ihe hKey hG hD depth next)
      cases hp1 : tryPureJnzDiamond true next c₁ t₁ e₁' with
      | some r₁ =>
        rcases tryPureJnzDiamond_wf hc ht he hG hD hp1 with ⟨r₂, hp2, hwfR⟩
        rw [hp2]; exact hwfR
      | none =>
        rw [tryPureJnzDiamond_none_eq next ht he hD hp1]; dsimp only
        cases hs1 : tryStoreJnzDiamond true next c₁ t₁ e₁' with
        | some r₁ =>
          rcases tryStoreJnzDiamond_wf hc ht he hG hD hKey hs1 with ⟨r₂, hs2, hwfR⟩
          rw [hs2]; exact hwfR
        | none =>
          rw [tryStoreJnzDiamond_none_eq next ht he hD hKey hs1]
          exact hfb
  | jump hj hargs =>
    intro _ G' D' hG hD depth next
    exact ifOpt_jump_wf _ hj hargs hG hD bitsOnly depth next
  | ret hvs =>
    intro _ G' _ hG _ _ _
    exact .ret (trel_iout hG hvs)
  | exit f hargs =>
    intro _ G' _ hG _ _ _
    exact .exit f (trel_iout hG hargs)
  | hlt =>
    intro _ _ _ _ _ _ _
    exact .hlt
  | @group G D sig b₁ b₂ k₁ k₂ _ hk ihb ihk =>
    intro hKey G' D' hG hD depth next
    cases bitsOnly
    · cases sig with
      | nil =>
        refine .group (fun Js₁ Js₂ => WfB.of_get fun i => nomatch i) fun Js₁ Js₂ => ?_
        exact ihk (Js₁.map fun _ l => .outer l) (Js₂.map fun _ l => .outer l)
          hKey hG (TagD.append_outer hD Js₁ Js₂) depth next
      | cons ts sig' =>
        cases sig' with
        | nil =>
          have hchk : checkDiamondWith false depth ts next (k₁ (.loc depth, ())) =
              checkDiamondWith false depth ts next (k₂ (.loc depth, ())) :=
            checkDiamond_eq_of_wf false depth ts (TagD.head_compat hD depth) next hKey
              (hk (.loc depth, ()) (.loc depth, ()))
          dsimp only [ifOptWith]
          refine .group (fun Js₁ Js₂ => WfB.of_get fun i xs₁ xs₂ => ?_) fun Js₁ Js₂ => ?_
          · rw [ifOptB_get, ifOptB_get]
            exact ihb (Js₁.map fun _ l => .outer l) (Js₂.map fun _ l => .outer l)
              i _ _ (iKeyEq_freshIVals hKey _ xs₁ xs₂ next) (hG.freshIVals xs₁ xs₂ next)
              (TagD.append_outer hD Js₁ Js₂) (depth + 1) (next + _)
          · rw [hchk]
            cases hplan : checkDiamondWith false depth ts next (k₂ (.loc depth, ())) with
            | none =>
              exact ihk (Js₁.map fun _ l => .outer l) (Js₂.map fun _ l => .outer l)
                hKey hG (TagD.append_outer hD Js₁ Js₂) (depth + 1) next
            | some plan =>
              have hsh_k2 : HasDiamondShape ts plan (k₂ (.outer Js₂.1, ())) :=
                hasDiamondShape_of_checkDiamond false depth ts next plan
                  (hk (.loc depth, ()) (.outer Js₂.1, ())) (hchk.symm ▸ hplan)
              have hwf_out := hk (.outer Js₁.1, ()) (.outer Js₂.1, ())
              have hsh_k1 : HasDiamondShape ts plan (k₁ (.outer Js₁.1, ())) :=
                hasDiamondShape_of_rhs ts plan hwf_out hsh_k2
              exact hoistDiamond_wf List.mem_cons_self plan next hwf_out hsh_k1 hG
        | cons ts₂ rest =>
          refine .group (fun Js₁ Js₂ => WfB.of_get fun i xs₁ xs₂ => ?_) fun Js₁ Js₂ => ?_
          · rw [ifOptB_get, ifOptB_get]
            exact ihb (Js₁.map fun _ l => .outer l) (Js₂.map fun _ l => .outer l)
              i _ _ (iKeyEq_freshIVals hKey _ xs₁ xs₂ next) (hG.freshIVals xs₁ xs₂ next)
              (TagD.append_outer hD Js₁ Js₂) (depth + rest.length + 2) (next + _)
          · exact ihk (Js₁.map fun _ l => .outer l) (Js₂.map fun _ l => .outer l)
              hKey hG (TagD.append_outer hD Js₁ Js₂) (depth + rest.length + 2) next
    · rw [ifOptWith_group_true_eq, ifOptWith_group_true_eq]
      refine .group (fun Js₁ Js₂ => WfB.of_get fun i xs₁ xs₂ => ?_) fun Js₁ Js₂ => ?_
      · rw [ifOptB_get, ifOptB_get]
        exact ihb (tagLabels depth Js₁) (tagLabels depth Js₂)
          i _ _ (iKeyEq_freshIVals hKey _ xs₁ xs₂ next) (hG.freshIVals xs₁ xs₂ next)
          (TagD.append_tag hD depth Js₁ Js₂) (depth + sig.length) (next + _)
      · exact ihk (tagLabels depth Js₁) (tagLabels depth Js₂)
          hKey hG (TagD.append_tag hD depth Js₁ Js₂) (depth + sig.length) next

/-- Well-formedness preservation for `ifOptWith`, proved via `Wf.induct`. -/
theorem ifOptWith_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    (bitsOnly : Bool) {G : Ctx (IVal V₁) (IVal V₂)} {D : Ctx (JLabel L₁) (JLabel L₂)}
    {e₁ : Expr (IVal V₁) (JLabel L₁) rs} {e₂ : Expr (IVal V₂) (JLabel L₂) rs}
    (hwf : Wf G D e₁ e₂)
    (hKey : IKeyEq G) {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂}
    (hG : IRelG G' G) (hD : OuterD D D') (depth next : Nat) :
    Wf G' D' (ifOptWith bitsOnly depth next e₁) (ifOptWith bitsOnly depth next e₂) :=
  ifOptWith_wf_aux bitsOnly hwf hKey hG (OuterD.to_tagD hD) depth next

/-- Well-formedness preservation for `ifOpt`, proved via `Wf.induct`. -/
theorem ifOpt_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx (IVal V₁) (IVal V₂)} {D : Ctx (JLabel L₁) (JLabel L₂)}
    {e₁ : Expr (IVal V₁) (JLabel L₁) rs} {e₂ : Expr (IVal V₂) (JLabel L₂) rs}
    (hwf : Wf G D e₁ e₂) :
    IKeyEq G → ∀ {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂},
      IRelG G' G → OuterD D D' → ∀ depth next,
        Wf G' D' (ifOpt depth next e₁) (ifOpt depth next e₂) :=
  fun hKey {_ _} hG hD depth next => ifOptWith_wf false hwf hKey hG hD depth next

private theorem tryPureJnzDiamond_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {depth next : Nat} {ρ : FEnv} {G : Ctx (IVal Val) Val} {D : Ctx (JLabel Cont) Cont}
    {c₁ : Arg (IVal Val) .bool} {c₂ : Arg Val .bool}
    {t₁ e₁' : Expr (IVal Val) (JLabel Cont) rs} {t₂ e₂' : Expr Val Cont rs}
    (hc : ArgRel G .bool c₁ c₂) (ht : Wf G D t₁ t₂) (he : Wf G D e₁' e₂')
    (hD : TagContD depth D) (hG : IGood ρ next G) {m : Mem 64}
    (hw : wp Γ Q X (.jnz c₂ t₂ e₂') m) {res : Expr Val Cont rs}
    (hp : tryPureJnzDiamond true next c₁ t₁ e₁' = some res) :
    wp Γ Q X res m := by
  dsimp only [tryPureJnzDiamond] at hp
  cases hff : findFirstJump 8 t₁ with
  | none =>
    rw [hff] at hp; dsimp only at hp
    cases hsel : isSelectSigWith true rs <;> rw [hsel] at hp
    · simp at hp
    · cases h1 : checkArm .ret 2 4 next t₁ with
      | none => rw [h1] at hp; simp at hp
      | some resT =>
        cases h2 : checkArm .ret 2 4 next e₁' with
        | none => rw [h1, h2] at hp; simp at hp
        | some resE =>
          rw [h1, h2] at hp; simp only [↓reduceIte, Option.some.injEq] at hp
          subst hp
          have hspT := armSpec_of_checkArm_ret ht h1
          have hspE := armSpec_of_checkArm_ret he h2
          exact hoistJnzArms_wp .ret (isSelectSigWith_imp true rs hsel) resT.1 resE.1 next
            hc ht he hspT hspE hG hw fun sel hs => by simpa [TermTarget.wp, wp] using hs
  | some tgt =>
    rcases tgt with ⟨jTs, jId, jLbl⟩
    rw [hff] at hp; dsimp only at hp
    cases hsel : isSelectSigWith true jTs <;> rw [hsel] at hp
    · simp at hp
    · cases h1 : checkArm (.tag jId jTs) 2 4 next t₁ with
      | none => rw [h1] at hp; simp at hp
      | some resT =>
        cases h2 : checkArm (.tag jId jTs) 2 4 next e₁' with
        | none => rw [h1, h2] at hp; simp at hp
        | some resE =>
          rw [h1, h2] at hp; simp only [↓reduceIte, Option.some.injEq] at hp
          subst hp
          have hj := findFirstJump_mem_of_wf depth hD 8 ht hff
          have hspT := armSpec_of_checkArm_tag jId jLbl jLbl depth ht hD hj h1
          have hspE := armSpec_of_checkArm_tag jId jLbl jLbl depth he hD hj h2
          exact hoistJnzArms_wp (.jump jLbl) (isSelectSigWith_imp true jTs hsel)
            resT.1 resE.1 next hc ht he hspT hspE hG hw fun sel hs => hs

private theorem tryStoreJnzDiamond_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {depth next : Nat} {ρ : FEnv} {G : Ctx (IVal Val) Val} {D : Ctx (JLabel Cont) Cont}
    {c₁ : Arg (IVal Val) .bool} {c₂ : Arg Val .bool}
    {t₁ e₁' : Expr (IVal Val) (JLabel Cont) rs} {t₂ e₂' : Expr Val Cont rs}
    (hc : ArgRel G .bool c₁ c₂) (ht : Wf G D t₁ t₂) (he : Wf G D e₁' e₂')
    (hD : TagContD depth D) (hG : IGood ρ next G) {m : Mem 64}
    (hw : wp Γ Q X (.jnz c₂ t₂ e₂') m) {res : Expr Val Cont rs}
    (hs : tryStoreJnzDiamond true next c₁ t₁ e₁' = some res) :
    wp Γ Q X res m := by
  dsimp only [tryStoreJnzDiamond] at hs
  cases hff : findFirstJumpStore 16 t₁ with
  | none =>
    rw [hff] at hs; dsimp only at hs
    cases hsel : isSelectSigWith true rs <;> rw [hsel] at hs
    · simp at hs
    · simp only [↓reduceIte] at hs
      cases hsp : checkStoreArms true .ret next t₁ e₁' <;> rw [hsp] at hs
      · cases hs
      · rename_i sp
        simp only [Option.map_some, Option.some.injEq] at hs
        subst hs
        have hspec := storeDiamondSpec_of_checkStoreArms_ret true next ρ ht he
          (symGIn_of_iGood hG) hsp
        exact hoistStoreArms_wp .ret (isSelectSigWith_imp true rs hsel) sp next hc ht he hspec hG
          hw fun sel _ hs' => by simpa [TermTarget.wp, wp] using hs'
  | some tgt =>
    rcases tgt with ⟨jTs, jId, jLbl⟩
    rw [hff] at hs; dsimp only at hs
    cases hsel : isSelectSigWith true jTs <;> rw [hsel] at hs
    · simp at hs
    · simp only [↓reduceIte] at hs
      cases hsp : checkStoreArms true (.tag jId jTs) next t₁ e₁' <;> rw [hsp] at hs
      · cases hs
      · rename_i sp
        simp only [Option.map_some, Option.some.injEq] at hs
        subst hs
        have hj := findFirstJumpStore_mem_of_wf depth hD 16 ht hff
        have hspec := storeDiamondSpec_of_checkStoreArms_tag true jId jLbl jLbl depth next ρ
          ht he hD hj (symGIn_of_iGood hG) hsp
        exact hoistStoreArms_wp (.jump jLbl) (isSelectSigWith_imp true jTs hsel) sp next
          hc ht he hspec hG hw fun sel _ hs' => hs'

private theorem ifOptWith_wp_aux {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (bitsOnly : Bool) {G : Ctx (IVal Val) Val} {D : Ctx (JLabel Cont) Cont}
    {e₁ : Expr (IVal Val) (JLabel Cont) rs} {e₂ : Expr Val Cont rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ {depth}, TagContD depth D → ∀ next ρ, IGood ρ next G → ∀ m,
    wp Γ Q X e₂ m → wp Γ Q X (ifOptWith bitsOnly depth next e₁) m := by
  induction hwf using Wf.induct with
  | let_ hop _ ih =>
    intro depth hD next ρ hG m hw
    cases hop with
    | @mk _ _ code _ args₂ hargs =>
      dsimp only [ifOptWith, wp, Op.wp] at hw ⊢
      rw [TRel.iout_vals hG hargs]
      exact OpCode.wp_mono code (vals args₂) (fun r hr =>
        ih (freshIVals _ r next) r hD (next + _) (fupdTup ρ next r)
          (hG.freshIVals r) m hr) hw
  | load t ha _ ih =>
    intro depth hD next ρ hG m ⟨v, hv, hk⟩
    dsimp only [ifOptWith, wp]
    rw [argRel_iout_val hG ha]
    exact ⟨v, hv, ih (.var v, .var next) v hD (next + 1) (fupd ρ next v)
      (hG.freshOne v) m hk⟩
  | store hv ha _ ih =>
    intro depth hD next ρ hG m ⟨hok, hk⟩
    dsimp only [ifOptWith, wp]
    rw [argRel_iout_val hG hv, argRel_iout_val hG ha]
    exact ⟨hok, ih hD next ρ hG _ hk⟩
  | call f hargs _ ih =>
    intro depth hD next ρ hG m ⟨P, E, hΓ, hP, hE⟩
    dsimp only [ifOptWith, wp]
    rw [TRel.iout_vals hG hargs]
    exact ⟨P, E, hΓ, fun r m' hp =>
      ih (freshIVals _ r next) r hD (next + _) (fupdTup ρ next r)
        (hG.freshIVals r) m' (hP r m' hp), hE⟩
  | @jnz _ _ c₁ c₂ t₁ t₂ e₁' e₂' hc ht he iht ihe =>
    intro depth hD next ρ hG m hw
    have hfb : wp Γ Q X (.jnz (iout c₁) (ifOptWith bitsOnly depth next t₁)
        (ifOptWith bitsOnly depth next e₁')) m := by
      dsimp only [wp] at hw ⊢
      rw [argRel_iout_val hG hc]
      exact ⟨fun h => iht hD next ρ hG m (hw.1 h), fun h => ihe hD next ρ hG m (hw.2 h)⟩
    dsimp only [ifOptWith]
    cases bitsOnly
    · exact hfb
    · dsimp only [tryJnzDiamond]
      cases hp : tryPureJnzDiamond true next c₁ t₁ e₁' with
      | some res => exact tryPureJnzDiamond_wp hc ht he hD hG hw hp
      | none =>
        cases hs : tryStoreJnzDiamond true next c₁ t₁ e₁' with
        | some res => exact tryStoreJnzDiamond_wp hc ht he hD hG hw hs
        | none => exact hfb
  | jump hj hargs =>
    intro depth hD next ρ hG m hw
    exact ifOpt_jump_wp hj hargs hD hG hw
  | ret hvs =>
    intro _ _ _ ρ hG m hw
    dsimp only [ifOptWith, wp] at hw ⊢
    rw [TRel.iout_vals hG hvs]
    exact hw
  | exit f hargs =>
    intro _ _ _ ρ hG m hw
    dsimp only [ifOptWith, wp] at hw ⊢
    rw [TRel.iout_vals hG hargs]
    exact hw
  | hlt =>
    intro _ _ _ _ _ _ hw
    exact hw
  | @group G D sig b₁ b₂ k₁ k₂ _ hk ihb ihk =>
    intro depth hD next ρ hG m hw
    cases bitsOnly
    · cases sig with
      | nil =>
        dsimp only [ifOptWith, wp] at hw ⊢
        intro Js hclosed
        refine ihk (Js.map fun _ l => .outer l) Js (TagContD.append_outer hD Js) next ρ hG
          m (hw Js ?_)
        rw [closed_iff] at hclosed ⊢
        intro _ i
        exact nomatch i
      | cons ts sig' =>
        cases sig' with
        | nil =>
          dsimp only [ifOptWith, wp] at hw ⊢
          intro Js hclosed
          have hclosed₂ : Closed Γ Q X (b₂ Js) Js := by
            rw [closed_iff] at hclosed ⊢
            intro ts' i xs m' hb'
            apply hclosed i xs m'
            rw [ifOptB_get]
            exact ihb (Js.map fun _ l => .outer l) Js i (freshIVals ts' xs next) xs
              ((TagContD.append_outer hD Js).mono (Nat.le_succ _)) (next + ts'.length)
              (fupdTup ρ next xs) (hG.freshIVals xs) m' hb'
          have hw₂ := hw Js hclosed₂
          cases hplan : checkDiamondWith false depth ts next (k₁ (.loc depth, ())) with
          | none =>
            exact ihk (Js.map fun _ l => .outer l) Js
              ((TagContD.append_outer hD Js).mono (Nat.le_succ _)) next ρ hG m hw₂
          | some plan =>
            have hsp := diamondSpec_of_checkDiamond false depth Js.1 depth next ρ plan hD
              (hk (.loc depth, ()) Js) (symGIn_of_iGood hG) hplan
            exact hoistDiamond_wp Js.1 plan next (hk (.outer Js.1, ()) Js) hsp hG m hw₂
        | cons ts₂ rest =>
          dsimp only [ifOptWith, wp] at hw ⊢
          intro Js hclosed
          refine ihk (Js.map fun _ l => .outer l) Js
            ((TagContD.append_outer hD Js).mono (show depth ≤ depth + rest.length + 2 by omega))
            next ρ hG m (hw Js ?_)
          rw [closed_iff] at hclosed ⊢
          intro ts' i xs m' hb'
          apply hclosed i xs m'
          rw [ifOptB_get]
          exact ihb (Js.map fun _ l => .outer l) Js i (freshIVals ts' xs next) xs
            ((TagContD.append_outer hD Js).mono
              (show depth ≤ depth + rest.length + 2 by omega))
            (next + ts'.length) (fupdTup ρ next xs) (hG.freshIVals xs) m' hb'
    · rw [ifOptWith_group_true_eq]
      dsimp only [wp] at hw ⊢
      intro Js hclosed
      refine ihk (tagLabels depth Js) Js (TagContD.append_tag hD Js) next ρ hG m (hw Js ?_)
      rw [closed_iff] at hclosed ⊢
      intro ts' i xs m' hb'
      apply hclosed i xs m'
      rw [ifOptB_get]
      exact ihb (tagLabels depth Js) Js i (freshIVals ts' xs next) xs
        (TagContD.append_tag hD Js) (next + ts'.length)
        (fupdTup ρ next xs) (hG.freshIVals xs) m' hb'

/-- Weakest-precondition refinement for `ifOptWith`, proved via `Wf.induct`. -/
theorem ifOptWith_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (bitsOnly : Bool) {G : Ctx (IVal Val) Val} {D : Ctx (JLabel Cont) Cont}
    {e₁ : Expr (IVal Val) (JLabel Cont) rs} {e₂ : Expr Val Cont rs}
    (hwf : Wf G D e₁ e₂) :
    OuterContD D → ∀ depth next ρ, IGood ρ next G → ∀ m,
    wp Γ Q X e₂ m → wp Γ Q X (ifOptWith bitsOnly depth next e₁) m :=
  fun hD depth next ρ hG m hw =>
    ifOptWith_wp_aux bitsOnly hwf (OuterContD.to_tagContD hD depth) next ρ hG m hw

/-- Weakest-precondition refinement for `ifOpt`, proved via `Wf.induct`. -/
theorem ifOpt_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx (IVal Val) Val} {D : Ctx (JLabel Cont) Cont}
    {e₁ : Expr (IVal Val) (JLabel Cont) rs} {e₂ : Expr Val Cont rs}
    (hwf : Wf G D e₁ e₂) :
    OuterContD D → ∀ depth next ρ, IGood ρ next G → ∀ m,
    wp Γ Q X e₂ m → wp Γ Q X (ifOpt depth next e₁) m :=
  ifOptWith_wp false hwf

/-! ## Pure integer compare sinking (`cmpSink`) soundness -/

namespace CmpSinkProofs

private inductive SValRel {V₁ V₂ : Ty → Type} (G' : Ctx V₁ V₂) :
    (t : Ty) → SVal V₁ t → SVal V₂ t → Prop
  | val {t : Ty} {a₁ : Arg V₁ t} {a₂ : Arg V₂ t} (id : Nat) :
    ArgRel G' t a₁ a₂ → SValRel G' t (.val a₁ id) (.val a₂ id)
  | defer {id n : Nat} {co : CmpOp}
      {l₁ r₁ : Arg V₁ (.bits n)} {l₂ r₂ : Arg V₂ (.bits n)} :
    ArgRel G' (.bits n) l₁ l₂ → ArgRel G' (.bits n) r₁ r₂ →
    SValRel G' .bool (.defer ⟨id, n, co, l₁, r₁⟩) (.defer ⟨id, n, co, l₂, r₂⟩)

private theorem SValRel.weaken {V₁ V₂ : Ty → Type} {G₁ G₂ : Ctx V₁ V₂}
    (hsub : ∀ p ∈ G₁, p ∈ G₂) {t : Ty} {s₁ : SVal V₁ t} {s₂ : SVal V₂ t}
    (h : SValRel G₁ t s₁ s₂) : SValRel G₂ t s₁ s₂ := by
  cases h with
  | val id ha => exact .val id (ArgRel.weaken hsub ha)
  | defer hl hr => exact .defer (ArgRel.weaken hsub hl) (ArgRel.weaken hsub hr)

private theorem SValRel.svalId_eq {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂} {t : Ty}
    {s₁ : SVal V₁ t} {s₂ : SVal V₂ t} (h : SValRel G' t s₁ s₂) : svalId s₁ = svalId s₂ := by
  cases h <;> rfl

private def SRelG {V₁ V₂ : Ty → Type} (G' : Ctx V₁ V₂) (G : Ctx (SVal V₁) (SVal V₂)) : Prop :=
  ∀ p ∈ G, SValRel G' p.1 p.2.1 p.2.2

private theorem SRelG.weaken {V₁ V₂ : Ty → Type} {G₁ G₂ : Ctx V₁ V₂}
    {G : Ctx (SVal V₁) (SVal V₂)} (hsub : ∀ p ∈ G₁, p ∈ G₂) (hG : SRelG G₁ G) :
    SRelG G₂ G :=
  fun _ hp => (hG _ hp).weaken hsub

private theorem SRelG.freshSVals {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂}
    {G : Ctx (SVal V₁) (SVal V₂)} (hG : SRelG G' G) :
    {ts : List Ty} → (xs₁ : Tup V₁ ts) → (xs₂ : Tup V₂ ts) → (next : Nat) →
    SRelG (Tup.zip xs₁ xs₂ ++ G') (Tup.zip (freshSVals ts xs₁ next) (freshSVals ts xs₂ next) ++ G)
  | [], (), (), _ => hG
  | t :: ts, (x₁, xs₁), (x₂, xs₂), next => by
    dsimp only [freshSVals, Tup.zip, SRelG]
    intro p hp
    cases hp with
    | head =>
      exact .val next (.var List.mem_cons_self)
    | tail _ hp =>
      have ih := SRelG.freshSVals (G' := G') (G := G) hG xs₁ xs₂ (next + 1) p hp
      exact ih.weaken fun q hq => List.mem_cons_of_mem _ hq

private theorem SRelG.dummySVals {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂}
    {G : Ctx (SVal V₁) (SVal V₂)} (hG : SRelG G' G) :
    (ts : List Ty) → (next : Nat) →
    SRelG G' (Tup.zip (dummySVals (V := V₁) ts next) (dummySVals (V := V₂) ts next) ++ G)
  | [], _ => hG
  | _ :: ts, next => by
    dsimp only [dummySVals, Tup.zip, SRelG]
    intro p hp
    cases hp with
    | head => exact .val next (.imm _)
    | tail _ hp => exact SRelG.dummySVals hG ts (next + 1) p hp

private theorem sarg_soutBits {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂}
    {G : Ctx (SVal V₁) (SVal V₂)} (hG : SRelG G' G) {n : Nat}
    {a₁ : Arg (SVal V₁) (.bits n)} {a₂ : Arg (SVal V₂) (.bits n)}
    (ha : ArgRel G (.bits n) a₁ a₂) : ArgRel G' (.bits n) (soutBits a₁) (soutBits a₂) := by
  cases ha with
  | imm c => exact .imm c
  | @var s₁ s₂ hm =>
    cases s₁ with
    | val _ _ =>
      cases s₂ with
      | val _ _ =>
        cases hG _ hm with
        | val _ ha' => exact ha'

private theorem sargIsId_eq {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂}
    {G : Ctx (SVal V₁) (SVal V₂)} (hG : SRelG G' G) (cid : Nat) {t : Ty}
    {a₁ : Arg (SVal V₁) t} {a₂ : Arg (SVal V₂) t}
    (ha : ArgRel G t a₁ a₂) : sargIsId cid a₁ = sargIsId cid a₂ := by
  cases ha with
  | imm _ => rfl
  | var hm => simp only [sargIsId, (hG _ hm).svalId_eq]

private theorem sargsHasId_eq {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂}
    {G : Ctx (SVal V₁) (SVal V₂)} (hG : SRelG G' G) (cid : Nat) :
    {ts : List Ty} → {a₁ : Tup (Arg (SVal V₁)) ts} → {a₂ : Tup (Arg (SVal V₂)) ts} →
    TRel (ArgRel G) a₁ a₂ → sargsHasId cid a₁ = sargsHasId cid a₂
  | [], (), (), .nil => rfl
  | _ :: _, (_, _), (_, _), .cons ha has => by
    dsimp only [sargsHasId]
    rw [sargIsId_eq hG cid ha, sargsHasId_eq hG cid has]

private theorem shouldDeferCmp_eq_of_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type}
    {rs : List Ty} (cid : Nat) :
    ∀ (fuel : Nat) (saw : Bool) (next : Nat) {G' : Ctx V₁ V₂} {G : Ctx (SVal V₁) (SVal V₂)}
      {D : Ctx L₁ L₂} {e₁ : Expr (SVal V₁) L₁ rs} {e₂ : Expr (SVal V₂) L₂ rs},
    SRelG G' G → Wf G D e₁ e₂ →
    shouldDeferCmp cid fuel saw next e₁ = shouldDeferCmp cid fuel saw next e₂
  | 0, _, _, _, _, _, _, _, _, _ => rfl
  | fuel + 1, saw, next, G', G, D, _, _, hG, hwf => by
    cases hwf with
    | @let_ _ _ ts _ _ _ _ hop hk =>
      cases hop with
      | @mk _ _ code args₁ args₂ hargs =>
        dsimp only [shouldDeferCmp]
        cases code with
        | select u =>
          rcases args₁ with ⟨c₁, aT₁, aE₁, ⟨⟩⟩
          rcases args₂ with ⟨c₂, aT₂, aE₂, ⟨⟩⟩
          cases hargs with | cons hc hargs =>
          cases hargs with | cons haT hargs =>
          cases hargs with | cons haE _ =>
          dsimp only [shouldDeferCmpStep]
          rw [sargIsId_eq hG cid hc, sargIsId_eq hG cid haT, sargIsId_eq hG cid haE]
          cases (sargIsId cid c₂ && !sargIsId cid aT₂ && !sargIsId cid aE₂) with
          | true => rfl
          | false =>
            cases (sargIsId cid c₂ || sargIsId cid aT₂ || sargIsId cid aE₂) with
            | true => rfl
            | false =>
              exact shouldDeferCmp_eq_of_wf cid fuel true (next + 1)
                (hG.dummySVals [u] next) (hk (dummySVals [u] next) (dummySVals [u] next))
        | _ =>
          dsimp only [shouldDeferCmpStep]
          rw [sargsHasId_eq hG cid hargs]
          cases sargsHasId cid args₂ with
          | true => rfl
          | false =>
            exact shouldDeferCmp_eq_of_wf cid fuel (saw || isCmpClobberOp _) (next + _)
              (hG.dummySVals _ next) (hk (dummySVals _ next) (dummySVals _ next))
    | load _ _ _ | store _ _ _ | call _ _ _ | jnz _ _ _ | jump _ _ | ret _ | exit _ _
    | hlt | group _ _ => rfl

private inductive MatRel {V₁ V₂ : Ty → Type} (G' : Ctx V₁ V₂) :
    List (Nat × V₁ .bool) → List (Nat × V₂ .bool) → Prop
  | nil : MatRel G' [] []
  | cons {id : Nat} {v₁ : V₁ .bool} {v₂ : V₂ .bool}
      {r₁ : List (Nat × V₁ .bool)} {r₂ : List (Nat × V₂ .bool)} :
    ⟨.bool, v₁, v₂⟩ ∈ G' → MatRel G' r₁ r₂ → MatRel G' ((id, v₁) :: r₁) ((id, v₂) :: r₂)

private theorem MatRel.weaken {V₁ V₂ : Ty → Type} {G₁ G₂ : Ctx V₁ V₂}
    (hsub : ∀ p ∈ G₁, p ∈ G₂) :
    {mat₁ : List (Nat × V₁ .bool)} → {mat₂ : List (Nat × V₂ .bool)} →
    MatRel G₁ mat₁ mat₂ → MatRel G₂ mat₁ mat₂
  | _, _, .nil => .nil
  | _, _, .cons hmem hrest => .cons (hsub _ hmem) (MatRel.weaken hsub hrest)

private theorem lookupMat_eq_of_matRel {V₁ V₂ : Ty → Type} {G' : Ctx V₁ V₂} (id : Nat) :
    {mat₁ : List (Nat × V₁ .bool)} → {mat₂ : List (Nat × V₂ .bool)} →
    MatRel G' mat₁ mat₂ →
    (lookupMat id mat₁ = none ∧ lookupMat id mat₂ = none) ∨
    (∃ v₁ v₂, lookupMat id mat₁ = some v₁ ∧ lookupMat id mat₂ = some v₂ ∧
      ⟨.bool, v₁, v₂⟩ ∈ G')
  | [], [], .nil => Or.inl ⟨rfl, rfl⟩
  | (k, v₁) :: _, (_, v₂) :: _, .cons hv hrest => by
    dsimp only [lookupMat]
    by_cases heq : k == id
    · simp only [heq, ↓reduceIte]
      exact Or.inr ⟨v₁, v₂, rfl, rfl, hv⟩
    · simp only [heq, Bool.false_eq_true, ↓reduceIte]
      exact lookupMat_eq_of_matRel id hrest

private theorem matArg_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} {G : Ctx (SVal V₁) (SVal V₂)}
    {mat₁ : List (Nat × V₁ .bool)} {mat₂ : List (Nat × V₂ .bool)}
    (hG : SRelG G' G) (hmat : MatRel G' mat₁ mat₂)
    {t : Ty} {a₁ : Arg (SVal V₁) t} {a₂ : Arg (SVal V₂) t} (ha : ArgRel G t a₁ a₂)
    {cont₁ : List (Nat × V₁ .bool) → Arg V₁ t → Expr V₁ L₁ rs}
    {cont₂ : List (Nat × V₂ .bool) → Arg V₂ t → Expr V₂ L₂ rs}
    (hcont : ∀ G'' mat₁' mat₂' a₁' a₂',
      (∀ p ∈ G', p ∈ G'') → MatRel G'' mat₁' mat₂' → ArgRel G'' t a₁' a₂' →
      Wf G'' D' (cont₁ mat₁' a₁') (cont₂ mat₂' a₂')) :
    Wf G' D' (matArg mat₁ a₁ cont₁) (matArg mat₂ a₂ cont₂) := by
  cases ha with
  | imm c => exact hcont G' mat₁ mat₂ (.imm c) (.imm c) (fun _ h => h) hmat (.imm c)
  | @var s₁ s₂ hm =>
    have hrel := hG _ hm
    cases s₁ with
    | val _ _ =>
      cases s₂ with
      | val _ _ =>
        cases hrel with
        | val _ ha' => exact hcont G' mat₁ mat₂ _ _ (fun _ h => h) hmat ha'
      | defer _ => cases hrel
    | defer d₁ =>
      cases s₂ with
      | val _ _ => cases hrel
      | defer d₂ =>
        cases hrel with
        | @defer id n co l₁ r₁ l₂ r₂ hl hr =>
          dsimp only [matArg]
          rcases lookupMat_eq_of_matRel id hmat with ⟨h1, h2⟩ | ⟨v₁, v₂, h1, h2, hmem⟩
          · rw [h1, h2]
            refine .let_ ⟨.cmp co (.bits n) .bool rfl, ?_⟩ fun xs₁ xs₂ => ?_
            · exact .cons hl (.cons hr .nil)
            · exact hcont _ ((id, xs₁.1) :: mat₁) ((id, xs₂.1) :: mat₂)
                (.var xs₁.1) (.var xs₂.1)
                (fun _ h => List.mem_cons_of_mem _ h)
                (.cons List.mem_cons_self (hmat.weaken fun _ h => List.mem_cons_of_mem _ h))
                (.var List.mem_cons_self)
          · rw [h1, h2]
            exact hcont G' mat₁ mat₂ (.var v₁) (.var v₂) (fun _ h => h) hmat (.var hmem)

private theorem matArgs_wf {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G' : Ctx V₁ V₂} {D' : Ctx L₁ L₂} {G : Ctx (SVal V₁) (SVal V₂)}
    {mat₁ : List (Nat × V₁ .bool)} {mat₂ : List (Nat × V₂ .bool)}
    (hG : SRelG G' G) (hmat : MatRel G' mat₁ mat₂) :
    {ts : List Ty} → {as₁ : Tup (Arg (SVal V₁)) ts} → {as₂ : Tup (Arg (SVal V₂)) ts} →
    TRel (ArgRel G) as₁ as₂ →
    {cont₁ : List (Nat × V₁ .bool) → Tup (Arg V₁) ts → Expr V₁ L₁ rs} →
    {cont₂ : List (Nat × V₂ .bool) → Tup (Arg V₂) ts → Expr V₂ L₂ rs} →
    (∀ G'' mat₁' mat₂' as₁' as₂',
      (∀ p ∈ G', p ∈ G'') → MatRel G'' mat₁' mat₂' → TRel (ArgRel G'') as₁' as₂' →
      Wf G'' D' (cont₁ mat₁' as₁') (cont₂ mat₂' as₂')) →
    Wf G' D' (matArgs mat₁ as₁ cont₁) (matArgs mat₂ as₂ cont₂)
  | [], (), (), .nil, _, _, hcont => hcont G' mat₁ mat₂ () () (fun _ h => h) hmat .nil
  | _ :: _, (_, _), (_, _), .cons ha has, _, _, hcont =>
    matArg_wf hG hmat ha fun _ _ _ a₁' a₂' hsub₁ hmat₁ ha' =>
      matArgs_wf (hG.weaken hsub₁) hmat₁ has fun G₂ mat₁'' mat₂'' as₁' as₂' hsub₂ hmat₂ has' =>
        hcont G₂ mat₁'' mat₂'' (a₁', as₁') (a₂', as₂')
          (fun p hp => hsub₂ p (hsub₁ p hp)) hmat₂ (.cons (ArgRel.weaken hsub₂ ha') has')

private theorem cmpSinkB_get {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (next : Nat) (mat : List (Nat × V .bool)) :
    {sig : List (List Ty)} → (bs : Blocks (SVal V) L rs sig) →
    {ts : List Ty} → (i : Member ts sig) → (xs : Tup V ts) →
    (cmpSinkB next mat bs).get i xs =
      cmpSink (next + ts.length) mat (bs.get i (freshSVals ts xs next))
  | _ :: _, .cons _ _, _, .here, _ => rfl
  | _ :: _, .cons _ bs, _, .there i, xs => cmpSinkB_get next mat bs i xs

private theorem cmpSink_wf_aux {V₁ V₂ : Ty → Type} {L₁ L₂ : List Ty → Type} {rs : List Ty}
    {G : Ctx (SVal V₁) (SVal V₂)} {D : Ctx L₁ L₂}
    {e₁ : Expr (SVal V₁) L₁ rs} {e₂ : Expr (SVal V₂) L₂ rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ (next : Nat) {G' : Ctx V₁ V₂} {mat₁ : List (Nat × V₁ .bool)} {mat₂ : List (Nat × V₂ .bool)},
    SRelG G' G → MatRel G' mat₁ mat₂ →
    Wf G' D (cmpSink next mat₁ e₁) (cmpSink next mat₂ e₂) := by
  induction hwf using Wf.induct with
  | @let_ G₁ _ ts _ _ k₁ k₂ hop hk ih =>
    intro next G' mat₁ mat₂ hG hmat
    cases hop with
    | @mk _ _ code args₁ args₂ hargs =>
      cases code with
      | cmp co t m h =>
        cases t with
        | bits n =>
          subst h
          rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩
          rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
          cases hargs with | cons ha hargs =>
          cases hargs with | cons hb _ =>
          dsimp only [cmpSink]
          have hdef : shouldDeferCmp next 16 false (next + 1)
              (k₁ (.val (.imm default) next, ())) =
            shouldDeferCmp next 16 false (next + 1)
              (k₂ (.val (.imm default) next, ())) :=
            shouldDeferCmp_eq_of_wf next 16 false (next + 1)
              (hG.dummySVals [.bool] next)
              (hk (dummySVals [.bool] next) (dummySVals [.bool] next))
          rw [hdef]
          split
          · have hG' : SRelG G' (⟨.bool, .defer ⟨next, n, co, soutBits a₁, soutBits b₁⟩,
                .defer ⟨next, n, co, soutBits a₂, soutBits b₂⟩⟩ :: G₁) := by
              intro p hp
              cases hp with
              | head => exact .defer (sarg_soutBits hG ha) (sarg_soutBits hG hb)
              | tail _ hp => exact hG _ hp
            exact ih _ _ (next + 1) hG' hmat
          · refine .let_ ⟨.cmp co (.bits n) .bool rfl,
              .cons (sarg_soutBits hG ha) (.cons (sarg_soutBits hG hb) .nil)⟩ fun xs₁ xs₂ => ?_
            have hG' : SRelG (⟨.bool, xs₁.1, xs₂.1⟩ :: G')
                (⟨.bool, .val (.var xs₁.1) next, .val (.var xs₂.1) next⟩ :: G₁) := by
              intro p hp
              cases hp with
              | head => exact .val next (.var List.mem_cons_self)
              | tail _ hp => exact (hG _ hp).weaken fun _ h => List.mem_cons_of_mem _ h
            exact ih _ _ (next + 1) hG' (hmat.weaken fun _ h => List.mem_cons_of_mem _ h)
        | bool | float _ | pair _ _ =>
          dsimp only [cmpSink]
          exact matArgs_wf hG hmat hargs fun _ _ _ _ _ hsub hmat' has' =>
            .let_ ⟨.cmp co _ m h, has'⟩ fun xs₁ xs₂ =>
              ih (freshSVals _ xs₁ next) (freshSVals _ xs₂ next) (next + 1)
                (hG.weaken hsub |>.freshSVals xs₁ xs₂ next)
                (hmat'.weaken fun _ h => List.mem_append_right _ h)
      | _ =>
        dsimp only [cmpSink]
        exact matArgs_wf hG hmat hargs fun _ _ _ _ _ hsub hmat' has' =>
          .let_ ⟨_, has'⟩ fun xs₁ xs₂ =>
            ih (freshSVals _ xs₁ next) (freshSVals _ xs₂ next) (next + _)
              (hG.weaken hsub |>.freshSVals xs₁ xs₂ next)
              (hmat'.weaken fun _ h => List.mem_append_right _ h)
  | load t ha _ ih =>
    intro next G' mat₁ mat₂ hG hmat
    dsimp only [cmpSink]
    exact matArg_wf hG hmat ha fun _ _ _ a₁' a₂' hsub hmat' ha' =>
      .load t ha' fun v₁ v₂ =>
        ih (.val (.var v₁) next) (.val (.var v₂) next) (next + 1)
          (by
            intro p hp
            cases hp with
            | head => exact .val next (.var List.mem_cons_self)
            | tail _ hp => exact (hG _ hp).weaken fun _ h => List.mem_cons_of_mem _ (hsub _ h))
          (hmat'.weaken fun _ h => List.mem_cons_of_mem _ h)
  | store hv ha _ ih =>
    intro next G' mat₁ mat₂ hG hmat
    dsimp only [cmpSink]
    exact matArg_wf hG hmat hv fun G₁ mat₁₁ mat₂₁ v₁' v₂' hsub₁ hmat₁ hv' =>
      matArg_wf (hG.weaken hsub₁) hmat₁ (ArgRel.weaken (fun _ h => h) ha)
        fun G₂ mat₁₂ mat₂₂ a₁' a₂' hsub₂ hmat₂ ha' =>
          .store (ArgRel.weaken hsub₂ hv') ha'
            (ih next (hG.weaken fun _ h => hsub₂ _ (hsub₁ _ h)) hmat₂)
  | call f hargs _ ih =>
    intro next G' mat₁ mat₂ hG hmat
    dsimp only [cmpSink]
    exact matArgs_wf hG hmat hargs fun G'' mat₁' mat₂' as₁' as₂' hsub hmat' has' =>
      .call f has' fun xs₁ xs₂ =>
        ih (freshSVals _ xs₁ next) (freshSVals _ xs₂ next) (next + _)
          (hG.weaken hsub |>.freshSVals xs₁ xs₂ next)
          (hmat'.weaken fun _ h => List.mem_append_right _ h)
  | jnz hc _ _ iht ihe =>
    intro next G' mat₁ mat₂ hG hmat
    dsimp only [cmpSink]
    exact matArg_wf hG hmat hc fun G'' mat₁' mat₂' c₁' c₂' hsub hmat' hc' =>
      .jnz hc' (iht next (hG.weaken hsub) hmat') (ihe next (hG.weaken hsub) hmat')
  | jump hj hargs =>
    intro _ G' mat₁ mat₂ hG hmat
    dsimp only [cmpSink]
    exact matArgs_wf hG hmat hargs fun _ _ _ _ _ _ _ has' => .jump hj has'
  | ret hvs =>
    intro _ G' mat₁ mat₂ hG hmat
    dsimp only [cmpSink]
    exact matArgs_wf hG hmat hvs fun _ _ _ _ _ _ _ hvs' => .ret hvs'
  | exit f hargs =>
    intro _ G' mat₁ mat₂ hG hmat
    dsimp only [cmpSink]
    exact matArgs_wf hG hmat hargs fun _ _ _ _ _ _ _ has' => .exit f has'
  | hlt =>
    intro _ _ _ _ _ _
    exact .hlt
  | group _ _ ihb ihk =>
    intro next G' mat₁ mat₂ hG hmat
    dsimp only [cmpSink]
    refine .group (fun Js₁ Js₂ => WfB.of_get fun i xs₁ xs₂ => ?_) fun Js₁ Js₂ => ?_
    · rw [cmpSinkB_get, cmpSinkB_get]
      exact ihb Js₁ Js₂ i (freshSVals _ xs₁ next) (freshSVals _ xs₂ next) (next + _)
        (hG.freshSVals xs₁ xs₂ next) (hmat.weaken fun _ h => List.mem_append_right _ h)
    · exact ihk Js₁ Js₂ next hG hmat

private def SValGood (env : Nat → Bool) : {t : Ty} → SVal Val t → Val t → Prop
  | _, .val a _, v => a.val = v
  | .bool, .defer d, v => d.co.evalBits d.lhs.val d.rhs.val = v ∧ env d.id = v

private def SGoodCtx (env : Nat → Bool) (bound : Nat) (G : Ctx (SVal Val) Val) : Prop :=
  ∀ p ∈ G, SValGood env p.2.1 p.2.2 ∧ svalId p.2.1 < bound

private def MatGood (env : Nat → Bool) (bound : Nat) (mat : List (Nat × Val .bool)) : Prop :=
  ∀ id v, lookupMat id mat = some v → id < bound ∧ env id = v

private theorem SGoodCtx.mono {env env' : Nat → Bool} {b b' : Nat} {G : Ctx (SVal Val) Val}
    (hle : b ≤ b') (henv : ∀ i, i < b → env' i = env i) (hG : SGoodCtx env b G) :
    SGoodCtx env' b' G := by
  intro p hp
  obtain ⟨hv, hlt⟩ := hG p hp
  refine ⟨?_, Nat.lt_of_lt_of_le hlt hle⟩
  rcases p with ⟨t, s, v⟩
  cases s with
  | val _ _ => exact hv
  | defer d =>
    dsimp only [SValGood] at hv ⊢
    dsimp only [svalId] at hlt
    exact ⟨hv.1, (henv d.id hlt).trans hv.2⟩

private theorem MatGood.mono {env env' : Nat → Bool} {b b' : Nat} {mat : List (Nat × Val .bool)}
    (hle : b ≤ b') (henv : ∀ i, i < b → env' i = env i) (hmat : MatGood env b mat) :
    MatGood env' b' mat := by
  intro id v hlk
  obtain ⟨hlt, hv⟩ := hmat id v hlk
  exact ⟨Nat.lt_of_lt_of_le hlt hle, (henv id hlt).trans hv⟩

private theorem SGoodCtx.freshSVals {env : Nat → Bool} {b : Nat} {G : Ctx (SVal Val) Val}
    (hG : SGoodCtx env b G) :
    {ts : List Ty} → (xs : Tup Val ts) →
    SGoodCtx env (b + ts.length) (Tup.zip (freshSVals ts xs b) xs ++ G)
  | [], () => hG
  | _ :: ts, (x, xs) => by
    dsimp only [freshSVals, Tup.zip]
    intro p hp
    cases hp with
    | head =>
      exact ⟨rfl, by
        change b < b + (_ :: ts).length
        simp only [List.length_cons]
        omega⟩
    | tail _ hp =>
      have hG' : SGoodCtx env (b + 1) G := hG.mono (Nat.le_succ b) fun _ _ => rfl
      have := SGoodCtx.freshSVals hG' xs p hp
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1 ts.length] using this

private theorem SGoodCtx.freshOne {env : Nat → Bool} {b : Nat} {G : Ctx (SVal Val) Val}
    (hG : SGoodCtx env b G) {t : Ty} (v : Val t) :
    SGoodCtx env (b + 1) (⟨t, .val (.var v) b, v⟩ :: G) := by
  intro p hp
  cases hp with
  | head => exact ⟨rfl, Nat.lt_succ_self b⟩
  | tail _ hp => exact (hG.mono (Nat.le_succ b) fun _ _ => rfl) p hp

private theorem SGoodCtx.soutBits_val {env : Nat → Bool} {b : Nat} {G : Ctx (SVal Val) Val}
    (hG : SGoodCtx env b G) {n : Nat} {a₁ : Arg (SVal Val) (.bits n)} {a₂ : Arg Val (.bits n)}
    (ha : ArgRel G (.bits n) a₁ a₂) : (soutBits a₁).val = a₂.val := by
  cases ha with
  | imm _ => rfl
  | @var s₁ _ hm =>
    obtain ⟨hv, _⟩ := hG _ hm
    cases s₁ with
    | val _ _ => exact hv

private theorem matArg_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {env : Nat → Bool} {b : Nat} {G : Ctx (SVal Val) Val} {mat : List (Nat × Val .bool)}
    (hG : SGoodCtx env b G) (hmat : MatGood env b mat)
    {t : Ty} {a₁ : Arg (SVal Val) t} {a₂ : Arg Val t} (ha : ArgRel G t a₁ a₂)
    {cont : List (Nat × Val .bool) → Arg Val t → Expr Val Cont rs}
    (hcont : ∀ mat' a₁', MatGood env b mat' → a₁'.val = a₂.val → wp Γ Q X (cont mat' a₁') m) :
    wp Γ Q X (matArg mat a₁ cont) m := by
  cases ha with
  | imm c => exact hcont mat (.imm c) hmat rfl
  | @var s₁ _ hm =>
    obtain ⟨hv, hlt⟩ := hG _ hm
    cases s₁ with
    | val a _ =>
      dsimp only [matArg]
      exact hcont mat a hmat hv
    | defer d =>
      dsimp only [matArg]
      dsimp only [SValGood] at hv
      dsimp only [svalId] at hlt
      cases hlk : lookupMat d.id mat with
      | some v =>
        obtain ⟨_, henv⟩ := hmat d.id v hlk
        exact hcont mat (.var v) hmat (henv.symm.trans hv.2)
      | none =>
        dsimp only [wp, Op.wp, OpCode.wp]
        refine hcont ((d.id, d.co.evalBits d.lhs.val d.rhs.val) :: mat)
          (.var (d.co.evalBits d.lhs.val d.rhs.val)) ?_ hv.1
        intro id' v' hlk'
        dsimp only [lookupMat] at hlk'
        by_cases heq : d.id == id'
        · simp only [heq, ↓reduceIte, Option.some.injEq] at hlk'
          have hid : d.id = id' := beq_iff_eq.mp heq
          subst hid; subst hlk'
          exact ⟨hlt, hv.2.trans hv.1.symm⟩
        · simp only [heq, Bool.false_eq_true, ↓reduceIte] at hlk'
          exact hmat id' v' hlk'

private theorem matArgs_wp {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {env : Nat → Bool} {b : Nat} {G : Ctx (SVal Val) Val} {mat : List (Nat × Val .bool)}
    (hG : SGoodCtx env b G) (hmat : MatGood env b mat) :
    {ts : List Ty} → {as₁ : Tup (Arg (SVal Val)) ts} → {as₂ : Tup (Arg Val) ts} →
    TRel (ArgRel G) as₁ as₂ →
    {cont : List (Nat × Val .bool) → Tup (Arg Val) ts → Expr Val Cont rs} →
    (∀ mat' as₁', MatGood env b mat' → vals as₁' = vals as₂ → wp Γ Q X (cont mat' as₁') m) →
    wp Γ Q X (matArgs mat as₁ cont) m
  | [], (), (), .nil, _, hcont => hcont mat () hmat rfl
  | _ :: _, (_, _), (_, _), .cons ha has, _, hcont =>
    matArg_wp hG hmat ha fun _ a₁' hmat₁ ha' =>
      matArgs_wp hG hmat₁ has fun mat₂ as₁' hmat₂ has' =>
        hcont mat₂ (a₁', as₁') hmat₂ (Prod.ext ha' has')

private theorem mem_tupZip_eq {α : Type} {f : α → Type} :
    {ts : List α} → (Js : Tup f ts) → ∀ p ∈ Tup.zip Js Js, p.2.1 = p.2.2
  | [], (), _, hp => nomatch hp
  | _ :: _, (j, js), p, hp => by
    cases hp with
    | head => rfl
    | tail _ hp => exact mem_tupZip_eq js p hp

private theorem cmpSink_wp_aux {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {G : Ctx (SVal Val) Val} {D : Ctx Cont Cont}
    {e₁ : Expr (SVal Val) Cont rs} {e₂ : Expr Val Cont rs}
    (hwf : Wf G D e₁ e₂) :
    (∀ p ∈ D, p.2.1 = p.2.2) →
    ∀ (next : Nat) (env : Nat → Bool) (mat : List (Nat × Val .bool)),
    SGoodCtx env next G → MatGood env next mat →
    ∀ m, wp Γ Q X e₂ m → wp Γ Q X (cmpSink next mat e₁) m := by
  induction hwf using Wf.induct with
  | @let_ G' _ ts _ _ _ _ hop _ ih =>
    intro hD next env mat hG hmat m hw
    cases hop with
    | @mk _ _ code args₁ args₂ hargs =>
      cases code with
      | cmp co t mty h =>
        cases t with
        | bits n =>
          subst h
          rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩
          rcases args₂ with ⟨a₂, b₂, ⟨⟩⟩
          cases hargs with | cons ha hargs =>
          cases hargs with | cons hb _ =>
          dsimp only [cmpSink]
          split
          · dsimp only [wp, Op.wp, OpCode.wp, liftCmp, CmpOp.evalBits] at hw
            have hf : (Ty.bits n).hasFloat = false := rfl
            simp only [hf, Bool.false_eq_true, ↓reduceIte] at hw
            let v : Bool := co.evalBits a₂.val b₂.val
            let env' : Nat → Bool := fun i => if i = next then v else env i
            have henv : ∀ i, i < next → env' i = env i := fun i hi => by
              simp only [env', Nat.ne_of_lt hi, ↓reduceIte]
            have hG' : SGoodCtx env' (next + 1)
                (⟨.bool, .defer ⟨next, n, co, soutBits a₁, soutBits b₁⟩, v⟩ :: G') := by
              intro p hp
              cases hp with
              | head =>
                refine ⟨⟨?_, ?_⟩, Nat.lt_succ_self next⟩
                · dsimp only
                  rw [hG.soutBits_val ha, hG.soutBits_val hb]
                · simp [env']
              | tail _ hp => exact (hG.mono (Nat.le_succ next) henv) p hp
            exact ih (.defer ⟨next, n, co, soutBits a₁, soutBits b₁⟩, ()) (v, ())
              hD (next + 1) env' mat hG'
              (hmat.mono (Nat.le_succ next) henv) m hw
          · dsimp only [wp, Op.wp, op2, vals] at hw ⊢
            rw [hG.soutBits_val ha, hG.soutBits_val hb]
            exact OpCode.wp_mono (.cmp co (.bits n) .bool rfl) (a₂.val, b₂.val, ())
              (fun r hr =>
                ih (.val (.var r.1) next, ()) r hD (next + 1) env mat
                  (hG.freshOne r.1) (hmat.mono (Nat.le_succ next) fun _ _ => rfl) m hr) hw
        | bool | float _ | pair _ _ =>
          dsimp only [cmpSink]
          refine matArgs_wp hG hmat hargs fun mat' _ hmat' heq => ?_
          dsimp only [wp, Op.wp] at hw ⊢
          rw [heq]
          exact OpCode.wp_mono (.cmp co _ mty h) (vals args₂) (fun r hr =>
            ih (freshSVals _ r next) r hD (next + 1) env mat'
              (hG.freshSVals r) (hmat'.mono (Nat.le_succ next) fun _ _ => rfl) m hr) hw
      | _ =>
        dsimp only [cmpSink]
        refine matArgs_wp hG hmat hargs fun mat' _ hmat' heq => ?_
        dsimp only [wp, Op.wp] at hw ⊢
        rw [heq]
        exact OpCode.wp_mono _ (vals args₂) (fun r hr =>
          ih (freshSVals _ r next) r hD (next + _) env mat'
            (hG.freshSVals r) (hmat'.mono (Nat.le_add_right _ _) fun _ _ => rfl) m hr) hw
  | load t ha _ ih =>
    intro hD next env mat hG hmat m ⟨v, hv, hk⟩
    dsimp only [cmpSink]
    refine matArg_wp hG hmat ha fun mat' a₁' hmat' heq => ?_
    dsimp only [wp]
    rw [heq]
    exact ⟨v, hv, ih (.val (.var v) next) v hD (next + 1) env mat'
      (hG.freshOne v) (hmat'.mono (Nat.le_succ next) fun _ _ => rfl) m hk⟩
  | store hv ha _ ih =>
    intro hD next env mat hG hmat m ⟨hok, hk⟩
    dsimp only [cmpSink]
    refine matArg_wp hG hmat hv fun mat₁ v₁' hmat₁ hv' =>
      matArg_wp hG hmat₁ ha fun mat₂ a₁' hmat₂ ha' => ?_
    dsimp only [wp]
    rw [hv', ha']
    exact ⟨hok, ih hD next env mat₂ hG hmat₂ _ hk⟩
  | call f hargs _ ih =>
    intro hD next env mat hG hmat m ⟨P, E, hΓ, hP, hE⟩
    dsimp only [cmpSink]
    refine matArgs_wp hG hmat hargs fun mat' as₁' hmat' heq => ?_
    dsimp only [wp]
    rw [heq]
    exact ⟨P, E, hΓ, fun r m' hp =>
      ih (freshSVals _ r next) r hD (next + _) env mat' (hG.freshSVals r)
        (hmat'.mono (Nat.le_add_right _ _) fun _ _ => rfl) m' (hP r m' hp), hE⟩
  | jnz hc _ _ iht ihe =>
    intro hD next env mat hG hmat m hw
    dsimp only [cmpSink]
    refine matArg_wp hG hmat hc fun mat' c₁' hmat' heq => ?_
    dsimp only [wp] at hw ⊢
    rw [heq]
    exact ⟨fun h => iht hD next env mat' hG hmat' m (hw.1 h),
           fun h => ihe hD next env mat' hG hmat' m (hw.2 h)⟩
  | jump hj hargs =>
    intro hD next env mat hG hmat m hw
    dsimp only [cmpSink]
    refine matArgs_wp hG hmat hargs fun _ _ _ heq => ?_
    dsimp only [wp] at hw ⊢
    have hj_eq : _ = _ := hD _ hj
    dsimp only at hj_eq
    rw [heq, hj_eq]
    exact hw
  | ret hvs =>
    intro _ next env mat hG hmat m hw
    dsimp only [cmpSink]
    refine matArgs_wp hG hmat hvs fun _ _ _ heq => ?_
    dsimp only [wp] at hw ⊢
    rw [heq]
    exact hw
  | exit f hargs =>
    intro _ next env mat hG hmat m hw
    dsimp only [cmpSink]
    refine matArgs_wp hG hmat hargs fun _ _ _ heq => ?_
    dsimp only [wp] at hw ⊢
    rw [heq]
    exact hw
  | hlt =>
    intro _ _ _ _ _ _ _ hw
    exact hw
  | @group _ D' sig b₁ b₂ k₁ k₂ _ hk ihb ihk =>
    intro hD next env mat hG hmat m hw
    dsimp only [cmpSink, wp] at hw ⊢
    intro Js hclosed
    have hD' : ∀ p ∈ (Tup.zip Js Js ++ D'), p.2.1 = p.2.2 := by
      intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · exact mem_tupZip_eq Js p hp
      · exact hD p hp
    have hclosed₂ : Closed Γ Q X (b₂ Js) Js := by
      rw [closed_iff] at hclosed ⊢
      intro ts' i xs m' hb'
      apply hclosed i xs m'
      rw [cmpSinkB_get]
      exact ihb Js Js i (freshSVals _ xs next) xs hD' (next + ts'.length) env mat
        (hG.freshSVals xs) (hmat.mono (Nat.le_add_right _ _) fun _ _ => rfl) m' hb'
    exact ihk Js Js hD' next env mat hG hmat m (hw Js hclosed₂)

private theorem matArg_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    (mat : List (Nat × Unit)) {t : Ty} (a : Arg (SVal (fun _ => Unit)) t)
    {cont : List (Nat × Unit) → Arg (fun _ => Unit) t → Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hcont : ∀ mat' a', (cont mat' a').callsOk allowed exits) :
    (matArg mat a cont).callsOk allowed exits := by
  cases a with
  | imm _ => exact hcont mat _
  | var sv =>
    cases sv with
    | val _ _ => exact hcont mat _
    | defer d =>
      dsimp only [matArg]
      cases lookupMat (V := fun _ => Unit) d.id mat <;> exact hcont _ _

private theorem matArgs_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    (mat : List (Nat × Unit)) :
    {ts : List Ty} → (as : Tup (Arg (SVal (fun _ => Unit))) ts) →
    {cont : List (Nat × Unit) → Tup (Arg (fun _ => Unit)) ts →
      Expr (fun _ => Unit) (fun _ => Unit) rs} →
    (∀ mat' as', (cont mat' as').callsOk allowed exits) →
    (matArgs mat as cont).callsOk allowed exits
  | [], (), _, hcont => hcont mat ()
  | _ :: _, (a, as), _, hcont =>
    matArg_callsOk mat a fun mat' a' =>
      matArgs_callsOk mat' as fun mat'' as' => hcont mat'' (a', as')

private theorem cmpSinkB_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    (next : Nat) (mat : List (Nat × Unit)) :
    {sig : List (List Ty)} →
    (bs : Blocks (SVal (fun _ => Unit)) (fun _ => Unit) rs sig) →
    (∀ {ts} (i : Member ts sig) xs,
      (cmpSink (next + ts.length) mat (bs.get i (freshSVals ts xs next))).callsOk allowed exits) →
    (cmpSinkB next mat bs).callsOk allowed exits
  | _, .nil, _ => trivial
  | _, .cons _ bs, h =>
    ⟨h .here (Tup.units _), cmpSinkB_callsOk next mat bs fun i => h (.there i)⟩

private theorem cmpSink_callsOk_aux {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {G : Ctx (SVal (fun _ => Unit)) (fun _ => Unit)}
    {D : Ctx (fun _ => Unit) (fun _ => Unit)}
    {e₁ : Expr (SVal (fun _ => Unit)) (fun _ => Unit) rs}
    {e₂ : Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ next mat, e₂.callsOk allowed exits → (cmpSink next mat e₁).callsOk allowed exits := by
  induction hwf using Wf.induct with
  | @let_ _ _ ts _ _ _ _ hop _ ih =>
    intro next mat hc
    cases hop with
    | @mk _ _ code args₁ _ _ =>
      cases code with
      | cmp co t _ h =>
        cases t with
        | bits n =>
          subst h
          rcases args₁ with ⟨a₁, b₁, ⟨⟩⟩
          dsimp only [cmpSink]
          split <;> exact ih _ _ (next + 1) mat hc
        | bool | float _ | pair _ _ =>
          dsimp only [cmpSink]
          exact matArgs_callsOk mat args₁ fun mat' _ =>
            ih (freshSVals _ (Tup.units _) next) (Tup.units _) (next + 1) mat' hc
      | _ =>
        dsimp only [cmpSink]
        exact matArgs_callsOk mat args₁ fun mat' _ =>
          ih (freshSVals _ (Tup.units _) next) (Tup.units _) (next + _) mat' hc
  | load _ _ _ ih =>
    intro next mat hc
    dsimp only [cmpSink]
    exact matArg_callsOk mat _ fun mat' _ => ih (.val (.var ()) next) () (next + 1) mat' hc
  | store _ _ _ ih =>
    intro next mat hc
    dsimp only [cmpSink]
    exact matArg_callsOk mat _ fun mat₁ _ =>
      matArg_callsOk mat₁ _ fun mat₂ _ => ih next mat₂ hc
  | call _ args _ ih =>
    intro next mat ⟨hf, hc⟩
    dsimp only [cmpSink]
    exact matArgs_callsOk mat _ fun mat' _ =>
      ⟨hf, ih (freshSVals _ (Tup.units _) next) (Tup.units _) (next + _) mat' hc⟩
  | jnz _ _ _ iht ihe =>
    intro next mat ⟨ht, he⟩
    dsimp only [cmpSink]
    exact matArg_callsOk mat _ fun mat' _ => ⟨iht next mat' ht, ihe next mat' he⟩
  | jump _ _ =>
    intro _ mat _
    dsimp only [cmpSink]
    exact matArgs_callsOk mat _ fun _ _ => trivial
  | ret _ | exit _ _ =>
    intro _ mat hc
    dsimp only [cmpSink]
    exact matArgs_callsOk mat _ fun _ _ => hc
  | hlt =>
    intro _ _ hc
    exact hc
  | @group _ _ sig _ _ _ _ _ _ ihb ihk =>
    intro next mat ⟨hb, hk⟩
    dsimp only [cmpSink, Expr.callsOk]
    refine ⟨cmpSinkB_callsOk next mat _ fun i xs => ?_,
      ihk (Tup.units sig) (Tup.units sig) next mat hk⟩
    exact ihb (Tup.units sig) (Tup.units sig) i (freshSVals _ xs next) (Tup.units _) (next + _) mat
      (Blocks.callsOk_get hb i)

end CmpSinkProofs

/-! ## Closed functions -/

/-- `Func.ifOptCore` preserves relational well-formedness `Func.Wf`. -/
theorem Func.ifOptCore_wf (bitsOnly : Bool) {as rs : List Ty} {f : Func as rs} (hf : f.Wf) :
    (Func.ifOptCore bitsOnly f).Wf := by
  intro V₁ V₂ L₁ L₂ xs₁ xs₂
  have hwf := hf (IVal V₁) (IVal V₂) (JLabel L₁) (JLabel L₂)
    (freshIVals as xs₁ 0) (freshIVals as xs₂ 0)
  have hrel : IRelG (Tup.zip xs₁ xs₂) (Tup.zip (freshIVals as xs₁ 0) (freshIVals as xs₂ 0)) := by
    simpa using IRelG.freshIVals (G := []) (G' := []) (fun _ hp => nomatch hp) xs₁ xs₂ 0
  have hKey : IKeyEq (Tup.zip (freshIVals as xs₁ 0) (freshIVals as xs₂ 0)) := by
    simpa using iKeyEq_freshIVals (G := []) (V₁ := V₁) (V₂ := V₂) (fun _ hp => nomatch hp)
      as xs₁ xs₂ 0
  exact LeanQbe.T.ifOptWith_wf bitsOnly hwf hKey hrel (fun _ hp => nomatch hp) 0 as.length

/-- `Func.cmpSink` preserves relational well-formedness `Func.Wf`. -/
theorem Func.cmpSink_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) :
    (Func.cmpSink f).Wf := by
  intro V₁ V₂ L₁ L₂ xs₁ xs₂
  have hwf := hf (SVal V₁) (SVal V₂) L₁ L₂ (freshSVals as xs₁ 0) (freshSVals as xs₂ 0)
  have hG : CmpSinkProofs.SRelG (Tup.zip xs₁ xs₂)
      (Tup.zip (freshSVals as xs₁ 0) (freshSVals as xs₂ 0)) := by
    simpa using CmpSinkProofs.SRelG.freshSVals (G' := []) (G := [])
      (fun _ hp => nomatch hp) xs₁ xs₂ 0
  exact CmpSinkProofs.cmpSink_wf_aux hwf as.length hG .nil

/-- `Func.ifOptWith` preserves relational well-formedness `Func.Wf`. -/
theorem Func.ifOptWith_wf (bitsOnly : Bool) {as rs : List Ty} {f : Func as rs} (hf : f.Wf) :
    (Func.ifOptWith bitsOnly f).Wf := by
  cases bitsOnly
  · exact Func.ifOptCore_wf false hf
  · exact Func.cmpSink_wf (Func.ifOptCore_wf true hf)

/-- `Func.ifOpt` preserves relational well-formedness `Func.Wf`. -/
theorem Func.ifOpt_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) : (Func.ifOpt f).Wf :=
  Func.ifOptWith_wf false hf

/-- `Func.ifOptBits` preserves relational well-formedness `Func.Wf`. -/
theorem Func.ifOptBits_wf {as rs : List Ty} {f : Func as rs} (hf : f.Wf) :
    (Func.ifOptBits f).Wf :=
  Func.ifOptWith_wf true hf

/-- `Func.ifOptCore` refines function contracts. -/
theorem Func.ifOptCore_spec (bitsOnly : Bool) {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    {Γ : Env} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.ifOptCore bitsOnly f) xs m Q X := by
  have hwf := hf (IVal Val) Val (JLabel Cont) Cont (freshIVals as xs 0) xs
  have hgood : IGood (fupdTup (fun _ _ => default) 0 xs) as.length
      (Tup.zip (freshIVals as xs 0) xs) := by
    simpa using IGood.freshIVals (ρ := fun _ _ => default) (b := 0) (G := [])
      (fun _ hp => nomatch hp) xs
  exact LeanQbe.T.ifOptWith_wp bitsOnly hwf (fun _ hp => nomatch hp) 0 as.length _ hgood m h

/-- `Func.cmpSink` refines function contracts. -/
theorem Func.cmpSink_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    {Γ : Env} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.cmpSink f) xs m Q X := by
  have hwf := hf (SVal Val) Val Cont Cont (freshSVals as xs 0) xs
  have hgood : CmpSinkProofs.SGoodCtx (fun _ => false) as.length
      (Tup.zip (freshSVals as xs 0) xs) := by
    simpa using CmpSinkProofs.SGoodCtx.freshSVals (env := fun _ => false) (b := 0) (G := [])
      (fun _ hp => nomatch hp) xs
  exact CmpSinkProofs.cmpSink_wp_aux hwf (fun _ hp => nomatch hp) as.length (fun _ => false) []
    hgood (fun _ _ h => nomatch h) m h

/-- `Func.ifOptWith` refines function contracts. -/
theorem Func.ifOptWith_spec (bitsOnly : Bool) {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    {Γ : Env} {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.ifOptWith bitsOnly f) xs m Q X := by
  cases bitsOnly
  · exact Func.ifOptCore_spec false hf h
  · exact Func.cmpSink_spec (Func.ifOptCore_wf true hf) (Func.ifOptCore_spec true hf h)

/-- `Func.ifOpt` refines function contracts: any source contract holds on `Func.ifOpt f`. -/
theorem Func.ifOpt_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.ifOpt f) xs m Q X :=
  Func.ifOptWith_spec false hf h

/-- `Func.ifOptBits` refines function contracts on post-`Legal` IR. -/
theorem Func.ifOptBits_spec {as rs : List Ty} {f : Func as rs} (hf : f.Wf) {Γ : Env}
    {xs : Tup Val as} {m : Mem 64} {Q : Post rs} {X : XPost}
    (h : Func.spec Γ f xs m Q X) : Func.spec Γ (Func.ifOptBits f) xs m Q X :=
  Func.ifOptWith_spec true hf h

private theorem tryPureJnzDiamond_callsOk {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} (next : Nat) (c : Arg (IVal (fun _ => Unit)) .bool)
    (t e : Expr (IVal (fun _ => Unit)) (JLabel (fun _ => Unit)) rs)
    {res : Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hp : tryPureJnzDiamond true next c t e = some res) :
    res.callsOk allowed exits := by
  dsimp only [tryPureJnzDiamond] at hp
  cases hff : findFirstJump 8 t with
  | none =>
    rw [hff] at hp; dsimp only at hp
    cases hsel : isSelectSigWith true rs <;> rw [hsel] at hp
    · simp at hp
    · cases h1 : checkArm .ret 2 4 next t with
      | none => rw [h1] at hp; simp at hp
      | some resT =>
        cases h2 : checkArm .ret 2 4 next e with
        | none => rw [h1, h2] at hp; simp at hp
        | some resE =>
          rw [h1, h2] at hp; simp only [↓reduceIte, Option.some.injEq] at hp
          subst hp
          exact hoistJnzArms_callsOk rs resT.1 resE.1 next c t e fun _ => trivial
  | some tgt =>
    rcases tgt with ⟨jTs, jId, _⟩
    rw [hff] at hp; dsimp only at hp
    cases hsel : isSelectSigWith true jTs <;> rw [hsel] at hp
    · simp at hp
    · cases h1 : checkArm (.tag jId jTs) 2 4 next t with
      | none => rw [h1] at hp; simp at hp
      | some resT =>
        cases h2 : checkArm (.tag jId jTs) 2 4 next e with
        | none => rw [h1, h2] at hp; simp at hp
        | some resE =>
          rw [h1, h2] at hp; simp only [↓reduceIte, Option.some.injEq] at hp
          subst hp
          exact hoistJnzArms_callsOk jTs resT.1 resE.1 next c t e fun _ => trivial

private theorem tryStoreJnzDiamond_callsOk {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} (next : Nat) (c : Arg (IVal (fun _ => Unit)) .bool)
    (t e : Expr (IVal (fun _ => Unit)) (JLabel (fun _ => Unit)) rs)
    {res : Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hs : tryStoreJnzDiamond true next c t e = some res) :
    res.callsOk allowed exits := by
  dsimp only [tryStoreJnzDiamond] at hs
  cases hff : findFirstJumpStore 16 t with
  | none =>
    rw [hff] at hs; dsimp only at hs
    cases hsel : isSelectSigWith true rs <;> rw [hsel] at hs
    · simp at hs
    · simp only [↓reduceIte] at hs
      cases hsp : checkStoreArms true .ret next t e <;> rw [hsp] at hs
      · cases hs
      · rename_i sp
        simp only [Option.map_some, Option.some.injEq] at hs
        subst hs
        exact hoistStoreArms_callsOk rs sp next c t e fun _ => trivial
  | some tgt =>
    rcases tgt with ⟨jTs, jId, _⟩
    rw [hff] at hs; dsimp only at hs
    cases hsel : isSelectSigWith true jTs <;> rw [hsel] at hs
    · simp at hs
    · simp only [↓reduceIte] at hs
      cases hsp : checkStoreArms true (.tag jId jTs) next t e <;> rw [hsp] at hs
      · cases hs
      · rename_i sp
        simp only [Option.map_some, Option.some.injEq] at hs
        subst hs
        exact hoistStoreArms_callsOk jTs sp next c t e fun _ => trivial

/-- `ifOptWith` preserves call/exit well-scopedness (`Expr.callsOk`) for any `Wf` expression. -/
theorem ifOptWith_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    (bitsOnly : Bool)
    {G : Ctx (IVal (fun _ => Unit)) (fun _ => Unit)}
    {D : Ctx (JLabel (fun _ => Unit)) (fun _ => Unit)}
    {e₁ : Expr (IVal (fun _ => Unit)) (JLabel (fun _ => Unit)) rs}
    {e₂ : Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ depth next, e₂.callsOk allowed exits →
      (ifOptWith bitsOnly depth next e₁).callsOk allowed exits := by
  induction hwf using Wf.induct with
  | let_ _ _ ih =>
    intro depth next hc
    exact ih (freshIVals _ (Tup.units _) next) (Tup.units _) depth (next + _) hc
  | load _ _ _ ih =>
    intro depth next hc
    exact ih (.var (), .var next) () depth (next + 1) hc
  | store _ _ _ ih =>
    intro depth next hc
    exact ih depth next hc
  | call _ _ _ ih =>
    intro depth next ⟨hf, hc⟩
    exact ⟨hf, ih (freshIVals _ (Tup.units _) next) (Tup.units _) depth (next + _) hc⟩
  | @jnz _ _ c₁ _ t₁ _ e₁' _ _ _ _ iht ihe =>
    intro depth next ⟨ht, he⟩
    dsimp only [ifOptWith]
    cases bitsOnly
    · exact ⟨iht depth next ht, ihe depth next he⟩
    · dsimp only [tryJnzDiamond]
      cases hp : tryPureJnzDiamond true next c₁ t₁ e₁' with
      | some res => exact tryPureJnzDiamond_callsOk next c₁ t₁ e₁' hp
      | none =>
        cases hs : tryStoreJnzDiamond true next c₁ t₁ e₁' with
        | some res => exact tryStoreJnzDiamond_callsOk next c₁ t₁ e₁' hs
        | none => exact ⟨iht depth next ht, ihe depth next he⟩
  | @jump _ _ _ j₁ _ _ _ _ _ =>
    intro depth next _
    cases j₁ <;> exact trivial
  | ret _ | exit _ _ | hlt =>
    intro _ _ hc
    exact hc
  | @group _ _ sig b₁ b₂ k₁ k₂ _ hk ihb ihk =>
    intro depth next ⟨hb, hk_c⟩
    cases bitsOnly
    · cases sig with
      | nil =>
        exact ⟨(ifOptB_callsOk false depth next _ fun i => nomatch i),
          ihk () () depth next hk_c⟩
      | cons ts sig' =>
        cases sig' with
        | nil =>
          dsimp only [ifOptWith, Expr.callsOk]
          refine ⟨ifOptB_callsOk false (depth + 1) next _ fun i xs => ?_, ?_⟩
          · exact ihb _ (Tup.units [ts]) i (freshIVals _ xs next) (Tup.units _)
              (depth + 1) (next + _) (Blocks.callsOk_get hb i)
          · cases hplan : checkDiamondWith false depth ts next (k₁ (.loc depth, ())) with
            | none => exact ihk (JLabel.outer (), ()) ((), ()) (depth + 1) next hk_c
            | some plan =>
              have hsh₂ := hasDiamondShape_of_checkDiamond false depth ts next plan
                (hk (.loc depth, ()) ((), ())) hplan
              exact hoistDiamond_callsOk () plan next (hk (.outer (), ()) ((), ())) hsh₂ hk_c
        | cons ts₂ rest =>
          dsimp only [ifOptWith, Expr.callsOk]
          refine ⟨ifOptB_callsOk false (depth + rest.length + 2) next _ fun i xs => ?_, ?_⟩
          · exact ihb _ (Tup.units _) i (freshIVals _ xs next) (Tup.units _)
              (depth + rest.length + 2) (next + _) (Blocks.callsOk_get hb i)
          · exact ihk _ (Tup.units _) (depth + rest.length + 2) next hk_c
    · rw [ifOptWith_group_true_eq]
      dsimp only [Expr.callsOk]
      refine ⟨ifOptB_callsOk true (depth + sig.length) next _ fun i xs => ?_, ?_⟩
      · exact ihb _ (Tup.units _) i (freshIVals _ xs next) (Tup.units _)
          (depth + sig.length) (next + _) (Blocks.callsOk_get hb i)
      · exact ihk _ (Tup.units _) (depth + sig.length) next hk_c

/-- `ifOpt` preserves call/exit well-scopedness (`Expr.callsOk`). -/
theorem ifOpt_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {G : Ctx (IVal (fun _ => Unit)) (fun _ => Unit)}
    {D : Ctx (JLabel (fun _ => Unit)) (fun _ => Unit)}
    {e₁ : Expr (IVal (fun _ => Unit)) (JLabel (fun _ => Unit)) rs}
    {e₂ : Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ depth next, e₂.callsOk allowed exits → (ifOpt depth next e₁).callsOk allowed exits :=
  ifOptWith_callsOk false hwf

/-- `Func.ifOptCore` preserves call/exit well-scopedness (`callsOk`). -/
theorem Func.ifOptCore_callsOk {allowed : List SigEntry} {exits : List Sym}
    (bitsOnly : Bool) {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.ifOptCore bitsOnly f) (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk
      allowed exits :=
  LeanQbe.T.ifOptWith_callsOk bitsOnly
    (hf (IVal (fun _ => Unit)) (fun _ => Unit) (JLabel (fun _ => Unit)) (fun _ => Unit)
      (freshIVals as (Tup.units as) 0) (Tup.units as))
    0 as.length hc

/-- `Func.cmpSink` preserves call/exit well-scopedness (`callsOk`). -/
theorem Func.cmpSink_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.cmpSink f) (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk
      allowed exits :=
  CmpSinkProofs.cmpSink_callsOk_aux
    (hf (SVal (fun _ => Unit)) (fun _ => Unit) (fun _ => Unit) (fun _ => Unit)
      (freshSVals as (Tup.units as) 0) (Tup.units as))
    as.length [] hc

/-- `Func.ifOptWith` preserves call/exit well-scopedness (`callsOk`). -/
theorem Func.ifOptWith_callsOk {allowed : List SigEntry} {exits : List Sym}
    (bitsOnly : Bool) {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.ifOptWith bitsOnly f) (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk
      allowed exits := by
  cases bitsOnly
  · exact Func.ifOptCore_callsOk false hf hc
  · exact Func.cmpSink_callsOk (Func.ifOptCore_wf true hf) (Func.ifOptCore_callsOk true hf hc)

/-- `Func.ifOpt` preserves call/exit well-scopedness (`callsOk`). -/
theorem Func.ifOpt_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.ifOpt f) (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits :=
  Func.ifOptWith_callsOk false hf hc

/-- `Func.ifOptBits` preserves call/exit well-scopedness (`callsOk`). -/
theorem Func.ifOptBits_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.ifOptBits f) (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits :=
  Func.ifOptWith_callsOk true hf hc

end LeanQbe.T
