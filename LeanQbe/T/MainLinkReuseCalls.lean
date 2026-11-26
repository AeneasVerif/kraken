module

public import LeanQbe.T.Opt
public import LeanQbe.T.Main
public import LeanQbe.T.MainLinkReuseLegalCalls
import LeanQbe.T.OptLemmas
import LeanQbe.T.LegalLemmas
import LeanQbe.T.FoldLemmas
import LeanQbe.T.CanonLemmas
import LeanQbe.T.CopyLemmas
import LeanQbe.T.GvnLemmas
import LeanQbe.T.DivConstLemmas
import LeanQbe.T.DceLemmas
import LeanQbe.T.DceParamLemmas
import LeanQbe.T.MemLoadLemmas
import LeanQbe.T.SimplifyGroupPlanLemmas
import LeanQbe.T.PeelLemmas
import LeanQbe.T.LicmLemmas
import LeanQbe.T.LicmRoLemmas
import LeanQbe.T.IfOptLemmas
import LeanQbe.T.ZeroPeelLemmas
import LeanQbe.T.AssumeBitsLemmas
import LeanQbe.T.AddrRangeOptLemmas
import LeanQbe.T.LoopRotateLemmas
import LeanQbe.T.CondThreadOptLemmas
import LeanQbe.T.TailDupLemmas

/-!
# Mid-End Call & Exit Preservation (`MainLinkReuseCalls`)

Proves that every pre-legal and post-legal optimization pass in `Fn.mid` preserves
`Expr.callsOk`, culminating in:

* `Fn.earlyOpt_callsOk`
* `Fn.mid_callsOk`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

/-! ## Raw pre-legal call/exit collectors and monotonicity -/

mutual
/-- Collect deduplicated `(callee, argTys, retTys)` triples from pre-legal expressions. -/
@[expose] def Expr.rawCallsAux {rs : List Ty} (acc : List SigEntry) :
    Expr (fun _ => Unit) (fun _ => Unit) rs → List SigEntry
  | .let_ _ k => Expr.rawCallsAux acc (k (Tup.units _))
  | .load _ _ k => Expr.rawCallsAux acc (k ())
  | .store _ _ k => Expr.rawCallsAux acc k
  | .call f (as := as) (bs := bs) _ k =>
    let acc' := if (f, as, bs) ∈ acc then acc else (f, as, bs) :: acc
    Expr.rawCallsAux acc' (k (Tup.units bs))
  | .jnz _ t e => Expr.rawCallsAux (Expr.rawCallsAux acc t) e
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => acc
  | .group (sig := sig) bodies k =>
    Expr.rawCallsAux (Blocks.rawCallsAux acc (bodies (Tup.units sig))) (k (Tup.units sig))

/-- Block-list companion of `Expr.rawCallsAux`. -/
@[expose] def Blocks.rawCallsAux {rs : List Ty} (acc : List SigEntry) :
    {sig : List (List Ty)} → Blocks (fun _ => Unit) (fun _ => Unit) rs sig → List SigEntry
  | _, .nil => acc
  | ts :: _, .cons b bs =>
    Blocks.rawCallsAux (Expr.rawCallsAux acc (b (Tup.units ts))) bs
end

/-- Deduplicated pre-legal callees of `f`. -/
@[expose] def Fn.rawCalls (f : Fn) : List SigEntry :=
  (Expr.rawCallsAux [] (f.body (fun _ => Unit) (fun _ => Unit) (Tup.units f.as))).reverse

mutual
/-- Collect deduplicated abnormal-exit symbols from expressions. -/
@[expose] def Expr.rawExitsAux {rs : List Ty} (acc : List Sym) :
    Expr (fun _ => Unit) (fun _ => Unit) rs → List Sym
  | .let_ _ k => Expr.rawExitsAux acc (k (Tup.units _))
  | .load _ _ k => Expr.rawExitsAux acc (k ())
  | .store _ _ k => Expr.rawExitsAux acc k
  | .call _ (bs := bs) _ k => Expr.rawExitsAux acc (k (Tup.units bs))
  | .jnz _ t e => Expr.rawExitsAux (Expr.rawExitsAux acc t) e
  | .jump _ _ | .ret _ | .hlt => acc
  | .exit g _ => if g ∈ acc then acc else g :: acc
  | .group (sig := sig) bodies k =>
    Expr.rawExitsAux (Blocks.rawExitsAux acc (bodies (Tup.units sig))) (k (Tup.units sig))

/-- Block-list companion of `Expr.rawExitsAux`. -/
@[expose] def Blocks.rawExitsAux {rs : List Ty} (acc : List Sym) :
    {sig : List (List Ty)} → Blocks (fun _ => Unit) (fun _ => Unit) rs sig → List Sym
  | _, .nil => acc
  | ts :: _, .cons b bs =>
    Blocks.rawExitsAux (Expr.rawExitsAux acc (b (Tup.units ts))) bs
end

/-- Deduplicated abnormal-exit symbols of `f`. -/
@[expose] def Fn.rawExits (f : Fn) : List Sym :=
  (Expr.rawExitsAux [] (f.body (fun _ => Unit) (fun _ => Unit) (Tup.units f.as))).reverse

private theorem tup_units_unit_eq {α : Type} :
    ∀ {ts : List α} (xs : Tup (fun _ => Unit) ts), xs = Tup.units ts
  | [], () => rfl
  | _ :: _, ((), rest) => congrArg ((), ·) (tup_units_unit_eq rest)

private theorem blocks_callsOk_of_get_unit {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} :
    ∀ {sig : List (List Ty)} (bs : Blocks (fun _ => Unit) (fun _ => Unit) rs sig),
      (∀ {ts} (i : Member ts sig) (xs : Tup (fun _ => Unit) ts),
        (bs.get i xs).callsOk allowed exits) →
      bs.callsOk allowed exits
  | _, .nil, _ => trivial
  | _, .cons _ _, h =>
    ⟨h .here (Tup.units _), blocks_callsOk_of_get_unit _ fun i => h (.there i)⟩

/-- `Expr.callsOk` is monotone in both `allowed` and `exits`. -/
theorem Expr.callsOk_mono_both {a₁ a₂ : List SigEntry} {x₁ x₂ : List Sym}
    (ha : ∀ c, c ∈ a₁ → c ∈ a₂) (hx : ∀ g, g ∈ x₁ → g ∈ x₂) {rs : List Ty}
    (e : Expr (fun _ => Unit) (fun _ => Unit) rs) (hc : e.callsOk a₁ x₁) :
    e.callsOk a₂ x₂ := by
  induction e using Expr.induct with
  | let_ _ _ ih => exact ih _ hc
  | load _ _ _ ih => exact ih _ hc
  | store _ _ _ ih => exact ih hc
  | call f _ _ ih => exact ⟨ha _ hc.1, ih _ hc.2⟩
  | jnz _ _ _ iht ihe => exact ⟨iht hc.1, ihe hc.2⟩
  | jump _ _ | ret _ | hlt => exact hc
  | exit _ _ => exact hx _ hc
  | group _ _ ihb ihk =>
    refine ⟨blocks_callsOk_of_get_unit _ fun i xs => ?_, ihk (Tup.units _) ?_⟩
    · rw [tup_units_unit_eq xs]
      exact ihb (Tup.units _) i (Tup.units _) (Blocks.callsOk_get hc.1 i)
    · exact hc.2

mutual
private theorem expr_rawCallsAux_acc {rs : List Ty} (acc : List SigEntry) {x : SigEntry}
    (hx : x ∈ acc) : (e : Expr (fun _ => Unit) (fun _ => Unit) rs) →
    x ∈ Expr.rawCallsAux acc e
  | .let_ _ k => expr_rawCallsAux_acc acc hx (k (Tup.units _))
  | .load _ _ k => expr_rawCallsAux_acc acc hx (k ())
  | .store _ _ k => expr_rawCallsAux_acc acc hx k
  | .call f (as := as) (bs := bs) _ k => by
    dsimp only [Expr.rawCallsAux]
    split
    · exact expr_rawCallsAux_acc acc hx (k (Tup.units bs))
    · exact expr_rawCallsAux_acc _ (List.mem_cons_of_mem _ hx) (k (Tup.units bs))
  | .jnz _ t e =>
    expr_rawCallsAux_acc _ (expr_rawCallsAux_acc acc hx t) e
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => hx
  | .group (sig := sig) bodies k =>
    expr_rawCallsAux_acc _ (blocks_rawCallsAux_acc acc hx (bodies (Tup.units sig)))
      (k (Tup.units sig))

private theorem blocks_rawCallsAux_acc {rs : List Ty} (acc : List SigEntry) {x : SigEntry}
    (hx : x ∈ acc) : {sig : List (List Ty)} →
    (bs : Blocks (fun _ => Unit) (fun _ => Unit) rs sig) → x ∈ Blocks.rawCallsAux acc bs
  | _, .nil => hx
  | ts :: _, .cons b bs =>
    blocks_rawCallsAux_acc _ (expr_rawCallsAux_acc acc hx (b (Tup.units ts))) bs
end

mutual
private theorem expr_rawExitsAux_acc {rs : List Ty} (acc : List Sym) {x : Sym}
    (hx : x ∈ acc) : (e : Expr (fun _ => Unit) (fun _ => Unit) rs) →
    x ∈ Expr.rawExitsAux acc e
  | .let_ _ k => expr_rawExitsAux_acc acc hx (k (Tup.units _))
  | .load _ _ k => expr_rawExitsAux_acc acc hx (k ())
  | .store _ _ k => expr_rawExitsAux_acc acc hx k
  | .call _ (bs := bs) _ k => expr_rawExitsAux_acc acc hx (k (Tup.units bs))
  | .jnz _ t e =>
    expr_rawExitsAux_acc _ (expr_rawExitsAux_acc acc hx t) e
  | .jump _ _ | .ret _ | .hlt => hx
  | .exit g _ => by
    dsimp only [Expr.rawExitsAux]
    split
    · exact hx
    · exact List.mem_cons_of_mem _ hx
  | .group (sig := sig) bodies k =>
    expr_rawExitsAux_acc _ (blocks_rawExitsAux_acc acc hx (bodies (Tup.units sig)))
      (k (Tup.units sig))

private theorem blocks_rawExitsAux_acc {rs : List Ty} (acc : List Sym) {x : Sym}
    (hx : x ∈ acc) : {sig : List (List Ty)} →
    (bs : Blocks (fun _ => Unit) (fun _ => Unit) rs sig) → x ∈ Blocks.rawExitsAux acc bs
  | _, .nil => hx
  | ts :: _, .cons b bs =>
    blocks_rawExitsAux_acc _ (expr_rawExitsAux_acc acc hx (b (Tup.units ts))) bs
end

private theorem blocks_callsOk_mono_both {a₁ a₂ : List SigEntry} {x₁ x₂ : List Sym}
    (ha : ∀ c, c ∈ a₁ → c ∈ a₂) (hx : ∀ g, g ∈ x₁ → g ∈ x₂) {rs : List Ty} :
    {sig : List (List Ty)} → (bs : Blocks (fun _ => Unit) (fun _ => Unit) rs sig) →
    bs.callsOk a₁ x₁ → bs.callsOk a₂ x₂
  | _, .nil, _ => trivial
  | _, .cons b bs, h =>
    ⟨Expr.callsOk_mono_both ha hx (b (Tup.units _)) h.1, blocks_callsOk_mono_both ha hx bs h.2⟩

mutual
private theorem expr_callsOk_rawAux {rs : List Ty} (acc : List SigEntry) (eacc : List Sym) :
    (e : Expr (fun _ => Unit) (fun _ => Unit) rs) →
    e.callsOk (Expr.rawCallsAux acc e) (Expr.rawExitsAux eacc e)
  | .let_ _ k => expr_callsOk_rawAux acc eacc (k (Tup.units _))
  | .load _ _ k => expr_callsOk_rawAux acc eacc (k ())
  | .store _ _ k => expr_callsOk_rawAux acc eacc k
  | .call f (as := as) (bs := bs) _ k => by
    dsimp only [Expr.callsOk, Expr.rawCallsAux, Expr.rawExitsAux]
    have hmem : (f, as, bs) ∈ (if (f, as, bs) ∈ acc then acc else (f, as, bs) :: acc) := by
      split
      · assumption
      · exact List.mem_cons_self
    exact ⟨expr_rawCallsAux_acc _ hmem _, expr_callsOk_rawAux _ eacc (k (Tup.units bs))⟩
  | .jnz _ t e =>
    ⟨Expr.callsOk_mono_both (fun _ h => expr_rawCallsAux_acc _ h e)
        (fun _ h => expr_rawExitsAux_acc _ h e) t (expr_callsOk_rawAux acc eacc t),
      expr_callsOk_rawAux (Expr.rawCallsAux acc t) (Expr.rawExitsAux eacc t) e⟩
  | .jump _ _ | .ret _ | .hlt => trivial
  | .exit g _ => by
    dsimp only [Expr.callsOk, Expr.rawExitsAux]
    split
    · assumption
    · exact List.mem_cons_self
  | .group (sig := sig) bodies k => by
    dsimp only [Expr.callsOk, Expr.rawCallsAux, Expr.rawExitsAux]
    refine ⟨blocks_callsOk_mono_both
        (fun _ h => expr_rawCallsAux_acc _ h (k (Tup.units sig)))
        (fun _ h => expr_rawExitsAux_acc _ h (k (Tup.units sig)))
        (bodies (Tup.units sig)) (blocks_callsOk_rawAux acc eacc (bodies (Tup.units sig))),
      expr_callsOk_rawAux (Blocks.rawCallsAux acc (bodies (Tup.units sig)))
        (Blocks.rawExitsAux eacc (bodies (Tup.units sig))) (k (Tup.units sig))⟩

private theorem blocks_callsOk_rawAux {rs : List Ty} (acc : List SigEntry) (eacc : List Sym) :
    {sig : List (List Ty)} → (bs : Blocks (fun _ => Unit) (fun _ => Unit) rs sig) →
    bs.callsOk (Blocks.rawCallsAux acc bs) (Blocks.rawExitsAux eacc bs)
  | _, .nil => trivial
  | ts :: _, .cons b bs => by
    dsimp only [Blocks.callsOk, Blocks.rawCallsAux, Blocks.rawExitsAux]
    refine ⟨Expr.callsOk_mono_both
        (fun _ h => blocks_rawCallsAux_acc _ h bs)
        (fun _ h => blocks_rawExitsAux_acc _ h bs)
        (b (Tup.units ts)) (expr_callsOk_rawAux acc eacc (b (Tup.units ts))),
      blocks_callsOk_rawAux (Expr.rawCallsAux acc (b (Tup.units ts)))
        (Expr.rawExitsAux eacc (b (Tup.units ts))) bs⟩
end

/-- Every closed function satisfies `Fn.callsOk f.rawCalls f.rawExits`. -/
theorem Fn.callsOk_raw (f : Fn) : f.callsOk f.rawCalls f.rawExits :=
  Expr.callsOk_mono_both (fun _ h => List.mem_reverse.mpr h)
    (fun _ h => List.mem_reverse.mpr h)
    (f.body (fun _ => Unit) (fun _ => Unit) (Tup.units f.as))
    (expr_callsOk_rawAux [] [] _)

/-! ## `fold`, `canon`, `copy`, `gvn`, `divConst` `callsOk` preservation -/

private theorem foldExpr_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {G : Ctx (FVal (fun _ => Unit)) (fun _ => Unit)}
    {D : Ctx (fun _ => Unit) (fun _ => Unit)}
    {e₁ : Expr (FVal (fun _ => Unit)) (fun _ => Unit) rs}
    {e₂ : Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ b, e₂.callsOk allowed exits → (fold b e₁).callsOk allowed exits := by
  induction hwf using Wf.induct with
  | @let_ _ _ _ op₁ _ _ _ _ _ ih =>
    intro b hc
    unfold fold
    cases op₁.simpAct with
    | some _ => exact ih _ (Tup.units _) b hc
    | none =>
      cases op₁.simpProv? with
      | some _ => exact ih _ (Tup.units _) b hc
      | none => exact ih _ (Tup.units _) (b + _) hc
  | load _ _ _ ih => intro b hc; exact ih _ () (b + 1) hc
  | store _ _ _ ih => intro b hc; exact ih b hc
  | call _ _ _ ih => intro b ⟨hm, hc⟩; exact ⟨hm, ih _ (Tup.units _) (b + _) hc⟩
  | @jnz _ _ c₁ _ _ _ _ _ _ _ _ iht ihe =>
    intro b ⟨ht, he⟩
    dsimp only [fold]
    cases c₁.fout with
    | imm bv => cases bv <;> first | exact iht b ht | exact ihe b he
    | var _ => exact ⟨iht b ht, ihe b he⟩
  | jump _ _ => intro _ _; trivial
  | ret _ => intro _ _; trivial
  | exit _ _ => intro _ hx; exact hx
  | hlt => intro _ _; trivial
  | group _ _ ihb ihk =>
    intro b ⟨hb, hk⟩
    refine ⟨blocks_callsOk_of_get_unit _ fun i xs => ?_,
      ihk (Tup.units _) (Tup.units _) b hk⟩
    rw [foldB_get, tup_units_unit_eq xs]
    exact ihb (Tup.units _) (Tup.units _) i _ (Tup.units _) (b + _) (Blocks.callsOk_get hb i)

/-- `Func.fold` preserves `Expr.callsOk`. -/
theorem Func.fold_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.fold f) (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits :=
  foldExpr_callsOk (hf (FVal (fun _ => Unit)) (fun _ => Unit) (fun _ => Unit) (fun _ => Unit)
    (freshFVals as (Tup.units as) 0) (Tup.units as)) as.length hc

private theorem canonExpr_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {G : Ctx (CanonVal (fun _ => Unit)) (fun _ => Unit)}
    {D : Ctx (fun _ => Unit) (fun _ => Unit)}
    {e₁ : Expr (CanonVal (fun _ => Unit)) (fun _ => Unit) rs}
    {e₂ : Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ b, e₂.callsOk allowed exits → (canon b e₁).callsOk allowed exits := by
  induction hwf using Wf.induct with
  | let_ _ _ ih => intro b hc; exact ih _ (Tup.units _) (b + _) hc
  | load _ _ _ ih => intro b hc; exact ih _ () (b + 1) hc
  | store _ _ _ ih => intro b hc; exact ih b hc
  | call _ _ _ ih => intro b ⟨hm, hc⟩; exact ⟨hm, ih _ (Tup.units _) (b + _) hc⟩
  | jnz _ _ _ iht ihe => intro b ⟨ht, he⟩; exact ⟨iht b ht, ihe b he⟩
  | jump _ _ => intro _ _; trivial
  | ret _ => intro _ _; trivial
  | exit _ _ => intro _ hx; exact hx
  | hlt => intro _ _; trivial
  | group _ _ ihb ihk =>
    intro b ⟨hb, hk⟩
    refine ⟨blocks_callsOk_of_get_unit _ fun i xs => ?_,
      ihk (Tup.units _) (Tup.units _) b hk⟩
    rw [canonB_get, tup_units_unit_eq xs]
    exact ihb (Tup.units _) (Tup.units _) i _ (Tup.units _) (b + _) (Blocks.callsOk_get hb i)

/-- `Func.canon` preserves `Expr.callsOk`. -/
theorem Func.canon_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.canon f) (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits :=
  canonExpr_callsOk (hf (CanonVal (fun _ => Unit)) (fun _ => Unit) (fun _ => Unit) (fun _ => Unit)
    (freshCanonVals as (Tup.units as) 0) (Tup.units as)) as.length hc

private theorem copyExpr_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {G : Ctx (CVal (fun _ => Unit)) (fun _ => Unit)}
    {D : Ctx (fun _ => Unit) (fun _ => Unit)}
    {e₁ : Expr (CVal (fun _ => Unit)) (fun _ => Unit) rs}
    {e₂ : Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ b, e₂.callsOk allowed exits → (copy b e₁).callsOk allowed exits := by
  induction hwf using Wf.induct with
  | @let_ _ _ _ op₁ _ _ _ _ _ ih =>
    intro b hc
    unfold copy
    cases op₁.copyLet b with
    | elim _ => exact ih _ (Tup.units _) b hc
    | emit _ next' _ => exact ih _ (Tup.units _) next' hc
  | load _ _ _ ih => intro b hc; exact ih _ () (b + 1) hc
  | store _ _ _ ih => intro b hc; exact ih b hc
  | call _ _ _ ih => intro b ⟨hm, hc⟩; exact ⟨hm, ih _ (Tup.units _) (b + _) hc⟩
  | jnz _ _ _ iht ihe => intro b ⟨ht, he⟩; exact ⟨iht b ht, ihe b he⟩
  | jump _ _ => intro _ _; trivial
  | ret _ => intro _ _; trivial
  | exit _ _ => intro _ hx; exact hx
  | hlt => intro _ _; trivial
  | group _ _ ihb ihk =>
    intro b ⟨hb, hk⟩
    refine ⟨blocks_callsOk_of_get_unit _ fun i xs => ?_,
      ihk (Tup.units _) (Tup.units _) b hk⟩
    rw [copyB_get, tup_units_unit_eq xs]
    exact ihb (Tup.units _) (Tup.units _) i _ (Tup.units _) (b + _) (Blocks.callsOk_get hb i)

/-- `Func.copy` preserves `Expr.callsOk`. -/
theorem Func.copy_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.copy f) (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits :=
  copyExpr_callsOk (hf (CVal (fun _ => Unit)) (fun _ => Unit) (fun _ => Unit) (fun _ => Unit)
    (freshCVals as (Tup.units as) 0) (Tup.units as)) as.length hc

private theorem gvnExpr_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {G : Ctx (GVal (fun _ => Unit)) (fun _ => Unit)}
    {D : Ctx (fun _ => Unit) (fun _ => Unit)}
    {e₁ : Expr (GVal (fun _ => Unit)) (fun _ => Unit) rs}
    {e₂ : Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ b tbl, e₂.callsOk allowed exits → (gvn b tbl e₁).callsOk allowed exits := by
  induction hwf using Wf.induct with
  | let_ _ _ ih =>
    intro b tbl hc
    unfold gvn
    dsimp only
    split
    · exact ih _ (Tup.units _) b tbl hc
    · exact ih _ (Tup.units _) (b + _) _ hc
  | load _ _ _ ih => intro b tbl hc; exact ih _ () (b + 1) tbl hc
  | store _ _ _ ih => intro b tbl hc; exact ih b tbl hc
  | call _ _ _ ih => intro b tbl ⟨hm, hc⟩; exact ⟨hm, ih _ (Tup.units _) (b + _) tbl hc⟩
  | jnz _ _ _ iht ihe => intro b tbl ⟨ht, he⟩; exact ⟨iht b tbl ht, ihe b tbl he⟩
  | jump _ _ => intro _ _ _; trivial
  | ret _ => intro _ _ _; trivial
  | exit _ _ => intro _ _ hx; exact hx
  | hlt => intro _ _ _; trivial
  | group _ _ ihb ihk =>
    intro b tbl ⟨hb, hk⟩
    refine ⟨blocks_callsOk_of_get_unit _ fun i xs => ?_,
      ihk (Tup.units _) (Tup.units _) b tbl hk⟩
    rw [gvnB_get, tup_units_unit_eq xs]
    exact ihb (Tup.units _) (Tup.units _) i _ (Tup.units _) (b + _) tbl (Blocks.callsOk_get hb i)

/-- `Func.gvn` preserves `Expr.callsOk`. -/
theorem Func.gvn_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.gvn f) (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits :=
  gvnExpr_callsOk (hf (GVal (fun _ => Unit)) (fun _ => Unit) (fun _ => Unit) (fun _ => Unit)
    (freshGVals as (Tup.units as) 0) (Tup.units as)) as.length .empty hc

section DivConstCalls

variable {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}

private theorem emitUDivConst_callsOk (n : Nat) (x : Arg (fun _ => Unit) (.bits n))
    (d : BitVec n) (k : Arg (fun _ => Unit) (.bits n) → Expr (fun _ => Unit) (fun _ => Unit) rs)
    (hk : ∀ r, (k r).callsOk allowed exits) :
    ∀ e, emitUDivConst n x d k = some e → e.callsOk allowed exits := by
  intro e he
  unfold emitUDivConst at he
  repeat' split at he
  all_goals cases he
  all_goals ((try dsimp only [Expr.callsOk]); exact hk _)

private theorem emitURemConst_callsOk (n : Nat) (x : Arg (fun _ => Unit) (.bits n))
    (d : BitVec n) (k : Arg (fun _ => Unit) (.bits n) → Expr (fun _ => Unit) (fun _ => Unit) rs)
    (hk : ∀ r, (k r).callsOk allowed exits) :
    ∀ e, emitURemConst n x d k = some e → e.callsOk allowed exits := by
  intro e he
  unfold emitURemConst at he
  repeat' split at he
  all_goals try cases he
  all_goals first
    | ((try dsimp only [Expr.callsOk]); exact hk _)
    | exact emitUDivConst_callsOk n x d _ (fun _ => by
        (try dsimp only [Expr.callsOk]); exact hk _) e he

private theorem emitSDivConst_callsOk (n : Nat) (x : Arg (fun _ => Unit) (.bits n))
    (d : BitVec n) (k : Arg (fun _ => Unit) (.bits n) → Expr (fun _ => Unit) (fun _ => Unit) rs)
    (hk : ∀ r, (k r).callsOk allowed exits) :
    ∀ e, emitSDivConst n x d k = some e → e.callsOk allowed exits := by
  intro e he
  unfold emitSDivConst at he
  repeat' split at he
  all_goals cases he
  all_goals
    try dsimp only
    repeat' (first | ((try dsimp only [Expr.callsOk]); exact hk _) | split)

private theorem emitSRemConst_callsOk (n : Nat) (x : Arg (fun _ => Unit) (.bits n))
    (d : BitVec n) (k : Arg (fun _ => Unit) (.bits n) → Expr (fun _ => Unit) (fun _ => Unit) rs)
    (hk : ∀ r, (k r).callsOk allowed exits) :
    ∀ e, emitSRemConst n x d k = some e → e.callsOk allowed exits := by
  intro e he
  unfold emitSRemConst at he
  repeat' split at he
  all_goals try cases he
  all_goals first
    | ((try dsimp only [Expr.callsOk]); exact hk _)
    | exact emitSDivConst_callsOk n x d _ (fun _ => by
        (try dsimp only [Expr.callsOk]); exact hk _) e he

private theorem divConstOp_callsOk {ts : List Ty}
    (op : Op (Arg (fun _ => Unit)) ts)
    (k : Tup (Arg (fun _ => Unit)) ts → Expr (fun _ => Unit) (fun _ => Unit) rs)
    (hk : ∀ res, (k res).callsOk allowed exits) :
    (divConstOp op k).callsOk allowed exits := by
  unfold divConstOp
  try dsimp +zetaHave only
  try dsimp only [Option.getD]
  repeat' (first
    | exact emitUDivConst_callsOk _ _ _ _ (fun _ => hk _) _ (by assumption)
    | exact emitURemConst_callsOk _ _ _ _ (fun _ => hk _) _ (by assumption)
    | exact emitSDivConst_callsOk _ _ _ _ (fun _ => hk _) _ (by assumption)
    | exact emitSRemConst_callsOk _ _ _ _ (fun _ => hk _) _ (by assumption)
    | ((try dsimp only [Expr.callsOk]); exact hk _)
    | (split; try dsimp only [Option.getD]))

end DivConstCalls

private theorem divConstB_get_eq {V : Ty → Type} {L : List Ty → Type} {rs : List Ty} :
    {sig : List (List Ty)} → (bs : Blocks (Arg V) L rs sig) →
    ∀ {ts : List Ty} (i : Member ts sig) (xs : Tup V ts),
    (divConstB bs).get i xs = divConst (bs.get i (toArgTup xs))
  | _ :: _, .cons _ _, _, .here, _ => rfl
  | _ :: _, .cons _ bt, _, .there i', xs => divConstB_get_eq bt i' xs

private theorem divConstExpr_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {G : Ctx (Arg (fun _ => Unit)) (fun _ => Unit)}
    {D : Ctx (fun _ => Unit) (fun _ => Unit)}
    {e₁ : Expr (Arg (fun _ => Unit)) (fun _ => Unit) rs}
    {e₂ : Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hwf : Wf G D e₁ e₂) (hc : e₂.callsOk allowed exits) :
    (divConst e₁).callsOk allowed exits := by
  induction hwf using Wf.induct with
  | let_ _ _ ih =>
    exact divConstOp_callsOk _ _ fun res => ih res (Tup.units _) hc
  | load _ _ _ ih => exact ih (.var ()) () hc
  | store _ _ _ ih => exact ih hc
  | call _ _ _ ih => exact ⟨hc.1, ih (toArgTup _) (Tup.units _) hc.2⟩
  | jnz _ _ _ iht ihe => exact ⟨iht hc.1, ihe hc.2⟩
  | jump _ _ | ret _ | hlt => trivial
  | exit _ _ => exact hc
  | group _ _ ihb ihk =>
    refine ⟨blocks_callsOk_of_get_unit _ fun i xs => ?_, ihk (Tup.units _) (Tup.units _) hc.2⟩
    rw [divConstB_get_eq, tup_units_unit_eq xs]
    exact ihb (Tup.units _) (Tup.units _) i (toArgTup _) (Tup.units _) (Blocks.callsOk_get hc.1 i)

/-- `Func.divConst` preserves `Expr.callsOk`. -/
theorem Func.divConst_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.divConst f) (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits :=
  divConstExpr_callsOk (hf (Arg (fun _ => Unit)) (fun _ => Unit) (fun _ => Unit) (fun _ => Unit)
    (toArgTup (Tup.units as)) (Tup.units as)) hc

/-! ## `memLoad`, `dce`, `dceP`, `assumeElim`, `mergeRets` `callsOk` preservation -/

private def mstGet' :
    MemSumBlocks → {sig : List (List Ty)} → {ts : List Ty} → Member ts sig → MemSumTree
  | .nil, _, _, _ => .leaf
  | .cons kh _, _, _, .here => kh
  | .cons _ kt, _, _, .there i => mstGet' kt i

private theorem memLoadSweepB_get_eq {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (next : Nat) (baseOff : BaseOffMap) (cache : List (CacheEntry V)) :
    {sig : List (List Ty)} → (bsMST : MemSumBlocks) → (bs : Blocks (MVal V) L rs sig) →
    ∀ {ts : List Ty} (i : Member ts sig) (xs : Tup V ts),
    (memLoadSweepB next baseOff cache bsMST bs).get i xs =
      memLoadSweep (next + ts.length) baseOff cache (mstGet' bsMST i)
        (bs.get i (freshMVals ts xs next))
  | _ :: _, .nil, .cons _ _, _, .here, _ => rfl
  | _ :: _, .cons _ _, .cons _ _, _, .here, _ => rfl
  | _ :: _, .nil, .cons _ bst, _, .there i', xs =>
    memLoadSweepB_get_eq next baseOff cache .nil bst i' xs
  | _ :: _, .cons _ ktt, .cons _ bst, _, .there i', xs =>
    memLoadSweepB_get_eq next baseOff cache ktt bst i' xs

private theorem memLoadSweep_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {G : Ctx (MVal (fun _ => Unit)) (fun _ => Unit)}
    {D : Ctx (fun _ => Unit) (fun _ => Unit)}
    {e₁ : Expr (MVal (fun _ => Unit)) (fun _ => Unit) rs}
    {e₂ : Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ next baseOff cache mst, e₂.callsOk allowed exits →
      (memLoadSweep next baseOff cache mst e₁).callsOk allowed exits := by
  induction hwf using Wf.induct with
  | let_ _ _ ih => intro next baseOff cache mst hc; exact ih _ (Tup.units _) _ _ _ _ hc
  | load _ _ _ ih =>
    intro next baseOff cache mst hc
    unfold memLoadSweep
    dsimp only
    split
    · exact ih _ () (next + 1) baseOff cache _ hc
    · exact ih _ () (next + 1) baseOff _ _ hc
  | store _ _ _ ih => intro next baseOff cache mst hc; exact ih next baseOff _ _ hc
  | call _ _ _ ih =>
    intro next baseOff cache mst ⟨hm, hc⟩
    exact ⟨hm, ih _ (Tup.units _) _ baseOff [] _ hc⟩
  | jnz _ _ _ iht ihe =>
    intro next baseOff cache mst ⟨ht, he⟩
    exact ⟨iht next baseOff cache _ ht, ihe next baseOff cache _ he⟩
  | jump _ _ | ret _ | hlt => intro _ _ _ _ _; trivial
  | exit _ _ => intro _ _ _ _ hx; exact hx
  | group _ _ ihb ihk =>
    intro next baseOff cache mst ⟨hb, hk⟩
    unfold memLoadSweep
    dsimp only
    split
    · refine ⟨blocks_callsOk_of_get_unit _ fun i xs => ?_,
        ihk (Tup.units _) (Tup.units _) next baseOff _ _ hk⟩
      rw [memLoadSweepB_get_eq, tup_units_unit_eq xs]
      exact ihb (Tup.units _) (Tup.units _) i _ (Tup.units _) (next + _) baseOff _ _
        (Blocks.callsOk_get hb i)
    · refine ⟨blocks_callsOk_of_get_unit _ fun i xs => ?_,
        ihk (Tup.units _) (Tup.units _) next baseOff _ _ hk⟩
      rw [memLoadSweepB_get_eq, tup_units_unit_eq xs]
      exact ihb (Tup.units _) (Tup.units _) i _ (Tup.units _) (next + _) baseOff _ _
        (Blocks.callsOk_get hb i)

/-- `Func.memLoad` preserves `Expr.callsOk`. -/
theorem Func.memLoad_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.memLoad f) (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits :=
  memLoadSweep_callsOk (hf (MVal (fun _ => Unit)) (fun _ => Unit) (fun _ => Unit)
    (fun _ => Unit) (freshMVals as (Tup.units as) 0) (Tup.units as)) as.length _ [] _ hc

private theorem dceSweepB_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty} :
    {sig : List (List Ty)} → (kbs : KeepBlocks) →
    (bs : Blocks (OptV (fun _ => Unit)) (fun _ => Unit) rs sig) →
    (∀ {ts} (i : Member ts sig) (xs : Tup (OptV (fun _ => Unit)) ts) (kt : KeepTree),
      (dceSweep kt (bs.get i xs)).callsOk allowed exits) →
    (dceSweepB kbs bs).callsOk allowed exits
  | _, _, .nil, _ => trivial
  | _, .nil, .cons _ bt, h =>
    ⟨trivial, dceSweepB_callsOk .nil bt fun i => h (.there i)⟩
  | _, .cons kh kbt, .cons _ bt, h =>
    ⟨h .here (someTup _ (Tup.units _)) kh, dceSweepB_callsOk kbt bt fun i => h (.there i)⟩

private theorem dceSweep_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {G : Ctx (OptV (fun _ => Unit)) (fun _ => Unit)}
    {D : Ctx (fun _ => Unit) (fun _ => Unit)}
    {e₁ : Expr (OptV (fun _ => Unit)) (fun _ => Unit) rs}
    {e₂ : Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ kt, e₂.callsOk allowed exits → (dceSweep kt e₁).callsOk allowed exits := by
  induction hwf using Wf.induct with
  | let_ _ _ ih =>
    intro kt hc
    unfold dceSweep
    cases kt with
    | letNode keep kt' =>
      cases keep <;> exact ih _ (Tup.units _) kt' hc
    | _ => trivial
  | load _ _ _ ih =>
    intro kt hc
    unfold dceSweep
    cases kt with
    | letNode keep kt' =>
      cases keep <;> exact ih _ () kt' hc
    | _ => trivial
  | store _ _ _ ih =>
    intro kt hc
    unfold dceSweep
    cases kt with
    | node1 kt' => exact ih kt' hc
    | _ => trivial
  | call _ _ _ ih =>
    intro kt ⟨hm, hc⟩
    unfold dceSweep
    cases kt with
    | node1 kt' => exact ⟨hm, ih _ (Tup.units _) kt' hc⟩
    | _ => trivial
  | jnz _ _ _ iht ihe =>
    intro kt ⟨ht, he⟩
    unfold dceSweep
    cases kt with
    | node2 ktt kte => exact ⟨iht ktt ht, ihe kte he⟩
    | _ => trivial
  | jump _ _ | ret _ | hlt => intro _ _; unfold dceSweep; trivial
  | exit _ _ =>
    intro kt hx
    unfold dceSweep
    cases kt with
    | leaf => exact hx
    | _ => trivial
  | group _ _ ihb ihk =>
    intro kt ⟨hb, hk⟩
    unfold dceSweep
    cases kt with
    | groupNode kbs ktk =>
      refine ⟨dceSweepB_callsOk kbs _ fun i xs kt' =>
          ihb (Tup.units _) (Tup.units _) i xs (Tup.units _) kt' (Blocks.callsOk_get hb i),
        ihk (Tup.units _) (Tup.units _) ktk hk⟩
    | _ => trivial

/-- `Func.dceWith` (including `Func.dce` and `Func.deadLoadElim`) preserves `Expr.callsOk`. -/
theorem Func.dceWith_callsOk (dropLets dropLoads : Bool)
    {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.dceWith dropLets dropLoads f) (fun _ => Unit) (fun _ => Unit)
      (Tup.units as)).callsOk allowed exits :=
  dceSweep_callsOk (hf (OptV (fun _ => Unit)) (fun _ => Unit) (fun _ => Unit)
    (fun _ => Unit) (someTup as (Tup.units as)) (Tup.units as)) _ hc

/-- `Func.dce` preserves `Expr.callsOk`. -/
theorem Func.dce_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.dce f) (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits :=
  Func.dceWith_callsOk true false hf hc

/-- `Func.deadLoadElim` preserves `Expr.callsOk`. -/
theorem Func.deadLoadElim_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.deadLoadElim f) (fun _ => Unit) (fun _ => Unit)
      (Tup.units as)).callsOk allowed exits :=
  Func.dceWith_callsOk false true hf hc

private theorem dceSweepBP_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty} :
    {sig : List (List Ty)} → (kbs : DceParam.PBlocks) →
    (bs : Blocks (OptV (fun _ => Unit)) (DceParam.NLabel (fun _ => Unit)) rs sig) →
    (∀ {ts} (i : Member ts sig) (xs : Tup (OptV (fun _ => Unit)) ts) (kt : DceParam.PTree),
      (DceParam.dceSweepP kt (bs.get i xs)).callsOk allowed exits) →
    (DceParam.dceSweepBP kbs bs).callsOk allowed exits
  | [], _, .nil, _ => trivial
  | _ :: _, kbs, .cons _ bt, h => by
    dsimp only [DceParam.dceSweepBP, Blocks.callsOk]
    exact ⟨h .here _ kbs.hd, dceSweepBP_callsOk kbs.tl bt fun i => h (.there i)⟩

private theorem dceSweepP_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {G : Ctx (OptV (fun _ => Unit)) (fun _ => Unit)}
    {D : Ctx (DceParam.NLabel (fun _ => Unit)) (fun _ => Unit)}
    {e₁ : Expr (OptV (fun _ => Unit)) (DceParam.NLabel (fun _ => Unit)) rs}
    {e₂ : Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ kt, e₂.callsOk allowed exits → (DceParam.dceSweepP kt e₁).callsOk allowed exits := by
  induction hwf using Wf.induct with
  | let_ _ _ ih =>
    intro kt hc
    unfold DceParam.dceSweepP
    cases kt with
    | letNode keep kt' =>
      cases keep <;> exact ih _ (Tup.units _) kt' hc
    | _ => trivial
  | load _ _ _ ih =>
    intro kt hc
    unfold DceParam.dceSweepP
    cases kt with
    | letNode keep kt' =>
      cases keep <;> exact ih _ () kt' hc
    | _ => trivial
  | store _ _ _ ih =>
    intro kt hc
    unfold DceParam.dceSweepP
    cases kt with
    | node1 kt' => exact ih kt' hc
    | _ => trivial
  | call _ _ _ ih =>
    intro kt ⟨hm, hc⟩
    unfold DceParam.dceSweepP
    cases kt with
    | node1 kt' => exact ⟨hm, ih _ (Tup.units _) kt' hc⟩
    | _ => trivial
  | jnz _ _ _ iht ihe =>
    intro kt ⟨ht, he⟩
    unfold DceParam.dceSweepP
    cases kt with
    | node2 ktt kte => exact ⟨iht ktt ht, ihe kte he⟩
    | _ => trivial
  | jump _ _ | ret _ | hlt => intro _ _; unfold DceParam.dceSweepP; trivial
  | exit _ _ =>
    intro kt hx
    unfold DceParam.dceSweepP
    cases kt with
    | leaf => exact hx
    | _ => trivial
  | @group _ _ sig _ _ _ _ _ _ ihb ihk =>
    intro kt ⟨hb, hk⟩
    unfold DceParam.dceSweepP
    cases kt with
    | groupNode kbs ktk =>
      refine ⟨dceSweepBP_callsOk kbs _ fun i xs kt' =>
          ihb (DceParam.wrapLabels sig _ (Tup.units _)) (Tup.units sig) i xs (Tup.units _) kt'
            (Blocks.callsOk_get hb i),
        ihk (DceParam.wrapLabels sig _ (Tup.units _)) (Tup.units sig) ktk hk⟩
    | _ => trivial

/-- `Func.dcePWith` (including `Func.dceP`) preserves `Expr.callsOk`. -/
theorem Func.dcePWith_callsOk (dl dld : Bool) (rounds : Nat := 0)
    {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.dcePWith dl dld rounds f) (fun _ => Unit) (fun _ => Unit)
      (Tup.units as)).callsOk allowed exits := by
  dsimp only [Func.dcePWith]
  split
  · exact dceSweepP_callsOk (hf (OptV (fun _ => Unit)) (fun _ => Unit)
      (DceParam.NLabel (fun _ => Unit)) (fun _ => Unit) (someTup as (Tup.units as))
      (Tup.units as)) _ hc
  · exact Func.dceWith_callsOk dl dld hf hc

/-- `Func.dceP` preserves `Expr.callsOk`. -/
theorem Func.dceP_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf) (rounds : Nat := 0)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.dceP f rounds) (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits :=
  Func.dcePWith_callsOk true false rounds hf hc

private theorem assumeElimB_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty} :
    {sig : List (List Ty)} → (bs : Blocks (fun _ => Unit) (fun _ => Unit) rs sig) →
    (∀ {ts} (i : Member ts sig) (xs : Tup (fun _ => Unit) ts),
      (assumeElim (bs.get i xs)).callsOk allowed exits) →
    (assumeElimB bs).callsOk allowed exits
  | _, .nil, _ => trivial
  | _, .cons _ bt, h => ⟨h .here (Tup.units _), assumeElimB_callsOk bt fun i => h (.there i)⟩

private theorem expr_assumeElim_callsOk {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} (e : Expr (fun _ => Unit) (fun _ => Unit) rs)
    (hc : e.callsOk allowed exits) : (assumeElim e).callsOk allowed exits := by
  induction e using Expr.induct with
  | let_ _ _ ih => exact ih _ hc
  | load _ _ _ ih => exact ih _ hc
  | store _ _ _ ih => exact ih hc
  | call _ _ _ ih => exact ⟨hc.1, ih _ hc.2⟩
  | jnz c t e iht ihe =>
    dsimp only [assumeElim, mkJnzAssume]
    split
    · exact iht hc.1
    · split
      · exact ihe hc.2
      · exact ⟨iht hc.1, ihe hc.2⟩
  | jump _ _ | ret _ | hlt => trivial
  | exit _ _ => exact hc
  | group _ _ ihb ihk =>
    refine ⟨assumeElimB_callsOk _ fun i xs => ?_, ihk (Tup.units _) hc.2⟩
    rw [tup_units_unit_eq xs]
    exact ihb (Tup.units _) i (Tup.units _) (Blocks.callsOk_get hc.1 i)

/-- `Func.assumeElim` preserves `Expr.callsOk`. -/
theorem Func.assumeElim_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs}
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.assumeElim f) (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits :=
  expr_assumeElim_callsOk _ hc

private theorem expr_mergeRets_callsOk {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} (exitLbl : Unit) (e : Expr (fun _ => Unit) (fun _ => Unit) rs)
    (hc : e.callsOk allowed exits) : (e.mergeRets exitLbl).callsOk allowed exits := by
  induction e using Expr.induct with
  | let_ _ _ ih => exact ih _ hc
  | load _ _ _ ih => exact ih _ hc
  | store _ _ _ ih => exact ih hc
  | call _ _ _ ih => exact ⟨hc.1, ih _ hc.2⟩
  | jnz _ _ _ iht ihe => exact ⟨iht hc.1, ihe hc.2⟩
  | jump _ _ | ret _ | hlt => trivial
  | exit _ _ => exact hc
  | group _ _ ihb ihk =>
    refine ⟨blocks_callsOk_of_get_unit _ fun i xs => ?_, ihk (Tup.units _) hc.2⟩
    rw [Blocks.mergeRets_get, tup_units_unit_eq xs]
    exact ihb (Tup.units _) i (Tup.units _) (Blocks.callsOk_get hc.1 i)

/-- `Func.mergeRets` preserves `Expr.callsOk`. -/
theorem Func.mergeRets_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs}
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.mergeRets f) (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits := by
  rw [Func.mergeRets_eq]
  dsimp only
  split
  · refine ⟨⟨trivial, trivial⟩, expr_mergeRets_callsOk () _ hc⟩
  · exact hc

/-! ## `simplifyGroupPlan`, `simplifyGroupFast`, `peel`, `peelFast` `callsOk` preservation -/

private theorem denoteFunc_reify_callsOk' {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((denoteFunc (reifyFunc f)) (fun _ => Unit) (fun _ => Unit)
      (Tup.units as)).callsOk allowed exits := by
  simpa [denoteFunc, reifyFunc] using
    denote_toTFlat_callsOk
      (hf K (fun _ => Unit) KL (fun _ => Unit) (Tup.levels as 0) (Tup.units as))
      as.length 0 (pushTup (Tup.units as) []) [] hc

section SimplifyGroupCalls

open SgpImpl

private def PlanLblOk (allowed : List SigEntry) (exits : List Sym) {rs : List Ty}
    (D : Ctx (PlanL UnitV (fun _ => Unit) rs) (fun _ => Unit)) : Prop :=
  ∀ p ∈ D, match p.2.1 with
    | .keep _ => True
    | .dead => True
    | .splice body => ∀ args, (body args).callsOk allowed exits

private theorem planLblOk_dead {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {D : Ctx (PlanL UnitV (fun _ => Unit) rs) (fun _ => Unit)}
    (hD : PlanLblOk allowed exits D) :
    ∀ (sig : List (List Ty)) (js₂ : Tup (fun _ => Unit) sig),
      PlanLblOk allowed exits (Tup.zip (deadTup sig) js₂ ++ D)
  | [], (), p, hp => hD p hp
  | _ :: sig, ((), js₂), p, hp => by
    dsimp only [deadTup, Tup.zip, List.cons_append] at hp
    cases hp with
    | head => trivial
    | tail _ hp => exact planLblOk_dead hD sig js₂ p hp

private theorem planLblOk_expand {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {D : Ctx (PlanL UnitV (fun _ => Unit) rs) (fun _ => Unit)}
    (hD : PlanLblOk allowed exits D) :
    ∀ (ks : List Bool) (sig : List (List Ty))
      (js₁ : Tup (fun _ => Unit) (filterSig ks sig)) (js₂ : Tup (fun _ => Unit) sig),
      PlanLblOk allowed exits (Tup.zip (expandKeepLabels ks sig js₁) js₂ ++ D)
  | _, [], (), (), p, hp => hD p hp
  | [], _ :: sig, (), ((), js₂), p, hp => by
    dsimp only [expandKeepLabels, Tup.zip, List.cons_append] at hp
    cases hp with
    | head => trivial
    | tail _ hp => exact planLblOk_dead hD sig js₂ p hp
  | true :: ks, _ :: sig, ((), js₁), ((), js₂), p, hp => by
    dsimp only [expandKeepLabels, Tup.zip, List.cons_append] at hp
    cases hp with
    | head => trivial
    | tail _ hp => exact planLblOk_expand hD ks sig js₁ js₂ p hp
  | false :: ks, _ :: sig, js₁, ((), js₂), p, hp => by
    dsimp only [expandKeepLabels, Tup.zip, List.cons_append] at hp
    cases hp with
    | head => trivial
    | tail _ hp => exact planLblOk_expand hD ks sig js₁ js₂ p hp

private theorem planLblOk_rewriteSpliceLabels {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} {D : Ctx (PlanL UnitV (fun _ => Unit) rs) (fun _ => Unit)}
    (hD : PlanLblOk allowed exits D) :
    ∀ (idx : Nat) (pbs : SimpPlanB) {sig : List (List Ty)}
      (bs : Blocks (Arg UnitV) (PlanL UnitV (fun _ => Unit) rs) rs sig)
      (js₂ : Tup (fun _ => Unit) sig),
      (∀ {ts} (i : Member ts sig) (pb : SimpPlan) (xs : Tup (Arg UnitV) ts),
        (rewriteExpr pb (bs.get i xs)).callsOk allowed exits) →
      PlanLblOk allowed exits (Tup.zip (rewriteSpliceLabels idx pbs bs) js₂ ++ D)
  | _, _, [], .nil, (), _, p, hp => hD p hp
  | 0, .cons pb _, _ :: sig, .cons _ _, ((), js₂), hb, p, hp => by
    dsimp only [rewriteSpliceLabels, Tup.zip, List.cons_append] at hp
    cases hp with
    | head => exact fun args => hb .here pb args
    | tail _ hp => exact planLblOk_dead hD sig js₂ p hp
  | idx + 1, .cons _ pbs, _ :: sig, .cons _ bs, ((), js₂), hb, p, hp => by
    dsimp only [rewriteSpliceLabels, Tup.zip, List.cons_append] at hp
    cases hp with
    | head => trivial
    | tail _ hp =>
      exact planLblOk_rewriteSpliceLabels hD idx pbs bs js₂ (fun i => hb (.there i)) p hp
  | idx, .nil, _ :: sig, .cons _ _, ((), js₂), _, p, hp => by
    cases idx <;> (dsimp only [rewriteSpliceLabels, Tup.zip, List.cons_append] at hp; cases hp with
      | head => trivial | tail _ hp => exact planLblOk_dead hD sig js₂ p hp)

private theorem rewriteFilteredBlocks_callsOk {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} :
    ∀ (ks : List Bool) (pbs : SimpPlanB) {sig : List (List Ty)}
      (bs : Blocks (Arg UnitV) (PlanL UnitV (fun _ => Unit) rs) rs sig),
      (∀ {ts} (i : Member ts sig) (p : SimpPlan) (xs : Tup (Arg UnitV) ts),
        (rewriteExpr p (bs.get i xs)).callsOk allowed exits) →
      (rewriteFilteredBlocks ks pbs bs).callsOk allowed exits
  | [], _, [], .nil, _ => trivial
  | _ :: _, _, [], .nil, _ => trivial
  | [], _, _ :: _, .cons _ _, _ => trivial
  | true :: ks, .cons pb pbs, _ :: _, .cons _ bs, h =>
    ⟨h .here pb (toArgTup (Tup.units _)),
      rewriteFilteredBlocks_callsOk ks pbs bs fun i => h (.there i)⟩
  | false :: ks, .cons _ pbs, _ :: _, .cons _ bs, h =>
    rewriteFilteredBlocks_callsOk ks pbs bs fun i => h (.there i)
  | true :: ks, .nil, _ :: _, .cons _ bs, h =>
    ⟨trivial, rewriteFilteredBlocks_callsOk ks .nil bs fun i => h (.there i)⟩
  | false :: ks, .nil, _ :: _, .cons _ bs, h =>
    rewriteFilteredBlocks_callsOk ks .nil bs fun i => h (.there i)

private theorem rewriteExpr_callsOk {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} {G : Ctx (Arg UnitV) (fun _ => Unit)}
    {D : Ctx (PlanL UnitV (fun _ => Unit) rs) (fun _ => Unit)}
    {e₁ : Expr (Arg UnitV) (PlanL UnitV (fun _ => Unit) rs) rs}
    {e₂ : Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ plan, PlanLblOk allowed exits D → e₂.callsOk allowed exits →
      (rewriteExpr plan e₁).callsOk allowed exits := by
  induction hwf using Wf.induct with
  | let_ _ _ ih =>
    intro plan hD hc
    cases plan <;> try trivial
    exact ih (toArgTup (Tup.units _)) (Tup.units _) _ hD hc
  | load _ _ _ ih =>
    intro plan hD hc
    cases plan <;> try trivial
    exact ih (.var ()) () _ hD hc
  | store _ _ _ ih =>
    intro plan hD hc
    cases plan <;> try trivial
    exact ih _ hD hc
  | call _ _ _ ih =>
    intro plan hD ⟨hm, hc⟩
    cases plan <;> try trivial
    exact ⟨hm, ih (toArgTup (Tup.units _)) (Tup.units _) _ hD hc⟩
  | jnz _ _ _ iht ihe =>
    intro plan hD ⟨ht, he⟩
    cases plan <;> try trivial
    exact ⟨iht _ hD ht, ihe _ hD he⟩
  | @jump _ _ _ j₁ _ _ _ hj _ =>
    intro plan hD _
    have hlbl := hD _ hj
    cases plan with
    | leaf =>
      dsimp only [rewriteExpr]
      cases j₁ with
      | keep _ => trivial
      | dead => trivial
      | splice _ => exact hlbl _
    | _ => trivial
  | ret _ => intro plan _ _; cases plan <;> trivial
  | exit _ _ => intro plan _ hx; cases plan <;> first | exact hx | trivial
  | hlt => intro plan _ _; cases plan <;> trivial
  | @group _ _ sig _ _ _ _ _ _ ihb ihk =>
    intro plan hD ⟨hb, hk⟩
    cases plan with
    | group act pbs pk =>
      cases act with
      | unwrap =>
        exact ihk (deadTup sig) (Tup.units sig) pk (planLblOk_dead hD sig (Tup.units sig)) hk
      | splice idx =>
        exact ihk (rewriteSpliceLabels idx pbs _) (Tup.units sig) pk
          (planLblOk_rewriteSpliceLabels hD idx pbs _ (Tup.units sig) fun i p xs =>
            ihb (deadTup sig) (Tup.units sig) i xs (Tup.units _) p
              (planLblOk_dead hD sig (Tup.units sig)) (Blocks.callsOk_get hb i))
          hk
      | filter keep =>
        refine ⟨rewriteFilteredBlocks_callsOk keep pbs _ fun i p xs =>
            ihb (expandKeepLabels keep sig _) (Tup.units sig) i xs (Tup.units _) p
              (planLblOk_expand hD keep sig _ (Tup.units sig)) (Blocks.callsOk_get hb i),
          ihk (expandKeepLabels keep sig _) (Tup.units sig) pk
            (planLblOk_expand hD keep sig _ (Tup.units sig)) hk⟩
    | _ => trivial

end SimplifyGroupCalls

/-- `Func.simplifyGroupPlan` preserves `Expr.callsOk`. -/
theorem Func.simplifyGroupPlan_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.simplifyGroupPlan f) (fun _ => Unit) (fun _ => Unit)
      (Tup.units as)).callsOk allowed exits := by
  unfold Func.simplifyGroupPlan
  dsimp only
  have hden := denoteFunc_reify_callsOk' hf hc
  split
  · unfold simplifyGroupWithPlan
    split
    · exact rewriteExpr_callsOk
        (Func.renorm_wf f (Arg SgpImpl.UnitV) (fun _ => Unit)
          (SgpImpl.PlanL SgpImpl.UnitV (fun _ => Unit) rs) (fun _ => Unit)
          (toArgTup (Tup.units as)) (Tup.units as))
        _ (fun _ hp => nomatch hp) hden
    · exact hden
  · exact hden

/-- `Func.simplifyGroupFast` preserves `Expr.callsOk`. -/
theorem Func.simplifyGroupFast_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.simplifyGroupFast f) (fun _ => Unit) (fun _ => Unit)
      (Tup.units as)).callsOk allowed exits := by
  rw [Func.simplifyGroupFast_eq]
  dsimp only
  have hden := denoteFunc_reify_callsOk' hf hc
  split
  · exact Func.renorm_callsOk (Func.simplifyGroupPlan_wf (Func.renorm_wf f))
      (Func.simplifyGroupPlan_callsOk (Func.renorm_wf f) hden)
  · exact hden

section PeelCalls

open Peel

private def PeelLblOk (allowed : List SigEntry) (exits : List Sym) {rs : List Ty}
    (D : Ctx (PeelL (fun _ => Unit) (fun _ => Unit) rs) (fun _ => Unit)) : Prop :=
  ∀ p ∈ D, match p.2.1 with
    | .outer _ => True
    | .probe _ => True
    | .subst _ k => ∀ args, (k args).callsOk allowed exits

private theorem peelLblOk_outer {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {D : Ctx (PeelL (fun _ => Unit) (fun _ => Unit) rs) (fun _ => Unit)}
    (hD : PeelLblOk allowed exits D) :
    ∀ (sig : List (List Ty)) (js₁ js₂ : Tup (fun _ => Unit) sig),
      PeelLblOk allowed exits (Tup.zip (toOuterTup js₁) js₂ ++ D)
  | [], (), (), p, hp => hD p hp
  | _ :: sig, ((), js₁), ((), js₂), p, hp => by
    dsimp only [toOuterTup, Tup.zip, List.cons_append] at hp
    cases hp with
    | head => trivial
    | tail _ hp => exact peelLblOk_outer hD sig js₁ js₂ p hp

private theorem peelLblOk_subst {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {D : Ctx (PeelL (fun _ => Unit) (fun _ => Unit) rs) (fun _ => Unit)}
    (hD : PeelLblOk allowed exits D) {ts : List Ty} (id : Nat)
    (k : Tup (Arg (fun _ => Unit)) ts → Expr (fun _ => Unit) (fun _ => Unit) rs)
    (hk : ∀ args, (k args).callsOk allowed exits) :
    PeelLblOk allowed exits (⟨ts, .subst id k, ()⟩ :: D) := by
  intro p hp
  cases hp with
  | head => exact hk
  | tail _ hp => exact hD p hp

private theorem peelArgBAux_fst_eq {rs : List Ty} (budget depth : Nat)
    {ts : List Ty} {sig : List (List Ty)}
    (bs : Blocks (Arg (fun _ => Unit)) (PeelL (fun _ => Unit) (fun _ => Unit) rs) rs (ts :: sig))
    (args : Tup (Arg (fun _ => Unit)) ts) :
    (peelArgBAux budget depth bs).fst args = peelAux budget depth (bs.get .here args) := by
  cases bs with
  | cons _ _ => rfl

private theorem peelBAux_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    (budget depth : Nat) :
    {sig : List (List Ty)} →
    (bs : Blocks (Arg (fun _ => Unit)) (PeelL (fun _ => Unit) (fun _ => Unit) rs) rs sig) →
    (∀ {ts} (i : Member ts sig) (xs : Tup (Arg (fun _ => Unit)) ts),
      (peelAux budget depth (bs.get i xs)).callsOk allowed exits) →
    (peelBAux budget depth bs).callsOk allowed exits
  | _, .nil, _ => trivial
  | _, .cons _ _, h =>
    ⟨h .here (toArgTup (Tup.units _)), peelBAux_callsOk budget depth _ fun i => h (.there i)⟩

private theorem peelAux_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {G : Ctx (Arg (fun _ => Unit)) (fun _ => Unit)}
    {D : Ctx (PeelL (fun _ => Unit) (fun _ => Unit) rs) (fun _ => Unit)}
    {e₁ : Expr (Arg (fun _ => Unit)) (PeelL (fun _ => Unit) (fun _ => Unit) rs) rs}
    {e₂ : Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ budget depth, PeelLblOk allowed exits D → e₂.callsOk allowed exits →
      (peelAux budget depth e₁).callsOk allowed exits := by
  induction hwf using Wf.induct with
  | let_ _ _ ih =>
    intro budget depth hD hc
    exact ih (toArgTup _) (Tup.units _) budget depth hD hc
  | load _ _ _ ih =>
    intro budget depth hD hc
    exact ih (.var ()) () budget depth hD hc
  | store _ _ _ ih =>
    intro budget depth hD hc
    exact ih budget depth hD hc
  | call _ _ _ ih =>
    intro budget depth hD ⟨hm, hc⟩
    exact ⟨hm, ih (toArgTup _) (Tup.units _) budget depth hD hc⟩
  | jnz _ _ _ iht ihe =>
    intro budget depth hD ⟨ht, he⟩
    exact ⟨iht budget depth hD ht, ihe budget depth hD he⟩
  | @jump _ _ _ j₁ _ _ _ hj _ =>
    intro _ _ hD _
    dsimp only [peelAux]
    have hl := hD _ hj
    cases j₁ with
    | subst _ _ => exact hl _
    | outer _ | probe _ => trivial
  | ret _ | hlt => intro _ _ _ _; trivial
  | exit _ _ => intro _ _ _ hx; exact hx
  | @group _ _ sig b₁ _ k₁ _ _ _ ihb ihk =>
    intro budget depth hD ⟨hb, hk⟩
    have hkeep :
        (Expr.group (sig := sig)
          (fun Js => peelBAux budget depth (b₁ (toOuterTup Js)))
          (fun Js => peelAux budget depth (k₁ (toOuterTup Js)))).callsOk allowed exits :=
      ⟨peelBAux_callsOk budget depth _ fun i xs =>
          ihb (toOuterTup (Tup.units sig)) (Tup.units sig) i xs (Tup.units _) budget depth
            (peelLblOk_outer hD sig (Tup.units sig) (Tup.units sig)) (Blocks.callsOk_get hb i),
        ihk (toOuterTup (Tup.units sig)) (Tup.units sig) budget depth
          (peelLblOk_outer hD sig (Tup.units sig) (Tup.units sig)) hk⟩
    rcases sig with _ | ⟨ts, sig'⟩
    · exact hkeep
    · rcases sig' with _ | ⟨ts', sig''⟩
      · dsimp only [peelAux]
        split
        · refine ihk (.subst (2 * depth + 1) _, ()) ((), ()) budget (depth + 1)
            (peelLblOk_subst hD (2 * depth + 1) _ fun args' => ?_) hk
          rw [peelArgBAux_fst_eq]
          refine ihb (.subst (2 * depth) _, ()) ((), ()) .here args' (Tup.units ts)
            ((_ - _) / 2) (depth + 1)
            (peelLblOk_subst hD (2 * depth) _ fun backArgs => ?_)
            (Blocks.callsOk_get hb .here)
          exact ⟨peelBAux_callsOk ((_ - _) / 2) (depth + 1) _ fun i xs =>
              ihb (toOuterTup (Tup.units [ts])) (Tup.units [ts]) i xs (Tup.units _)
                ((_ - _) / 2) (depth + 1)
                (peelLblOk_outer hD [ts] (Tup.units [ts]) (Tup.units [ts]))
                (Blocks.callsOk_get hb i),
            trivial⟩
        · exact hkeep
      · exact hkeep

end PeelCalls

/-- `Func.peel` preserves `Expr.callsOk`. -/
theorem Func.peel_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf) (maxLoopSize : Nat := 40)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.peel f maxLoopSize) (fun _ => Unit) (fun _ => Unit)
      (Tup.units as)).callsOk allowed exits :=
  peelAux_callsOk
    (hf (Arg (fun _ => Unit)) (fun _ => Unit)
      (Peel.PeelL (fun _ => Unit) (fun _ => Unit) rs) (fun _ => Unit)
      (toArgTup (Tup.units as)) (Tup.units as))
    maxLoopSize 0 (fun _ hp => nomatch hp) hc

/-- `Func.peelFast` preserves `Expr.callsOk`. -/
theorem Func.peelFast_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf) (budget : Nat := 24)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.peelFast f budget) (fun _ => Unit) (fun _ => Unit)
      (Tup.units as)).callsOk allowed exits := by
  rw [Func.peelFast_eq f budget]
  dsimp only
  have hden := denoteFunc_reify_callsOk' hf hc
  split
  · exact Func.renorm_callsOk (Func.peel_wf (Func.renorm_wf f) budget)
      (Func.peel_callsOk (Func.renorm_wf f) budget hden)
  · exact hden

/-! ## `licmPure`, `roSweepFunc`, `licm` `callsOk` preservation -/

section LicmCalls

private def hbGet :
    HoistBlocks → {sig : List (List Ty)} → {ts : List Ty} → Member ts sig → HoistPlan
  | .nil, _, _, _ => .leaf
  | .cons kh _, _, _, .here => kh
  | .cons _ kt, _, _, .there i => hbGet kt i

private theorem licmSweepB_get_eq' {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (b : Nat) (env : VEnv V) (tbl : GvnTbl V) :
    {sig : List (List Ty)} → (hbs : HoistBlocks) → (bs : Blocks (GVal V) L rs sig) →
    ∀ {ts : List Ty} (i : Member ts sig) (xs : Tup V ts),
    (licmSweepB b env tbl hbs bs).get i xs =
      licmSweep (b + ts.length) (envInsertTup env b xs) tbl (hbGet hbs i)
        (bs.get i (freshGVals ts xs b))
  | _ :: _, .nil, .cons _ _, _, .here, _ => rfl
  | _ :: _, .cons _ _, .cons _ _, _, .here, _ => rfl
  | _ :: _, .nil, .cons _ bt, _, .there i', xs => licmSweepB_get_eq' b env tbl .nil bt i' xs
  | _ :: _, .cons _ hbt, .cons _ bt, _, .there i', xs => licmSweepB_get_eq' b env tbl hbt bt i' xs

private theorem emitHoists_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    (cont : Nat → VEnv (fun _ => Unit) → GvnTbl (fun _ => Unit) →
      Expr (fun _ => Unit) (fun _ => Unit) rs)
    (hcont : ∀ b env tbl, (cont b env tbl).callsOk allowed exits) :
    ∀ (hoists : List HoistOp) b (env : VEnv (fun _ => Unit)) (tbl : GvnTbl (fun _ => Unit)),
      (emitHoists hoists b env tbl cont).callsOk allowed exits
  | [], b, env, tbl => hcont b env tbl
  | h :: rest, b, env, tbl => by
    dsimp only [emitHoists]
    repeat' (first
      | exact emitHoists_callsOk cont hcont rest _ _ _
      | (dsimp only [Expr.callsOk]; exact emitHoists_callsOk cont hcont rest _ _ _)
      | split)

private theorem licmSweep_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {G : Ctx (GVal (fun _ => Unit)) (fun _ => Unit)}
    {D : Ctx (fun _ => Unit) (fun _ => Unit)}
    {e₁ : Expr (GVal (fun _ => Unit)) (fun _ => Unit) rs}
    {e₂ : Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ b env tbl plan, e₂.callsOk allowed exits →
      (licmSweep b env tbl plan e₁).callsOk allowed exits := by
  induction hwf using Wf.induct with
  | let_ _ _ ih =>
    intro b env tbl plan hc
    unfold licmSweep
    dsimp only
    split
    · exact ih _ (Tup.units _) b env tbl _ hc
    · exact ih _ (Tup.units _) (b + _) (envInsertTup env b _) tbl _ hc
  | load _ _ _ ih =>
    intro b env tbl plan hc
    dsimp only [licmSweep]
    exact ih _ () (b + 1) _ tbl _ hc
  | store _ _ _ ih =>
    intro b env tbl plan hc
    dsimp only [licmSweep]
    exact ih b env tbl _ hc
  | call _ _ _ ih =>
    intro b env tbl plan ⟨hm, hc⟩
    dsimp only [licmSweep, Expr.callsOk]
    exact ⟨hm, ih _ (Tup.units _) (b + _) (envInsertTup env b _) tbl _ hc⟩
  | jnz _ _ _ iht ihe =>
    intro b env tbl plan ⟨ht, he⟩
    dsimp only [licmSweep, Expr.callsOk]
    exact ⟨iht b env tbl _ ht, ihe b env tbl _ he⟩
  | jump _ _ | ret _ | hlt => intro _ _ _ _ _; trivial
  | exit _ _ => intro _ _ _ _ hx; exact hx
  | group _ _ ihb ihk =>
    intro b env tbl plan ⟨hb, hk⟩
    dsimp only [licmSweep]
    refine emitHoists_callsOk _ (fun b' env' tbl' => ?_) _ b env tbl
    refine ⟨blocks_callsOk_of_get_unit _ fun i xs => ?_,
      ihk (Tup.units _) (Tup.units _) b' env' tbl' _ hk⟩
    rw [licmSweepB_get_eq', tup_units_unit_eq xs]
    exact ihb (Tup.units _) (Tup.units _) i _ (Tup.units _) (b' + _)
      (envInsertTup env' b' (Tup.units _)) tbl' _ (Blocks.callsOk_get hb i)

private def rbGet : RoBlocks → {sig : List (List Ty)} → {ts : List Ty} → Member ts sig → RoPlan
  | .nil, _, _, _ => .leaf
  | .cons kh _, _, _, .here => kh
  | .cons _ kt, _, _, .there i => rbGet kt i

private theorem roSweepB_get_eq' {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (b : Nat) (env : VEnv V) :
    {sig : List (List Ty)} → (rbs : RoBlocks) → (bs : Blocks V L rs sig) →
    ∀ {ts : List Ty} (i : Member ts sig) (xs : Tup V ts),
    (roSweepB b env rbs bs).get i xs =
      roSweep (b + ts.length) (envInsertTup env b xs) (rbGet rbs i) (bs.get i xs)
  | _ :: _, .nil, .cons _ _, _, .here, _ => rfl
  | _ :: _, .cons _ _, .cons _ _, _, .here, _ => rfl
  | _ :: _, .nil, .cons _ bt, _, .there i', xs => roSweepB_get_eq' b env .nil bt i' xs
  | _ :: _, .cons _ rbt, .cons _ bt, _, .there i', xs => roSweepB_get_eq' b env rbt bt i' xs

private theorem emitRoHoists_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    (cont : Nat → VEnv (fun _ => Unit) → Expr (fun _ => Unit) (fun _ => Unit) rs)
    (hcont : ∀ b env, (cont b env).callsOk allowed exits) :
    ∀ (hoists : List HoistLoad) b (env : VEnv (fun _ => Unit)),
      (emitRoHoists hoists b env cont).callsOk allowed exits
  | [], b, env => hcont b env
  | h :: rest, b, env => by
    dsimp only [emitRoHoists]
    repeat' (first
      | exact emitRoHoists_callsOk cont hcont rest _ _
      | (dsimp only [Expr.callsOk]; exact emitRoHoists_callsOk cont hcont rest _ _)
      | split)

private theorem roSweep_callsOk {allowed : List SigEntry} {exits : List Sym} {rs : List Ty}
    {G : Ctx (fun _ => Unit) (fun _ => Unit)}
    {D : Ctx (fun _ => Unit) (fun _ => Unit)}
    {e₁ e₂ : Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ b env plan, e₂.callsOk allowed exits →
      (roSweep b env plan e₁).callsOk allowed exits := by
  induction hwf using Wf.induct with
  | let_ _ _ ih =>
    intro b env plan hc
    dsimp only [roSweep, Expr.callsOk]
    exact ih (Tup.units _) (Tup.units _) (b + _) (envInsertTup env b _) _ hc
  | load _ _ _ ih =>
    intro b env plan hc
    unfold roSweep
    cases plan with
    | fwdLoad lvl kPlan =>
      dsimp only
      split
      · split
        · exact ih () () b env kPlan hc
        · exact ih () () (b + 1) _ kPlan hc
      · exact ih () () (b + 1) _ kPlan hc
    | _ => exact ih () () (b + 1) _ _ hc
  | store _ _ _ ih =>
    intro b env plan hc
    dsimp only [roSweep, Expr.callsOk]
    exact ih b env _ hc
  | call _ _ _ ih =>
    intro b env plan ⟨hm, hc⟩
    dsimp only [roSweep, Expr.callsOk]
    exact ⟨hm, ih (Tup.units _) (Tup.units _) (b + _) (envInsertTup env b _) _ hc⟩
  | jnz _ _ _ iht ihe =>
    intro b env plan ⟨ht, he⟩
    dsimp only [roSweep, Expr.callsOk]
    exact ⟨iht b env _ ht, ihe b env _ he⟩
  | jump _ _ | ret _ | hlt => intro _ _ _ _; trivial
  | exit _ _ => intro _ _ _ hx; exact hx
  | group _ _ ihb ihk =>
    intro b env plan ⟨hb, hk⟩
    dsimp only [roSweep]
    refine emitRoHoists_callsOk _ (fun b' env' => ?_) _ b env
    refine ⟨blocks_callsOk_of_get_unit _ fun i xs => ?_,
      ihk (Tup.units _) (Tup.units _) b' env' _ hk⟩
    rw [roSweepB_get_eq', tup_units_unit_eq xs]
    exact ihb (Tup.units _) (Tup.units _) i (Tup.units _) (Tup.units _) (b' + _)
      (envInsertTup env' b' (Tup.units _)) _ (Blocks.callsOk_get hb i)

end LicmCalls

/-- `Func.licmPure` preserves `Expr.callsOk`. -/
theorem Func.licmPure_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.licmPure f) (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits := by
  unfold Func.licmPure
  try dsimp only
  first
  | exact licmSweep_callsOk
      (hf (GVal (fun _ => Unit)) (fun _ => Unit) (fun _ => Unit) (fun _ => Unit)
        (freshGVals as (Tup.units as) 0) (Tup.units as))
      as.length (envInsertTup .empty 0 (Tup.units as)) .empty _ hc
  | (split <;> first
    | exact licmSweep_callsOk
        (hf (GVal (fun _ => Unit)) (fun _ => Unit) (fun _ => Unit) (fun _ => Unit)
          (freshGVals as (Tup.units as) 0) (Tup.units as))
        as.length (envInsertTup .empty 0 (Tup.units as)) _ _ hc
    | exact denoteFunc_reify_callsOk' hf hc
    | exact hc)

/-- `Func.licm` preserves `Expr.callsOk`. -/
theorem Func.licm_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.licm f) (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits := by
  dsimp only [Func.licm]
  have hf1 : f.licmPure.Wf := Func.licmPure_wf hf
  have hc1 := Func.licmPure_callsOk hf hc
  split
  · have hro : ((fun V L xs => roSweep as.length (envInsertTup .empty 0 xs)
        (Licm.buildRoPlan as.length (reifyFunc f.licmPure)) (f.licmPure V L xs))
        (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits :=
      roSweep_callsOk
        (hf1 (fun _ => Unit) (fun _ => Unit) (fun _ => Unit) (fun _ => Unit)
          (Tup.units as) (Tup.units as))
        as.length (envInsertTup .empty 0 (Tup.units as)) _ hc1
    exact Func.licmPure_callsOk (roSweepFunc_wf hf1) hro
  · exact hc1

/-! ## Pipeline composition: `earlyOpt` and `Fn.mid` -/

/-- `Func.earlyCore` preserves `Expr.callsOk`. -/
theorem Func.earlyCore_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.earlyCore f) (fun _ => Unit) (fun _ => Unit)
      (Tup.units as)).callsOk allowed exits := by
  rw [Func.earlyCore_eq]
  have hf1 := Func.fold_wf hf
  have hf2 := Func.canon_wf hf1
  have hf3 := Func.copy_wf hf2
  have hf4 := Func.gvn_wf hf3
  have hf5 := Func.copy_wf hf4
  exact Func.fold_callsOk hf5 (Func.copy_callsOk hf4 (Func.gvn_callsOk hf3
    (Func.copy_callsOk hf2 (Func.canon_callsOk hf1 (Func.fold_callsOk hf hc)))))

/-- Pre-`Legal` mid-end (`Func.earlyOpt`) preserves `Expr.callsOk`. -/
theorem Func.earlyOpt_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.earlyOpt f) (fun _ => Unit) (fun _ => Unit)
      (Tup.units as)).callsOk allowed exits := by
  rw [Func.earlyOpt_eq]
  have hcore := Func.earlyCore_wf hf
  have hif := Func.ifOpt_wf hcore
  have hsg := Func.simplifyGroupFast_wf (Func.ifOpt f.earlyCore)
  have hpeel := Func.peelFast_wf (Func.simplifyGroupFast (Func.ifOpt f.earlyCore)) 24
  have hzp := Func.zeroPeelWith_wf { peelBudget := 24 } hpeel
  have hcp := Func.copy_wf hzp
  have hfd := Func.fold_wf hcp
  have hdc := Func.dceP_wf hfd
  exact Func.renorm_callsOk hdc
    (Func.dceP_callsOk hfd 0
      (Func.fold_callsOk hcp
        (Func.copy_callsOk hzp
          (Func.zeroPeelWith_callsOk { peelBudget := 24 } hpeel
            (Func.peelFast_callsOk hsg 24
              (Func.simplifyGroupFast_callsOk hif
                (Func.ifOpt_callsOk hcore
                  (Func.earlyCore_callsOk hf hc))))))))

/-- Named-function wrapper for `Func.earlyOpt_callsOk`. -/
theorem Fn.earlyOpt_callsOk {allowed : List SigEntry} {exits : List Sym}
    {f : Fn} (hf : f.Wf) (hc : f.callsOk allowed exits) :
    f.earlyOpt.callsOk allowed exits :=
  Func.earlyOpt_callsOk hf hc

/-- `Func.lateCorePre` preserves `Expr.callsOk`. -/
theorem Func.lateCorePre_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.lateCorePre f) (fun _ => Unit) (fun _ => Unit)
      (Tup.units as)).callsOk allowed exits := by
  rw [Func.lateCorePre_eq]
  have hf1 := Func.fold_wf hf
  have hf2 := Func.canon_wf hf1
  have hf3 := Func.divConst_wf hf2
  exact Func.copy_callsOk hf3
    (Func.divConst_callsOk hf2
      (Func.canon_callsOk hf1
        (Func.fold_callsOk hf hc)))

/-- `Func.lateCorePost` preserves `Expr.callsOk`. -/
theorem Func.lateCorePost_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.lateCorePost f) (fun _ => Unit) (fun _ => Unit)
      (Tup.units as)).callsOk allowed exits := by
  rw [Func.lateCorePost_eq]
  have hf1 := Func.memLoad_wf hf
  have hf2 := Func.gvn_wf hf1
  have hf3 := Func.assumeBits_wf hf2
  exact Func.fold_callsOk hf3
    (Func.assumeBits_callsOk hf2
      (Func.gvn_callsOk hf1
        (Func.memLoad_callsOk hf hc)))

private theorem addrRangeSweep_let {V : Ty → Type} {L : List Ty → Type} {ts rs : List Ty}
    (curD next : Nat) (plan : LoopTree) (op : Op (ARVal V) ts)
    (k : Tup (ARVal V) ts → Expr (ARVal V) L rs) :
    addrRangeSweep curD next plan (.let_ op k) =
      let kPlan := plan.step1
      match op.arStep curD next with
      | .elim res => addrRangeSweep curD next kPlan (k res)
      | .emit1 op' wrap =>
        .let_ op' fun xs => addrRangeSweep curD (next + ts.length) kPlan (k (wrap xs))
      | .rangeSubCmp w o x lo width outD =>
        .let_ (op2 (.sub (.bits w)) x (.imm lo)) fun (t, ()) =>
        .let_ (op2 (.cmp o (.bits w)) (.var t) (.imm width)) fun (r, ()) =>
        addrRangeSweep curD (next + 1) kPlan (k (ARVal.fresh r next outD, ()))
      | .addrShl n isSub base inv iv ivD sh _ disp =>
        .let_ (op2 (.shl (.bits n)) inv (.imm (BitVec.ofNat n sh))) fun (t1, ()) =>
        .let_ (op2 (if isSub then .sub (.bits n) else .add (.bits n)) base (.var t1))
          fun (t2, ()) =>
        .let_ (op2 (.shl (.bits n)) iv (.imm (BitVec.ofNat n sh))) fun (t3, ()) =>
        .let_ (op2 (.add (.bits n)) (.var t2) (.var t3)) fun (t4, ()) =>
        if disp == 0#n then
          addrRangeSweep curD (next + 1) kPlan (k (ARVal.fresh t4 next ivD, ()))
        else
          .let_ (op2 (.add (.bits n)) (.var t4) (.imm disp)) fun (t5, ()) =>
          addrRangeSweep curD (next + 1) kPlan (k (ARVal.fresh t5 next ivD, ()))
      | .addrPlain n isSub base inv iv invD ivD disp =>
        .let_ (op2 (if isSub then .sub (.bits n) else .add (.bits n)) base inv) fun (t1, ()) =>
        .let_ (op2 (.add (.bits n)) (.var t1) iv) fun (t2, ()) =>
        if disp == 0#n then
          addrRangeSweep curD (next + 1) kPlan
            (k (⟨.var t2, .var next, ivD,
              { addr? := some (.addVV (.var t1) invD iv ivD 0#n) }⟩, ()))
        else
          .let_ (op2 (.add (.bits n)) (.var t2) (.imm disp)) fun (t3, ()) =>
          addrRangeSweep curD (next + 1) kPlan
            (k (⟨.var t3, .var next, ivD,
              { addr? := some (.addVV (.var t1) invD iv ivD disp) }⟩, ())) := by
  delta addrRangeSweep; dsimp only [Expr.brecOn, Expr.rec, addrRangeSweep._f]
  cases op.arStep curD next <;> rfl

private theorem addrRangeSweep_callsOk {allowed : List SigEntry} {exits : List Sym}
    {rs : List Ty} {G : Ctx (ARVal (fun _ => Unit)) (fun _ => Unit)}
    {D : Ctx (fun _ => Unit) (fun _ => Unit)}
    {e₁ : Expr (ARVal (fun _ => Unit)) (fun _ => Unit) rs}
    {e₂ : Expr (fun _ => Unit) (fun _ => Unit) rs}
    (hwf : Wf G D e₁ e₂) :
    ∀ curD b plan, e₂.callsOk allowed exits →
      (addrRangeSweep curD b plan e₁).callsOk allowed exits := by
  induction hwf using Wf.induct with
  | @let_ _ _ ts op₁ _ _ _ _ _ ih =>
    intro curD b plan hc
    rw [addrRangeSweep_let]
    dsimp only
    split
    · exact ih _ (Tup.units _) curD b _ hc
    · dsimp only [Expr.callsOk]
      exact ih _ (Tup.units _) curD (b + _) _ hc
    · dsimp only [Expr.callsOk]
      exact ih _ (Tup.units _) curD (b + 1) _ hc
    · dsimp only [Expr.callsOk]
      split <;> ((try dsimp only [Expr.callsOk]); exact ih _ (Tup.units _) curD (b + 1) _ hc)
    · dsimp only [Expr.callsOk]
      split <;> ((try dsimp only [Expr.callsOk]); exact ih _ (Tup.units _) curD (b + 1) _ hc)
  | load _ _ _ ih =>
    intro curD b plan hc
    dsimp only [addrRangeSweep]
    exact ih _ () curD (b + 1) _ hc
  | store _ _ _ ih =>
    intro curD b plan hc
    dsimp only [addrRangeSweep]
    exact ih curD b _ hc
  | call _ _ _ ih =>
    intro curD b plan ⟨hm, hc⟩
    dsimp only [addrRangeSweep, Expr.callsOk]
    exact ⟨hm, ih _ (Tup.units _) curD (b + _) _ hc⟩
  | @jnz _ _ c₁ _ _ _ _ _ _ _ _ iht ihe =>
    intro curD b plan ⟨ht, he⟩
    dsimp only [addrRangeSweep]
    cases c₁.arOut with
    | imm bv => cases bv <;> first | exact iht curD b _ ht | exact ihe curD b _ he
    | var _ => exact ⟨iht curD b _ ht, ihe curD b _ he⟩
  | jump _ _ | ret _ | hlt => intro _ _ _ _; trivial
  | exit _ _ => intro _ _ _ hx; exact hx
  | group _ _ ihb ihk =>
    intro curD b plan ⟨hb, hk⟩
    dsimp only [addrRangeSweep, Expr.callsOk]
    refine ⟨blocks_callsOk_of_get_unit _ fun i xs => ?_,
      ihk (Tup.units _) (Tup.units _) curD b _ hk⟩
    rw [addrRangeSweepB_get_eq, tup_units_unit_eq xs]
    exact ihb (Tup.units _) (Tup.units _) i _ (Tup.units _)
      (if (plan.stepGroup.1.get i).1 then curD + 1 else curD) (b + _) _
      (Blocks.callsOk_get hb i)

/-- `Func.addrRangeOpt` preserves `Expr.callsOk`. -/
theorem Func.addrRangeOpt_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.addrRangeOpt f) (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk
      allowed exits := by
  dsimp only [Func.addrRangeOpt]
  split
  · exact addrRangeSweep_callsOk
      (hf (ARVal (fun _ => Unit)) (fun _ => Unit) (fun _ => Unit) (fun _ => Unit)
        (freshARVals 0 as (Tup.units as) 0) (Tup.units as))
      0 as.length _ hc
  · exact hc

/-- `Func.lateCfgPre` preserves `Expr.callsOk`. -/
theorem Func.lateCfgPre_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.lateCfgPre f) (fun _ => Unit) (fun _ => Unit)
      (Tup.units as)).callsOk allowed exits := by
  rw [Func.lateCfgPre_eq]
  have hf1 := Func.ifOptBits_wf hf
  have hf2 := Func.simplifyGroupFast_wf (Func.ifOptBits f)
  have hf3 := Func.deadLoadElim_wf hf2
  have hf4 := Func.assumeElim_wf hf3
  have hf5 := Func.fold_wf hf4
  have hf6 := Func.addrRangeOpt_wf hf5
  exact Func.gvn_callsOk hf6
    (Func.addrRangeOpt_callsOk hf5
      (Func.fold_callsOk hf4
        (Func.assumeElim_callsOk
          (Func.deadLoadElim_callsOk hf2
            (Func.simplifyGroupFast_callsOk hf1
              (Func.ifOptBits_callsOk hf hc))))))

/-- `Func.lateLoopRotate` preserves `Expr.callsOk`. -/
theorem Func.lateLoopRotate_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.lateLoopRotate f) (fun _ => Unit) (fun _ => Unit)
      (Tup.units as)).callsOk allowed exits := by
  rw [Func.lateLoopRotate_eq]
  have hcfg := Func.lateCfgPost_wf hf
  have hpost : ((Func.lateCfgPost f) (fun _ => Unit) (fun _ => Unit)
      (Tup.units as)).callsOk allowed exits := by
    rw [Func.lateCfgPost_eq]
    exact Func.dceP_callsOk (Func.licm_wf hf) 0 (Func.licm_callsOk hf hc)
  exact Func.loopRotate_callsOk hcfg LoopRotate.defaultRotConfig hpost

/-- `Func.lateCondThread` preserves `Expr.callsOk`. -/
theorem Func.lateCondThread_callsOk {allowed : List SigEntry} {exits : List Sym}
    {as rs : List Ty} {f : Func as rs} (hf : f.Wf)
    (hc : (f (fun _ => Unit) (fun _ => Unit) (Tup.units as)).callsOk allowed exits) :
    ((Func.lateCondThread f) (fun _ => Unit) (fun _ => Unit)
      (Tup.units as)).callsOk allowed exits := by
  rw [Func.lateCondThread_eq]
  have hf1 := Func.condThreadLateOpt_wf f
  have hf2 := Func.fold_wf hf1
  have hf3 := Func.dceP_wf hf2
  exact Func.mergeRets_callsOk
    (Func.tailDup_callsOk hf3 {}
      (Func.dceP_callsOk hf2 0
        (Func.fold_callsOk hf1
          (Func.condThreadLateOpt_callsOk hf hc))))

/-- Full mid-end (`Fn.mid lt f`) satisfies `callsOk` with `(f.rawCalls.map (sigEntryLegal lt))`
and `f.rawExits`, without evaluating `Fn.mid` in the kernel. -/
theorem Fn.mid_callsOk (lt : LegalTarget) {f : Fn} (hf : f.Wf) :
    (f.mid lt).callsOk (f.rawCalls.map (sigEntryLegal lt)) f.rawExits := by
  dsimp only [Fn.callsOk, Fn.mid, Fn.midFromEarly]
  rw [Fn.midStage_eq]
  have hearly := Func.earlyOpt_wf hf
  have hc0 : f.callsOk f.rawCalls f.rawExits := Fn.callsOk_raw f
  have hc1 := Func.earlyOpt_callsOk hf hc0
  have hleg := Func.legal_wf lt hearly
  have hc2 := Func.legal_callsOk lt hearly hc1
  have hpre := Func.lateCorePre_wf hleg
  have hc3 := Func.lateCorePre_callsOk hleg hc2
  have hren1 := Func.renorm_wf (Func.lateCorePre (Func.legal lt f.earlyOpt.body))
  have hc4 := Func.renorm_callsOk hpre hc3
  have hpost := Func.lateCorePost_wf hren1
  have hc5 := Func.lateCorePost_callsOk hren1 hc4
  have hren2 := Func.renorm_wf (Func.lateCorePost (Func.renorm (Func.lateCorePre
    (Func.legal lt f.earlyOpt.body))))
  have hc6 := Func.renorm_callsOk hpost hc5
  have hcfg := Func.lateCfgPre_wf hren2
  have hc7 := Func.lateCfgPre_callsOk hren2 hc6
  have hren3 := Func.renorm_wf (Func.lateCfgPre (Func.renorm (Func.lateCorePost
    (Func.renorm (Func.lateCorePre (Func.legal lt f.earlyOpt.body))))))
  have hc8 := Func.renorm_callsOk hcfg hc7
  have hrot := Func.lateLoopRotate_wf hren3
  have hc9 := Func.lateLoopRotate_callsOk hren3 hc8
  have hren4 := Func.renorm_wf (Func.lateLoopRotate (Func.renorm (Func.lateCfgPre
    (Func.renorm (Func.lateCorePost (Func.renorm (Func.lateCorePre
      (Func.legal lt f.earlyOpt.body))))))))
  have hc10 := Func.renorm_callsOk hrot hc9
  have hct := Func.lateCondThread_wf hren4
  have hc11 := Func.lateCondThread_callsOk hren4 hc10
  exact Func.renorm_callsOk hct hc11

end LeanQbe.T
