module
public import LeanQbe.T.Examples.Kissat.Full3
public import LeanQbe.T.Examples.Kissat.FullInv2
public import LeanQbe.T.Examples.Kissat.FullArena
public import LeanQbe.T.Logic.C0Step
public meta import Lean.Elab.Tactic
public meta import LeanQbe.T.Logic.C0Step
public meta import LeanQbe.T.Logic.Rules
import all Kraken.Mem
import all Kraken.Separation
/-! # Kissat `D-Full` Transitive Reduction Specs & Lemmas (`Stage 4`, Part 1) -/
set_option autoImplicit false
@[expose] public section
namespace LeanQbe.T.Examples.Kissat.Full
open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test
/-! ## 1. Strictly scoped tactics and BitVec/C0 arithmetic helpers -/
namespace FullTransTactics
attribute [scoped bv_c0] List.length_set
theorem strip_le_32_64 {P : Prop} (h : P) : 32 ≤ 64 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_32 {P : Prop} (h : P) : 8 ≤ 32 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_64 {P : Prop} (h : P) : 8 ≤ 64 ∧ P := ⟨by decide, h⟩
scoped macro "ft_strip" : tactic =>
  `(tactic| first | apply strip_le_32_64 | apply strip_le_8_32 | apply strip_le_8_64)
scoped macro "ft_unmdata" : tactic =>
  `(tactic| ((try unfold Func.wp); first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _))

section FtWp
variable {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
local notation "K " t => Tup Val [t] → Expr Val Cont rs
theorem ft_wp_copy {t} {a : Arg Val t} {k : K t} (h : wp Γ Q X (k (a.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.copy t) (a, ())) k) m := by simpa only [wp_let_copy_eq] using h
theorem ft_wp_add {n} {a b : Arg Val (.bits n)} {k : K (.bits n)}
    (h : wp Γ Q X (k (a.val + b.val, ())) m) : wp Γ Q X (.let_ (Op.mk (.add _) (a, b, ())) k) m :=
  by simpa only [wp_let_add_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2] using h
theorem ft_wp_sub {n} {a b : Arg Val (.bits n)} {k : K (.bits n)}
    (h : wp Γ Q X (k (a.val - b.val, ())) m) : wp Γ Q X (.let_ (Op.mk (.sub _) (a, b, ())) k) m :=
  by simpa only [wp_let_sub_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2] using h
theorem ft_wp_mul {n} {a b : Arg Val (.bits n)} {k : K (.bits n)}
    (h : wp Γ Q X (k (a.val * b.val, ())) m) : wp Γ Q X (.let_ (Op.mk (.mul _) (a, b, ())) k) m :=
  by simpa only [wp_let_mul_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2] using h
theorem ft_wp_neg {n} {a : Arg Val (.bits n)} {k : K (.bits n)} (h : wp Γ Q X (k (-a.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.neg _) (a, ())) k) m := by
  simpa only [wp_let_neg_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift1] using h
theorem ft_wp_and {n} {a b : Arg Val (.bits n)} {k : K (.bits n)}
    (h : wp Γ Q X (k (a.val &&& b.val, ())) m) : wp Γ Q X (.let_ (Op.mk (.and _) (a, b, ())) k) m :=
  by simpa only [wp_let_and_eq, lift2] using h
theorem ft_wp_or {n} {a b : Arg Val (.bits n)} {k : K (.bits n)}
    (h : wp Γ Q X (k (a.val ||| b.val, ())) m) : wp Γ Q X (.let_ (Op.mk (.or _) (a, b, ())) k) m :=
  by simpa only [wp_let_or_eq, lift2] using h
theorem ft_wp_xor {n} {a b : Arg Val (.bits n)} {k : K (.bits n)}
    (h : wp Γ Q X (k (a.val ^^^ b.val, ())) m) : wp Γ Q X (.let_ (Op.mk (.xor _) (a, b, ())) k) m :=
  by simpa only [wp_let_xor_eq, lift2] using h
private theorem ft_shl1 {n} {a b : Arg Val (.bits n)} {k : K (.bits n)} (hb : b.val.toNat % n = 1)
    (h : wp Γ Q X (k (a.val <<< 1, ())) m) : wp Γ Q X (.let_ (Op.mk (.shl _) (a, b, ())) k) m :=
  by simpa only [wp_let_shl_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2, hb] using h
theorem ft_wp_shl1_64 {a : Arg Val (.bits 64)} {k : K (.bits 64)}
    (h : wp Γ Q X (k (a.val <<< 1, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.shl _) (a, Arg.imm 1#64, ())) k) m := ft_shl1 (by decide) h
theorem ft_wp_shl1_64v {a : Arg Val (.bits 64)} {k : K (.bits 64)}
    (h : wp Γ Q X (k (a.val <<< 1, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.shl _) (a, Arg.var 1#64, ())) k) m := ft_shl1 (by decide) h
theorem ft_wp_shl1_64s {a : Arg Val (.bits 64)} {k : K (.bits 64)}
    (h : wp Γ Q X (k (a.val <<< 1, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.shl _) (a, Arg.var (BitVec.signExtend 64 (1 : BitVec 32)), ())) k)
      m := ft_shl1 (by decide) h
theorem ft_wp_shl1_32 {a : Arg Val (.bits 32)} {k : K (.bits 32)}
    (h : wp Γ Q X (k (a.val <<< 1, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.shl _) (a, Arg.imm 1#32, ())) k) m := ft_shl1 (by decide) h
theorem ft_wp_shl1_32v {a : Arg Val (.bits 32)} {k : K (.bits 32)}
    (h : wp Γ Q X (k (a.val <<< 1, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.shl _) (a, Arg.var 1#32, ())) k) m := ft_shl1 (by decide) h
theorem ft_wp_zext {mW nW} {a : Arg Val (.bits mW)} {k : K (.bits nW)} (hle : mW ≤ nW)
    (h : wp Γ Q X (k (a.val.setWidth nW, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.zext mW nW) (a, ())) k) m := by rw [wp_let_zext_eq]; exact ⟨hle, h⟩
theorem ft_wp_sext {mW nW} {a : Arg Val (.bits mW)} {k : K (.bits nW)} (hle : mW ≤ nW)
    (h : wp Γ Q X (k (a.val.signExtend nW, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.sext mW nW) (a, ())) k) m := by rw [wp_let_sext_eq]; exact ⟨hle, h⟩
theorem ft_wp_sext32_64_1 {k : K (.bits 64)} (h : wp Γ Q X (k (1#64, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.sext 32 64) (Arg.imm 1#32, ())) k) m := by
  simpa only [wp_let_sext_eq] using ⟨by decide, h⟩
theorem ft_wp_sext8_32_0 {k : K (.bits 32)} (h : wp Γ Q X (k (0#32, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.sext 8 32) (Arg.var 0#8, ())) k) m := by
  simpa only [wp_let_sext_eq] using ⟨by decide, h⟩
theorem ft_wp_trunc {mW nW} {a : Arg Val (.bits mW)} {k : K (.bits nW)} (hle : nW ≤ mW)
    (h : wp Γ Q X (k (a.val.setWidth nW, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.trunc mW nW) (a, ())) k) m := by rw [wp_let_trunc_eq]; exact ⟨hle, h⟩
theorem ft_wp_trunc32_8_0 {k : K (.bits 8)} (h : wp Γ Q X (k (0#8, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.trunc 32 8) (Arg.imm 0#32, ())) k) m := by
  simpa only [wp_let_trunc_eq] using ⟨by decide, h⟩
theorem ft_wp_cmp {o n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : wp Γ Q X (k (o.evalBits a.val b.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp o (.bits n) .bool rfl) (a, b, ())) k) m := by
  simpa only [wp_let_cmp_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, cast_eq, liftCmp] using h
theorem ft_wp_cmp_eq {n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : wp Γ Q X (k ((a.val == b.val), ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .eq (.bits n) .bool rfl) (a, b, ())) k) m :=
  ft_wp_cmp (evalBits_eq_beq a.val b.val ▸ h)
theorem ft_wp_cmp_ne {n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : wp Γ Q X (k ((a.val != b.val), ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .ne (.bits n) .bool rfl) (a, b, ())) k) m :=
  ft_wp_cmp (evalBits_ne_bne a.val b.val ▸ h)
theorem ft_wp_cmp_ult {n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : wp Γ Q X (k (a.val.ult b.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .ult (.bits n) .bool rfl) (a, b, ())) k) m :=
  ft_wp_cmp (evalBits_ult_eq a.val b.val ▸ h)
theorem ft_wp_cmp_ule {n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : wp Γ Q X (k (a.val.ule b.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .ule (.bits n) .bool rfl) (a, b, ())) k) m :=
  ft_wp_cmp (evalBits_ule_eq a.val b.val ▸ h)
theorem ft_wp_cmp_ugt {n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : wp Γ Q X (k (b.val.ult a.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .ugt (.bits n) .bool rfl) (a, b, ())) k) m :=
  ft_wp_cmp (evalBits_ugt_eq a.val b.val ▸ h)
theorem ft_wp_cmp_uge {n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : wp Γ Q X (k (b.val.ule a.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .uge (.bits n) .bool rfl) (a, b, ())) k) m :=
  ft_wp_cmp (evalBits_uge_eq a.val b.val ▸ h)
theorem ft_wp_cmp_slt {n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : wp Γ Q X (k (a.val.slt b.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .slt (.bits n) .bool rfl) (a, b, ())) k) m :=
  ft_wp_cmp (evalBits_slt_eq a.val b.val ▸ h)
theorem ft_wp_jump0 {L : Cont []} (h : L () m) : wp (rs := rs) Γ Q X (.jump L ()) m := h
theorem ft_wp_jump1 {t} {L : Cont [t]} {a : Arg Val t} (h : L (a.val, ()) m) :
    wp (rs := rs) Γ Q X (.jump L (a, ())) m := h
theorem ft_wp_jump2 {t1 t2} {L : Cont [t1, t2]} {a : Arg Val t1} {b : Arg Val t2}
    (h : L (a.val, b.val, ()) m) : wp (rs := rs) Γ Q X (.jump L (a, b, ())) m := h
theorem ft_wp_jump3 {t1 t2 t3} {L : Cont [t1, t2, t3]} {a : Arg Val t1}
    {b : Arg Val t2} {d : Arg Val t3} (h : L (a.val, b.val, d.val, ()) m) :
    wp (rs := rs) Γ Q X (.jump L (a, b, d, ())) m := h
end FtWp
theorem ft_wp_ret1 {Γ X m t} {Q : Post [t]} {a : Arg Val t} (h : Q (a.val, ()) m) :
    wp Γ Q X (.ret (a, ())) m := h
section FtMeta
open Lean Elab Tactic Meta
private meta def ftReduceProjOnce (e : Lean.Expr) : Lean.Expr :=
  e.replace fun sub => match sub with
    | .proj ``Prod 0 a => if a.isAppOfArity ``Prod.mk 4 then some (a.getArg! 2) else none
    | .proj ``Prod 1 a => if a.isAppOfArity ``Prod.mk 4 then some (a.getArg! 3) else none
    | _ =>
      if sub.isAppOfArity ``Prod.fst 3 && sub.appArg!.isAppOfArity ``Prod.mk 4 then
        some (sub.appArg!.getArg! 2)
      else if sub.isAppOfArity ``Prod.snd 3 && sub.appArg!.isAppOfArity ``Prod.mk 4 then
        some (sub.appArg!.getArg! 3)
      else if sub.isAppOf ``Arg.val && sub.getAppNumArgs ≥ 1 then
        let a := sub.appArg!
        if (a.isAppOf ``Arg.var || a.isAppOf ``Arg.imm) && a.getAppNumArgs ≥ 1 then some a.appArg!
        else none
      else none
private meta def ftReduceHeadE (e : Lean.Expr) : Lean.Expr :=
  ftReduceProjOnce (ftReduceProjOnce (ftReduceProjOnce e.headBeta))
private meta def ftNormWpGoal (g : MVarId) : TacticM MVarId := do
  let ty := (← instantiateMVars (← g.getType)).consumeMData.headBeta
  if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 then
    let e := ty.getArg! 4; let e' := ftReduceHeadE e
    if e' != e then return ← g.change (mkAppN ty.getAppFn (ty.getAppArgs.set! 4 e'))
  return g
private meta def ftBvNat? (e : Lean.Expr) : Option Nat :=
  let e := e.consumeMData
  if e.isAppOf ``BitVec.ofNat && e.getAppNumArgs == 2 then (e.getArg! 1).nat?
  else if e.isAppOf ``OfNat.ofNat && e.getAppNumArgs == 3 then (e.getArg! 1).nat? else none
private meta def ftFastLetLemma? (op : Lean.Expr) : Option (Name × Bool) :=
  if !(op.isAppOf ``Op.mk && op.getAppNumArgs == 5) then none else
  let code := op.getArg! 3; let args := op.getArg! 4
  let a1 := if args.isAppOfArity ``Prod.mk 4 then some (args.getArg! 2) else none
  let a2 := if args.isAppOfArity ``Prod.mk 4 && (args.getArg! 3).isAppOfArity ``Prod.mk 4
    then some ((args.getArg! 3).getArg! 2) else none
  let isArgNat := fun (o : Option Lean.Expr) (c : Name) (k : Nat) =>
    match o with | some x => x.isAppOf c && ftBvNat? x.appArg! == some k | none => false
  match code.getAppFn.constName? with
  | some ``OpCode.copy => some (``ft_wp_copy, false)
  | some ``OpCode.add => some (``ft_wp_add, false) | some ``OpCode.sub => some (``ft_wp_sub, false)
  | some ``OpCode.mul => some (``ft_wp_mul, false) | some ``OpCode.neg => some (``ft_wp_neg, false)
  | some ``OpCode.and => some (``ft_wp_and, false) | some ``OpCode.or => some (``ft_wp_or, false)
  | some ``OpCode.xor => some (``ft_wp_xor, false)
  | some ``OpCode.shl => if code.getAppNumArgs != 1 then none else
    let t := (code.getArg! 0).consumeMData
    let n := if t.isConstOf ``LeanQbe.T.i64 then some 64
      else if t.isConstOf ``LeanQbe.T.i32 then some 32
      else if t.isAppOfArity ``Ty.bits 1 then t.appArg!.nat? else none
    if n == some 64 && isArgNat a2 ``Arg.imm 1 then some (``ft_wp_shl1_64, false)
    else if n == some 64 && isArgNat a2 ``Arg.var 1 then some (``ft_wp_shl1_64v, false)
    else if n == some 64 && (match a2 with
      | some x => let x := x.consumeMData
        x.isAppOf ``Arg.var && x.appArg!.consumeMData.isAppOf ``BitVec.signExtend
      | none => false) then some (``ft_wp_shl1_64s, false)
    else if n == some 32 && isArgNat a2 ``Arg.imm 1 then some (``ft_wp_shl1_32, false)
    else if n == some 32 && isArgNat a2 ``Arg.var 1 then some (``ft_wp_shl1_32v, false) else none
  | some ``OpCode.zext => some (``ft_wp_zext, true)
  | some ``OpCode.sext =>
    if code.getAppNumArgs == 2 && (code.getArg! 0).nat? == some 32 &&
        (code.getArg! 1).nat? == some 64 && isArgNat a1 ``Arg.imm 1 then
      some (``ft_wp_sext32_64_1, false)
    else if code.getAppNumArgs == 2 && (code.getArg! 0).nat? == some 8 &&
        (code.getArg! 1).nat? == some 32 && isArgNat a1 ``Arg.var 0 then
      some (``ft_wp_sext8_32_0, false)
    else some (``ft_wp_sext, true)
  | some ``OpCode.trunc =>
    if code.getAppNumArgs == 2 && (code.getArg! 0).nat? == some 32 &&
        (code.getArg! 1).nat? == some 8 && isArgNat a1 ``Arg.imm 0 then
      some (``ft_wp_trunc32_8_0, false)
    else some (``ft_wp_trunc, true)
  | some ``OpCode.cmp => if code.getAppNumArgs != 4 then none else
    match (code.getArg! 0).getAppFn.constName? with
    | some ``CmpOp.eq => some (``ft_wp_cmp_eq, false)
    | some ``CmpOp.ne => some (``ft_wp_cmp_ne, false)
    | some ``CmpOp.ult => some (``ft_wp_cmp_ult, false)
    | some ``CmpOp.ule => some (``ft_wp_cmp_ule, false)
    | some ``CmpOp.ugt => some (``ft_wp_cmp_ugt, false)
    | some ``CmpOp.uge => some (``ft_wp_cmp_uge, false)
    | some ``CmpOp.slt => some (``ft_wp_cmp_slt, false) | _ => none
  | _ => none
private meta def ftClearStale (m0 : Lean.Expr) : TacticM Unit := withMainContext do
  let .fvar mId := m0 | return
  for d in (← getLCtx).decls.toArray.reverse do
    let some d := d | continue
    if (← instantiateMVars d.type).isAppOf ``Std.ExtHashMap.sep &&
        (← instantiateMVars d.type).appArg! == m0 then
      try liftMetaTactic1 fun g => some <$> g.clear d.fvarId catch _ => pure ()
  try liftMetaTactic1 fun g => some <$> g.clear mId catch _ => pure ()
private meta def ftFindJoinHyp (J : FVarId) : TacticM (Option Lean.Expr) := withMainContext do
  for d in (← getLCtx).decls.toArray.reverse do
    let some d := d | continue
    let ok ← forallTelescopeReducing d.type fun xs concl => do
      if xs.size < 1 then return false
      return concl.getAppFn.isFVarOf J && (← inferType xs[xs.size - 1]!).isAppOf ``LeanQbe.T.wp
    if ok then return some d.toExpr
  return none

private meta def ftFallbackLetSimp (g : MVarId) (ty : Lean.Expr) : TacticM Bool := do
  let args := ty.getAppArgs; let e := args[4]!.consumeMData.headBeta; let eArgs := e.getAppArgs
  if eArgs.size < 1 then return false
  let orig := eArgs[eArgs.size - 1]!
  let (lctx, mGen, gProof) ← g.withContext do
    let genTy ← withLocalDeclD (← mkFreshUserName `k0) (← inferType orig) fun fv =>
      mkForallFVars #[fv] (mkAppN ty.getAppFn (args.set! 4
        (mkAppN e.getAppFn (eArgs.set! (eArgs.size - 1) fv))))
    let mGen ← mkFreshExprSyntheticOpaqueMVar genTy; return (← getLCtx, mGen, mkApp mGen orig)
  let (fvId, curG) ← mGen.mvarId!.intro1P; setGoals [curG]; let s ← saveState
  try evalTactic (← `(tactic| c0_let_simp)) catch _ => s.restore; return false
  try evalTactic (← `(tactic| simp only [LeanQbe.T.lift1, LeanQbe.T.lift2, LeanQbe.T.lift3,
    LeanQbe.T.liftCmp, LeanQbe.T.Ty.hasFloat, ite_false, ite_true,
    LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm])) catch _ => pure ()
  let mut out : List MVarId := []
  for sg in ← getUnsolvedGoals do
    setGoals [sg]; let sg ← getMainGoal
    let (fullNewTy, extraFVars) ← sg.withContext do
      let sgTy ← instantiateMVars (← sg.getType); let newTy0 := sgTy.replaceFVarId fvId orig
      let newTy := if newTy0.isAppOf ``LeanQbe.T.wp && newTy0.getAppNumArgs == 6 then
          let a := newTy0.getAppArgs; mkAppN newTy0.getAppFn (a.set! 4 a[4]!.consumeMData.headBeta)
        else newTy0
      let extraFVars := (((← getLCtx).decls.toArray.filterMap id |>.filter fun d =>
        !d.isImplementationDetail && (lctx.find? d.fvarId).isNone &&
        d.fvarId != fvId).map (·.fvarId)).map mkFVar
      pure (← mkForallFVars extraFVars newTy, extraFVars)
    let mFull ← g.withContext (mkFreshExprSyntheticOpaqueMVar fullNewTy)
    let mut gFull := mFull.mvarId!
    for _ in extraFVars do let (_, gNext) ← gFull.intro1P; gFull := gNext
    sg.assign (mkAppN mFull extraFVars); out := out ++ [gFull]
  g.assign gProof; setGoals out; return true
meta def ftStepOnce (stopAtGroup splitJnz : Bool) : TacticM Bool := withMainContext do
  let g ← getMainGoal; let ty := (← instantiateMVars (← g.getType)).consumeMData.headBeta
  if ty.isAppOf ``And then evalTactic (← `(tactic| repeat ft_strip)); return true
  if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 then
    let e := (ty.getArg! 4).consumeMData.headBeta
    match e.getAppFn.constName? with
    | some ``LeanQbe.T.Expr.let_ =>
      if e.getAppNumArgs == 6 then
        if let some (lem, hasSide) := ftFastLetLemma? (e.getArg! 4).headBeta then
          let s ← saveState
          try
            let gs ← g.apply (← mkConstWithFreshMVarLevels lem)
            if hasSide && gs.length == 2 then
              setGoals [gs[0]!]; evalTactic (← `(tactic| decide))
              setGoals [← ftNormWpGoal gs[1]!]; return true
            else if !hasSide && gs.length == 1 then setGoals [← ftNormWpGoal gs[0]!]; return true
            s.restore
          catch _ => s.restore
      return ← ftFallbackLetSimp g ty
    | some ``LeanQbe.T.Expr.load =>
      let s ← saveState
      try
        let [hl, hk] := (← g.apply (← mkConstWithFreshMVarLevels ``wp_load_of)).take 2
          | s.restore; return false
        LeanQbe.T.C0Step.memSolve true hl; setGoals [← ftNormWpGoal hk]; return true
      catch _ => s.restore; return false
    | some ``LeanQbe.T.Expr.store =>
      let s ← saveState
      try
        let m0 := ty.getArg! 5
        let [hs, hk] := (← g.apply (← mkConstWithFreshMVarLevels ``wp_store_sep)).take 2
          | s.restore; return false
        LeanQbe.T.C0Step.memSolve false hs; setGoals [hk]
        let mId := mkIdent `m; let hmId := mkIdent `hm
        evalTactic (← `(tactic| intro $mId:ident $hmId:ident; try simp only [LeanQbe.T.Arg.val_var,
          LeanQbe.T.Arg.val_imm, Std.ExtHashMap.sep_emp] at $hmId:ident))
        ftClearStale m0; return true
      catch _ => s.restore; return false
    | some ``LeanQbe.T.Expr.jnz =>
      if !splitJnz || e.getAppNumArgs < 2 then return false
      evalTactic (← `(tactic| refine LeanQbe.T.wp_jnz_of (fun hc => ?_) (fun hc => ?_);
        all_goals (try simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm, bv_c0,
          decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true, Bool.not_eq_false,
          beq_iff_eq, bne_iff_ne, ne_eq] at hc))); return true
    | some ``LeanQbe.T.Expr.jump | some ``LeanQbe.T.Expr.ret =>
      let lems := if e.isAppOf ``LeanQbe.T.Expr.ret then #[``ft_wp_ret1]
        else #[``ft_wp_jump0, ``ft_wp_jump1, ``ft_wp_jump2, ``ft_wp_jump3]
      for lem in lems do
        let s2 ← saveState
        try
          let [hk] ← g.apply (← mkConstWithFreshMVarLevels lem) | s2.restore; continue
          let hkTy ← instantiateMVars (← hk.getType)
          let hkTy' := ftReduceProjOnce (ftReduceProjOnce hkTy)
          setGoals [← if hkTy' != hkTy then hk.change hkTy' else pure hk]; return true
        catch _ => s2.restore
      let s ← saveState
      try evalTactic (← `(tactic| c0_let_simp)); return true catch _ => s.restore; return false
    | some ``LeanQbe.T.Expr.group =>
    if !stopAtGroup && e.getAppNumArgs == 6 then
        if let .lam _ _ b _ := e.getArg! 4 then if !b.hasLooseBVars then
          evalTactic (← `(tactic| refine LeanQbe.T.wp_unroll_group fun J hJ => ?_)); return true
      return false
    | some ``LeanQbe.T.Blocks.get =>
      if e.getAppNumArgs == 8 then
        let bs := (e.getArg! 5).headBeta
        if bs.isAppOf ``Blocks.cons && bs.getAppNumArgs == 7 && (e.getArg! 6).isAppOf ``Member.here
        then do
          let newE := ftReduceHeadE (mkApp (bs.getArg! 5) (e.getArg! 7))
          setGoals [← g.change (mkAppN ty.getAppFn (ty.getAppArgs.set! 4 newE))]; return true
      return false
    | _ => return false
  if let .fvar J := ty.getAppFn then
    if let some h ← ftFindJoinHyp J then setGoals (← (← g.apply h).mapM ftNormWpGoal); return true
  return false
meta partial def ftRunGoals (stopAtGroup : Bool) (fuel : Nat) : TacticM Unit := do
  if fuel = 0 then return
  let mut out : Array MVarId := #[]
  for g in ← getUnsolvedGoals do
    if ← g.isAssigned then continue
    setGoals [g]
    if ← ftStepOnce stopAtGroup false then
      ftRunGoals stopAtGroup (fuel - 1); out := out ++ (← getUnsolvedGoals)
    else out := out.push g
  setGoals out.toList
scoped elab "ft_steps" : tactic => do
  evalTactic (← `(tactic| try ft_unmdata)); ftRunGoals false 250
scoped elab "ft_to_group" : tactic => do
  evalTactic (← `(tactic| try ft_unmdata)); ftRunGoals true 250
scoped elab "ft_split" : tactic => do
  evalTactic (← `(tactic| try ft_unmdata))
  for _ in [0:100] do
    let ty := (← Lean.instantiateMVars (← (← getMainGoal).getType)).consumeMData.headBeta
    if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 &&
        ((ty.getArg! 4).consumeMData.headBeta).isAppOf ``LeanQbe.T.Expr.jnz then
      let _ ← ftStepOnce false true; break
    if !(← ftStepOnce false false) then break
end FtMeta
scoped macro "ft_call" h:term : tactic =>
  `(tactic| (refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_)))
end FullTransTactics
section Helpers
theorem ft_bv32_setWidth64 (x : BitVec 32) : (BitVec.setWidth 64 x).toNat = x.toNat :=
  zext_toNat x (by decide)
theorem ft_bv64_sub1 {f : BitVec 64} (hf : f ≠ 0#64) : (f - 1#64).toNat = f.toNat - 1 := by
  have hpos : 0 < f.toNat :=
    Nat.pos_of_ne_zero fun h0 => hf (BitVec.eq_of_toNat_eq (by simpa using h0))
  bv_omega
theorem ft_bv64_add1 {f : BitVec 64} (hf : f.toNat + 1 < 2 ^ 64) :
    (f + 1#64).toNat = f.toNat + 1 := by bv_omega
theorem ft_bv64_add2 {f : BitVec 64} (hf : f.toNat + 2 < 2 ^ 64) :
    (f + 2#64).toNat = f.toNat + 2 := by bv_omega
theorem ft_bv64_shl1 {x : BitVec 64} (hx : 2 * x.toNat < 2 ^ 64) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm, Nat.mod_eq_of_lt hx]
theorem ft_bv64_shl1_setWidth32 {x : BitVec 64} (hx : 2 * x.toNat < 2 ^ 32) :
    ((x <<< (1 : Nat)).setWidth 32).toNat = 2 * x.toNat := by
  have h1 : (x <<< (1 : Nat)).toNat = 2 * x.toNat := ft_bv64_shl1 (by omega)
  rw [BitVec.toNat_setWidth, h1, Nat.mod_eq_of_lt hx]
private theorem ft_nat_two_mul_or_one (k : Nat) : (2 * k) ||| 1 = 2 * k + 1 := by
  apply Nat.eq_of_testBit_eq; intro i; rw [Nat.testBit_or]
  rcases i with _ | i
  · simp [Nat.testBit_zero]
  · simp [Nat.testBit_succ, show (2 * k + 1) / 2 = k by omega]
theorem ft_bv64_shl1_or1_setWidth32 {x : BitVec 64} (hx : 2 * x.toNat + 1 < 2 ^ 32) :
    (((x <<< (1 : Nat)) ||| 1#64).setWidth 32).toNat = 2 * x.toNat + 1 := by
  have h1 : (x <<< (1 : Nat)).toNat = 2 * x.toNat := ft_bv64_shl1 (by omega)
  have hor : ((x <<< (1 : Nat)) ||| 1#64).toNat = 2 * x.toNat + 1 := by
    rw [BitVec.toNat_or, h1, show (1#64 : BitVec 64).toNat = 1 from rfl, ft_nat_two_mul_or_one]
  rw [BitVec.toNat_setWidth, hor, Nat.mod_eq_of_lt hx]
theorem ft_bv32_xor1 (x : BitVec 32) : (x ^^^ 1#32).toNat = x.toNat ^^^ 1 := by
  simp [BitVec.toNat_xor]
theorem ft_i8_vals_slt0 {x : BitVec 8} (hx : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8) :
    (x.signExtend 32).slt 0#32 = true ↔ x = 0xFF#8 := by rcases hx with rfl | rfl | rfl <;> decide
theorem ft_tomb_mask7f : (0xFFFFFFFF#32 &&& 0x7FFFFFFF#32).toNat = 0x7FFFFFFF := by decide
theorem ft_tomb_bin_flag : (0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32 := by decide
end Helpers
/-! ## 2. Canonical Stage-4 invariants and `FullTransSpecs` -/
namespace FullTransSpecs
def FullMrkZero (c : FullCfg) (s : FullState) : Prop :=
  ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8
def FullLitMarksClear (c : FullCfg) (s : FullState) : Prop :=
  FullMrkZero c s ∧ (∀ l < 2 * c.max_vars, s.core.lit_mark[l]?.getD 0#8 = 0#8)
def FullArenaVarsNodup (s : FullState) : Prop :=
  ∀ r ∈ fullArenaClauseRefs s, fullArenaClauseGarb s r = false →
    ((fullArenaClauseLits s r).map (· / 2)).Nodup
def FullLastLearnedWf (s : FullState) : Prop :=
  ∀ i < 8, let cr := s.scratch.last_learned[i]?.getD 0xFFFFFFFF#32
    cr = 0xFFFFFFFF#32 ∨ cr.toNat ∈ fullArenaClauseRefs s
def FullExtScratchOk (c : FullCfg) (s : FullState) : Prop :=
  FullLastLearnedWf s ∧ s.scratch.extend_len ≤ c.extend_cap
def FullExtScratchPres (s s' : FullState) : Prop :=
  s'.scratch.last_learned = s.scratch.last_learned ∧
  s'.scratch.extend_len = s.scratch.extend_len
def FullProbeScratchPres (s s' : FullState) : Prop :=
  FullExtScratchPres s s' ∧ s'.scratch.work_stk1 = s.scratch.work_stk1 ∧
  s'.scratch.work_stk2 = s.scratch.work_stk2 ∧ s'.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
  s'.scratch.scratch_buf = s.scratch.scratch_buf ∧ s'.scratch.ant_sz = s.scratch.ant_sz ∧
  s'.scratch.res_sz = s.scratch.res_sz ∧ s'.scratch.sim_sig = s.scratch.sim_sig
def FullSparseInv (c : FullCfg) (F0 : CNF Nat) (s : FullState) : Prop :=
  FullCoreInv c F0 s ∧ FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧
  FullExtScratchOk c s ∧ s.core.dense_mode = 0#64
def FullConflictOkW (F_cur : List (List Nat)) (s : FullState) : Prop :=
  (s.core.confl_type = 1#64 ∧ s.core.confl_lit0.toNat < 2 * s.core.cur_vars ∧
    s.core.confl_lit1.toNat < 2 * s.core.cur_vars ∧
    s.core.vals[s.core.confl_lit0.toNat]?.getD 0#8 = 0xFF#8 ∧
    s.core.vals[s.core.confl_lit1.toNat]?.getD 0#8 = 0xFF#8 ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause [s.core.confl_lit0.toNat, s.core.confl_lit1.toNat])) ∨
  (s.core.confl_type ≠ 1#64 ∧ s.core.confl_ref.toNat ∈ fullArenaClauseRefs s ∧
    fullArenaClauseGarb s s.core.confl_ref.toNat = false ∧
    ∀ l ∈ fullArenaClauseLits s s.core.confl_ref.toNat, s.core.vals[l]?.getD 0#8 = 0xFF#8)
theorem level0_unsat_of_conflict_okW {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core) (hl0 : s.core.cur_level = 0)
    (hc : FullConflictOkW F_cur s) : F0.Unsat := by
  rcases hc with ⟨_, h0lt, h1lt, hf0, hf1, hent⟩ | ⟨_, href, hng, hfals⟩
  · refine hw.ext_sound.2 (unsat_of_entails_nil (entails_of_mem_or_false hent fun l hl => ?_))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl; right; rcases hl with rfl | rfl
    · obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff _ h0lt).mp hf0
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [heq] at hs
    · obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff _ h1lt).mp hf1
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [heq] at hs
  · refine hw.ext_sound.2
      (unsat_of_entails_nil (entails_of_mem_or_false (hw.arena.entails _ href hng) fun l hl => ?_))
    right; have hlt := hw.arena.lits_lt _ href hng l hl
    obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hlt).mp (hfals l hl)
    have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [heq] at hs
/-- Relaxed witness invariant matching `FullSpec1.FullOtfsWitnessInv` for `fullBacktrackSpec`. -/
structure FullOtfsWitnessInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (k : FullCoreState) : Prop where
  ext_sound : ExtUnsatSound F0 k.cur_vars F_cur
  inconsistent_sound : k.inconsistent ≠ 0#64 → (cnfOfClauses F_cur).Unsat
  arena : FullArenaClausesInv c F_cur k
  watches : ModeWatchesInv F_cur k
  cur_level_le : k.cur_level ≤ k.trail_end
  trail_lits_lt : ∀ i < k.trail_end, (k.trl[i]?.getD 0#32).toNat < 2 * k.cur_vars
  trail_vars_nodup : ∀ i j, i < k.trail_end → j < k.trail_end →
    (k.trl[i]?.getD 0#32).toNat / 2 = (k.trl[j]?.getD 0#32).toNat / 2 → i = j
  vals_domain : ∀ l < 2 * k.cur_vars,
    k.vals[l]?.getD 0#8 = 0#8 ∨ k.vals[l]?.getD 0#8 = 1#8 ∨ k.vals[l]?.getD 0#8 = 0xFF#8
  vals_true_iff : ∀ l < 2 * k.cur_vars,
    k.vals[l]?.getD 0#8 = 1#8 ↔ ∃ i < k.trail_end, (k.trl[i]?.getD 0#32).toNat = l
  vals_false_iff : ∀ l < 2 * k.cur_vars,
    k.vals[l]?.getD 0#8 = 0xFF#8 ↔ ∃ i < k.trail_end, (k.trl[i]?.getD 0#32).toNat = l ^^^ 1
  lvl_le : ∀ i < k.trail_end,
    (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ k.cur_level
  dec_earliest : ∀ i j, i < k.trail_end → j < k.trail_end →
    (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
      (k.lvl[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat →
    0 < (k.lvl[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ∧
    k.rsns[(k.trl[j]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 → j ≤ i
  levels_inhabited : ∀ L, 1 ≤ L → L ≤ k.cur_level →
    ∃ i < k.trail_end, (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = L
  level0_sound : ∀ i < k.trail_end,
    (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 →
    (cnfOfClauses F_cur).EntailsClause (cnfClause [(k.trl[i]?.getD 0#32).toNat])
  trail_pos_inv : ∀ i < k.trail_end,
    (k.trail_pos[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = i
  level0_rsn_none : ∀ idx < k.trail_end,
    (k.lvl[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 →
    k.rsns[(k.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32
  frame_trail_lt : ∀ L ≤ k.cur_level, (k.frame_trail[L]?.getD 0#32).toNat ≤ k.trail_end
  frame_trail_mono : ∀ L1 L2, L1 ≤ L2 → L2 ≤ k.cur_level →
    (k.frame_trail[L1]?.getD 0#32).toNat ≤ (k.frame_trail[L2]?.getD 0#32).toNat
  frame_trail_before_lt : ∀ L, 1 ≤ L → L ≤ k.cur_level →
    ∀ i < (k.frame_trail[L]?.getD 0#32).toNat,
      (k.lvl[(k.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat < L
  frame_dec_lt : ∀ L, 1 ≤ L → L ≤ k.cur_level → (k.frame_dec[L]?.getD 0#32).toNat < 2 * k.cur_vars
  reason_inv_below : ∀ idx < k.trail_end,
    let p := (k.trl[idx]?.getD 0#32).toNat
    let rsn := k.rsns[p / 2]?.getD 0xFFFFFFFF#32
    (k.lvl[p / 2]?.getD 0#32).toNat < k.cur_level → rsn ≠ 0xFFFFFFFF#32 →
    if (rsn &&& 0x80000000#32) ≠ 0#32 then
      let ot := (rsn &&& 0x7FFFFFFF#32).toNat
      ot < 2 * k.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [p, ot]) ∧
      ∃ m < idx, (k.trl[m]?.getD 0#32).toNat = ot ^^^ 1 ∧
        (k.lvl[ot / 2]?.getD 0#32).toNat ≤ (k.lvl[p / 2]?.getD 0#32).toNat
    else
      rsn.toNat ∈ fullArenaClauseRefsCore k ∧ fullArenaClauseGarbCore k rsn.toNat = false ∧
      ∀ q ∈ fullArenaClauseLitsCore k rsn.toNat,
        q = p ∨ ∃ m < idx, (k.trl[m]?.getD 0#32).toNat = q ^^^ 1 ∧
          (k.lvl[q / 2]?.getD 0#32).toNat ≤ (k.lvl[p / 2]?.getD 0#32).toNat
  reason_lit_mem_below : ∀ idx < k.trail_end,
    let p := (k.trl[idx]?.getD 0#32).toNat
    let rsn := k.rsns[p / 2]?.getD 0xFFFFFFFF#32
    (k.lvl[p / 2]?.getD 0#32).toNat < k.cur_level → rsn ≠ 0xFFFFFFFF#32 →
    (rsn &&& 0x80000000#32) = 0#32 → p ∈ fullArenaClauseLitsCore k rsn.toNat
/-! ### Callee `Spec` contracts (`5` callees matching `FullSpec{2,3}` 1:1) -/

def fullWstackDefragSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧ (FullMem c s ⋆ R) m ∧
    ∀ wvec' wstk' wlen' wsort' m',
      let s' : FullState :=
        { s with
          core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
          scratch := { s.scratch with wsort := wsort' } }
      s'.LengthsOk c → WatchStackLayout s'.core → (1 ≤ s.core.wlen → 1 ≤ wlen') →
      (∀ l < 2 * s.core.cur_vars, fullWatchSize s' l = fullWatchSize s l ∧
        ∀ k < fullWatchSize s l,
          s'.core.wstk[fullWatchOff s' l + k]? = s.core.wstk[fullWatchOff s l + k]?) →
      (FullMem c s' ⋆ R) m' → Q () m'
def fullBacktrackSpec : Spec [i64, i64] [] := fun (h, target_lvl, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧
    (target_lvl.toNat < s.core.cur_level → target_lvl.toNat < c.max_vars) ∧
    (∀ i < s.core.trail_end, (s.core.trl[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m',
      let s' : FullState :=
        { s with
          core :=
            { s.core with
              vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp'
              trail_end := te', propagated := prop', cur_level := cl', unassigned := unass' }
          scratch := sc' }
      s'.LengthsOk c → te' ≤ s.core.trail_end → prop' ≤ te' →
      cl' = min s.core.cur_level target_lvl.toNat → FullProbeScratchPres s s' →
      (∀ i < te', (trl'[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) →
      (∀ F0 F_cur, FullWitnessInv c F0 F_cur s.core → target_lvl.toNat ≤ s.core.cur_level →
        FullWitnessInv c F0 F_cur s'.core) →
      (∀ F0 F_cur, FullOtfsWitnessInv c F0 F_cur s.core → target_lvl.toNat < s.core.cur_level →
        FullWitnessInv c F0 F_cur s'.core) →
      (FullMem c s' ⋆ R) m' → Q () m'
def fullPropagateSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullArenaVarsNodup s ∧
    s.core.dense_mode = 0#64 ∧ (FullMem c s ⋆ R) m ∧
    ∀ r vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
      fuel' ctype' cref' c0' c1' oom' sc' m',
      let s' : FullState :=
        { s with
          core :=
            { s.core with
              vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl'
              trail_pos := tp', trail_end := te', propagated := prop', unassigned := unass'
              unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk', wlen := wlen'
              wusable := wu', fuel := fuel', confl_type := ctype', confl_ref := cref'
              confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
          scratch := sc' }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → FullArenaVarsNodup s' →
      FullProbeScratchPres s s' → s.core.trail_end ≤ te' → fuel'.toNat ≤ s.core.fuel.toNat →
      (∀ ref ∈ fullArenaClauseRefs s, ref ∈ fullArenaClauseRefs s') →
      (∀ i < s.core.trail_end, trl'[i]? = s.core.trl[i]?) → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → prop' = te' ∧ (s.core.oom = 0#64 → oom' = 0#64) ∧
        (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧ FullConflictOkW F_cur s') →
      (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
      (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s' = s) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'
def fullDeleteBinSideSpec : Spec [i64, i32, i32] [] := fun (h, lit, _other, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧
    (lit.toNat < 2 * s.core.cur_vars →
      fullWatchOff s lit.toNat + fullWatchSize s lit.toNat ≤ s.core.wlen) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ wvec' wstk' wu' m',
      let s' : FullState :=
        { s with core := { s.core with wvec := wvec', wstk := wstk', wusable := wu' } }
      s'.LengthsOk c →
      (lit.toNat < 2 * s.core.cur_vars →
        fullWatchOff s' lit.toNat = fullWatchOff s lit.toNat ∧
        fullWatchSize s' lit.toNat ≤ fullWatchSize s lit.toNat) →
      (∀ l < 2 * s.core.cur_vars, l ≠ lit.toNat →
        fullWatchOff s' l = fullWatchOff s l ∧ fullWatchSize s' l = fullWatchSize s l) →
      (∀ idx < c.wcap, (lit.toNat < 2 * s.core.cur_vars → idx < fullWatchOff s lit.toNat ∨
          fullWatchOff s lit.toNat + fullWatchSize s lit.toNat ≤ idx) →
        wstk'[idx]? = s.core.wstk[idx]?) →
      (∀ F_cur, WatchSliceOk F_cur s.core lit.toNat (fullWatchOff s lit.toNat)
          (fullWatchSize s lit.toNat) → WatchSliceOk F_cur s'.core lit.toNat
          (fullWatchOff s' lit.toNat) (fullWatchSize s' lit.toNat)) →
      (∀ F_cur, DenseWatchSliceOk F_cur s.core lit.toNat (fullWatchOff s lit.toNat)
          (fullWatchSize s lit.toNat) → DenseWatchSliceOk F_cur s'.core lit.toNat
          (fullWatchOff s' lit.toNat) (fullWatchSize s' lit.toNat)) →
      (WatchStackLayout s.core → WatchStackLayout s'.core) →
      (∀ F_cur, ModeWatchesInv F_cur s.core → ModeWatchesInv F_cur s'.core) →
      (FullMem c s' ⋆ R) m' → Q () m'
def fullAddUnitSpec : Spec [i64, i32] [.bool] := fun (h, lit, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    (lit.toNat < 2 * s.core.cur_vars → (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat])) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc' sc' m',
      let s' : FullState :=
        { s with
          core :=
            { s.core with
              vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl'
              trail_pos := tp', trail_end := te', propagated := prop', cur_level := cl'
              unassigned := unass', unflushed := unfl', inconsistent := inc' }
          scratch := sc' }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → FullProbeScratchPres s s' → cl' = 0 →
      (lit.toNat < 2 * s.core.cur_vars → ok = false → F0.Unsat ∧ inc' ≠ 0#64) →
      (ok = false → 2 * s.core.cur_vars ≤ lit.toNat ∨ (F0.Unsat ∧ inc' ≠ 0#64)) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'
def fullTransLitSpec : Spec [i64, i32] [.bool] := fun (h, src, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ s.core.cur_level = 0 ∧
    src.toNat < 2 * s.core.cur_vars ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) s' m', FullSparseInv c F0 s' → s'.core.cur_level = 0 →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      (ok = false → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (ok, ()) m'
def fullTransitiveSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m', FullSparseInv c F0 s' → s'.core.cur_level = 0 → s'.core.probing = 0#64 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → (r = 1#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (r, ()) m'
end FullTransSpecs
open FullTransSpecs
/-! ## 3. Watch-slice and tombstone lemmas -/
section WatchAndTombLemmas
theorem watchSlice_inv_bin {F_cur : List (List Nat)} {k : FullCoreState} {lit p len : Nat}
    {w0 : BitVec 32} (h : WatchSliceOk F_cur k lit p len) (hlen : 0 < len)
    (hget : k.wstk[p]? = some w0) (hflag : (w0 &&& 0x80000000#32) ≠ 0#32) :
    w0 ≠ 0xFFFFFFFF#32 ∧ (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
    WatchSliceOk F_cur k lit (p + 1) (len - 1) := by
  cases h with
  | empty => omega
  | bin h0 _ hne hlt hent hrest =>
    have hw := Option.some.inj (h0.symm.trans hget); subst hw
    exact ⟨hne, hlt, hent, by simpa using hrest⟩
  | large h0 _ hf _ _ _ =>
    have hw := Option.some.inj (h0.symm.trans hget); subst hw; exact absurd hf hflag
theorem watchSlice_inv_large {F_cur : List (List Nat)} {k : FullCoreState} {lit p len : Nat}
    {w0 : BitVec 32} (h : WatchSliceOk F_cur k lit p len) (hlen : 0 < len)
    (hget : k.wstk[p]? = some w0) (hflag : (w0 &&& 0x80000000#32) = 0#32) :
    2 ≤ len ∧ ∃ cref : BitVec 32, k.wstk[p + 1]? = some cref ∧
      cref.toNat < 0x80000000 ∧ cref.toNat ∈ fullArenaClauseRefsCore k ∧
      WatchSliceOk F_cur k lit (p + 2) (len - 2) := by
  cases h with
  | empty => omega
  | bin h0 hf _ _ _ =>
    have hw := Option.some.inj (h0.symm.trans hget); subst hw; exact absurd hflag hf
  | large h0 h1 _ hlt href hrest => exact ⟨by omega, _, h1, hlt, href, by simpa using hrest⟩
theorem watchSlice_append {F_cur : List (List Nat)} {k : FullCoreState} {lit p len1 len2 : Nat}
    (h1 : WatchSliceOk F_cur k lit p len1) (h2 : WatchSliceOk F_cur k lit (p + len1) len2) :
    WatchSliceOk F_cur k lit p (len1 + len2) := by
  induction h1 with
  | empty => simpa using h2
  | @bin p rem w0 h0 hf hn hl he _ ih =>
    rw [show p + (rem + 1) = (p + 1) + rem by omega] at h2
    rw [show rem + 1 + len2 = (rem + len2) + 1 by omega]; exact .bin h0 hf hn hl he (ih h2)
  | @large p rem w0 cr h0 h1 hf hl hr _ ih =>
    rw [show p + (rem + 2) = (p + 2) + rem by omega] at h2
    rw [show rem + 2 + len2 = (rem + len2) + 2 by omega]; exact .large h0 h1 hf hl hr (ih h2)
/-- Watch slice permitting `nt` tombstones (`0xFFFFFFFF#32`) interspersed among valid entries. -/
inductive TombWatchSliceOk (F_cur : List (List Nat)) (k : FullCoreState) (lit : Nat) :
    Nat → Nat → Nat → Prop where
  | empty {p} : TombWatchSliceOk F_cur k lit p 0 0
  | tomb {p rem nt} : k.wstk[p]? = some 0xFFFFFFFF#32 →
      TombWatchSliceOk F_cur k lit (p + 1) rem nt →
      TombWatchSliceOk F_cur k lit p (rem + 1) (nt + 1)
  | bin {p rem nt w0} : k.wstk[p]? = some w0 → (w0 &&& 0x80000000#32) ≠ 0#32 →
      w0 ≠ 0xFFFFFFFF#32 → (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) →
      TombWatchSliceOk F_cur k lit (p + 1) rem nt → TombWatchSliceOk F_cur k lit p (rem + 1) nt
  | large {p rem nt w0 cref} : k.wstk[p]? = some w0 → k.wstk[p + 1]? = some cref →
      (w0 &&& 0x80000000#32) = 0#32 → cref.toNat < 0x80000000 →
      cref.toNat ∈ fullArenaClauseRefsCore k →
      TombWatchSliceOk F_cur k lit (p + 2) rem nt → TombWatchSliceOk F_cur k lit p (rem + 2) nt
theorem TombWatchSliceOk.of_watchSlice {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} (h : WatchSliceOk F_cur k lit p rem) :
    TombWatchSliceOk F_cur k lit p rem 0 := by
  induction h with
  | empty => exact .empty | bin a b c d e _ ih => exact .bin a b c d e ih
  | large a b c d e _ ih => exact .large a b c d e ih
theorem TombWatchSliceOk.to_watchSlice {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem : Nat} (h : TombWatchSliceOk F_cur k lit p rem 0) :
    WatchSliceOk F_cur k lit p rem := by
  generalize hnt : (0 : Nat) = nt at h
  induction h with
  | empty => exact .empty | tomb _ _ => omega
  | bin a b c d e _ ih => exact .bin a b c d e (ih hnt)
  | large a b c d e _ ih => exact .large a b c d e (ih hnt)
theorem TombWatchSliceOk.mono {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p rem nt : Nat} (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx, p ≤ idx → idx < p + rem → k'.wstk[idx]? = k.wstk[idx]?)
    (h : TombWatchSliceOk F_cur k lit p rem nt) : TombWatchSliceOk F_cur k' lit p rem nt := by
  induction h with
  | empty => exact .empty
  | @tomb p rem nt hp _ ih =>
    exact .tomb (by rw [hwstk p (by omega) (by omega), hp])
      (ih fun _ _ _ => hwstk _ (by omega) (by omega))
  | @bin p rem nt w0 hp hf hn hl he _ ih =>
    exact .bin (by rw [hwstk p (by omega) (by omega), hp]) hf hn (by omega) he
      (ih fun _ _ _ => hwstk _ (by omega) (by omega))
  | @large p rem nt w0 cref hp hp1 hf hl hr _ ih =>
    exact .large (by rw [hwstk p (by omega) (by omega), hp])
      (by rw [hwstk (p + 1) (by omega) (by omega), hp1]) hf hl (hsub _ hr)
      (ih fun _ _ _ => hwstk _ (by omega) (by omega))
theorem TombWatchSliceOk.append {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p len1 len2 nt1 nt2 : Nat} (h1 : TombWatchSliceOk F_cur k lit p len1 nt1)
    (h2 : TombWatchSliceOk F_cur k lit (p + len1) len2 nt2) :
    TombWatchSliceOk F_cur k lit p (len1 + len2) (nt1 + nt2) := by
  induction h1 with
  | empty => simpa using h2
  | @tomb p rem nt hp _ ih =>
    rw [show p + (rem + 1) = (p + 1) + rem by omega] at h2
    rw [show rem + 1 + len2 = (rem + len2) + 1 by omega]
    rw [show nt + 1 + nt2 = (nt + nt2) + 1 by omega]; exact .tomb hp (ih h2)
  | @bin p rem nt w0 hp hf hn hl he _ ih =>
    rw [show p + (rem + 1) = (p + 1) + rem by omega] at h2
    rw [show rem + 1 + len2 = (rem + len2) + 1 by omega]; exact .bin hp hf hn hl he (ih h2)
  | @large p rem nt w0 cr hp hp1 hf hl hr _ ih =>
    rw [show p + (rem + 2) = (p + 2) + rem by omega] at h2
    rw [show rem + 2 + len2 = (rem + len2) + 2 by omega]; exact .large hp hp1 hf hl hr (ih h2)
theorem TombWatchSliceOk.nt_le_rem {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p rem nt : Nat} (h : TombWatchSliceOk F_cur k lit p rem nt) : nt ≤ rem := by
  induction h <;> omega
theorem TombWatchSliceOk.eq_zero_of_rem0 {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p nt : Nat} (h : TombWatchSliceOk F_cur k lit p 0 nt) : nt = 0 := by
  have := h.nt_le_rem; omega
theorem TombWatchSliceOk.inv_step {F_cur : List (List Nat)} {k : FullCoreState}
    {lit p len nt : Nat} {w0 : BitVec 32} (h : TombWatchSliceOk F_cur k lit p len nt)
    (hlen : 0 < len) (hget : k.wstk[p]? = some w0) :
    if (w0 &&& 0x80000000#32) = 0#32 then
      2 ≤ len ∧ ∃ cref : BitVec 32, k.wstk[p + 1]? = some cref ∧
        cref.toNat < 0x80000000 ∧ cref.toNat ∈ fullArenaClauseRefsCore k ∧
        TombWatchSliceOk F_cur k lit (p + 2) (len - 2) nt
    else if w0 = 0xFFFFFFFF#32 then
      1 ≤ nt ∧ TombWatchSliceOk F_cur k lit (p + 1) (len - 1) (nt - 1)
    else (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
      TombWatchSliceOk F_cur k lit (p + 1) (len - 1) nt := by
  cases h with
  | empty => omega
  | tomb hp hrest =>
    have hw := Option.some.inj (hp.symm.trans hget); subst hw
    simp only [ft_tomb_bin_flag, ↓reduceIte]; exact ⟨by omega, by simpa using hrest⟩
  | bin hp hf hn hl he hrest =>
    have hw := Option.some.inj (hp.symm.trans hget); subst hw
    simp only [hf, ↓reduceIte, hn]; exact ⟨hl, he, by simpa using hrest⟩
  | large hp hp1 hf hl hr hrest =>
    have hw := Option.some.inj (hp.symm.trans hget); subst hw
    simp only [hf, ↓reduceIte]; exact ⟨by omega, _, hp1, hl, hr, by simpa using hrest⟩
theorem WatchSliceOk.relocate_same {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : WatchSliceOk F_cur k lit p rem) : WatchSliceOk F_cur k' lit p' rem := by
  induction h generalizing p' with
  | empty => exact .empty
  | @bin p rem w0 hp hf hn hl he _ ih =>
    exact .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hn (by omega) he
      (ih (p' := p' + 1) fun idx hi => by simpa [Nat.add_assoc] using hwstk (1 + idx) (by omega))
  | @large p rem w0 cr hp hp1 hf hl hr _ ih =>
    exact .large (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hf hl (hsub _ hr)
      (ih (p' := p' + 2) fun idx hi => by simpa [Nat.add_assoc] using hwstk (2 + idx) (by omega))
theorem DenseWatchSliceOk.relocate_same {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : DenseWatchSliceOk F_cur k lit p rem) : DenseWatchSliceOk F_cur k' lit p' rem := by
  induction h generalizing p' with
  | empty => exact .empty
  | @bin p rem w0 hp hf hn hl he _ ih =>
    exact .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hn (by omega) he
      (ih (p' := p' + 1) fun idx hi => by simpa [Nat.add_assoc] using hwstk (1 + idx) (by omega))
  | @occ p rem w0 cr hp hp1 hf hs1 hl hr _ ih =>
    exact .occ (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hf hs1 hl (hsub _ hr)
      (ih (p' := p' + 2) fun idx hi => by simpa [Nat.add_assoc] using hwstk (2 + idx) (by omega))
theorem fullWstackDefrag_preserves_modeWatchesInv {F_cur : List (List Nat)}
    {k k' : FullCoreState} (hw : ModeWatchesInv F_cur k) (hlay : WatchStackLayout k')
    (hvars : k'.cur_vars = k.cur_vars) (hdm : k'.dense_mode = k.dense_mode)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hpres : ∀ l < 2 * k.cur_vars, fullWatchSizeCore k' l = fullWatchSizeCore k l ∧
      ∀ idx < fullWatchSizeCore k l,
        k'.wstk[fullWatchOffCore k' l + idx]? = k.wstk[fullWatchOffCore k l + idx]?) :
    ModeWatchesInv F_cur k' := by
  unfold ModeWatchesInv at hw ⊢; rw [hdm]
  by_cases hc : k.dense_mode = 0#64 <;> simp only [hc, ↓reduceIte] at hw ⊢ <;>
    exact ⟨hlay, fun l hl => by
      obtain ⟨hsz, hslice⟩ := hpres l (hvars ▸ hl); rw [hsz]
      exact (hw.slices l (hvars ▸ hl)).relocate_same (by omega) hsub hslice⟩
end WatchAndTombLemmas
/-! ## 4. Outer-loop and compaction invariants for `full_trans_lit` -/
section TransLitInvariants
/-- Shared outer state & disjointness invariant of `full_trans_lit` across scan and compaction. -/
structure TransOuterBase (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 : FullState) (src off end_v : Nat) (st : FullState) : Prop where
  len_ok : st.LengthsOk c
  core_pres : st.core.cur_vars = s0.core.cur_vars ∧ st.core.cur_level = 0 ∧
    s0.core.cur_level = 0 ∧ st.core.fuel = s0.core.fuel ∧ st.core.dense_mode = 0#64 ∧
    st.core.probing = s0.core.probing ∧ st.core.oom = s0.core.oom ∧
    st.core.inconsistent = s0.core.inconsistent ∧ st.core.arena = s0.core.arena ∧
    st.core.arena_len = s0.core.arena_len ∧ st.core.vals = s0.core.vals ∧
    st.core.lvl = s0.core.lvl ∧ st.core.rsns = s0.core.rsns ∧
    st.core.trail_pos = s0.core.trail_pos ∧ st.core.trail_end = s0.core.trail_end ∧
    (∀ i < s0.core.trail_end, st.core.trl[i]? = s0.core.trl[i]?) ∧ st.core.mrk = s0.core.mrk ∧
    st.core.lit_mark = s0.core.lit_mark ∧ st.core.flags = s0.core.flags ∧
    st.core.frame_trail = s0.core.frame_trail ∧ st.core.frame_dec = s0.core.frame_dec ∧
    st.core.wlen = s0.core.wlen
  scratch_pres : st.scratch.last_learned = s0.scratch.last_learned ∧
    st.scratch.extend_len = s0.scratch.extend_len
  off_le_end : off ≤ end_v
  src_off : fullWatchOffCore st.core src = off
  src_sz : fullWatchSizeCore st.core src = end_v - off
  end_le_wlen : end_v ≤ st.core.wlen
  off_pos : 1 ≤ off
  other_bounds : ∀ l < 2 * st.core.cur_vars, l ≠ src →
    fullWatchOffCore st.core l + fullWatchSizeCore st.core l ≤ st.core.wlen
  other_pos_off : ∀ l < 2 * st.core.cur_vars, l ≠ src →
    0 < fullWatchSizeCore st.core l → 1 ≤ fullWatchOffCore st.core l
  disjoint_all : ∀ l1 l2, l1 < 2 * st.core.cur_vars → l2 < 2 * st.core.cur_vars → l1 ≠ l2 →
    0 < fullWatchSizeCore st.core l1 → 0 < fullWatchSizeCore st.core l2 →
    fullWatchOffCore st.core l1 + fullWatchSizeCore st.core l1 ≤ fullWatchOffCore st.core l2 ∨
    fullWatchOffCore st.core l2 + fullWatchSizeCore st.core l2 ≤ fullWatchOffCore st.core l1
  other_no_sent : ∀ l < 2 * st.core.cur_vars, l ≠ src → ∀ idx < fullWatchSizeCore st.core l,
    st.core.wstk[fullWatchOffCore st.core l + idx]? ≠ some 0xFFFFFFFF#32
  other_slices : ∀ l < 2 * st.core.cur_vars, l ≠ src →
    WatchSliceOk F_cur st.core l (fullWatchOffCore st.core l) (fullWatchSizeCore st.core l)
structure TransOuterInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 : FullState) (src off p end_v reduced : Nat) (st : FullState) : Prop where
  base : TransOuterBase c F0 F_cur s0 src off end_v st
  off_le_p : off ≤ p
  p_le_end : p ≤ end_v
  red_le : reduced ≤ p - off
  src_pref : TombWatchSliceOk F_cur st.core src off (p - off) reduced
  src_rem : WatchSliceOk F_cur st.core src p (end_v - p)
theorem TransOuterBase.frame_wstk {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off end_v : Nat} {st : FullState}
    (hb : TransOuterBase c F0 F_cur s0 src off end_v st) (hsrc_lt : src < 2 * st.core.cur_vars)
    {wstk' : List (BitVec 32)} {wu' tc' : BitVec 64} (hlen : wstk'.length = c.wcap)
    (hout : ∀ idx, (idx < off ∨ end_v ≤ idx) → wstk'[idx]? = st.core.wstk[idx]?) :
    TransOuterBase c F0 F_cur s0 src off end_v
      { st with core := { st.core with wstk := wstk', wusable := wu' }
                scratch := { st.scratch with trans_cnt := tc' } } := by
  have hdisj : ∀ l < 2 * st.core.cur_vars, l ≠ src → ∀ idx < fullWatchSizeCore st.core l,
      fullWatchOffCore st.core l + idx < off ∨ end_v ≤ fullWatchOffCore st.core l + idx := by
    intro l hl hls idx hidx; by_cases hoff_eq : off = end_v
    · subst hoff_eq; exact Nat.lt_or_ge _ _
    · have := hb.off_le_end
      rcases hb.disjoint_all src l hsrc_lt hl hls.symm (by rw [hb.src_sz]; omega) (by omega) with
        ha | hb2
      · rw [hb.src_off, hb.src_sz] at ha; right; omega
      · rw [hb.src_off] at hb2; left; omega
  exact { hb with
    len_ok := ⟨{ hb.len_ok.core_ok with wstk_len_arr := hlen },
      { hb.len_ok.scratch_ok with walk_vals_len := hb.len_ok.scratch_ok.walk_vals_len }⟩
    other_no_sent := fun l hl hls idx _ => by
      change wstk'[fullWatchOffCore st.core l + idx]? ≠ some 0xFFFFFFFF#32
      rw [hout _ (hdisj l hl hls idx ‹_›)]; exact hb.other_no_sent l hl hls idx ‹_›
    other_slices := fun l hl hls => WatchSliceOk.relocate_same (k := st.core)
      (k' := { st.core with wstk := wstk', wusable := wu' }) (Nat.le_refl _) (fun _ hr => hr)
      (fun idx hi => hout _ (hdisj l hl hls idx hi)) (hb.other_slices l hl hls) }
theorem TransOuterInv.src_full_tomb {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off p end_v reduced : Nat} {st : FullState}
    (h : TransOuterInv c F0 F_cur s0 src off p end_v reduced st) :
    TombWatchSliceOk F_cur st.core src off (end_v - off) reduced := by
  have h1 : off + (p - off) = p := by have := h.off_le_p; omega
  have h2 : p - off + (end_v - p) = end_v - off := by have := h.off_le_p; have := h.p_le_end; omega
  have hcomb := h.src_pref.append (by rw [h1]; exact TombWatchSliceOk.of_watchSlice h.src_rem)
  rwa [h2, Nat.add_zero] at hcomb
theorem TransOuterInv.init {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} (hlen : s0.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s0.core)
    (hdm : s0.core.dense_mode = 0#64) (hcl : s0.core.cur_level = 0)
    {src : Nat} (hsrc : src < 2 * s0.core.cur_vars) (hpos : 0 < fullWatchSizeCore s0.core src) :
    let off := fullWatchOffCore s0.core src
    TransOuterInv c F0 F_cur s0 src off off (off + fullWatchSizeCore s0.core src) 0 s0 := by
  have hwm : WatchesInv F_cur s0.core := by
    have hm := hw.watches; unfold ModeWatchesInv at hm; simp only [hdm, ↓reduceIte] at hm; exact hm
  exact {
    base :=
      { len_ok := hlen, scratch_pres := ⟨rfl, rfl⟩, off_le_end := by omega
        core_pres := ⟨rfl, hcl, hcl, rfl, hdm, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
          fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        src_off := rfl, src_sz := by omega, end_le_wlen := hwm.layout.bounds src hsrc
        off_pos := hwm.layout.pos_off src hsrc hpos
        other_bounds := fun l hl _ => hwm.layout.bounds l hl
        other_pos_off := fun l hl _ hp => hwm.layout.pos_off l hl hp
        disjoint_all := hwm.layout.disjoint
        other_no_sent := fun l hl _ => hwm.layout.no_sentinel l hl
        other_slices := fun l hl _ => hwm.slices l hl }
    off_le_p := Nat.le_refl _, p_le_end := by omega, red_le := by simp
    src_pref := by simp only [Nat.sub_self]; exact .empty
    src_rem := by simpa only [Nat.add_sub_cancel_left] using hwm.slices src hsrc }
theorem TransOuterBase.toWitness_of_src_clean {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s0 : FullState} {src off end_v : Nat} {st : FullState}
    (hw0 : FullWitnessInv c F0 F_cur s0.core) (hb : TransOuterBase c F0 F_cur s0 src off end_v st)
    (hclean : WatchSliceOk F_cur st.core src
      (fullWatchOffCore st.core src) (fullWatchSizeCore st.core src)) :
    FullWitnessInv c F0 F_cur st.core := by
  obtain ⟨hcv, hcl0, hs0cl0, _, hdm, _, _, hinc, har, hal, hvals, hlvl, hrsn, htp, hte, htrl, _, _,
    _, hft, hfd, _⟩ := hb.core_pres
  have hrefs : fullArenaClauseRefsCore st.core = fullArenaClauseRefsCore s0.core := by
    unfold fullArenaClauseRefsCore; rw [har, hal]
  have hgarb : ∀ r, fullArenaClauseGarbCore st.core r = fullArenaClauseGarbCore s0.core r :=
    fun r => by unfold fullArenaClauseGarbCore fullArenaHdrCore; rw [har]
  have hlits : ∀ r, fullArenaClauseLitsCore st.core r = fullArenaClauseLitsCore s0.core r :=
    fun r => by unfold fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [har]
  have hsz_core : ∀ r, fullArenaClauseSizeCore st.core r = fullArenaClauseSizeCore s0.core r :=
    fun r => by unfold fullArenaClauseSizeCore; rw [har]
  have hlay : WatchStackLayout st.core :=
    { bounds := fun l hl => by
        by_cases hls : l = src
        · subst hls; have := hb.off_le_end; rw [hb.src_off, hb.src_sz]
          exact Nat.le_trans (by omega) hb.end_le_wlen
        · exact hb.other_bounds l hl hls
      pos_off := fun l hl hp =>
        if hls : l = src then by subst hls; rw [hb.src_off]; exact hb.off_pos
        else hb.other_pos_off l hl hls hp
      disjoint := hb.disjoint_all
      no_sentinel := fun l hl =>
        if hls : l = src then hls ▸ hclean.ne_sentinel else hb.other_no_sent l hl hls }
  have hwat : ModeWatchesInv F_cur st.core := by
    unfold ModeWatchesInv; simp only [hdm, ↓reduceIte]
    exact ⟨hlay, fun l hl => if hls : l = src then hls ▸ hclean else hb.other_slices l hl hls⟩
  have htrl_d : ∀ i < st.core.trail_end,
      (st.core.trl[i]?.getD 0#32).toNat = (s0.core.trl[i]?.getD 0#32).toNat :=
    fun i hi => by rw [htrl i (hte ▸ hi)]
  have hvals_d : ∀ l : Nat, st.core.vals[l]?.getD 0#8 = s0.core.vals[l]?.getD 0#8 :=
    fun l => by rw [hvals]
  have hlvl_d : ∀ v : Nat, (st.core.lvl[v]?.getD 0#32).toNat = (s0.core.lvl[v]?.getD 0#32).toNat :=
    fun v => by rw [hlvl]
  have hrsn_d : ∀ v : Nat, st.core.rsns[v]?.getD 0xFFFFFFFF#32 =
      s0.core.rsns[v]?.getD 0xFFFFFFFF#32 := fun v => by rw [hrsn]
  refine
    { ext_sound := hcv ▸ hw0.ext_sound, watches := hwat
      inconsistent_sound := fun hi => hw0.inconsistent_sound (hinc ▸ hi)
      arena :=
        { len_ok := hal ▸ hw0.arena.len_ok
          refs_wf := fun r hr => by
            rw [hrefs] at hr; rw [hal, har, hsz_core r]; exact hw0.arena.refs_wf r hr
          shrk_term := fun r hr hsh => by
            rw [hrefs] at hr; obtain ⟨t, ht1, ht2, hsent⟩ := hw0.arena.shrk_term r hr
              (by unfold fullArenaHdrCore at hsh ⊢; rwa [har] at hsh)
            exact ⟨t, by rw [hsz_core r]; exact ht1, by rw [hal]; exact ht2,
              by rw [har]; exact hsent⟩
          lits_lt := fun r hr hg l hl => by
            rw [hrefs] at hr; rw [hgarb r] at hg; rw [hlits r] at hl
            exact hcv ▸ hw0.arena.lits_lt r hr hg l hl
          entails := fun r hr hg => by
            rw [hrefs] at hr; rw [hgarb r] at hg; rw [hlits r]; exact hw0.arena.entails r hr hg }
      cur_level_le := by rw [hcl0]; exact Nat.zero_le _
      trail_lits_lt := fun i hi => by rw [hcv, htrl_d i hi]; exact hw0.trail_lits_lt i (hte ▸ hi)
      trail_vars_nodup := fun i j hi hj he => by
        rw [htrl_d i hi, htrl_d j hj] at he
        exact hw0.trail_vars_nodup i j (hte ▸ hi) (hte ▸ hj) he
      vals_domain := fun l hl => by rw [hvals_d l]; exact hw0.vals_domain l (hcv ▸ hl)
      vals_true_iff := fun l hl => by
        rw [hvals_d l, hte]; constructor
        · rintro h1; obtain ⟨i, hi, he⟩ := (hw0.vals_true_iff l (hcv ▸ hl)).mp h1
          exact ⟨i, hi, by rw [htrl_d i (hte ▸ hi), he]⟩
        · rintro ⟨i, hi, he⟩; rw [htrl_d i (hte ▸ hi)] at he
          exact (hw0.vals_true_iff l (hcv ▸ hl)).mpr ⟨i, hi, he⟩
      vals_false_iff := fun l hl => by
        rw [hvals_d l, hte]; constructor
        · rintro h1; obtain ⟨i, hi, he⟩ := (hw0.vals_false_iff l (hcv ▸ hl)).mp h1
          exact ⟨i, hi, by rw [htrl_d i (hte ▸ hi), he]⟩
        · rintro ⟨i, hi, he⟩; rw [htrl_d i (hte ▸ hi)] at he
          exact (hw0.vals_false_iff l (hcv ▸ hl)).mpr ⟨i, hi, he⟩
      lvl_le := fun i hi => by
        rw [hcl0, htrl_d i hi, hlvl_d]; have := hw0.lvl_le i (hte ▸ hi); omega
      dec_earliest := fun i j hi hj hleq hdec => by
        rw [htrl_d i hi, htrl_d j hj, hlvl_d, hlvl_d] at hleq
        rw [htrl_d j hj, hlvl_d, hrsn_d] at hdec
        exact hw0.dec_earliest i j (hte ▸ hi) (hte ▸ hj) hleq hdec
      levels_inhabited := fun L h1 h2 => by omega
      level0_sound := fun i hi hl0 => by
        rw [htrl_d i hi, hlvl_d] at hl0; rw [htrl_d i hi]; exact hw0.level0_sound i (hte ▸ hi) hl0
      trail_pos_inv := fun i hi => by rw [htp, htrl_d i hi]; exact hw0.trail_pos_inv i (hte ▸ hi)
      level0_rsn_none := fun idx hidx hl0 => by
        rw [htrl_d idx hidx, hlvl_d] at hl0; rw [htrl_d idx hidx, hrsn_d]
        exact hw0.level0_rsn_none idx (hte ▸ hidx) hl0
      frame_trail_lt := fun L hL => by
        rw [hcl0] at hL; rw [hft, hte]; exact hw0.frame_trail_lt L (by omega)
      frame_trail_mono := fun L1 L2 h1 h2 => by
        rw [hcl0] at h2; rw [hft]; exact hw0.frame_trail_mono L1 L2 h1 (by omega)
      frame_trail_before_lt := fun L h1 h2 => by rw [hcl0] at h2; omega
      frame_dec_lt := fun L h1 h2 => by rw [hcl0] at h2; omega
      reason_inv := fun idx hidx hne => by
        rw [htrl_d idx hidx, hrsn_d] at hne ⊢
        have hl0 : (s0.core.lvl[(s0.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 :=
          by have := hw0.lvl_le idx (hte ▸ hidx); omega
        exact absurd (hw0.level0_rsn_none idx (hte ▸ hidx) hl0) hne
      reason_lit_mem := fun idx hidx hne _ => by
        rw [htrl_d idx hidx, hrsn_d] at hne
        have hl0 : (s0.core.lvl[(s0.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 :=
          by have := hw0.lvl_le idx (hte ▸ hidx); omega
        exact absurd (hw0.level0_rsn_none idx (hte ▸ hidx) hl0) hne }
theorem TransOuterBase.toSparse {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off end_v : Nat} {st : FullState}
    (hsp0 : FullSparseInv c F0 s0) (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (hb : TransOuterBase c F0 F_cur s0 src off end_v st)
    (hclean : WatchSliceOk F_cur st.core src
      (fullWatchOffCore st.core src) (fullWatchSizeCore st.core src)) : FullSparseInv c F0 st := by
  have hw' := hb.toWitness_of_src_clean hw0 hclean
  obtain ⟨_, _, _, _, hdm, _, _, _, har, hal, _, _, _, _, _, _, hmrk, hlm, _, _, _, _⟩ :=
    hb.core_pres
  obtain ⟨hll, hel⟩ := hb.scratch_pres
  refine ⟨⟨hb.len_ok, F_cur, hw'⟩, ⟨fun v hv => hmrk ▸ hsp0.2.1.1 v hv,
    fun l hl => hlm ▸ hsp0.2.1.2 l hl⟩, ?_, ⟨?_, hel ▸ hsp0.2.2.2.1.2⟩, hdm⟩
  · intro r hr hng
    unfold fullArenaClauseRefs fullArenaClauseRefsCore at hr
    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hng
    unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore
    rw [har, hal] at hr; rw [har] at hng ⊢; exact hsp0.2.2.1 r hr hng
  · intro i hi; dsimp only; unfold fullArenaClauseRefs fullArenaClauseRefsCore
    rw [hll, har, hal]; exact hsp0.2.2.2.1.1 i hi
theorem TransOuterInv.of_delete_bin_side {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off p end_v reduced dst : Nat} {st st' : FullState}
    (h : TransOuterInv c F0 F_cur s0 src off p end_v reduced st)
    (hsrc_lt : src < 2 * st.core.cur_vars) (hdst_lt : dst < 2 * st.core.cur_vars)
    (hdst_ne : dst ≠ src) (hst'_eq : st' = { st with core :=
      { st.core with wvec := st'.core.wvec, wstk := st'.core.wstk, wusable := st'.core.wusable } })
    (hlen' : st'.LengthsOk c) (hdst_ws : fullWatchOff st' dst = fullWatchOff st dst ∧
      fullWatchSize st' dst ≤ fullWatchSize st dst)
    (hother_ws : ∀ l < 2 * st.core.cur_vars, l ≠ dst →
      fullWatchOff st' l = fullWatchOff st l ∧ fullWatchSize st' l = fullWatchSize st l)
    (hwstk_out : ∀ idx < c.wcap,
      (idx < fullWatchOff st dst ∨ fullWatchOff st dst + fullWatchSize st dst ≤ idx) →
      st'.core.wstk[idx]? = st.core.wstk[idx]?)
    (hdst_slice : WatchSliceOk F_cur st.core dst (fullWatchOff st dst) (fullWatchSize st dst) →
      WatchSliceOk F_cur st'.core dst (fullWatchOff st' dst) (fullWatchSize st' dst)) :
    TransOuterInv c F0 F_cur s0 src off p end_v reduced st' := by
  dsimp only [fullWatchOff, fullWatchSize] at hdst_ws hother_ws hwstk_out hdst_slice
  have hb := h.base; have hcp := hb.core_pres
  have har' : st'.core.arena = st.core.arena := by rw [hst'_eq]
  have hal' : st'.core.arena_len = st.core.arena_len := by rw [hst'_eq]
  have hcv' : st'.core.cur_vars = st.core.cur_vars := by rw [hst'_eq]
  have hwlen' : st'.core.wlen = st.core.wlen := by rw [hst'_eq]
  have hrefs : ∀ r ∈ fullArenaClauseRefsCore st.core, r ∈ fullArenaClauseRefsCore st'.core :=
    fun r hr => by unfold fullArenaClauseRefsCore at hr ⊢; rwa [har', hal']
  have hws : ∀ l < 2 * st.core.cur_vars, fullWatchOffCore st'.core l = fullWatchOffCore st.core l ∧
      fullWatchSizeCore st'.core l ≤ fullWatchSizeCore st.core l := fun l hl => by
    by_cases hld : l = dst; · exact hld ▸ hdst_ws
    · exact ⟨(hother_ws l hl hld).1, by rw [(hother_ws l hl hld).2]; exact Nat.le_refl _⟩
  have hout_range : ∀ a b, b ≤ st.core.wlen → (fullWatchSizeCore st.core dst = 0 ∨
      b ≤ fullWatchOffCore st.core dst ∨
      fullWatchOffCore st.core dst + fullWatchSizeCore st.core dst ≤ a) →
      ∀ idx, a ≤ idx → idx < b → st'.core.wstk[idx]? = st.core.wstk[idx]? := by
    intro a b hb2 hdis idx ha1 ha2; have hcap := hb.len_ok.core_ok.wlen_le
    apply hwstk_out idx (by omega)
    rcases hdis with h0 | hlt | hgt
    · rw [h0]; rcases Nat.lt_or_ge idx (fullWatchOffCore st.core dst) with hlt | hge
      · exact Or.inl hlt
      · exact Or.inr (by omega)
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have hsrc_ws := hother_ws src hsrc_lt hdst_ne.symm
  have hsrc_wstk : ∀ idx, off ≤ idx → idx < end_v → st'.core.wstk[idx]? = st.core.wstk[idx]? := by
    by_cases hoff_end : off = end_v
    · intro idx ha hb2; omega
    · have hlt : off < end_v := by have := hb.off_le_end; omega
      refine hout_range off end_v hb.end_le_wlen (by
        by_cases hdz : fullWatchSizeCore st.core dst = 0
        · exact Or.inl hdz
        · have hds := hb.disjoint_all src dst hsrc_lt hdst_lt hdst_ne.symm
            (by rw [hb.src_sz]; omega) (Nat.pos_of_ne_zero hdz)
          rw [hb.src_off, hb.src_sz, show off + (end_v - off) = end_v by omega] at hds
          exact Or.inr hds)
  have hslice_dst := hdst_slice (hb.other_slices dst hdst_lt hdst_ne)
  have hother_sl : ∀ l < 2 * st'.core.cur_vars, l ≠ src → WatchSliceOk F_cur st'.core l
      (fullWatchOffCore st'.core l) (fullWatchSizeCore st'.core l) := by
    intro l hl hls; rw [hcv'] at hl
    by_cases hld : l = dst
    · subst hld; exact hslice_dst
    · have hlws := hother_ws l hl hld; rw [hlws.1, hlws.2]
      refine (hb.other_slices l hl hls).relocate_same (by omega) hrefs fun idx hidx =>
        hout_range (fullWatchOffCore st.core l)
          (fullWatchOffCore st.core l + fullWatchSizeCore st.core l) (hb.other_bounds l hl hls) (by
            by_cases hdz : fullWatchSizeCore st.core dst = 0
            · exact Or.inl hdz
            · exact Or.inr (hb.disjoint_all l dst hl hdst_lt hld (by omega)
                (Nat.pos_of_ne_zero hdz))) _ (by omega) (by omega)
  exact
    { base :=
        { len_ok := hlen', core_pres := by rw [hst'_eq]; simpa using hcp
          scratch_pres := by rw [hst'_eq]; exact hb.scratch_pres
          off_le_end := hb.off_le_end, src_off := hsrc_ws.1.trans hb.src_off
          src_sz := hsrc_ws.2.trans hb.src_sz, end_le_wlen := hwlen'.symm ▸ hb.end_le_wlen
          off_pos := hb.off_pos
          other_bounds := fun l hl hls => by
            rw [hcv'] at hl; rw [hwlen']; have hw := hws l hl
            exact Nat.le_trans (by omega) (hb.other_bounds l hl hls)
          other_pos_off := fun l hl hls hpos => by
            rw [hcv'] at hl; have hw := hws l hl; rw [hw.1]
            exact hb.other_pos_off l hl hls (by omega)
          disjoint_all := fun l1 l2 h1 h2 hne hp1 hp2 => by
            rw [hcv'] at h1 h2
            obtain ⟨_, hw1s⟩ := hws l1 h1; obtain ⟨_, hw2s⟩ := hws l2 h2
            have hw1o := (hws l1 h1).1; have hw2o := (hws l2 h2).1
            rcases hb.disjoint_all l1 l2 h1 h2 hne (by omega) (by omega) with ha | hb2
            · exact Or.inl (by omega)
            · exact Or.inr (by omega)
          other_no_sent := fun l hl hls => (hother_sl l hl hls).ne_sentinel
          other_slices := hother_sl }
      off_le_p := h.off_le_p, p_le_end := h.p_le_end, red_le := h.red_le
      src_pref := h.src_pref.mono (by omega) hrefs fun idx ha _ =>
        hsrc_wstk idx ha (by have := h.p_le_end; omega)
      src_rem := h.src_rem.relocate_same (k := st.core) (by omega) hrefs fun idx _ =>
        hsrc_wstk (p + idx) (by have := h.off_le_p; omega) (by omega) }
theorem TransOuterInv.skip_bin {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off p end_v reduced : Nat} {st : FullState} {w0 : BitVec 32}
    (h : TransOuterInv c F0 F_cur s0 src off p end_v reduced st) (hp : p < end_v)
    (hget : st.core.wstk[p]? = some w0) (hflag : (w0 &&& 0x80000000#32) ≠ 0#32) :
    w0 ≠ 0xFFFFFFFF#32 ∧ (w0 &&& 0x7FFFFFFF#32).toNat < 2 * st.core.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [src, (w0 &&& 0x7FFFFFFF#32).toNat]) ∧
    TransOuterInv c F0 F_cur s0 src off (p + 1) end_v reduced st := by
  obtain ⟨hne, hlt, hent, htail⟩ := watchSlice_inv_bin h.src_rem (by omega) hget hflag
  have h1 : TombWatchSliceOk F_cur st.core src p 1 0 := .bin hget hflag hne hlt hent .empty
  have hpref := h.src_pref.append
    (by rw [show off + (p - off) = p by have := h.off_le_p; omega]; exact h1)
  rw [show p - off + 1 = (p + 1) - off by have := h.off_le_p; omega, Nat.add_zero] at hpref
  exact ⟨hne, hlt, hent,
    { h with
      off_le_p := by have := h.off_le_p; omega
      p_le_end := by omega, red_le := by have := h.red_le; omega, src_pref := hpref
      src_rem := by rwa [show end_v - p - 1 = end_v - (p + 1) by omega] at htail }⟩
theorem TransOuterInv.skip_large {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off p end_v reduced : Nat} {st : FullState} {w0 : BitVec 32}
    (h : TransOuterInv c F0 F_cur s0 src off p end_v reduced st) (hp : p < end_v)
    (hget : st.core.wstk[p]? = some w0) (hflag : (w0 &&& 0x80000000#32) = 0#32) :
    p + 2 ≤ end_v ∧ TransOuterInv c F0 F_cur s0 src off (p + 2) end_v reduced st := by
  obtain ⟨hle, cr, h1, hcr, href, htail⟩ := watchSlice_inv_large h.src_rem (by omega) hget hflag
  have hs : TombWatchSliceOk F_cur st.core src p 2 0 := .large hget h1 hflag hcr href .empty
  have hpref := h.src_pref.append
    (by rw [show off + (p - off) = p by have := h.off_le_p; omega]; exact hs)
  rw [show p - off + 2 = (p + 2) - off by have := h.off_le_p; omega, Nat.add_zero] at hpref
  exact ⟨by omega,
    { h with
      off_le_p := by have := h.off_le_p; omega
      p_le_end := by omega, red_le := by have := h.red_le; omega, src_pref := hpref
      src_rem := by rwa [show end_v - p - 2 = end_v - (p + 2) by omega] at htail }⟩

theorem TransOuterInv.mark_tomb {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off p end_v reduced : Nat} {st : FullState} {w0 : BitVec 32}
    {wu' tc' : BitVec 64} (h : TransOuterInv c F0 F_cur s0 src off p end_v reduced st)
    (hp : p < end_v) (hsrc_lt : src < 2 * st.core.cur_vars)
    (hget : st.core.wstk[p]? = some w0) (hflag : (w0 &&& 0x80000000#32) ≠ 0#32) :
    let st' : FullState :=
      { st with core := { st.core with wstk := st.core.wstk.set p 0xFFFFFFFF#32, wusable := wu' }
                scratch := { st.scratch with trans_cnt := tc' } }
    TransOuterInv c F0 F_cur s0 src off (p + 1) end_v (reduced + 1) st' := by
  intro st'; obtain ⟨_, _, _, htail⟩ := watchSlice_inv_bin h.src_rem (by omega) hget hflag
  have hp_len : p < st.core.wstk.length := by
    have := h.base.end_le_wlen; have := h.base.len_ok.core_ok.wlen_le
    rw [h.base.len_ok.core_ok.wstk_len_arr]; omega
  have hset_ne : ∀ idx, idx ≠ p → st'.core.wstk[idx]? = st.core.wstk[idx]? :=
    fun idx hi => List.getElem?_set_ne hi.symm
  have hset_p : st'.core.wstk[p]? = some 0xFFFFFFFF#32 := List.getElem?_set_self hp_len
  have hpref := (TombWatchSliceOk.mono (k := st.core) (k' := st'.core) (Nat.le_refl _)
    (fun _ hr => hr) (fun idx _ hi => hset_ne idx (by have := h.off_le_p; omega)) h.src_pref).append
    (by rw [show off + (p - off) = p by have := h.off_le_p; omega]
        exact (show TombWatchSliceOk F_cur st'.core src p 1 1 from .tomb hset_p .empty))
  rw [show p - off + 1 = (p + 1) - off by have := h.off_le_p; omega] at hpref
  exact
    { base := h.base.frame_wstk hsrc_lt (by simp [h.base.len_ok.core_ok.wstk_len_arr])
        (fun idx ho => hset_ne idx (by have := h.off_le_p; rcases ho with ho | ho <;> omega))
      off_le_p := by have := h.off_le_p; omega
      p_le_end := by omega, red_le := by have := h.off_le_p; have := h.red_le; omega
      src_pref := hpref
      src_rem := WatchSliceOk.relocate_same (k := st.core) (k' := st'.core) (Nat.le_refl _)
        (fun _ hr => hr) (fun idx _ => hset_ne (p + 1 + idx) (by omega))
        (by rwa [show end_v - p - 1 = end_v - (p + 1) by omega] at htail) }
theorem TransOuterInv.with_scratch {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off p end_v reduced : Nat} {st : FullState} {sc' : FullScratch}
    (h : TransOuterInv c F0 F_cur s0 src off p end_v reduced st) (hok : sc'.LengthsOk c)
    (hll : sc'.last_learned = st.scratch.last_learned)
    (hel : sc'.extend_len = st.scratch.extend_len) :
    TransOuterInv c F0 F_cur s0 src off p end_v reduced { st with scratch := sc' } :=
  { h with
    base :=
      { h.base with
        len_ok := h.base.len_ok.with_scratch hok
        scratch_pres := ⟨hll.trans h.base.scratch_pres.1, hel.trans h.base.scratch_pres.2⟩ } }
theorem TransOuterInv.of_reduced0 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off p end_v : Nat} {st : FullState}
    (hsp0 : FullSparseInv c F0 s0) (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (h : TransOuterInv c F0 F_cur s0 src off p end_v 0 st) : FullSparseInv c F0 st :=
  h.base.toSparse hsp0 hw0
    (by rw [h.base.src_off, h.base.src_sz]; exact h.src_full_tomb.to_watchSlice)
structure TransCompactInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 : FullState) (src off q p end_v reduced : Nat) (st : FullState) : Prop where
  base : TransOuterBase c F0 F_cur s0 src off end_v st
  q_range : off ≤ q ∧ q ≤ p ∧ p ≤ end_v
  red_le : p - q ≤ reduced
  comp_pref : WatchSliceOk F_cur st.core src off (q - off)
  comp_rem : TombWatchSliceOk F_cur st.core src p (end_v - p) (reduced - (p - q))
theorem TransCompactInv.init {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off p_old end_v reduced : Nat} {st : FullState}
    (h : TransOuterInv c F0 F_cur s0 src off p_old end_v reduced st) :
    TransCompactInv c F0 F_cur s0 src off off off end_v reduced st :=
  { base := h.base, q_range := ⟨Nat.le_refl _, Nat.le_refl _, h.base.off_le_end⟩
    red_le := by simp, comp_pref := by simp only [Nat.sub_self]; exact .empty
    comp_rem := by simpa only [Nat.sub_self, Nat.sub_zero] using h.src_full_tomb }
theorem TransCompactInv.step_tomb {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off q p end_v reduced : Nat} {st : FullState} {w0 : BitVec 32}
    (h : TransCompactInv c F0 F_cur s0 src off q p end_v reduced st) (hp : p < end_v)
    (hget : st.core.wstk[p]? = some w0) (htomb : w0 = 0xFFFFFFFF#32) :
    TransCompactInv c F0 F_cur s0 src off q (p + 1) end_v reduced st := by
  have hstep := h.comp_rem.inv_step (by omega) hget; subst htomb
  simp only [ft_tomb_bin_flag, ↓reduceIte] at hstep
  have hqr := h.q_range; have hrl := h.red_le; obtain ⟨_, htail⟩ := hstep
  exact
    { h with
      q_range := by omega, red_le := by omega
      comp_rem := by rwa [show end_v - p - 1 = end_v - (p + 1) by omega,
        show reduced - (p - q) - 1 = reduced - (p + 1 - q) by omega] at htail }
theorem TransCompactInv.step_bin {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off q p end_v reduced : Nat} {st : FullState} {w0 : BitVec 32}
    (h : TransCompactInv c F0 F_cur s0 src off q p end_v reduced st) (hp : p < end_v)
    (hsrc_lt : src < 2 * st.core.cur_vars) (hget : st.core.wstk[p]? = some w0)
    (hne : w0 ≠ 0xFFFFFFFF#32) (hflag : (w0 &&& 0x80000000#32) ≠ 0#32) :
    let st' := { st with core := { st.core with wstk := st.core.wstk.set q w0 } }
    TransCompactInv c F0 F_cur s0 src off (q + 1) (p + 1) end_v reduced st' := by
  intro st'; have hstep := h.comp_rem.inv_step (by omega) hget
  simp only [hflag, ↓reduceIte, hne] at hstep; obtain ⟨hlt, hent, htail⟩ := hstep
  have hqr := h.q_range
  have hqlen : q < st.core.wstk.length := by
    have := h.base.end_le_wlen; have := h.base.len_ok.core_ok.wlen_le
    rw [h.base.len_ok.core_ok.wstk_len_arr]; omega
  have hset_ne : ∀ idx, idx ≠ q → st'.core.wstk[idx]? = st.core.wstk[idx]? :=
    fun idx hi => List.getElem?_set_ne hi.symm
  have hpref := watchSlice_append (WatchSliceOk.relocate_same (k := st.core) (k' := st'.core)
    (p' := off) (Nat.le_refl _) (fun _ hr => hr) (fun idx hi => hset_ne (off + idx) (by omega))
    h.comp_pref)
    (by rw [show off + (q - off) = q by omega]
        exact .bin (List.getElem?_set_self hqlen) hflag hne hlt hent .empty)
  rw [show q - off + 1 = (q + 1) - off by omega] at hpref
  exact
    { base := h.base.frame_wstk hsrc_lt (wu' := st.core.wusable) (tc' := st.scratch.trans_cnt)
        (List.length_set.trans h.base.len_ok.core_ok.wstk_len_arr)
        (fun idx ho => hset_ne idx (by omega))
      q_range := by omega, red_le := by have := h.red_le; omega, comp_pref := hpref
      comp_rem := by
        rw [show p + 1 - (q + 1) = p - q by omega]
        exact TombWatchSliceOk.mono (k := st.core) (k' := st'.core) (Nat.le_refl _)
          (fun _ hr => hr) (fun idx ha _ => hset_ne idx (by omega))
          (by rwa [show end_v - p - 1 = end_v - (p + 1) by omega] at htail) }
theorem TransCompactInv.step_large {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off q p end_v reduced : Nat} {st : FullState} {w0 : BitVec 32}
    (h : TransCompactInv c F0 F_cur s0 src off q p end_v reduced st) (hp : p < end_v)
    (hsrc_lt : src < 2 * st.core.cur_vars) (hget : st.core.wstk[p]? = some w0)
    (hflag : (w0 &&& 0x80000000#32) = 0#32) : p + 1 < end_v ∧
    ∃ w1 : BitVec 32, st.core.wstk[p + 1]? = some w1 ∧
      let st1 := { st with core := { st.core with wstk := st.core.wstk.set q w0 } }
      let st' := { st1 with core := { st1.core with wstk := st1.core.wstk.set (q + 1) w1 } }
      TransCompactInv c F0 F_cur s0 src off (q + 2) (p + 2) end_v reduced st' := by
  have hstep := h.comp_rem.inv_step (by omega) hget; simp only [hflag, ↓reduceIte] at hstep
  obtain ⟨hle, cr, hcr_get, hcr_lt, hcr_ref, htail⟩ := hstep
  have hqr := h.q_range; refine ⟨by omega, cr, hcr_get, ?_⟩
  have hqlen : q < st.core.wstk.length := by
    have := h.base.end_le_wlen; have := h.base.len_ok.core_ok.wlen_le
    rw [h.base.len_ok.core_ok.wstk_len_arr]; omega
  have hq1len : q + 1 < (st.core.wstk.set q w0).length := by
    have := h.base.end_le_wlen; have := h.base.len_ok.core_ok.wlen_le
    rw [List.length_set, h.base.len_ok.core_ok.wstk_len_arr]; omega
  let st1 := { st with core := { st.core with wstk := st.core.wstk.set q w0 } }
  let st' := { st1 with core := { st1.core with wstk := st1.core.wstk.set (q + 1) cr } }
  have hset_ne : ∀ idx, idx ≠ q → idx ≠ q + 1 → st'.core.wstk[idx]? = st.core.wstk[idx]? :=
    fun idx h0 h1 => (List.getElem?_set_ne h1.symm).trans (List.getElem?_set_ne h0.symm)
  have hget_q : st'.core.wstk[q]? = some w0 :=
    (List.getElem?_set_ne (by omega : q + 1 ≠ q)).trans (List.getElem?_set_self hqlen)
  have hpref := watchSlice_append (WatchSliceOk.relocate_same (k := st.core) (k' := st'.core)
    (p' := off) (Nat.le_refl _) (fun _ hr => hr)
    (fun idx hi => hset_ne (off + idx) (by omega) (by omega)) h.comp_pref)
    (by rw [show off + (q - off) = q by omega]
        exact .large hget_q (List.getElem?_set_self hq1len) hflag hcr_lt hcr_ref .empty)
  rw [show q - off + 2 = (q + 2) - off by omega] at hpref
  exact
    { base := h.base.frame_wstk hsrc_lt (wu' := st.core.wusable) (tc' := st.scratch.trans_cnt)
        (by simp [h.base.len_ok.core_ok.wstk_len_arr])
        (fun idx ho => hset_ne idx (by omega) (by omega))
      q_range := by omega, red_le := by have := h.red_le; omega, comp_pref := hpref
      comp_rem := by
        rw [show p + 2 - (q + 2) = p - q by omega]
        exact TombWatchSliceOk.mono (k := st.core) (k' := st'.core) (Nat.le_refl _)
          (fun _ hr => hr) (fun idx ha _ => hset_ne idx (by omega) (by omega))
          (by rwa [show end_v - p - 2 = end_v - (p + 2) by omega] at htail) }

theorem TransCompactInv.at_end {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off q end_v reduced : Nat} {st : FullState}
    (h : TransCompactInv c F0 F_cur s0 src off q end_v end_v reduced st) :
    q = end_v - reduced ∧ off ≤ end_v - reduced ∧ end_v - reduced ≤ end_v ∧
    WatchSliceOk F_cur st.core src off (end_v - off - reduced) := by
  have hqr := h.q_range; have hrl := h.red_le
  have hz : reduced - (end_v - q) = 0 := by
    have hr := h.comp_rem; rw [Nat.sub_self] at hr; exact hr.eq_zero_of_rem0
  have hq : q = end_v - reduced := by omega
  have hp := h.comp_pref; rw [hq, show end_v - reduced - off = end_v - off - reduced by omega] at hp
  exact ⟨hq, by omega, by omega, hp⟩
theorem TransOuterBase.sentinel_fill_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off q_start q end_v : Nat} {st : FullState}
    (hb : TransOuterBase c F0 F_cur s0 src off end_v st) (hsrc_lt : src < 2 * st.core.cur_vars)
    (hq : off ≤ q_start ∧ q_start ≤ q ∧ q < end_v)
    (hsl : WatchSliceOk F_cur st.core src off (q_start - off)) :
    let st' := { st with core := { st.core with wstk := st.core.wstk.set q 0xFFFFFFFF#32 } }
    TransOuterBase c F0 F_cur s0 src off end_v st' ∧
    WatchSliceOk F_cur st'.core src off (q_start - off) :=
  ⟨hb.frame_wstk hsrc_lt (wu' := st.core.wusable) (tc' := st.scratch.trans_cnt)
    (by simp [hb.len_ok.core_ok.wstk_len_arr])
    (fun idx ho => List.getElem?_set_ne (by cases ho <;> omega)),
   WatchSliceOk.relocate_same (k := st.core) (p' := off) (Nat.le_refl _) (fun _ hr => hr)
    (fun idx hi => List.getElem?_set_ne (by omega)) hsl⟩
theorem TransOuterBase.of_compact_done_full {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off end_v reduced : Nat} {wu' : BitVec 64} {nb' : Nat} {st : FullState}
    (hsp0 : FullSparseInv c F0 s0) (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (hb : TransOuterBase c F0 F_cur s0 src off end_v st) (hsrc_lt : src < 2 * st.core.cur_vars)
    (hred : reduced ≤ end_v - off)
    (hsl : WatchSliceOk F_cur st.core src off (end_v - off - reduced)) :
    let new_sz := BitVec.ofNat 32 ((end_v - off) - reduced)
    let st' := { st with core := { st.core with
      wvec := st.core.wvec.set (2 * src + 1) new_sz, wusable := wu', num_binary := nb' } }
    FullSparseInv c F0 st' ∧ FullWitnessInv c F0 F_cur st'.core := by
  intro new_sz st'
  have hnw : new_sz.toNat = end_v - off - reduced := by
    have := hb.end_le_wlen; have := hb.len_ok.core_ok.wlen_le; have := c.hwcap
    unfold dimacsBound at *; simp only [new_sz, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  have hwv_len : 2 * src + 1 < st.core.wvec.length := by
    rw [hb.len_ok.core_ok.wvec_len]; have := hb.len_ok.core_ok.cur_vars_le; omega
  have hwv_even : ∀ l < 2 * st.core.cur_vars,
      fullWatchOffCore st'.core l = fullWatchOffCore st.core l := fun l _ =>
    congrArg (fun o : Option (BitVec 32) => (o.getD 0#32).toNat)
      (List.getElem?_set_ne (by omega : 2 * src + 1 ≠ 2 * l))
  have hwv_odd_ne : ∀ l < 2 * st.core.cur_vars, l ≠ src →
      fullWatchSizeCore st'.core l = fullWatchSizeCore st.core l := fun l _ hls =>
    congrArg (fun o : Option (BitVec 32) => (o.getD 0#32).toNat)
      (List.getElem?_set_ne (by omega : 2 * src + 1 ≠ 2 * l + 1))
  have hsrc_off' : fullWatchOffCore st'.core src = off := (hwv_even src hsrc_lt).trans hb.src_off
  have hsrc_sz' : fullWatchSizeCore st'.core src = end_v - off - reduced := by
    unfold fullWatchSizeCore
    change ((st.core.wvec.set (2 * src + 1) new_sz)[2 * src + 1]?.getD 0#32).toNat = _
    rw [List.getElem?_set_self hwv_len]; simp [hnw]
  have hsl' : WatchSliceOk F_cur st'.core src
      (fullWatchOffCore st'.core src) (fullWatchSizeCore st'.core src) := by
    rw [hsrc_off', hsrc_sz']
    exact WatchSliceOk.relocate_same (k := st.core) (Nat.le_refl _)
      (fun _ hr => hr) (fun _ _ => rfl) hsl
  have hws : ∀ l < 2 * st.core.cur_vars, fullWatchOffCore st'.core l = fullWatchOffCore st.core l ∧
      fullWatchSizeCore st'.core l ≤ fullWatchSizeCore st.core l := fun l hl => by
    by_cases hls : l = src
    · subst hls; rw [hsrc_off', hsrc_sz', hb.src_off, hb.src_sz]; exact ⟨rfl, by omega⟩
    · exact ⟨hwv_even l hl, by rw [hwv_odd_ne l hl hls]; exact Nat.le_refl _⟩
  have := hb.off_le_end
  have hb' : TransOuterBase c F0 F_cur s0 src off (end_v - reduced) st' :=
    { len_ok := ⟨{ hb.len_ok.core_ok with wvec_len := by simp [st', hb.len_ok.core_ok.wvec_len] },
        hb.len_ok.scratch_ok⟩, core_pres := hb.core_pres, scratch_pres := hb.scratch_pres
      off_le_end := by omega, src_off := hsrc_off', src_sz := by rw [hsrc_sz']; omega
      end_le_wlen := Nat.le_trans (by omega) hb.end_le_wlen, off_pos := hb.off_pos
      other_bounds := fun l hl hls => by
        rw [(hws l hl).1]; have := (hws l hl).2
        exact Nat.le_trans (by omega) (hb.other_bounds l hl hls)
      other_pos_off := fun l hl hls hp => by
        rw [(hws l hl).1]; have := (hws l hl).2; exact hb.other_pos_off l hl hls (by omega)
      disjoint_all := fun l1 l2 h1 h2 hne hp1 hp2 => by
        obtain ⟨_, hw1s⟩ := hws l1 h1; obtain ⟨_, hw2s⟩ := hws l2 h2
        have hw1o := (hws l1 h1).1; have hw2o := (hws l2 h2).1
        exact Or.imp (fun ha => by omega) (fun hb2 => by omega)
          (hb.disjoint_all l1 l2 h1 h2 hne (by omega) (by omega))
      other_no_sent := fun l hl hls => by
        rw [hwv_even l hl, hwv_odd_ne l hl hls]; exact hb.other_no_sent l hl hls
      other_slices := fun l hl hls => by
        rw [hwv_even l hl, hwv_odd_ne l hl hls]
        exact WatchSliceOk.relocate_same (k := st.core) (Nat.le_refl _) (fun _ hr => hr)
          (fun _ _ => rfl) (hb.other_slices l hl hls) }
  exact ⟨hb'.toSparse hsp0 hw0 hsl', hb'.toWitness_of_src_clean hw0 hsl'⟩
theorem TransOuterBase.of_compact_done {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 : FullState} {src off end_v reduced : Nat} {wu' : BitVec 64} {nb' : Nat} {st : FullState}
    (hsp0 : FullSparseInv c F0 s0) (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (hb : TransOuterBase c F0 F_cur s0 src off end_v st) (hsrc_lt : src < 2 * st.core.cur_vars)
    (hred : reduced ≤ end_v - off)
    (hsl : WatchSliceOk F_cur st.core src off (end_v - off - reduced)) :
    let new_sz := BitVec.ofNat 32 ((end_v - off) - reduced)
    let st' := { st with core := { st.core with
      wvec := st.core.wvec.set (2 * src + 1) new_sz, wusable := wu', num_binary := nb' } }
    FullSparseInv c F0 st' :=
  (hb.of_compact_done_full hsp0 hw0 hsrc_lt hred hsl).1
end TransLitInvariants
end LeanQbe.T.Examples.Kissat.Full
