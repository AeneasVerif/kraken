module

public import LeanQbe.T.Examples.Kissat.FullSweepFwdLemmas1
public meta import LeanQbe.T.Logic.C0Step

/-!
# Kissat `D-Full` Bounded Cone SAT Sweeping — Part 2 (`Stage 4`)

Parametric `(Γ : Env)` `Func.wp` proof for:
3. `full_sweep_cone` (`full_sweep_cone_wp`, `Full.lean` #12)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat Kraken.Bedrock2.Test
open FullSweepFwdSpecs FullSweepFwdHelpers

/-! ## 0. O(1)-per-step scoped symbolic executor (`FullSweepFwdFast`, zero stack-depth blowup) -/

namespace FullSweepFwdFast

theorem strip_wp {Γ rs Q X e m} (h : wp (rs := rs) Γ Q X e m) : wp Γ Q X e m := h

section FastWp
variable {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
local notation "K " t => Tup Val [t] → Expr Val Cont rs
local notation "W " e => wp Γ Q X e m
theorem sw_wp_copy {t} {a : Arg Val t} {k : K t} (h : W (k (a.val, ()))) :
    W (.let_ (Op.mk (.copy t) (a, ())) k) := by simpa only [wp_let_copy_eq] using h
theorem sw_wp_add {n} {a b : Arg Val (.bits n)} {k : K (.bits n)}
    (h : W (k (a.val + b.val, ()))) : W (.let_ (Op.mk (.add _) (a, b, ())) k) := by
  simpa only [wp_let_add_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2] using h
theorem sw_wp_sub {n} {a b : Arg Val (.bits n)} {k : K (.bits n)}
    (h : W (k (a.val - b.val, ()))) : W (.let_ (Op.mk (.sub _) (a, b, ())) k) := by
  simpa only [wp_let_sub_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2] using h
theorem sw_wp_mul {n} {a b : Arg Val (.bits n)} {k : K (.bits n)}
    (h : W (k (a.val * b.val, ()))) : W (.let_ (Op.mk (.mul _) (a, b, ())) k) := by
  simpa only [wp_let_mul_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2] using h
theorem sw_wp_and {n} {a b : Arg Val (.bits n)} {k : K (.bits n)}
    (h : W (k (a.val &&& b.val, ()))) : W (.let_ (Op.mk (.and _) (a, b, ())) k) := by
  simpa only [wp_let_and_eq, lift2] using h
theorem sw_wp_or {n} {a b : Arg Val (.bits n)} {k : K (.bits n)}
    (h : W (k (a.val ||| b.val, ()))) : W (.let_ (Op.mk (.or _) (a, b, ())) k) := by
  simpa only [wp_let_or_eq, lift2] using h
theorem sw_wp_xor {n} {a b : Arg Val (.bits n)} {k : K (.bits n)}
    (h : W (k (a.val ^^^ b.val, ()))) : W (.let_ (Op.mk (.xor _) (a, b, ())) k) := by
  simpa only [wp_let_xor_eq, lift2] using h
theorem sw_wp_not {n} {a : Arg Val (.bits n)} {k : K (.bits n)}
    (h : W (k (~~~a.val, ()))) : W (.let_ (Op.mk (.not _) (a, ())) k) := by
  simpa only [wp_let_not_eq, lift1] using h
theorem sw_wp_shl {n} {a b : Arg Val (.bits n)} {k : K (.bits n)}
    (h : W (k (a.val <<< (b.val.toNat % n), ()))) : W (.let_ (Op.mk (.shl _) (a, b, ())) k) := by
  simpa only [wp_let_shl_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2] using h
theorem sw_wp_shl1_64 {a : Arg Val (.bits 64)} {k : K (.bits 64)}
    (h : W (k (a.val <<< (1 : Nat), ()))) : W (.let_ (Op.mk (.shl _) (a, Arg.imm 1#64, ())) k) :=
  sw_wp_shl (by simpa only [Arg.val_imm, BitVec.reduceToNat, Nat.reduceMod] using h)
theorem sw_wp_shl16_64 {a : Arg Val (.bits 64)} {k : K (.bits 64)}
    (h : W (k (a.val <<< (16 : Nat), ()))) :
    W (.let_ (Op.mk (.shl _) (a, Arg.imm 16#64, ())) k) :=
  sw_wp_shl (by simpa only [Arg.val_imm, BitVec.reduceToNat, Nat.reduceMod] using h)
theorem sw_wp_shl1_32 {a : Arg Val (.bits 32)} {k : K (.bits 32)}
    (h : W (k (a.val <<< (1 : Nat), ()))) : W (.let_ (Op.mk (.shl _) (a, Arg.imm 1#32, ())) k) :=
  sw_wp_shl (by simpa only [Arg.val_imm, BitVec.reduceToNat, Nat.reduceMod] using h)
theorem sw_wp_lshr1_32 {a : Arg Val (.bits 32)} {k : K (.bits 32)}
    (h : W (k (a.val >>> (1 : Nat), ()))) :
    W (.let_ (Op.mk (.lshr _) (a, Arg.imm 1#32, ())) k) := by
  simpa only [wp_let_lshr_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2, Arg.val_imm,
    BitVec.reduceToNat, Nat.reduceMod] using h
theorem sw_wp_zext32_64 {a : Arg Val (.bits 32)} {k : K (.bits 64)}
    (h : W (k (a.val.setWidth 64, ()))) : W (.let_ (Op.mk (.zext 32 64) (a, ())) k) := by
  rw [wp_let_zext_eq]; exact ⟨by decide, h⟩
theorem sw_wp_sext32_64 {a : Arg Val (.bits 32)} {k : K (.bits 64)}
    (h : W (k (a.val.signExtend 64, ()))) : W (.let_ (Op.mk (.sext 32 64) (a, ())) k) := by
  rw [wp_let_sext_eq]; exact ⟨by decide, h⟩
theorem sw_wp_sext8_32 {a : Arg Val (.bits 8)} {k : K (.bits 32)}
    (h : W (k (a.val.signExtend 32, ()))) : W (.let_ (Op.mk (.sext 8 32) (a, ())) k) := by
  rw [wp_let_sext_eq]; exact ⟨by decide, h⟩
theorem sw_wp_sext32_64_0 {k : K (.bits 64)} (h : W (k (0#64, ()))) :
    W (.let_ (Op.mk (.sext 32 64) (Arg.imm 0#32, ())) k) := by
  simpa only [wp_let_sext_eq] using ⟨by decide, h⟩
theorem sw_wp_sext32_64_16 {k : K (.bits 64)} (h : W (k (16#64, ()))) :
    W (.let_ (Op.mk (.sext 32 64) (Arg.imm 16#32, ())) k) := by
  simpa only [wp_let_sext_eq] using ⟨by decide, h⟩
theorem sw_wp_sext32_64_1 {k : K (.bits 64)} (h : W (k (1#64, ()))) :
    W (.let_ (Op.mk (.sext 32 64) (Arg.imm 1#32, ())) k) := by
  simpa only [wp_let_sext_eq] using ⟨by decide, h⟩
theorem sw_wp_trunc64_32 {a : Arg Val (.bits 64)} {k : K (.bits 32)}
    (h : W (k (a.val.setWidth 32, ()))) : W (.let_ (Op.mk (.trunc 64 32) (a, ())) k) := by
  simpa only [wp_let_trunc_eq] using ⟨by decide, h⟩
theorem sw_wp_trunc32_8 {a : Arg Val (.bits 32)} {k : K (.bits 8)}
    (h : W (k (a.val.setWidth 8, ()))) : W (.let_ (Op.mk (.trunc 32 8) (a, ())) k) := by
  simpa only [wp_let_trunc_eq] using ⟨by decide, h⟩
theorem sw_wp_cmp {o n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : W (k (o.evalBits a.val b.val, ()))) :
    W (.let_ (Op.mk (.cmp o (.bits n) .bool rfl) (a, b, ())) k) := by
  simpa only [wp_let_cmp_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, cast_eq, liftCmp] using h
theorem sw_wp_cmp_eq {n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : W (k ((a.val == b.val), ()))) :
    W (.let_ (Op.mk (.cmp .eq (.bits n) .bool rfl) (a, b, ())) k) :=
  sw_wp_cmp (evalBits_eq_beq a.val b.val ▸ h)
theorem sw_wp_cmp_ne {n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : W (k ((a.val != b.val), ()))) :
    W (.let_ (Op.mk (.cmp .ne (.bits n) .bool rfl) (a, b, ())) k) :=
  sw_wp_cmp (evalBits_ne_bne a.val b.val ▸ h)
theorem sw_wp_cmp_ult {n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : W (k (a.val.ult b.val, ()))) :
    W (.let_ (Op.mk (.cmp .ult (.bits n) .bool rfl) (a, b, ())) k) :=
  sw_wp_cmp (evalBits_ult_eq a.val b.val ▸ h)
theorem sw_wp_cmp_ule {n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : W (k (a.val.ule b.val, ()))) :
    W (.let_ (Op.mk (.cmp .ule (.bits n) .bool rfl) (a, b, ())) k) :=
  sw_wp_cmp (evalBits_ule_eq a.val b.val ▸ h)
theorem sw_wp_cmp_ugt {n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : W (k (b.val.ult a.val, ()))) :
    W (.let_ (Op.mk (.cmp .ugt (.bits n) .bool rfl) (a, b, ())) k) :=
  sw_wp_cmp (evalBits_ugt_eq a.val b.val ▸ h)
theorem sw_wp_cmp_uge {n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : W (k (b.val.ule a.val, ()))) :
    W (.let_ (Op.mk (.cmp .uge (.bits n) .bool rfl) (a, b, ())) k) :=
  sw_wp_cmp (evalBits_uge_eq a.val b.val ▸ h)
theorem sw_wp_cmp_slt {n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : W (k (a.val.slt b.val, ()))) :
    W (.let_ (Op.mk (.cmp .slt (.bits n) .bool rfl) (a, b, ())) k) :=
  sw_wp_cmp (evalBits_slt_eq a.val b.val ▸ h)
theorem sw_wp_cmp_sgt {n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : W (k (b.val.slt a.val, ()))) :
    W (.let_ (Op.mk (.cmp .sgt (.bits n) .bool rfl) (a, b, ())) k) :=
  sw_wp_cmp (evalBits_sgt_eq a.val b.val ▸ h)
theorem sw_wp_not_bool {a : Arg Val .bool} {k : K .bool} (h : W (k (!a.val, ()))) :
    W (.let_ (Op.mk (.not .bool) (a, ())) k) := by simpa only [wp_let_not_eq, lift1] using h
theorem sw_wp_jump0 {L : Cont []} (h : L () m) : W (.jump L ()) := h
theorem sw_wp_jump1 {t} {L : Cont [t]} {a : Arg Val t}
    (h : L (a.val, ()) m) : W (.jump L (a, ())) := h
theorem sw_wp_jump2 {t1 t2} {L : Cont [t1, t2]} {a : Arg Val t1} {b : Arg Val t2}
    (h : L (a.val, b.val, ()) m) : W (.jump L (a, b, ())) := h
theorem sw_wp_jump3 {t1 t2 t3} {L : Cont [t1, t2, t3]} {a : Arg Val t1} {b : Arg Val t2}
    {c : Arg Val t3} (h : L (a.val, b.val, c.val, ()) m) : W (.jump L (a, b, c, ())) := h
theorem sw_wp_jump4 {t1 t2 t3 t4} {L : Cont [t1, t2, t3, t4]} {a : Arg Val t1}
    {b : Arg Val t2} {c : Arg Val t3} {d : Arg Val t4} (h : L (a.val, b.val, c.val, d.val, ()) m) :
    W (.jump L (a, b, c, d, ())) := h
end FastWp

theorem sw_wp_ret1 {Γ X m t} {Q : Post [t]} {a : Arg Val t} (h : Q (a.val, ()) m) :
    wp Γ Q X (.ret (a, ())) m := h

private meta def swReduceProjOnce (e : Lean.Expr) : Lean.Expr :=
  e.replace fun sub => match sub with
    | .proj ``Prod 0 arg => if arg.isAppOfArity ``Prod.mk 4 then some (arg.getArg! 2) else none
    | .proj ``Prod 1 arg => if arg.isAppOfArity ``Prod.mk 4 then some (arg.getArg! 3) else none
    | _ =>
      if sub.isAppOfArity ``Prod.fst 3 && sub.appArg!.isAppOfArity ``Prod.mk 4 then
        some (sub.appArg!.getArg! 2)
      else if sub.isAppOfArity ``Prod.snd 3 && sub.appArg!.isAppOfArity ``Prod.mk 4 then
        some (sub.appArg!.getArg! 3)
      else if sub.isAppOf ``Arg.val && sub.getAppNumArgs ≥ 1 &&
          (sub.appArg!.isAppOf ``Arg.var || sub.appArg!.isAppOf ``Arg.imm) &&
          sub.appArg!.getAppNumArgs ≥ 1 then some sub.appArg!.appArg!
      else none
private meta def swReduceHeadE (e : Lean.Expr) : Lean.Expr :=
  swReduceProjOnce (swReduceProjOnce (swReduceProjOnce e.headBeta))
private meta def swNormWpGoal (g : Lean.MVarId) : Lean.Elab.Tactic.TacticM Lean.MVarId := do
  let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData.headBeta
  if ty.isAppOf ``wp && ty.getAppNumArgs == 6 then
    let e := ty.getArg! 4; let e' := swReduceHeadE e
    if e' != e then return ← g.change (Lean.mkAppN ty.getAppFn (ty.getAppArgs.set! 4 e'))
  return g

private meta def swFastLetLemmas (op : Lean.Expr) : Array Lean.Name :=
  if op.isAppOf ``Op.mk && op.getAppNumArgs == 5 then
    let code := op.getArg! 3
    match code.getAppFn.constName? with
    | some ``OpCode.copy => #[``sw_wp_copy] | some ``OpCode.add => #[``sw_wp_add]
    | some ``OpCode.sub => #[``sw_wp_sub] | some ``OpCode.mul => #[``sw_wp_mul]
    | some ``OpCode.and => #[``sw_wp_and] | some ``OpCode.or => #[``sw_wp_or]
    | some ``OpCode.xor => #[``sw_wp_xor] | some ``OpCode.zext => #[``sw_wp_zext32_64]
    | some ``OpCode.lshr => #[``sw_wp_lshr1_32]
    | some ``OpCode.trunc => #[``sw_wp_trunc64_32, ``sw_wp_trunc32_8]
    | some ``OpCode.not =>
      if code.getAppNumArgs == 1 && (code.getArg! 0).isConstOf ``Ty.bool then #[``sw_wp_not_bool]
      else #[``sw_wp_not]
    | some ``OpCode.shl => #[``sw_wp_shl1_64, ``sw_wp_shl16_64, ``sw_wp_shl1_32, ``sw_wp_shl]
    | some ``OpCode.sext => #[``sw_wp_sext32_64_0, ``sw_wp_sext32_64_1, ``sw_wp_sext32_64_16,
        ``sw_wp_sext32_64, ``sw_wp_sext8_32]
    | some ``OpCode.cmp =>
      if code.getAppNumArgs == 4 then
        match (code.getArg! 0).getAppFn.constName? with
        | some ``CmpOp.eq => #[``sw_wp_cmp_eq] | some ``CmpOp.ne => #[``sw_wp_cmp_ne]
        | some ``CmpOp.ult => #[``sw_wp_cmp_ult] | some ``CmpOp.ule => #[``sw_wp_cmp_ule]
        | some ``CmpOp.ugt => #[``sw_wp_cmp_ugt] | some ``CmpOp.uge => #[``sw_wp_cmp_uge]
        | some ``CmpOp.slt => #[``sw_wp_cmp_slt] | some ``CmpOp.sgt => #[``sw_wp_cmp_sgt]
        | _ => #[]
      else #[]
    | _ => #[]
  else #[]

private meta def swClearStale (m0 : Lean.Expr) : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
    let .fvar mId := m0 | return
    for d in (← Lean.getLCtx).decls.toArray.reverse do
      let some d := d | continue
      let t ← Lean.instantiateMVars d.type
      if t.isAppOf ``Std.ExtHashMap.sep && t.appArg! == m0 then
        try Lean.Elab.Tactic.liftMetaTactic1 fun g => some <$> g.clear d.fvarId catch _ => pure ()
    try Lean.Elab.Tactic.liftMetaTactic1 fun g => some <$> g.clear mId catch _ => pure ()

private meta def swStepOnce (unrollGroup splitJnz : Bool) : Lean.Elab.Tactic.TacticM Bool :=
  Lean.Elab.Tactic.withMainContext do
    let g ← Lean.Elab.Tactic.getMainGoal
    let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData.headBeta
    if ty.isAppOf ``wp && ty.getAppNumArgs == 6 then
      let e := (ty.getArg! 4).consumeMData.headBeta
      match e.getAppFn.constName? with
      | some ``Expr.let_ =>
        if e.getAppNumArgs != 6 then return false
        for lem in swFastLetLemmas (e.getArg! 4).headBeta do
          let s ← Lean.Elab.Tactic.saveState
          try
            let [hk] ← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels lem) | s.restore; continue
            Lean.Elab.Tactic.setGoals [← swNormWpGoal hk]; return true
          catch _ => s.restore
        return false
      | some ``Expr.load =>
        let s ← Lean.Elab.Tactic.saveState
        try
          let [hl, hk] := (← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels ``wp_load_of)).take 2
            | s.restore; return false
          LeanQbe.T.C0Step.memSolve true hl
          Lean.Elab.Tactic.setGoals [← swNormWpGoal hk]; return true
        catch _ => s.restore; return false
      | some ``Expr.store =>
        let s ← Lean.Elab.Tactic.saveState
        try
          let m0 := ty.getArg! 5
          let [hs, hk] := (← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels ``wp_store_sep)).take 2
            | s.restore; return false
          LeanQbe.T.C0Step.memSolve false hs; Lean.Elab.Tactic.setGoals [hk]
          let mId := Lean.mkIdent `m; let hmId := Lean.mkIdent `hm
          Lean.Elab.Tactic.evalTactic (← `(tactic| intro $mId:ident $hmId:ident;
            try simp only [Arg.val_var, Arg.val_imm, Std.ExtHashMap.sep_emp] at $hmId:ident))
          swClearStale m0; return true
        catch _ => s.restore; return false
      | some ``Expr.jnz =>
        if !splitJnz then return false
        let hc := Lean.mkIdent `hc
        Lean.Elab.Tactic.evalTactic (← `(tactic|
          (refine wp_jnz_of (fun $hc:ident => ?_) (fun $hc:ident => ?_)) <;> (
            try simp only [Arg.val_var, Arg.val_imm] at $hc:ident; c0_cond $hc
            try (first | exact ($hc).elim | exact absurd rfl $hc | exact $hc rfl
                       | exact absurd trivial $hc))))
        return true
      | some ``Expr.jump | some ``Expr.ret =>
        let lems := if e.isAppOf ``Expr.ret then #[``sw_wp_ret1]
          else #[``sw_wp_jump0, ``sw_wp_jump1, ``sw_wp_jump2, ``sw_wp_jump3, ``sw_wp_jump4]
        for lem in lems do
          let s2 ← Lean.Elab.Tactic.saveState
          try
            let [hk] ← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels lem) | s2.restore; continue
            let hkTy ← Lean.instantiateMVars (← hk.getType)
            let hkTy' := swReduceProjOnce (swReduceProjOnce hkTy)
            Lean.Elab.Tactic.setGoals [← if hkTy' != hkTy then hk.change hkTy' else pure hk]
            return true
          catch _ => s2.restore
        return false
      | some ``Expr.group =>
        if unrollGroup && e.getAppNumArgs == 6 then
          if let .lam _ _ b _ := e.getArg! 4 then
            if !b.hasLooseBVars then
              let J := Lean.mkIdent `J_jn; let hJ := Lean.mkIdent `hJ_jn
              Lean.Elab.Tactic.evalTactic (← `(tactic|
                refine wp_unroll_group fun $J:ident $hJ:ident => ?_))
              return true
        return false
      | some ``Blocks.get =>
        if e.getAppNumArgs == 8 then
          let bs := (e.getArg! 5).headBeta
          if bs.isAppOf ``Blocks.cons && bs.getAppNumArgs == 7 &&
              (e.getArg! 6).isAppOf ``Member.here then
            let newE := swReduceHeadE (Lean.mkApp (bs.getArg! 5) (e.getArg! 7))
            let newTy := Lean.mkAppN ty.getAppFn (ty.getAppArgs.set! 4 newE)
            Lean.Elab.Tactic.setGoals [← g.change newTy]; return true
        return false
      | _ => return false
    else if let .fvar jId := ty.getAppFn then
      for d in (← Lean.getLCtx).decls.toArray.reverse do
        let some d := d | continue
        let mut dt ← Lean.instantiateMVars d.type; let mut lastPrem : Option Lean.Expr := none
        while let .forallE _ dom body _ := dt do lastPrem := some dom; dt := body
        if dt.getAppFn == .fvar jId then
          if let some p := lastPrem then
            let p := p.consumeMData.headBeta
            if p.isAppOf ``wp && p.getAppNumArgs == 6 &&
                (p.getArg! 4).consumeMData.headBeta.isAppOf ``Blocks.get then
              let s ← Lean.Elab.Tactic.saveState
              try let [hk] ← g.apply d.toExpr | s.restore; continue
                  Lean.Elab.Tactic.setGoals [hk]; return true
              catch _ => s.restore
      return false
    return false

private meta partial def swStepsLoop (unrollGroup splitJnz : Bool) (fuel : Nat) :
    Lean.Elab.Tactic.TacticM Unit := do
  if fuel = 0 then return
  let mut out : Array Lean.MVarId := #[]
  for g in (← Lean.Elab.Tactic.getUnsolvedGoals) do
    if ← g.isAssigned then continue
    Lean.Elab.Tactic.setGoals [g]
    if ← swStepOnce unrollGroup splitJnz then swStepsLoop unrollGroup splitJnz (fuel - 1)
    out := out ++ (← Lean.Elab.Tactic.getUnsolvedGoals)
  Lean.Elab.Tactic.setGoals out.toList

scoped elab "sw_fast" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| try refine strip_wp ?_)); swStepsLoop false false 2000
scoped elab "sw_unroll" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| try refine strip_wp ?_)); swStepsLoop true false 2000
scoped elab "sw_split" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| try refine strip_wp ?_))
  swStepsLoop false false 2000; let _ ← swStepOnce false true
scoped elab "sw_bd" : tactic => do
  let hc := Lean.mkIdent `hc
  Lean.Elab.Tactic.evalTactic (← `(tactic|
    (try simp only [bv_c0, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat] at $hc:ident ⊢);
    first | exact $hc:ident | omega))
@[scoped bv_c0] theorem bv64_shl1_nat (x : BitVec 64) :
    (x <<< (1 : Nat)).toNat = (2 * x.toNat) % 2 ^ 64 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]
@[scoped bv_c0] theorem bv32_shl1_nat (x : BitVec 32) :
    (x <<< (1 : Nat)).toNat = (2 * x.toNat) % 2 ^ 32 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]
@[scoped bv_c0] theorem bv32_shr1_nat (x : BitVec 32) :
    (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
end FullSweepFwdFast

section
open scoped FullArenaTactics FullSweepFwdTactics FullSweepFwdFast

/-! ## 1. Pure & memory helpers for `full_sweep_cone_wp` -/

private theorem bv32_shr1_toNat (x : BitVec 32) : (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
private theorem bv32_and1_toNat (x : BitVec 32) : (x &&& 1#32).toNat = x.toNat % 2 := by
  rw [BitVec.toNat_and, show (1#32).toNat = 1 from rfl]
  simp [Nat.and_two_pow_sub_one_eq_mod x.toNat 1]
private theorem bv32_shl1_or_and1 (t l : BitVec 32) (ht : t.toNat < 2 ^ 31) :
    ((t <<< (1 : Nat)) ||| (l &&& 1#32)).toNat = 2 * t.toNat + l.toNat % 2 := by
  have h1 : (l &&& 1#32).toNat < 2 := by rw [bv32_and1_toNat]; omega
  simpa [bv32_and1_toNat] using bv32_shl1_or_pol t (l &&& 1#32) ht h1
private theorem bv64_shl1_toNat (x : BitVec 32) :
    (x.setWidth 64 <<< (1 : Nat)).toNat = 2 * x.toNat := by
  have hx := x.isLt; simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by omega : x.toNat * 2 < 2 ^ 64)]; omega
private theorem bv64_shl1_add1_toNat (x : BitVec 32) :
    ((x.setWidth 64 <<< (1 : Nat)) + 1#64).toNat = 2 * x.toNat + 1 := by
  have hx := x.isLt; rw [BitVec.toNat_add, bv64_shl1_toNat, show (1#64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega : 2 * x.toNat + 1 < 2 ^ 64)]

private theorem bv64_pack_toNat (nv nc : BitVec 32) (hnv : nv.toNat ≤ 24) (hnc : nc.toNat ≤ 64) :
    ((nv.setWidth 64 ||| (nc.setWidth 64 <<< (16 : Nat))) &&& 0xFFFF#64).toNat = nv.toNat ∧
    ((nv.setWidth 64 ||| (nc.setWidth 64 <<< (16 : Nat))) >>> (16 : Nat)).toNat = nc.toNat := by
  have hpk := bv64_pack_nv_nc hnv hnc
  have hor_lt : nv.toNat ||| (nc.toNat <<< 16) < 2 ^ 30 :=
    Nat.or_lt_two_pow (by omega) (by rw [Nat.shiftLeft_eq]; omega)
  have heq : nv.setWidth 64 ||| (nc.setWidth 64 <<< (16 : Nat)) =
      BitVec.ofNat 64 (nv.toNat ||| (nc.toNat <<< 16)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_or, BitVec.toNat_shiftLeft, bv32_zext64_eq, bv32_zext64_eq,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : nv.toNat < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : nc.toNat < 2 ^ 64),
      Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega : nc.toNat <<< 16 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega)]
  rw [heq]; have h1 := congrArg BitVec.toNat hpk.1; have h2 := congrArg BitVec.toNat hpk.2
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : nv.toNat < 2 ^ 32),
    Nat.mod_eq_of_lt (by omega : nc.toNat < 2 ^ 32)] at h1 h2
  have hlt1 : (BitVec.ofNat 64 (nv.toNat ||| (nc.toNat <<< 16)) &&& 0xFFFF#64).toNat < 2 ^ 32 := by
    rw [BitVec.toNat_and, show (0xFFFF#64).toNat = 65535 from rfl]
    have := Nat.and_le_right (n := (BitVec.ofNat 64 (nv.toNat ||| (nc.toNat <<< 16))).toNat)
      (m := 65535); omega
  have hlt2 : (BitVec.ofNat 64 (nv.toNat ||| (nc.toNat <<< 16)) >>> (16 : Nat)).toNat < 2 ^ 32 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega)]; omega
  rw [Nat.mod_eq_of_lt hlt1] at h1; rw [Nat.mod_eq_of_lt hlt2] at h2; exact ⟨h1, h2⟩

private theorem cone_clause_entails_of_filtered {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} {cr : Nat} {kept : List Nat}
    (hw : FullWitnessInv c F0 F_cur k) (hl0 : k.cur_level = 0)
    (href : cr ∈ fullArenaClauseRefsCore k) (hng : fullArenaClauseGarbCore k cr = false)
    (hcov : ∀ l ∈ fullArenaClauseLitsCore k cr, k.vals[l]?.getD 0#8 = 0xFF#8 ∨ l ∈ kept) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause kept) := by
  rw [CNF.entails_clause_def]; intro α hα
  have hent := hw.arena.entails cr href hng; rw [CNF.entails_clause_def] at hent
  obtain ⟨l, hl_mem, hl_sat⟩ := (clause_sat_cnfClause_iff _ _).mp (hent α hα)
  rcases hcov l hl_mem with hfals | hkept
  · exact absurd ((sat_cnfClause_singleton _ _).mpr hl_sat)
      (level0_false_not_sat hw hl0 (hw.arena.lits_lt cr href hng l hl_mem) hfals hα)
  · exact (clause_sat_cnfClause_iff _ _).mpr ⟨l, hkept, hl_sat⟩

private theorem fullArenaClauseLitsCore_mem_iff {k : FullCoreState} {cr l : Nat}
    (hbd : cr + 3 + (k.arena[cr + 2]?.getD 0#32).toNat ≤ k.arena.length) :
    l ∈ fullArenaClauseLitsCore k cr ↔
      ∃ i < (k.arena[cr + 2]?.getD 0#32).toNat, (k.arena[cr + 3 + i]?.getD 0#32).toNat = l := by
  unfold fullArenaClauseLitsCore fullArenaClauseSizeCore
  generalize (k.arena[cr + 2]?.getD 0#32).toNat = sz at hbd ⊢
  simp only [List.mem_map]; constructor
  · rintro ⟨w, hw, rfl⟩; obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hw
    simp only [List.length_take, List.length_drop,
      Nat.min_eq_left (by omega : sz ≤ k.arena.length - (cr + 3))] at hi
    refine ⟨i, hi, ?_⟩; simp only [List.getElem_take, List.getElem_drop] at heq
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some, heq]
  · rintro ⟨i, hi, rfl⟩
    have hmem : ((k.arena.drop (cr + 3)).take sz)[i]'(by simp; omega) ∈
        (k.arena.drop (cr + 3)).take sz := List.getElem_mem _
    exact ⟨k.arena[cr + 3 + i]'(by omega),
      by simpa [List.getElem_take, List.getElem_drop] using hmem,
      by rw [List.getElem?_eq_getElem (by omega), Option.getD_some]⟩

private theorem sweepConeOk_add_cl_pair {c : FullCfg} {F_cur : List (List Nat)}
    {s : FullState} {root_v nv nc : Nat} {l0 l1 : BitVec 32} {scr' : List (BitVec 32)}
    (hlen : s.LengthsOk c) (hcap : 1152 ≤ c.scratch_cap)
    (hc : SweepConeOk F_cur s root_v nv nc) (hnc_lt : nc < 64)
    (hsum : s.scratch.res_sz.toNat + 2 ≤ 1024) (hl0 : l0.toNat < 2 * nv) (hl1 : l1.toNat < 2 * nv)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [coneLift s.scratch.work_stk1 l0.toNat, coneLift s.scratch.work_stk1 l1.toNat]))
    (hslen : scr'.length = c.scratch_cap)
    (hhold : ∀ i < c.scratch_cap, i ≠ nc → i ≠ 64 + nc →
      ¬ (s.scratch.res_sz.toNat ≤ i ∧ i < s.scratch.res_sz.toNat + 2) →
      scr'[i]? = s.scratch.scratch_buf[i]?)
    (h0 : scr'[nc]? = some (BitVec.ofNat 32 s.scratch.res_sz.toNat))
    (h64 : scr'[64 + nc]? = some 2#32)
    (hcp : ∀ k < 2, scr'[s.scratch.res_sz.toNat + k]? = [l0, l1][k]?) :
    SweepConeOk F_cur { s with scratch := { s.scratch with
        scratch_buf := scr', res_sz := BitVec.ofNat 64 (s.scratch.res_sz.toNat + 2) } }
      root_v nv (nc + 1) :=
  sweepConeOk_add_cl hlen hcap hc hnc_lt hsum (by simp)
    (fun k hk => by rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h0 | rfl
                    · simpa [show k = 0 by omega] using hl0
                    · simpa using hl1)
    (by simpa using hent) hslen hhold h0 h64 hcp

/-- Handles `tmp[1] = l1; nc = (u32)full_sweep_add_cl(h, tmp, 2u, nc)` once `tmp[0] = l0` is stored,
for ALL `c.max_vars ≥ 1` (using `padU32B` when `c.max_vars = 1`). -/
private theorem cone_bin_store1_and_addCl {Γ : Env} {c : FullCfg} {F_cur : List (List Nat)}
    {s0 st : FullState} {root_v : BitVec 32} {nv nc l0 l1 : BitVec 32}
    {aVal : Arg Val i32} {aPtr : Arg Val i64}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    {k : Tup Val [i64] → Expr Val Cont [i64]}
    (hAddCl : ∀ args m Q X, fullSweepAddClSpec args m Q X →
      Γ "full_sweep_add_cl" [i64, i64, i32, i32] [i64] args m Q X)
    (haVal : aVal.val = l1) (haPtr : aPtr.val = c.pTmp + 4#64)
    (hlen : st.LengthsOk c) (hag : AgreesExcept coneMask s0 st) (hcap : 1152 ≤ c.scratch_cap)
    (hcone : SweepConeOk F_cur st root_v.toNat nv.toNat nc.toNat) (hnc_lt : nc.toNat < 64)
    (ht0 : st.core.tmp[0]? = some l0) (hl0 : l0.toNat < 2 * nv.toNat)
    (hl1 : l1.toNat < 2 * nv.toNat)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause [coneLift st.scratch.work_stk1 l0.toNat, coneLift st.scratch.work_stk1 l1.toNat]))
    (hm : (FullMem c st ⋆ R) m)
    (hk : ∀ (nc' : BitVec 64) (st' : FullState) (m' : Mem 64),
      st'.LengthsOk c → AgreesExcept coneMask s0 st' →
      SweepConeOk F_cur st' root_v.toNat nv.toNat (nc'.setWidth 32).toNat →
      st'.scratch.tarjan_mark = st.scratch.tarjan_mark →
      st'.scratch.work_stk1 = st.scratch.work_stk1 →
      (FullMem c st' ⋆ R) m' → wp Γ Q X (k (nc', ())) m') :
    wp Γ Q X
      (Expr.store (t := i32) aVal aPtr
        (Expr.call (as := [i64, i64, i32, i32]) (bs := [i64]) "full_sweep_add_cl"
          (Arg.var c.hdr, Arg.var c.pTmp, Arg.imm 2#32, Arg.var nc, ()) k)) m := by
  have htmp_len := hlen.core_ok.tmp_len_arr
  have hmv_pos : 1 ≤ c.max_vars := by
    have := hcone.1; have := hcone.2.2.1; have := hlen.core_ok.cur_vars_le; omega
  by_cases hmv2 : 2 ≤ c.max_vars
  · have hst1 := FullSweepFwdTactics.store_full_tmp1 (c := c) (s := st) l1 (by omega) hm
    rw [← haVal, ← show aPtr.val = c.pTmp + 4 from haPtr] at hst1
    refine wp_store_sep hst1 fun m2 hm2 => ?_; rw [haVal] at hm2
    let st2 : FullState := { st with core := { st.core with tmp := st.core.tmp.set 1 l1 } }
    have h0 : st.core.tmp[0]'(by omega) = l0 := by
      rw [List.getElem?_eq_getElem (by omega)] at ht0; exact Option.some.inj ht0
    have htmp0 : st2.core.tmp[0]'(by simp [st2, htmp_len]; omega) = l0 := by
      simp [st2, List.getElem_set_ne, h0]
    have htmp1 : st2.core.tmp[1]'(by simp [st2, htmp_len]; omega) = l1 := by
      simp [st2, List.getElem_set_self]
    have htk : st2.core.tmp.take 2 = [l0, l1] := List.ext_getElem
      (by simp [st2, htmp_len]; omega) fun j _ hj2 => by
        rcases (by simp at hj2; omega : j = 0 ∨ j = 1) with rfl | rfl <;>
          simpa [List.getElem_take] using (by first | exact htmp0 | exact htmp1)
    refine full_sweep_cone_call_addCl hAddCl (st := st2) (aSz := Arg.imm 2#32) rfl
      ⟨{ hlen.core_ok with tmp_len_arr := by simp [st2, htmp_len] }, hlen.scratch_ok⟩
      (hag.update _ fun _ => rfl) hcap hcone hnc_lt
      (by simp [st2, htmp_len, show (2#32).toNat = 2 from rfl]; omega)
      (fun j hj => by
        rcases (by simp [show (2#32).toNat = 2 from rfl] at hj; omega : j = 0 ∨ j = 1) with
          rfl | rfl <;> simp [htmp0, htmp1, hl0, hl1])
      (by simpa [show (2#32).toNat = 2 from rfl, htk] using hent) hm2 hk
  · have hmv1 : c.max_vars = 1 := by omega
    have ht_eq : st.core.tmp = [l0] := match h : st.core.tmp with
      | [] => by rw [h] at htmp_len; simp at htmp_len; omega
      | [x] => by rw [h] at ht0; simp at ht0; rw [ht0]
      | _ :: _ :: _ => by rw [h] at htmp_len; simp at htmp_len; omega
    obtain ⟨v1, hmem⟩ := fullMem_focus_tmp2_of_mv1 hmv1 ht_eq hm
    have hsep_tmp : ∀ {A B C D : Mem 64 → Prop} {k : Mem 64},
        (A ⋆ B ⋆ C ⋆ D) k → (C ⋆ (A ⋆ B ⋆ D)) k := fun h => by ecancel
    have hsep_untmp : ∀ {A B C D : Mem 64 → Prop} {k : Mem 64},
        (C ⋆ (A ⋆ B ⋆ D)) k → (A ⋆ B ⋆ C ⋆ D) k := fun h => by ecancel
    have hst1 : storeOk m i32 (c.pTmp + 4#64) ∧
        (array (t := i32) c.pTmp [l0, l1] ⋆ (array64 (c.hdr + 32) (hdrTailWords c st) ⋆
          array (t := i32) c.pScratchBuf st.scratch.scratch_buf ⋆
          (fullSweepAddRestTmp1 c st ⋆ R))) (storeMem m i32 (c.pTmp + 4#64) l1) := by
      simpa [show i32.bytes = 4 from rfl] using
        store_array (t := i32) (i := 1) l1 (by decide) (by simp) (hsep_tmp hmem)
    rw [← haVal, ← haPtr] at hst1
    refine wp_store_sep hst1 fun m2 hm2 => ?_; rw [haVal] at hm2
    have hbuf := hcone.2.2.2.2.1; refine wp_call_of_spec _ k ?_
    simp only [vals, Arg.val_var, Arg.val_imm]
    refine hAddCl (c.hdr, c.pTmp, 2#32, nc, ()) m2 (fun r m' => wp Γ Q X (k r) m') X
      ⟨c, st, [l0, l1], fullSweepAddRestTmp1 c st ⋆ R, rfl, hlen, hcap,
        hbuf.2.2.1, hbuf.2.2.2.1, by simp [show (2#32).toNat = 2 from rfl], hsep_untmp hm2, ?_⟩
    simp only [show (2#32).toNat = 2 from rfl]
    by_cases hfull : 64 ≤ nc.toNat ∨ 1024 < st.scratch.res_sz.toNat + 2
    · rw [ite_eq_left hfull]
      let st' : FullState := { st with core := { st.core with tmp := [l0] } }
      have hnc_id : (nc.setWidth 64).setWidth 32 = nc := by apply BitVec.eq_of_toNat_eq; simp
      exact hk (nc.setWidth 64) st' m2
        ⟨{ hlen.core_ok with tmp_len_arr := by simp [st', hmv1] }, hlen.scratch_ok⟩
        (hag.update _ fun _ => rfl) (by rw [hnc_id]; exact hcone) rfl rfl
        (fullMem_unfocus_tmp2_of_mv1 hmv1 (hsep_untmp hm2))
    · rw [ite_eq_right hfull]; intro scr' m' hslen hhold h0 h64 hcp hm'
      let st' : FullState :=
        { st with
          core := { st.core with tmp := [l0] }
          scratch := { st.scratch with scratch_buf := scr',
                                       res_sz := BitVec.ofNat 64 (st.scratch.res_sz.toNat + 2) } }
      have hcone' : SweepConeOk F_cur st' root_v.toNat nv.toNat (nc.toNat + 1) :=
        sweepConeOk_add_cl_pair hlen hcap hcone hnc_lt (by omega) hl0 hl1 hent hslen hhold h0 h64
          hcp
      have hnc1 : ((BitVec.ofNat 64 (nc.toNat + 1)).setWidth 32).toNat = nc.toNat + 1 := by
        rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      exact hk (BitVec.ofNat 64 (nc.toNat + 1)) st' m'
        ⟨{ hlen.core_ok with tmp_len_arr := by simp [st', hmv1] },
          { hlen.scratch_ok with scratch_buf_len := hslen }⟩
        (hag.update _ fun _ => rfl) (by rw [hnc1]; exact hcone') rfl rfl
        (fullMem_unfocus_tmp2_of_mv1 hmv1 hm')

private theorem coneMask_state_eq {s st : FullState} (hag : AgreesExcept coneMask s st) :
    st = { s with core := { s.core with tmp := st.core.tmp }, scratch := { s.scratch with
      work_stk1 := st.scratch.work_stk1, tarjan_mark := st.scratch.tarjan_mark,
      scratch_buf := st.scratch.scratch_buf, res_sz := st.scratch.res_sz } } := by
  have hc0 := coneMask_core_eq hag
  have hs0 : (coneMask st).scratch = (coneMask s).scratch := congrArg FullState.scratch hag
  cases st with | mk c1 sc1 => cases s with | mk c2 sc2 =>
  dsimp only [coneMask] at hc0 hs0 ⊢; cases sc1; cases sc2; cases hs0; rw [hc0]

private theorem cone_push_var_step {c : FullCfg} {F_cur : List (List Nat)} {s st : FullState}
    {root_v cv qi nv nc v : BitVec 32} (hlen : st.LengthsOk c) (hag : AgreesExcept coneMask s st)
    (hcone : SweepConeOk F_cur st root_v.toNat nv.toNat nc.toNat) (hnv24 : nv.toNat < 24)
    (hqi_lt : qi.toNat < nv.toNat) (hv_lt : v.toNat < s.core.cur_vars)
    (htmk_cv : st.scratch.tarjan_mark[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 qi.toNat)
    (hwk_cv : (st.scratch.work_stk1[qi.toNat]?.getD 0#32).toNat = cv.toNat)
    (hmiss : st.scratch.tarjan_mark[v.toNat]?.getD 0#32 = 0xFFFFFFFF#32) :
    let st' : FullState := { st with scratch := { st.scratch with
      tarjan_mark := st.scratch.tarjan_mark.set v.toNat nv
      work_stk1 := st.scratch.work_stk1.set nv.toNat v } }
    nv.toNat < c.max_vars ∧ (nv + 1#32).toNat = nv.toNat + 1 ∧ st'.LengthsOk c ∧
    AgreesExcept coneMask s st' ∧ SweepConeOk F_cur st' root_v.toNat (nv + 1#32).toNat nc.toNat ∧
    st'.scratch.tarjan_mark[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 qi.toNat ∧
    (st'.scratch.work_stk1[qi.toNat]?.getD 0#32).toNat = cv.toNat ∧
    st'.scratch.tarjan_mark[v.toNat]?.getD 0#32 ≠ 0xFFFFFFFF#32 ∧
    (∀ j < nv.toNat, st'.scratch.work_stk1[j]? = st.scratch.work_stk1[j]?) := by
  have hcv_st := hag.get (·.core.cur_vars); have hcv_le := hlen.core_ok.cur_vars_le
  have hpush := sweepConeOk_push_var hlen hcone hnv24 (by rw [hcv_st]; exact hv_lt) hmiss
  have htm_len := hlen.scratch_ok.tarjan_mark_len; have hwk_len := hlen.scratch_ok.work_stk1_len
  have hnv1 : (nv + 1#32).toNat = nv.toNat + 1 := by
    rw [BitVec.toNat_add, show (1#32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
  have hne_cv : cv.toNat ≠ v.toNat := fun heq => by
    rw [← heq, htmk_cv] at hmiss; have := congrArg BitVec.toNat hmiss
    simp [BitVec.toNat_ofNat] at this; omega
  refine ⟨by omega, hnv1, ⟨hlen.core_ok, { hlen.scratch_ok with
      tarjan_mark_len := by simp [htm_len], work_stk1_len := by simp [hwk_len] }⟩,
    hag.update _ fun _ => rfl, ?_, ?_, ?_, ?_, fun j hj => List.getElem?_set_ne (by omega)⟩
  · rw [hnv1]; simpa [bv_ofNat_toNat_eq] using hpush.2
  · rw [List.getElem?_set_ne (Ne.symm hne_cv)]; exact htmk_cv
  · rw [List.getElem?_set_ne (by omega)]; exact hwk_cv
  · rw [List.getElem?_set_self (by omega), Option.getD_some]
    intro heq; have := congrArg BitVec.toNat heq; simp at this; omega

private theorem cone_bin_lits_ok {st : FullState}
    {cv qi pol lit ot ov nv : BitVec 32} {iov : Nat}
    (hqi_lt : qi.toNat < nv.toNat) (hnv24 : nv.toNat ≤ 24) (hpol_lt : pol.toNat < 2)
    (hlit_eq : lit.toNat = 2 * cv.toNat + pol.toNat) (hov_eq : ov.toNat = ot.toNat / 2)
    (hiov : iov < nv.toNat)
    (htca : st.scratch.tarjan_mark[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 qi.toNat)
    (hwca : (st.scratch.work_stk1[qi.toNat]?.getD 0#32).toNat = cv.toNat)
    (htov : st.scratch.tarjan_mark[ov.toNat]?.getD 0#32 = BitVec.ofNat 32 iov)
    (hwov : (st.scratch.work_stk1[iov]?.getD 0#32).toNat = ov.toNat) :
    let l0 := ((st.scratch.tarjan_mark[cv.toNat]?.getD 0#32) <<< (1 : Nat)) ||| pol
    let l1 := ((st.scratch.tarjan_mark[ov.toNat]?.getD 0#32) <<< (1 : Nat)) ||| (ot &&& 1#32)
    l0.toNat < 2 * nv.toNat ∧ l1.toNat < 2 * nv.toNat ∧
    coneLift st.scratch.work_stk1 l0.toNat = lit.toNat ∧
    coneLift st.scratch.work_stk1 l1.toNat = ot.toNat := by
  intro l0 l1
  have hl0 : l0.toNat = 2 * qi.toNat + pol.toNat := by
    dsimp only [l0]; rw [htca]
    have := bv32_shl1_or_pol (BitVec.ofNat 32 qi.toNat) pol
      (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega) hpol_lt
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : qi.toNat < 2 ^ 32)] using this
  have hl1 : l1.toNat = 2 * iov + ot.toNat % 2 := by
    dsimp only [l1]; rw [htov]
    have := bv32_shl1_or_and1 (BitVec.ofNat 32 iov) ot
      (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : iov < 2 ^ 32)] using this
  refine ⟨by omega, by omega, ?_, by rw [hl1]; exact coneLift_of_tmk_pair hwov hov_eq.symm⟩
  rw [hl0]; simpa [show lit.toNat % 2 = pol.toNat by omega] using
    coneLift_of_tmk_pair (wk := st.scratch.work_stk1) (idx := qi.toNat) (v := cv.toNat)
      (l := lit.toNat) hwca (by omega)

private theorem cone_occ_hdr_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s st_w : FullState} {cr sz : BitVec 32} (hlen : s.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur s.core) (hnd : FullArenaVarsNodup s)
    (har_eq : st_w.core.arena = s.core.arena) (hcr_ref : cr.toNat ∈ fullArenaClauseRefsCore s.core)
    (hsz_core : sz.toNat = fullArenaClauseSizeCore s.core cr.toNat)
    (hgr0 : (st_w.core.arena[cr.toNat]'(by
      have := (hw.arena.refs_wf cr.toNat hcr_ref).1; have := hlen.core_ok.arena_len_le
      rw [har_eq, hlen.core_ok.arena_len_arr]; omega) &&& (0x00080000#32 ||| 0x00400000#32)) =
      0#32) :
    fullArenaClauseGarbCore s.core cr.toNat = false ∧
    cr.toNat + 3 + sz.toNat ≤ s.core.arena_len ∧ sz.toNat ≤ s.core.cur_vars ∧
    cr.toNat + 3 + sz.toNat ≤ s.core.arena.length := by
  have hwf := hw.arena.refs_wf cr.toNat hcr_ref
  have hal := hlen.core_ok.arena_len_le; have har := hlen.core_ok.arena_len_arr
  have hng : fullArenaClauseGarbCore s.core cr.toNat = false := by
    unfold fullArenaClauseGarbCore fullArenaHdrCore
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    have h0 := bv32_garb_false_of_and_garb_red hgr0; simp [har_eq] at h0; simp [h0]
  have hsz_le : cr.toNat + 3 + sz.toNat ≤ s.core.arena_len := by have := hwf.2.2; omega
  have hsz_cv : sz.toNat ≤ s.core.cur_vars := by
    have hlen_lits : (fullArenaClauseLits s cr.toNat).length = sz.toNat := by
      unfold fullArenaClauseLits fullArenaClauseLitsCore
      rw [List.length_map, List.length_take, List.length_drop, ← hsz_core]
      exact Nat.min_eq_left (by omega)
    rw [← hlen_lits]
    have hle := nodup_length_le_of_lt (xs := (fullArenaClauseLits s cr.toNat).map (· / 2))
      (n := s.core.cur_vars) (hnd cr.toNat hcr_ref hng) fun v hv => by
        rcases List.mem_map.mp hv with ⟨l, hl, rfl⟩
        have := hw.arena.lits_lt cr.toNat hcr_ref hng l hl; omega
    simpa [List.length_map] using hle
  exact ⟨hng, hsz_le, hsz_cv, by omega⟩

private theorem cone_k_unassigned_step {c : FullCfg}
    {s st_k st_u : FullState} {cr sz k cnt nv_k nv_u lit_k : BitVec 32} {ilv : Nat}
    (hlu : st_u.LengthsOk c) (htmpu_eq : st_u.core.tmp = st_k.core.tmp)
    (hwku_eq : ∀ j < nv_k.toNat, st_u.scratch.work_stk1[j]? = st_k.scratch.work_stk1[j]?)
    (hnvku : nv_k.toNat ≤ nv_u.toNat) (hnvu24 : nv_u.toNat ≤ 24)
    (hk_lt : k.toNat < sz.toNat) (hsz_le6 : sz.toNat ≤ 6) (hsz_cv : sz.toNat ≤ s.core.cur_vars)
    (hcv_le : s.core.cur_vars ≤ c.max_vars) (hcnt_le : cnt.toNat ≤ k.toNat)
    (hlit_ar : (s.core.arena[cr.toNat + 3 + k.toNat]?.getD 0#32).toNat = lit_k.toNat)
    (hilv : ilv < nv_u.toNat)
    (hwlv : (st_u.scratch.work_stk1[ilv]?.getD 0#32).toNat = lit_k.toNat / 2)
    (htlv_v : st_u.scratch.tarjan_mark[lit_k.toNat / 2]?.getD 0#32 = BitVec.ofNat 32 ilv)
    (hlts_k : ∀ j < cnt.toNat, (st_k.core.tmp[j]?.getD 0#32).toNat < 2 * nv_k.toNat)
    (hcov_k : ∀ i < k.toNat,
      let l := (s.core.arena[cr.toNat + 3 + i]?.getD 0#32).toNat
      s.core.vals[l]?.getD 0#8 = 0xFF#8 ∨
      l ∈ (st_k.core.tmp.take cnt.toNat).map (fun x => coneLift st_k.scratch.work_stk1 x.toNat)) :
    let new_l : BitVec 32 :=
      ((st_u.scratch.tarjan_mark[lit_k.toNat / 2]?.getD 0#32) <<< (1 : Nat)) ||| (lit_k &&& 1#32)
    let st_u' : FullState :=
      { st_u with core := { st_u.core with tmp := st_u.core.tmp.set cnt.toNat new_l } }
    (cnt + 1#32).toNat = cnt.toNat + 1 ∧ st_u'.LengthsOk c ∧
    (∀ j < (cnt + 1#32).toNat, (st_u'.core.tmp[j]?.getD 0#32).toNat < 2 * nv_u.toNat) ∧
    (∀ i < (k + 1#32).toNat,
      let l := (s.core.arena[cr.toNat + 3 + i]?.getD 0#32).toNat
      s.core.vals[l]?.getD 0#8 = 0xFF#8 ∨
      l ∈ (st_u'.core.tmp.take (cnt + 1#32).toNat).map
        (fun x => coneLift st_u.scratch.work_stk1 x.toNat)) := by
  intro new_l st_u'
  have htmp_u := hlu.core_ok.tmp_len_arr
  have htmp_k : st_k.core.tmp.length = c.max_vars := htmpu_eq ▸ htmp_u
  have hcnt1 : (cnt + 1#32).toNat = cnt.toNat + 1 := by
    rw [BitVec.toNat_add, show (1#32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
  have hk1 : (k + 1#32).toNat = k.toNat + 1 := by
    rw [BitVec.toNat_add, show (1#32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
  have hnew_n : new_l.toNat = 2 * ilv + lit_k.toNat % 2 := by
    simp only [new_l, htlv_v]
    have := bv32_shl1_or_and1 (BitVec.ofNat 32 ilv) lit_k
      (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : ilv < 2 ^ 32)] using this
  have hnew_lift : coneLift st_u.scratch.work_stk1 new_l.toNat = lit_k.toNat := by
    rw [hnew_n]; exact coneLift_of_tmk_pair hwlv rfl
  have htake_u' : st_u'.core.tmp.take (cnt + 1#32).toNat =
      st_u.core.tmp.take cnt.toNat ++ [new_l] := by
    have hlen_tk : (st_u.core.tmp.take cnt.toNat).length = cnt.toNat := by simp [htmp_u]; omega
    rw [hcnt1]; dsimp only [st_u']; apply List.ext_getElem; · simp [htmp_u]; omega
    intro j hj1 _; have hj : j < cnt.toNat + 1 := by simp [htmp_u] at hj1; omega
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · rw [List.getElem_take, List.getElem_set_ne (by omega : cnt.toNat ≠ j),
        List.getElem_append_left (by omega), List.getElem_take]
    · simp [List.getElem_take, List.getElem_set_self, List.getElem_append_right, hlen_tk]
  refine ⟨hcnt1, ⟨{ hlu.core_ok with tmp_len_arr := by simp [st_u', htmp_u] }, hlu.scratch_ok⟩,
    fun j hj => ?_, fun i hi => ?_⟩
  · rw [hcnt1] at hj; rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
    · dsimp only [st_u']; rw [List.getElem?_set_ne (by omega : cnt.toNat ≠ j), htmpu_eq]
      have := hlts_k j hlt; omega
    · dsimp only [st_u']; rw [List.getElem?_set_self (by omega), Option.getD_some]; omega
  · rw [hk1] at hi; rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
    · rcases hcov_k i hlt with hfals | hmem; · exact Or.inl hfals
      right; rw [htake_u', List.map_append]; apply List.mem_append_left
      rcases List.mem_map.mp hmem with ⟨x, hx, heq_l⟩
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
      have hj_cnt : j < cnt.toNat := by simp at hj; omega
      have hx_lt := hlts_k j hj_cnt
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at hx_lt
      have hwk_eq_x : st_u.scratch.work_stk1[(st_k.core.tmp[j]'(by omega)).toNat / 2]? =
          st_k.scratch.work_stk1[(st_k.core.tmp[j]'(by omega)).toNat / 2]? := hwku_eq _ (by omega)
      refine List.mem_map.mpr ⟨st_u.core.tmp[j]'(by omega), ?_, ?_⟩
      · have hmem' : (st_u.core.tmp.take cnt.toNat)[j]'(by simp [htmp_u]; omega) ∈
            st_u.core.tmp.take cnt.toNat := List.getElem_mem _
        simpa [List.getElem_take] using hmem'
      · rw [← heq_l]; simp only [List.getElem_take, coneLift, htmpu_eq, hwk_eq_x]
    · right; rw [htake_u', List.map_append]; apply List.mem_append_right; simp [hlit_ar, hnew_lift]

private theorem cone_k_unassigned_wp {Γ : Env} {c : FullCfg} {F_cur : List (List Nat)}
    {s st_k : FullState} {root_v cv qi nv nc_w cr sz nv_k cnt k lit_v : BitVec 32}
    {R : Mem 64 → Prop} {mk : Mem 64} {Q : Post [i64]} {X : XPost}
    {J_ke : Cont [i32, .bool, i32, i32]} {J_jn : Cont [i32, .bool, i32]}
    {J_k : Cont [i32, i32, i32]}
    (hJ_ke : ∀ (xs : Tup Val [i32, .bool, i32, i32]) (m : Mem 64),
      (match xs with
      | (nv_ke, sat_e, cnt_e, _, ()) =>
        cnt_e.toNat ≤ sz.toNat ∧ nv.toNat ≤ nv_ke.toNat ∧ ∃ st_ke : FullState,
          st_ke.LengthsOk c ∧ AgreesExcept coneMask s st_ke ∧
          SweepConeOk F_cur st_ke root_v.toNat nv_ke.toNat nc_w.toNat ∧
          st_ke.scratch.tarjan_mark[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 qi.toNat ∧
          (st_ke.scratch.work_stk1[qi.toNat]?.getD 0#32).toNat = cv.toNat ∧
          (sat_e = false →
            (∀ j < cnt_e.toNat, (st_ke.core.tmp[j]?.getD 0#32).toNat < 2 * nv_ke.toNat) ∧
            ∀ i < sz.toNat,
              let l := (s.core.arena[cr.toNat + 3 + i]?.getD 0#32).toNat
              s.core.vals[l]?.getD 0#8 = 0xFF#8 ∨
              l ∈ (st_ke.core.tmp.take cnt_e.toNat).map
                (fun x => coneLift st_ke.scratch.work_stk1 x.toNat)) ∧
          (FullMem c st_ke ⋆ R) m) → J_ke xs m)
    (hJ_jn : ∀ (xs : Tup Val [i32, .bool, i32]) (m' : Mem 64),
      wp Γ Q X ((Blocks.cons (fun (p : Tup Val [i32, .bool, i32]) =>
        Expr.let_ (Op.mk (.add i32) (Arg.var k, Arg.imm 1, ())) fun p_1 =>
          Expr.jump J_k (Arg.var p.fst, Arg.var p.snd.snd.fst, Arg.var p_1.fst, ()))
        Blocks.nil).get Member.here xs) m' → J_jn xs m')
    (hJ_k : ∀ (ys : Tup Val [i32, i32, i32]) (m' : Mem 64),
      ((match ys with | (_, _, k', ()) => sz.toNat - k'.toNat) < sz.toNat - k.toNat) →
      (match ys with
      | (nv_k, cnt, k, ()) =>
        k.toNat ≤ sz.toNat ∧ cnt.toNat ≤ k.toNat ∧ nv.toNat ≤ nv_k.toNat ∧ ∃ st_k : FullState,
          st_k.LengthsOk c ∧ AgreesExcept coneMask s st_k ∧
          SweepConeOk F_cur st_k root_v.toNat nv_k.toNat nc_w.toNat ∧
          st_k.scratch.tarjan_mark[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 qi.toNat ∧
          (st_k.scratch.work_stk1[qi.toNat]?.getD 0#32).toNat = cv.toNat ∧
          (∀ j < cnt.toNat, (st_k.core.tmp[j]?.getD 0#32).toNat < 2 * nv_k.toNat) ∧
          (∀ i < k.toNat,
            let l := (s.core.arena[cr.toNat + 3 + i]?.getD 0#32).toNat
            s.core.vals[l]?.getD 0#8 = 0xFF#8 ∨
            l ∈ (st_k.core.tmp.take cnt.toNat).map
              (fun x => coneLift st_k.scratch.work_stk1 x.toNat)) ∧
          (FullMem c st_k ⋆ R) m') → J_k ys m')
    (hcv_le : s.core.cur_vars ≤ c.max_vars) (hqi_lt : qi.toNat < nv.toNat)
    (hsz_le6 : sz.toNat ≤ 6) (hsz_cv : sz.toNat ≤ s.core.cur_vars)
    (hk_lt : k.toNat < sz.toNat) (hcnt_le : cnt.toNat ≤ k.toNat)
    (hnv_k_mono : nv.toNat ≤ nv_k.toNat)
    (hlen_k : st_k.LengthsOk c) (hag_k : AgreesExcept coneMask s st_k)
    (hcone_k : SweepConeOk F_cur st_k root_v.toNat nv_k.toNat nc_w.toNat)
    (htmk_k : st_k.scratch.tarjan_mark[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 qi.toNat)
    (hwk_k : (st_k.scratch.work_stk1[qi.toNat]?.getD 0#32).toNat = cv.toNat)
    (hlts_k : ∀ j < cnt.toNat, (st_k.core.tmp[j]?.getD 0#32).toNat < 2 * nv_k.toNat)
    (hcov_k : ∀ i < k.toNat, let l := (s.core.arena[cr.toNat + 3 + i]?.getD 0#32).toNat
      s.core.vals[l]?.getD 0#8 = 0xFF#8 ∨
      l ∈ (st_k.core.tmp.take cnt.toNat).map (fun x => coneLift st_k.scratch.work_stk1 x.toNat))
    (hlit_lt : lit_v.toNat < 2 * s.core.cur_vars)
    (hlit_ar : (s.core.arena[cr.toNat + 3 + k.toNat]?.getD 0#32).toNat = lit_v.toNat)
    (hmk : (FullMem c st_k ⋆ R) mk) :
    wp Γ Q X
      (Expr.let_ (Op.mk (.lshr i32) (Arg.var lit_v, Arg.imm 1, ())) fun p_1 =>
        Expr.group (fun _ => Blocks.cons (fun (p_2 : Tup Val [i32]) =>
          Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_1.fst, ())) fun p_3 =>
          Expr.let_ (Op.mk (.mul i64) (Arg.var p_3.fst, Arg.imm 4, ())) fun p_4 =>
          Expr.let_ (Op.mk (.add i64) (Arg.var c.pTarjanMark, Arg.var p_4.fst, ())) fun p_5 =>
          Expr.load i32 (Arg.var p_5.fst) fun ld =>
          Expr.let_ (Op.mk (.cmp .eq i32 .bool rfl) (Arg.var ld, Arg.imm 4294967295, ()))
            fun p_6 =>
          Expr.jnz (Arg.var p_6.fst)
            (Expr.jump J_ke (Arg.var p_2.fst, Arg.imm true, Arg.var cnt, Arg.var k, ()))
            (Expr.let_ (Op.mk (.zext 32 64) (Arg.var cnt, ())) fun p_7 =>
             Expr.let_ (Op.mk (.mul i64) (Arg.var p_7.fst, Arg.imm 4, ())) fun p_8 =>
             Expr.let_ (Op.mk (.add i64) (Arg.var c.pTmp, Arg.var p_8.fst, ())) fun p_9 =>
             Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_1.fst, ())) fun p_10 =>
             Expr.let_ (Op.mk (.mul i64) (Arg.var p_10.fst, Arg.imm 4, ())) fun p_11 =>
             Expr.let_ (Op.mk (.add i64) (Arg.var c.pTarjanMark, Arg.var p_11.fst, ())) fun p_12 =>
             Expr.load i32 (Arg.var p_12.fst) fun ld =>
             Expr.let_ (Op.mk (.shl i32) (Arg.var ld, Arg.imm 1, ())) fun p_13 =>
             Expr.let_ (Op.mk (.and i32) (Arg.var lit_v, Arg.imm 1, ())) fun p =>
             Expr.let_ (Op.mk (.or i32) (Arg.var p_13.fst, Arg.var p.fst, ())) fun p =>
             Expr.store (t := i32) (Arg.var p.fst) (Arg.var p_9.fst)
               (Expr.let_ (Op.mk (.add i32) (Arg.var cnt, Arg.imm 1, ())) fun p =>
                Expr.jump J_jn (Arg.var p_2.fst, Arg.imm false, Arg.var p.fst, ())))) Blocks.nil)
        fun Js =>
          Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_1.fst, ())) fun p =>
          Expr.let_ (Op.mk (.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
          Expr.let_ (Op.mk (.add i64) (Arg.var c.pTarjanMark, Arg.var p.fst, ())) fun p =>
          Expr.load i32 (Arg.var p.fst) fun ld =>
          Expr.let_ (Op.mk (.cmp .eq i32 .bool rfl) (Arg.var ld, Arg.imm 4294967295, ()))
            fun p =>
          Expr.jnz (Arg.var p.fst)
            (Expr.let_ (Op.mk (.cmp .ult i32 .bool rfl) (Arg.var nv_k, Arg.imm 24, ())) fun p =>
             Expr.jnz (Arg.var p.fst)
               (Expr.let_ (Op.mk (.zext 32 64) (Arg.var p_1.fst, ())) fun p =>
                Expr.let_ (Op.mk (.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
                Expr.let_ (Op.mk (.add i64) (Arg.var c.pTarjanMark, Arg.var p.fst, ())) fun p =>
                Expr.store (t := i32) (Arg.var nv_k) (Arg.var p.fst)
                  (Expr.let_ (Op.mk (.zext 32 64) (Arg.var nv_k, ())) fun p =>
                   Expr.let_ (Op.mk (.mul i64) (Arg.var p.fst, Arg.imm 4, ())) fun p =>
                   Expr.let_ (Op.mk (.add i64) (Arg.var c.pWorkStk1, Arg.var p.fst, ())) fun p =>
                   Expr.store (t := i32) (Arg.var p_1.fst) (Arg.var p.fst)
                     (Expr.let_ (Op.mk (.add i32) (Arg.var nv_k, Arg.imm 1, ())) fun p =>
                      Expr.jump Js.fst (Arg.var p.fst, ()))))
               (Expr.jump Js.fst (Arg.var nv_k, ())))
            (Expr.jump Js.fst (Arg.var nv_k, ()))) mk := by
  have hcv_k := hag_k.get (·.core.cur_vars); have htm_k := hlen_k.scratch_ok.tarjan_mark_len
  have hwk_k_len := hlen_k.scratch_ok.work_stk1_len; have htmp_k := hlen_k.core_ok.tmp_len_arr
  have hlv_eq : (lit_v >>> (1 : Nat)).toNat = lit_v.toNat / 2 := bv32_shr1_toNat lit_v
  have hlv_lt : (lit_v >>> (1 : Nat)).toNat < s.core.cur_vars := by omega
  sw_fast
  refine wp_join_group (ts := [i32])
    (fun (nv_u, ()) m_u => nv.toNat ≤ nv_u.toNat ∧ ∃ st_u : FullState,
      st_u.LengthsOk c ∧ AgreesExcept coneMask s st_u ∧
      SweepConeOk F_cur st_u root_v.toNat nv_u.toNat nc_w.toNat ∧
      st_u.scratch.tarjan_mark[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 qi.toNat ∧
      (st_u.scratch.work_stk1[qi.toNat]?.getD 0#32).toNat = cv.toNat ∧
      st_u.core.tmp = st_k.core.tmp ∧
      (∀ j < nv_k.toNat, st_u.scratch.work_stk1[j]? = st_k.scratch.work_stk1[j]?) ∧
      nv_k.toNat ≤ nv_u.toNat ∧ (FullMem c st_u ⋆ R) m_u) ?_ ?_
  · rintro _ ⟨nv_u, ⟨⟩⟩ m_u ⟨hnvu, st_u, hlu, hau, hcu, htu, hwu, htmpu_eq, hwku_eq, hnvku, hmu⟩
    clear hmk hlen_k hag_k hcone_k htmk_k hwk_k
    have htm_u := hlu.scratch_ok.tarjan_mark_len; have htmp_u := hlu.core_ok.tmp_len_arr
    have hcv_u := hau.get (·.core.cur_vars); sw_fast; sw_split
    · sw_fast; exact hJ_ke (nv_u, true, cnt, k, ()) m_u
        ⟨Nat.le_trans hcnt_le (Nat.le_of_lt hk_lt), hnvu, st_u, hlu, hau, hcu, htu,
          hwu, fun hf => Bool.noConfusion hf, hmu⟩
    have hlv_tm : (lit_v >>> (1 : Nat)).toNat < st_u.scratch.tarjan_mark.length := by omega
    have hne_lv : st_u.scratch.tarjan_mark[(lit_v >>> (1 : Nat)).toNat]?.getD 0#32 ≠
        0xFFFFFFFF#32 := by rw [List.getElem?_eq_getElem hlv_tm, Option.getD_some]; sw_bd
    rcases hcu.2.2.2.2.2.2.2.1 (lit_v >>> (1 : Nat)).toNat (by rw [hcv_u]; exact hlv_lt) with
      hff | ⟨ilv, hilv, hwlv, htlv⟩
    · exact absurd hff hne_lv
    sw_fast
    obtain ⟨hcnt1, hlen_u', hlts_u', hcov_u'⟩ :=
      cone_k_unassigned_step hlu htmpu_eq hwku_eq hnvku hcu.2.1 hk_lt hsz_le6 hsz_cv
        hcv_le hcnt_le hlit_ar hilv (hlv_eq ▸ hwlv) (hlv_eq ▸ htlv) hlts_k hcov_k
    have hk1 : (k + 1#32).toNat = k.toNat + 1 := by
      rw [BitVec.toNat_add, show (1#32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
    have htm_get : st_u.scratch.tarjan_mark[lit_v.toNat / 2]?.getD 0#32 =
        st_u.scratch.tarjan_mark[(lit_v >>> (1 : Nat)).toNat]'hlv_tm := by
      rw [← hlv_eq, List.getElem?_eq_getElem hlv_tm, Option.getD_some]
    have hm_u' : (FullMem c { st_u with
        core := { st_u.core with
          tmp := st_u.core.tmp.set cnt.toNat
            (((st_u.scratch.tarjan_mark[lit_v.toNat / 2]?.getD 0#32) <<< (1 : Nat)) |||
              (lit_v &&& 1#32)) } } ⋆ R) m := by
      rw [htm_get, show (1#32 : BitVec 32) = 1 from rfl]
      simpa only [bv32_zext64_eq, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by have := cnt.isLt; omega : cnt.toNat < 2 ^ 64),
        Nat.mod_eq_of_lt (by have := (lit_v >>> (1 : Nat)).isLt; omega :
          (lit_v >>> (1 : Nat)).toNat < 2 ^ 64)] using hm
    exact hJ_k (nv_u, cnt + 1#32, k + 1#32, ()) m (by dsimp only; omega)
      ⟨by omega, by omega, hnvu, _, hlen_u', hau.update _ (fun _ => rfl), hcu, htu,
        hwu, hlts_u', hcov_u', hm_u'⟩
  intro J_u hJ_u; sw_split; rotate_left
  · sw_fast; exact hJ_u (nv_k, ()) mk ⟨hnv_k_mono, st_k, hlen_k, hag_k, hcone_k, htmk_k,
      hwk_k, rfl, fun _ _ => rfl, Nat.le_refl _, hmk⟩
  have hmiss_lv : st_k.scratch.tarjan_mark[(lit_v >>> (1 : Nat)).toNat]?.getD 0#32 =
      0xFFFFFFFF#32 := by rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; sw_bd
  sw_split; rotate_left
  · sw_fast; exact hJ_u (nv_k, ()) mk ⟨hnv_k_mono, st_k, hlen_k, hag_k, hcone_k, htmk_k,
      hwk_k, rfl, fun _ _ => rfl, Nat.le_refl _, hmk⟩
  have hnv_k_24 : nv_k.toNat < 24 := by sw_bd
  have hnv_k_lt : nv_k.toNat < s.core.cur_vars := by
    rw [← hcv_k]
    exact (sweepConeOk_push_var hlen_k hcone_k hnv_k_24 (by rw [hcv_k]; exact hlv_lt) hmiss_lv).1
  sw_fast
  obtain ⟨_, hnvk1, hlen_u, hag_u, hcu, htu, hwu, _, hwku_eq⟩ :=
    cone_push_var_step hlen_k hag_k hcone_k hnv_k_24 (by omega) hlv_lt htmk_k hwk_k hmiss_lv
  have hm_u : (FullMem c { st_k with scratch := { st_k.scratch with
      tarjan_mark := st_k.scratch.tarjan_mark.set (lit_v >>> (1 : Nat)).toNat nv_k
      work_stk1 := st_k.scratch.work_stk1.set nv_k.toNat (lit_v >>> (1 : Nat)) } } ⋆ R) m := by
    simpa only [bv32_zext64_eq, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : nv_k.toNat < 2 ^ 64),
      Nat.mod_eq_of_lt (by have := (lit_v >>> (1 : Nat)).isLt; omega :
        (lit_v >>> (1 : Nat)).toNat < 2 ^ 64)] using hm
  exact hJ_u (nv_k + 1#32, ()) m
    ⟨by omega, _, hlen_u, hag_u, hcu, htu, hwu, rfl, hwku_eq, by omega, hm_u⟩

/-! ## 2. `full_sweep_cone_wp` (`Full.lean` #12) -/

theorem full_sweep_cone_wp (Γ : Env)
    (hAddCl : ∀ args m Q X, fullSweepAddClSpec args m Q X →
      Γ "full_sweep_add_cl" [i64, i64, i32, i32] [i64] args m Q X) :
    ∀ args m Q X, fullSweepConeSpec args m Q X → Func.wp Γ full_sweep_cone_body args m Q X := by
  rintro ⟨h, root_v, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, ⟨hlen, hw, hlm, hnd, hext, hcl0, hdm⟩, hcap, hroot, htmk, hm, hQ⟩
  have hcv_le := hlen.core_ok.cur_vars_le
  have hwk_len := hlen.scratch_ok.work_stk1_len; have htm_len := hlen.scratch_ok.tarjan_mark_len
  have hdw : DenseWatchesInv F_cur s.core := by
    have hmw := hw.watches; unfold ModeWatchesInv at hmw; simp only [hdm, ↓reduceIte] at hmw
    exact hmw
  unfold Func.wp full_sweep_cone_body; dsimp only; sw_fast
  -- Outer loop: `while (qi < nv && nv < 24u && nc < 64u)`
  refine wp_loop_inv (ts := [i32, i32, i32])
    (fun (nv, nc, qi, ()) mo =>
      qi.toNat ≤ nv.toNat ∧ ∃ st : FullState, st.LengthsOk c ∧ AgreesExcept coneMask s st ∧
        SweepConeOk F_cur st root_v.toNat nv.toNat nc.toNat ∧ (FullMem c st ⋆ R) mo)
    (fun (nv, _, qi, ()) _ => 24 - qi.toNat) ?_ ?_
  · intro J_out hJ_out; sw_fast
    have ⟨hlen1, hag1, hcone1⟩ := full_sweep_cone_init_ok (F_cur := F_cur) hlen hroot htmk
    exact hJ_out (1#32, 0#32, 0#32, ()) _ ⟨Nat.zero_le _, _, hlen1, hag1, hcone1, by assumption⟩
  · intro J_out; rintro ⟨nv, nc, qi, ⟨⟩⟩ mo ⟨hqi_le, st, hlen_st, hag_st, hcone_st, hmo⟩ hJ_out
    sw_fast
    refine wp_join_group (ts := [])
      (fun () m_ex => ∃ st_e : FullState, st_e.LengthsOk c ∧ AgreesExcept coneMask s st_e ∧
        SweepConeOk F_cur st_e root_v.toNat nv.toNat nc.toNat ∧ (FullMem c st_e ⋆ R) m_ex)
      ?_ ?_
    · rintro _ ⟨⟩ m_ex ⟨st_e, hlen_e, hag_e, hcone_e, hm_e⟩; sw_fast
      have hpk := bv64_pack_toNat nv nc hcone_e.2.1 hcone_e.2.2.2.1
      have hdense := coneMask_preserves_dense hag_e hw hlm hnd hext hcl0
      have hQ' := hQ (nv.setWidth 64 ||| (nc.setWidth 64 <<< (16 : Nat))) st_e.core.tmp
        st_e.scratch.work_stk1 st_e.scratch.tarjan_mark st_e.scratch.scratch_buf
        st_e.scratch.res_sz m_ex
      rw [← coneMask_state_eq hag_e, hpk.1, hpk.2] at hQ'
      refine hQ' ⟨hlen_e, hdense.1, hdense.2.1, hdense.2.2.1, hdense.2.2.2.1, hdense.2.2.2.2.1,
        hdense.2.2.2.2.2.1 ▸ hdm⟩ hcone_e.1 (sweepConeOk_to_fullSweepConeOk hlen_e hcap hcone_e)
        ?_ ?_ hm_e
      · rw [hcone_e.2.2.2.2.2.1, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by have := root_v.isLt; omega)]
      · intro v hv hne
        rcases hcone_e.2.2.2.2.2.2.2.1 v (by rw [hdense.2.2.2.2.2.2.1]; exact hv) with
          hff | ⟨i, hi, hwi, _⟩
        · exact absurd hff hne
        · exact ⟨i, hi, hwi⟩
    intro J_ex hJ_ex; clear hQ hlm hext hdm htmk hroot hm
    sw_split; rotate_left; · sw_fast; exact hJ_ex () mo ⟨st, hlen_st, hag_st, hcone_st, hmo⟩
    have hqi_lt : qi.toNat < nv.toNat := by sw_bd
    sw_split; rotate_left; · sw_fast; exact hJ_ex () mo ⟨st, hlen_st, hag_st, hcone_st, hmo⟩
    have hnv_lt24 : nv.toNat < 24 := by sw_bd
    sw_split; rotate_left; · sw_fast; exact hJ_ex () mo ⟨st, hlen_st, hag_st, hcone_st, hmo⟩
    have hnc_lt64 : nc.toNat < 64 := by sw_bd
    have hwk_st := hlen_st.scratch_ok.work_stk1_len
    have hnv_cv : nv.toNat ≤ s.core.cur_vars := by
      have hc0 := hag_st.get (·.core.cur_vars); have := hcone_st.2.2.1; omega
    sw_fast; have hqi_z : (qi.setWidth 64).toNat = qi.toNat := by simp only [bv_c0]
    generalize hcv_eq : st.scratch.work_stk1[(qi.setWidth 64).toNat]'(by omega) = cv
    have hwk_qi : st.scratch.work_stk1[qi.toNat]?.getD 0#32 = cv := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some, ← hcv_eq]; simp [hqi_z]
    have hcv_lt_s : cv.toNat < s.core.cur_vars := by
      have hf := (hcone_st.2.2.2.2.2.2.1 qi.toNat hqi_lt).1
      rw [hwk_qi, hag_st.get (·.core.cur_vars)] at hf; exact hf
    have hcv_idx : st.scratch.tarjan_mark[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 qi.toNat := by
      have hf := (hcone_st.2.2.2.2.2.2.1 qi.toNat hqi_lt).2; rw [hwk_qi] at hf; exact hf
    have hqi1 : (qi + 1#32).toNat = qi.toNat + 1 := by
      rw [BitVec.toNat_add, show (1#32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
    -- `pol` loop: `while (pol < 2u && nc < 64u)`
    refine wp_loop_inv (ts := [i32, i32, i32])
      (fun (nv_p, nc_p, pol, ()) mp =>
        pol.toNat ≤ 2 ∧ nv.toNat ≤ nv_p.toNat ∧ ∃ st_p : FullState,
          st_p.LengthsOk c ∧ AgreesExcept coneMask s st_p ∧
          SweepConeOk F_cur st_p root_v.toNat nv_p.toNat nc_p.toNat ∧
          st_p.scratch.tarjan_mark[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 qi.toNat ∧
          (st_p.scratch.work_stk1[qi.toNat]?.getD 0#32).toNat = cv.toNat ∧ (FullMem c st_p ⋆ R) mp)
      (fun (_, _, pol, ()) _ => 2 - pol.toNat) ?_ ?_
    · intro J_pol hJ_pol; sw_fast
      exact hJ_pol (nv, nc, 0#32, ()) mo ⟨Nat.zero_le _, Nat.le_refl _, st, hlen_st, hag_st,
        hcone_st, hcv_idx, by rw [hwk_qi], hmo⟩
    · intro J_pol; rintro ⟨nv_p, nc_p, pol, ⟨⟩⟩ mp
        ⟨hpol_le, hnv_mono, st_p, hlen_p, hag_p, hcone_p, htmk_cv, hwk_cv, hmp⟩ hJ_pol
      sw_split; rotate_left
      · sw_fast; exact hJ_out (nv_p, nc_p, qi + 1#32, ()) mp (by dsimp only; omega)
          ⟨by omega, st_p, hlen_p, hag_p, hcone_p, hmp⟩
      have hpol_lt : pol.toNat < 2 := by sw_bd
      sw_split; rotate_left
      · sw_fast; exact hJ_out (nv_p, nc_p, qi + 1#32, ()) mp (by dsimp only; omega)
          ⟨by omega, st_p, hlen_p, hag_p, hcone_p, hmp⟩
      have hncp_lt : nc_p.toNat < 64 := by sw_bd
      let lit : BitVec 32 := (cv <<< (1 : Nat)) ||| pol
      have hlit_eq : lit.toNat = 2 * cv.toNat + pol.toNat :=
        bv32_shl1_or_pol cv pol (by have := c.hmaxv; unfold dimacsBound at this; omega) hpol_lt
      have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by omega
      have hlit_lt' : ((cv <<< (1 : Nat)) ||| pol).toNat < 2 * s.core.cur_vars := hlit_lt
      have hwvec_p := hlen_p.core_ok.wvec_len
      have h2lit : (lit.setWidth 64 <<< (1 : Nat)).toNat = 2 * lit.toNat := bv64_shl1_toNat _
      have h2lit1 : ((lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat = 2 * lit.toNat + 1 :=
        bv64_shl1_add1_toNat _
      sw_fast; have hwvec_eq : st_p.core.wvec = s.core.wvec := hag_p.get (·.core.wvec)
      have hbounds := hdw.layout.bounds lit.toNat hlit_lt
      have hwlen_le := hlen.core_ok.wlen_le; have hwcap_lt := c.hwcap
      let wOff := (st_p.core.wvec[(lit.setWidth 64 <<< (1 : Nat)).toNat]'(by omega)).setWidth 64
      let wSz :=
        (st_p.core.wvec[((lit.setWidth 64 <<< (1 : Nat)) + 1#64).toNat]'(by omega)).setWidth 64
      have hwOff_n : wOff.toNat = fullWatchOffCore s.core lit.toNat := by
        dsimp only [wOff]; unfold fullWatchOffCore
        rw [bv32_zext64_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        rw [List.getElem?_eq_getElem (by rw [← hwvec_eq]; omega), Option.getD_some]
        simp [hwvec_eq, h2lit]
      have hwSz_n : wSz.toNat = fullWatchSizeCore s.core lit.toNat := by
        dsimp only [wSz]; unfold fullWatchSizeCore
        rw [bv32_zext64_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        rw [List.getElem?_eq_getElem (by rw [← hwvec_eq]; omega), Option.getD_some]
        simp [hwvec_eq, h2lit1]
      let wEnd := wOff + wSz
      have hend_eq : wEnd.toNat =
          fullWatchOffCore s.core lit.toNat + fullWatchSizeCore s.core lit.toNat := by
        unfold dimacsBound at hwcap_lt; dsimp only [wEnd]
        rw [BitVec.toNat_add, hwOff_n, hwSz_n, Nat.mod_eq_of_lt (by omega)]
      have hpol1 : (pol + 1#32).toNat = pol.toNat + 1 := by
        rw [BitVec.toNat_add, show (1#32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
      refine wp_join_group (ts := [i32, i32, i64])
        (fun (nv_e, nc_e, _, ()) m_we =>
          nv.toNat ≤ nv_e.toNat ∧ ∃ st_we : FullState,
            st_we.LengthsOk c ∧ AgreesExcept coneMask s st_we ∧
            SweepConeOk F_cur st_we root_v.toNat nv_e.toNat nc_e.toNat ∧
            st_we.scratch.tarjan_mark[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 qi.toNat ∧
            (st_we.scratch.work_stk1[qi.toNat]?.getD 0#32).toNat = cv.toNat ∧
            (FullMem c st_we ⋆ R) m_we) ?_ ?_
      · rintro _ ⟨nv_e, nc_e, _, ⟨⟩⟩ m_we ⟨hnve, st_we, hl_e, ha_e, hc_e, ht_e, hw_e, hm_e⟩
        sw_fast
        exact hJ_pol (nv_e, nc_e, pol + 1#32, ()) m_we (by dsimp only; omega)
          ⟨by omega, hnve, st_we, hl_e, ha_e, hc_e, ht_e, hw_e, hm_e⟩
      intro J_we hJ_we; sw_fast
      -- Watch-list loop: `while (p < end && nc < 64u)`
      refine wp_loop_inv (ts := [i32, i32, i64])
        (fun (nv_w, nc_w, p, ()) mw =>
          p.toNat ≤ wEnd.toNat ∧ nv.toNat ≤ nv_w.toNat ∧
          DenseWatchSliceOk F_cur s.core lit.toNat p.toNat (wEnd.toNat - p.toNat) ∧
          ∃ st_w : FullState, st_w.LengthsOk c ∧ AgreesExcept coneMask s st_w ∧
            SweepConeOk F_cur st_w root_v.toNat nv_w.toNat nc_w.toNat ∧
            st_w.scratch.tarjan_mark[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 qi.toNat ∧
            (st_w.scratch.work_stk1[qi.toNat]?.getD 0#32).toNat = cv.toNat ∧
            (FullMem c st_w ⋆ R) mw)
        (fun (_, _, p, ()) _ => wEnd.toNat - p.toNat) ?_ ?_
      · intro J_w hJ_w; sw_fast
        refine hJ_w (nv_p, nc_p, wOff, ()) mp ⟨by omega, hnv_mono, ?_, st_p, hlen_p, hag_p,
          hcone_p, htmk_cv, hwk_cv, hmp⟩
        rw [hwOff_n, show wEnd.toNat - fullWatchOffCore s.core lit.toNat =
          fullWatchSizeCore s.core lit.toNat by omega]
        exact hdw.slices lit.toNat hlit_lt
      · intro J_w; rintro ⟨nv_w, nc_w, p, ⟨⟩⟩ mw
          ⟨hp_le, hnv_w_mono, hslice, st_w, hlen_w, hag_w, hcone_w, htmk_w, hwk_w, hmw⟩ hJ_w
        clear hJ_out hJ_ex hJ_pol hmp hlen_p hag_p hcone_p htmk_cv hwk_cv hmo hlen_st hag_st
          hcone_st hwk_qi hcv_idx
        sw_split; rotate_left
        · sw_fast; exact hJ_we (nv_w, nc_w, p, ()) mw
            ⟨hnv_w_mono, st_w, hlen_w, hag_w, hcone_w, htmk_w, hwk_w, hmw⟩
        have hp_lt : p.toNat < wEnd.toNat := by
          have hmod : (wOff.toNat + wSz.toNat) % 2 ^ 64 = wEnd.toNat := by rw [← BitVec.toNat_add]
          have hlt : p.toNat < (wOff.toNat + wSz.toNat) % 2 ^ 64 := by
            dsimp only [wOff, wSz, lit]; sw_bd
          omega
        sw_split; rotate_left
        · sw_fast; exact hJ_we (nv_w, nc_w, p, ()) mw
            ⟨hnv_w_mono, st_w, hlen_w, hag_w, hcone_w, htmk_w, hwk_w, hmw⟩
        have hncw_lt : nc_w.toNat < 64 := by sw_bd
        have hwstk_eq : st_w.core.wstk = s.core.wstk := hag_w.get (·.core.wstk)
        have hcv_w : st_w.core.cur_vars = s.core.cur_vars := hag_w.get (·.core.cur_vars)
        have hwstk_w := hlen_w.core_ok.wstk_len_arr; have hp_wcap : p.toNat < c.wcap := by omega
        have hp1 : (p + 1#64).toNat = p.toNat + 1 := by
          unfold dimacsBound at hwcap_lt
          rw [BitVec.toNat_add, show (1#64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
        sw_fast
        generalize hw0_eq : st_w.core.wstk[p.toNat]'(by omega) = w0
        have hw0_s : s.core.wstk[p.toNat]? = some w0 := by
          rw [List.getElem?_eq_getElem (by rw [← hwstk_eq]; omega), ← hw0_eq]
          exact congrArg some (by simp [hwstk_eq])
        sw_split
        · -- Binary watch branch: `(w0 & PW_BIN_FLAG) != 0`
          have hbin : (w0 &&& 0x80000000#32) ≠ 0#32 := by sw_bd
          obtain ⟨_, hot_lt, hent_bin, hslice1⟩ :=
            denseWatchSlice_step_bin hslice (by omega) hw0_s hbin
          let ot : BitVec 32 := w0 &&& 0x7FFFFFFF#32
          have hot_lt' : ot.toNat < 2 * s.core.cur_vars := hot_lt
          let ov : BitVec 32 := ot >>> (1 : Nat)
          have hov_eq : ov.toNat = ot.toNat / 2 := bv32_shr1_toNat ot
          have hov_lt : ov.toNat < s.core.cur_vars := by omega
          have hvals_w := hlen_w.core_ok.vals_len; have htm_w := hlen_w.scratch_ok.tarjan_mark_len
          have hwk_w_len := hlen_w.scratch_ok.work_stk1_len
          sw_fast
          refine wp_join_group (ts := [i32, i32])
            (fun (nv_b, nc_b, ()) m_b =>
              nv.toNat ≤ nv_b.toNat ∧ ∃ st_b : FullState,
                st_b.LengthsOk c ∧ AgreesExcept coneMask s st_b ∧
                SweepConeOk F_cur st_b root_v.toNat nv_b.toNat nc_b.toNat ∧
                st_b.scratch.tarjan_mark[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 qi.toNat ∧
                (st_b.scratch.work_stk1[qi.toNat]?.getD 0#32).toNat = cv.toNat ∧
                (FullMem c st_b ⋆ R) m_b) ?_ ?_
          · rintro _ ⟨nv_b, nc_b, ⟨⟩⟩ m_b ⟨hnvb, st_b, hlb, hab, hcb, htb, hwb, hmb⟩; sw_fast
            exact hJ_w (nv_b, nc_b, p + 1#64, ()) m_b (by dsimp only; omega)
              ⟨by omega, hnvb, by rw [hp1, show wEnd.toNat - (p.toNat + 1) =
                  wEnd.toNat - p.toNat - 1 by omega]; exact hslice1,
                st_b, hlb, hab, hcb, htb, hwb, hmb⟩
          intro J_bin hJ_bin; sw_fast; sw_split; rotate_left
          · sw_fast; exact hJ_bin (nv_w, nc_w, ()) mw
              ⟨hnv_w_mono, st_w, hlen_w, hag_w, hcone_w, htmk_w, hwk_w, hmw⟩
          sw_fast
          refine wp_join_group (ts := [])
            (fun () m_or => m_or = mw ∧
              (st_w.scratch.tarjan_mark[ov.toNat]?.getD 0#32 ≠ 0xFFFFFFFF#32 ∨ nv_w.toNat < 24))
            ?_ ?_
          · rintro _ ⟨⟩ m_or ⟨hmor, hor⟩; subst m_or; sw_fast
            refine wp_join_group (ts := [i32])
              (fun (nv_a, ()) m_a =>
                nv.toNat ≤ nv_a.toNat ∧ ∃ st_a : FullState,
                  st_a.LengthsOk c ∧ AgreesExcept coneMask s st_a ∧
                  SweepConeOk F_cur st_a root_v.toNat nv_a.toNat nc_w.toNat ∧
                  st_a.scratch.tarjan_mark[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 qi.toNat ∧
                  (st_a.scratch.work_stk1[qi.toNat]?.getD 0#32).toNat = cv.toNat ∧
                  st_a.scratch.tarjan_mark[ov.toNat]?.getD 0#32 ≠ 0xFFFFFFFF#32 ∧
                  (FullMem c st_a ⋆ R) m_a) ?_ ?_
            · rintro _ ⟨nv_a, ⟨⟩⟩ m_a ⟨hnva, st_a, hla, haa, hca, htca, hwca, htoa, hma⟩
              sw_unroll; sw_split; rotate_left
              · sw_fast; exact hJ_bin (nv_a, nc_w, ()) m_a
                  ⟨hnva, st_a, hla, haa, hca, htca, hwca, hma⟩
              have htm_a := hla.scratch_ok.tarjan_mark_len; have htmp_a := hla.core_ok.tmp_len_arr
              have hcv_a := haa.get (·.core.cur_vars)
              rcases hca.2.2.2.2.2.2.2.1 ov.toNat (by rw [hcv_a]; exact hov_lt) with
                hff | ⟨iov, hiov, hwov, htov⟩
              · exact absurd hff htoa
              sw_fast
              obtain ⟨hl0_lt, hl1_lt, hlift0, hlift1⟩ :=
                cone_bin_lits_ok (Nat.lt_of_lt_of_le hqi_lt hnva) hca.2.1 hpol_lt hlit_eq
                  hov_eq hiov htca hwca htov hwov
              have hcv_tm : cv.toNat < st_a.scratch.tarjan_mark.length := by omega
              have hov_tm : ov.toNat < st_a.scratch.tarjan_mark.length := by omega
              rw [List.getElem?_eq_getElem hcv_tm, Option.getD_some] at hl0_lt hlift0
              rw [List.getElem?_eq_getElem hov_tm, Option.getD_some] at hl1_lt hlift1
              let l0_b := (st_a.scratch.tarjan_mark[cv.toNat]'hcv_tm <<< (1 : Nat)) ||| pol
              let l1_b :=
                (st_a.scratch.tarjan_mark[ov.toNat]'hov_tm <<< (1 : Nat)) ||| (ot &&& 1#32)
              let st_a1 : FullState :=
                { st_a with core := { st_a.core with tmp := st_a.core.tmp.set 0 l0_b } }
              refine cone_bin_store1_and_addCl hAddCl (st := st_a1) (l0 := l0_b) (l1 := l1_b) rfl
                (by simp [Arg.val_var])
                ⟨{ hla.core_ok with tmp_len_arr := by simp [st_a1, htmp_a] }, hla.scratch_ok⟩
                (haa.update _ fun _ => rfl) hcap hca hncw_lt
                (by dsimp only [st_a1]; exact List.getElem?_set_self (by omega))
                hl0_lt hl1_lt (by rw [hlift0, hlift1]; exact hent_bin) hm
                fun nc' st' m' hl' ha' hc' ht' hw' hm' => by
                  sw_fast; exact hJ_bin (nv_a, nc'.setWidth 32, ()) m'
                    ⟨hnva, st', hl', ha', hc', ht' ▸ htca, hw' ▸ hwca, hm'⟩
            intro J_a hJ_a; sw_fast; sw_split
            · have hmiss : st_w.scratch.tarjan_mark[ov.toNat]?.getD 0#32 = 0xFFFFFFFF#32 := by
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; dsimp only [ov, ot]
                sw_bd
              have hnv_lt24_w : nv_w.toNat < 24 := hor.elim (absurd hmiss) id
              have hnv_w_lt : nv_w.toNat < s.core.cur_vars := by
                rw [← hcv_w]; exact (sweepConeOk_push_var hlen_w hcone_w hnv_lt24_w
                  (by rw [hcv_w]; exact hov_lt) hmiss).1
              sw_fast
              obtain ⟨_, hnv1, hlen_a, hag_a, hca, htca, hwca, htoa, _⟩ :=
                cone_push_var_step hlen_w hag_w hcone_w hnv_lt24_w (by omega) hov_lt htmk_w
                  hwk_w hmiss
              have hm_a : (FullMem c { st_w with scratch := { st_w.scratch with
                  tarjan_mark := st_w.scratch.tarjan_mark.set ov.toNat nv_w
                  work_stk1 := st_w.scratch.work_stk1.set nv_w.toNat ov } } ⋆ R) m := by
                have h1 : (((w0 &&& 0x7FFFFFFF#32) >>> (1 : Nat)).setWidth 64).toNat =
                    ov.toNat := by dsimp only [ov, ot]; simp only [bv_c0]
                rw [← h1]; exact hm
              exact hJ_a (nv_w + 1#32, ()) m
                ⟨by omega, _, hlen_a, hag_a, hca, htca, hwca, htoa, hm_a⟩
            · have hne_ov : st_w.scratch.tarjan_mark[ov.toNat]?.getD 0#32 ≠ 0xFFFFFFFF#32 := by
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                dsimp only [ov, ot]; sw_bd
              sw_fast; exact hJ_a (nv_w, ()) mw
                ⟨hnv_w_mono, st_w, hlen_w, hag_w, hcone_w, htmk_w, hwk_w, hne_ov, hmw⟩
          intro J_or hJ_or; sw_split
          · have hne : st_w.scratch.tarjan_mark[ov.toNat]?.getD 0#32 ≠ 0xFFFFFFFF#32 := by
              rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
              dsimp only [ov, ot]; sw_bd
            sw_fast; exact hJ_or () mw ⟨rfl, Or.inl hne⟩
          · sw_split
            · have hlt : nv_w.toNat < 24 := by sw_bd
              sw_fast; exact hJ_or () mw ⟨rfl, Or.inr hlt⟩
            · sw_fast; exact hJ_bin (nv_w, nc_w, ()) mw
                ⟨hnv_w_mono, st_w, hlen_w, hag_w, hcone_w, htmk_w, hwk_w, hmw⟩
        · have hocc : (w0 &&& 0x80000000#32) = 0#32 := by sw_bd
          obtain ⟨hrem2, _, cr, hcr_s, hcr_lt, hcr_ref, hslice2⟩ :=
            denseWatchSlice_step_occ hslice (by omega) hw0_s hocc
          sw_split
          · exfalso
            have hmod : (wOff.toNat + wSz.toNat) % 2 ^ 64 = wEnd.toNat := by rw [← BitVec.toNat_add]
            have hge : (wOff.toNat + wSz.toNat) % 2 ^ 64 ≤ (p.toNat + 1) % 2 ^ 64 := by
              dsimp only [wOff, wSz, lit]; sw_bd
            have hmodp : (p.toNat + 1) % 2 ^ 64 = p.toNat + 1 := by
              unfold dimacsBound at hwcap_lt; exact Nat.mod_eq_of_lt (by omega)
            omega
          have hp2 : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by
            unfold dimacsBound at hwcap_lt
            rw [BitVec.toNat_add, hp1, show (1#64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
          have har_w := hlen_w.core_ok.arena_len_arr; have har_s := hlen.core_ok.arena_len_arr
          have hcr_wf := hw.arena.refs_wf cr.toNat hcr_ref; have hacap_lt := c.harena
          have hal_le := hlen.core_ok.arena_len_le
          have hcr_eq : st_w.core.wstk[p.toNat + 1]'(by omega) = cr := by
            rw [List.getElem?_eq_getElem (by rw [← hwstk_eq]; omega)] at hcr_s
            simpa [hwstk_eq] using Option.some.inj hcr_s
          have hcr_eq' : st_w.core.wstk[(p + 1#64).toNat]'(by omega) = cr := by
            simpa [hp1] using hcr_eq
          have hcr2_lt : (cr.setWidth 64 + 2#64).toNat = cr.toNat + 2 := by
            unfold dimacsBound at hacap_lt; simp only [bv_c0, BitVec.toNat_ofNat]; omega
          sw_fast; have har_eq : st_w.core.arena = s.core.arena := hag_w.get (·.core.arena)
          let sz : BitVec 32 := st_w.core.arena[((st_w.core.wstk[(p + 1#64).toNat]'(
            by omega)).setWidth 64 + 2#64).toNat]'(by rw [hcr_eq']; omega)
          have hsz_core : sz.toNat = fullArenaClauseSizeCore s.core cr.toNat := by
            unfold fullArenaClauseSizeCore; dsimp only [sz]
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
            have hidx : ((st_w.core.wstk[(p + 1#64).toNat]'(by omega)).setWidth 64 +
                2#64).toNat = cr.toNat + 2 := by rw [hcr_eq', hcr2_lt]
            simp only [har_eq, hidx]
          have hstep_occ : ∀ (nv_x nc_x : BitVec 32) (st_x : FullState) (mx : Mem 64),
              nv.toNat ≤ nv_x.toNat → st_x.LengthsOk c → AgreesExcept coneMask s st_x →
              SweepConeOk F_cur st_x root_v.toNat nv_x.toNat nc_x.toNat →
              st_x.scratch.tarjan_mark[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 qi.toNat →
              (st_x.scratch.work_stk1[qi.toNat]?.getD 0#32).toNat = cv.toNat →
              (FullMem c st_x ⋆ R) mx → J_w (nv_x, nc_x, p + 1#64 + 1#64, ()) mx :=
            fun nv_x nc_x st_x mx hnvx hlx hax hcx htx hwx hmx =>
              hJ_w (nv_x, nc_x, p + 1#64 + 1#64, ()) mx (by dsimp only; omega)
                ⟨by omega, hnvx, by rw [hp2, show wEnd.toNat - (p.toNat + 2) =
                    wEnd.toNat - p.toNat - 2 by omega]; exact hslice2,
                  st_x, hlx, hax, hcx, htx, hwx, hmx⟩
          let hocc_done :=
            hstep_occ nv_w nc_w st_w mw hnv_w_mono hlen_w hag_w hcone_w htmk_w hwk_w hmw
          sw_split; · sw_fast; exact hocc_done
          have hgr0 : (st_w.core.arena[cr.toNat]'(by omega) &&&
              (0x00080000#32 ||| 0x00400000#32)) = 0#32 := by
            have hpeq : (p.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 = (p + 1#64).toNat := by
              rw [BitVec.toNat_add]; rfl
            have hidx_n : (st_w.core.wstk[(p.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'(by
                rw [hpeq]; omega)).toNat = cr.toNat :=
              congrArg BitVec.toNat (by simpa only [hpeq] using hcr_eq')
            simp only [hidx_n] at hc; exact hc
          sw_split; · sw_fast; exact hocc_done
          have hsz_ge3 : 3 ≤ sz.toNat := by dsimp only [sz]; sw_bd
          sw_split; · sw_fast; exact hocc_done
          have hsz_le6 : sz.toNat ≤ 6 := by dsimp only [sz]; sw_bd
          obtain ⟨hng, hcr_sz_le, hsz_cv, hcr3_bd⟩ :=
            cone_occ_hdr_ok hlen hw hnd har_eq hcr_ref hsz_core hgr0
          have hsz_ar : (s.core.arena[cr.toNat + 2]?.getD 0#32).toNat = sz.toNat := hsz_core.symm
          sw_fast
          refine wp_join_group (ts := [i32, .bool, i32, i32])
            (fun (nv_ke, sat_e, cnt_e, _, ()) m_ke =>
              cnt_e.toNat ≤ sz.toNat ∧ nv.toNat ≤ nv_ke.toNat ∧ ∃ st_ke : FullState,
                st_ke.LengthsOk c ∧ AgreesExcept coneMask s st_ke ∧
                SweepConeOk F_cur st_ke root_v.toNat nv_ke.toNat nc_w.toNat ∧
                st_ke.scratch.tarjan_mark[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 qi.toNat ∧
                (st_ke.scratch.work_stk1[qi.toNat]?.getD 0#32).toNat = cv.toNat ∧
                (sat_e = false →
                  (∀ j < cnt_e.toNat, (st_ke.core.tmp[j]?.getD 0#32).toNat < 2 * nv_ke.toNat) ∧
                  ∀ i < sz.toNat,
                    let l := (s.core.arena[cr.toNat + 3 + i]?.getD 0#32).toNat
                    s.core.vals[l]?.getD 0#8 = 0xFF#8 ∨
                    l ∈ (st_ke.core.tmp.take cnt_e.toNat).map
                      (fun x => coneLift st_ke.scratch.work_stk1 x.toNat)) ∧
                (FullMem c st_ke ⋆ R) m_ke) ?_ ?_
          · rintro _ ⟨nv_ke, sat_e, cnt_e, _, ⟨⟩⟩ m_ke
              ⟨hcnt_sz, hnv_ke, st_ke, hl_ke, ha_ke, hc_ke, ht_ke, hw_ke, hs_ke, hm_ke⟩
            sw_unroll; sw_split
            · sw_fast
              exact hstep_occ nv_ke nc_w st_ke m_ke hnv_ke hl_ke ha_ke hc_ke ht_ke hw_ke hm_ke
            have hsat_f : sat_e = false := by sw_bd
            sw_split; rotate_left
            · sw_fast
              exact hstep_occ nv_ke nc_w st_ke m_ke hnv_ke hl_ke ha_ke hc_ke ht_ke hw_ke hm_ke
            obtain ⟨hlts_ke, hcov_ke⟩ := hs_ke hsat_f
            have hcnt_tmp : cnt_e.toNat ≤ st_ke.core.tmp.length := by
              rw [hl_ke.core_ok.tmp_len_arr]
              exact Nat.le_trans hcnt_sz (Nat.le_trans hsz_cv hcv_le)
            have hent_ke : (cnfOfClauses F_cur).EntailsClause (cnfClause
                ((st_ke.core.tmp.take cnt_e.toNat).map
                  (fun x => coneLift st_ke.scratch.work_stk1 x.toNat))) := by
              refine cone_clause_entails_of_filtered hw hcl0 hcr_ref hng fun l hl => ?_
              obtain ⟨i, hi, rfl⟩ := (fullArenaClauseLitsCore_mem_iff
                (by rw [hsz_ar]; exact hcr3_bd)).mp hl
              rw [hsz_ar] at hi; exact hcov_ke i hi
            sw_fast
            refine full_sweep_cone_call_addCl hAddCl (aSz := Arg.var cnt_e) rfl hl_ke ha_ke hcap
              hc_ke hncw_lt hcnt_tmp
              (fun j hj => by
                have h := hlts_ke j hj
                rwa [List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hj hcnt_tmp),
                  Option.getD_some] at h)
              hent_ke hm_ke
              fun nc' st' m' hl' ha' hc' ht_eq hw_eq hm' => by
                sw_fast; exact hstep_occ nv_ke (nc'.setWidth 32) st' m' hnv_ke hl' ha' hc'
                  (ht_eq ▸ ht_ke) (hw_eq ▸ hw_ke) hm'
          intro J_ke hJ_ke; sw_fast
          -- Inner literal loop: `while (k < sz)`
          refine wp_loop_inv (ts := [i32, i32, i32])
            (fun (nv_k, cnt, k, ()) mk =>
              k.toNat ≤ sz.toNat ∧ cnt.toNat ≤ k.toNat ∧ nv.toNat ≤ nv_k.toNat ∧
              ∃ st_k : FullState, st_k.LengthsOk c ∧ AgreesExcept coneMask s st_k ∧
                SweepConeOk F_cur st_k root_v.toNat nv_k.toNat nc_w.toNat ∧
                st_k.scratch.tarjan_mark[cv.toNat]?.getD 0#32 = BitVec.ofNat 32 qi.toNat ∧
                (st_k.scratch.work_stk1[qi.toNat]?.getD 0#32).toNat = cv.toNat ∧
                (∀ j < cnt.toNat, (st_k.core.tmp[j]?.getD 0#32).toNat < 2 * nv_k.toNat) ∧
                (∀ i < k.toNat,
                  let l := (s.core.arena[cr.toNat + 3 + i]?.getD 0#32).toNat
                  s.core.vals[l]?.getD 0#8 = 0xFF#8 ∨
                  l ∈ (st_k.core.tmp.take cnt.toNat).map
                    (fun x => coneLift st_k.scratch.work_stk1 x.toNat)) ∧
                (FullMem c st_k ⋆ R) mk)
            (fun (_, _, k, ()) _ => sz.toNat - k.toNat) ?_ ?_
          · intro J_k hJ_k; sw_fast; exact hJ_k (nv_w, 0#32, 0#32, ()) mw
              ⟨Nat.zero_le _, Nat.zero_le _, hnv_w_mono, st_w, hlen_w, hag_w, hcone_w, htmk_w,
                hwk_w, fun _ hj => by simp at hj, fun _ hi => by simp at hi, hmw⟩
          · intro J_k; rintro ⟨nv_k, cnt, k, ⟨⟩⟩ mk
              ⟨hk_le, hcnt_le, hnv_k_mono, st_k, hlen_k, hag_k, hcone_k, htmk_k, hwk_k, hlts_k,
                hcov_k, hmk⟩ hJ_k
            clear hocc_done hJ_we hJ_w hslice hslice2 hstep_occ hlen_w hag_w hcone_w htmk_w hwk_w
              hmw hdw hnd hcl0 hgr0 hsz_ge3 hAddCl
            sw_split; rotate_left
            · have hk_eq : k.toNat = sz.toNat := by
                dsimp only [sz] at hk_le ⊢
                simp only [bv_c0, show (1 : BitVec 64).toNat = 1 from rfl,
                  show (2 : BitVec 64).toNat = 2 from rfl] at hc hk_le ⊢; omega
              sw_fast; exact hJ_ke (nv_k, false, cnt, k, ()) mk
                ⟨by omega, hnv_k_mono, st_k, hlen_k, hag_k, hcone_k, htmk_k, hwk_k,
                  fun _ => ⟨hlts_k, by simpa [hk_eq] using hcov_k⟩, hmk⟩
            have hk_lt : k.toNat < sz.toNat := by dsimp only [sz]; sw_bd
            have hae_k := hag_k.get (·.core.arena); have hve_k := hag_k.get (·.core.vals)
            have har_k := hlen_k.core_ok.arena_len_arr; have hvals_k := hlen_k.core_ok.vals_len
            have hp1_n : (p + (1 : BitVec 64)).toNat = p.toNat + 1 := hp1
            have hp1_bd : (p + (1 : BitVec 64)).toNat < st_w.core.wstk.length := by
              rw [hp1_n]; omega
            have hcr_1 : st_w.core.wstk[(p + (1 : BitVec 64)).toNat]'hp1_bd = cr := hcr_eq'
            have hidx_k : ((st_w.core.wstk[(p + (1 : BitVec 64)).toNat]'hp1_bd).setWidth 64 +
                3 + k.setWidth 64).toNat = cr.toNat + 3 + k.toNat := by
              rw [hcr_1]; unfold dimacsBound at hacap_lt
              simp only [bv_c0, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat]; omega
            have hidx_bd : ((st_w.core.wstk[(p + (1 : BitVec 64)).toNat]'hp1_bd).setWidth 64 +
                3 + k.setWidth 64).toNat < st_k.core.arena.length := by omega
            have hl_in_cl : (st_k.core.arena[cr.toNat + 3 + k.toNat]'(by omega)).toNat ∈
                fullArenaClauseLitsCore s.core cr.toNat := by
              rw [fullArenaClauseLitsCore_mem_iff (by rw [hsz_ar]; exact hcr3_bd)]
              refine ⟨k.toNat, by rw [hsz_ar]; exact hk_lt, ?_⟩
              rw [List.getElem?_eq_getElem (by rw [← hae_k]; omega), Option.getD_some]; simp [hae_k]
            have hl_lt_s : (st_k.core.arena[((st_w.core.wstk[(p + (1 : BitVec 64)).toNat]'
                hp1_bd).setWidth 64 + 3 + k.setWidth 64).toNat]'hidx_bd).toNat <
                2 * s.core.cur_vars := by
              simpa only [hidx_k] using hw.arena.lits_lt cr.toNat hcr_ref hng _ hl_in_cl
            sw_fast
            let lit_k : BitVec 32 := st_k.core.arena[((st_w.core.wstk[(p + (1 : BitVec 64)).toNat]'
              hp1_bd).setWidth 64 + 3 + k.setWidth 64).toNat]'hidx_bd
            have hval_bd : lit_k.toNat < st_k.core.vals.length := by dsimp only [lit_k]; omega
            have hval_k_eq : st_k.core.vals[lit_k.toNat]'hval_bd =
                s.core.vals[lit_k.toNat]?.getD 0#8 := by
              rw [List.getElem?_eq_getElem (by rw [← hve_k]; exact hval_bd), Option.getD_some]
              simp [hve_k]
            have hk1 : (k + 1#32).toNat = k.toNat + 1 := by
              rw [BitVec.toNat_add, show (1#32).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]
            have hlit_ar : (s.core.arena[cr.toNat + 3 + k.toNat]?.getD 0#32).toNat =
                lit_k.toNat := by
              rw [List.getElem?_eq_getElem (by rw [← hae_k]; omega), Option.getD_some]
              simp only [lit_k, hidx_k, hae_k]
            sw_split
            · sw_fast; exact hJ_ke (nv_k, true, cnt, k, ()) mk
                ⟨Nat.le_trans hcnt_le (Nat.le_of_lt hk_lt), hnv_k_mono, st_k, hlen_k, hag_k,
                  hcone_k, htmk_k, hwk_k, fun hf => Bool.noConfusion hf, hmk⟩
            have hnot_pos : s.core.vals[lit_k.toNat]?.getD 0#8 ≠ 1#8 := fun h1 => by
              have h1' : st_k.core.vals[lit_k.toNat]'hval_bd = 1#8 := hval_k_eq.trans h1
              dsimp only [lit_k] at h1'; simp only [bv_c0] at h1'; rw [h1'] at hc
              exact absurd hc (by decide)
            sw_unroll; sw_split
            · exact cone_k_unassigned_wp (Γ := Γ) (c := c) (F_cur := F_cur) (s := s) (st_k := st_k)
                (root_v := root_v) (cv := cv) (qi := qi) (nv := nv) (nc_w := nc_w) (cr := cr)
                (sz := sz) (nv_k := nv_k) (cnt := cnt) (k := k) (lit_v := lit_k)
                hJ_ke hJ_jn hJ_k hcv_le hqi_lt hsz_le6 hsz_cv hk_lt hcnt_le hnv_k_mono hlen_k hag_k
                hcone_k htmk_k hwk_k hlts_k hcov_k hl_lt_s hlit_ar hmk
            · have hne0 : s.core.vals[lit_k.toNat]?.getD 0#8 ≠ 0#8 := fun h0 => by
                have h0' : st_k.core.vals[lit_k.toNat]'hval_bd = 0#8 := hval_k_eq.trans h0
                dsimp only [lit_k] at h0'; simp only [bv_c0] at h0'; rw [h0'] at hc
                exact absurd hc (by decide)
              have hfals_k : s.core.vals[lit_k.toNat]?.getD 0#8 = 0xFF#8 :=
                (hw.vals_domain lit_k.toNat hl_lt_s).elim (absurd · hne0)
                  (·.elim (absurd · hnot_pos) id)
              sw_fast; refine hJ_k (nv_k, cnt, k + 1#32, ()) mk (by dsimp only; omega)
                ⟨by omega, by omega, hnv_k_mono, st_k, hlen_k, hag_k, hcone_k, htmk_k, hwk_k,
                  hlts_k, fun i hi => ?_, hmk⟩
              rw [hk1] at hi; rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
              · exact hcov_k i hlt
              · left; rwa [hlit_ar]

end

end LeanQbe.T.Examples.Kissat.Full
