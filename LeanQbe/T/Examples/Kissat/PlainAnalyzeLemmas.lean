module

public import LeanQbe.T.Examples.Kissat.PlainAnalyzeLemmas1

/-!
# Kissat `D-Plain` Conflict-Analysis `Func.wp` Proof (Part 2: `plain_analyze`)

Builds on `PlainAnalyzeLemmas1` (`plain_analyze_lit`, `plain_analyze_rsn`, 1-UIP resolvent
theory) to verify `plain_analyze` (`plainAnalyzeSpec`, `plain_analyze_wp`) parameterized over
all 14 `Γ` callees.
-/

set_option autoImplicit false
@[expose] public section
namespace LeanQbe.T.Examples.Kissat.Plain
open Std Std.Sat Std.ExtHashMap LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat LeanQbe.T.C0Step Kraken.Bedrock2.Test PlainAnalyzeTactics
open scoped PlainAnalyzeTactics

/-! ## 1. Strictly `local` `C0Step` helpers and O(1)-per-step symbolic executor -/

private theorem strip_wp {Γ rs Q X e m} (h : wp (rs := rs) Γ Q X e m) : wp Γ Q X e m := h
private theorem strip_fwp {as rs Γ f args m Q X}
    (h : Func.wp (as := as) (rs := rs) Γ f args m Q X) : Func.wp Γ f args m Q X := h
private theorem strip_le_wp {a b : Nat} {P : Prop} (h : a ≤ b) (hp : P) : a ≤ b ∧ P := ⟨h, hp⟩
attribute [local bv_c0] Bool.true_eq_false Bool.false_eq_true
private theorem i8_sext32_eq0 (v : BitVec 8) : (v.signExtend 32 = 0#32) ↔ v = 0#8 := by
  revert v; decide
private theorem u8_zext32_eq0 (v : BitVec 8) : (v.setWidth 32 = 0#32) ↔ v = 0#8 := by
  revert v; decide
@[local bv_c0] private theorem i8_sext32_zero : (0#8 : BitVec 8).signExtend 32 = 0#32 := rfl
@[local bv_c0] private theorem u8_zext32_zero : (0#8 : BitVec 8).setWidth 32 = 0#32 := rfl
@[local bv_c0] private theorem i8_sext32_eq0_prop (v : BitVec 8) :
    (v.signExtend 32 = 0#32) = (v = 0#8) := propext (i8_sext32_eq0 v)
@[local bv_c0] private theorem u8_zext32_eq0_prop (v : BitVec 8) :
    (v.setWidth 32 = 0#32) = (v = 0#8) := propext (u8_zext32_eq0 v)
@[local c0_store] private theorem c0_store_ptmp_0 {c : PlainCfg} {s : PlainState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.tmp.length)
    (hm : (PlainMem c s ⋆ R) m) : storeOk m i32 (c.pTmp + 0#64) ∧
      (PlainMem c { s with tmp := s.tmp.set 0 v } ⋆ R) (storeMem m i32 (c.pTmp + 0#64) v) :=
  store_arena_tmp (i := 0) v hi hm
@[local c0_load] private theorem c0_load_ptmp_1 {c : PlainCfg} {s : PlainState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 1 < s.tmp.length) (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pTmp + 4#64) = some (s.tmp[1]'hi) := load_arena_tmp (i := 1) hi hm
@[local c0_store] private theorem c0_store_ptmp_1 {c : PlainCfg} {s : PlainState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 1 < s.tmp.length)
    (hm : (PlainMem c s ⋆ R) m) : storeOk m i32 (c.pTmp + 4#64) ∧
      (PlainMem c { s with tmp := s.tmp.set 1 v } ⋆ R) (storeMem m i32 (c.pTmp + 4#64) v) :=
  store_arena_tmp (i := 1) v hi hm
private theorem getElem_eq_of_idx {α : Type} {xs : List α} {i j : Nat}
    {hi : i < xs.length} {hj : j < xs.length} (h : i = j) : xs[i]'hi = xs[j]'hj := by subst h; rfl
section PaWp
variable {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
local notation "K " t => Tup Val [t] → Expr Val Cont rs
private theorem pa_wp_copy {t} {a : Arg Val t} {k : K t} (h : wp Γ Q X (k (a.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.copy t) (a, ())) k) m := by simpa only [wp_let_copy_eq] using h
private theorem pa_wp_add {n} {a b : Arg Val (.bits n)} {k : K (.bits n)}
    (h : wp Γ Q X (k (a.val + b.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.add _) (a, b, ())) k) m := by
  simpa only [wp_let_add_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2] using h
private theorem pa_wp_sub {n} {a b : Arg Val (.bits n)} {k : K (.bits n)}
    (h : wp Γ Q X (k (a.val - b.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.sub _) (a, b, ())) k) m := by
  simpa only [wp_let_sub_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2] using h
private theorem pa_wp_mul {n} {a b : Arg Val (.bits n)} {k : K (.bits n)}
    (h : wp Γ Q X (k (a.val * b.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.mul _) (a, b, ())) k) m := by
  simpa only [wp_let_mul_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2] using h
private theorem pa_wp_and {n} {a b : Arg Val (.bits n)} {k : K (.bits n)}
    (h : wp Γ Q X (k (a.val &&& b.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.and _) (a, b, ())) k) m := by simpa only [wp_let_and_eq, lift2] using h
private theorem pa_wp_or {n} {a b : Arg Val (.bits n)} {k : K (.bits n)}
    (h : wp Γ Q X (k (a.val ||| b.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.or _) (a, b, ())) k) m := by simpa only [wp_let_or_eq, lift2] using h
private theorem pa_wp_xor {n} {a b : Arg Val (.bits n)} {k : K (.bits n)}
    (h : wp Γ Q X (k (a.val ^^^ b.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.xor _) (a, b, ())) k) m := by simpa only [wp_let_xor_eq, lift2] using h
private theorem pa_wp_lshr1_32 {a : Arg Val (.bits 32)} {k : K (.bits 32)}
    (h : wp Γ Q X (k (a.val >>> 1, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.lshr _) (a, Arg.imm 1#32, ())) k) m := by
  simpa only [wp_let_lshr_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2, Arg.val_imm,
    BitVec.reduceToNat, Nat.reduceMod] using h
private theorem pa_wp_zext32_64 {a : Arg Val (.bits 32)} {k : K (.bits 64)}
    (h : wp Γ Q X (k (a.val.setWidth 64, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.zext 32 64) (a, ())) k) m := by
  rw [wp_let_zext_eq]; exact ⟨by decide, h⟩
private theorem pa_wp_zext8_32 {a : Arg Val (.bits 8)} {k : K (.bits 32)}
    (h : wp Γ Q X (k (a.val.setWidth 32, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.zext 8 32) (a, ())) k) m := by
  rw [wp_let_zext_eq]; exact ⟨by decide, h⟩
private theorem pa_wp_sext32_64_0 {k : K (.bits 64)} (h : wp Γ Q X (k (0#64, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.sext 32 64) (Arg.imm 0#32, ())) k) m := by
  simpa only [wp_let_sext_eq] using ⟨by decide, h⟩
private theorem pa_wp_sext32_64_1 {k : K (.bits 64)} (h : wp Γ Q X (k (1#64, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.sext 32 64) (Arg.imm 1#32, ())) k) m := by
  simpa only [wp_let_sext_eq] using ⟨by decide, h⟩
private theorem pa_wp_mul_0_4 {k : K (.bits 64)} (h : wp Γ Q X (k (0#64, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.mul _) (Arg.imm 0#64, Arg.imm 4#64, ())) k) m := by
  simpa only [wp_let_mul_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2, Arg.val_imm,
    BitVec.reduceMul] using h
private theorem pa_wp_mul_1_4 {k : K (.bits 64)} (h : wp Γ Q X (k (4#64, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.mul _) (Arg.imm 1#64, Arg.imm 4#64, ())) k) m := by
  simpa only [wp_let_mul_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, lift2, Arg.val_imm,
    BitVec.reduceMul] using h
private theorem pa_wp_sext8_32 {a : Arg Val (.bits 8)} {k : K (.bits 32)}
    (h : wp Γ Q X (k (a.val.signExtend 32, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.sext 8 32) (a, ())) k) m := by
  simpa only [wp_let_sext_eq] using ⟨by decide, h⟩
private theorem pa_wp_trunc64_32 {a : Arg Val (.bits 64)} {k : K (.bits 32)}
    (h : wp Γ Q X (k (a.val.setWidth 32, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.trunc 64 32) (a, ())) k) m := by
  simpa only [wp_let_trunc_eq] using ⟨by decide, h⟩
private theorem pa_wp_cmp {o n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : wp Γ Q X (k (o.evalBits a.val b.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp o (.bits n) .bool rfl) (a, b, ())) k) m := by
  simpa only [wp_let_cmp_eq, Ty.hasFloat, Bool.false_eq_true, ↓reduceIte, cast_eq, liftCmp] using h
private theorem pa_wp_cmp_eq {n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : wp Γ Q X (k ((a.val == b.val), ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .eq (.bits n) .bool rfl) (a, b, ())) k) m :=
  pa_wp_cmp (evalBits_eq_beq a.val b.val ▸ h)
private theorem pa_wp_cmp_ne {n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : wp Γ Q X (k ((a.val != b.val), ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .ne (.bits n) .bool rfl) (a, b, ())) k) m :=
  pa_wp_cmp (evalBits_ne_bne a.val b.val ▸ h)
private theorem pa_wp_cmp_ult {n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : wp Γ Q X (k (a.val.ult b.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .ult (.bits n) .bool rfl) (a, b, ())) k) m :=
  pa_wp_cmp (evalBits_ult_eq a.val b.val ▸ h)
private theorem pa_wp_cmp_ule {n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : wp Γ Q X (k (a.val.ule b.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .ule (.bits n) .bool rfl) (a, b, ())) k) m :=
  pa_wp_cmp (evalBits_ule_eq a.val b.val ▸ h)
private theorem pa_wp_cmp_ugt {n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : wp Γ Q X (k (b.val.ult a.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .ugt (.bits n) .bool rfl) (a, b, ())) k) m :=
  pa_wp_cmp (evalBits_ugt_eq a.val b.val ▸ h)
private theorem pa_wp_cmp_uge {n} {a b : Arg Val (.bits n)} {k : K .bool}
    (h : wp Γ Q X (k (b.val.ule a.val, ())) m) :
    wp Γ Q X (.let_ (Op.mk (.cmp .uge (.bits n) .bool rfl) (a, b, ())) k) m :=
  pa_wp_cmp (evalBits_uge_eq a.val b.val ▸ h)
private theorem pa_wp_jump0 {L : Cont []} (h : L () m) : wp (rs := rs) Γ Q X (.jump L ()) m := h
private theorem pa_wp_jump1 {t} {L : Cont [t]} {a : Arg Val t} (h : L (a.val, ()) m) :
    wp (rs := rs) Γ Q X (.jump L (a, ())) m := h
private theorem pa_wp_jump2 {t1 t2} {L : Cont [t1, t2]} {a : Arg Val t1} {b : Arg Val t2}
    (h : L (a.val, b.val, ()) m) : wp (rs := rs) Γ Q X (.jump L (a, b, ())) m := h
end PaWp
private theorem pa_wp_ret1 {Γ X m t} {Q : Post [t]} {a : Arg Val t} (h : Q (a.val, ()) m) :
    wp Γ Q X (.ret (a, ())) m := h

private meta def paReduceProjOnce (e : Lean.Expr) : Lean.Expr :=
  e.replace fun sub =>
    match sub with
    | .proj ``Prod 0 arg => if arg.isAppOfArity ``Prod.mk 4 then some (arg.getArg! 2) else none
    | .proj ``Prod 1 arg => if arg.isAppOfArity ``Prod.mk 4 then some (arg.getArg! 3) else none
    | _ =>
      if sub.isAppOfArity ``Prod.fst 3 && sub.appArg!.isAppOfArity ``Prod.mk 4 then
        some (sub.appArg!.getArg! 2)
      else if sub.isAppOfArity ``Prod.snd 3 && sub.appArg!.isAppOfArity ``Prod.mk 4 then
        some (sub.appArg!.getArg! 3)
      else if sub.isAppOf ``Arg.val && sub.getAppNumArgs ≥ 1 then
        let arg := sub.appArg!
        if (arg.isAppOf ``Arg.var || arg.isAppOf ``Arg.imm) && arg.getAppNumArgs ≥ 1 then
          some arg.appArg!
        else none
      else none

private meta def paReduceHeadE (e : Lean.Expr) : Lean.Expr :=
  paReduceProjOnce (paReduceProjOnce (paReduceProjOnce e.headBeta))
private meta def paNormWpGoal (g : Lean.MVarId) : Lean.Elab.Tactic.TacticM Lean.MVarId := do
  let ty := (← Lean.instantiateMVars (← g.getType)).headBeta
  if ty.isAppOf ``wp && ty.getAppNumArgs == 6 then
    let e := ty.getArg! 4; let e' := paReduceHeadE e
    if e' != e then return ← g.change (Lean.mkAppN ty.getAppFn (ty.getAppArgs.set! 4 e'))
  return g
private meta def paBvLit (w v : Nat) : Lean.Expr :=
  Lean.mkApp2 (Lean.mkConst ``BitVec.ofNat) (Lean.mkNatLit w) (Lean.mkNatLit v)
private meta def paFastLetLemma? (op : Lean.Expr) : Option Lean.Name :=
  if op.isAppOf ``Op.mk && op.getAppNumArgs == 5 then
    let code := op.getArg! 3; let args := op.getArg! 4
    let hasImm1 := args.isAppOfArity ``Prod.mk 4 && (args.getArg! 2).isAppOf ``Arg.imm
    let hasImm2 := hasImm1 && (args.getArg! 3).isAppOfArity ``Prod.mk 4 &&
      ((args.getArg! 3).getArg! 2).isAppOf ``Arg.imm
    match code.getAppFn.constName? with
    | some ``OpCode.copy => some ``pa_wp_copy
    | some ``OpCode.add => if hasImm2 then none else some ``pa_wp_add
    | some ``OpCode.sub => if hasImm2 then none else some ``pa_wp_sub
    | some ``OpCode.mul =>
      if hasImm2 then
        let a := (args.getArg! 2).appArg!
        if a == paBvLit 64 0 then some ``pa_wp_mul_0_4
        else if a == paBvLit 64 1 then some ``pa_wp_mul_1_4 else none
      else some ``pa_wp_mul
    | some ``OpCode.and => some ``pa_wp_and
    | some ``OpCode.or => some ``pa_wp_or
    | some ``OpCode.xor => some ``pa_wp_xor
    | some ``OpCode.lshr => some ``pa_wp_lshr1_32
    | some ``OpCode.zext =>
      if hasImm1 || code.getAppNumArgs != 2 then none
      else if (code.getArg! 0).nat? == some 32 && (code.getArg! 1).nat? == some 64 then
        some ``pa_wp_zext32_64
      else if (code.getArg! 0).nat? == some 8 && (code.getArg! 1).nat? == some 32 then
        some ``pa_wp_zext8_32
      else none
    | some ``OpCode.sext =>
      if code.getAppNumArgs != 2 then none
      else if (code.getArg! 0).nat? == some 32 && (code.getArg! 1).nat? == some 64 && hasImm1 then
        let a := (args.getArg! 2).appArg!
        if a == paBvLit 32 0 then some ``pa_wp_sext32_64_0
        else if a == paBvLit 32 1 then some ``pa_wp_sext32_64_1 else none
      else if !hasImm1 && (code.getArg! 0).nat? == some 8 && (code.getArg! 1).nat? == some 32 then
        some ``pa_wp_sext8_32
      else none
    | some ``OpCode.trunc =>
      if !hasImm1 && code.getAppNumArgs == 2 && (code.getArg! 0).nat? == some 64 &&
          (code.getArg! 1).nat? == some 32 then some ``pa_wp_trunc64_32 else none
    | some ``OpCode.cmp =>
      if code.getAppNumArgs == 4 then
        match (code.getArg! 0).getAppFn.constName? with
        | some ``CmpOp.eq => some ``pa_wp_cmp_eq | some ``CmpOp.ne => some ``pa_wp_cmp_ne
        | some ``CmpOp.ult => some ``pa_wp_cmp_ult | some ``CmpOp.ule => some ``pa_wp_cmp_ule
        | some ``CmpOp.ugt => some ``pa_wp_cmp_ugt | some ``CmpOp.uge => some ``pa_wp_cmp_uge
        | _ => none
      else none
    | _ => none
  else none

private meta def paClearStale (m0 : Lean.Expr) : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
    let .fvar mId := m0 | return
    for d in (← Lean.getLCtx).decls.toArray.reverse do
      let some d := d | continue
      let t ← Lean.instantiateMVars d.type
      if t.isAppOf ``Std.ExtHashMap.sep && t.appArg! == m0 then
        try Lean.Elab.Tactic.liftMetaTactic1 fun g => some <$> g.clear d.fvarId catch _ => pure ()
    try Lean.Elab.Tactic.liftMetaTactic1 fun g => some <$> g.clear mId catch _ => pure ()
private meta def paFindJoinHyp (J : Lean.FVarId) :
    Lean.Elab.Tactic.TacticM (Option Lean.Expr) :=
  Lean.Elab.Tactic.withMainContext do
    for d in (← Lean.getLCtx).decls.toArray.reverse do
      let some d := d | continue
      let ok ← Lean.Meta.forallTelescopeReducing d.type fun xs concl => do
        if xs.size < 1 then return false
        return concl.getAppFn.isFVarOf J && (← Lean.Meta.inferType xs[xs.size - 1]!).isAppOf ``wp
      if ok then return some d.toExpr
    return none
private meta def paStepOnce (unrollGroup : Bool := true) : Lean.Elab.Tactic.TacticM Bool :=
  Lean.Elab.Tactic.withMainContext do
    let g ← Lean.Elab.Tactic.getMainGoal
    let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData.headBeta
    if ty.isAppOf ``And then
      let s ← Lean.Elab.Tactic.saveState
      try Lean.Elab.Tactic.evalTactic (← `(tactic| refine strip_le_wp (by decide) ?_)); return true
      catch _ => s.restore; return false
    if ty.isAppOf ``wp && ty.getAppNumArgs == 6 then
      let e := (ty.getArg! 4).consumeMData.headBeta
      match e.getAppFn.constName? with
      | some ``Expr.let_ =>
        if e.getAppNumArgs != 6 then return false
        if let some lem := paFastLetLemma? (e.getArg! 4).headBeta then
          let s ← Lean.Elab.Tactic.saveState
          try
            let [hk] ← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels lem)
              | s.restore; return false
            Lean.Elab.Tactic.setGoals [← paNormWpGoal hk]; return true
          catch _ => s.restore
        let s ← Lean.Elab.Tactic.saveState
        try Lean.Elab.Tactic.evalTactic (← `(tactic| c0_let_simp)); return true
        catch _ => s.restore; return false
      | some ``Expr.load =>
        let s ← Lean.Elab.Tactic.saveState
        try
          let [hl, hk] := (← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels ``wp_load_of)).take 2
            | s.restore; return false
          LeanQbe.T.C0Step.memSolve true hl
          Lean.Elab.Tactic.setGoals [← paNormWpGoal hk]; return true
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
          paClearStale m0; return true
        catch _ => s.restore; return false
      | some ``Expr.jnz =>
        let hc := Lean.mkIdent `hc
        Lean.Elab.Tactic.evalTactic (← `(tactic|
          (refine wp_jnz_of (fun $hc:ident => ?_) (fun $hc:ident => ?_)) <;> (
            try simp only [Arg.val_var, Arg.val_imm] at $hc:ident; c0_cond $hc
            try (first | exact ($hc).elim | exact absurd rfl $hc | exact $hc rfl
                       | exact absurd trivial $hc))))
        return true
      | some ``Expr.jump | some ``Expr.ret =>
        let lems := if e.isAppOf ``Expr.ret then #[``pa_wp_ret1]
          else #[``pa_wp_jump0, ``pa_wp_jump1, ``pa_wp_jump2]
        for lem in lems do
          let s2 ← Lean.Elab.Tactic.saveState
          try
            let [hk] ← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels lem) | s2.restore; continue
            let hkTy ← Lean.instantiateMVars (← hk.getType)
            let hkTy' := paReduceProjOnce (paReduceProjOnce hkTy)
            Lean.Elab.Tactic.setGoals [← if hkTy' != hkTy then hk.change hkTy' else pure hk]
            return true
          catch _ => s2.restore
        return false
      | some ``Expr.group =>
        if unrollGroup && e.getAppNumArgs == 6 then
          if let .lam _ _ b _ := e.getArg! 4 then
            if !b.hasLooseBVars then
              let J := Lean.mkIdent `J; let hJ := Lean.mkIdent `hJ
              Lean.Elab.Tactic.evalTactic (← `(tactic|
                refine wp_unroll_group fun $J:ident $hJ:ident => ?_))
              return true
        return false
      | some ``Blocks.get =>
        if e.getAppNumArgs == 8 then
          let bs := (e.getArg! 5).headBeta
          if bs.isAppOf ``Blocks.cons && bs.getAppNumArgs == 7 &&
              (e.getArg! 6).isAppOf ``Member.here then
            let newE := paReduceHeadE (Lean.mkApp (bs.getArg! 5) (e.getArg! 7))
            let newTy := Lean.mkAppN ty.getAppFn (ty.getAppArgs.set! 4 newE)
            Lean.Elab.Tactic.setGoals [← g.change newTy]; return true
        return false
      | _ => return false
    if let .fvar J := ty.getAppFn then
      if let some h ← paFindJoinHyp J then
        Lean.Elab.Tactic.setGoals (← (← g.apply h).mapM paNormWpGoal); return true
    return false

private meta partial def paStepsLoop (unrollGroup : Bool) (fuel : Nat) :
    Lean.Elab.Tactic.TacticM Unit := do
  if fuel = 0 then return
  let mut out : Array Lean.MVarId := #[]
  for g in (← Lean.Elab.Tactic.getUnsolvedGoals) do
    if ← g.isAssigned then continue
    Lean.Elab.Tactic.setGoals [g]
    if ← paStepOnce unrollGroup then paStepsLoop unrollGroup (fuel - 1)
    out := out ++ (← Lean.Elab.Tactic.getUnsolvedGoals)
  Lean.Elab.Tactic.setGoals out.toList

/-- O(1)-per-step symbolic executor avoiding `simp` over `Expr.let_` continuations. -/
local elab "pa_steps" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| try (first | refine strip_fwp ?_ | refine strip_wp ?_)))
  paStepsLoop true 2000

local elab "pa_steps_nogrp" : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| try (first | refine strip_fwp ?_ | refine strip_wp ?_)))
  paStepsLoop false 2000

/-! ## 2. Factored exit and semantic helpers for `plain_analyze` -/

private theorem analyze_ret_ok {c : PlainCfg} {F0 : CNF Nat} {s s' : PlainState}
    {R : Mem 64 → Prop} {Q : Post [i64]} {m' : Mem 64}
    (hQ : ∀ r vals' lvl' rsns' trl' tp' te' prop' cl' fuel' tc' tl' mrk' tmp' wvec' arena' alen'
      wstk' wlen' wu' ag' fr' ni' nr' nb' unfl' ctype' cref' c0' c1' oom' ms' mc' mcl' mcf' hr' m'',
      let st : PlainState := { s with
        vals := vals', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp', trail_end := te',
        propagated := prop', cur_level := cl', fuel := fuel', tmp_cnt := tc', tmp_len := tl',
        mrk := mrk', tmp := tmp', wvec := wvec', arena := arena', arena_len := alen',
        wstk := wstk', wlen := wlen', wusable := wu', arena_garbage := ag', first_reducible := fr',
        num_irred := ni', num_redundant := nr', num_binary := nb', unflushed := unfl',
        confl_type := ctype', confl_ref := cref', confl_lit0 := c0', confl_lit1 := c1', oom := oom',
        min_stk := ms', min_clr := mc', min_clr_len := mcl', min_clr_full := mcf', heur := hr' }
      st.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) → fuel'.toNat ≤ s.fuel.toNat →
      (∀ i < te', (trl'[i]?.getD 0#32).toNat < 2 * c.mv) → (r = 20#64 → F0.Unsat) →
      (r = 1#64 → PlainInv c F0 st ∧ cl' < s.cur_level) → (PlainMem c st ⋆ R) m'' → Q (r, ()) m'')
    (r : Val i64) (hl : s'.LengthsOk c) (hr : r = 0#64 ∨ r = 1#64 ∨ r = 20#64)
    (hfu : s'.fuel.toNat ≤ s.fuel.toNat)
    (htrl : ∀ i < s'.trail_end, (s'.trl[i]?.getD 0#32).toNat < 2 * c.mv)
    (hu : r = 20#64 → F0.Unsat) (hi : r = 1#64 → PlainInv c F0 s' ∧ s'.cur_level < s.cur_level)
    (hm' : (PlainMem c s' ⋆ R) m')
    (hd1 : s'.d_cur = s.d_cur) (hd2 : s'.d_val = s.d_val) (hpr : s'.probing = s.probing) :
    Q (r, ()) m' := by
  have heq : s' = { s with
    vals := s'.vals, lvl := s'.lvl, rsns := s'.rsns, trl := s'.trl, trail_pos := s'.trail_pos,
    trail_end := s'.trail_end, propagated := s'.propagated, cur_level := s'.cur_level,
    fuel := s'.fuel, tmp_cnt := s'.tmp_cnt, tmp_len := s'.tmp_len, mrk := s'.mrk, tmp := s'.tmp,
    wvec := s'.wvec, arena := s'.arena, arena_len := s'.arena_len, wstk := s'.wstk, wlen := s'.wlen,
    wusable := s'.wusable, arena_garbage := s'.arena_garbage, first_reducible := s'.first_reducible,
    num_irred := s'.num_irred, num_redundant := s'.num_redundant, num_binary := s'.num_binary,
    unflushed := s'.unflushed, confl_type := s'.confl_type, confl_ref := s'.confl_ref,
    confl_lit0 := s'.confl_lit0, confl_lit1 := s'.confl_lit1, oom := s'.oom, min_stk := s'.min_stk,
    min_clr := s'.min_clr, min_clr_len := s'.min_clr_len, min_clr_full := s'.min_clr_full,
    heur := s'.heur } := by
    cases s'; cases s; simp only at hd1 hd2 hpr; subst hd1 hd2 hpr; rfl
  exact hQ r _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m'
    (heq ▸ hl) hr hfu htrl hu (fun h => by obtain ⟨h1, h2⟩ := hi h; exact ⟨heq ▸ h1, h2⟩)
    (heq ▸ hm')

private theorem analyze_bin_seed_sem {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hinv : PlainInv c F0 s) {mrk_a mrk_b : List (BitVec 8)} {tmp_a tmp_b : List (BitVec 32)}
    {tc_a tc_b tl_a tl_b : Nat}
    (hl0_lt : s.confl_lit0.toNat < 2 * c.mv) (hl1_lt : s.confl_lit1.toNat < 2 * c.mv)
    (hent_bin : F0.EntailsClause (cnfClause [s.confl_lit0.toNat, s.confl_lit1.toNat]))
    (hf0 : s.vals[s.confl_lit0.toNat]?.getD 0#8 = 0xFF#8)
    (hf1 : s.vals[s.confl_lit1.toNat]?.getD 0#8 = 0xFF#8)
    (htla_ge : 1 ≤ tl_a) (htla_mv : tl_a ≤ c.mv) (htlb_ge : tl_a ≤ tl_b) (htlb_mv : tl_b ≤ c.mv)
    (htcb_ge : tc_a ≤ tc_b) (hta_l : tmp_a.length = c.mv) (htb_l : tmp_b.length = c.mv)
    (htca_eq : let v0 := (s.confl_lit0.setWidth 32).toNat / 2
      tc_a = 0 + if v0 < c.mv ∧ s.mrk[v0]?.getD 0#8 = 0#8 ∧ mrk_a[v0]?.getD 0#8 ≠ 0#8 ∧
        (s.lvl[v0]?.getD 0#32).toNat = s.cur_level then 1 else 0)
    (hmp_a : ∀ v < c.mv, s.mrk[v]?.getD 0#8 ≠ 0#8 → mrk_a[v]?.getD 0#8 = s.mrk[v]?.getD 0#8)
    (htp_a : ∀ k < 1, tmp_a[k]? = s.tmp[k]?)
    (hnm_a : ∀ v < c.mv, s.mrk[v]?.getD 0#8 = 0#8 → mrk_a[v]?.getD 0#8 ≠ 0#8 →
      (s.confl_lit0.setWidth 32).toNat / 2 = v ∧ v ≠ (0xFFFFFFFF#32).toNat ∧
      0 < (s.lvl[v]?.getD 0#32).toNat ∧ (s.lvl[v]?.getD 0#32).toNat ≤ s.cur_level)
    (hnt_a : let l0 := s.confl_lit0.setWidth 32; let v0 := l0.toNat / 2
      ∀ j, 1 ≤ j → j < tl_a → (tmp_a[j]?.getD 0#32).toNat = l0.toNat ∧ v0 < c.mv ∧
        v0 ≠ (0xFFFFFFFF#32).toNat ∧ s.mrk[v0]?.getD 0#8 = 0#8 ∧
        0 < (s.lvl[v0]?.getD 0#32).toNat ∧ (s.lvl[v0]?.getD 0#32).toNat < s.cur_level ∧
        mrk_a[v0]?.getD 0#8 ≠ 0#8)
    (hok_a : let l0 := s.confl_lit0.setWidth 32; let v0 := l0.toNat / 2
      v0 < c.mv ∧ (v0 ≠ (0xFFFFFFFF#32).toNat →
        (0 < (s.lvl[v0]?.getD 0#32).toNat → mrk_a[v0]?.getD 0#8 ≠ 0#8) ∧
        (s.mrk[v0]?.getD 0#8 = 0#8 → (s.lvl[v0]?.getD 0#32).toNat ≤ s.cur_level ∧
          (0 < (s.lvl[v0]?.getD 0#32).toNat → (s.lvl[v0]?.getD 0#32).toNat = s.cur_level →
            tc_a = 0 + 1) ∧
          (0 < (s.lvl[v0]?.getD 0#32).toNat → (s.lvl[v0]?.getD 0#32).toNat < s.cur_level →
            tl_a = 1 + 1 ∧ tmp_a[1]? = some l0))))
    (htcb_eq : let v1 := (s.confl_lit1.setWidth 32).toNat / 2
      tc_b = tc_a + if v1 < c.mv ∧ mrk_a[v1]?.getD 0#8 = 0#8 ∧ mrk_b[v1]?.getD 0#8 ≠ 0#8 ∧
        (s.lvl[v1]?.getD 0#32).toNat = s.cur_level then 1 else 0)
    (hmp_b : ∀ v < c.mv, mrk_a[v]?.getD 0#8 ≠ 0#8 → mrk_b[v]?.getD 0#8 = mrk_a[v]?.getD 0#8)
    (htp_b : ∀ k < tl_a, tmp_b[k]? = tmp_a[k]?)
    (hnm_b : ∀ v < c.mv, mrk_a[v]?.getD 0#8 = 0#8 → mrk_b[v]?.getD 0#8 ≠ 0#8 →
      (s.confl_lit1.setWidth 32).toNat / 2 = v ∧ v ≠ (0xFFFFFFFF#32).toNat ∧
      0 < (s.lvl[v]?.getD 0#32).toNat ∧ (s.lvl[v]?.getD 0#32).toNat ≤ s.cur_level)
    (hnt_b : let l1 := s.confl_lit1.setWidth 32; let v1 := l1.toNat / 2
      ∀ j, tl_a ≤ j → j < tl_b → (tmp_b[j]?.getD 0#32).toNat = l1.toNat ∧ v1 < c.mv ∧
        v1 ≠ (0xFFFFFFFF#32).toNat ∧ mrk_a[v1]?.getD 0#8 = 0#8 ∧
        0 < (s.lvl[v1]?.getD 0#32).toNat ∧ (s.lvl[v1]?.getD 0#32).toNat < s.cur_level ∧
        mrk_b[v1]?.getD 0#8 ≠ 0#8)
    (hok_b : let l1 := s.confl_lit1.setWidth 32; let v1 := l1.toNat / 2
      v1 < c.mv ∧ (v1 ≠ (0xFFFFFFFF#32).toNat →
        (0 < (s.lvl[v1]?.getD 0#32).toNat → mrk_b[v1]?.getD 0#8 ≠ 0#8) ∧
        (mrk_a[v1]?.getD 0#8 = 0#8 → (s.lvl[v1]?.getD 0#32).toNat ≤ s.cur_level ∧
          (0 < (s.lvl[v1]?.getD 0#32).toNat → (s.lvl[v1]?.getD 0#32).toNat = s.cur_level →
            tc_b = tc_a + 1) ∧
          (0 < (s.lvl[v1]?.getD 0#32).toNat → (s.lvl[v1]?.getD 0#32).toNat < s.cur_level →
            tl_b = tl_a + 1 ∧ tmp_b[tl_a]? = some l1)))) :
    tc_b = (curTrailIdxs s mrk_b s.trail_end).length ∧ LowerInv c s tmp_b mrk_b tl_b ∧
    MarksCov c s tmp_b mrk_b tl_b ∧
    F0.EntailsClause (cnfClause (activeResolvent s tmp_b mrk_b tl_b s.trail_end)) := by
  have hcore := hinv.core; have hmv := c.hmv; unfold dimacsBound at hmv
  have hl0_tr : (s.confl_lit0.setWidth 32).toNat = s.confl_lit0.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  have hl1_tr : (s.confl_lit1.setWidth 32).toNat = s.confl_lit1.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  have hct0 := curTrailIdxs_of_marksClear hinv
  have hcnt_a := filter_step_of_lit (fun _ _ _ => rfl) hmp_a
    (fun w hw h0 hnz => (hnm_a w hw h0 hnz).1) (Nat.le_refl _)
    (by rw [Nat.sub_self, List.filter_eq_nil_iff.mpr (fun _ _ => by simp)]; rfl) htca_eq
  obtain ⟨htca_eq', hlow_a, hcov_a, _, _, hq_a⟩ :=
    analyzeStep_preserves hcore (· = s.confl_lit0.toNat) (Nat.le_refl _) (Nat.le_refl _)
      htla_ge htla_mv hcore.lengths.tmp_len_arr hta_l hct0.symm (Nat.zero_le _)
      (fun _ h1 h2 => by omega) (fun v hv hnz => absurd (hinv.marks v hv) hnz)
      (fun _ e => e ▸ hl0_lt) (fun _ e => Or.inr (e ▸ (hcore.vals_false_iff _ hl0_lt).mp hf0))
      hmp_a htp_a (fun v h h0 z => let ⟨e, r⟩ := hnm_a v h h0 z; ⟨_, rfl, by rwa [← hl0_tr], r⟩)
      (fun j h1 h2 => let ⟨e, a, b, _, p, cl, hmk⟩ := hnt_a j h1 h2
        ⟨by rw [e, hl0_tr], by omega, by rwa [e], by rwa [e], by rwa [e], by rwa [e]⟩)
      hcnt_a (fun l hl => by
        subst l; rw [← hl0_tr]; refine ⟨hok_a.1, fun hne' => ⟨(hok_a.2 hne').1, fun h0 => ?_⟩⟩
        obtain ⟨hle, _, hlow⟩ := (hok_a.2 hne').2 h0
        exact ⟨hle, fun hp hlt =>
          let ⟨_, ht⟩ := hlow hp hlt; ⟨1, Nat.le_refl _, by omega, by rw [ht]; rfl⟩⟩)
  have hcnt_b := filter_step_of_lit (fun _ _ _ => rfl) hmp_b
    (fun w hw h0 hnz => (hnm_b w hw h0 hnz).1) (Nat.le_refl _)
    (by rw [Nat.sub_self, List.filter_eq_nil_iff.mpr (fun _ _ => by simp)]; rfl) htcb_eq
  obtain ⟨htcb_eq', hlow_b, hcov_b, hlow_sub, hcur_sub, hq_b⟩ :=
    analyzeStep_preserves hcore (· = s.confl_lit1.toNat) (Nat.le_refl _) htla_ge htlb_ge
      htlb_mv hta_l htb_l htca_eq' htcb_ge hlow_a hcov_a (fun _ heq => heq ▸ hl1_lt)
      (fun _ heq => Or.inr (heq ▸ (hcore.vals_false_iff _ hl1_lt).mp hf1)) hmp_b htp_b
      (fun v hv h0 hz => let ⟨e, hr⟩ := hnm_b v hv h0 hz; ⟨_, rfl, by rwa [← hl1_tr], hr⟩)
      (fun j h1 h2 => let ⟨e, a, b, _, p, cl, hmk⟩ := hnt_b j h1 h2
        ⟨by rw [e, hl1_tr], by omega, by rwa [e], by rwa [e], by rwa [e], by rwa [e]⟩)
      hcnt_b (fun l hl => by
        subst l; rw [← hl1_tr]; refine ⟨hok_b.1, fun hne' => ⟨(hok_b.2 hne').1, fun h0 => ?_⟩⟩
        obtain ⟨hle, _, hlow⟩ := (hok_b.2 hne').2 h0
        exact ⟨hle, fun hp hlt =>
          let ⟨_, ht⟩ := hlow hp hlt; ⟨tl_a, Nat.le_refl _, by omega, by rw [ht]; rfl⟩⟩)
  refine ⟨htcb_eq', hlow_b, hcov_b, entails_of_mem_or_false hent_bin fun q hq => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl
  · rcases hq_a s.confl_lit0.toNat rfl with _ | hmem | hf
    · have : (0xFFFFFFFF#32).toNat = 2 ^ 32 - 1 := rfl; omega
    · exact Or.inl ((List.mem_append.mp hmem).elim (fun h => List.mem_append_left _ (hlow_sub _ h))
        (fun h => List.mem_append_right _ (hcur_sub _ h)))
    · exact Or.inr hf
  · rcases hq_b s.confl_lit1.toNat rfl with _ | hmem | hf
    · have : (0xFFFFFFFF#32).toNat = 2 ^ 32 - 1 := rfl; omega
    · exact Or.inl hmem
    · exact Or.inr hf

/-! ## 3. `plain_analyze` (`plainAnalyzeSpec`) -/

private theorem bv64_sub1_toNat {n : Nat} (h1 : 0 < n) (h2 : n < 2 ^ 64) :
    (BitVec.ofNat 64 n - 1).toNat = n - 1 := by
  rw [show (1 : BitVec 64) = 1#64 from rfl]
  simp only [bv_c0, show (1#64 : BitVec 64).toNat = 1 from rfl]; omega
private theorem bv64_add1_ofNat (n : Nat) :
    BitVec.ofNat 64 n + (1 : BitVec 64) = BitVec.ofNat 64 (n + 1) := by
  apply BitVec.eq_of_toNat_eq; simp only [bv_c0, show (1 : BitVec 64).toNat = 1 from rfl]
private theorem bv64_sub1_raw {n : Nat} (h1 : 0 < n) (h2 : n < 2 ^ 64) :
    (2 ^ 64 - BitVec.toNat (1 : BitVec 64) + n) % 2 ^ 64 = n - 1 := by
  have : BitVec.toNat (1 : BitVec 64) = 1 := rfl; omega
private theorem bv64_ne_sentinel {n : Nat} (hn : n < 2 ^ 31 - 1) :
    BitVec.ofNat 64 n ≠ 0xFFFFFFFF#64 ∧ BitVec.ofNat 64 n ≠ 0xFFFFFFFE#64 :=
  ⟨fun h => by have := congrArg BitVec.toNat h; rw [bv64_ofNat_toNat (by omega)] at this
               have : (0xFFFFFFFF#64).toNat = 2 ^ 32 - 1 := rfl; omega,
   fun h => by have := congrArg BitVec.toNat h; rw [bv64_ofNat_toNat (by omega)] at this
               have : (0xFFFFFFFE#64).toNat = 2 ^ 32 - 2 := rfl; omega⟩
private theorem vals_getD_eq0 {vals : List (BitVec 8)} {u : BitVec 32} (hu : u.toNat < vals.length)
    (hz : vals[u.toNat % 2 ^ 64]'(by
      have := u.isLt; rw [Nat.mod_eq_of_lt (by omega)]; exact hu) = 0#8) :
    vals[u.toNat]?.getD 0#8 = 0#8 := by
  rw [List.getElem?_eq_getElem hu, Option.getD_some]
  have := u.isLt; simpa only [Nat.mod_eq_of_lt (by omega : u.toNat < 2 ^ 64)] using hz
private abbrev gcState (sbt : PlainState) (rsns_g : List (BitVec 32)) (prop_g : Nat)
    (wvec_g arena_g : List (BitVec 32)) (alen_g : Nat) (wstk_g : List (BitVec 32)) (wlen_g : Nat)
    (wu_g ag_g fred_g ni_g nr_g nb_g unfl_g fuel_g ctype_g cref_g c0_g c1_g oom_g : BitVec 64)
    (heur_g : PlainHeur) : PlainState :=
  { sbt with rsns := rsns_g, propagated := prop_g, wvec := wvec_g, arena := arena_g,
             arena_len := alen_g, wstk := wstk_g, wlen := wlen_g, wusable := wu_g,
             arena_garbage := ag_g, first_reducible := fred_g, num_irred := ni_g,
             num_redundant := nr_g, num_binary := nb_g, unflushed := unfl_g, fuel := fuel_g,
             confl_type := ctype_g, confl_ref := cref_g, confl_lit0 := c0_g, confl_lit1 := c1_g,
             oom := oom_g, heur := heur_g }

theorem plain_analyze_wp (Γ : Env)
    (hAlit : ∀ a m Q X, plainAnalyzeLitSpec a m Q X →
      Γ "plain_analyze_lit" [i64, i32, i32] [.bool] a m Q X)
    (hArsn : ∀ a m Q X, plainAnalyzeRsnSpec a m Q X →
      Γ "plain_analyze_rsn" [i64, i32, i32] [.bool] a m Q X)
    (hCm : ∀ a m Q X, plainClearMarksSpec a m Q X → Γ "plain_clear_marks" [i64, i64] [] a m Q X)
    (hBv : ∀ a m Q X, plainBumpVarSpec a m Q X → Γ "plain_bump_var" [i64, i32] [] a m Q X)
    (hQmtf : ∀ a m Q X, plainQueueMtfSpec a m Q X → Γ "plain_queue_mtf" [i64, i32] [] a m Q X)
    (hBd : ∀ a m Q X, plainBumpDecaySpec a m Q X → Γ "plain_bump_decay" [i64] [] a m Q X)
    (hMs : ∀ a m Q X, plainMinShrinkSpec a m Q X → Γ "plain_min_shrink" [i64] [] a m Q X)
    (hTr : ∀ a m Q X, plainTickRelSpec a m Q X → Γ "plain_tick_rel" [i64] [] a m Q X)
    (hEma : ∀ a m Q X, plainEmaUpdateSpec a m Q X → Γ "plain_ema_update" [i64, i64] [] a m Q X)
    (hBt : ∀ a m Q X, plainBacktrackSpec a m Q X → Γ "plain_backtrack" [i64, i64] [] a m Q X)
    (hAsgn : ∀ a m Q X, plainAssignSpec a m Q X → Γ "plain_assign" [i64, i32, i32] [] a m Q X)
    (hDefrag : ∀ a m Q X, plainWstackDefragSpec a m Q X → Γ "plain_wstack_defrag" [i64] [] a m Q X)
    (hRed : ∀ a m Q X, plainReduceSpec a m Q X → Γ "plain_reduce" [i64, .bool] [i64] a m Q X)
    (hAddCl : ∀ a m Q X, plainAddClauseSpec a m Q X →
      Γ "plain_add_clause" [i64, i32, i32, .bool] [i64] a m Q X) :
    ∀ args m Q X, plainAnalyzeSpec args m Q X → Func.wp Γ plain_analyze_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hconfl, hm, hQ⟩
  have hmv : c.mv < 2 ^ 28 := c.hmv
  have har_cap : c.arena_cap < 2 * 2 ^ 28 := c.harena
  have hcore := hinv.core; have hlen := hcore.lengths
  have hcur_le := hcore.cur_level_le; have hte_le := hlen.trail_end_le
  have hcur32 : s.cur_level < 2 ^ 32 := by omega
  have hret0 : ∀ (st : PlainState) (m' : Mem 64),
      st.LengthsOk c → st.fuel.toNat ≤ s.fuel.toNat →
      (∀ i < st.trail_end, (st.trl[i]?.getD 0#32).toNat < 2 * c.mv) →
      st.d_cur = s.d_cur → st.d_val = s.d_val → st.probing = s.probing →
      (PlainMem c st ⋆ R) m' → Q (0#64, ()) m' :=
    fun st m' hl hfu htrl hd1 hd2 hpr hm' =>
      analyze_ret_ok hQ 0#64 hl (Or.inl rfl) hfu htrl (fun hc => by cases hc)
        (fun hc => by cases hc) hm' hd1 hd2 hpr
  -- Step 1: `if (h->cur_level == 0ULL) { return 20ULL; }`
  unfold Func.wp plain_analyze_body
  pa_steps_nogrp
  · have hcl0 : s.cur_level = 0 := ofNat64_eq_zero (by omega) (by assumption)
    refine analyze_ret_ok hQ 20#64 hlen (Or.inr (Or.inr rfl)) (Nat.le_refl _)
      hcore.trail_lits_lt (fun _ => ?_) (fun hc => by cases hc) hm rfl rfl rfl
    rcases hconfl with ⟨_, h0, h1, hent, hf0, hf1⟩ | ⟨_, href, hng, hfals⟩
    · exact hcore.level0_unsat_of_bin_conflict hcl0 h0 h1 hent hf0 hf1
    · exact hcore.level0_unsat_of_conflict hcl0 href hng hfals
  have hcur_pos : 0 < s.cur_level := ofNat64_pos (by assumption)
  have hmv_pos : 1 ≤ c.mv := by omega
  -- Step 2: `h->tmp_cnt = 0ULL; h->tmp_len = 1ULL; seed_ok = ...`
  refine wp_join_group (ts := [.bool])
    (fun (seed_ok, ()) m_sd => ∃ mrk1 tmp1 tc1 tl1 arena1 heur1,
      let s1 : PlainState :=
        { s with mrk := mrk1, tmp := tmp1, tmp_cnt := tc1, tmp_len := tl1,
                 arena := arena1, heur := heur1 }
      PlainCoreInv c F0 s1 ∧ 1 ≤ tl1 ∧ tl1 ≤ c.mv ∧
      (seed_ok = true →
        tc1 = (curTrailIdxs s mrk1 s.trail_end).length ∧
        LowerInv c s tmp1 mrk1 tl1 ∧ MarksCov c s tmp1 mrk1 tl1 ∧
        F0.EntailsClause (cnfClause (activeResolvent s tmp1 mrk1 tl1 s.trail_end))) ∧
      (PlainMem c s1 ⋆ R) m_sd) ?_ ?_
  · -- Post-seed continuation
    rintro _ ⟨seed_ok, ⟨⟩⟩ m_sd ⟨mrk1, tmp1, tc1, tl1, arena1, heur1,
      hcore1, htl1_ge1, htl1_mv, hsd_ok, hm_sd⟩
    have hfail_cm : ∀ (st : PlainState) (mf : Mem 64),
        st.LengthsOk c → st.tmp_len ≤ c.mv → st.fuel.toNat ≤ s.fuel.toNat →
        (∀ i < st.trail_end, (st.trl[i]?.getD 0#32).toNat < 2 * c.mv) →
        st.d_cur = s.d_cur → st.d_val = s.d_val → st.probing = s.probing →
        (PlainMem c st ⋆ R) mf →
        wp Γ Q X
          (Expr.call (rs := [i64]) (as := [i64, i64]) (bs := []) "plain_clear_marks"
            (Arg.var c.hdr, Arg.imm 0#64, ())
            fun _ => Expr.ret (rs := [i64]) (Arg.imm 0#64, ())) mf := by
      intro st mf hsfl htlf hfu htrl hd1 hd2 hpr hmf
      refine wp_call_of_spec _ _ (hCm _ _ _ _ ⟨c, st, R, rfl, hsfl, htlf, hmf,
        fun mrk_c m_c hmc_l _ _ _ hm_c => ?_⟩)
      wp_unfold
      exact hret0 { st with mrk := mrk_c } m_c { hsfl with mrk_len := hmc_l } hfu htrl
        hd1 hd2 hpr hm_c
    cases seed_ok with
    | false =>
      pa_steps
      exact hfail_cm _ m_sd hcore1.lengths htl1_mv (Nat.le_refl _) hcore.trail_lits_lt
        rfl rfl rfl hm_sd
    | true =>
      obtain ⟨htc1_eq, hlow1, hcov1, hent1⟩ := hsd_ok rfl
      have htc1_le_mv : tc1 ≤ c.mv := by
        rw [htc1_eq]; exact Nat.le_trans (List.length_filter_le _ _) (by simp; omega)
      pa_steps
      · -- `h->tmp_cnt == 0ULL`
        have htc1_0 : tc1 = 0 := ofNat64_eq_zero (by omega) (by assumption)
        refine wp_call_of_spec _ _ (hCm _ _ _ _ ⟨c, _, R, rfl, hcore1.lengths, htl1_mv, hm_sd,
          fun mrk_z m_z hmlz _ _ _ hm_z => ?_⟩)
        let sz : PlainState :=
          { s with mrk := mrk_z, tmp := tmp1, tmp_cnt := tc1, tmp_len := tl1,
                   arena := arena1, heur := heur1 }
        have hlen_z : sz.LengthsOk c := { hcore1.lengths with mrk_len := hmlz }
        pa_steps
        · have htl_is1 : tl1 = 1 := ofNat64_eq_one (by omega) (by assumption)
          refine analyze_ret_ok hQ 20#64 hlen_z
            (Or.inr (Or.inr rfl)) (Nat.le_refl _) hcore.trail_lits_lt (fun _ => ?_)
            (fun hc => by cases hc) hm_z rfl rfl rfl
          have hres_nil : activeResolvent s tmp1 mrk1 tl1 s.trail_end = [] := by
            unfold activeResolvent lowerLits curLits
            have hct_nil : curTrailIdxs s mrk1 s.trail_end = [] :=
              List.eq_nil_of_length_eq_zero (by rw [← htc1_eq]; exact htc1_0)
            simp [htl_is1, hct_nil]
          rw [hres_nil] at hent1; exact unsat_of_entails_nil hent1
        · exact hret0 sz m_z hlen_z (Nat.le_refl _) hcore.trail_lits_lt rfl rfl rfl hm_z
      · -- `h->tmp_cnt > 0`: post-1UIP continuation (`hJ_post`) + 1-UIP loop (`wp_loop_group`)
        have htc1_pos : 0 < tc1 := ofNat64_pos (by assumption)
        have hJ_post : ∀ idx mrk_b tmp_b tl_b arena_b heur_b p_bv mb,
            let sb : PlainState :=
              { s with mrk := mrk_b, tmp := tmp_b, tmp_cnt := 0, tmp_len := tl_b,
                       arena := arena_b, heur := heur_b }
            idx < s.trail_end → s.trl[idx]? = some p_bv →
            (s.lvl[p_bv.toNat / 2]?.getD 0#32).toNat = s.cur_level →
            PlainCoreInv c F0 sb → 1 ≤ tl_b → tl_b ≤ c.mv →
            (curTrailIdxs s mrk_b idx).length = 0 →
            LowerInv c s tmp_b mrk_b tl_b → MarksCov c s tmp_b mrk_b tl_b →
            F0.EntailsClause (cnfClause ((p_bv ^^^ 1#32).toNat :: lowerLits tmp_b tl_b)) →
            (PlainMem c sb ⋆ R) mb →
            J (BitVec.ofNat 64 idx, p_bv ^^^ 1#32, ()) mb := by
          intro idx mrk_b tmp_b tl_b arena_b heur_b p_bv mb sb
            hidx_lt hp_def hp_cl hcore_b htlb1 htlb_mv hct_b0 hlow_b hcov_b hent_b hmb
          clear hAlit hArsn hlow1 hcov1 hent1 htc1_eq htc1_pos htc1_le_mv htl1_ge1 htl1_mv
            hsd_ok hm_sd hcore1 hconfl hm
          apply hJ
          have hp_lt : p_bv.toNat < 2 * c.mv := by
            have := hcore.trail_lits_lt idx hidx_lt; rwa [hp_def, Option.getD_some] at this
          let uip := p_bv ^^^ 1#32
          have huip_nat : uip.toNat = p_bv.toNat ^^^ 1 := bv32_xor_1 p_bv
          have huip_lt : uip.toNat < 2 * c.mv := huip_nat ▸ litNeg_lt_two_mul hp_lt
          have huip_ne : uip ≠ 0xFFFFFFFF#32 := fun heq => by
            have := congrArg BitVec.toNat heq
            have : (0xFFFFFFFF#32).toNat = 2 ^ 32 - 1 := rfl; omega
          have htb_len : tmp_b.length = c.mv := hcore_b.lengths.tmp_len_arr
          have h0_tmpb : 0 < tmp_b.length := by omega
          pa_steps
          · exact absurd hc huip_ne
          · let tmp0 := tmp_b.set 0 uip
            let st0 : PlainState := { s with
              mrk := mrk_b, tmp := tmp0, tmp_cnt := 0, tmp_len := tl_b, arena := arena_b,
              heur := heur_b }
            have hst0_len : st0.LengthsOk c :=
              { hcore_b.lengths with tmp_len_arr := by dsimp [st0, tmp0]; simp [htb_len] }
            have htmp0_gt0 : ∀ j, 1 ≤ j → tmp0[j]? = tmp_b[j]? := fun _ _ =>
              List.getElem?_set_ne (by omega)
            have hlow0 : LowerInv c s tmp0 mrk_b tl_b := fun j h1 h2 =>
              htmp0_gt0 j h1 ▸ hlow_b j h1 h2
            have hcov0 : MarksCov c s tmp0 mrk_b tl_b := fun v hv hnz =>
              (hcov_b v hv hnz).elim
                (fun ⟨j, h1, h2, e⟩ => Or.inl ⟨j, h1, h2, htmp0_gt0 j h1 ▸ e⟩) Or.inr
            have hlowLits0 : lowerLits tmp0 tl_b = lowerLits tmp_b tl_b := by
              change lowerLits (tmp_b.set 0 uip) tl_b = lowerLits tmp_b tl_b
              unfold lowerLits; cases tmp_b <;> rfl
            have htmp0_0 : tmp0[0]? = some uip := List.getElem?_set_self (by omega)
            refine wp_call_of_spec _ _ (hCm _ _ _ _ ⟨c, st0, R, rfl, hst0_len, htlb_mv, hm,
              fun mrk_c m_c hmcl hmc_pres hmc_clrt hmc_clrr hm_c => ?_⟩)
            let sc : PlainState := { s with
              mrk := mrk_c, tmp := tmp0, tmp_cnt := 0, tmp_len := tl_b, arena := arena_b,
              heur := heur_b }
            have hsc_core : PlainCoreInv c F0 sc :=
              same_core_plainCoreInv hcore_b hmcl (by simp [tmp0, htb_len]) htlb_mv
            have hsc_inv : PlainInv c F0 sc := ⟨hsc_core, clear_marks_restores_marksClear hcov0
              hct_b0 hmc_pres hmc_clrt ((bv64_ofNat_toNat (by omega : idx < 2 ^ 64)) ▸ hmc_clrr)⟩
            pa_steps
            -- Bump loop: `bi = 1 ..< tl_b`
            refine wp_loop_group (fun r (bi_v, ()) m_bi => ∃ bi heur_bi,
                1 ≤ bi ∧ bi ≤ tl_b ∧ r = tl_b - bi ∧ bi_v = BitVec.ofNat 64 bi ∧
                heur_bi.LengthsOk c ∧ (PlainMem c { sc with heur := heur_bi } ⋆ R) m_bi) ?_ ?_
            · rintro Lbi _ ⟨bi_v, ⟨⟩⟩ m_bi ih_bi ⟨bi, heur_bi, hbi1, hbile, rfl, rfl, hh_bi, hm_bi⟩
              pa_steps
              · have hbilt : bi < tl_b := by
                  have hlt : bi % 2 ^ 64 < tl_b % 2 ^ 64 := by assumption
                  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hlt
                have hbi_t : (BitVec.ofNat 64 bi).toNat < tmp0.length := by
                  rw [bv64_ofNat_toNat (by omega)]; simp [tmp0, htb_len]; omega
                pa_steps
                refine wp_call_of_spec _ _ (hBv _ _ _ _ ⟨c, { sc with heur := heur_bi }, R, rfl,
                  hsc_core.lengths.with_heur hh_bi, hm_bi, fun heur_bv m_bv hh_bv hm_bv => ?_⟩)
                pa_steps
                refine wp_call_of_spec _ _ (hQmtf _ _ _ _ ⟨c, { sc with heur := heur_bv }, R, rfl,
                  hsc_core.lengths.with_heur hh_bv, hm_bv, fun heur_qm m_qm hh_qm hm_qm => ?_⟩)
                pa_steps; rw [bv64_add1_ofNat]
                exact ih_bi (tl_b - (bi + 1)) _ _ (by omega)
                  ⟨bi + 1, heur_qm, by omega, by omega, rfl, rfl, hh_qm, hm_qm⟩
              · -- Post-bump loop: `plain_bump_decay`, `plain_min_shrink`, `plain_tick_rel`, glue
                refine wp_call_of_spec _ _ (hBd _ _ _ _ ⟨c, { sc with heur := heur_bi }, R, rfl,
                  hsc_core.lengths.with_heur hh_bi, hm_bi, fun heur_bd m_bd hh_bd hm_bd => ?_⟩)
                pa_steps
                have hbd_inv := hsc_inv.with_heur hh_bd
                have hent0 : F0.EntailsClause (cnfClause ((tmp0.take tl_b).map BitVec.toNat)) := by
                  rw [tmp_take_eq_cons_lowerLits htlb1 htmp0_0, hlowLits0]; exact hent_b
                have huip_fals : s.vals[uip.toNat]?.getD 0#8 = 0xFF#8 :=
                  (hcore.vals_false_iff uip.toNat huip_lt).mpr ⟨idx, hidx_lt, by
                    rw [hp_def, Option.getD_some, huip_nat]; exact (litNeg_litNeg _).symm⟩
                have hms_lits : ∀ k < tl_b, let l := (tmp0[k]?.getD 0#32).toNat
                    l < 2 * c.mv ∧ s.vals[l]?.getD 0#8 = 0xFF#8 := fun k hk => by
                  cases k with
                  | zero => rw [htmp0_0, Option.getD_some]; exact ⟨huip_lt, huip_fals⟩
                  | succ k' => let hlk := hlow0 (k' + 1) (by omega) hk; exact ⟨hlk.1, hlk.2.1⟩
                have hms_low : ∀ k, 1 ≤ k → k < tl_b → let l := (tmp0[k]?.getD 0#32).toNat
                    0 < (s.lvl[l / 2]?.getD 0#32).toNat ∧
                    (s.lvl[l / 2]?.getD 0#32).toNat < s.cur_level := fun k hk1 hk2 =>
                  let hlk := hlow0 k hk1 hk2; ⟨hlk.2.2.1, hlk.2.2.2.1⟩
                refine wp_call_of_spec _ _ (hMs (c.hdr, ()) _ _ _
                  ⟨c, F0, { sc with heur := heur_bd }, R, rfl, hbd_inv, htlb1, htlb_mv, hent0,
                    hms_lits, hms_low, hm_bd, ?_⟩)
                intro tmp_ms tl_ms mrk_ms mstk_ms mclr_ms mcl_ms mcf_ms heur_ms m_ms _
                  hms_inv htlms1 htlms_le htmpms_0 _ hms_post hent_ms hm_ms
                let sms : PlainState :=
                  { sc with tmp := tmp_ms, tmp_len := tl_ms, mrk := mrk_ms, min_stk := mstk_ms,
                            min_clr := mclr_ms, min_clr_len := mcl_ms, min_clr_full := mcf_ms,
                            heur := heur_ms }
                dsimp only [sc] at hms_inv htlms_le htmpms_0 hms_post hm_ms
                have htlms_mv : tl_ms ≤ c.mv := by omega
                have htmpms_0' : tmp_ms[0]? = some uip := htmpms_0.trans htmp0_0
                pa_steps
                refine wp_call_of_spec _ _ (hTr _ _ _ _ ⟨c, sms, R, rfl, hms_inv.core.lengths,
                  hm_ms, fun heur_tr m_tr hh_tr hm_tr => ?_⟩)
                let str : PlainState := { sms with heur := heur_tr }
                have hstr_inv : PlainInv c F0 str := hms_inv.with_heur hh_tr
                have hstr_len : str.LengthsOk c := hstr_inv.core.lengths
                have htms_len : tmp_ms.length = c.mv := hstr_len.tmp_len_arr
                pa_steps
                -- Glue loop (`gi = 1 ..< tl_ms`, read-only)
                refine wp_loop_group (fun r (glue_v, last_v, gi_v, ()) m_gi => ∃ gi,
                    1 ≤ gi ∧ gi ≤ tl_ms ∧ r = tl_ms - gi ∧ gi_v = BitVec.ofNat 64 gi ∧
                    (PlainMem c str ⋆ R) m_gi) ?_ ?_
                · rintro Lgi _ ⟨glue_v, last_v, gi_v, ⟨⟩⟩ m_gi ih_gi ⟨gi, hgi1, hgile, rfl, rfl,
                    hm_gi⟩
                  pa_steps
                  · have hgilt : gi < tl_ms := by
                      have hlt : gi % 2 ^ 64 < tl_ms % 2 ^ 64 := by assumption
                      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hlt
                    have hgi_nat := bv64_ofNat_toNat (by omega : gi < 2 ^ 64)
                    have hgi_t : (BitVec.ofNat 64 gi).toNat < tmp_ms.length :=
                      hgi_nat.symm ▸ by omega
                    have hgi_v :
                        ((tmp_ms[(BitVec.ofNat 64 gi).toNat]'hgi_t >>> 1).setWidth 64).toNat <
                          s.lvl.length := by
                      rw [bv_c0_zext32_64, bv32_lshr_1, hlen.lvl_len,
                        getElem_eq_of_idx hgi_nat (hj := (by omega : gi < tmp_ms.length))]
                      have h1 := (hms_post gi hgi1 hgilt).1
                      rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h1; omega
                    pa_steps
                    all_goals
                      rw [bv64_add1_ofNat]
                      exact ih_gi (tl_ms - (gi + 1)) _ _ (by omega)
                        ⟨gi + 1, by omega, by omega, rfl, rfl, hm_gi⟩
                  · -- Post-glue loop: `plain_ema_update` then unit vs non-unit branch
                    refine wp_call_of_spec _ _ (hEma _ _ _ _ ⟨c, str, R, rfl, hstr_len, hm_gi,
                      fun heur_em m_em hh_em _ hm_em => ?_⟩)
                    let sem : PlainState := { str with heur := heur_em }
                    have hsem_inv : PlainInv c F0 sem := hstr_inv.with_heur hh_em
                    have hsem_len : sem.LengthsOk c := hsem_inv.core.lengths
                    pa_steps
                    · -- Unit learned clause (`tl_ms == 1`, lines 903-908)
                      have htl_is1 : tl_ms = 1 := ofNat64_eq_one (by omega) (by assumption)
                      have hent_unit : F0.EntailsClause (cnfClause [uip.toNat]) := by
                        rw [tmp_take_eq_cons_lowerLits htlms1 htmpms_0'] at hent_ms
                        have hnil : lowerLits tmp_ms tl_ms = [] := by
                          unfold lowerLits; simp [htl_is1]
                        rwa [hnil] at hent_ms
                      refine wp_call_of_spec _ _ (hBt (c.hdr, 0#64, ()) _ _ _
                        ⟨c, sem, R, rfl, hsem_len, hsem_inv.core.trail_lits_lt, hm_em, ?_⟩)
                      intro vals_bt lvl_bt rsns_bt te_bt prop_bt heur_bt m_bt _
                        hbt_len hbt_te_le hbt_prop_le _ _ hbt_cond hm_bt
                      obtain ⟨hbt_core, _⟩ := hbt_cond F0 hsem_inv.core (Nat.zero_le _)
                      let sbt : PlainState :=
                        { sem with vals := vals_bt, lvl := lvl_bt, rsns := rsns_bt,
                                   trail_end := te_bt, propagated := prop_bt,
                                   cur_level := 0, heur := heur_bt }
                      have huip_vlen : uip.toNat < vals_bt.length := by
                        rw [hbt_len.vals_len]; exact huip_lt
                      pa_steps
                      · exact hret0 sbt m_bt hbt_len (Nat.le_refl _) hbt_core.trail_lits_lt
                          rfl rfl rfl hm_bt
                      · have huip_z : vals_bt[uip.toNat]?.getD 0#8 = 0#8 :=
                          vals_getD_eq0 huip_vlen (by assumption)
                        have hbt_te_lt : te_bt < c.mv :=
                          hbt_core.trail_end_lt_of_unassigned huip_lt huip_z
                        have hnot_oob : ¬ (c.mv ≤ uip.toNat / 2 ∨ c.mv ≤ te_bt) := by omega
                        refine wp_call_of_spec _ _ (hAsgn (c.hdr, uip, 0xFFFFFFFF#32, ()) _ _ _
                          ⟨c, sbt, R, rfl, hbt_len, by dsimp [sbt]; decide, hm_bt, ?_⟩)
                        dsimp only [sbt]; simp only [hnot_oob, ↓reduceIte]
                        intro phases' m_f hph hflen hm_f
                        pa_steps
                        have hfin_core := assign_preserves_core hbt_core (lit := uip)
                          (rsn := 0xFFFFFFFF#32) (unflushed' := s.unflushed + 1#64)
                          huip_lt hph huip_z (by change 0 ≤ te_bt + 1; omega)
                          (fun L h1 h2 => by change L ≤ 0 at h2; omega)
                          (fun _ => hent_unit) (fun _ hne => absurd rfl hne)
                          (fun _ hne _ => absurd rfl hne)
                        exact analyze_ret_ok hQ 1#64 hflen (Or.inr (Or.inl rfl)) (Nat.le_refl _)
                          hfin_core.trail_lits_lt (fun hc => by cases hc)
                          (fun _ => ⟨⟨hfin_core, hsem_inv.marks⟩, hcur_pos⟩) hm_f rfl rfl rfl
                    · -- Non-unit learned clause (`tl_ms ≥ 2`, lines 909-931)
                      clear hCm hBv hQmtf hBd hMs hTr hEma hlow0 hcov0 hlow_b hcov_b hent_b
                        hlowLits0 hsc_core hsc_inv hms_lits hms_low hbd_inv hent0
                        hstr_inv hstr_len hm_c hm_bi hm_bd hm_ms hm_tr
                      have htl_ge2 : 2 ≤ tl_ms := by
                        have hne : ¬ BitVec.ofNat 64 tl_ms = 1#64 := by assumption
                        have : tl_ms ≠ 1 := fun h1 => hne (by rw [h1]); omega
                      have h1_tms : 1 < tmp_ms.length := by omega
                      have hmi_lt : tl_ms - 1 < tmp_ms.length := by omega
                      have hmi_post := hms_post (tl_ms - 1) (by omega) (by omega)
                      let max_lvl : Nat :=
                        (s.lvl[(tmp_ms[tl_ms - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
                      have hml_pos : 0 < max_lvl := hmi_post.2.2.1
                      have hml_lt : max_lvl < s.cur_level := hmi_post.2.2.2.1
                      have hmi_eq : (BitVec.ofNat 64 tl_ms - 1).toNat = tl_ms - 1 :=
                        bv64_sub1_toNat (by omega) (by omega)
                      have hmi_t : (BitVec.ofNat 64 tl_ms - 1).toNat < tmp_ms.length := by
                        rw [hmi_eq]; exact hmi_lt
                      have hmi_v : (tmp_ms[tl_ms - 1]'hmi_lt).toNat / 2 < s.lvl.length := by
                        rw [hlen.lvl_len]; have h1 := hmi_post.1
                        rw [List.getElem?_eq_getElem hmi_lt, Option.getD_some] at h1; omega
                      have hmi_v' : ((tmp_ms[(BitVec.ofNat 64 tl_ms - 1).toNat]'hmi_t >>>
                          1).setWidth 64).toNat < s.lvl.length := by
                        rw [bv_c0_zext32_64, bv32_lshr_1]
                        rw [getElem_eq_of_idx hmi_eq (hj := hmi_lt)]; exact hmi_v
                      have hml_get : (s.lvl[(tmp_ms[tl_ms - 1]'hmi_lt).toNat / 2]'hmi_v).toNat =
                          max_lvl := by
                        dsimp only [max_lvl]; rw [List.getElem?_eq_getElem hmi_lt, Option.getD_some,
                          List.getElem?_eq_getElem hmi_v, Option.getD_some]
                      have hmi_t_set : (BitVec.ofNat 64 tl_ms - 1).toNat <
                          (tmp_ms.set 1 (tmp_ms[(BitVec.ofNat 64 tl_ms - 1).toNat]'hmi_t)).length :=
                        by simp only [List.length_set]; exact hmi_t
                      pa_steps
                      · exfalso
                        have h1 := bv64_sub1_raw (by omega : 0 < tl_ms) (by omega)
                        have hmod : (tmp_ms[tl_ms - 1]'hmi_lt).toNat / 2 % 2 ^ 64 =
                            (tmp_ms[tl_ms - 1]'hmi_lt).toNat / 2 := Nat.mod_eq_of_lt (by omega)
                        change s.cur_level % 2 ^ 64 % 2 ^ 32 % 2 ^ 64 ≤
                          (s.lvl[(tmp_ms[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) + tl_ms) %
                            2 ^ 64]'(by rw [h1]; exact hmi_lt)).toNat / 2 % 2 ^ 64]'(by
                              simp only [h1, hmod]; exact hmi_v)).toNat % 2 ^ 64 at hc
                        simp only [h1, hmod, hml_get,
                          Nat.mod_eq_of_lt (by omega : max_lvl < 2 ^ 64),
                          Nat.mod_eq_of_lt (by omega : s.cur_level < 2 ^ 64),
                          Nat.mod_eq_of_lt hcur32] at hc; omega
                      · let w1 := tmp_ms[1]'h1_tms
                        let wm := tmp_ms[tl_ms - 1]'hmi_lt
                        let tmp_sw := (tmp_ms.set 1 wm).set (tl_ms - 1) w1
                        let s_sw : PlainState := { sem with tmp := tmp_sw }
                        have hsw_len : tmp_sw.length = c.mv := by simp [tmp_sw, htms_len]
                        have hsw_core : PlainCoreInv c F0 s_sw :=
                          same_core_plainCoreInv hsem_inv.core hsem_len.mrk_len hsw_len
                            hsem_len.tmp_len_le
                        obtain ⟨hsw_iff, hsw_mem, _, _⟩ := swap_tmp_props htl_ge2 (by omega)
                          (by omega : 1 ≤ tl_ms - 1) (by omega : tl_ms - 1 < tl_ms) htmpms_0'
                        have hsw_get1 : tmp_sw[1]? = some wm :=
                          swap_tmp_get_1 htl_ge2 (by omega) (by omega) (by omega)
                        have hsw_get0 : tmp_sw[0]? = some uip := by
                          dsimp only [tmp_sw]
                          rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                          exact htmpms_0'
                        have hent_sw :
                            F0.EntailsClause (cnfClause ((tmp_sw.take tl_ms).map BitVec.toNat)) :=
                          entails_of_mem_or_false hent_ms fun l hl => Or.inl ((hsw_iff l).mpr hl)
                        have hsw_lits_lt : ∀ l ∈ (tmp_sw.take tl_ms).map BitVec.toNat,
                            l < 2 * c.mv := by
                          intro l hl
                          rcases hsw_mem l hl with rfl | ⟨j, hj1, hj2, hjeq⟩
                          · exact huip_lt
                          · rw [← hjeq]; exact (hms_post j hj1 hj2).1
                        have hm_sw : (PlainMem c s_sw ⋆ R) m := by
                          simpa only [s_sw, sem, str, sms, tmp_sw, w1, wm, hmi_eq,
                            show (1#64 : BitVec 64).toNat = 1 from rfl] using hm
                        have hml_bv :
                            (s.lvl[((tmp_ms[(BitVec.ofNat 64 tl_ms - 1).toNat]'hmi_t >>>
                              1).setWidth 64).toNat]'hmi_v').setWidth 64 =
                              BitVec.ofNat 64 max_lvl := by
                          apply BitVec.eq_of_toNat_eq
                          simp only [bv_c0, bv_c0_zext32_64, bv32_lshr_1, hmi_eq, hml_get,
                            Nat.mod_eq_of_lt (by omega : max_lvl < 2 ^ 64)]
                        rw [hml_bv]
                        refine wp_call_of_spec _ _
                          (hBt (c.hdr, BitVec.ofNat 64 max_lvl, ()) _ _ _
                            ⟨c, s_sw, R, rfl, hsw_core.lengths, hsw_core.trail_lits_lt, hm_sw, ?_⟩)
                        intro vals_bt lvl_bt rsns_bt te_bt prop_bt heur_bt m_bt s_bt
                          hbt_len hbt_te_le hbt_prop_le _ _ hbt_cond hm_bt
                        have hml_nat : (BitVec.ofNat 64 max_lvl).toNat = max_lvl :=
                          bv64_ofNat_toNat (by omega)
                        obtain ⟨hbt_core, hbt_keep⟩ := hbt_cond F0 hsw_core
                          (by dsimp [s_sw, sem, str, sms, sc]; rw [hml_nat]; omega)
                        dsimp only [s_bt] at hbt_core hbt_keep hm_bt
                        rw [hml_nat] at hbt_core hbt_keep hm_bt
                        let sbt : PlainState :=
                          { s_sw with vals := vals_bt, lvl := lvl_bt, rsns := rsns_bt,
                                      trail_end := te_bt, propagated := prop_bt,
                                      cur_level := max_lvl, heur := heur_bt }
                        have hbt_inv : PlainInv c F0 sbt := ⟨hbt_core, hsem_inv.marks⟩
                        have hlow_on_bt : ∀ j, 1 ≤ j → j < tl_ms →
                            ∃ k < te_bt, (s.trl[k]?.getD 0#32).toNat =
                              (tmp_ms[j]?.getD 0#32).toNat ^^^ 1 := by
                          intro j hj1 hj2
                          obtain ⟨hjl, hjf, _, _, hjle⟩ := hms_post j hj1 hj2
                          obtain ⟨k, hk, hkeq⟩ := (hcore.vals_false_iff _ hjl).mp hjf
                          have hklvl : (s.lvl[(s.trl[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
                              max_lvl := by
                            have hv : (s.trl[k]?.getD 0#32).toNat / 2 =
                                (tmp_ms[j]?.getD 0#32).toNat / 2 := by
                              rw [hkeq]; exact litVar_litNeg _
                            rw [hv]; exact hjle
                          exact ⟨k, (hbt_keep k hk).mp hklvl, hkeq⟩
                        -- Join after GC `if` block (`L916-925`)
                        refine wp_join_group (ts := [])
                          (fun () m_gc => ∃ rsns_g prop_g wvec_g arena_g alen_g wstk_g wlen_g wu_g
                              ag_g fred_g ni_g nr_g nb_g unfl_g fuel_g ctype_g cref_g c0_g c1_g
                              oom_g heur_g,
                            let s_gc := gcState sbt rsns_g prop_g wvec_g arena_g alen_g wstk_g
                              wlen_g wu_g ag_g fred_g ni_g nr_g nb_g unfl_g fuel_g ctype_g cref_g
                              c0_g c1_g oom_g heur_g
                            PlainInv c F0 s_gc ∧ fuel_g.toNat ≤ s.fuel.toNat ∧
                            (PlainMem c s_gc ⋆ R) m_gc) ?_ ?_
                        · -- Post-GC: `plain_add_clause` + `plain_assign`
                          rintro _ ⟨⟩ m_gc
                            ⟨rsns_g, prop_g, wvec_g, arena_g, alen_g, wstk_g, wlen_g, wu_g, ag_g,
                              fred_g, ni_g, nr_g, nb_g, unfl_g, fuel_g, ctype_g, cref_g, c0_g, c1_g,
                              oom_g, heur_g, hgc_inv, hgc_fuel, hm_gc⟩
                          clear hDefrag hRed hbt_inv hbt_core hbt_len hm_bt hm_sw
                          let s_gc := gcState sbt rsns_g prop_g wvec_g arena_g alen_g wstk_g
                            wlen_g wu_g ag_g fred_g ni_g nr_g nb_g unfl_g fuel_g ctype_g cref_g
                            c0_g c1_g oom_g heur_g
                          have hgc_len : s_gc.LengthsOk c := hgc_inv.core.lengths
                          pa_steps
                          have htl_tr32 : ((BitVec.ofNat 64 tl_ms).setWidth 32).toNat = tl_ms := by
                            rw [bv64_trunc32_ofNat (by omega), bv32_ofNat_toNat (by omega)]
                          refine wp_call_of_spec _ _
                            (hAddCl (c.hdr, (BitVec.ofNat 64 tl_ms).setWidth 32,
                              glue_v.setWidth 32, true, ()) _ _ _
                              ⟨c, F0, s_gc, R, rfl, hgc_inv.core, by rw [htl_tr32]; omega,
                                fun _ =>
                                  ⟨by dsimp [s_gc, sbt, s_sw]; rw [htl_tr32]; exact hsw_lits_lt,
                                   by dsimp [s_gc, sbt, s_sw]; rw [htl_tr32]; exact hent_sw⟩,
                                hm_gc, ?_⟩)
                          rw [htl_tr32]
                          simp only [show ¬ tl_ms < 2 by omega, ↓reduceIte]
                          by_cases htl2 : tl_ms = 2
                          · simp only [htl2, ↓reduceIte]
                            intro r_ac wvec_a wstk_a wlen_a wu_a nb_a wsort_a m_ac hr_ac hac_core
                              hm_ac
                            let sac : PlainState :=
                              { s_gc with wvec := wvec_a, wstk := wstk_a, wlen := wlen_a,
                                          wusable := wu_a, num_binary := nb_a,
                                          heur := { heur_g with wsort := wsort_a } }
                            have hac_len : sac.LengthsOk c := hac_core.lengths
                            have huip_vlen : uip.toNat < vals_bt.length := by
                              have := hac_len.vals_len; dsimp [sac, s_gc, sbt] at this; omega
                            have h1_sw : 1 < tmp_sw.length := by omega
                            pa_steps
                            · exact hret0 sac m_ac hac_len hgc_fuel hac_core.trail_lits_lt
                                rfl rfl rfl hm_ac
                            · exact hret0 sac m_ac hac_len hgc_fuel hac_core.trail_lits_lt
                                rfl rfl rfl hm_ac
                            · have huip_z : vals_bt[uip.toNat]?.getD 0#8 = 0#8 :=
                                vals_getD_eq0 huip_vlen (by assumption)
                              have hac_te_lt : te_bt < c.mv :=
                                hac_core.trail_end_lt_of_unassigned huip_lt huip_z
                              have hnot_oob : ¬ (c.mv ≤ uip.toNat / 2 ∨ c.mv ≤ te_bt) := by omega
                              have hwm_eq : tmp_sw[1]'h1_sw = wm := by
                                have h1 := List.getElem?_eq_getElem h1_sw
                                rw [hsw_get1] at h1; exact (Option.some.inj h1).symm
                              have hwm_lt : wm.toNat < 2 * c.mv := by
                                have h1 := (hms_post (tl_ms - 1) (by omega) (by omega)).1
                                rwa [List.getElem?_eq_getElem hmi_lt, Option.getD_some] at h1
                              have hbin_props := bin_rsn_mask_props (l := wm) (by omega)
                              refine wp_call_of_spec _ _
                                (hAsgn (c.hdr, uip,
                                  (tmp_sw[1]'h1_sw &&& 0x7FFFFFFF#32) ||| 0x80000000#32, ()) _ _ _
                                  ⟨c, sac, R, rfl, hac_len, by dsimp [sac, s_gc, sbt]; omega,
                                    hm_ac, ?_⟩)
                              dsimp only [sac, s_gc, sbt]; simp only [hnot_oob, ↓reduceIte]
                              intro phases' m_f hph hflen hm_f
                              pa_steps
                              have hfin_core := assign_preserves_core hac_core (lit := uip)
                                (rsn := (tmp_sw[1]'h1_sw &&& 0x7FFFFFFF#32) ||| 0x80000000#32)
                                (unflushed' := if max_lvl = 0 then unfl_g + 1#64 else unfl_g)
                                huip_lt hph huip_z
                                (by have := hac_core.cur_level_le
                                    dsimp [sac, s_gc, sbt] at this ⊢; omega)
                                (fun L h1 h2 => Or.inr (hac_core.levels_inhabited L h1 h2))
                                (fun h0 => by dsimp [sac, s_gc, sbt] at h0; omega)
                                (fun _ _ => by
                                  rw [hwm_eq]; split
                                  · simp only [hbin_props.2.2]
                                    refine ⟨hwm_lt, ?_, ?_⟩
                                    · rw [htl2] at hent_sw
                                      rwa [tmp_take2_eq hsw_get0 hsw_get1] at hent_sw
                                    · obtain ⟨k, hk, hkeq⟩ :=
                                        hlow_on_bt (tl_ms - 1) (by omega) (by omega)
                                      rw [List.getElem?_eq_getElem hmi_lt, Option.getD_some] at hkeq
                                      exact ⟨k, hk, hkeq⟩
                                  · rename_i h; exact absurd hbin_props.2.1 h)
                                (fun _ _ h => absurd (hwm_eq ▸ h) hbin_props.2.1)
                              exact analyze_ret_ok hQ 1#64 hflen (Or.inr (Or.inl rfl)) hgc_fuel
                                hfin_core.trail_lits_lt (fun hc => by cases hc)
                                (fun _ => ⟨⟨hfin_core, hgc_inv.marks⟩, hml_lt⟩) hm_f rfl rfl rfl
                            · exfalso; rcases hr_ac with h | h <;> exact absurd h (by assumption)
                          · simp only [htl2, ↓reduceIte]
                            intro r_ac arena_a alen_a wvec_a wstk_a wlen_a wu_a fred_a ni_a nr_a
                              wsort_a m_ac hr_ac hfail_ac hok_ac
                            rcases hr_ac with rfl | rfl
                            · obtain ⟨hac_core, hm_ac⟩ := hfail_ac rfl
                              pa_steps
                              exact hret0 _ m_ac hac_core.lengths hgc_fuel hac_core.trail_lits_lt
                                rfl rfl rfl hm_ac
                            · obtain ⟨ha_a, hac_core, href_a, hng_a, hlits_a, hm_ac⟩ := hok_ac rfl
                              let sac := addClauseState s_gc tl_ms arena_a wvec_a wstk_a wlen_a
                                wu_a fred_a ni_a nr_a wsort_a
                              have hac_len : sac.LengthsOk c := hac_core.lengths
                              have halen_lt : alen_g < 2 ^ 31 - 1 := by
                                have := hgc_len.arena_len_le; dsimp [s_gc] at this; omega
                              have huip_vlen : uip.toNat < vals_bt.length := by
                                have := hac_len.vals_len
                                dsimp [sac, addClauseState, s_gc, sbt] at this; omega
                              obtain ⟨href_ne_ff, href_ne_fe⟩ := bv64_ne_sentinel halen_lt
                              pa_steps
                              · exact absurd (by assumption) href_ne_ff
                              · exact hret0 sac m_ac hac_len hgc_fuel hac_core.trail_lits_lt
                                  rfl rfl rfl hm_ac
                              · exact absurd (by assumption) href_ne_fe
                              · have huip_z : vals_bt[uip.toNat]?.getD 0#8 = 0#8 :=
                                  vals_getD_eq0 huip_vlen (by assumption)
                                have hac_te_lt : te_bt < c.mv :=
                                  hac_core.trail_end_lt_of_unassigned huip_lt huip_z
                                have hnot_oob : ¬ (c.mv ≤ uip.toNat / 2 ∨ c.mv ≤ te_bt) := by omega
                                obtain ⟨hr_toNat, hr_ne, hr_lo⟩ := bv64_confl_ref_u32
                                  (r := BitVec.ofNat 64 alen_g)
                                  (by rw [bv64_ofNat_toNat (by omega)]; exact halen_lt)
                                rw [bv64_ofNat_toNat (by omega)] at hr_toNat
                                refine wp_call_of_spec _ _
                                  (hAsgn (c.hdr, uip, (BitVec.ofNat 64 alen_g).setWidth 32, ())
                                    _ _ _ ⟨c, sac, R, rfl, hac_len,
                                      by dsimp [sac, addClauseState, s_gc, sbt]; omega, hm_ac, ?_⟩)
                                dsimp only [sac, addClauseState, s_gc, sbt]
                                simp only [hnot_oob, ↓reduceIte]
                                intro phases' m_f hph hflen hm_f; pa_steps
                                have hfin_core := assign_preserves_core hac_core (lit := uip)
                                  (rsn := (BitVec.ofNat 64 alen_g).setWidth 32)
                                  (unflushed' := if max_lvl = 0 then unfl_g + 1#64 else unfl_g)
                                  huip_lt hph huip_z
                                  (by have := hac_core.cur_level_le
                                      dsimp [sac, addClauseState, s_gc, sbt] at this ⊢; omega)
                                  (fun L h1 h2 => Or.inr (hac_core.levels_inhabited L h1 h2))
                                  (fun h0 => by dsimp [sac, addClauseState, s_gc, sbt] at h0; omega)
                                  (fun _ _ => by
                                    split
                                    · rename_i h; exact absurd hr_lo h
                                    · rw [hr_toNat]; refine ⟨href_a, hng_a, fun q hq => ?_⟩
                                      rw [hlits_a] at hq
                                      rcases hsw_mem q hq with rfl | ⟨j, hj1, hj2, hjeq⟩
                                      · exact Or.inl rfl
                                      · rw [← hjeq]; exact Or.inr (hlow_on_bt j hj1 hj2))
                                  (fun _ _ _ => by
                                    rw [hr_toNat, hlits_a]
                                    rw [tmp_take_eq_cons_lowerLits htlms1 hsw_get0]
                                    exact List.mem_cons_self)
                                exact analyze_ret_ok hQ 1#64 hflen (Or.inr (Or.inl rfl)) hgc_fuel
                                  hfin_core.trail_lits_lt (fun hc => by cases hc)
                                  (fun _ => ⟨⟨hfin_core, hgc_inv.marks⟩, hml_lt⟩) hm_f rfl rfl rfl
                        · -- Body of GC `if` block (`L917-926`)
                          clear hAddCl hAsgn hent_sw hsw_lits_lt hsw_mem hsw_get1 hsw_get0
                            hlow_on_bt hms_post hent_ms
                          intro Jgc hJgc
                          refine wp_join_group (ts := []) (fun () m_in => m_bt = m_in) ?_ ?_
                          · rintro _ ⟨⟩ m_in hm_in; subst hm_in
                            refine wp_join_group (ts := [])
                              (fun () m_def => ∃ wvec_d wstk_d wlen_d wu_d wsort_d,
                                let s_d : PlainState := { sbt with
                                  wvec := wvec_d, wstk := wstk_d, wlen := wlen_d, wusable := wu_d,
                                  heur := { heur_bt with wsort := wsort_d } }
                                PlainInv c F0 s_d ∧ (PlainMem c s_d ⋆ R) m_def) ?_ ?_
                            · rintro _ ⟨⟩ m_def
                                ⟨wvec_d, wstk_d, wlen_d, wu_d, wsort_d, hd_inv, hm_def⟩
                              let s_d : PlainState := { sbt with
                                wvec := wvec_d, wstk := wstk_d, wlen := wlen_d, wusable := wu_d,
                                heur := { heur_bt with wsort := wsort_d } }
                              pa_steps
                              · refine wp_call_of_spec _ _ (hRed (c.hdr, true, ()) _ _ _
                                  ⟨c, F0, s_d, R, rfl, hd_inv.core, hm_def, ?_⟩)
                                intro rr vals_r lvl_r rsns_r trl_r tp_r te_r prop_r cl_r fuel_r
                                  unfl_r wvec_r wstk_r arena_r alen_r wlen_r wu_r ag_r fred_r ni_r
                                  nr_r nb_r ctype_r cref_r c0_r c1_r oom_r heur_r m_r s_r hr_len
                                  hr_val hr_fuel hr_trl hr_20 hr_1 hr_pos hm_r
                                have huip_rv : uip.toNat < vals_r.length := by
                                  have := hr_len.vals_len; dsimp [s_r] at this; omega
                                have hret_r1 : rr = 1#64 → Q (1#64, ()) m_r := fun hrr => by
                                  obtain ⟨hr_core, hr_cl_le, _⟩ := hr_1 hrr
                                  exact analyze_ret_ok hQ 1#64 hr_len (Or.inr (Or.inl rfl))
                                    hr_fuel hr_trl (fun hc => by cases hc)
                                    (fun _ => ⟨⟨hr_core, hd_inv.marks⟩,
                                      by dsimp only [s_r, s_d, sbt] at hr_cl_le ⊢; omega⟩)
                                    hm_r rfl rfl rfl
                                pa_steps
                                · exact analyze_ret_ok hQ 20#64 hr_len (Or.inr (Or.inr rfl))
                                    hr_fuel hr_trl (fun _ => hr_20 (by assumption))
                                    (fun hc => by cases hc) hm_r rfl rfl rfl
                                · exact hret0 _ m_r hr_len hr_fuel hr_trl rfl rfl rfl hm_r
                                · exact hret_r1 (by assumption)
                                · exact hret_r1 (by assumption)
                                · have hrr1 : rr = 1#64 := by assumption
                                  obtain ⟨hr_core, hr_cl_le, _⟩ := hr_1 hrr1
                                  dsimp only [s_r, s_d, sbt] at hr_cl_le
                                  have hcl_eq : cl_r = max_lvl := by
                                    have hbv : BitVec.ofNat 64 cl_r = BitVec.ofNat 64 max_lvl := by
                                      assumption
                                    have hnat := congrArg BitVec.toNat hbv
                                    rw [bv64_ofNat_toNat (by omega),
                                      bv64_ofNat_toNat (by omega)] at hnat; exact hnat
                                  obtain ⟨_, hve, hle, hte, htpe, htee⟩ :=
                                    hr_pos hrr1 (by omega : 0 < cl_r)
                                  dsimp only [s_r, s_d] at hve hle hte htpe htee hr_core hm_r
                                  have hcl_sbt : cl_r = sbt.cur_level := hcl_eq
                                  rw [hcl_sbt, hve, hle, hte, htpe, htee] at hr_core hm_r
                                  exact hJgc () m_r ⟨rsns_r, prop_r, wvec_r, arena_r, alen_r,
                                    wstk_r, wlen_r, wu_r, ag_r, fred_r, ni_r, nr_r, nb_r, unfl_r,
                                    fuel_r, ctype_r, cref_r, c0_r, c1_r, oom_r, heur_r,
                                    ⟨hr_core, hd_inv.marks⟩, hr_fuel, hm_r⟩
                              · exact hJgc () m_def ⟨rsns_bt, prop_bt, wvec_d, arena_b, s.arena_len,
                                  wstk_d, wlen_d, wu_d, s.arena_garbage, s.first_reducible,
                                  s.num_irred, s.num_redundant, s.num_binary, s.unflushed, s.fuel,
                                  s.confl_type, s.confl_ref, s.confl_lit0, s.confl_lit1, s.oom,
                                  { heur_bt with wsort := wsort_d }, hd_inv, Nat.le_refl _, hm_def⟩
                            · intro Jdef hJdef; pa_steps
                              · refine wp_call_of_spec _ _ (hDefrag (c.hdr, ()) _ _ _
                                  ⟨c, sbt, R, rfl, hbt_core.lengths, hbt_core.watches.layout,
                                    hm_bt, ?_⟩)
                                intro wv_d ws_d wl_d wso_d m_d _ hd_len hd_lay _ hd_pres hm_d
                                let sd : PlainState := { sbt with
                                  wvec := wv_d, wstk := ws_d, wlen := wl_d, wusable := 0#64,
                                  heur := { heur_bt with wsort := wso_d } }
                                have hd_core : PlainCoreInv c F0 sd :=
                                  { hbt_core with
                                    lengths := hd_len, arena := { hbt_core.arena with }
                                    watches := plainWstackDefrag_preserves_watchesInv
                                      hbt_core.watches hd_lay (fun _ hr => hr) hd_pres }
                                pa_steps
                                exact hJdef () m_d ⟨wv_d, ws_d, wl_d, 0#64, wso_d,
                                  ⟨hd_core, hbt_inv.marks⟩, hm_d⟩
                              · exact hJdef () m_bt ⟨s.wvec, s.wstk, s.wlen, s.wusable,
                                  heur_bt.wsort, hbt_inv, hm_bt⟩
                          · intro Jbody hJbody; pa_steps
                            · exact hJbody () m_bt rfl
                            · exact hJbody () m_bt rfl
                            · exact hJgc () m_bt ⟨rsns_bt, prop_bt, s.wvec, arena_b, s.arena_len,
                                s.wstk, s.wlen, s.wusable, s.arena_garbage, s.first_reducible,
                                s.num_irred, s.num_redundant, s.num_binary, s.unflushed, s.fuel,
                                s.confl_type, s.confl_ref, s.confl_lit0, s.confl_lit1, s.oom,
                                heur_bt, hbt_inv, Nat.le_refl _, hm_bt⟩
                · intro Lgi hLgi; pa_steps
                  exact hLgi (tl_ms - 1) _ m_tr ⟨1, Nat.le_refl _, htlms1, rfl, rfl, hm_tr⟩
            · intro Lbi hLbi; pa_steps
              exact hLbi (tl_b - 1) _ m_c ⟨1, heur_b, Nat.le_refl _, htlb1, rfl, rfl,
                hsc_core.lengths.heur_ok, hm_c⟩
        clear hJ
        -- 1-UIP loop (`L866-880`)
        refine wp_loop_group (ts := [i64])
          (fun r (idx_v, ()) ml => ∃ idx mrk_l tmp_l tc_l tl_l arena_l heur_l,
            let sl : PlainState :=
              { s with mrk := mrk_l, tmp := tmp_l, tmp_cnt := tc_l, tmp_len := tl_l,
                       arena := arena_l, heur := heur_l }
            idx ≤ s.trail_end ∧ r = idx ∧ idx_v = BitVec.ofNat 64 idx ∧
            PlainCoreInv c F0 sl ∧ 1 ≤ tl_l ∧ tl_l ≤ c.mv ∧
            0 < tc_l ∧ tc_l = (curTrailIdxs s mrk_l idx).length ∧
            LowerInv c s tmp_l mrk_l tl_l ∧ MarksCov c s tmp_l mrk_l tl_l ∧
            F0.EntailsClause (cnfClause (activeResolvent s tmp_l mrk_l tl_l idx)) ∧
            (PlainMem c sl ⋆ R) ml) ?_ ?_
        · -- 1-UIP loop body (`L866-880`)
          rintro L idx ⟨idx_v, ⟨⟩⟩ ml ih
            ⟨idx', mrk_l, tmp_l, tc_l, tl_l, arena_l, heur_l, hidx_le, rfl, rfl, hcore_l, htl1,
              htl_mv, htc_pos, htc_eq, hlow_l, hcov_l, hent_l, hml⟩
          clear hAlit hBd hMs hTr hEma hBt hAsgn hDefrag hRed hAddCl hlow1 hcov1 hent1 htc1_eq
            htc1_pos htc1_le_mv htl1_ge1 htl1_mv hsd_ok hm_sd hcore1 hconfl hm
          have htc_le_mv : tc_l ≤ c.mv := by
            rw [htc_eq]; exact Nat.le_trans (List.length_filter_le _ _) (by simp; omega)
          have hlen_l := hcore_l.lengths
          pa_steps
          · exact hfail_cm _ ml hlen_l htl_mv (Nat.le_refl _) hcore.trail_lits_lt rfl rfl rfl hml
          · have hidx_pos : 0 < idx := ofNat64_pos hc
            have hsub_idx := bv64_sub1_toNat hidx_pos (by omega : idx < 2 ^ 64)
            have hi_trl : idx - 1 < s.trl.length := by rw [hlen.trl_len]; omega
            have hsub_trl : (BitVec.ofNat 64 idx - 1).toNat < s.trl.length := hsub_idx.symm ▸ hi_trl
            let p_bv := s.trl[idx - 1]'hi_trl
            have hp_get : (s.trl[idx - 1]?.getD 0#32).toNat = p_bv.toNat := by
              rw [List.getElem?_eq_getElem hi_trl, Option.getD_some]
            have hp_lt : p_bv.toNat < 2 * c.mv := hp_get ▸ hcore.trail_lits_lt (idx - 1) (by omega)
            let pv := p_bv.toNat / 2
            have hpv_lt : pv < c.mv := by omega
            have hsub_pv_lt : ((s.trl[(BitVec.ofNat 64 idx - 1).toNat]'hsub_trl >>>
                1).setWidth 64).toNat < c.mv := by
              rw [bv_c0_zext32_64, bv32_lshr_1, getElem_eq_of_idx hsub_idx (hj := hi_trl)]
              exact hpv_lt
            have hsub_mrk_lt : ((s.trl[(BitVec.ofNat 64 idx - 1).toNat]'hsub_trl >>>
                1).setWidth 64).toNat < mrk_l.length := hlen_l.mrk_len ▸ hsub_pv_lt
            have hsub_lvl_lt : ((s.trl[(BitVec.ofNat 64 idx - 1).toNat]'hsub_trl >>>
                1).setWidth 64).toNat < s.lvl.length := hlen.lvl_len ▸ hsub_pv_lt
            have hsub_rsn_lt : ((s.trl[(BitVec.ofNat 64 idx - 1).toNat]'hsub_trl >>>
                1).setWidth 64).toNat < s.rsns.length := hlen.rsns_len ▸ hsub_pv_lt
            have hiter : ∀ mrk2 tmp2 tc2 tl2 arena2 heur2 m2,
                let s2 : PlainState := { s with
                  mrk := mrk2, tmp := tmp2, tmp_cnt := tc2, tmp_len := tl2,
                  arena := arena2, heur := heur2 }
                PlainCoreInv c F0 s2 → 1 ≤ tl2 → tl2 ≤ c.mv → 0 < tc2 →
                tc2 = (curTrailIdxs s mrk2 (idx - 1)).length →
                LowerInv c s tmp2 mrk2 tl2 → MarksCov c s tmp2 mrk2 tl2 →
                F0.EntailsClause (cnfClause (activeResolvent s tmp2 mrk2 tl2 (idx - 1))) →
                (PlainMem c s2 ⋆ R) m2 → L (BitVec.ofNat 64 idx - 1, ()) m2 := by
              intro mrk2 tmp2 tc2 tl2 arena2 heur2 m2 _ hc2 h12 hmv2 hpos2 heq2 hl2 hcv2 hen2 hm2
              have hsub_bv : BitVec.ofNat 64 idx - 1 = BitVec.ofNat 64 (idx - 1) :=
                BitVec.eq_of_toNat_eq (hsub_idx.trans (bv64_ofNat_toNat (by omega)).symm)
              rw [hsub_bv]; exact ih (idx - 1) _ _ (by omega)
                ⟨idx - 1, mrk2, tmp2, tc2, tl2, arena2, heur2, by omega, rfl, rfl, hc2, h12, hmv2,
                  hpos2, heq2, hl2, hcv2, hen2, hm2⟩
            have hskip : ¬ (mrk_l[pv]?.getD 0#8 ≠ 0#8 ∧
                (s.lvl[pv]?.getD 0#32).toNat = s.cur_level) →
                L (BitVec.ofNat 64 idx - 1, ()) ml := fun hnot => by
              have hnot' : ¬ (mrk_l[(s.trl[idx - 1]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 ∧
                  (s.lvl[(s.trl[idx - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
                    s.cur_level) := by simpa only [hp_get] using hnot
              have hidx_eq : idx - 1 + 1 = idx := by omega
              have hct_same : curTrailIdxs s mrk_l idx = curTrailIdxs s mrk_l (idx - 1) :=
                hidx_eq ▸ curTrailIdxs_succ_false hnot'
              have hcl_same : curLits s mrk_l idx = curLits s mrk_l (idx - 1) :=
                hidx_eq ▸ curLits_succ_false hnot'
              refine hiter mrk_l tmp_l tc_l tl_l arena_l heur_l ml hcore_l htl1 htl_mv htc_pos
                (hct_same ▸ htc_eq) hlow_l hcov_l ?_ hml
              unfold activeResolvent at hent_l ⊢; rwa [hcl_same] at hent_l
            have hsub_raw := bv64_sub1_raw hidx_pos (by omega : idx < 2 ^ 64)
            have hpv_mod : (s.trl[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) + idx) % 2 ^ 64]'(by
                rw [hsub_raw]; exact hi_trl)).toNat / 2 % 2 ^ 64 = pv := by
              simp only [hsub_raw]; exact Nat.mod_eq_of_lt (by omega : p_bv.toNat / 2 < 2 ^ 64)
            pa_steps
            · exact hfail_cm _ ml hlen_l htl_mv (Nat.le_refl _) hcore.trail_lits_lt rfl rfl rfl hml
            · clear hskip
              have hmnz : mrk_l[pv]?.getD 0#8 ≠ 0#8 := by
                rw [List.getElem?_eq_getElem (by rw [hlen_l.mrk_len]; exact hpv_lt),
                  Option.getD_some]
                have hne : mrk_l[(s.trl[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) + idx) % 2 ^ 64]'(by
                    rw [hsub_raw]; exact hi_trl)).toNat / 2 % 2 ^ 64]'(by
                    rw [hlen_l.mrk_len, hpv_mod]; exact hpv_lt) ≠ 0#8 := by assumption
                exact (getElem_eq_of_idx hpv_mod) ▸ hne
              have hpl_cl : (s.lvl[pv]?.getD 0#32).toNat = s.cur_level := by
                rw [List.getElem?_eq_getElem (by rw [hlen.lvl_len]; exact hpv_lt), Option.getD_some]
                have heq0 : s.lvl[(s.trl[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) + idx) % 2 ^ 64]'(by
                      rw [hsub_raw]; exact hi_trl)).toNat / 2 % 2 ^ 64]'(by
                      rw [hlen.lvl_len, hpv_mod]; exact hpv_lt) =
                    (BitVec.ofNat 64 s.cur_level).setWidth 32 := by assumption
                have heq : s.lvl[pv]'(by rw [hlen.lvl_len]; exact hpv_lt) =
                    (BitVec.ofNat 64 s.cur_level).setWidth 32 :=
                  (getElem_eq_of_idx hpv_mod).symm.trans heq0
                rw [heq, bv64_trunc32_ofNat hcur32, bv32_ofNat_toNat hcur32]
              have hidx_eq : idx - 1 + 1 = idx := by omega
              have hmnz' : mrk_l[(s.trl[idx - 1]?.getD 0#32).toNat / 2]?.getD 0#8 ≠ 0#8 := by
                simpa only [hp_get] using hmnz
              have hpl_cl' : (s.lvl[(s.trl[idx - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
                  s.cur_level := by simpa only [hp_get] using hpl_cl
              have hct_succ : curTrailIdxs s mrk_l idx =
                  curTrailIdxs s mrk_l (idx - 1) ++ [idx - 1] := by
                rw [← hidx_eq]; exact curTrailIdxs_succ_true hmnz' hpl_cl'
              have hcl_succ : curLits s mrk_l idx =
                  curLits s mrk_l (idx - 1) ++ [p_bv.toNat ^^^ 1] := by
                rw [← hidx_eq, ← hp_get]; exact curLits_succ_true hmnz' hpl_cl'
              have htc_sub : tc_l - 1 = (curTrailIdxs s mrk_l (idx - 1)).length := by
                rw [htc_eq, hct_succ, List.length_append, List.length_singleton]; omega
              let sl : PlainState :=
                { s with mrk := mrk_l, tmp := tmp_l, tmp_cnt := tc_l, tmp_len := tl_l,
                         arena := arena_l, heur := heur_l }
              refine wp_call_of_spec _ _ (hBv _ _ _ _ ⟨c, sl, R, rfl, hlen_l, hml,
                fun heur_bv m_bv hh_bv hm_bv => ?_⟩)
              pa_steps
              refine wp_call_of_spec _ _ (hQmtf _ _ _ _ ⟨c, { sl with heur := heur_bv }, R, rfl,
                hlen_l.with_heur hh_bv, hm_bv, fun heur_qm m_qm hh_qm hm_qm => ?_⟩)
              clear hBv hQmtf hml hm_bv hh_bv
              have hcore_qm : PlainCoreInv c F0 { sl with heur := heur_qm } :=
                hcore_l.with_heur hh_qm
              have htc_sub_bv : (BitVec.ofNat 64 tc_l - 1).toNat = tc_l - 1 :=
                bv64_sub1_toNat htc_pos (by omega)
              have htc_raw : (2 ^ 64 - BitVec.toNat (1 : BitVec 64) + tc_l) % 2 ^ 64 = tc_l - 1 :=
                bv64_sub1_raw htc_pos (by omega)
              pa_steps
              · clear hArsn hCm hiter hJ hfail_cm
                have htc_is0 : tc_l - 1 = 0 := by
                  have h0 : BitVec.ofNat 64 (tc_l - 1) = 0#64 := by
                    simpa only [sl, htc_raw, show (0 : BitVec 64) = 0#64 from rfl] using hc
                  exact ofNat64_eq_zero (by omega) h0
                have hsub_bv : BitVec.ofNat 64 idx - 1 = BitVec.ofNat 64 (idx - 1) := by
                  apply BitVec.eq_of_toNat_eq
                  exact hsub_idx.trans (bv64_ofNat_toNat (by omega)).symm
                have hp_some : s.trl[idx - 1]? = some p_bv := List.getElem?_eq_getElem hi_trl
                have hm_b : (PlainMem c { s with
                    mrk := mrk_l, tmp := tmp_l, tmp_cnt := 0, tmp_len := tl_l,
                    arena := arena_l, heur := heur_qm } ⋆ R) m := by
                  dsimp only [sl] at hm; rw [htc_sub_bv, htc_is0] at hm; exact hm
                have hcore_b0 : PlainCoreInv c F0 { s with
                    mrk := mrk_l, tmp := tmp_l, tmp_cnt := 0, tmp_len := tl_l,
                    arena := arena_l, heur := heur_qm } :=
                  same_core_plainCoreInv hcore_qm hlen_l.mrk_len hlen_l.tmp_len_arr htl_mv
                have hjp := hJ_post (idx - 1) mrk_l tmp_l tl_l arena_l heur_qm p_bv m (by omega)
                  hp_some hpl_cl hcore_b0 htl1 htl_mv (by omega) hlow_l hcov_l
                  (analyze_uip_entails hcl_succ (by omega) hent_l) hm_b
                have hp_eq : s.trl[(BitVec.ofNat 64 idx - 1).toNat]'hsub_trl = p_bv :=
                  getElem_eq_of_idx hsub_idx
                have hpair : (BitVec.ofNat 64 idx - 1,
                    s.trl[(BitVec.ofNat 64 idx - 1).toNat]'hsub_trl ^^^ (1 : BitVec 32), ()) =
                    (BitVec.ofNat 64 (idx - 1), p_bv ^^^ 1#32, ()) := by
                  rw [hp_eq, hsub_bv]; rfl
                exact hpair.symm ▸ hjp
              · clear hJ_post
                have htc_gt0 : 0 < tc_l - 1 := by
                  have hne : ¬ BitVec.ofNat 64 (tc_l - 1) = 0#64 := by
                    simpa only [sl, htc_raw, show (0 : BitVec 64) = 0#64 from rfl] using hc
                  exact ofNat64_pos hne
                let sl1 : PlainState :=
                  { s with mrk := mrk_l, tmp := tmp_l, tmp_cnt := tc_l - 1, tmp_len := tl_l,
                           arena := arena_l, heur := heur_qm }
                have hcore_l1 : PlainCoreInv c F0 sl1 :=
                  same_core_plainCoreInv hcore_qm hlen_l.mrk_len hlen_l.tmp_len_arr htl_mv
                have hm_l1 : (PlainMem c sl1 ⋆ R) m := by
                  dsimp only [sl] at hm; rw [htc_sub_bv] at hm; exact hm
                have hrc_idx : pv < s.rsns.length := by rw [hlen.rsns_len]; exact hpv_lt
                let rsn_bv := s.rsns[pv]'hrc_idx
                have hrsn_get : s.rsns[(s.trl[idx - 1]?.getD 0#32).toNat / 2]?.getD
                    0xFFFFFFFF#32 = rsn_bv := by
                  rw [hp_get, List.getElem?_eq_getElem hrc_idx, Option.getD_some]
                have hrsn_ref : rsn_bv ≠ 0xFFFFFFFF#32 → (rsn_bv &&& 0x80000000#32) = 0#32 →
                    rsn_bv.toNat ∈ arenaClauseRefs sl1 := by
                  intro hne hlo
                  have hr := hcore_l1.reason_inv (idx - 1) (by dsimp [sl1]; omega)
                    (by dsimp [sl1]; rwa [hrsn_get])
                  dsimp only [sl1] at hr; rw [hrsn_get] at hr
                  split at hr
                  · rename_i h; exact absurd hlo h
                  · exact hr.1
                have harg_rsn :
                    s.rsns[((s.trl[(BitVec.ofNat 64 idx - 1).toNat]'hsub_trl >>> 1).setWidth
                      64).toNat]'hsub_rsn_lt = rsn_bv := by
                  simp only [bv_c0_zext32_64, bv32_lshr_1, hsub_idx]; rfl
                refine wp_call_of_spec _ _
                  (hArsn (c.hdr,
                    s.rsns[((s.trl[(BitVec.ofNat 64 idx - 1).toNat]'hsub_trl >>> 1).setWidth
                      64).toNat]'hsub_rsn_lt,
                    s.trl[(BitVec.ofNat 64 idx - 1).toNat]'hsub_trl >>> 1, ()) _ _ _
                    ⟨c, F0, sl1, R, rfl, hcore_l1, htl_mv, by dsimp [sl1]; omega,
                      by rw [harg_rsn]; exact hrsn_ref, hm_l1, ?_⟩)
                intro ok2 mrk2 tmp2 tc2 tl2 arena2 heur2 m2 _ hcore2 htl2_ge htl2_le htc2_ge
                  hrefs2 hcl2 hmp2 htp2 hnm2 hnt2 hcnt2 hall2 hm2
                dsimp only [sl1] at hcore2 htl2_ge htl2_le htc2_ge hrefs2 hcl2
                dsimp only [sl1] at hmp2 htp2 hnm2 hnt2 hcnt2 hall2 hm2
                cases ok2 with
                | false =>
                  pa_steps
                  exact hfail_cm _ m2 hcore2.lengths htl2_le (Nat.le_refl _) hcore.trail_lits_lt
                    rfl rfl rfl hm2
                | true =>
                  pa_steps
                  rw [harg_rsn] at hnm2 hnt2 hall2
                  obtain ⟨hrsn_ne, _, _, hall2'⟩ := hall2 rfl
                  have hpv_tr :
                      (s.trl[(BitVec.ofNat 64 idx - 1).toNat]'hsub_trl >>> 1).toNat = pv := by
                    simp only [hsub_idx, bv32_lshr_1]; rfl
                  rw [hpv_tr] at hnm2 hnt2 hall2'
                  obtain ⟨htc2_eq, hlow2, hcov2, hent2⟩ :=
                    analyze_resolve_sem hcore hidx_pos hidx_le hp_get hrsn_get hrsn_ne hcore_l1
                      hcore2 htl1 htl2_ge htl2_le htc_sub htc2_ge hcl_succ hlow_l hcov_l hent_l
                      hmp2 htp2 hnm2 hnt2 hcnt2 hall2'
                  exact hiter mrk2 tmp2 tc2 tl2 arena2 heur2 m2 hcore2 (by omega) htl2_le
                    (by omega) htc2_eq hlow2 hcov2 hent2 hm2
            · apply hskip; intro ⟨_, hcl⟩
              have hne0 : s.lvl[(s.trl[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) + idx) % 2 ^ 64]'(by
                  rw [hsub_raw]; exact hi_trl)).toNat / 2 % 2 ^ 64]'(by
                  rw [hlen.lvl_len, hpv_mod]; exact hpv_lt) ≠
                  (BitVec.ofNat 64 s.cur_level).setWidth 32 := by assumption
              apply (getElem_eq_of_idx hpv_mod ▸ hne0); apply BitVec.eq_of_toNat_eq
              rw [bv64_trunc32_ofNat hcur32, bv32_ofNat_toNat hcur32]
              rw [List.getElem?_eq_getElem (by rw [hlen.lvl_len]; exact hpv_lt),
                  Option.getD_some] at hcl; exact hcl
            · apply hskip; intro ⟨hmnz, _⟩; apply hmnz
              rw [List.getElem?_eq_getElem (by rw [hlen_l.mrk_len]; exact hpv_lt), Option.getD_some]
              have hz0 : mrk_l[(s.trl[(2 ^ 64 - BitVec.toNat (1 : BitVec 64) + idx) % 2 ^ 64]'(by
                  rw [hsub_raw]; exact hi_trl)).toNat / 2 % 2 ^ 64]'(by
                  rw [hlen_l.mrk_len, hpv_mod]; exact hpv_lt) = 0#8 := by assumption
              exact (getElem_eq_of_idx hpv_mod).symm.trans hz0
          · exfalso
            have h0 : ¬ (0#64).toNat < tc_l % 2 ^ 64 := by assumption
            have : tc_l % 2 ^ 64 = tc_l := Nat.mod_eq_of_lt (by omega)
            change ¬ 0 < tc_l % 2 ^ 64 at h0; omega
        · intro L hL; pa_steps
          exact hL s.trail_end _ m_sd ⟨s.trail_end, mrk1, tmp1, tc1, tl1, arena1, heur1,
            Nat.le_refl _, rfl, rfl, hcore1, htl1_ge1, htl1_mv, htc1_pos, htc1_eq, hlow1, hcov1,
            hent1, hm_sd⟩
  · -- Seed branch body before join (`L845-850`)
    clear hCm hBv hQmtf hBd hMs hTr hEma hBt hAsgn hDefrag hRed hAddCl
    intro Jsd hJsd
    let s0 : PlainState := { s with tmp_cnt := 0, tmp_len := 1 }
    have hs0_core : PlainCoreInv c F0 s0 :=
      same_core_plainCoreInv hcore hlen.mrk_len hlen.tmp_len_arr hmv_pos
    pa_steps
    · -- Binary conflict (`confl_type == 1`): two `plain_analyze_lit` calls
      have hct1 : s.confl_type = 1#64 := by assumption
      rcases hconfl with ⟨_, hl0_lt, hl1_lt, hent_bin, hf0, hf1⟩ | ⟨hne, _⟩
      · refine wp_call_of_spec _ _
          (hAlit (c.hdr, s.confl_lit0.setWidth 32, 0xFFFFFFFF#32, ()) _ _ _
            ⟨c, s0, R, rfl, hs0_core.lengths, hcur32, hmv_pos, by dsimp [s0]; decide, hm, ?_⟩)
        intro ok_a mrk_a tmp_a tc_a tl_a m_a _ hlen_a htla_ge htla_inc htla_mv htca_ge htca_eq
          hmp_a htp_a hnm_a hnt_a hok_a hm_a
        dsimp only [s0] at hlen_a htla_ge htla_inc htla_mv htca_ge htca_eq hmp_a htp_a hnm_a hnt_a
        dsimp only [s0] at hok_a hm_a
        have hcore_a : PlainCoreInv c F0 { s with
          mrk := mrk_a, tmp := tmp_a, tmp_cnt := tc_a, tmp_len := tl_a } :=
          same_core_plainCoreInv hcore hlen_a.mrk_len hlen_a.tmp_len_arr htla_mv
        cases ok_a with
        | false =>
          pa_steps; exact hJsd (false, ()) m_a ⟨mrk_a, tmp_a, tc_a, tl_a, s.arena, s.heur, hcore_a,
            htla_ge, htla_mv, (fun hc => by cases hc), hm_a⟩
        | true =>
          pa_steps
          have htca_le_1 : tc_a ≤ 1 := by split at htca_eq <;> omega
          let sa : PlainState :=
            { s with mrk := mrk_a, tmp := tmp_a, tmp_cnt := tc_a, tmp_len := tl_a }
          refine wp_call_of_spec _ _
            (hAlit (c.hdr, s.confl_lit1.setWidth 32, 0xFFFFFFFF#32, ()) _ _ _
              ⟨c, sa, R, rfl, hlen_a, hcur32, htla_mv, by dsimp [sa]; omega, hm_a, ?_⟩)
          intro ok_b mrk_b tmp_b tc_b tl_b m_b _ hlen_b htlb_ge htlb_inc htlb_mv htcb_ge htcb_eq
            hmp_b htp_b hnm_b hnt_b hok_b hm_b
          dsimp only [sa] at hlen_b htlb_ge htlb_inc htlb_mv htcb_ge htcb_eq hmp_b htp_b hnm_b hnt_b
          dsimp only [sa] at hok_b hm_b
          have hcore_b : PlainCoreInv c F0 { s with
            mrk := mrk_b, tmp := tmp_b, tmp_cnt := tc_b, tmp_len := tl_b } :=
            same_core_plainCoreInv hcore hlen_b.mrk_len hlen_b.tmp_len_arr htlb_mv
          cases ok_b with
          | false =>
            pa_steps; exact hJsd (false, ()) m_b ⟨mrk_b, tmp_b, tc_b, tl_b, s.arena, s.heur,
              hcore_b, by omega, htlb_mv, (fun hc => by cases hc), hm_b⟩
          | true =>
            pa_steps; exact hJsd (true, ()) m_b ⟨mrk_b, tmp_b, tc_b, tl_b, s.arena, s.heur, hcore_b,
              by omega, htlb_mv,
              fun _ => analyze_bin_seed_sem hinv hl0_lt hl1_lt hent_bin hf0 hf1 htla_ge htla_mv
                htlb_ge htlb_mv htcb_ge hlen_a.tmp_len_arr hlen_b.tmp_len_arr htca_eq hmp_a htp_a
                hnm_a hnt_a (hok_a rfl) htcb_eq hmp_b htp_b hnm_b hnt_b (hok_b rfl), hm_b⟩
      · exact absurd hct1 hne
    · -- Large arena conflict (`confl_type ≠ 1`): one `plain_analyze_rsn` call
      have hct_ne : s.confl_type ≠ 1#64 := by assumption
      rcases hconfl with ⟨h1, _⟩ | ⟨_, href, hng, hfals⟩
      · exact absurd h1 hct_ne
      · have href_lt : s.confl_ref.toNat < 2 ^ 31 - 1 := by
          have := (hcore.arena.refs_wf s.confl_ref.toNat href).1
          have := hlen.arena_len_le; omega
        obtain ⟨hcr_nat, hcr_ne, hcr_lo⟩ := bv64_confl_ref_u32 href_lt
        refine wp_call_of_spec _ _ (hArsn (c.hdr, s.confl_ref.setWidth 32, 0xFFFFFFFF#32, ()) _ _ _
          ⟨c, F0, s0, R, rfl, hs0_core, hmv_pos, by dsimp [s0]; omega,
            fun _ _ => by dsimp [s0]; rwa [hcr_nat], hm, ?_⟩)
        intro ok1 mrk1 tmp1 tc1 tl1 arena1 heur1 m1 _ hcore1 htl1_ge htl1_mv htc1_ge hrefs1 hcl1
          hmp1 htp1 hnm1 hnt1 hcnt1 hall1 hm1
        dsimp only [s0] at hcore1 htl1_ge htl1_mv htc1_ge hrefs1 hcl1 hmp1 htp1 hnm1 hnt1 hcnt1
        dsimp only [s0] at hall1 hm1
        cases ok1 with
        | false =>
          pa_steps; exact hJsd (false, ()) m1 ⟨mrk1, tmp1, tc1, tl1, arena1, heur1, hcore1, htl1_ge,
            htl1_mv, (fun hc => by cases hc), hm1⟩
        | true =>
          pa_steps; exact hJsd (true, ()) m1 ⟨mrk1, tmp1, tc1, tl1, arena1, heur1, hcore1, htl1_ge,
            htl1_mv, fun _ => analyze_large_seed_sem hinv href hng hfals hcr_nat hcr_ne hcr_lo
              htl1_ge htl1_mv hcore1.lengths.tmp_len_arr hmp1 htp1 hnm1 hnt1 hcnt1
              (hall1 rfl).2.2.2, hm1⟩

end LeanQbe.T.Examples.Kissat.Plain
