module

public import LeanQbe.T.Examples.Kissat.PlainSpec

/-!
# Kissat `D-Plain` Clause-Database Reduction Helpers & Core Contracts — Part 1 (`Wave 2b`)

Provides scoped tactics (`PlainReduceTactics`), shared `BitVec` / `PlainCoreInv` /
arena-flag / binary-watch / garbage-mask preservation lemmas, and verified parametric
`(Γ : Env)` `Func.wp` contracts for:
1. `plain_red_less` (`plainRedLessSpec`)
2. `plain_lit_rank` (`plainLitRankSpec`)
3. `plain_recompute_tiers` (`plainRecomputeTiersSpec`)
4. `plain_mark_reasons` (`plainMarkReasonsSpec`)
5. `plain_sort_reds` (`plainSortRedsSpec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Plain

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.C0Step
open Kraken.Bedrock2.Test

/-! ## 1. Scoped tactics & `BitVec` / arena helper lemmas -/

namespace PlainReduceTactics

theorem bv_c0_shr1_32 (x : BitVec 32) : (x >>> 1#32).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem bv_c0_shr1_64 (x : BitVec 64) : (x >>> 1#64).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem bv_c0_shl1_64 (x : BitVec 64) : (x <<< 1#64).toNat = (2 * x.toNat) % 2 ^ 64 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

theorem bv_c0_shr1n_32 (x : BitVec 32) : (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem bv_c0_shr1n_64 (x : BitVec 64) : (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem bv_c0_shl1n_64 (x : BitVec 64) :
    (x <<< (1 : Nat)).toNat = (2 * x.toNat) % 2 ^ 64 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]

attribute [scoped bv_c0] bv_c0_shr1_32 bv_c0_shr1_64 bv_c0_shl1_64
  bv_c0_shr1n_32 bv_c0_shr1n_64 bv_c0_shl1n_64 List.length_set

@[scoped c0_load] theorem load_red_refs_zero {c : PlainCfg} {s : PlainState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < s.heur.red_refs.length)
    (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 (c.pRedRefs + 0#64) = some s.heur.red_refs[0] :=
  load_arena_red_refs (i := 0) hi hm

@[scoped c0_store] theorem store_red_refs_zero {c : PlainCfg} {s : PlainState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.heur.red_refs.length)
    (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i32 (c.pRedRefs + 0#64) ∧
      (PlainMem c { s with heur := { s.heur with red_refs := s.heur.red_refs.set 0 v } } ⋆ R)
        (storeMem m i32 (c.pRedRefs + 0#64) v) :=
  store_arena_red_refs (i := 0) v hi hm

@[scoped c0_load] theorem load_red_refs_base {c : PlainCfg} {s : PlainState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < s.heur.red_refs.length)
    (hm : (PlainMem c s ⋆ R) m) :
    loadVal m i32 c.pRedRefs = some s.heur.red_refs[0] := by
  simpa using load_red_refs_zero hi hm

@[scoped c0_store] theorem store_red_refs_base {c : PlainCfg} {s : PlainState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.heur.red_refs.length)
    (hm : (PlainMem c s ⋆ R) m) :
    storeOk m i32 c.pRedRefs ∧
      (PlainMem c { s with heur := { s.heur with red_refs := s.heur.red_refs.set 0 v } } ⋆ R)
        (storeMem m i32 c.pRedRefs v) := by
  simpa using store_red_refs_zero v hi hm

section
open Lean Meta Elab Tactic
/-- Strip outer `Expr.mdata` wrappers so `c0_step` recognizes `Func.wp`/`wp`. -/
scoped elab "c0_unmdata" : tactic => withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  if ty.isMData then
    replaceMainGoal [← g.change ty.consumeMData (checkDefEq := false)]

/-- Clear all non-detail hypotheses not in `ids` when no dependency blocks it. -/
scoped elab "clear_except" "[" ids:ident* "]" : tactic => withMainContext do
  let keep := ids.map (·.getId) |>.toList
  let mut g ← getMainGoal
  for d in (← getLCtx).decls.toArray.reverse do
    let some d := d | continue
    if !d.isImplementationDetail && !keep.contains d.userName then
      try g ← g.clear d.fvarId catch _ => pure ()
  replaceMainGoal [g]

private meta def mkPrSimp : TacticM (Simp.Context × Simp.Methods) := do
  let stx ← `(tactic| simp only [
    LeanQbe.T.op1_eq_mk, LeanQbe.T.op2_eq_mk, LeanQbe.T.op3_eq_mk, LeanQbe.T.wp_let_copy_eq,
    LeanQbe.T.wp_let_add_eq, LeanQbe.T.wp_let_sub_eq, LeanQbe.T.wp_let_mul_eq,
    LeanQbe.T.wp_let_neg_eq, LeanQbe.T.wp_let_and_eq, LeanQbe.T.wp_let_or_eq,
    LeanQbe.T.wp_let_xor_eq, LeanQbe.T.wp_let_not_eq, LeanQbe.T.wp_let_shl_eq,
    LeanQbe.T.wp_let_lshr_eq, LeanQbe.T.wp_let_ashr_eq, LeanQbe.T.wp_let_rotl_eq,
    LeanQbe.T.wp_let_rotr_eq, LeanQbe.T.wp_let_clz_eq, LeanQbe.T.wp_let_cls_eq,
    LeanQbe.T.wp_let_rbit_eq, LeanQbe.T.wp_let_ctz_eq, LeanQbe.T.wp_let_popcnt_eq,
    LeanQbe.T.wp_let_cmp_eq, LeanQbe.T.wp_let_select_eq, LeanQbe.T.wp_let_zext_eq,
    LeanQbe.T.wp_let_sext_eq, LeanQbe.T.wp_let_trunc_eq, LeanQbe.T.wp_let_ofBool_eq,
    LeanQbe.T.wp_let_udiv0_eq, LeanQbe.T.wp_let_sdiv0_eq, LeanQbe.T.wp_let_mkpair_eq,
    LeanQbe.T.wp_let_unpair_eq, LeanQbe.T.wp_let_bitcast_eq, LeanQbe.T.wp_jump,
    LeanQbe.T.wp_ret, LeanQbe.T.wp_exit, LeanQbe.T.OpCode.eq, LeanQbe.T.OpCode.ne,
    LeanQbe.T.OpCode.ult, LeanQbe.T.OpCode.ule, LeanQbe.T.OpCode.ugt, LeanQbe.T.OpCode.uge,
    LeanQbe.T.OpCode.slt, LeanQbe.T.OpCode.sle, LeanQbe.T.OpCode.sgt, LeanQbe.T.OpCode.sge,
    LeanQbe.T.vals_nil, LeanQbe.T.vals_cons, LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm,
    LeanQbe.T.Blocks.get_here, LeanQbe.T.Blocks.get_there, LeanQbe.T.Ty.hasFloat_vec,
    LeanQbe.T.Ty.hasFloat, LeanQbe.T.Ty.isFloatTree, LeanQbe.T.evalBits_eq_beq,
    LeanQbe.T.evalBits_ne_bne, LeanQbe.T.evalBits_ult_eq, LeanQbe.T.evalBits_ule_eq,
    LeanQbe.T.evalBits_ugt_eq, LeanQbe.T.evalBits_uge_eq, LeanQbe.T.evalBits_slt_eq,
    LeanQbe.T.evalBits_sle_eq, LeanQbe.T.evalBits_sgt_eq, LeanQbe.T.evalBits_sge_eq,
    LeanQbe.T.evalBool_eq_beq, LeanQbe.T.evalBool_ne_bne, LeanQbe.T.lift1, LeanQbe.T.lift2,
    LeanQbe.T.lift3, LeanQbe.T.liftCmp, LeanQbe.T.shl_three, cast_eq, ite_self, ite_true,
    ite_false, Bool.false_eq_true, Bool.true_eq_false, BitVec.add_zero, BitVec.zero_add,
    BitVec.reduceToNat, Nat.reduceMod, Nat.reduceLeDiff, true_and, and_true,
    BitVec.reduceSignExtend, BitVec.reduceSetWidth, BitVec.reduceAdd, BitVec.reduceMul])
  let { ctx, simprocs, .. } ← mkSimpContext stx (eraseLocal := false)
  let m0 := Simp.mkDefaultMethodsCore simprocs
  let methods : Simp.Methods := { m0 with
    pre := fun sub => do
      if sub.isAppOf ``LeanQbe.T.Expr.group || sub.isAppOf ``LeanQbe.T.Expr.load ||
         sub.isAppOf ``LeanQbe.T.Expr.store || sub.isAppOf ``LeanQbe.T.Expr.jnz ||
         sub.isAppOf ``LeanQbe.T.Expr.call then
        return .done { expr := sub }
      m0.pre sub }
  return (ctx, methods)

private meta def prLetSimpWith (ctx : Simp.Context) (methods : Simp.Methods) : TacticM Unit :=
  withMainContext do
    let g ← getMainGoal
    let r := (← Simp.main (← instantiateMVars (← g.getType)) ctx (methods := methods)).1
    replaceMainGoal [← g.replaceTargetEq r.expr (← r.getProof)]

private meta def prSimpHypWith (ctx : Simp.Context) (methods : Simp.Methods)
    (name : Name) : TacticM Unit := withMainContext do
  let some d := (← getLCtx).findFromUserName? name | return
  let r := (← Simp.main (← instantiateMVars d.type) ctx (methods := methods)).1
  let g ← getMainGoal
  let res ← g.replaceLocalDecl d.fvarId r.expr (← r.getProof)
  replaceMainGoal [res.mvarId]

private meta partial def prSepClauses (e : Lean.Expr) : List Lean.Expr :=
  if e.isAppOf ``Std.ExtHashMap.sep && e.getAppNumArgs ≥ 2 then
    prSepClauses (e.getArg! (e.getAppNumArgs - 2)) ++
      prSepClauses (e.getArg! (e.getAppNumArgs - 1))
  else [e]

private meta def prFootprints : TacticM (Array Name) := withMainContext do
  let mut keys : Array Name := #[]
  for d in (← getLCtx).decls.toArray.reverse do
    let some d := d | continue
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if t.isAppOf ``Std.ExtHashMap.sep && t.getAppNumArgs ≥ 3 then
      for c in prSepClauses t.appFn! do
        if let some k := c.getAppFn.constName? then
          unless keys.contains k do keys := keys.push k
  return keys

private meta def prCloseWith (g : MVarId) (tac : TSyntax `tactic) : TacticM Bool := do
  if ← g.isAssigned then return true
  let s ← saveState
  try
    setGoals [g]; evalTactic tac
    if (← getUnsolvedGoals).isEmpty then return true
    s.restore; return false
  catch _ => s.restore; return false

private meta def prTryMemLemma (ctx : Simp.Context) (methods : Simp.Methods)
    (g : MVarId) (nm : Name) : TacticM Bool := do
  let s ← saveState
  try
    let gs ← withReducible <| g.apply (← mkConstWithFreshMVarLevels nm)
    for g' in gs do
      let ty ← instantiateMVars (← g'.getType)
      if ty.isAppOf ``Std.ExtHashMap.sep then
        unless ← withReducible (prCloseWith g' (← `(tactic| c0_frame))) do throwError "frame"
    let b1 ← `(tactic| first | assumption | rfl | decide | omega)
    let b2 ← `(tactic| first
      | (simp only [bv_c0, Nat.reducePow, Nat.reduceMod, Nat.reduceDiv, BitVec.reduceToNat];
          omega)
      | c0_bound)
    for g' in gs do
      if ← g'.isAssigned then continue
      if ← isProp (← g'.getType) then
        if !(← prCloseWith g' b1) then
          let ok2 ← do
            let s2 ← saveState
            try
              setGoals [g']; try prLetSimpWith ctx methods catch _ => pure ()
              let g'' ← getMainGoal
              let r := (← Simp.main (← instantiateMVars (← g''.getType)) ctx
                (methods := methods)).1
              replaceMainGoal [← g''.replaceTargetEq r.expr (← r.getProof)]
              evalTactic b2
              if (← getUnsolvedGoals).isEmpty then pure true
              else do s2.restore; pure false
            catch _ => s2.restore; pure false
          unless ok2 do throwError "side"
    for g' in gs do
      unless ← g'.isAssigned do throwError "unassigned"
    return true
  catch _ => s.restore; return false

private meta def prMemSolveRes (ctx : Simp.Context) (methods : Simp.Methods)
    (isLoad : Bool) (g : MVarId) : TacticM (Except String Unit) := do
  setGoals [g]
  try prLetSimpWith ctx methods catch _ => pure ()
  let g ← getMainGoal
  let keys ← prFootprints
  let env ← getEnv
  for k in keys do
    for nm in C0Step.c0MemLemmas env isLoad k do
      if ← prTryMemLemma ctx methods g nm then return .ok ()
  return .error
    s!"pr_steps: unmatched mem goal:\n  {(← Meta.ppExpr (← instantiateMVars (← g.getType))).pretty}"

private meta def prClearStale (m0 : Lean.Expr) : TacticM Unit := withMainContext do
  let .fvar mId := m0 | return
  for d in (← getLCtx).decls.toArray.reverse do
    let some d := d | continue
    let t ← instantiateMVars d.type
    if t.isAppOf ``Std.ExtHashMap.sep && t.appArg! == m0 then
      try liftMetaTactic1 fun g => some <$> g.clear d.fvarId catch _ => pure ()
  try liftMetaTactic1 fun g => some <$> g.clear mId catch _ => pure ()

private meta def prIsJoin (bodies : Lean.Expr) : Bool :=
  match bodies with | .lam _ _ b _ => !b.hasLooseBVars | _ => false

private meta def prFindJoinHyp (J : FVarId) : TacticM (Option Lean.Expr) := withMainContext do
  for d in (← getLCtx).decls.toArray.reverse do
    let some d := d | continue
    let ok ← forallTelescopeReducing d.type fun xs concl => do
      if xs.size < 1 then return false
      return concl.getAppFn.isFVarOf J && (← inferType xs[xs.size - 1]!).isAppOf ``LeanQbe.T.wp
    if ok then return some d.toExpr
  return none

private meta def prLetOpCode? (e : Lean.Expr) : Option Name :=
  if e.isAppOf ``LeanQbe.T.Expr.let_ && e.getAppNumArgs == 6 then
    let op := (e.getArg! 4).headBeta
    if op.isAppOf ``LeanQbe.T.Op.mk && op.getAppNumArgs == 5 then
      (op.getArg! 3).getAppFn.constName?
    else if op.isAppOf ``LeanQbe.T.op2 && op.getAppNumArgs == 7 then
      (op.getArg! 4).getAppFn.constName?
    else none
  else none

private meta def prStepDiv (ctx : Simp.Context) (methods : Simp.Methods)
    (g : MVarId) (lem : Name) : TacticM Bool := do
  let s ← saveState
  try
    setGoals [g]
    evalTactic (← `(tactic| try simp only [LeanQbe.T.op2_eq_mk]))
    let g ← getMainGoal
    let [hSide, hk] := (← g.apply (← mkConstWithFreshMVarLevels lem)).take 2
      | s.restore; return false
    setGoals [hSide]
    evalTactic (← `(tactic| try simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm]))
    let hSide ← getMainGoal
    let sideClosed ← prCloseWith hSide (← `(tactic| c0_div_bound))
    setGoals [hk]
    try prLetSimpWith ctx methods catch _ => pure ()
    let hkRest ← getUnsolvedGoals
    setGoals ((if sideClosed then [] else [hSide]) ++ hkRest)
    return true
  catch _ => s.restore; return false

private meta def prStepOnceRes (ctx : Simp.Context) (methods : Simp.Methods)
    (strictMem pruneDead : Bool) : TacticM (Option String × Bool) := withMainContext do
  let g ← getMainGoal
  let ty ← instantiateMVars (← g.getType)
  let g ← if ty.isMData then g.change ty.consumeMData (checkDefEq := false) else pure g
  setGoals [g]
  let ty := (← instantiateMVars (← g.getType)).headBeta
  if ty.isAppOf ``LeanQbe.T.Func.wp && ty.getAppNumArgs ≥ 4 then
    if let some c := (ty.getArg! 3).getAppFn.constName? then
      evalTactic (← `(tactic| unfold LeanQbe.T.Func.wp $(mkIdent c):ident))
      try prLetSimpWith ctx methods catch _ => pure ()
      return (none, true)
  if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 then
    let e := (ty.getArg! 4).headBeta
    match e.getAppFn.constName? with
    | some ``LeanQbe.T.Expr.let_ =>
      match prLetOpCode? e with
      | some ``LeanQbe.T.OpCode.udiv =>
        return (none, ← prStepDiv ctx methods g ``LeanQbe.T.wp_udiv_of)
      | some ``LeanQbe.T.OpCode.urem =>
        return (none, ← prStepDiv ctx methods g ``LeanQbe.T.wp_urem_of)
      | some ``LeanQbe.T.OpCode.sdiv =>
        return (none, ← prStepDiv ctx methods g ``LeanQbe.T.wp_sdiv_of)
      | some ``LeanQbe.T.OpCode.srem =>
        return (none, ← prStepDiv ctx methods g ``LeanQbe.T.wp_srem_of)
      | _ => prLetSimpWith ctx methods; return (none, true)
    | some ``LeanQbe.T.Expr.jump | some ``LeanQbe.T.Expr.ret | some ``LeanQbe.T.Expr.exit
    | some ``LeanQbe.T.Blocks.get =>
      prLetSimpWith ctx methods; return (none, true)
    | some ``LeanQbe.T.Expr.load =>
      let s ← saveState
      let [hl, hk] := (← g.apply (← mkConstWithFreshMVarLevels ``LeanQbe.T.wp_load_of)).take 2
        | s.restore; return (none, false)
      match ← prMemSolveRes ctx methods true hl with
      | .ok () =>
        setGoals [hk]; try prLetSimpWith ctx methods catch _ => pure ()
        return (none, true)
      | .error msg =>
        s.restore; if strictMem then throwError msg; return (some msg, false)
    | some ``LeanQbe.T.Expr.store =>
      let s ← saveState
      let m0 := ty.getArg! 5
      let [hs, hk] := (← g.apply (← mkConstWithFreshMVarLevels ``LeanQbe.T.wp_store_sep)).take 2
        | s.restore; return (none, false)
      match ← prMemSolveRes ctx methods false hs with
      | .ok () =>
        setGoals [hk]
        let mId := mkIdent `m; let hmId := mkIdent `hm
        evalTactic (← `(tactic| intro $mId:ident $hmId:ident))
        evalTactic (← `(tactic| try simp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm,
          Std.ExtHashMap.sep_emp] at $hmId:ident))
        prClearStale m0; try prLetSimpWith ctx methods catch _ => pure ()
        return (none, true)
      | .error msg =>
        s.restore; if strictMem then throwError msg; return (some msg, false)
    | some ``LeanQbe.T.Expr.jnz =>
      let hc := mkIdent `hc
      evalTactic (← `(tactic|
        refine LeanQbe.T.wp_jnz_of (fun $hc:ident => ?_) (fun $hc:ident => ?_)))
      let mut out : Array MVarId := #[]
      for g' in ← getUnsolvedGoals do
        if ← g'.isAssigned then continue
        setGoals [g']; prSimpHypWith ctx methods `hc
        evalTactic (← `(tactic| c0_cond $hc))
        if pruneDead then
          evalTactic (← `(tactic| try (exfalso; first
            | omega
            | (simp only [bv_c0, Nat.reducePow, Nat.reduceMod] at $hc:ident; omega)
            | bv_omega)))
        for g'' in ← getUnsolvedGoals do
          if ← g''.isAssigned then continue
          setGoals [g'']; try prLetSimpWith ctx methods catch _ => pure ()
          out := out ++ (← getUnsolvedGoals)
      setGoals out.toList; return (none, true)
    | some ``LeanQbe.T.Expr.group =>
      if e.getAppNumArgs == 6 && prIsJoin (e.getArg! 4) then
        let J := mkIdent `J; let hJ := mkIdent `hJ
        evalTactic (← `(tactic| refine LeanQbe.T.wp_unroll_group fun $J:ident $hJ:ident => ?_))
        try prLetSimpWith ctx methods catch _ => pure ()
        return (none, true)
      return (none, false)
    | _ => return (none, false)
  if let .fvar J := ty.getAppFn then
    if let some h ← prFindJoinHyp J then
      setGoals (← g.apply h); try prLetSimpWith ctx methods catch _ => pure ()
      return (none, true)
  return (none, false)

private meta partial def prStepsRec (ctx : Simp.Context) (methods : Simp.Methods)
    (strictMem pruneDead : Bool) (fuel : Nat) : TacticM (Bool × Option String) := do
  if fuel = 0 then return (false, none)
  let mut progressed := false
  let mut err? : Option String := none
  let mut out : Array MVarId := #[]
  for g in ← getUnsolvedGoals do
    if ← g.isAssigned then continue
    setGoals [g]
    let (e?, ok) ← prStepOnceRes ctx methods strictMem pruneDead
    if err?.isNone then err? := e?
    if ok then
      progressed := true
      let (_, se?) ← prStepsRec ctx methods strictMem pruneDead (fuel - 1)
      if err?.isNone then err? := se?
    out := out ++ (← getUnsolvedGoals)
  setGoals out.toList
  return (progressed, err?)

/-- Fast symbolic execution for `Plain` C0 bodies (cached simplifier; avoids `at *` blowup). -/
scoped elab "pr_steps" : tactic => do
  let (ctx, methods) ← mkPrSimp
  let (prog, err?) ← prStepsRec ctx methods false false 10000
  if !prog then if let some msg := err? then throwError msg

/-- Strict fast symbolic execution for `Plain` C0 bodies (throws on unmatched loads/stores). -/
scoped elab "pr_steps!" : tactic => do
  let (ctx, methods) ← mkPrSimp
  let (prog, err?) ← prStepsRec ctx methods true true 10000
  if !prog then if let some msg := err? then throwError msg
end

end PlainReduceTactics

section
open scoped PlainReduceTactics

private theorem bv32_add2_toNat_le (a : BitVec 32) : (a + 2#32).toNat ≤ a.toNat + 2 := by
  bv_omega

theorem PlainReduceTactics.bv32_and_msb_zero_of_ult {r : BitVec 32} (h : r.toNat < 0x80000000) :
    (r &&& 0x80000000#32) = 0#32 := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_and, BitVec.toNat_zero]
  apply Nat.eq_of_testBit_eq; intro i; rw [Nat.testBit_and, Nat.zero_testBit]
  by_cases hi : i = 31
  · subst hi; rw [Nat.testBit_lt_two_pow h, Bool.false_and]
  · rw [show (0x80000000#32 : BitVec 32).toNat = 2 ^ 31 from rfl,
      Nat.testBit_two_pow, decide_eq_false (Ne.symm hi), Bool.and_false]

theorem PlainReduceTactics.bv32_ne_allOnes_of_ult {r : BitVec 32} (h : r.toNat < 0x80000000) :
    r ≠ 0xFFFFFFFF#32 := fun heq => by subst heq; simp at h

namespace PlainReduceHelpers

private theorem bv32_or_rsn_mask (x : BitVec 32) :
    ((x ||| 0x00200000#32) &&& ~~~0x00200000#32) = x &&& ~~~0x00200000#32 := by
  have hm : ((0x00200000#32 : BitVec 32) &&& ~~~0x00200000#32) = 0#32 := by decide
  rw [BitVec.and_or_distrib_right, hm, BitVec.or_zero]
private theorem bv32_and_not_rsn_mask (x : BitVec 32) :
    ((x &&& ~~~0x00200000#32) &&& ~~~0x00200000#32) = x &&& ~~~0x00200000#32 := by
  rw [BitVec.and_assoc, BitVec.and_self]
theorem bv32_shl27_and_use (u : BitVec 32) : ((u <<< (27 : Nat)) &&& 0x07FFFFFF#32) = 0#32 := by
  ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_zero]
  by_cases h27 : i < 27
  · simp [h27]
  · have hm : (0x07FFFFFF#32 : BitVec 32)[i] = false := by
      rw [BitVec.getElem_eq_testBit_toNat, show (0x07FFFFFF#32 : BitVec 32).toNat = 0x07FFFFFF
        from rfl]
      exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide : 0x07FFFFFF < 2 ^ 27)
        (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [hm]
theorem bv32_use_mask (hdr u : BitVec 32) :
    (((hdr &&& 0x07FFFFFF#32) ||| (u <<< (27 : Nat))) &&& 0x07FFFFFF#32) =
      (hdr &&& 0x07FFFFFF#32) := by
  rw [BitVec.and_or_distrib_right, BitVec.and_assoc, BitVec.and_self, bv32_shl27_and_use,
    BitVec.or_zero]
private theorem bv32_mask_sub_eq {mask sub x y : BitVec 32} (hm : (mask &&& sub) = sub)
    (h : (x &&& mask) = (y &&& mask)) : (x &&& sub) = (y &&& sub) := by
  calc x &&& sub = (x &&& mask) &&& sub := by rw [BitVec.and_assoc, hm]
    _ = (y &&& mask) &&& sub := by rw [h]
    _ = y &&& sub := by rw [BitVec.and_assoc, hm]

private theorem arenaNextOff_congr_shrk {ar1 ar2 : List (BitVec 32)} {alen r : Nat}
    (h0 : (ar2[r]?.getD 0#32 &&& 0x00800000#32) = (ar1[r]?.getD 0#32 &&& 0x00800000#32))
    (h2 : ar2[r + 2]? = ar1[r + 2]?)
    (hpad : ∀ k, r + 3 + (ar1[r + 2]?.getD 0#32).toNat ≤ k →
      k < arenaNextOff ar1 alen r → ar2[k]? = ar1[k]?) :
    arenaNextOff ar2 alen r = arenaNextOff ar1 alen r := by
  unfold arenaNextOff; split
  · rfl
  · rename_i hnot; simp only [h2]; split
    · rfl
    · simp only [h0]; split
      · rename_i hle_p hshrk
        refine arenaSkipShrk_congr fun k hk1 hk2 => hpad k hk1 ?_
        unfold arenaNextOff; simp only [hnot, ↓reduceIte, hle_p, hshrk, ne_eq,
          not_false_eq_true]; exact hk2
      · rfl

/-! ## 2. Arena mask-preservation invariant, scan traversal, `RedSub`, and binary watches -/

@[expose] def ArenaMaskOk (mask : BitVec 32) (s : PlainState) (arena' : List (BitVec 32)) : Prop :=
  arena'.length = s.arena.length ∧
  (∀ k, k ∉ arenaClauseRefs s → arena'[k]? = s.arena[k]?) ∧
  ∀ r ∈ arenaClauseRefs s,
    (arena'[r]?.getD 0#32 &&& mask) = (s.arena[r]?.getD 0#32 &&& mask)

theorem arenaMask_refl (mask : BitVec 32) (s : PlainState) :
    ArenaMaskOk mask s s.arena :=
  ⟨rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem arenaMask_set {mask : BitVec 32} {s : PlainState} {arena' : List (BitVec 32)}
    (hp : ArenaMaskOk mask s arena') {r : Nat} (hr : r ∈ arenaClauseRefs s)
    (hlt : r < arena'.length) {v : BitVec 32}
    (hv : (v &&& mask) = (arena'[r] &&& mask)) :
    ArenaMaskOk mask s (arena'.set r v) := by
  refine ⟨by simp [hp.1], fun k hk => ?_, fun r' hr' => ?_⟩
  · have hne : r ≠ k := fun h => hk (h ▸ hr)
    rw [List.getElem?_set_ne hne]; exact hp.2.1 k hk
  · by_cases hrr' : r = r'
    · subst r'
      rw [List.getElem?_set_self hlt, Option.getD_some, hv]
      have := hp.2.2 r hr
      rwa [List.getElem?_eq_getElem hlt, Option.getD_some] at this
    · rw [List.getElem?_set_ne hrr']; exact hp.2.2 r' hr'

private theorem arenaClauseRefs_not_mem_inner {ar : List (BitVec 32)} {alen r k : Nat}
    (hr : r ∈ arenaScanRefs ar alen 0 alen) (hgt : r < k) (hk : k < arenaNextOff ar alen r) :
    k ∉ arenaScanRefs ar alen 0 alen :=
  fun hmem => by have := arenaScanRefs_disjoint hr hmem hgt; omega

theorem arenaMask_next {mask : BitVec 32} (hshrk : (mask &&& 0x00800000#32) = 0x00800000#32)
    {c : PlainCfg} {F0 : CNF Nat} {s : PlainState} (hinv : PlainCoreInv c F0 s)
    {arena' : List (BitVec 32)} (hp : ArenaMaskOk mask s arena') {r : Nat}
    (hr : r ∈ arenaClauseRefs s) :
    arenaNextOff arena' s.arena_len r = arenaNextOff s.arena s.arena_len r := by
  have := hinv.arena.refs_wf r hr
  exact arenaNextOff_congr_shrk (bv32_mask_sub_eq hshrk (hp.2.2 r hr))
    (hp.2.1 (r + 2) (arenaClauseRefs_not_mem_inner hr (by omega) (by omega)))
    (fun k _ hk2 => hp.2.1 k (arenaClauseRefs_not_mem_inner hr (by omega) hk2))

private theorem arenaPres_core {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    {arena' : List (BitVec 32)} (har_len : arena'.length = s.arena.length)
    (hout : ∀ k, k ∉ arenaClauseRefs s → arena'[k]? = s.arena[k]?)
    (hshrk : ∀ r ∈ arenaClauseRefs s,
      (arena'[r]?.getD 0#32 &&& 0x00800000#32) = (s.arena[r]?.getD 0#32 &&& 0x00800000#32))
    (hng_imp : ∀ r ∈ arenaClauseRefs s,
      arenaClauseGarb { s with arena := arena' } r = false → arenaClauseGarb s r = false)
    (hrsn_ng : ∀ idx < s.trail_end,
      let p := (s.trl[idx]?.getD 0#32).toNat
      let rsn := s.rsns[p / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 →
      arenaClauseGarb { s with arena := arena' } rsn.toNat = false)
    (hinv : PlainCoreInv c F0 s) :
    let s' : PlainState := { s with arena := arena' }
    arenaClauseRefs s' = arenaClauseRefs s ∧
    (∀ r ∈ arenaClauseRefs s, arenaClauseSize s' r = arenaClauseSize s r ∧
      arenaClauseLits s' r = arenaClauseLits s r) ∧
    PlainCoreInv c F0 s' := by
  intro s'
  have hnxt : ∀ r ∈ arenaClauseRefs s,
      arenaNextOff arena' s.arena_len r = arenaNextOff s.arena s.arena_len r := fun r hr => by
    have := hinv.arena.refs_wf r hr
    exact arenaNextOff_congr_shrk (hshrk r hr)
      (hout (r + 2) (arenaClauseRefs_not_mem_inner hr (by omega) (by omega)))
      (fun k hk1 hk2 => hout k (arenaClauseRefs_not_mem_inner hr (by omega) hk2))
  have hrefs : arenaClauseRefs s' = arenaClauseRefs s := arenaClauseRefs_congr rfl hnxt
  have hprops : ∀ r ∈ arenaClauseRefs s,
      arenaClauseSize s' r = arenaClauseSize s r ∧ arenaClauseLits s' r = arenaClauseLits s r := by
    intro r hr; have hwf := hinv.arena.refs_wf r hr; have hlen := hinv.lengths
    have hsz : arenaClauseSize s' r = arenaClauseSize s r := by
      unfold arenaClauseSize s'
      rw [hout (r + 2) (arenaClauseRefs_not_mem_inner hr (by omega) (by omega))]
    refine ⟨hsz, ?_⟩
    have hbd1 : r + 3 + arenaClauseSize s r ≤ s.arena.length := by
      have := hlen.arena_len_arr; have := hlen.arena_len_le; omega
    have hbd2 : r + 3 + arenaClauseSize s' r ≤ s'.arena.length := by
      rw [hsz]; dsimp only [s']; rw [har_len]; exact hbd1
    unfold arenaClauseLits; rw [hsz]
    apply List.ext_getElem
    · simp only [List.length_map, List.length_take, List.length_drop]; dsimp only [s']; rw [har_len]
    · intro k hk1 _
      have hks : k < arenaClauseSize s r := by
        simp only [List.length_map, List.length_take, List.length_drop] at hk1; omega
      simp only [List.getElem_map, List.getElem_take, List.getElem_drop]
      have hopt : s'.arena[r + 3 + k]? = s.arena[r + 3 + k]? :=
        hout (r + 3 + k) (arenaClauseRefs_not_mem_inner hr (by omega) (by omega))
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hopt
      exact congrArg BitVec.toNat (Option.some.inj hopt)
  have hlen' : s'.LengthsOk c :=
    { hinv.lengths with arena_len_arr := by dsimp [s']; rw [har_len, hinv.lengths.arena_len_arr] }
  have harena' : ArenaClausesInv c F0 s' := by
    refine ⟨hinv.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; dsimp only [s']
      rw [hnxt r hr, (hprops r hr).1]; exact hinv.arena.refs_wf r hr
    · intro r hr; rw [hrefs] at hr; unfold arenaHdr s'
      rw [hshrk r hr]; exact hinv.arena.no_shrk r hr
    · intro r hr hng l hl; rw [hrefs] at hr; rw [(hprops r hr).2] at hl
      exact hinv.arena.lits_lt r hr (hng_imp r hr hng) l hl
    · intro r hr hng; rw [hrefs] at hr; rw [(hprops r hr).2]
      exact hinv.arena.entails r hr (hng_imp r hr hng)
  refine ⟨hrefs, hprops,
    ⟨hlen', harena', hinv.watches.with_wstk rfl rfl rfl hrefs, hinv.cur_level_le,
      hinv.trail_lits_lt, hinv.trail_vars_nodup, hinv.vals_domain, hinv.vals_true_iff,
      hinv.vals_false_iff, hinv.lvl_le, hinv.trail_mono, hinv.levels_inhabited, hinv.level0_sound,
      hinv.trail_pos_inv, hinv.level0_rsn_none, ?_, ?_⟩⟩
  · intro idx hidx; dsimp only [s']; intro hne
    have hrs := hinv.reason_inv idx hidx hne
    split at hrs <;> split
    · exact hrs
    · rename_i h1 h2; exact absurd h1 h2
    · rename_i h1 h2; exact absurd h2 h1
    · rename_i hmsb
      have hmsb0 : (s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 &&&
          0x80000000#32) = 0#32 := Classical.not_not.mp hmsb
      exact ⟨hrefs ▸ hrs.1, hrsn_ng idx hidx hne hmsb0,
        fun q hq => hrs.2.2 q ((hprops _ hrs.1).2 ▸ hq)⟩
  · intro idx hidx; dsimp only [s']; intro hne hmsb
    have hrs := hinv.reason_inv idx hidx hne; split at hrs
    · rename_i h1; exact absurd hmsb h1
    · exact (hprops _ hrs.1).2 ▸ hinv.reason_lit_mem idx hidx hne hmsb

theorem arenaMask_core {mask : BitVec 32} (hshrk : (mask &&& 0x00800000#32) = 0x00800000#32)
    (hgarb : (mask &&& 0x00080000#32) = 0x00080000#32)
    {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hinv : PlainCoreInv c F0 s) {arena' : List (BitVec 32)}
    (hp : ArenaMaskOk mask s arena') :
    let s' : PlainState := { s with arena := arena' }
    arenaClauseRefs s' = arenaClauseRefs s ∧
    (∀ r ∈ arenaClauseRefs s, arenaClauseSize s' r = arenaClauseSize s r ∧
      arenaClauseGarb s' r = arenaClauseGarb s r ∧
      arenaClauseLits s' r = arenaClauseLits s r) ∧
    PlainCoreInv c F0 s' := by
  have hgarb_eq : ∀ r ∈ arenaClauseRefs s,
      arenaClauseGarb { s with arena := arena' } r = arenaClauseGarb s r := fun r hr => by
    unfold arenaClauseGarb arenaHdr; rw [bv32_mask_sub_eq hgarb (hp.2.2 r hr)]
  obtain ⟨hrefs, hprops, hcore⟩ := arenaPres_core hp.1 hp.2.1
    (fun r hr => bv32_mask_sub_eq hshrk (hp.2.2 r hr))
    (fun r hr h => by rw [hgarb_eq r hr] at h; exact h)
    (fun idx hidx hne hmsb => by
      have hrs := hinv.reason_inv idx hidx hne
      simp only [hmsb, ne_eq, not_true_eq_false, ↓reduceIte] at hrs
      rw [hgarb_eq _ hrs.1]; exact hrs.2.1) hinv
  exact ⟨hrefs, fun r hr => ⟨(hprops r hr).1, hgarb_eq r hr, (hprops r hr).2⟩, hcore⟩

theorem arenaMask_reasonsMarked {mask : BitVec 32}
    (hrsn : (mask &&& 0x00200000#32) = 0x00200000#32)
    {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hinv : PlainCoreInv c F0 s) (hrm : ReasonsMarked s)
    {arena' : List (BitVec 32)} (hp : ArenaMaskOk mask s arena') :
    ReasonsMarked { s with arena := arena' } := by
  intro idx hidx
  dsimp only at hidx ⊢
  intro hpos hmsb
  have hne : s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
    intro heq; rw [heq] at hmsb; revert hmsb; decide
  have hrs := hinv.reason_inv idx hidx hne
  simp only [hmsb, ne_eq, not_true_eq_false, ↓reduceIte] at hrs
  have heq : (arenaHdr { s with arena := arena' }
      (s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat &&&
      0x00200000#32) =
      (arenaHdr s (s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat &&&
      0x00200000#32) := by
    unfold arenaHdr; exact bv32_mask_sub_eq hrsn (hp.2.2 _ hrs.1)
  rw [heq]; exact hrm idx hidx hpos hmsb

private theorem arenaScan_step_aux {ar : List (BitVec 32)} {alen : Nat} :
    ∀ {fuel pos p : Nat}, alen - pos ≤ fuel →
      p ∈ arenaScanRefs ar alen pos fuel →
      (arenaNextOff ar alen p = alen ∨ arenaNextOff ar alen p + 3 ≤ alen) →
      arenaNextOff ar alen p = alen ∨ arenaNextOff ar alen p ∈ arenaScanRefs ar alen pos fuel
  | 0, _, _, _, hp, _ => by simp [arenaScanRefs] at hp
  | fuel + 1, pos, p, hfl, hp, hnxt => by
    unfold arenaScanRefs at hp ⊢; split at hp
    · rename_i hle
      have hnb := arenaNextOff_bounds (ar := ar) (alen := alen) (cref := pos) hle
      simp only [hle, ↓reduceIte, List.mem_cons] at hp ⊢
      rcases hp with rfl | hrest
      · rcases hnxt with h | h
        · exact Or.inl h
        · refine Or.inr (Or.inr ?_)
          cases fuel with | zero => omega | succ f' => unfold arenaScanRefs; simp [h]
      · exact (arenaScan_step_aux (by omega) hrest hnxt).imp id Or.inr
    · simp at hp

theorem arenaScan_step {ar : List (BitVec 32)} {alen p : Nat}
    (hchain : ∀ r ∈ arenaScanRefs ar alen 0 alen,
      arenaNextOff ar alen r = alen ∨ arenaNextOff ar alen r + 3 ≤ alen)
    (hp : p ∈ arenaScanRefs ar alen 0 alen) :
    arenaNextOff ar alen p = alen ∨ arenaNextOff ar alen p ∈ arenaScanRefs ar alen 0 alen :=
  arenaScan_step_aux (Nat.le_refl _) hp (hchain p hp)

theorem arenaScan_zero {s : PlainState} (hlen : s.arena_len = 0 ∨ 3 ≤ s.arena_len) :
    s.arena_len = 0 ∨ 0 ∈ arenaClauseRefs s := by
  rcases hlen with h0 | h3
  · exact Or.inl h0
  · refine Or.inr ?_; unfold arenaClauseRefs
    cases h : s.arena_len
    · omega
    · unfold arenaScanRefs; simp [h ▸ h3]

def RedSub (n : Nat) (xs xs0 : List (BitVec 32)) : Prop :=
  xs.length = xs0.length ∧ ∀ k < n, ∃ j < n, xs[k]? = xs0[j]?
theorem redSub_refl (n : Nat) (xs : List (BitVec 32)) : RedSub n xs xs :=
  ⟨rfl, fun k hk => ⟨k, hk, rfl⟩⟩
theorem redSub_swap {n i j : Nat} {xs xs0 : List (BitVec 32)}
    (h : RedSub n xs xs0) (hi : i < n) (hj : j < n) (hil : i < xs.length) (hjl : j < xs.length) :
    RedSub n ((xs.set i xs[j]).set j xs[i]) xs0 := by
  refine ⟨by simp [h.1], fun k hk => ?_⟩
  by_cases hkj : k = j
  · subst hkj; rw [List.getElem?_set_self (by simpa using hjl), ← List.getElem?_eq_getElem hil]
    exact h.2 i hi
  · rw [List.getElem?_set_ne (Ne.symm hkj)]
    by_cases hki : k = i
    · subst hki; rw [List.getElem?_set_self hil, ← List.getElem?_eq_getElem hjl]; exact h.2 j hj
    · rw [List.getElem?_set_ne (Ne.symm hki)]; exact h.2 k hk
theorem redSub_bound {n cap : Nat} {xs xs0 : List (BitVec 32)}
    (h : RedSub n xs xs0) (hbd : ∀ k < n, (xs0[k]?.getD 0#32).toNat + 2 < cap)
    {k : Nat} (hk : k < n) (hkl : k < xs.length) : xs[k].toNat + 2 < cap := by
  obtain ⟨j, hj, heq⟩ := h.2 k hk
  have hg : xs[k] = xs0[j]?.getD 0#32 := by
    simpa [List.getElem?_eq_getElem hkl] using congrArg (·.getD 0#32) heq
  rw [hg]; exact hbd j hj
@[expose] def BinWatchOk (c : PlainCfg) (F0 : CNF Nat) (l : Nat) (w : BitVec 32) : Prop :=
  (w &&& 0x80000000#32) ≠ 0#32 ∧ (w &&& 0x7FFFFFFF#32).toNat < 2 * c.mv ∧
  F0.EntailsClause (cnfClause [l, (w &&& 0x7FFFFFFF#32).toNat])
theorem binWatch_ne_sent {c : PlainCfg} {F0 : CNF Nat} {l : Nat} {w : BitVec 32}
    (hw : BinWatchOk c F0 l w) : w ≠ 0xFFFFFFFF#32 := fun heq => by
  subst heq; have hmv := c.hmv; unfold dimacsBound at hmv
  have hlt : (0xFFFFFFFF#32 &&& 0x7FFFFFFF#32).toNat = 0x7FFFFFFF := by decide
  have := hw.2.1; omega
theorem watchSliceOk_of_bin {c : PlainCfg} {F0 : CNF Nat} {s : PlainState} {l : Nat} :
    ∀ len p, (∀ k < len, ∃ w, s.wstk[p + k]? = some w ∧ BinWatchOk c F0 l w) →
      WatchSliceOk c F0 s l p len
  | 0, _, _ => .empty
  | len + 1, p, h => by
    obtain ⟨w, hw, hflg, hlt, hent⟩ := h 0 (Nat.zero_lt_succ len); rw [Nat.add_zero] at hw
    exact .bin hw hflg hlt hent (watchSliceOk_of_bin len (p + 1) fun k hk => by
      have := h (k + 1) (by omega); rwa [show p + (k + 1) = p + 1 + k from by omega] at this)
theorem reducePct_le {logv : BitVec 64} (h1 : 1 ≤ logv.toNat) :
    logv ≠ 0#64 ∧ (900#64 - 400#64 / logv).toNat ≤ 900 := by
  have hne : logv ≠ 0#64 := fun h => by subst h; simp at h1
  have hdiv : (400#64 / logv).toNat ≤ 400 := by
    rw [BitVec.toNat_udiv]; exact Nat.le_trans (Nat.div_le_self _ _) (by decide)
  have hsub : (900#64 - 400#64 / logv).toNat = 900 - (400#64 / logv).toNat := by
    simpa [BitVec.toNat_ofNat] using
      BitVec.toNat_sub_of_le (x := 900#64) (y := 400#64 / logv) (by bv_omega)
  exact ⟨hne, by omega⟩
theorem reduceTarget_le {rc p : BitVec 64} (hrc : rc.toNat < 2 ^ 30) (hp : p.toNat ≤ 900) :
    ((rc * p) / 1000#64).toNat ≤ rc.toNat := by
  rw [BitVec.toNat_udiv, BitVec.toNat_mul, show (1000#64 : BitVec 64).toNat = 1000 from rfl]
  have : rc.toNat * p.toNat ≤ rc.toNat * 900 := Nat.mul_le_mul_left _ hp
  rw [Nat.mod_eq_of_lt (by omega)]; exact Nat.div_le_of_le_mul (by omega)

/-! ## 3. Verified `Func.wp` contracts for `plain_red_less`, `plain_lit_rank`,
`plain_recompute_tiers`, `plain_mark_reasons` -/

end PlainReduceHelpers

open PlainReduceHelpers

theorem plain_red_less_wp (Γ : Env) :
    ∀ args m Q X, plainRedLessSpec args m Q X →
      Func.wp Γ plain_red_less_body args m Q X := by
  rintro ⟨ar_ptr, a, b, ⟨⟩⟩ m Q X ⟨ar, R, ha, hb, hm, hQ⟩
  c0_steps!; all_goals exact hQ _

theorem plain_lit_rank_wp (Γ : Env) :
    ∀ args m Q X, plainLitRankSpec args m Q X →
      Func.wp Γ plain_lit_rank_body args m Q X := by
  rintro ⟨vals_ptr, lvl_ptr, l, ⟨⟩⟩ m Q X ⟨vals, lvl, R, hvl, hll, hm, hQ⟩
  c0_steps!; all_goals exact hQ _

private theorem PlainHeur.LengthsOk.with_tiers {c : PlainCfg} {h : PlainHeur}
    (hok : h.LengthsOk c) (t1 t2 : BitVec 64) :
    ({ h with tier1 := t1, tier2 := t2 } : PlainHeur).LengthsOk c := { hok with }

theorem plain_recompute_tiers_wp (Γ : Env) :
    ∀ args m Q X, plainRecomputeTiersSpec args m Q X →
      Func.wp Γ plain_recompute_tiers_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hgu : s.heur.glue_used.length = 64 := hlen.heur_ok.glue_used_len
  c0_unmdata; c0_steps!
  refine wp_loop_inv (ts := [i64, i64])
    (fun v m1 => v.2.1.toNat ≤ 64 ∧ (PlainMem c s ⋆ R) m1) (fun v _ => 64 - v.2.1.toNat) ?_ ?_
  · intro J hJ; c0_steps!; exact hJ (0#64, 0#64, ()) m ⟨by simp, hm⟩
  · rintro J ⟨total, g, ⟨⟩⟩ m1 ⟨hg, hm1⟩ hJ; dsimp only at hg hJ; c0_unmdata; c0_steps!
    · have hg1 : (g + 1).toNat = g.toNat + 1 ∧ g.toNat < 64 := by bv_omega
      exact hJ _ m1 (by dsimp only; omega) ⟨by dsimp only; omega, hm1⟩
    · refine wp_loop_inv (ts := [i64, i64, i64, .bool])
        (fun v m2 => v.1.toNat ≤ 64 ∧ (PlainMem c s ⋆ R) m2) (fun v _ => 64 - v.1.toNat) ?_ ?_
      · intro L hL; c0_steps!; exact hL (0#64, 2#64, 0#64, false, ()) m1 ⟨by simp, hm1⟩
      · rintro L ⟨g2, t1, acc, got1, ⟨⟩⟩ m2 ⟨hg2, hm2⟩ hL; dsimp only at hg2 hL
        c0_unmdata; c0_steps!
        all_goals first
          | exact hQ _ _ (hlen.heur_ok.with_tiers _ _) (by c0_frame)
          | (have hg2_1 : (g2 + 1).toNat = g2.toNat + 1 ∧ g2.toNat < 64 := by bv_omega
             exact hL _ m2 (by dsimp only; omega) ⟨by dsimp only; omega, hm2⟩)
    · exact hQ _ _ (hlen.heur_ok.with_tiers _ _) (by c0_frame)

theorem PlainReduceTactics.bv32_lt_msb_of_and_zero {r : BitVec 32}
    (h : (r &&& 0x80000000#32) = 0#32) : r.toNat < 0x80000000 := by
  have hm := congrArg BitVec.msb h
  rw [BitVec.msb_and, show (0x80000000#32 : BitVec 32).msb = true from rfl,
    Bool.and_true, BitVec.msb_zero] at hm
  rw [BitVec.msb_eq_false_iff_two_mul_lt] at hm
  omega

private theorem bv32_or_rsn_nz (x : BitVec 32) :
    ((x ||| 0x00200000#32) &&& 0x00200000#32) ≠ 0#32 := by
  intro h
  have ht := congrArg (fun z : BitVec 32 => z[21]) h
  simp [show (0x00200000#32 : BitVec 32)[21] = true from rfl] at ht

private def MarkRsnInv (s : PlainState) (set_flag : Bool)
    (n : Nat) (arena' : List (BitVec 32)) : Prop :=
  n ≤ s.trail_end ∧ ArenaMaskOk (~~~0x00200000#32) s arena' ∧
  (set_flag = true → ∀ idx < n,
    let v := (s.trl[idx]?.getD 0#32).toNat / 2
    let rsn := s.rsns[v]?.getD 0xFFFFFFFF#32
    0 < (s.lvl[v]?.getD 0#32).toNat → (rsn &&& 0x80000000#32) = 0#32 →
    (arena'[rsn.toNat]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32)

private theorem markRsnInv_skip {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    {set_flag : Bool} {i : Nat} {arena' : List (BitVec 32)}
    (hinv : PlainCoreInv c F0 s) (hm : MarkRsnInv s set_flag i arena') (hi : i < s.trail_end)
    (hbad : set_flag = true →
      (s.trl[i]?.getD 0#32).toNat / 2 < c.mv →
      0 < (s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat →
      (s.rsns[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat < 0x80000000 →
      (s.rsns[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat + 3 ≤ s.arena_len →
      False) :
    MarkRsnInv s set_flag (i + 1) arena' := by
  refine ⟨by omega, hm.2.1, fun hf idx hidx hpos hmsb => ?_⟩
  by_cases hlt : idx < i
  · exact hm.2.2 hf idx hlt hpos hmsb
  · have heq : idx = i := by omega
    subst heq
    have hv : (s.trl[idx]?.getD 0#32).toNat / 2 < c.mv := by
      have := hinv.trail_lits_lt idx hi; omega
    have hr_lt := PlainReduceTactics.bv32_lt_msb_of_and_zero hmsb
    have hrs := hinv.reason_inv idx hi (PlainReduceTactics.bv32_ne_allOnes_of_ult hr_lt)
    simp only [hmsb, ne_eq, not_true_eq_false, ↓reduceIte] at hrs
    have hwf := (hinv.arena.refs_wf _ hrs.1).1
    exact absurd (hbad hf hv hpos hr_lt hwf) id

private theorem markRsnInv_set {s : PlainState} {i r : Nat} {v : BitVec 32}
    {arena' : List (BitVec 32)}
    (hm : MarkRsnInv s true i arena') (hi : i < s.trail_end)
    (hr : r ∈ arenaClauseRefs s) (hlt : r < arena'.length)
    (hr_eq : r = (s.rsns[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat)
    (hvm : (v &&& ~~~0x00200000#32) = (arena'[r] &&& ~~~0x00200000#32))
    (hv21 : (v &&& 0x00200000#32) ≠ 0#32) :
    MarkRsnInv s true (i + 1) (arena'.set r v) := by
  refine ⟨by omega, arenaMask_set hm.2.1 hr hlt hvm, fun _ idx hidx hpos hmsb => ?_⟩
  by_cases hcur : (s.rsns[(s.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat = r
  · rw [hcur, List.getElem?_set_self hlt, Option.getD_some]; exact hv21
  · have hne : idx ≠ i := fun h => hcur (h ▸ hr_eq.symm)
    have hlti : idx < i := Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hidx) hne
    rw [List.getElem?_set_ne (Ne.symm hcur)]
    exact hm.2.2 rfl idx hlti hpos hmsb

private theorem markRsn_cont {c : PlainCfg} {s : PlainState} {set_flag : Bool}
    {i : BitVec 64} {arena_new : List (BitVec 32)} {R : Mem 64 → Prop}
    {J_lp : Cont [i64]} {m2 : Mem 64}
    (hJ_lp : ∀ (ys : Tup Val [i64]) (m' : Mem 64),
      s.trail_end - ys.fst.toNat < s.trail_end - i.toNat →
        (∃ a', MarkRsnInv s set_flag ys.fst.toNat a' ∧
          (PlainMem c { s with arena := a' } ⋆ R) m') → J_lp ys m')
    (hm2 : (PlainMem c { s with arena := arena_new } ⋆ R) m2)
    (hlt : s.trail_end - (i + 1).toNat < s.trail_end - i.toNat)
    (hinv_new : MarkRsnInv s set_flag (i + 1).toNat arena_new) :
    J_lp (i + 1, ()) m2 :=
  hJ_lp _ m2 hlt ⟨arena_new, hinv_new, hm2⟩

private theorem markRsn_prep {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    {arena' : List (BitVec 32)} (hinv : PlainCoreInv c F0 s)
    (hcur_len : arena'.length = c.arena_cap) {i : BitVec 64}
    (hi_lt : i.toNat < s.trail_end) (hi_trl : i.toNat < s.trl.length)
    (hlt_mod : ∀ h : (s.trl[i.toNat]'hi_trl >>> (1 : BitVec 32)).toNat % 2 ^ 64 < s.rsns.length,
      (s.rsns[(s.trl[i.toNat]'hi_trl >>> (1 : BitVec 32)).toNat % 2 ^ 64]'h).toNat < 0x80000000) :
    let hidx_nat := (s.trl[i.toNat]'hi_trl >>> (1 : Nat)).toNat
    let r := (s.rsns[hidx_nat]?.getD 0xFFFFFFFF#32).toNat
    hidx_nat < s.rsns.length ∧
      (s.trl[i.toNat]'hi_trl >>> (1 : BitVec 32)).toNat % 2 ^ 64 < s.rsns.length ∧
      r ∈ arenaClauseRefs s ∧ r < arena'.length ∧
      r = (s.rsns[(s.trl[i.toNat]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat := by
  have hilt := hinv.trail_lits_lt i.toNat hi_lt; have hmv := c.hmv; unfold dimacsBound at hmv
  have htrl_val : (s.trl[i.toNat]'hi_trl).toNat = (s.trl[i.toNat]?.getD 0#32).toNat := by
    simp [List.getElem?_eq_getElem hi_trl]
  have hv_eq : (s.trl[i.toNat]'hi_trl >>> (1 : Nat)).toNat =
      (s.trl[i.toNat]?.getD 0#32).toNat / 2 := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one, htrl_val]
  have hidx_nat : (s.trl[i.toNat]'hi_trl >>> (1 : Nat)).toNat < s.rsns.length := by
    rw [hv_eq, hinv.lengths.rsns_len]; omega
  have h32 := (s.trl[i.toNat]'hi_trl).isLt
  have hv_mod : (s.trl[i.toNat]'hi_trl >>> (1 : BitVec 32)).toNat % 2 ^ 64 =
      (s.trl[i.toNat]?.getD 0#32).toNat / 2 := by
    rw [show (1 : BitVec 32) = 1#32 from rfl, PlainReduceTactics.bv_c0_shr1_32,
      Nat.mod_eq_of_lt (by omega), htrl_val]
  have hrsn_mod : s.rsns[(s.trl[i.toNat]'hi_trl >>> (1 : BitVec 32)).toNat % 2 ^ 64]?.getD
      0xFFFFFFFF#32 = s.rsns[(s.trl[i.toNat]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 :=
    congrArg (fun k => s.rsns[k]?.getD 0xFFFFFFFF#32) hv_mod
  have hrsn_nat : s.rsns[(s.trl[i.toNat]'hi_trl >>> (1 : Nat)).toNat]?.getD 0xFFFFFFFF#32 =
      s.rsns[(s.trl[i.toNat]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 :=
    congrArg (fun k => s.rsns[k]?.getD 0xFFFFFFFF#32) hv_eq
  have hidx_mod : (s.trl[i.toNat]'hi_trl >>> (1 : BitVec 32)).toNat % 2 ^ 64 < s.rsns.length := by
    rw [hv_mod, hinv.lengths.rsns_len]; omega
  have hr_lt : (s.rsns[(s.trl[i.toNat]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat <
      0x80000000 := by
    rw [← hrsn_mod, List.getElem?_eq_getElem hidx_mod, Option.getD_some]; exact hlt_mod hidx_mod
  have hrs := hinv.reason_inv i.toNat hi_lt (PlainReduceTactics.bv32_ne_allOnes_of_ult hr_lt)
  simp only [PlainReduceTactics.bv32_and_msb_zero_of_ult hr_lt,
    ne_eq, not_true_eq_false, ↓reduceIte] at hrs
  have href : (s.rsns[(s.trl[i.toNat]'hi_trl >>> (1 : Nat)).toNat]?.getD 0xFFFFFFFF#32).toNat ∈
      arenaClauseRefs s := by rw [hrsn_nat]; exact hrs.1
  have h3 := (hinv.arena.refs_wf _ href).1; have har_le := hinv.lengths.arena_len_le
  exact ⟨hidx_nat, hidx_mod, href, by rw [hcur_len]; omega, congrArg BitVec.toNat hrsn_nat⟩

private theorem markRsn_skip_false {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    (hinv : PlainCoreInv c F0 s) {i : BitVec 64} (hi_trl : i.toNat < s.trl.length)
    (hv : (s.trl[i.toNat]?.getD 0#32).toNat / 2 < c.mv)
    (hpos : 0 < (s.lvl[(s.trl[i.toNat]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    (hr_lt : (s.rsns[(s.trl[i.toNat]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat <
      0x80000000)
    (hwf : (s.rsns[(s.trl[i.toNat]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32).toNat + 3 ≤
      s.arena_len)
    (hnot : ¬ ((s.trl[i.toNat]'hi_trl).toNat / 2 % 2 ^ 64 < c.mv % 2 ^ 64) ∨
      ¬ 0 < (s.lvl[(s.trl[i.toNat]'hi_trl).toNat / 2 % 2 ^ 64]?.getD 0#32).toNat ∨
      ¬ (s.rsns[(s.trl[i.toNat]'hi_trl).toNat / 2 % 2 ^ 64]?.getD 0xFFFFFFFF#32).toNat <
        0x80000000 ∨
      ¬ ((s.rsns[(s.trl[i.toNat]'hi_trl).toNat / 2 % 2 ^ 64]?.getD 0xFFFFFFFF#32).toNat +
          BitVec.toNat (3 : BitVec 64)) % 2 ^ 64 ≤ s.arena_len % 2 ^ 64) :
    False := by
  have hmv := c.hmv; have har := c.harena; unfold dimacsBound at hmv har
  have _ := hinv.lengths.arena_len_le; have h32 := (s.trl[i.toNat]'hi_trl).isLt
  have hteq : (s.trl[i.toNat]'hi_trl).toNat / 2 % 2 ^ 64 =
      (s.trl[i.toNat]?.getD 0#32).toNat / 2 := by
    rw [Nat.mod_eq_of_lt (by omega)]; simp [List.getElem?_eq_getElem hi_trl]
  rw [hteq] at hnot
  rcases hnot with h1 | h2 | h3 | h4
  · exact h1 (by rw [Nat.mod_eq_of_lt (by omega)]; exact hv)
  · exact h2 hpos
  · exact h3 hr_lt
  · rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h4
    exact h4 hwf

theorem plain_mark_reasons_wp (Γ : Env) :
    ∀ args m Q X, plainMarkReasonsSpec args m Q X →
      Func.wp Γ plain_mark_reasons_body args m Q X := by
  rintro ⟨h, set_flag, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  have hlen := hinv.lengths; have hmv := c.hmv; have har := c.harena; unfold dimacsBound at hmv har
  c0_unmdata; c0_steps!
  refine wp_loop_inv (ts := [i64])
    (fun v m1 => ∃ arena' : List (BitVec 32),
      MarkRsnInv s set_flag v.1.toNat arena' ∧
      (PlainMem c { s with arena := arena' } ⋆ R) m1)
    (fun v _ => s.trail_end - v.1.toNat) ?_ ?_
  · intro J_lp hJ_lp; c0_steps!
    exact hJ_lp (0#64, ()) m ⟨s.arena, ⟨by simp, arenaMask_refl _ s, fun _ _ h => by simp at h⟩,
      hm⟩
  · rintro J_lp ⟨i, ⟨⟩⟩ m1 ⟨arena', ⟨hi, hp, hrm⟩, hm1⟩ hJ_lp
    dsimp only at hi hJ_lp
    have hcur_len : arena'.length = c.arena_cap := hp.1.trans hlen.arena_len_arr
    have htrl_len := hlen.trl_len; have hte_le := hlen.trail_end_le
    have hlvl_len := hlen.lvl_len; have hrsn_len := hlen.rsns_len
    have har_len : s.arena_len ≤ arena'.length := hp.1 ▸ hlen.arena_len_arr ▸ hlen.arena_len_le
    cases set_flag
    · c0_unmdata; c0_steps
      all_goals first
        | contradiction
        | (obtain ⟨hrefs, hprops, hcore'⟩ := arenaMask_core (by decide) (by decide) hinv hp
           exact hQ arena' m1 hrefs hprops (fun h => by cases h) hcore' hm1)
        | (have hi1 : (i + 1).toNat = i.toNat + 1 ∧ i.toNat < s.trail_end := by bv_omega
           exact hJ_lp _ m1 (by dsimp only; omega)
             ⟨arena', ⟨by dsimp only; omega, hp, fun h => by cases h⟩, hm1⟩)
        | (have hi1 : (i + 1).toNat = i.toNat + 1 ∧ i.toNat < s.trail_end := by bv_omega
           have hi_trl : i.toNat < s.trl.length := by omega
           obtain ⟨hidx_nat, hidx_mod, href, hbd, _⟩ :=
             markRsn_prep hinv hcur_len hi1.2 hi_trl (fun _ => by c0_bound)
           rw [List.getElem?_eq_getElem hidx_nat, Option.getD_some] at href hbd
           refine markRsn_cont hJ_lp (by assumption) (by omega) ?_
           rw [hi1.1]
           exact ⟨by omega, arenaMask_set hp (by simpa only [bv_c0_zext32_64] using href)
             (by simpa only [bv_c0_zext32_64] using hbd) (bv32_and_not_rsn_mask _),
             fun h => by cases h⟩)
    · c0_unmdata; c0_steps
      all_goals first
        | contradiction
        | (have hte : i.toNat = s.trail_end := by bv_omega
           obtain ⟨hrefs, hprops, hcore'⟩ := arenaMask_core (by decide) (by decide) hinv hp
           exact hQ arena' m1 hrefs hprops
             (fun _ idx hidx => hrm rfl idx (hte ▸ hidx)) hcore' hm1)
        | (have hi1 : (i + 1).toNat = i.toNat + 1 ∧ i.toNat < s.trail_end := by bv_omega
           have hi_trl : i.toNat < s.trl.length := by omega
           refine hJ_lp _ m1 (by dsimp only; omega) ⟨arena', ?_, hm1⟩
           rw [show (i + 1, ()).fst.toNat = i.toNat + 1 from hi1.1]
           refine markRsnInv_skip hinv ⟨hi, hp, hrm⟩ hi1.2 fun _ hv hpos hr_lt hwf => ?_
           refine markRsn_skip_false hinv hi_trl hv hpos hr_lt hwf ?_
           first
             | exact Or.inl (by assumption)
             | exact Or.inr (Or.inl (by
                 rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                 simpa using (by assumption : ¬ BitVec.toNat (0 : BitVec 64) < _)))
             | exact Or.inr (Or.inr (Or.inl (by
                 rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                 assumption)))
             | exact Or.inr (Or.inr (Or.inr (by
                 rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                 assumption))))
        | (have hi1 : (i + 1).toNat = i.toNat + 1 ∧ i.toNat < s.trail_end := by bv_omega
           have hi_trl : i.toNat < s.trl.length := by omega
           obtain ⟨hidx_nat, _, href, hbd, hrsn_eq⟩ :=
             markRsn_prep hinv hcur_len hi1.2 hi_trl (fun _ => by c0_bound)
           rw [List.getElem?_eq_getElem hidx_nat, Option.getD_some] at href hbd hrsn_eq
           refine markRsn_cont hJ_lp (by assumption) (by omega) ?_
           rw [hi1.1]
           have h21 : (2097152 : BitVec 32) = 0x00200000#32 := BitVec.eq_of_toNat_eq rfl
           exact markRsnInv_set ⟨hi, hp, hrm⟩ hi1.2
             (by simpa only [bv_c0_zext32_64] using href)
             (by simpa only [bv_c0_zext32_64] using hbd)
             (by simpa only [bv_c0_zext32_64] using hrsn_eq)
             (by rw [h21]; exact bv32_or_rsn_mask _) (by rw [h21]; exact bv32_or_rsn_nz _))

private def plainArenaRest (c : PlainCfg) (s : PlainState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.d_cur s.d_val ⋆
  array64 (c.hdr + 32) (hdrTailWords c s) ⋆
  (array (t := i8) c.pVals s.vals ⋆ array (t := i8) c.pMark s.mrk ⋆
   array (t := i32) c.pLevel s.lvl ⋆ array (t := i32) c.pReason s.rsns ⋆
   array (t := i32) c.pTrail s.trl ⋆ array (t := i32) c.pTrailPos s.trail_pos ⋆
   array (t := i32) c.pTmp s.tmp ⋆ array (t := i32) c.pWvec s.wvec ⋆
   array (t := i32) c.pWstk s.wstk ⋆ array (t := i32) c.pMinStk s.min_stk ⋆
   array (t := i32) c.pMinClr s.min_clr) ⋆ PlainHeurArrays c s.heur ⋆ c.pad

private theorem plainMem_swap_arena (c : PlainCfg) (s : PlainState) :
    PlainMem c s = (array (t := i32) c.pArena s.arena ⋆ plainArenaRest c s) := by
  unfold PlainMem PlainCoreArrays plainArenaRest; ac_rfl

private theorem PlainHeur.LengthsOk.with_red_refs {c : PlainCfg} {h : PlainHeur}
    (hok : h.LengthsOk c) {rr : List (BitVec 32)} (hrr : rr.length = c.red_cap) :
    ({ h with red_refs := rr } : PlainHeur).LengthsOk c :=
  { hok with red_refs_len := hrr }

private theorem sortReds_ch_eq (root : BitVec 64) (hbd : root.toNat < 2 ^ 30) :
    ((root <<< (1 : Nat)) + (1 : BitVec 64)).toNat = 2 * root.toNat + 1 := by
  have hsh := PlainReduceTactics.bv_c0_shl1n_64 root; bv_omega
private theorem sortReds_ch1_eq (root : BitVec 64) (hbd : root.toNat < 2 ^ 30) :
    ((root <<< (1 : Nat) + (1 : BitVec 64)) + (1 : BitVec 64)).toNat = 2 * root.toNat + 2 := by
  rw [BitVec.toNat_add, sortReds_ch_eq root hbd]; bv_omega
private theorem bv64_gt0_of_lt {x : BitVec 64} (h : (0 : BitVec 64).toNat < x.toNat) :
    0 < x.toNat := by simpa using h
private theorem bv64_sub1_eq {x : BitVec 64} (h : 0 < x.toNat) :
    (x - (1 : BitVec 64)).toNat = x.toNat - 1 := by bv_omega
private theorem bv64_ch_lt {rt bnd : BitVec 64} (hbd : rt.toNat < 2 ^ 30)
    (heq : (rt <<< (1 : Nat) + (1 : BitVec 64)).toNat = 2 * rt.toNat + 1)
    (hnot : ¬ bnd.toNat ≤ (2 * rt.toNat + (1 : BitVec 64).toNat) % 2 ^ 64) :
    (rt <<< (1 : Nat) + (1 : BitVec 64)).toNat < bnd.toNat := by
  rw [heq]; rw [show (1 : BitVec 64).toNat = 1 from rfl] at hnot
  have : (2 * rt.toNat + 1) % 2 ^ 64 = 2 * rt.toNat + 1 := Nat.mod_eq_of_lt (by omega); omega
private theorem bv64_ch1_lt {rt bnd : BitVec 64} (hbd : rt.toNat < 2 ^ 30)
    (heq1 : ((rt <<< (1 : Nat) + (1 : BitVec 64)) + (1 : BitVec 64)).toNat = 2 * rt.toNat + 2)
    (h1 : (2 * rt.toNat + (1 : BitVec 64).toNat + (1 : BitVec 64).toNat) % 2 ^ 64 < bnd.toNat) :
    ((rt <<< (1 : Nat) + (1 : BitVec 64)) + (1 : BitVec 64)).toNat < bnd.toNat := by
  rw [heq1]; rw [show (1 : BitVec 64).toNat = 1 from rfl] at h1
  have : (2 * rt.toNat + 1 + 1) % 2 ^ 64 = 2 * rt.toNat + 2 := Nat.mod_eq_of_lt (by omega); omega

private theorem sortReds_call_rl {Γ : Env}
    (hRL : ∀ args m Q X, plainRedLessSpec args m Q X →
      Γ "plain_red_less" [i64, i32, i32] [.bool] args m Q X)
    {c : PlainCfg} {s : PlainState} {R : Mem 64 → Prop} {rr : List (BitVec 32)}
    {m : Mem 64} {n i j : Nat} {a b : BitVec 32}
    (hi : i < n) (hj : j < n) (hil : i < rr.length) (hjl : j < rr.length)
    (hsub : RedSub n rr s.heur.red_refs)
    (hbd : ∀ k < n, (s.heur.red_refs[k]?.getD 0#32).toNat + 2 < c.arena_cap)
    (har_len : s.arena.length = c.arena_cap) (ha : a = rr[i]) (hb : b = rr[j])
    (hm : (PlainMem c { s with heur := { s.heur with red_refs := rr } } ⋆ R) m)
    {rs : List Ty} {Q : Post rs} {X : XPost} {k : Tup Val [.bool] → Expr Val Cont rs}
    (hk : ∀ res : Bool, wp Γ Q X (k (res, ())) m) :
    wp Γ Q X (.call (rs := rs) (as := [i64, i32, i32]) (bs := [.bool])
      "plain_red_less" (Arg.var c.pArena, Arg.var a, Arg.var b, ()) k) m := by
  rw [plainMem_swap_arena] at hm
  have hm' : (array (t := i32) c.pArena s.arena ⋆
      (plainArenaRest c { s with heur := { s.heur with red_refs := rr } } ⋆ R)) m := sep_ac hm
  refine LeanQbe.T.wp_call_of_spec _ _ (hRL (c.pArena, a, b, ()) m _ X
    ⟨s.arena, _, har_len ▸ ha ▸ redSub_bound hsub hbd hi hil,
      har_len ▸ hb ▸ redSub_bound hsub hbd hj hjl, hm', fun res => hk res⟩)

local macro "sortReds_cmp_swap" n:ident "," hRL:term "," hbd:term "," har_len:term ","
    hJ_out:term "," hJin:term "," rt_var:ident "," m_s:ident "," rr_s:ident "," hm_s:ident ","
    hsub_s:ident "," ch_bv:term "," hch_lt:term : tactic =>
  `(tactic| (
    refine sortReds_call_rl (n := ($n).toNat) $hRL (i := ($rt_var).toNat) (j := ($ch_bv).toNat)
      (by omega) (by omega) (by omega) (by omega) $hsub_s $hbd $har_len rfl rfl $hm_s
      fun res_cmp => ?_
    cases res_cmp
    · pr_steps!
      exact $hJ_out $m_s ⟨_, $hsub_s, $hm_s⟩
    · have hch_rr : ($ch_bv).toNat <
          (($rr_s).set ($rt_var).toNat ($rr_s)[($ch_bv).toNat]).length := by
        rw [List.length_set]; omega
      have hrt_rr : ($rt_var).toNat < ($rr_s).length := by omega
      pr_steps!
      refine $hJin ($ch_bv, ()) _ (by dsimp only; omega)
        ⟨_, $hch_lt, redSub_swap (i := ($rt_var).toNat) (j := ($ch_bv).toNat)
          $hsub_s (by omega) (by omega) (by omega) (by omega),
          by assumption⟩))

local macro "sortReds_sift_body" c:ident "," s:ident "," R:ident "," n:ident ","
    bnd:term "," hRL:term "," hbd:term "," har_len:term "," hrr0:term "," hJ_out:term ","
    J_in:ident "," hJin:ident "," rt:ident "," m_s:ident "," rr_s:ident "," hm_s:ident ","
    hsub_s:ident "," init_rt:term "," hinit:term "," rr_init:term "," hsub_init:term ","
    hm_init:term : tactic =>
  `(tactic| (
    refine wp_loop_inv (ts := [i64])
      (fun v m' => ∃ rr_s : List (BitVec 32),
        v.1.toNat < ($bnd : BitVec 64).toNat ∧ RedSub ($n).toNat rr_s ($s).heur.red_refs ∧
        (PlainMem $c { $s with heur := { ($s).heur with red_refs := rr_s } } ⋆ $R) m')
      (fun v _ => ($bnd : BitVec 64).toNat - v.1.toNat) ?_ ?_
    · intro $J_in hJin0; pr_steps!
      exact hJin0 ($init_rt, ()) _ ⟨$rr_init, $hinit, $hsub_init, $hm_init⟩
    · rintro $J_in ⟨$rt, ⟨⟩⟩ $m_s ⟨$rr_s, hrt, $hsub_s, $hm_s⟩ $hJin
      dsimp only at hrt $hJin
      have hrr_s : ($rr_s).length = ($c).red_cap := ($hsub_s).1.trans $hrr0
      have hch_eq := sortReds_ch_eq $rt (by omega)
      have hch1_eq := sortReds_ch1_eq $rt (by omega)
      pr_steps!
      · exact $hJ_out $m_s ⟨$rr_s, $hsub_s, $hm_s⟩
      · have hch_lt : ($rt <<< (1 : Nat) + (1 : BitVec 64)).toNat <
            ($bnd : BitVec 64).toNat := bv64_ch_lt (by omega) hch_eq (by assumption)
        have hch1_lt : (($rt <<< (1 : Nat) + (1 : BitVec 64)) + (1 : BitVec 64)).toNat <
            ($bnd : BitVec 64).toNat := bv64_ch1_lt (by omega) hch1_eq (by assumption)
        refine sortReds_call_rl (n := ($n).toNat) $hRL
          (i := (($rt <<< (1 : Nat) + (1 : BitVec 64)) + (1 : BitVec 64)).toNat)
          (j := ($rt <<< (1 : Nat) + (1 : BitVec 64)).toNat)
          (by omega) (by omega) (by omega) (by omega) $hsub_s $hbd $har_len rfl rfl $hm_s
          fun res => ?_
        cases res
        · pr_steps!
          sortReds_cmp_swap $n, $hRL, $hbd, $har_len, $hJ_out, $hJin, $rt, $m_s, $rr_s, $hm_s,
            $hsub_s, (($rt <<< (1 : Nat) + (1 : BitVec 64)) + (1 : BitVec 64)), hch1_lt
        · pr_steps!
          sortReds_cmp_swap $n, $hRL, $hbd, $har_len, $hJ_out, $hJin, $rt, $m_s, $rr_s, $hm_s,
            $hsub_s, ($rt <<< (1 : Nat) + (1 : BitVec 64)), hch_lt
      · have hch_lt : ($rt <<< (1 : Nat) + (1 : BitVec 64)).toNat <
            ($bnd : BitVec 64).toNat := bv64_ch_lt (by omega) hch_eq (by assumption)
        sortReds_cmp_swap $n, $hRL, $hbd, $har_len, $hJ_out, $hJin, $rt, $m_s, $rr_s, $hm_s,
          $hsub_s, ($rt <<< (1 : Nat) + (1 : BitVec 64)), hch_lt))

theorem plain_sort_reds_wp (Γ : Env)
    (hRL : ∀ args m Q X, plainRedLessSpec args m Q X →
      Γ "plain_red_less" [i64, i32, i32] [.bool] args m Q X) :
    ∀ args m Q X, plainSortRedsSpec args m Q X →
      Func.wp Γ plain_sort_reds_body args m Q X := by
  rintro ⟨h, n, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hn, hbd, hm, hQ⟩
  have hrr0 : s.heur.red_refs.length = c.red_cap := hlen.heur_ok.red_refs_len
  have har_len : s.arena.length = c.arena_cap := hlen.arena_len_arr
  have hmv := c.hmv; have har := c.harena; have hred := c.hred
  unfold dimacsBound at hmv har hred
  pr_steps!
  · exact hQ s.heur m hlen.heur_ok rfl (fun k hk => ⟨k, hk, rfl⟩) hm
  have hn1 : 1 < n.toNat := by clear hQ hm; bv_omega
  refine wp_loop_inv (ts := [i64])
    (fun v m1 => ∃ rr : List (BitVec 32),
      v.1.toNat ≤ n.toNat / 2 ∧ RedSub n.toNat rr s.heur.red_refs ∧
      (PlainMem c { s with heur := { s.heur with red_refs := rr } } ⋆ R) m1)
    (fun v _ => v.1.toNat) ?_ ?_
  · intro J1 hJ1; pr_steps!
    exact hJ1 _ m ⟨s.heur.red_refs, by rw [PlainReduceTactics.bv_c0_shr1n_64]; exact Nat.le_refl _,
      redSub_refl n.toNat s.heur.red_refs, hm⟩
  · rintro J1 ⟨st, ⟨⟩⟩ m1 ⟨rr, hst, hsub, hm1⟩ hJ1
    dsimp only at hst hJ1
    pr_steps!
    · have hst_pos : 0 < st.toNat := bv64_gt0_of_lt (by assumption)
      have hst_sub := bv64_sub1_eq hst_pos
      have hst_lt_n : (st - 1).toNat < n.toNat := by omega
      have hJ1_out : ∀ m' : Mem 64, (∃ rr', RedSub n.toNat rr' s.heur.red_refs ∧
          (PlainMem c { s with heur := { s.heur with red_refs := rr' } } ⋆ R) m') →
          J1 (st - 1, ()) m' := fun m' ⟨rr', hsub', hm'⟩ =>
        hJ1 (st - 1, ()) m' (by dsimp only; omega)
          ⟨rr', by dsimp only; omega, hsub', hm'⟩
      clear_except [Γ hRL n c s R hn hbd hrr0 har_len hred st m1 rr hsub hm1 hJ1_out hst_lt_n
        J hJ]
      sortReds_sift_body c, s, R, n, n, hRL, hbd, har_len, hrr0, hJ1_out,
        J1a, hJ1a, rt1, ms1, rr1, hms1, hsub1, st - 1, hst_lt_n, rr, hsub, hm1
    · refine wp_loop_inv (ts := [i64])
        (fun v m2 => ∃ rr2 : List (BitVec 32),
          v.1.toNat < n.toNat ∧ RedSub n.toNat rr2 s.heur.red_refs ∧
          (PlainMem c { s with heur := { s.heur with red_refs := rr2 } } ⋆ R) m2)
        (fun v _ => v.1.toNat) ?_ ?_
      · intro J2 hJ2; pr_steps!
        exact hJ2 _ m1 ⟨rr, by dsimp only; rw [bv64_sub1_eq (by omega)]; omega, hsub, hm1⟩
      · rintro J2 ⟨ed, ⟨⟩⟩ m2 ⟨rr2, hed, hsub2, hm2⟩ hJ2
        clear hc
        clear J1 st m1 rr hst hsub hm1 hJ1
        dsimp only at hed hJ2
        have hrr2 : rr2.length = c.red_cap := hsub2.1.trans hrr0
        have hrr2_pos : 0 < rr2.length := by omega
        pr_steps!
        · have hed_pos : 0 < ed.toNat := bv64_gt0_of_lt (by assumption)
          have hed_sub := bv64_sub1_eq hed_pos
          have hJ2_out : ∀ m' : Mem 64, (∃ rr', RedSub n.toNat rr' s.heur.red_refs ∧
              (PlainMem c { s with heur := { s.heur with red_refs := rr' } } ⋆ R) m') →
              J2 (ed - 1, ()) m' := fun m' ⟨rr', hsub', hm'⟩ =>
            hJ2 (ed - 1, ()) m' (by dsimp only; omega)
              ⟨rr', by dsimp only; omega, hsub', hm'⟩
          refine (fun (h_wp : ∀ (m_sw : Mem 64) (rr2_sw : List (BitVec 32)),
              RedSub n.toNat rr2_sw s.heur.red_refs →
              (PlainMem c { s with heur := { s.heur with red_refs := rr2_sw } } ⋆ R) m_sw →
              wp Γ Q X _ m_sw) =>
            h_wp _ _ (redSub_swap hsub2 (by omega) hed hrr2_pos (by omega)) (by assumption)) ?_
          intro m_sw rr2_sw hsub_sw hm2_sw
          clear_except [Γ hRL n c s R hlen hn hbd hrr0 har_len hred J2 ed hed hJ2_out
            m_sw rr2_sw hsub_sw hm2_sw hed_pos J hJ]
          sortReds_sift_body c, s, R, n, ed, hRL, hbd, har_len, hrr0, hJ2_out,
            J2a, hJ2a, rt2, ms2, rr2i, hms2, hsub2i, 0#64, hed_pos, rr2_sw, hsub_sw, hm2_sw
        · exact hQ _ m2 (hlen.heur_ok.with_red_refs hrr2) rfl hsub2.2 hm2

/-! ## 5. Shared `BitVec` / `BinWatchesOnly` / `GarbMaskOk` helpers (exported for Part 2) -/

namespace PlainReduceHelpers

theorem bv8_slt_zero_iff {x : BitVec 8} (hx : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8) :
    x.slt 0#8 = true ↔ x = 0xFF#8 := by rcases hx with rfl | rfl | rfl <;> decide
theorem bv8_zero_slt_iff {x : BitVec 8} (hx : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8) :
    (0#8).slt x = true ↔ x = 1#8 := by rcases hx with rfl | rfl | rfl <;> decide
theorem bv8_sext32_slt_zero_iff {x : BitVec 8} (hx : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8) :
    (x.signExtend 32).slt 0#32 = true ↔ x = 0xFF#8 := by rcases hx with rfl | rfl | rfl <;> decide
theorem bv8_zero_slt_sext32_iff {x : BitVec 8} (hx : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8) :
    (0#32).slt (x.signExtend 32) = true ↔ x = 1#8 := by rcases hx with rfl | rfl | rfl <;> decide

theorem bv32_shrk_rsn_clear_props (h : BitVec 32) :
    let h' := h &&& ~~~0x00A00000#32
    (h' &&& 0x00800000#32) = 0#32 ∧ (h' &&& 0x00200000#32) = 0#32 ∧
    (h' &&& 0x00080000#32) = (h &&& 0x00080000#32) := by
  have h1 : (~~~(0x00A00000#32 : BitVec 32) &&& 0x00800000#32) = 0#32 := by decide
  have h2 : (~~~(0x00A00000#32 : BitVec 32) &&& 0x00200000#32) = 0#32 := by decide
  have h3 : (~~~(0x00A00000#32 : BitVec 32) &&& 0x00080000#32) = 0x00080000#32 := by decide
  exact ⟨by rw [BitVec.and_assoc, h1, BitVec.and_zero],
    by rw [BitVec.and_assoc, h2, BitVec.and_zero], by rw [BitVec.and_assoc, h3]⟩
theorem bv32_or_garb_props (h : BitVec 32) :
    ((h ||| 0x00080000#32) &&& 0xFFF7FFFF#32) = (h &&& 0xFFF7FFFF#32) ∧
    ((h ||| 0x00080000#32) &&& 0x00080000#32) ≠ 0#32 := by
  constructor
  · have hm : ((0x00080000#32 : BitVec 32) &&& 0xFFF7FFFF#32) = 0#32 := by decide
    rw [BitVec.and_or_distrib_right, hm, BitVec.or_zero]
  · intro heq; have hb := congrArg (fun z : BitVec 32 => z[19]) heq
    simp [show (0x00080000#32 : BitVec 32)[19] = true from rfl] at hb
theorem bv32_lit_bin_flag {lit : BitVec 32} (hlt : lit.toNat < 0x7FFFFFFF) :
    let b := (lit &&& 0x7FFFFFFF#32) ||| 0x80000000#32
    (lit &&& 0x7FFFFFFF#32) = lit ∧ (b &&& 0x80000000#32) ≠ 0#32 ∧
    (b &&& 0x7FFFFFFF#32) = lit ∧ b ≠ 0xFFFFFFFF#32 := by
  have hm : (lit &&& 0x7FFFFFFF#32) = lit := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (0x7FFFFFFF#32 : BitVec 32).toNat = 2 ^ 31 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod]; exact Nat.mod_eq_of_lt (by omega)
  have hor_msb : ((lit ||| 0x80000000#32) &&& 0x80000000#32) ≠ 0#32 := fun h => by
    have hb := congrArg BitVec.msb h
    simp [BitVec.msb_and, BitVec.msb_or, show (0x80000000#32 : BitVec 32).msb = true from rfl] at hb
  have hor_low : ((lit ||| 0x80000000#32) &&& 0x7FFFFFFF#32) = lit := by
    have hz : ((0x80000000#32 : BitVec 32) &&& 0x7FFFFFFF#32) = 0#32 := by decide
    rw [BitVec.and_or_distrib_right, hm, hz, BitVec.or_zero]
  have hne : (lit ||| 0x80000000#32) ≠ 0xFFFFFFFF#32 := fun heq => by
    have hcon := congrArg (fun z => (z &&& 0x7FFFFFFF#32).toNat) heq
    rw [hor_low, show (0xFFFFFFFF#32 &&& 0x7FFFFFFF#32 : BitVec 32).toNat = 0x7FFFFFFF
      from by decide] at hcon; omega
  refine ⟨hm, ?_, ?_, ?_⟩ <;> simpa [hm]

@[expose] def BinWatchesOnly (c : PlainCfg) (F0 : CNF Nat) (s : PlainState) (n : Nat) : Prop :=
  WatchesInv c F0 s ∧ ∀ l < n, l < 2 * c.mv → ∀ k < watchSize s l,
    ∃ w, s.wstk[watchOff s l + k]? = some w ∧ BinWatchOk c F0 l w

theorem binWatchesOnly_of_all_bin {c : PlainCfg} {F0 : CNF Nat}
    {s : PlainState} (hlay : WatchStackLayout c s)
    (hbin : ∀ l < 2 * c.mv, ∀ k < watchSize s l,
      ∃ w, s.wstk[watchOff s l + k]? = some w ∧ BinWatchOk c F0 l w) :
    BinWatchesOnly c F0 s (2 * c.mv) :=
  ⟨WatchesInv.of_slices hlay.bounds hlay.pos_off hlay.disjoint
      fun l hl => watchSliceOk_of_bin (watchSize s l) (watchOff s l) (hbin l hl),
    fun l _ hl => hbin l hl⟩

theorem binWatchesOnly_defrag {c : PlainCfg} {F0 : CNF Nat} {s s' : PlainState}
    (hb : BinWatchesOnly c F0 s (2 * c.mv)) (hlay : WatchStackLayout c s')
    (hare : s'.arena = s.arena) (hal : s'.arena_len = s.arena_len)
    (hpres : ∀ l < 2 * c.mv, watchSize s' l = watchSize s l ∧
      ∀ k < watchSize s l, s'.wstk[watchOff s' l + k]? = s.wstk[watchOff s l + k]?) :
    BinWatchesOnly c F0 s' (2 * c.mv) := by
  have hrefs := arenaClauseRefs_congr hal fun r _ => by rw [hare]
  refine ⟨WatchesInv.of_slices hlay.bounds hlay.pos_off hlay.disjoint fun l hl => ?_,
      fun l _ hl k hk => ?_⟩
  · obtain ⟨hsz, hslice⟩ := hpres l hl; rw [hsz]
    exact (hb.1.slices l hl).relocate (by rw [CNF.entails_def]; exact fun _ h => h)
      (fun _ hr => hrefs ▸ hr) hslice
  · obtain ⟨hsz, hslice⟩ := hpres l hl; rw [hsz] at hk
    obtain ⟨w, hw, hok⟩ := hb.2 l hl hl k hk; exact ⟨w, (hslice k hk).trans hw, hok⟩

theorem binWatchesOnly_with_arena {c : PlainCfg} {F0 : CNF Nat}
    {s : PlainState} (hb : BinWatchesOnly c F0 s (2 * c.mv)) (arena' : List (BitVec 32))
    (alen' : Nat) :
    BinWatchesOnly c F0 { s with arena := arena', arena_len := alen' } (2 * c.mv) :=
  ⟨WatchesInv.of_slices hb.1.layout.bounds hb.1.layout.pos_off hb.1.layout.disjoint
      (fun l hl => watchSliceOk_of_bin (watchSize s l) (watchOff s l) (hb.2 l hl hl)),
    fun l _ hl => hb.2 l hl hl⟩

theorem binWatchesOnly_assign {c : PlainCfg} {F0 : CNF Nat} {s s' : PlainState}
    (hb : BinWatchesOnly c F0 s (2 * c.mv)) (hw : WatchesInv c F0 s')
    (hv : s'.wvec = s.wvec) (hs : s'.wstk = s.wstk) :
    BinWatchesOnly c F0 s' (2 * c.mv) := ⟨hw, fun l hn hl k hk => by
  unfold watchSize at hk; unfold watchOff; rw [hv] at hk ⊢; rw [hs]; exact hb.2 l hn hl k hk⟩

theorem binWatchesOnly_push {c : PlainCfg} {F0 : CNF Nat} {s s' : PlainState} {lit w0 : BitVec 32}
    (hb : BinWatchesOnly c F0 s (2 * c.mv)) (hlay : WatchStackLayout c s')
    (hsub : ∀ r ∈ arenaClauseRefs s, r ∈ arenaClauseRefs s') (hbin : BinWatchOk c F0 lit.toNat w0)
    (hother : ∀ l < 2 * c.mv, l ≠ lit.toNat → watchSize s' l = watchSize s l ∧
      ∀ k < watchSize s l, s'.wstk[watchOff s' l + k]? = s.wstk[watchOff s l + k]?)
    (hsz : watchSize s' lit.toNat = watchSize s lit.toNat + 1)
    (hpre : ∀ k < watchSize s lit.toNat,
      s'.wstk[watchOff s' lit.toNat + k]? = s.wstk[watchOff s lit.toNat + k]?)
    (hw0 : s'.wstk[watchOff s' lit.toNat + watchSize s lit.toNat]? = some w0) :
    BinWatchesOnly c F0 s' (2 * c.mv) := by
  have hwat : WatchesInv c F0 s' := ⟨hlay, fun l hl => by
    by_cases hle : l = lit.toNat
    · subst hle; rw [hsz]
      exact (hb.1.slices _ hl).append_bin hsub hpre hw0 hbin.1 hbin.2.1 hbin.2.2
    · obtain ⟨hszl, hsl⟩ := hother l hl hle; rw [hszl]
      exact WatchSliceOk.relocate (s := s) (s' := s') (p := watchOff s l) (p' := watchOff s' l)
        (by rw [CNF.entails_def]; exact fun _ h => h) hsub hsl (hb.1.slices l hl)⟩
  refine ⟨hwat, fun l _ hl k hk => ?_⟩
  by_cases hle : l = lit.toNat
  · subst hle; rw [hsz] at hk
    by_cases hkl : k < watchSize s lit.toNat
    · obtain ⟨w, hw, hok⟩ := hb.2 _ hl hl k hkl; exact ⟨w, (hpre k hkl).trans hw, hok⟩
    · have hk_eq : k = watchSize s lit.toNat := by omega
      subst hk_eq; exact ⟨w0, hw0, hbin⟩
  · obtain ⟨hszl, hsl⟩ := hother l hl hle; rw [hszl] at hk
    obtain ⟨w, hw, hok⟩ := hb.2 l hl hl k hk; exact ⟨w, (hsl k hk).trans hw, hok⟩

theorem watchSliceOk_step {c : PlainCfg} {F0 : CNF Nat} {s : PlainState}
    {l p end_ : Nat} {w0 : BitVec 32} (hws : WatchSliceOk c F0 s l p (end_ - p))
    (hp : p < end_) (hw0 : s.wstk[p]? = some w0) :
    ((w0 &&& 0x80000000#32) ≠ 0#32 →
      BinWatchOk c F0 l w0 ∧ 1 ≤ end_ - p ∧ WatchSliceOk c F0 s l (p + 1) (end_ - (p + 1))) ∧
    ((w0 &&& 0x80000000#32) = 0#32 →
      2 ≤ end_ - p ∧ WatchSliceOk c F0 s l (p + 2) (end_ - (p + 2))) := by
  generalize hrem : end_ - p = n at hws
  cases hws with
  | empty => omega
  | @bin _ rem w hw hf hl he hrest =>
    simp only [hw0, Option.some.injEq] at hw; subst w
    exact ⟨fun _ => ⟨⟨hf, hl, he⟩, by omega, by rwa [show end_ - (p + 1) = rem from by omega]⟩,
      fun h => absurd h hf⟩
  | @large _ rem w cref hw _ hf _ _ hrest =>
    simp only [hw0, Option.some.injEq] at hw; subst w
    exact ⟨fun h => absurd hf h,
      fun _ => ⟨by omega, by rwa [show end_ - (p + 2) = rem from by omega]⟩⟩

theorem sweep_finish_slice {c : PlainCfg} {F0 : CNF Nat} {s : PlainState} {l new_sz : Nat}
    {wstk' : List (BitVec 32)} {wusable' num_binary' : BitVec 64}
    (hlen : s.LengthsOk c) (hb : BinWatchesOnly c F0 s l) (hl : l < 2 * c.mv)
    (hws_len : wstk'.length = c.wcap) (hsz_le : new_sz ≤ watchSize s l)
    (hws_out : ∀ m, m < watchOff s l ∨ watchOff s l + watchSize s l ≤ m → wstk'[m]? = s.wstk[m]?)
    (hws_in : ∀ k < new_sz, ∃ w, wstk'[watchOff s l + k]? = some w ∧ BinWatchOk c F0 l w) :
    let s' : PlainState :=
      { s with wstk := wstk', wvec := s.wvec.set (2 * l + 1) (BitVec.ofNat 32 new_sz),
               wusable := wusable', num_binary := num_binary' }
    s'.LengthsOk c ∧ BinWatchesOnly c F0 s' (l + 1) := by
  intro s'; have hlay := hb.1.layout; have hcw := c.hwcap; unfold dimacsBound at hcw
  have hbdd := hlay.bounds l hl; have hwlen_le := hlen.wlen_le
  have hwoff : ∀ l' < 2 * c.mv, watchOff s' l' = watchOff s l' := fun l' _ => by
    unfold watchOff s'; rw [List.getElem?_set_ne (by omega)]
  have hwsz_ne : ∀ l' < 2 * c.mv, l' ≠ l → watchSize s' l' = watchSize s l' := fun l' _ hne => by
    unfold watchSize s'; rw [List.getElem?_set_ne (by omega)]
  have hwsz_eq : watchSize s' l = new_sz := by
    unfold watchSize s'
    rw [List.getElem?_set_self (by rw [hlen.wvec_len]; omega), Option.getD_some,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hother : ∀ l' < 2 * c.mv, l' ≠ l →
      ∀ k < watchSize s l', s'.wstk[watchOff s l' + k]? = s.wstk[watchOff s l' + k]? := by
    intro l' hl' hne k hk
    by_cases hsz0 : watchSize s l = 0
    · exact hws_out _ (by omega)
    · rcases hlay.disjoint l l' hl hl' (Ne.symm hne) (by omega) (by omega) with h | h <;>
        exact hws_out _ (by omega)
  have hdisj' : ∀ l1 l2, l1 < 2 * c.mv → l2 < 2 * c.mv → l1 ≠ l2 → 0 < watchSize s' l1 →
      0 < watchSize s' l2 → watchOff s' l1 + watchSize s' l1 ≤ watchOff s' l2 ∨
        watchOff s' l2 + watchSize s' l2 ≤ watchOff s' l1 := by
    intro l1 l2 h1 h2 hne hp1 hp2; rw [hwoff l1 h1, hwoff l2 h2]
    by_cases he1 : l1 = l
    · rw [he1] at hp1 ⊢; rw [hwsz_eq] at hp1 ⊢; rw [hwsz_ne l2 h2 (by omega)] at hp2 ⊢
      rcases hlay.disjoint l l2 hl h2 (by omega) (by omega) hp2 with hd | hd
      · exact Or.inl (by omega)
      · exact Or.inr hd
    · by_cases he2 : l2 = l
      · rw [he2] at hp2 ⊢; rw [hwsz_eq] at hp2 ⊢; rw [hwsz_ne l1 h1 he1] at hp1 ⊢
        rcases hlay.disjoint l1 l h1 hl (by omega) hp1 (by omega) with hd | hd
        · exact Or.inl hd
        · exact Or.inr (by omega)
      · rw [hwsz_ne l1 h1 he1] at hp1 ⊢; rw [hwsz_ne l2 h2 he2] at hp2 ⊢
        exact hlay.disjoint l1 l2 h1 h2 hne hp1 hp2
  have hwat' : WatchesInv c F0 s' := WatchesInv.of_slices
    (fun l' hl' => by
      rw [hwoff l' hl']; by_cases hle : l' = l
      · rw [hle, hwsz_eq]; exact Nat.le_trans (Nat.add_le_add_left hsz_le _) hbdd
      · rw [hwsz_ne l' hl' hle]; exact hlay.bounds l' hl')
    (fun l' hl' hpos => by
      rw [hwoff l' hl']; by_cases hle : l' = l
      · rw [hle, hwsz_eq] at hpos; rw [hle]; exact hlay.pos_off l hl (by omega)
      · rw [hwsz_ne l' hl' hle] at hpos; exact hlay.pos_off l' hl' hpos)
    hdisj'
    (fun l' hl' => by
      rw [hwoff l' hl']; by_cases hle : l' = l
      · rw [hle, hwsz_eq]; exact watchSliceOk_of_bin new_sz (watchOff s l) hws_in
      · rw [hwsz_ne l' hl' hle]
        exact WatchSliceOk.relocate (s := s) (s' := s') (p := watchOff s l')
          (p' := watchOff s l') (by rw [CNF.entails_def]; exact fun _ h => h)
          (fun _ hr => hr) (hother l' hl' hle) (hb.1.slices l' hl'))
  refine ⟨{ hlen with wvec_len := by simp [s', hlen.wvec_len], wstk_len_arr := hws_len },
    hwat', fun l' hl' hl'_mv k hk => ?_⟩
  rw [hwoff l' hl'_mv]; by_cases hle : l' = l
  · rw [hle, hwsz_eq] at hk; rw [hle]; exact hws_in k hk
  · rw [hwsz_ne l' hl'_mv hle] at hk
    obtain ⟨w, hw, hok⟩ := hb.2 l' (by omega) hl'_mv k hk
    exact ⟨w, (hother l' hl'_mv hle k hk).trans hw, hok⟩

theorem sweep_fill_sentinels {ws0 ws1 ws : List (BitVec 32)} {off end_ q k : Nat}
    (hko : off ≤ k) (hkq : q ≤ k) (hk_end : k < end_) (hlen : ws.length = ws0.length)
    (hout : ∀ m, m < off ∨ end_ ≤ m → ws[m]? = ws0[m]?)
    (hpre : ∀ m, off ≤ m → m < q → ws[m]? = ws1[m]?) :
    (ws.set k 0xFFFFFFFF#32).length = ws0.length ∧
    (∀ m, m < off ∨ end_ ≤ m → (ws.set k 0xFFFFFFFF#32)[m]? = ws0[m]?) ∧
    (∀ m, off ≤ m → m < q → (ws.set k 0xFFFFFFFF#32)[m]? = ws1[m]?) :=
  ⟨by simp [hlen],
   (fun m hm => by
     by_cases hkm : k = m
     · subst k; rcases hm with hm | hm <;> omega
     · rw [List.getElem?_set_ne hkm]; exact hout m hm),
   (fun m hm1 hm2 => by rw [List.getElem?_set_ne (by omega)]; exact hpre m hm1 hm2)⟩

theorem sweep_prune_push {ws0 ws : List (BitVec 32)} {off q p end_ : Nat} {w0 : BitVec 32}
    (hoff_q : off ≤ q) (hq_p : q ≤ p) (hp_end : p < end_) (hws_len : ws.length = ws0.length)
    (hq_lt : q < ws.length) (hout : ∀ m, m < off ∨ end_ ≤ m → ws[m]? = ws0[m]?)
    (hsuf : ∀ m, p ≤ m → m < end_ → ws[m]? = ws0[m]?) :
    (ws.set q w0).length = ws0.length ∧
    (∀ m, m < off ∨ end_ ≤ m → (ws.set q w0)[m]? = ws0[m]?) ∧
    (∀ m, p + 1 ≤ m → m < end_ → (ws.set q w0)[m]? = ws0[m]?) ∧
    (∀ k < (q + 1) - off, k < q - off → (ws.set q w0)[off + k]? = ws[off + k]?) ∧
    (ws.set q w0)[off + (q - off)]? = some w0 :=
  ⟨by simp [hws_len],
   (fun m hm => by rw [List.getElem?_set_ne (by omega)]; exact hout m hm),
   (fun m hm1 hm2 => by rw [List.getElem?_set_ne (by omega)]; exact hsuf m (by omega) hm2),
   (fun k _ hkl => by rw [List.getElem?_set_ne (by omega)]),
   by rw [show off + (q - off) = q by omega, List.getElem?_set_self hq_lt]⟩

@[expose] def GarbMaskOk (s0 : PlainState) (arena' : List (BitVec 32)) : Prop :=
  arena'.length = s0.arena.length ∧
  (∀ k, k ∉ arenaClauseRefs s0 → arena'[k]? = s0.arena[k]?) ∧
  (∀ r ∈ arenaClauseRefs s0,
    (arena'[r]?.getD 0#32 &&& 0xFFF7FFFF#32) = (s0.arena[r]?.getD 0#32 &&& 0xFFF7FFFF#32)) ∧
  (∀ r ∈ arenaClauseRefs s0,
    (arena'[r]?.getD 0#32 &&& 0x00080000#32) = 0#32 →
    (s0.arena[r]?.getD 0#32 &&& 0x00080000#32) = 0#32) ∧
  (∀ r ∈ arenaClauseRefs s0,
    (s0.arena[r]?.getD 0#32 &&& 0x00200000#32) ≠ 0#32 → arena'[r]? = s0.arena[r]?)

theorem garbMask_refl (s0 : PlainState) : GarbMaskOk s0 s0.arena :=
  ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ h => h, fun _ _ _ => rfl⟩

theorem garbMask_set {s0 : PlainState} {arena' : List (BitVec 32)}
    (hg : GarbMaskOk s0 arena') {r : Nat} (hr : r ∈ arenaClauseRefs s0) (hlt : r < arena'.length)
    (hnrsn : (arena'[r] &&& 0x00200000#32) = 0#32) :
    GarbMaskOk s0 (arena'.set r (arena'[r] ||| 0x00080000#32)) := by
  have hm_rsn : ((0xFFF7FFFF#32 : BitVec 32) &&& 0x00200000#32) = 0x00200000#32 := by decide
  have hm_r : (s0.arena[r]?.getD 0#32 &&& 0x00200000#32) = 0#32 := by
    have h1 := congrArg (· &&& 0x00200000#32) (hg.2.2.1 r hr)
    rw [BitVec.and_assoc, hm_rsn, BitVec.and_assoc, hm_rsn, List.getElem?_eq_getElem hlt,
      Option.getD_some, hnrsn] at h1; exact h1.symm
  refine ⟨by simp [hg.1], fun k hk => ?_, fun r' hr' => ?_, fun r' hr' hz => ?_,
      fun r' hr' hp => ?_⟩
  · rw [List.getElem?_set_ne (fun h => hk (by rw [← h]; exact hr))]; exact hg.2.1 k hk
  · by_cases hrr' : r = r'
    · subst r'; rw [List.getElem?_set_self hlt, Option.getD_some, (bv32_or_garb_props _).1]
      have := hg.2.2.1 r hr; rwa [List.getElem?_eq_getElem hlt, Option.getD_some] at this
    · rw [List.getElem?_set_ne hrr']; exact hg.2.2.1 r' hr'
  · by_cases hrr' : r = r'
    · subst r'; rw [List.getElem?_set_self hlt, Option.getD_some] at hz
      exact absurd hz (bv32_or_garb_props _).2
    · rw [List.getElem?_set_ne hrr'] at hz; exact hg.2.2.2.1 r' hr' hz
  · rw [List.getElem?_set_ne (fun h => by subst h; simp [hm_r] at hp)]; exact hg.2.2.2.2 r' hr' hp

theorem garbMask_core {c : PlainCfg} {F0 : CNF Nat} {s0 : PlainState}
    (hinv : PlainCoreInv c F0 s0) (hrm : 0 < s0.cur_level → ReasonsMarked s0)
    {arena' : List (BitVec 32)} (hg : GarbMaskOk s0 arena') :
    let s' : PlainState := { s0 with arena := arena' }
    PlainCoreInv c F0 s' ∧ (0 < s'.cur_level → ReasonsMarked s') := by
  have hrs_ng : ∀ idx < s0.trail_end,
      let p := (s0.trl[idx]?.getD 0#32).toNat
      let rsn := s0.rsns[p / 2]?.getD 0xFFFFFFFF#32
      rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 →
      arenaClauseGarb { s0 with arena := arena' } rsn.toNat = false := fun idx hidx hne hmsb => by
    have hrs := hinv.reason_inv idx hidx hne
    simp only [hmsb, ne_eq, not_true_eq_false, ↓reduceIte] at hrs
    have hpos_lvl : 0 < (s0.lvl[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0#32).toNat :=
      Nat.pos_of_ne_zero fun h0 => absurd (hinv.level0_rsn_none idx hidx h0) hne
    have hmarked := hrm (Nat.lt_of_lt_of_le hpos_lvl (hinv.lvl_le idx hidx)) idx hidx hpos_lvl hmsb
    unfold arenaClauseGarb arenaHdr
    rw [hg.2.2.2.2 _ hrs.1 hmarked]; exact hrs.2.1
  obtain ⟨_, _, hcore⟩ := arenaPres_core hg.1 hg.2.1
    (fun r hr => bv32_mask_sub_eq (by decide) (hg.2.2.1 r hr))
    (fun r hr hng => by
      unfold arenaClauseGarb arenaHdr at hng ⊢; rw [bne_eq_false_iff_eq] at hng ⊢
      exact hg.2.2.2.1 r hr hng)
    hrs_ng hinv
  refine ⟨hcore, fun hpos idx hidx hlv hmsb => ?_⟩
  have hne : s0.rsns[(s0.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 :=
    fun heq => by rw [heq] at hmsb; revert hmsb; decide
  have hrs := hinv.reason_inv idx hidx hne
  simp only [hmsb, ne_eq, not_true_eq_false, ↓reduceIte] at hrs
  have hmarked := hrm hpos idx hidx hlv hmsb
  unfold arenaHdr at hmarked ⊢; rw [hg.2.2.2.2 _ hrs.1 hmarked]; exact hmarked

end PlainReduceHelpers

end

end LeanQbe.T.Examples.Kissat.Plain
