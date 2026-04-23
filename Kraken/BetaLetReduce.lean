import Lean

open Lean Expr Meta Sym.Simp

/-- Checks whether `.bvar bvar` occurs at most once in `e`, disregarding sharing. -/
partial def usedLinearly (e : Expr) (bvar : Nat) : Bool :=
  (go e 0 |>.run 0 |>.2) <= 1
where go (e : Expr) (offset : Nat) : StateM Nat Unit := do
  if (← get) > 1 || offset >= e.looseBVarRange then
    return
  match e with
  | .bvar idx =>
    if idx == bvar + offset then
      modify (· + 1)
  | .fvar .. | .mvar .. | .sort .. | .const .. | .lit .. => pure ()
  | .app f a => go f offset; go a offset
  | .lam _ t b _ | .forallE _ t b _ => go t offset; go b (offset + 1)
  | .letE _ t v b _ => go t offset; go v offset; go b (offset + 1)
  | .mdata _ e' => go e' offset
  | .proj _ _ e' => go e' offset

/-- Like `betaRev` but let-binds (some) args before instantiation. -/
partial def betaLetRev (e : Expr) (revArgs : Array Expr) : Expr := Id.run do
  if revArgs.isEmpty then
    return e
  go e 0
where
  go (e : Expr) (numLams : Nat) : Expr := Id.run do
    if numLams >= revArgs.size then
      return e
    match e with
    | .lam n t b _ =>
      let arg := revArgs[revArgs.size - 1 - numLams]!
      if !arg.isAtomic then
        if !usedLinearly b 0 then
          return .letE (nondep := true) n t arg <| go b (numLams + 1)
      go (b.instantiate1 arg) (numLams + 1)
    | .mdata _ b => go b numLams
    | _ =>
      -- Body is no longer a lambda but revArgs still has entries (e.g. the RHS
      -- was eta-reduced before we got here). Apply the remaining args.
      mkAppN e ((revArgs.extract 0 (revArgs.size - numLams)).reverse)

def betaLetReduce : Simproc := fun e => do
  if !e.isApp then
    return .rfl
  let f := e.getAppFn
  if !f.isHeadBetaTargetFn (useZeta := false) then
    return .rfl
  let revArgs := e.getAppRevArgs
  let new := betaLetRev f revArgs
  if checkDependentLet new then
    dbg_trace "betaLetReduce produced dependent let (will trip Sym.simp's nondep assertion):\n  in:  {e}\n  out: {new}"
  let new ← Sym.share new
  return .step new (← Sym.mkEqRefl new)
where
  /-- True if `e` is a `letE` chain whose inner binder type references an outer let. -/
  checkDependentLet : Expr → Bool
    | .letE _ _ _ b _ => hasInnerDepLet b 0 || checkDependentLet b
    | _ => false
  hasInnerDepLet : Expr → Nat → Bool
    | .letE _ t _ b _, depth =>
        t.hasLooseBVar depth || hasInnerDepLet b (depth + 1)
    | _, _ => false

syntax (name := symBetaLetReduce) "beta_let_reduce" : sym_simproc
@[sym_simproc symBetaLetReduce]
def evalBetaLetReduce : Elab.Tactic.Grind.SymSimprocElab := fun _ =>
  return betaLetReduce

register_sym_simp betaLetReduce where
  pre  := beta_let_reduce
  post := beta_let_reduce
