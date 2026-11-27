module

import Kraken.Tactics
meta import Kraken.Tactics

open Lean Meta Elab

/--
info: let a := 1;
have b := 2;
let y := 10;
(a + b).add
  ((fun x =>
      let z := x + 1;
      y + z)
    5)
-/
#guard_msgs in
run_elab do
  let expr ← instantiateMVars (← Term.elabTermAndSynthesize
    (← `(Nat.add
      (let a := 1; have b := 2; a + b)
      ((fun x => let y := 10; let z := x + 1; y + z) 5))) none)
  let expr' ← peelArgsLets expr fun fvars f args => do
    mkLetFVars fvars (mkAppN f args) (generalizeNondepLet := false)
  Lean.logInfo m!"{expr'}"

-- Why `kdeltaBetaOnly` peels lets before `unfoldDefinition?`:
-- Without hoisting `let x := n + n` out of the argument first, unfolding `Option.getD`
-- and reducing the resulting `match` inlines `x`, duplicating `n + n`.
/--
info: without peelArgsLets: n✝ + n✝ + (n✝ + n✝)
---
info: with    peelArgsLets: let x := n✝ + n✝;
x + x
-/
#guard_msgs in
run_elab do
  let expr ← instantiateMVars (← Term.elabTermAndSynthesize
    (← `(fun n => Option.getD (let x := n + n; some (x + x)) 0)) none)
  lambdaTelescope expr fun _ body => do
    let some u1 ← Meta.unfoldDefinition? body true | throwError "unfold failed"
    let some r1 ← Meta.reduceRecMatcher? u1 | throwError "reduce failed"
    let r2 ← peelArgsLets body fun fvars f args => do
      let some u2 ← Meta.unfoldDefinition? (mkAppN f args) true | throwError "unfold failed"
      let some r2 ← Meta.reduceRecMatcher? u2 | throwError "reduce failed"
      mkLetFVars fvars r2 (generalizeNondepLet := false)
    logInfo m!"without peelArgsLets: {r1}"
    logInfo m!"with    peelArgsLets: {r2}"
