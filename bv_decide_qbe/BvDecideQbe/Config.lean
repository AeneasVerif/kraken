module

public import Std.Tactic.BVDecide.Syntax

/-!
# Lightweight Public Configuration Types for `bv_decide_qbe`

Pure `Init` + `Std.Tactic.BVDecide.Syntax` configuration types (`QbeMode`, `QbeSolverVariant`,
`QbeConfig`, `QbeFeatures`, `resolveQbeFeatures`) kept free of `Lean.*` imports so downstream
files importing `BvDecideQbe` / `BvDecideQbe.Tactic` elaborate without loading `Lean.*` `.olean`s.
-/

set_option autoImplicit false

public section

namespace BvDecideQbe

/-- Execution preset mode for `bv_decide_qbe`:
- `.upstream`: disables all enhanced divergences (`D1–D8`), keeping only the verified
  `KissatFidelity` in-process solver backend (`D0`) and exact upstream `BVDecideConfig` defaults.
- `.enhanced`: default mode enabling conservative validated enhancements (`D1`, etc.). -/
inductive QbeMode where
  | upstream
  | enhanced
  deriving Repr, BEq, DecidableEq, Inhabited

instance : ToString QbeMode where
  toString
    | .upstream => "upstream"
    | .enhanced => "enhanced"

/-- Verified SAT solver variant selector (`D10`). -/
inductive QbeSolverVariant where
  | fidelity
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Extended tactic configuration for `bv_decide_qbe`, compatible with upstream `BVDecideConfig`
and `optConfig` (`(config := { timeout := ..., acNf := ..., ... })`). -/
structure QbeConfig extends Lean.Elab.Tactic.BVDecide.BVDecideConfig where
  /-- Preset override (`none` resolves via the `bv_decide_qbe.mode` option). -/
  mode : Option QbeMode := none
  /-- `D1`: Auto-enable `acNf` when `BitVec`/fixed-int multiplication is present. -/
  autoAcNf : Option Bool := none
  /-- `D2`: Apply `BvDecideQbe.NormalizeRules` `shiftmul`/`opt_share` pre-pass. -/
  extraNormalize : Option Bool := none
  /-- `D3`: Fast 64-pattern simulation CEX pre-check. -/
  simCex : Option Bool := none
  /-- `D4`: Pure `BitVec` ring dispatch via `grind`. -/
  ringDispatch : Option Bool := none
  /-- `D5`: ARiSCA Tier-1 algebraic checker dispatch. -/
  arisca : Option Bool := none
  /-- `D5`: Short Kissat probe duration in milliseconds before ARiSCA dispatch. -/
  ariscaProbeMs : Option Nat := none
  /-- `D6`: ARiSCA Tier-2 sub-lemma dispatch. -/
  ariscaTier2 : Option Bool := none
  /-- `D7`: FRAIG equivalence hints (`BVH1`). -/
  fraigHints : Option Bool := none
  /-- `D8`: Kitten peel (`K6Mem`). -/
  kitten : Option Bool := none
  /-- `D10`: SAT solver backend variant. -/
  solverVariant : QbeSolverVariant := .fidelity

instance : Coe Lean.Elab.Tactic.BVDecide.BVDecideConfig QbeConfig where
  coe cfg := { toBVDecideConfig := cfg }

/-- Resolved feature switches after applying `QbeMode` defaults and per-feature overrides. -/
structure QbeFeatures where
  mode : QbeMode := .enhanced
  autoAcNf : Bool := true
  extraNormalize : Bool := false
  simCex : Bool := true
  ringDispatch : Bool := false
  arisca : Bool := false
  ariscaProbeMs : Nat := 500
  ariscaTier2 : Bool := false
  fraigHints : Bool := false
  kitten : Bool := false
  solverVariant : QbeSolverVariant := .fidelity
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Resolve per-feature switches from `mode` and explicit `Option` overrides in `cfg`.
In `.upstream` mode, every `D1–D8` divergence defaults to `false`. -/
def resolveQbeFeatures (mode : QbeMode) (cfg : QbeConfig) (inCut : Bool := false) :
    QbeFeatures :=
  match mode with
  | .upstream => {
      mode := .upstream
      autoAcNf := cfg.autoAcNf.getD false
      extraNormalize := cfg.extraNormalize.getD false
      simCex := cfg.simCex.getD false
      ringDispatch := cfg.ringDispatch.getD false
      arisca := cfg.arisca.getD false
      ariscaProbeMs := cfg.ariscaProbeMs.getD 0
      ariscaTier2 := cfg.ariscaTier2.getD false
      fraigHints := cfg.fraigHints.getD false
      kitten := cfg.kitten.getD false
      solverVariant := .fidelity
    }
  | .enhanced => {
      mode := .enhanced
      autoAcNf := cfg.autoAcNf.getD true
      extraNormalize := cfg.extraNormalize.getD inCut
      simCex := cfg.simCex.getD true
      ringDispatch := cfg.ringDispatch.getD inCut
      arisca := cfg.arisca.getD false
      ariscaProbeMs := cfg.ariscaProbeMs.getD 500
      ariscaTier2 := cfg.ariscaTier2.getD false
      fraigHints := cfg.fraigHints.getD false
      kitten := cfg.kitten.getD false
      solverVariant := cfg.solverVariant
    }

end BvDecideQbe
