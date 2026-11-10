module

public import LeanQbe.Main
public import LeanQbe.RegaLemmas
public import LeanQbe.OptLemmas

/-!
# Correctness of the pipeline

`compileFn_correct`: if `compileFn T f = .ok code` and the code sits in host `h`, the compiled
function meets the *source* function's `wp` as a `FnSpec`. The mid-end refines contracts
(`Func.opt_spec`), the lowering is `lowerFn_correct`, and `FnSpec` is antitone in the contract.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe

theorem compileFn_correct {T : Target} (h : T.Host) (f : Fn) (Γ : Env) (n nX : Nat)
    (code : List T.Directive) (k₀ : Nat)
    (hcomp : compileFn T.toIsa f = .ok code) (hcode : code.IsInfixAt (T.prog h) k₀)
    (hu : T.LabelsUnique h) (hwf : Func.Wf f.body) (hn : n + T.raBytes ≤ 2 ^ 64) :
    T.FnSpec h f.name (Func.spec Γ f.body) n nX :=
  Target.FnSpec.of_spec T (Rega.lowerFn_correct h _ f.opt Γ n code k₀ hcomp hcode hu
    (Func.opt_wf hwf) hn nX) fun _ _ _ _ hs => Func.opt_spec hwf hs

end LeanQbe
