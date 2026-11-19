module

public import LeanQbe.T.Flat
public import LeanQbe.T.Fold
public import LeanQbe.T.Canon
public import LeanQbe.T.Copy
public import LeanQbe.T.Gvn
public import LeanQbe.T.Dce
public import LeanQbe.T.DivConst
public import LeanQbe.T.MemLoad
public import LeanQbe.T.Peel
public import LeanQbe.T.IfOpt
public import LeanQbe.T.SimplifyGroup
public import LeanQbe.T.Inline
public import LeanQbe.T.Module

/-!
# The Staged Typed-IR Mid-End Pipeline (`T6`, `O-M1`, `O-M2`)

* `Func.opt`: legacy `T6` mid-end (`fold → copy → gvn → copy → fold → dce`).
* `Func.earlyOpt`: pre-`Legal` pipeline (`renorm → fold → canon → copy → gvn → copy → fold →
  renorm → simplifyGroup → peel → dce → renorm`), simplifying source and inlined bodies and peeling
  bounded loops while preserving `C4`–`C9` widening arithmetic (`addc`/`subb`/`mulx` chains).
* `Func.lateOpt`: post-`Legal` pipeline (`renorm → fold → canon → divConst → copy → memLoad →
  gvn → renorm → simplifyGroup → ifOptBits → simplifyGroup → deadLoadElim → assumeElim → dce →
  renorm`), running target-safe scalar division reduction, memory load forwarding, machine-width
  if-conversion, and cleanup on legalized IR.
* `Fn.renorm` / `Module.optInline`: acyclic small-callee inlining followed by AST renormalization.

Correctness (`LeanQbe/T/OptLemmas.lean`): `Func.opt_wf`, `Func.opt_spec`, `Func.earlyOpt_wf`,
`Func.earlyOpt_spec`, `Func.lateOpt_wf`, `Func.lateOpt_spec`, `Module.optInline_ok`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-- Run the legacy `T6` mid-end optimization pipeline on a closed typed function. -/
def Func.opt {as rs : List Ty} (f : Func as rs) : Func as rs :=
  Func.dce (Func.fold (Func.copy (Func.gvn (Func.copy (Func.fold f)))))

mutual
/-- Count jumps targeting de Bruijn label index `d` inside a `TFlat` AST. -/
def tflatJumps {rs : List Ty} (d : Nat) : TFlat rs → Nat
  | .let_ _ k | .load _ _ k | .store _ _ k | .call _ _ _ k => tflatJumps d k
  | .jnz _ t e => tflatJumps d t + tflatJumps d e
  | .jump j _ => if j == d then 1 else 0
  | .ret _ | .exit _ _ | .hlt => 0
  | .group (sig := sig) bodies k =>
    tblocksJumps (d + sig.length) bodies + tflatJumps (d + sig.length) k

/-- Block-list companion of `tflatJumps`. -/
def tblocksJumps {rs : List Ty} (d : Nat) : {sig : List (List Ty)} → TBlocks rs sig → Nat
  | _, .nil => 0
  | _, .cons b bs => tflatJumps d b + tblocksJumps d bs
end

mutual
/-- Node count of a `TFlat` AST (linear `O(N)` proxy for `exprSizeJ`). -/
def tflatSize {rs : List Ty} : TFlat rs → Nat
  | .let_ _ k | .load _ _ k | .store _ _ k | .call _ _ _ k => 1 + tflatSize k
  | .jnz _ t e => 1 + tflatSize t + tflatSize e
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => 1
  | .group bodies k => 1 + tblocksSize bodies + tflatSize k

/-- Block-list companion of `tflatSize`. -/
def tblocksSize {rs : List Ty} : {sig : List (List Ty)} → TBlocks rs sig → Nat
  | _, .nil => 0
  | _, .cons b bs => tflatSize b + tblocksSize bs
end

mutual
/-- Count self-jumping single-block loops inside a `TFlat` AST. -/
def tflatLoops {rs : List Ty} : TFlat rs → Nat
  | .let_ _ k | .load _ _ k | .store _ _ k | .call _ _ _ k => tflatLoops k
  | .jnz _ t e => tflatLoops t + tflatLoops e
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => 0
  | .group (sig := [_]) (.cons b .nil) k =>
    (if tflatJumps 0 b > 0 then 1 else 0) + tflatLoops b + tflatLoops k
  | .group (sig := _) bodies k => tblocksLoops bodies + tflatLoops k

/-- Block-list companion of `tflatLoops`. -/
def tblocksLoops {rs : List Ty} : {sig : List (List Ty)} → TBlocks rs sig → Nat
  | _, .nil => 0
  | _, .cons b bs => tflatLoops b + tblocksLoops bs
end

mutual
/-- True iff `tf` contains an eliminable single-block acyclic join group (avoiding `O(3^d)`
`SimplifyGroup` re-traversal on deeply nested `while` loops that have nothing to simplify). -/
def hasSimpGroup (allowSmall : Bool) {rs : List Ty} : TFlat rs → Bool
  | .let_ _ k | .load _ _ k | .store _ _ k | .call _ _ _ k => hasSimpGroup allowSmall k
  | .jnz _ t e => hasSimpGroup allowSmall t || hasSimpGroup allowSmall e
  | .jump _ _ | .ret _ | .exit _ _ | .hlt => false
  | .group (sig := [_]) (.cons b .nil) k =>
    let tailJump := match k with | .jump 0 _ => true | _ => false
    let acyc := tflatJumps 0 b == 0
    let jc := tflatJumps 0 k
    (acyc && (jc == 0 || tailJump || (allowSmall && jc == 1 && tflatSize b ≤ 16))) ||
      hasSimpGroup allowSmall b || hasSimpGroup allowSmall k
  | .group (sig := _) bodies k => hasSimpGroupB allowSmall bodies || hasSimpGroup allowSmall k

/-- Block-list companion of `hasSimpGroup`. -/
def hasSimpGroupB (allowSmall : Bool) {rs : List Ty} :
    {sig : List (List Ty)} → TBlocks rs sig → Bool
  | _, .nil => false
  | _, .cons b bs => hasSimpGroup allowSmall b || hasSimpGroupB allowSmall bs
end

/-- Renormalize and run `Func.simplifyGroup` (with trailing `Func.renorm`) only when an acyclic
join candidate is present (gating single-use non-tail joins to functions with `≤ 1` loop). -/
def Func.simplifyGroupFast {as rs : List Ty} (f : Func as rs) : Func as rs :=
  let tf := reifyFunc f
  if hasSimpGroup (tflatLoops tf ≤ 1) tf then Func.renorm (Func.simplifyGroup (denoteFunc tf))
  else denoteFunc tf

/-- Renormalize and apply bounded loop peeling (`Func.peel`) only to compact single-loop
functions (`≤ 1` loop and `≤ 40` AST nodes), avoiding `O(N)` code expansion across multi-loop
parsers. -/
def Func.peelFast {as rs : List Ty} (f : Func as rs) (budget : Nat := 24) : Func as rs :=
  let tf := reifyFunc f
  if tflatLoops tf ≤ 1 && tflatSize tf ≤ 40 then Func.renorm (Func.peel (denoteFunc tf) budget)
  else denoteFunc tf

/-- Pre-`Legal` value-optimization core (`fold → canon → copy → gvn → copy → fold`). -/
def Func.earlyCore {as rs : List Ty} (f : Func as rs) : Func as rs :=
  Func.fold (Func.copy (Func.gvn (Func.copy (Func.canon (Func.fold f)))))

/-- Stage 1 (`earlyOpt`, pre-`Legal`): simplify source/inlined bodies and peel compact
single-loop functions while keeping PHOAS closures flat via `Func.renorm` for `Legal`. -/
def Func.earlyOpt {as rs : List Ty} (f : Func as rs) : Func as rs :=
  Func.renorm (Func.dce (Func.peelFast (Func.simplifyGroupFast (Func.earlyCore f)) 24))

/-- Post-`Legal` value/memory optimization core (`fold → canon → divConst → copy → renorm →
memLoad → gvn → fold`). -/
def Func.lateCore {as rs : List Ty} (f : Func as rs) : Func as rs :=
  Func.fold (Func.gvn (Func.memLoad (Func.renorm (Func.copy (Func.divConst (Func.canon
    (Func.fold f)))))))

/-- Post-`Legal` CFG/cleanup core (`renorm → ifOptBits → simplifyGroupFast → deadLoadElim →
assumeElim → renorm → dce`). -/
def Func.lateCfg {as rs : List Ty} (f : Func as rs) : Func as rs :=
  Func.dce (Func.renorm (Func.assumeElim (Func.deadLoadElim
    (Func.simplifyGroupFast (Func.ifOptBits (Func.renorm f))))))

/-- Stage 2 (`lateOpt`, post-`Legal`): strength-reduce constant division, forward memory loads,
run machine-width `.bits` if-conversion (`ifOptBits`), clean up dead loads/blocks, and renormalize
before `Rega`. -/
def Func.lateOpt {as rs : List Ty} (f : Func as rs) : Func as rs :=
  Func.renorm (Func.lateCfg (Func.lateCore f))

theorem Func.earlyCore_eq {as rs : List Ty} (f : Func as rs) :
    Func.earlyCore f =
      Func.fold (Func.copy (Func.gvn (Func.copy (Func.canon (Func.fold f))))) :=
  rfl

theorem Func.earlyOpt_eq {as rs : List Ty} (f : Func as rs) :
    Func.earlyOpt f =
      Func.renorm (Func.dce (Func.peelFast (Func.simplifyGroupFast (Func.earlyCore f)) 24)) :=
  rfl

theorem Func.lateCore_eq {as rs : List Ty} (f : Func as rs) :
    Func.lateCore f =
      Func.fold (Func.gvn (Func.memLoad (Func.renorm (Func.copy (Func.divConst (Func.canon
        (Func.fold f))))))) :=
  rfl

theorem Func.lateCfg_eq {as rs : List Ty} (f : Func as rs) :
    Func.lateCfg f =
      Func.dce (Func.renorm (Func.assumeElim (Func.deadLoadElim
        (Func.simplifyGroupFast (Func.ifOptBits (Func.renorm f)))))) :=
  rfl

theorem Func.lateOpt_eq {as rs : List Ty} (f : Func as rs) :
    Func.lateOpt f = Func.renorm (Func.lateCfg (Func.lateCore f)) :=
  rfl

attribute [irreducible] Func.earlyCore Func.earlyOpt Func.lateCore Func.lateCfg Func.lateOpt

/-- Renormalize a named function's body to flat canonical AST form, preserving metadata. -/
def Fn.renorm (fn : Fn) : Fn :=
  ⟨fn.name, fn.as, fn.rs, Func.renorm fn.body⟩

/-- Run acyclic small-callee inlining on `M` and renormalize every function body. -/
def Module.optInline (M : Module) (maxSize : Nat := 40) : Module :=
  let M' := M.inline maxSize
  { M' with fns := M'.fns.map Fn.renorm }

end LeanQbe.T
