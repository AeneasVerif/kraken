module

public import LeanQbe.T.Flat
public import LeanQbe.T.OptUtil
public import LeanQbe.T.Fold
public import LeanQbe.T.Canon
public import LeanQbe.T.Copy
public import LeanQbe.T.Gvn
public import LeanQbe.T.DceParam
public import LeanQbe.T.DivConst
public import LeanQbe.T.MemLoad
public import LeanQbe.T.Peel
public import LeanQbe.T.IfOpt
public import LeanQbe.T.SimplifyGroupPlan
public import LeanQbe.T.Licm
public import LeanQbe.T.AddrRangeOpt
public import LeanQbe.T.LoopRotate
public import LeanQbe.T.CondThreadOpt
public import LeanQbe.T.ZeroPeel
public import LeanQbe.T.AssumeBits
public import LeanQbe.T.Inline
public import LeanQbe.T.Module

/-!
# The Staged Typed-IR Mid-End Pipeline

* `Func.opt`: legacy mid-end (`fold → copy → gvn → copy → fold → dceP`).
* `Func.earlyOpt`: pre-`Legal` pipeline (`fold → canon → copy → gvn → copy → fold → ifOpt →
  simplifyGroupFast → peelFast 24 → zeroPeelWith { peelBudget := 24 } → copy → fold → dceP →
  renorm`), simplifying source and inlined bodies, if-converting branch diamonds, widening
  constant-fill loops, and peeling bounded loops while preserving multi-word widening
  arithmetic (`addc`/`subb`/`mulx` chains).
* `Func.lateOpt`: post-`Legal` pipeline (`fold → canon → divConst → copy → renorm → memLoad →
  gvn → assumeBits → fold → renorm → ifOptBits → simplifyGroupFast → deadLoadElim →
  assumeElim → fold → addrRangeOpt → gvn → renorm → licm → dceP → loopRotate → mergeRets →
  renorm → condThreadLateOpt → fold → dceP → renorm`), running target-safe scalar division
  reduction, memory load forwarding, known-bits simplification, machine-width if-conversion,
  loop-aware address reassociation and range-check collapse, loop-invariant code motion, CFG loop
  rotation, conditional branch threading, and cleanup on legalized IR.
* `Fn.renorm` / `Module.optInline`: acyclic small-callee inlining followed by materialized
  AST renormalization.

Correctness (`LeanQbe/T/OptLemmas.lean`): `Func.opt_wf`, `Func.opt_spec`, `Func.earlyOpt_wf`,
`Func.earlyOpt_spec`, `Func.lateOpt_wf`, `Func.lateOpt_spec`, `Module.optInline_ok`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-- Run the legacy mid-end optimization pipeline on a closed typed function. -/
def Func.opt {as rs : List Ty} (f : Func as rs) : Func as rs :=
  Func.dceP (Func.fold (Func.copy (Func.gvn (Func.copy (Func.fold f)))))

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
/-- True iff `tf` contains an eliminable single-block acyclic join group (gating
`simplifyGroupFast` so non-join functions bypass the pass until gate removal). -/
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

/-- Renormalize and run `Func.simplifyGroupPlan` (with trailing `Func.renorm`) only when an
acyclic join candidate is present (gating single-use non-tail joins to `≤ 1` loop fns). -/
def Func.simplifyGroupFast {as rs : List Ty} (f : Func as rs) : Func as rs :=
  let tf := reifyFunc f
  if hasSimpGroup (tflatLoops tf ≤ 1) tf then
    Func.renorm (Func.simplifyGroupPlan (denoteFunc tf))
  else denoteFunc tf

/-- Renormalize and apply bounded loop peeling (`Func.peel`) only to compact single-loop
functions (`≤ 1` loop and `≤ 40` AST nodes), avoiding `O(N)` code expansion across multi-loop
parsers. -/
def Func.peelFast {as rs : List Ty} (f : Func as rs) (budget : Nat := 24) : Func as rs :=
  let tf := reifyFunc f
  if tflatLoops tf ≤ 1 && tflatSize tf ≤ 40 then Func.renorm (Func.peel (denoteFunc tf) budget)
  else denoteFunc tf

mutual
/-- Count `.ret` sites inside a `TFlat` AST. -/
def tflatRets {rs : List Ty} : TFlat rs → Nat
  | .let_ _ k | .load _ _ k | .store _ _ k | .call _ _ _ k => tflatRets k
  | .jnz _ t e => tflatRets t + tflatRets e
  | .jump _ _ | .exit _ _ | .hlt => 0
  | .ret _ => 1
  | .group bodies k => tblocksRets bodies + tflatRets k

/-- Block-list companion of `tflatRets`. -/
def tblocksRets {rs : List Ty} : {sig : List (List Ty)} → TBlocks rs sig → Nat
  | _, .nil => 0
  | _, .cons b bs => tflatRets b + tblocksRets bs
end

mutual
/-- Replace all `.ret vs` with `.jump exit_lbl vs` throughout an `Expr`. -/
def Expr.mergeRets {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (exit_lbl : L rs) : Expr V L rs → Expr V L rs
  | .let_ op k => .let_ op fun xs => (k xs).mergeRets exit_lbl
  | .load t a k => .load t a fun v => (k v).mergeRets exit_lbl
  | .store v a k => .store v a (k.mergeRets exit_lbl)
  | .call f args k => .call f args fun xs => (k xs).mergeRets exit_lbl
  | .jnz c t e => .jnz c (t.mergeRets exit_lbl) (e.mergeRets exit_lbl)
  | .jump j args => .jump j args
  | .ret vs => .jump exit_lbl vs
  | .exit f args => .exit f args
  | .hlt => .hlt
  | .group bodies k =>
    .group (fun Js => (bodies Js).mergeRets exit_lbl)
      (fun Js => (k Js).mergeRets exit_lbl)

/-- Block-list companion of `Expr.mergeRets`. -/
def Blocks.mergeRets {V : Ty → Type} {L : List Ty → Type} {rs : List Ty}
    (exit_lbl : L rs) : {sig : List (List Ty)} → Blocks V L rs sig → Blocks V L rs sig
  | _, .nil => .nil
  | _, .cons b bs =>
    .cons (fun xs => (b xs).mergeRets exit_lbl) (bs.mergeRets exit_lbl)
end

/-- Unified Epilogue Merging (`Func.mergeRets`): when a function has `≥ 2` `.ret` sites,
rewrite the body into a single outer `Expr.group` with one shared exit join block
`exit_blk(ret_vals) -> .ret ret_vals`, replacing every interior `.ret xs` with
`.jump exit_blk xs`. Single-return (`retCount ≤ 1`) functions bypass rewriting without
modifying the body. -/
def Func.mergeRets {as rs : List Ty} (f : Func as rs) : Func as rs :=
  let tf := reifyFunc f
  if tflatRets tf ≥ 2 then
    fun V L params =>
      .group (sig := [rs])
        (fun (_, ()) => .cons (fun r_params => .ret (toArgTup r_params)) .nil)
        (fun (exit_lbl, ()) => (f V L params).mergeRets exit_lbl)
  else f

/-- Pre-`Legal` value-optimization core (`fold → canon → copy → gvn → copy → fold`). -/
def Func.earlyCore {as rs : List Ty} (f : Func as rs) : Func as rs :=
  Func.fold (Func.copy (Func.gvn (Func.copy (Func.canon (Func.fold f)))))

/-- Pre-`Legal` mid-end (`earlyOpt`): simplify source/inlined bodies, peel compact single-loop
functions, widen constant-fill loops / peel small single-iter loops (`ZeroPeel`), clean `.copy`
bindings, and keep PHOAS closures flat via `Func.renorm` for `Legal`. -/
def Func.earlyOpt {as rs : List Ty} (f : Func as rs) : Func as rs :=
  Func.renorm (Func.dceP (Func.fold (Func.copy (Func.zeroPeelWith { peelBudget := 24 }
    (Func.peelFast (Func.simplifyGroupFast (Func.ifOpt (Func.earlyCore f))) 24)))))

/-- Post-`Legal` pre-`renorm` value core (`fold → canon → divConst → copy`). -/
def Func.lateCorePre {as rs : List Ty} (f : Func as rs) : Func as rs :=
  Func.copy (Func.divConst (Func.canon (Func.fold f)))

/-- Post-`Legal` post-`renorm` memory/known-bits core (`memLoad → gvn → assumeBits → fold`). -/
def Func.lateCorePost {as rs : List Ty} (f : Func as rs) : Func as rs :=
  Func.fold (Func.assumeBits (Func.gvn (Func.memLoad f)))

/-- Post-`Legal` value/memory optimization core (`fold → canon → divConst → copy → renorm →
memLoad → gvn → assumeBits → fold`). -/
def Func.lateCore {as rs : List Ty} (f : Func as rs) : Func as rs :=
  Func.lateCorePost (Func.renorm (Func.lateCorePre f))

/-- Post-`Legal` CFG/cleanup pre-`licm` core (`ifOptBits → simplifyGroupFast → deadLoadElim →
assumeElim → fold → addrRangeOpt → gvn`). -/
def Func.lateCfgPre {as rs : List Ty} (f : Func as rs) : Func as rs :=
  Func.gvn (Func.addrRangeOpt (Func.fold (Func.assumeElim (Func.deadLoadElim
    (Func.simplifyGroupFast (Func.ifOptBits f))))))

/-- Post-`Legal` CFG/cleanup post-`licm` core (`licm → dceP`). -/
def Func.lateCfgPost {as rs : List Ty} (f : Func as rs) : Func as rs :=
  Func.dceP (Func.licm f)

/-- Post-`Legal` tail (`licm → dceP → loopRotate → mergeRets`) prior to conditional branch
threading. -/
def Func.lateLoopRotate {as rs : List Ty} (f : Func as rs) : Func as rs :=
  Func.mergeRets (Func.loopRotate (Func.lateCfgPost f))

/-- Post-`Legal` branch-threading and cleanup tail (`condThreadLateOpt → fold → dceP`). -/
def Func.lateCondThread {as rs : List Ty} (f : Func as rs) : Func as rs :=
  Func.dceP (Func.fold (Func.condThreadLateOpt f))

/-- Post-`Legal` CFG/cleanup core (`renorm → ifOptBits → simplifyGroupFast → deadLoadElim →
assumeElim → fold → addrRangeOpt → gvn → renorm → licm → dceP`). -/
def Func.lateCfg {as rs : List Ty} (f : Func as rs) : Func as rs :=
  Func.lateCfgPost (Func.renorm (Func.lateCfgPre (Func.renorm f)))

/-- Post-`Legal` mid-end (`lateOpt`): strength-reduce constant division, forward memory loads,
run machine-width `.bits` if-conversion (`ifOptBits`), clean up dead loads/blocks, reassociate
addresses and collapse range checks (`addrRangeOpt`), hoist loop-invariant pure operations
(`licm`), rotate header-tested loops (`loopRotate`), merge duplicate epilogues (`mergeRets`),
thread constant/known branches (`condThreadLateOpt`), and clean up before `Rega`. -/
def Func.lateOpt {as rs : List Ty} (f : Func as rs) : Func as rs :=
  Func.renorm (Func.lateCondThread (Func.renorm
    (Func.lateLoopRotate (Func.lateCfg (Func.lateCore f)))))

theorem Func.mergeRets_eq {as rs : List Ty} (f : Func as rs) :
    Func.mergeRets f =
      let tf := reifyFunc f
      if tflatRets tf ≥ 2 then
        fun V L params =>
          .group (sig := [rs])
            (fun (_, ()) => .cons (fun r_params => .ret (toArgTup r_params)) .nil)
            (fun (exit_lbl, ()) => (f V L params).mergeRets exit_lbl)
      else f :=
  rfl

theorem Func.simplifyGroupFast_eq {as rs : List Ty} (f : Func as rs) :
    Func.simplifyGroupFast f =
      let tf := reifyFunc f
      if hasSimpGroup (tflatLoops tf ≤ 1) tf then
        Func.renorm (Func.simplifyGroupPlan (denoteFunc tf))
      else denoteFunc tf :=
  rfl

theorem Func.peelFast_eq {as rs : List Ty} (f : Func as rs) (budget : Nat := 24) :
    Func.peelFast f budget =
      let tf := reifyFunc f
      if tflatLoops tf ≤ 1 && tflatSize tf ≤ 40 then Func.renorm (Func.peel (denoteFunc tf) budget)
      else denoteFunc tf :=
  rfl

theorem Func.earlyCore_eq {as rs : List Ty} (f : Func as rs) :
    Func.earlyCore f =
      Func.fold (Func.copy (Func.gvn (Func.copy (Func.canon (Func.fold f))))) :=
  rfl

theorem Func.earlyOpt_eq {as rs : List Ty} (f : Func as rs) :
    Func.earlyOpt f =
      Func.renorm (Func.dceP (Func.fold (Func.copy (Func.zeroPeelWith { peelBudget := 24 }
        (Func.peelFast (Func.simplifyGroupFast (Func.ifOpt (Func.earlyCore f))) 24))))) :=
  rfl

theorem Func.lateCorePre_eq {as rs : List Ty} (f : Func as rs) :
    Func.lateCorePre f = Func.copy (Func.divConst (Func.canon (Func.fold f))) :=
  rfl

theorem Func.lateCorePost_eq {as rs : List Ty} (f : Func as rs) :
    Func.lateCorePost f = Func.fold (Func.assumeBits (Func.gvn (Func.memLoad f))) :=
  rfl

theorem Func.lateCore_eq {as rs : List Ty} (f : Func as rs) :
    Func.lateCore f =
      Func.fold (Func.assumeBits (Func.gvn (Func.memLoad (Func.renorm (Func.copy
        (Func.divConst (Func.canon (Func.fold f)))))))) :=
  rfl

theorem Func.lateCfgPre_eq {as rs : List Ty} (f : Func as rs) :
    Func.lateCfgPre f =
      Func.gvn (Func.addrRangeOpt (Func.fold (Func.assumeElim (Func.deadLoadElim
        (Func.simplifyGroupFast (Func.ifOptBits f)))))) :=
  rfl

theorem Func.lateCfgPost_eq {as rs : List Ty} (f : Func as rs) :
    Func.lateCfgPost f = Func.dceP (Func.licm f) :=
  rfl

theorem Func.lateLoopRotate_eq {as rs : List Ty} (f : Func as rs) :
    Func.lateLoopRotate f = Func.mergeRets (Func.loopRotate (Func.lateCfgPost f)) :=
  rfl

theorem Func.lateCondThread_eq {as rs : List Ty} (f : Func as rs) :
    Func.lateCondThread f = Func.dceP (Func.fold (Func.condThreadLateOpt f)) :=
  rfl

theorem Func.lateCfg_def {as rs : List Ty} (f : Func as rs) :
    Func.lateCfg f = Func.lateCfgPost (Func.renorm (Func.lateCfgPre (Func.renorm f))) :=
  rfl

theorem Func.lateCfg_eq {as rs : List Ty} (f : Func as rs) :
    Func.lateCfg f =
      Func.dceP (Func.licm (Func.renorm (Func.gvn (Func.addrRangeOpt (Func.fold (Func.assumeElim
        (Func.deadLoadElim (Func.simplifyGroupFast (Func.ifOptBits (Func.renorm f)))))))))) :=
  rfl

theorem Func.lateOpt_eq {as rs : List Ty} (f : Func as rs) :
    Func.lateOpt f = Func.renorm (Func.lateCondThread (Func.renorm
      (Func.lateLoopRotate (Func.lateCfg (Func.lateCore f))))) :=
  rfl

attribute [irreducible] Func.mergeRets Func.simplifyGroupFast Func.peelFast
attribute [irreducible] Func.earlyCore Func.earlyOpt
attribute [irreducible] Func.lateCorePre Func.lateCorePost Func.lateCore
attribute [irreducible] Func.lateCfgPre Func.lateCfgPost Func.lateLoopRotate Func.lateCondThread
attribute [irreducible] Func.lateCfg Func.lateOpt

/-- Renormalize a named function's body to flat canonical AST form once, preserving metadata. -/
def Fn.renorm (fn : Fn) : Fn :=
  let tf := reifyFunc fn.body
  ⟨fn.name, fn.as, fn.rs, denoteFunc tf⟩

/-- Run acyclic small-callee inlining on `M` and renormalize every function body. -/
def Module.optInline (M : Module) (maxSize : Nat := 40) : Module :=
  let M' := M.inline maxSize
  { M' with fns := M'.fns.map Fn.renorm }

end LeanQbe.T
