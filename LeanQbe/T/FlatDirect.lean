module

public import LeanQbe.T.Flat
public import LeanQbe.T.Module
public import LeanQbe.T.Legal
public import LeanQbe.T.Main

/-!
# First-Order `TFlat` Function Carrier, Target-Support Check, and `Ext` Collector

* `TFlatFn`, `TFlatFn.toFn`, `TFlatFn.wfCheck`, `TFlatFn.sig`, `TFlatFn.supportsSource`:
  first-order `Type 0` mirror of `Fn` backed by `denoteFunc`.
* `TFlat.extAux`, `TBlocks.extAux`, `TFlat.ext`: direct `TFlat` extraction of `Rega.Ext`
  (callee signatures and exit symbols, pruning dead `.jnz (.imm b)` arms) matching `Fn.ext`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-- First-order `Type 0` function mirroring `Fn` (`denoteFunc`-backed). -/
structure TFlatFn where
  name : Sym
  as : List Ty
  rs : List Ty
  body : TFlat rs

/-- Reconstruct a closed PHOAS `Fn` from a first-order `TFlatFn`. -/
def TFlatFn.toFn (f : TFlatFn) : Fn :=
  ⟨f.name, f.as, f.rs, denoteFunc f.body⟩

/-- Computable scope and type well-formedness check for a closed `TFlatFn`. -/
def TFlatFn.wfCheck (f : TFlatFn) : Bool :=
  f.body.wfCheck (pushTypes f.as []) []

/-- Signature entry `(name, as, rs)` matching `Fn.sig`. -/
def TFlatFn.sig (f : TFlatFn) : SigEntry :=
  (f.name, f.as, f.rs)

/-- Direct target-support check on a `TFlatFn`, matching `f.toFn.body.supportsSource lt`. -/
def TFlatFn.supportsSource (lt : LegalTarget) (f : TFlatFn) : Bool :=
  lt.valid && f.as.all lt.supportsTy && f.rs.all lt.supportsTy && f.body.supportsSource lt

mutual
/-- Direct `TFlat` mirror of `Expr.extAux`, collecting callee signatures and exit symbols
matching `Rega.lowerFlatExpr` traversal (pruning the dead arm of `.jnz (.imm b)`). -/
def TFlat.extAux {rs : List Ty} :
    TFlat rs → List SigEntry → List Sym → List SigEntry × List Sym
  | .let_ _ k, cs, xs => k.extAux cs xs
  | .load _ _ k, cs, xs => k.extAux cs xs
  | .store _ _ k, cs, xs => k.extAux cs xs
  | .call g (as := as) bs _ k, cs, xs => k.extAux (addCalleeSig g as bs cs) xs
  | .jnz (.imm b) t e, cs, xs =>
    if b then t.extAux cs xs else e.extAux cs xs
  | .jnz (.var _) t e, cs, xs =>
    let (cs₁, xs₁) := e.extAux cs xs
    t.extAux cs₁ xs₁
  | .jump _ _, cs, xs | .ret _, cs, xs | .hlt, cs, xs => (cs, xs)
  | .exit g _, cs, xs => (cs, addExitSym g xs)
  | .group bodies k, cs, xs =>
    let (cs₁, xs₁) := k.extAux cs xs
    bodies.extAux cs₁ xs₁

/-- Mutual helper for `TFlat.extAux` over `TBlocks`. -/
def TBlocks.extAux {rs : List Ty} :
    {sig : List (List Ty)} → TBlocks rs sig →
    List SigEntry → List Sym → List SigEntry × List Sym
  | _, .nil, cs, xs => (cs, xs)
  | _, .cons b bs, cs, xs =>
    let (cs₁, xs₁) := b.extAux cs xs
    bs.extAux cs₁ xs₁
end

/-- Extract `Rega.Ext` (callee signatures and exit targets) directly from a `TFlat`. -/
def TFlat.ext {rs : List Ty} (tf : TFlat rs) : Rega.Ext :=
  let (cs, xs) := tf.extAux [] []
  ⟨cs.reverse, xs.reverse⟩

end LeanQbe.T
