module

public meta import Lean.Meta.Tactic.Simp.RegisterCommand
public meta import Lean.Elab.Command
public import Kraken.Separation

/-!
# Attributes for the C0 proof-scaling toolkit (`c0_load`, `c0_store`, `bv_c0`)

Lean only allows an attribute to be used in modules that import the module registering it, so the
attributes used by `LeanQbe.T.Logic.C0Step`, `LeanQbe.T.Logic.C0HeadStep`, and `c0_layout_lemmas!`
live here:

* `@[c0_load]` / `@[c0_store]`: memory access lemmas of the shape
  `(P ⋆ R) m → … → loadVal m t a = some v` (resp. `storeOk m t a ∧ (P' ⋆ R) (storeMem m t a v)`).
  Each lemma is indexed at two levels:
  1. First by the head constant of `P` (its *footprint predicate*, e.g. `cell`, `array`, `FullMem`,
     or a generated `Foo.At`), preserving `c0MemLemmas` for 100% backward compatibility.
  2. Second by `(P, AddrKey)` extracted from the target address `a` (`constOff base k`,
     `baseOnly base`, or `any`), enabling `O(1)` bucket dispatch in `c0MemLemmasForAddr` instead of
     linearly scanning hundreds of arena accessors.
* `bv_c0`: simp set normalizing C0 bit-vector casts and comparisons to `Nat` (`toNat`) form, ready
  for `omega`.
-/

set_option autoImplicit false

public section

/-- Simp set normalizing C0 bit-vector casts, offsets and comparisons to `toNat` form. -/
register_simp_attr bv_c0

namespace LeanQbe.T.C0Step

open Lean Meta

/-- Second-level address dispatch key for `@[c0_load]` / `@[c0_store]` lemmas. -/
meta inductive AddrKey where
  | constOff (baseField : Name) (off : Nat)
  | baseOnly (baseField : Name)
  | any
  deriving BEq, Hashable, Repr, Inhabited

/-- Two-level memory-lemma table for one direction (`c0_load` or `c0_store`).
`all` retains every lemma under its footprint head in registration order (`c0MemLemmas`), while
`byAddr` partitions lemmas by `(footprintHead, AddrKey)` for `O(1)` address-indexed dispatch. -/
meta structure C0MemTable where
  all : NameMap (Array Name) := {}
  byAddr : Std.HashMap (Name × AddrKey) (Array Name) := {}
  deriving Inhabited

meta def C0MemTable.insert (t : C0MemTable) (fp : Name) (ak : AddrKey) (nm : Name) : C0MemTable :=
  { all := t.all.insert fp ((t.all.find? fp |>.getD #[]).push nm)
    byAddr := t.byAddr.insert (fp, ak) ((t.byAddr.getD (fp, ak) #[]).push nm) }

/-- `c0_load` / `c0_store` lemma tables, indexed by `(footprintHead, AddrKey)`. -/
meta initialize c0MemExt :
    SimpleScopedEnvExtension (Bool × Name × AddrKey × Name) (C0MemTable × C0MemTable) ←
  registerSimpleScopedEnvExtension {
    initial := ({}, {})
    addEntry := fun (ld, st) (isLoad, fp, ak, nm) =>
      if isLoad then (ld.insert fp ak nm, st) else (ld, st.insert fp ak nm)
  }

/-- Evaluate a small constant `Nat` expression (literals, `OfNat`, `zero`/`succ`, `+`, `*`). -/
private meta partial def extractNatLit? (e : Lean.Expr) : Option Nat :=
  let e := e.consumeMData.headBeta
  match e with
  | .lit (.natVal n) => some n
  | _ =>
    if e.isAppOfArity ``OfNat.ofNat 3 then extractNatLit? (e.getArg! 1)
    else if e.isConstOf ``Nat.zero then some 0
    else if e.isAppOfArity ``Nat.succ 1 then (· + 1) <$> extractNatLit? (e.getArg! 0)
    else if e.isAppOfArity ``Nat.add 2 then
      (· + ·) <$> extractNatLit? (e.getArg! 0) <*> extractNatLit? (e.getArg! 1)
    else if e.isAppOfArity ``Nat.mul 2 then
      (· * ·) <$> extractNatLit? (e.getArg! 0) <*> extractNatLit? (e.getArg! 1)
    else if e.isAppOfArity ``HAdd.hAdd 6 then
      (· + ·) <$> extractNatLit? (e.getArg! 4) <*> extractNatLit? (e.getArg! 5)
    else if e.isAppOfArity ``HMul.hMul 6 then
      (· * ·) <$> extractNatLit? (e.getArg! 4) <*> extractNatLit? (e.getArg! 5)
    else e.nat?

/-- Extract a constant 64-bit byte offset from `BitVec.ofNat 64 k` or
`OfNat.ofNat (BitVec 64) k`. -/
private meta def extractBvOff? (e : Lean.Expr) : Option Nat :=
  let e := e.consumeMData.headBeta
  if e.isAppOfArity ``BitVec.ofNat 2 then
    (· % 2 ^ 64) <$> extractNatLit? (e.getArg! 1)
  else if e.isAppOfArity ``OfNat.ofNat 3 then
    (· % 2 ^ 64) <$> extractNatLit? (e.getArg! 1)
  else none

/-- Peel `Arg.val (Arg.var x)` / `Arg.val (Arg.imm v)` wrappers around an address expression. -/
private meta partial def unwrapArgVal (e : Lean.Expr) : Lean.Expr :=
  let e := e.consumeMData.headBeta
  if e.isAppOf `LeanQbe.T.Arg.val && e.getAppNumArgs ≥ 2 then
    let a := e.appArg!.consumeMData.headBeta
    if (a.isAppOf `LeanQbe.T.Arg.var || a.isAppOf `LeanQbe.T.Arg.imm) && a.getAppNumArgs ≥ 1 then
      unwrapArgVal a.appArg!
    else e
  else e

/-- Reject arithmetic/literal/control heads that are not pointer base accessors. -/
private meta def isNonBaseHead (nm : Name) : Bool :=
  nm == ``HAdd.hAdd || nm == ``HSub.hSub || nm == ``HMul.hMul ||
  nm == ``HShiftLeft.hShiftLeft || nm == ``HShiftRight.hShiftRight ||
  nm == ``BitVec.ofNat || nm == ``OfNat.ofNat ||
  nm == ``BitVec.setWidth || nm == ``BitVec.signExtend ||
  nm == ``ite || nm == ``dite || nm == ``cond

/-- Extract a non-reducible base field constant from `c.hdr`, `c.pArena`, or a `.proj`. -/
private meta def extractBaseConst? (e : Lean.Expr) (env? : Option Environment := none) :
    Option Name :=
  let e := unwrapArgVal e
  let nm? : Option Name :=
    match e with
    | .proj structName idx _ =>
      env?.bind fun env =>
        (getStructureInfo? env structName).bind fun info =>
          info.fieldInfo[idx]?.map (·.projFn)
    | _ => e.getAppFn.consumeMData.constName?
  match nm? with
  | some nm =>
    if isNonBaseHead nm then none
    else if env?.any (fun env =>
        !env.isProjectionFn nm && getReducibilityStatusCore env nm == .reducible) then none
    else some nm
  | none => none

/-- Walk down left-associated `HAdd.hAdd` chains to find the base operand. -/
private meta partial def leftmostAddOperand (e : Lean.Expr) : Lean.Expr :=
  let e := unwrapArgVal e
  if e.isAppOfArity ``HAdd.hAdd 6 then leftmostAddOperand (e.getArg! 4) else e

/-- Extract an `AddrKey` from an address expression (`c.hdr`, `c.hdr + 48`, `c.pArena + i * 4`,
`(c.pScratchBuf + off) + i * 4`, etc.). -/
meta def extractAddrKey (addr : Lean.Expr) (env? : Option Environment := none) : AddrKey :=
  let addr := unwrapArgVal addr
  if addr.isAppOfArity ``HAdd.hAdd 6 then
    let lhs := unwrapArgVal (addr.getArg! 4)
    let rhs := unwrapArgVal (addr.getArg! 5)
    if lhs.isAppOfArity ``HAdd.hAdd 6 then
      match extractBaseConst? (leftmostAddOperand lhs) env? with
      | some b => .baseOnly b
      | none => .any
    else
      match extractBaseConst? lhs env? with
      | some b =>
        match extractBvOff? rhs with
        | some k => .constOff b k
        | none => .baseOnly b
      | none => .any
  else
    match extractBaseConst? addr env? with
    | some b => .constOff b 0
    | none => .any

/-- Extract the address argument from a load (`loadVal m t a = some v`) or store
(`storeOk m t a ∧ ...`) conclusion. -/
meta def extractMemGoalAddr? (isLoad : Bool) (concl : Lean.Expr) : Option Lean.Expr :=
  let concl := concl.consumeMData.headBeta
  if isLoad then
    match concl.eq? with
    | some (_, lhs, _) =>
      let lhs := lhs.consumeMData.headBeta
      if lhs.isAppOf `LeanQbe.T.loadVal && lhs.getAppNumArgs == 3 then some (lhs.getArg! 2)
      else none
    | none => none
  else
    match concl.and? with
    | some (lhs, _) =>
      let lhs := lhs.consumeMData.headBeta
      if lhs.isAppOf `LeanQbe.T.storeOk && lhs.getAppNumArgs == 3 then some (lhs.getArg! 2)
      else none
    | none => none

/-- Head constant of the footprint `P` in the first hypothesis of shape `(P ⋆ R) m`. -/
meta def footprintKey (ty : Lean.Expr) : MetaM (Option Name) :=
  forallTelescopeReducing ty fun xs _ => do
    for x in xs do
      let t ← instantiateMVars (← inferType x)
      if t.isAppOf ``Std.ExtHashMap.sep && t.getAppNumArgs ≥ 3 then
        let p := t.getArg! (t.getAppNumArgs - 3)
        if let some c := p.getAppFn.constName? then return some c
    return none

/-- Footprint head and `AddrKey` of a `@[c0_load]` / `@[c0_store]` lemma type. -/
meta def footprintAndAddrKey (isLoad : Bool) (ty : Lean.Expr) :
    MetaM (Option (Name × AddrKey)) :=
  forallTelescopeReducing ty fun xs concl => do
    let mut fp? : Option Name := none
    for x in xs do
      let t ← instantiateMVars (← inferType x)
      if t.isAppOf ``Std.ExtHashMap.sep && t.getAppNumArgs ≥ 3 then
        let p := t.getArg! (t.getAppNumArgs - 3)
        if let some c := p.getAppFn.constName? then
          fp? := some c
          break
    let some fp := fp? | return none
    let env ← getEnv
    let ak := match extractMemGoalAddr? isLoad (← instantiateMVars concl) with
      | some addr => extractAddrKey addr (some env)
      | none => .any
    return some (fp, ak)

/-- Footprint- and address-indexed lemma attribute registration for `c0_load` and `c0_store`. -/
meta def registerC0MemAttr (attr : Name) (isLoad : Bool) : IO Unit :=
  registerBuiltinAttribute {
    name := attr
    descr := s!"C0 {if isLoad then "load" else "store"} lemma, indexed by footprint and address"
    add := fun decl _ kind => do
      let info ← getConstInfo decl
      let some (fp, ak) ← (footprintAndAddrKey isLoad info.type).run' {} {}
        | throwError "@[{attr}]: no hypothesis of shape `(P ⋆ R) m` with constant head `P`"
      c0MemExt.add (isLoad, fp, ak, decl) kind
  }

meta initialize registerC0MemAttr `c0_load true
meta initialize registerC0MemAttr `c0_store false

/-- All `c0_load` (`isLoad := true`) or `c0_store` lemmas registered for footprint `key`
(backward-compatible API preserving registration order). -/
meta def c0MemLemmas (env : Environment) (isLoad : Bool) (key : Name) : Array Name :=
  let (ld, st) := c0MemExt.getState env
  (if isLoad then ld else st).all.find? key |>.getD #[]

/-- Exact `(footprint, AddrKey)` bucket lookup. -/
meta def c0MemLemmasByKey (env : Environment) (isLoad : Bool) (fp : Name) (ak : AddrKey) :
    Array Name :=
  let (ld, st) := c0MemExt.getState env
  (if isLoad then ld else st).byAddr.getD (fp, ak) #[]

/-- Two-level `O(1)` candidate lookup for `(fp, addr)` ordered from most specific to generic:
* `constOff b off` → `constOff b off`, then `baseOnly b`, then `any`;
* `baseOnly b` → `baseOnly b`, then `any`;
* `any` → `any`. -/
meta def c0MemLemmasForAddr (env : Environment) (isLoad : Bool) (fp : Name) (addr : Lean.Expr) :
    Array Name :=
  let (ld, st) := c0MemExt.getState env
  let tbl := if isLoad then ld else st
  match extractAddrKey addr (some env) with
  | .constOff b off =>
    tbl.byAddr.getD (fp, .constOff b off) #[] ++
      tbl.byAddr.getD (fp, .baseOnly b) #[] ++
      tbl.byAddr.getD (fp, .any) #[]
  | .baseOnly b =>
    tbl.byAddr.getD (fp, .baseOnly b) #[] ++
      tbl.byAddr.getD (fp, .any) #[]
  | .any =>
    tbl.byAddr.getD (fp, .any) #[]

end LeanQbe.T.C0Step
