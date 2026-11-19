module

public import LeanQbe.T.Frontend.C0.Parser
public import LeanQbe.T.Frontend.C0.Layout
public import LeanQbe.T.Frontend.C0.Elab
public import LeanQbe.T.Logic.C0Step
public meta import LeanQbe.T.Frontend.C0.Parser
public meta import LeanQbe.T.Frontend.C0.Layout
public meta import LeanQbe.T.Frontend.C0.Elab
public meta import Lean.Elab.Command

/-!
# `c0_layout_lemmas!` & `c0_decl_and_layout!`: struct footprints and lemmas from C0 layouts

`c0_layout_lemmas! "<C0 source>"` lays out every non-union `struct` of a C0 translation unit
(which may also contain `extern`s and C function definitions) with `Frontend.C0.Layout`
(SysV LP64) and, for each struct `S` with scalar fields (`uN`/`iN`, pointers, including scalars
recursively flattened from embedded non-union structs `structRef` / `anonAggregate false` as
`<outer>_<inner>` at offset `o_outer + o_inner`), generates in the current namespace:

* `structure S` with one `BitVec (8 * sizeof f)` field per scalar C field (flat structs keep
  their exact C names and order; embedded non-union structs flatten to `outer_inner`);
* `S.sizeof : Nat` and `S.At (p : BitVec 64) (s : S) : Mem 64 → Prop`, the separation-logic
  footprint `cell p s.f₀ ⋆ cell (p + o₁) s.f₁ ⋆ …` at the C byte offsets `oᵢ` (padding is
  not owned);
* `@[c0_load] S.load_f : (S.At p s ⋆ R) m → loadVal m (.bits w) (p + o) = some s.f`;
* `@[c0_store] S.store_f v : (S.At p s ⋆ R) m →
    storeOk m (.bits w) (p + o) ∧ (S.At p { s with f := v } ⋆ R) (storeMem m (.bits w) (p + o) v)`.

`c0_decl_and_layout! [pfx] "<C0 source>"` elaborates both `c0_layout_lemmas!` and `c0_decl!`
from a single combined C0 source string so struct definitions are never duplicated.

Field `0` is addressed by `p` itself, matching the lowering of `s->f₀`. The store lemmas update the
state with a record update, so frames over the unchanged fields are free: proofs and invariants
talk about `{ s with f := v }` and never list the other fields. `c0_step` finds these lemmas through
the `S.At` footprint of the current separation-logic hypotheses. Generated proofs only use
`loadVal_cell` / `store_cell` and `c0_frame` (AC frame matching), so they depend on the standard
axioms only.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Frontend.C0

open Lean Elab Command

/-- A scalar struct field: C name, byte offset, and width in bits. -/
meta structure LayoutField where
  name : String
  off : Nat
  bits : Nat

/-- Scalar view of a resolved C0 field type (`none` for aggregates, arrays, floats, bitfields). -/
meta def scalarBits (env : LayoutEnv) (ty : C0Type) : Option Nat :=
  match resolveType env ty with
  | .ok (.int _ b) => if b == 8 || b == 16 || b == 32 || b == 64 then some b else none
  | .ok (.ptr _) => some 64
  | _ => none

/-- Scalar fields of an aggregate layout, recursively flattening embedded non-union structs
(`structRef` / `anonAggregate false`) to `<outer>_<inner>` at exact offset `o_outer + o_inner`.
Flat structs keep their exact C field names/offsets; unions, arrays, floats, and bitfields are
skipped (not owned). -/
meta def layoutFields (env : LayoutEnv) (lay : AggregateLayout) : List LayoutField :=
  go 64 "" 0 lay
where
  go : Nat → String → Nat → AggregateLayout → List LayoutField
    | 0, _, _, _ => []
    | fuel + 1, pfx, baseOff, lay =>
      if lay.isUnion then []
      else lay.fields.flatMap fun (nm, loc) =>
        let full := if pfx.isEmpty then nm else s!"{pfx}_{nm}"
        match loc with
        | .regular off ty _ =>
          let absOff := baseOff + off
          match scalarBits env ty with
          | some b => [⟨full, absOff, b⟩]
          | none =>
            match resolveType env ty with
            | .ok (.structRef tag) =>
              match env.structs.get? tag with
              | some subLay => go fuel full absOff subLay
              | none => []
            | .ok (.anonAggregate false fields) =>
              match layoutAggregate env false fields with
              | .ok subLay => go fuel full absOff subLay
              | .error _ => []
            | _ => []
        | .bitfield .. => []

/-- All named, non-union struct layouts of a translation unit (typedef name preferred). -/
meta def structLayouts (tu : TranslationUnit) (env : LayoutEnv) :
    Except String (List (String × AggregateLayout)) := do
  let mut out : List (String × AggregateLayout) := []
  for d in tu.decls do
    match d with
    | .typedef nm ty =>
      match resolveType env ty with
      | .ok (.anonAggregate false fields) =>
        out := out ++ [(nm, ← layoutAggregate env false fields)]
      | .ok (.structRef tag) =>
        if let some lay := env.structs.get? tag then
          out := (out.filter (·.1 != tag)) ++ [(nm, lay)]
      | _ => pure ()
    | .structDef sd =>
      if !sd.isUnion && !(out.any (·.1 == sd.name)) then
        if let some lay := env.structs.get? sd.name then out := out ++ [(sd.name, lay)]
    | _ => pure ()
  return out

private meta def q (s : String) : String := s!"«{s}»"

private meta def addrOf (f : LayoutField) : String :=
  if f.off == 0 then "p" else s!"(p + {f.off})"

private meta def memTy : String := "Std.ExtHashMap (BitVec 64) UInt8"

/-- Lean source of all declarations generated for struct `S` with fields `fs`. -/
meta def layoutCommands (S : String) (size : Nat) (fs : List LayoutField) : List String :=
  let sQ := q S
  let struct := s!"structure {sQ} where\n" ++
    String.intercalate "\n" (fs.map fun f => s!"  {q f.name} : BitVec {f.bits}")
  let cellOf (f : LayoutField) :=
    s!"LeanQbe.T.cell (t := .bits {f.bits}) {addrOf f} s.{q f.name}"
  let atBody := String.intercalate " ⋆\n    " (fs.map cellOf)
  let sizeDef := s!"def {sQ}.sizeof : Nat := {size}"
  let atDef := s!"def {sQ}.At (p : BitVec 64) (s : {sQ}) : {memTy} → Prop :=\n    {atBody}"
  let hyps := s!"\{p : BitVec 64} \{s : {sQ}} \{R : {memTy} → Prop} \{m : {memTy}}"
  let loads := fs.map fun f =>
    s!"@[c0_load] theorem {sQ}.{q ("load_" ++ f.name)} {hyps}\n" ++
    s!"    (h : ({sQ}.At p s ⋆ R) m) :\n" ++
    s!"    LeanQbe.T.loadVal m (.bits {f.bits}) {addrOf f} = some s.{q f.name} := by\n" ++
    s!"  unfold {sQ}.At at h; exact LeanQbe.T.loadVal_cell (by decide) (by c0_frame)"
  let upd (f : LayoutField) :=
    if fs.length == 1 then s!"\{ {q f.name} := v }" else s!"\{ s with {q f.name} := v }"
  let stores := fs.map fun f =>
    let a := addrOf f
    s!"@[c0_store] theorem {sQ}.{q ("store_" ++ f.name)} {hyps} (v : BitVec {f.bits})\n" ++
    s!"    (h : ({sQ}.At p s ⋆ R) m) :\n" ++
    s!"    LeanQbe.T.storeOk m (.bits {f.bits}) {a} ∧\n" ++
    s!"      ({sQ}.At p {upd f} ⋆ R)\n" ++
    s!"        (LeanQbe.T.storeMem m (.bits {f.bits}) {a} v) := by\n" ++
    s!"  unfold {sQ}.At at h ⊢\n" ++
    s!"  obtain ⟨hok, h'⟩ := LeanQbe.T.store_cell (t := .bits {f.bits}) (a := {a}) v " ++
    s!"(by decide)\n    (show (LeanQbe.T.cell {a} s.{q f.name} ⋆ _) m by c0_frame)\n" ++
    s!"  exact ⟨hok, by dsimp only; c0_frame⟩"
  [struct, sizeDef, atDef] ++ loads ++ stores

/-- Parse and elaborate one generated command. -/
meta def elabGenerated (src : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command src "<c0_layout_lemmas!>" with
  | .ok stx => elabCommand stx
  | .error err => throwError "c0_layout_lemmas!: generated code does not parse: {err}\n{src}"

private meta def checkFieldNamesUnique (S : String) (fs : List LayoutField) :
    CommandElabM Unit := do
  let mut seen : Std.HashSet String := {}
  for f in fs do
    if seen.contains f.name then
      throwError "c0_layout_lemmas!: duplicate flattened field '{f.name}' in struct '{S}'"
    seen := seen.insert f.name

/-- Generate layout structures, footprints, and `c0_load` / `c0_store` lemmas for `src`. -/
meta def elabC0Layout (src : String) : CommandElabM Unit := do
  let tu ← match parseC0 src with
    | .ok tu => pure tu
    | .error err => throwError err
  let env ← match buildLayoutEnv tu with
    | .ok e => pure e
    | .error err => throwError err
  let lays ← match structLayouts tu env with
    | .ok l => pure l
    | .error err => throwError err
  if lays.isEmpty then throwError "c0_layout_lemmas!: no struct definitions found"
  let mut emitted : Nat := 0
  for (S, lay) in lays do
    let fs := layoutFields env lay
    if fs.isEmpty then continue
    checkFieldNamesUnique S fs
    for cmd in layoutCommands S lay.size fs do
      elabGenerated cmd
    emitted := emitted + 1
  if emitted == 0 then
    throwError "c0_layout_lemmas!: no struct definitions with scalar fields found"

/-- Elaborate both struct layout lemmas (`elabC0Layout`) and C0 module functions (`elabC0Module`)
from a single combined C0 source string. -/
meta def elabC0DeclAndLayout (modPrefix? : Option Name) (src : String)
    (exits : List Sym := []) (forceExpose : Bool := false)
    (registerShapes : Bool := true) (emitModule : Bool := true) : CommandElabM Unit := do
  elabC0Layout src
  elabC0Module modPrefix? src exits forceExpose registerShapes emitModule

/-- `c0_layout_lemmas! "<C0 source>"`: see the module documentation. -/
syntax "c0_layout_lemmas! " str : command

/-- `c0_decl_and_layout! [pfx] "<C0 source>"`: elaborate both `c0_layout_lemmas!` and `c0_decl!`
from a single combined C0 source string without duplicating struct definitions. -/
syntax "c0_decl_and_layout! " (ident)? str : command

elab_rules : command
  | `(c0_layout_lemmas! $src:str) => elabC0Layout src.getString
  | `(c0_decl_and_layout! $[$pfx:ident]? $src:str) =>
    elabC0DeclAndLayout (pfx.map (·.getId)) src.getString

end LeanQbe.T.Frontend.C0
