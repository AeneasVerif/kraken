module

public import LeanQbe.T.Frontend.C0.Syntax
public import Std.Data.HashMap

/-!
# SysV LP64 Struct, Union, and Bitfield Layout (`X0-core`)

Computes deterministic byte sizes, natural alignments, field byte offsets, and little-endian
LSB-first non-straddling bitfield positions matching `gcc`/`clang` under SysV LP64.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Frontend.C0

/-- Location of a field within an aggregate (`struct` or `union`). -/
inductive FieldLoc : Type
  | regular (byteOff : Nat) (ty : C0Type) (size : Nat)
  | bitfield (unitByteOff : Nat) (unitBytes : Nat) (localBitOff : Nat) (width : Nat) (declaredTy : C0Type)
  deriving Repr, BEq, Inhabited

/-- Resolved layout of a `struct` or `union`. -/
structure AggregateLayout : Type where
  isUnion : Bool
  size : Nat
  align : Nat
  fields : List (String × FieldLoc)
  deriving Repr, BEq, Inhabited

/-- Type & aggregate layout environment for a C0 translation unit. -/
structure LayoutEnv : Type where
  typedefs : Std.HashMap String C0Type := {}
  structs : Std.HashMap String AggregateLayout := {}
  unions : Std.HashMap String AggregateLayout := {}
  deriving Inhabited

def alignUp (n a : Nat) : Nat :=
  if a ≤ 1 then n else ((n + a - 1) / a) * a

/-- Expand `typedefRef` chains with a cycle limit. -/
def resolveType (env : LayoutEnv) : C0Type → Except String C0Type :=
  go 64
where
  go : Nat → C0Type → Except String C0Type
    | 0, t => throw s!"cyclic typedef resolving {repr t}"
    | fuel + 1, .typedefRef nm => do
      match env.typedefs.get? nm with
      | some t' => go fuel t'
      | none => throw s!"unknown typedef '{nm}'"
    | fuel + 1, .ptr elem => do pure (.ptr (← go fuel elem))
    | fuel + 1, .array elem len => do pure (.array (← go fuel elem) len)
    | fuel + 1, .tuple elems => do pure (.tuple (← elems.mapM (go fuel)))
    | _, t => pure t

mutual
  /-- Compute `(sizeof, alignof)` in bytes under SysV LP64.
  Trailing flexible arrays `T[]` contribute `size = 0` and `align = alignof(T)`. -/
  partial def typeSizeAlign (env : LayoutEnv) (ty : C0Type) : Except String (Nat × Nat) := do
    match ← resolveType env ty with
    | .void => throw "cannot take size of void"
    | .bool => pure (1, 1)
    | .int _ bits =>
      let b := (bits + 7) / 8
      pure (b, b)
    | .f64 => pure (8, 8)
    | .ptr _ => pure (8, 8)
    | .array elem (some len) =>
      let (sz, al) ← typeSizeAlign env elem
      pure (sz * len, al)
    | .array elem none =>
      let (_, al) ← typeSizeAlign env elem
      pure (0, al)
    | .structRef nm =>
      match env.structs.get? nm with
      | some lay => pure (lay.size, lay.align)
      | none => throw s!"incomplete or unknown struct '{nm}'"
    | .unionRef nm =>
      match env.unions.get? nm with
      | some lay => pure (lay.size, lay.align)
      | none => throw s!"incomplete or unknown union '{nm}'"
    | .anonAggregate isUnion fields =>
      let lay ← layoutAggregate env isUnion fields
      pure (lay.size, lay.align)
    | .tuple _ =>
      throw "tuple types have no C memory layout"
    | .typedefRef nm =>
      throw s!"unresolved typedef '{nm}'"

  /-- Lay out a `struct` or `union` under SysV LP64. -/
  partial def layoutAggregate (env : LayoutEnv) (isUnion : Bool) (fields : List FieldDecl) :
      Except String AggregateLayout := do
    if isUnion then
      let mut maxSize : Nat := 0
      let mut maxAlign : Nat := 1
      let mut outFields : List (String × FieldLoc) := []
      for f in fields do
        let fty ← resolveType env f.ty
        match f.bitWidth with
        | none =>
          let (sz, al) ← typeSizeAlign env fty
          if sz > maxSize then maxSize := sz
          if al > maxAlign then maxAlign := al
          if let some nm := f.name then
            outFields := outFields ++ [(nm, .regular 0 fty sz)]
        | some w =>
          let (unitBytes, al) ← typeSizeAlign env fty
          let unitBits := unitBytes * 8
          if w > unitBits then
            throw s!"bitfield width {w} exceeds base type width {unitBits}"
          if w > 0 then
            let neededBytes := (w + 7) / 8
            if neededBytes > maxSize then maxSize := neededBytes
            if unitBytes > maxSize then maxSize := unitBytes
            if al > maxAlign then maxAlign := al
            if let some nm := f.name then
              outFields := outFields ++ [(nm, .bitfield 0 unitBytes 0 w fty)]
      pure { isUnion := true, size := alignUp maxSize maxAlign, align := maxAlign, fields := outFields }
    else
      let mut bitCursor : Nat := 0
      let mut maxAlign : Nat := 1
      let mut outFields : List (String × FieldLoc) := []
      let nFields := fields.length
      for idx in [:nFields] do
        let f := fields[idx]!
        let fty ← resolveType env f.ty
        match f.bitWidth with
        | none =>
          match fty with
          | .array _ none =>
            if idx + 1 != nFields then
              throw "flexible array member must be the last field of a struct"
          | _ => pure ()
          let (sz, al) ← typeSizeAlign env fty
          let byteOff := alignUp ((bitCursor + 7) / 8) al
          bitCursor := (byteOff + sz) * 8
          if al > maxAlign then maxAlign := al
          if let some nm := f.name then
            outFields := outFields ++ [(nm, .regular byteOff fty sz)]
        | some w =>
          let (unitBytes, al) ← typeSizeAlign env fty
          let unitBits := unitBytes * 8
          if unitBytes != 1 && unitBytes != 2 && unitBytes != 4 && unitBytes != 8 then
            throw s!"unsupported bitfield storage unit size {unitBytes}"
          if w > unitBits then
            throw s!"bitfield width {w} exceeds base type width {unitBits}"
          if w == 0 then
            bitCursor := alignUp bitCursor unitBits
          else
            let unitStart := (bitCursor / unitBits) * unitBits
            let placedBit :=
              if bitCursor + w ≤ unitStart + unitBits then bitCursor
              else alignUp bitCursor unitBits
            let unitByteOff := (placedBit / unitBits) * unitBytes
            let localBitOff := placedBit % unitBits
            bitCursor := placedBit + w
            if al > maxAlign then maxAlign := al
            if let some nm := f.name then
              outFields := outFields ++ [(nm, .bitfield unitByteOff unitBytes localBitOff w fty)]
      let rawBytes := (bitCursor + 7) / 8
      let totalSize := alignUp rawBytes maxAlign
      pure { isUnion := false, size := totalSize, align := maxAlign, fields := outFields }
end

/-- Build a `LayoutEnv` from all `typedef` and `struct`/`union` declarations in a `TranslationUnit`. -/
def buildLayoutEnv (tu : TranslationUnit) : Except String LayoutEnv := do
  let mut env : LayoutEnv := {}
  for d in tu.decls do
    match d with
    | .typedef nm ty =>
      env := { env with typedefs := env.typedefs.insert nm ty }
    | .structDef sd =>
      let lay ← layoutAggregate env sd.isUnion sd.fields
      if sd.isUnion then
        env := { env with unions := env.unions.insert sd.name lay }
      else
        env := { env with structs := env.structs.insert sd.name lay }
    | _ => pure ()
  pure env

/-- Look up the `AggregateLayout` of a struct/union type. -/
def getAggregateLayout (env : LayoutEnv) (aggTy : C0Type) : Except String AggregateLayout := do
  match ← resolveType env aggTy with
  | .structRef nm =>
    match env.structs.get? nm with
    | some lay => pure lay
    | none => throw s!"unknown struct '{nm}'"
  | .unionRef nm =>
    match env.unions.get? nm with
    | some lay => pure lay
    | none => throw s!"unknown union '{nm}'"
  | .anonAggregate isUnion fields =>
    layoutAggregate env isUnion fields
  | t => throw s!"expected struct or union type, got {repr t}"

/-- Look up a named field inside a struct/union type. -/
def lookupField (env : LayoutEnv) (aggTy : C0Type) (fld : String) : Except String FieldLoc := do
  let lay ← getAggregateLayout env aggTy
  match lay.fields.find? (fun (nm, _) => nm == fld) with
  | some (_, loc) => pure loc
  | none => throw s!"field '{fld}' not found in aggregate {repr aggTy}"

/-- Return the byte offset of a regular field (or `unitByteOff` of a bitfield) for layout testing. -/
def offsetOfField (env : LayoutEnv) (aggTy : C0Type) (fld : String) : Except String Nat := do
  match ← lookupField env aggTy fld with
  | .regular off _ _ => pure off
  | .bitfield unitOff _ _ _ _ => pure unitOff

end LeanQbe.T.Frontend.C0
