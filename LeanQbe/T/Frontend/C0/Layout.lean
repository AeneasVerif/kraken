module

public import LeanQbe.T.Frontend.C0.Syntax
public import Std.Data.HashMap
public import Std.Data.HashSet

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

/-! ## C0 Type Promotion, Expression Typing, and Static AST Analysis -/

def intLitType (v : Int) (suf : IntSuffix) (isDecimal : Bool) : C0Type :=
  match suf with
  | .ull | .ul => .u64
  | .ll | .l => if !isDecimal && v > (2^63 - 1 : Int) then .u64 else .i64
  | .u => if v >= 0 && v < 2^32 then .u32 else .u64
  | .none =>
    if isDecimal then
      if v >= -(2^31 : Int) && v < (2^31 : Int) then .i32
      else if v >= -(2^63 : Int) && v < (2^63 : Int) then .i64
      else .u64
    else
      if v >= -(2^31 : Int) && v < (2^31 : Int) then .i32
      else if v >= 0 && v < (2^32 : Int) then .u32
      else if v >= -(2^63 : Int) && v < (2^63 : Int) then .i64
      else .u64

def intPromote (ty : C0Type) : C0Type :=
  match ty with
  | .bool => .i32
  | .int _ n => if n < 32 then .i32 else ty
  | _ => ty

def usualArithType (t1 t2 : C0Type) : Except String C0Type := do
  if t1 == .f64 || t2 == .f64 then pure .f64
  else
    let p1 := intPromote t1
    let p2 := intPromote t2
    match p1, p2 with
    | .int s1 n1, .int s2 n2 =>
      if s1 == s2 then pure (.int s1 (Nat.max n1 n2))
      else if !s1 && n1 >= n2 then pure p1
      else if !s2 && n2 >= n1 then pure p2
      else if s1 && n1 > n2 then pure p1
      else pure p2
    | _, _ => throw s!"invalid operands for arithmetic conversion: {repr t1}, {repr t2}"

def bitfieldValueType (env : LayoutEnv) (declTy : C0Type) (width : Nat) : Except String C0Type := do
  match ← resolveType env declTy with
  | .bool => pure .bool
  | .int true _ => pure (if width <= 32 then .i32 else .i64)
  | .int false w => if w <= 32 && width < 32 then pure .i32 else pure (.int false w)
  | t => throw s!"unsupported bitfield type {repr t}"

private def isNullPtrConst : Expr → Bool
  | .null | .intLit 0 _ _ => true
  | _ => false

private def isArithType : C0Type → Bool
  | .bool | .int _ _ | .f64 => true
  | _ => false

def condResultType (env : LayoutEnv) (t1 t2 : C0Type) (e1 e2 : Expr) : Except String C0Type := do
  let r1 ← resolveType env t1
  let r2 ← resolveType env t2
  if isArithType r1 && isArithType r2 then
    usualArithType r1 r2
  else
    match r1, r2 with
    | .ptr p1, .ptr p2 => pure (if p1 == .void then .ptr p2 else .ptr p1)
    | .ptr _, _ => if isNullPtrConst e2 then pure r1 else throw s!"incompatible '?:' types {repr r1}, {repr r2}"
    | _, .ptr _ => if isNullPtrConst e1 then pure r2 else throw s!"incompatible '?:' types {repr r1}, {repr r2}"
    | _, _ => if r1 == r2 then pure r1 else throw s!"incompatible '?:' types {repr r1}, {repr r2}"

partial def inferExprType (env : LayoutEnv) (lookupVar : String → Except String C0Type)
    (lookupFnRet : String → Except String C0Type) (e : Expr)
    (decayArray : Bool := true) (forSizeof : Bool := false) : Except String C0Type := do
  let maybeDecay (t : C0Type) : C0Type :=
    if decayArray then match t with | .array elem _ => .ptr elem | _ => t else t
  let fieldRes (agg : C0Type) (fld : String) : Except String C0Type := do
    match ← lookupField env agg fld with
    | .regular _ fty _ => pure (maybeDecay (← resolveType env fty))
    | .bitfield _ _ _ w fty => bitfieldValueType env fty w
  match e with
  | .intLit v suf isDec => pure (intLitType v suf isDec)
  | .floatLit _ => pure .f64
  | .boolLit _ => pure (if forSizeof then .i32 else .bool)
  | .null => pure (.ptr .void)
  | .var nm => lookupVar nm
  | .cast ty _ => resolveType env ty
  | .sizeofTy _ | .sizeofExpr _ => pure .u64
  | .unary .pos sub | .unary .neg sub | .unary .bitnot sub =>
    let t ← inferExprType env lookupVar lookupFnRet sub true forSizeof
    pure (if t == .f64 then .f64 else intPromote t)
  | .unary .lognot _ => pure (if forSizeof then .i32 else .bool)
  | .unary .deref p =>
    match ← resolveType env (← inferExprType env lookupVar lookupFnRet p true forSizeof) with
    | .ptr elem => pure (maybeDecay (← resolveType env elem))
    | t => throw s!"cannot dereference {repr t}"
  | .unary .addrOf sub =>
    pure (.ptr (← inferExprType env lookupVar lookupFnRet sub false forSizeof))
  | .binary op a b =>
    match op with
    | .eq | .ne | .lt | .le | .gt | .ge | .logand | .logor =>
      pure (if forSizeof then .i32 else .bool)
    | .shl | .shr => pure (intPromote (← inferExprType env lookupVar lookupFnRet a true forSizeof))
    | .add =>
      let ta ← resolveType env (← inferExprType env lookupVar lookupFnRet a true forSizeof)
      let tb ← resolveType env (← inferExprType env lookupVar lookupFnRet b true forSizeof)
      match ta, tb with
      | .ptr _, _ => pure ta | _, .ptr _ => pure tb
      | _, _ => usualArithType ta tb
    | .sub =>
      let ta ← resolveType env (← inferExprType env lookupVar lookupFnRet a true forSizeof)
      let tb ← resolveType env (← inferExprType env lookupVar lookupFnRet b true forSizeof)
      match ta, tb with
      | .ptr _, .ptr _ => pure .i64 | .ptr _, _ => pure ta
      | _, _ => usualArithType ta tb
    | _ =>
      let ta ← resolveType env (← inferExprType env lookupVar lookupFnRet a true forSizeof)
      let tb ← resolveType env (← inferExprType env lookupVar lookupFnRet b true forSizeof)
      usualArithType ta tb
  | .ternary _ t f =>
    let tt ← inferExprType env lookupVar lookupFnRet t true forSizeof
    let ft ← inferExprType env lookupVar lookupFnRet f true forSizeof
    condResultType env tt ft t f
  | .field b fld =>
    let tb ← inferExprType env lookupVar lookupFnRet b false forSizeof
    fieldRes tb fld
  | .arrow p fld =>
    match ← resolveType env (← inferExprType env lookupVar lookupFnRet p true forSizeof) with
    | .ptr agg => fieldRes agg fld
    | t => throw s!"'->' on non-pointer {repr t}"
  | .index a _ =>
    match ← resolveType env (← inferExprType env lookupVar lookupFnRet a true forSizeof) with
    | .ptr elem | .array elem _ => pure (maybeDecay (← resolveType env elem))
    | t => throw s!"index on non-pointer {repr t}"
  | .call fn _ =>
    match fn with
    | "c0_rotl32" | "c0_rotr32" | "c0_clz32" | "c0_ctz32" | "c0_popcnt32" => pure .u32
    | "c0_rotl64" | "c0_rotr64" | "c0_clz64" | "c0_ctz64" | "c0_popcnt64"
    | "c0_f64_to_bits" | "c0_f64_to_u64_sat" => pure .u64
    | "c0_bits_to_f64" => pure .f64
    | _ => resolveType env (← lookupFnRet fn)

def setUnion (a b : Std.HashSet String) : Std.HashSet String :=
  b.fold (fun acc x => acc.insert x) a

def lvalMutatedLocal : LVal → Option String
  | .var x => some x
  | .dot b _ => lvalMutatedLocal b
  | _ => none

partial def stmtHasBreak : Stmt → Bool
  | .breakStmt => true
  | .block ss => ss.any stmtHasBreak
  | .ifStmt _ t e? => stmtHasBreak t || (e?.map stmtHasBreak |>.getD false)
  | .labelStmt _ s => stmtHasBreak s
  | _ => false

partial def stmtHasContinue : Stmt → Bool
  | .continueStmt => true
  | .block ss => ss.any stmtHasContinue
  | .ifStmt _ t e? => stmtHasContinue t || (e?.map stmtHasContinue |>.getD false)
  | .switchStmt _ arms => arms.any (fun a => a.body.any stmtHasContinue)
  | .labelStmt _ s => stmtHasContinue s
  | _ => false

partial def stmtHasAnyLabel : Stmt → Bool
  | .labelStmt _ _ => true
  | .block ss => ss.any stmtHasAnyLabel
  | .ifStmt _ t e? => stmtHasAnyLabel t || (e?.map stmtHasAnyLabel |>.getD false)
  | _ => false

partial def stmtHasGoto (lbl : String) : Stmt → Bool
  | .gotoStmt l => l == lbl
  | .block ss => ss.any (stmtHasGoto lbl)
  | .ifStmt _ t e? => stmtHasGoto lbl t || (e?.map (stmtHasGoto lbl) |>.getD false)
  | .whileStmt _ b | .doWhileStmt b _ | .forStmt _ _ _ b => stmtHasGoto lbl b
  | .switchStmt _ arms => arms.any (fun a => a.body.any (stmtHasGoto lbl))
  | .labelStmt _ s => stmtHasGoto lbl s
  | _ => false

private def isConstTrueExpr : Expr → Bool
  | .boolLit true => true
  | .intLit v _ _ => v != 0
  | _ => false

mutual
  partial def stmtBlockFallThrough (ss : List Stmt) : Bool :=
    ss.foldl (fun reach st =>
      match st with
      | .labelStmt _ inner => stmtMayFallThrough inner
      | _ => reach && stmtMayFallThrough st) true

  partial def stmtMayFallThrough : Stmt → Bool
    | .retStmt _ | .breakStmt | .continueStmt | .gotoStmt _ => false
    | .ifStmt _ t (some e) => stmtMayFallThrough t || stmtMayFallThrough e
    | .ifStmt _ _ none => true
    | .whileStmt cond b => !(isConstTrueExpr cond && !stmtHasBreak b)
    | .forStmt _ none _ b => stmtHasBreak b
    | .switchStmt _ arms =>
      if !(arms.any (·.hasDefault)) || arms.any (fun a => a.body.any stmtHasBreak) then true
      else match arms.getLast? with
        | some last => stmtBlockFallThrough last.body
        | none => true
    | .block ss => stmtBlockFallThrough ss
    | .labelStmt _ s => stmtMayFallThrough s
    | _ => true
end

partial def stmtAlwaysExitsLoop (inNestedBreakScope : Bool) : Stmt → Bool
  | .retStmt _ => true
  | .breakStmt => !inNestedBreakScope
  | .ifStmt _ t (some e) => stmtAlwaysExitsLoop inNestedBreakScope t && stmtAlwaysExitsLoop inNestedBreakScope e
  | .labelStmt _ s => stmtAlwaysExitsLoop inNestedBreakScope s
  | .block ss =>
    let rec go : List Stmt → Bool
      | [] => false
      | st :: rest =>
        if stmtAlwaysExitsLoop inNestedBreakScope st && !(rest.any stmtHasAnyLabel) then true
        else go rest
    go ss
  | _ => false

partial def stmtMutatedLocals (onlyBackEdge inNestedBreakScope : Bool) (s : Stmt) :
    Std.HashSet String :=
  if onlyBackEdge && !stmtHasContinue s && stmtAlwaysExitsLoop inNestedBreakScope s then {} else
  match s with
  | .empty | .breakStmt | .continueStmt | .gotoStmt _ | .decl _ _ _
  | .retStmt _ | .assumeStmt _ | .checkStmt _ _ | .assertStmt _ _ => {}
  | .assign lv _ _ | .incDec lv _ =>
    match lvalMutatedLocal lv with | some x => ({} : Std.HashSet String).insert x | none => {}
  | .callStmt lhs _ _ => lhs.foldl (fun acc x => acc.insert x) {}
  | .ifStmt _ t e? =>
    setUnion (stmtMutatedLocals onlyBackEdge inNestedBreakScope t)
      (e?.map (stmtMutatedLocals onlyBackEdge inNestedBreakScope) |>.getD {})
  | .whileStmt _ b | .doWhileStmt b _ => stmtMutatedLocals onlyBackEdge true b
  | .forStmt init? _ step? b =>
    let mi := init?.map (stmtMutatedLocals onlyBackEdge true) |>.getD {}
    let ms := step?.map (stmtMutatedLocals onlyBackEdge true) |>.getD {}
    setUnion mi (setUnion ms (stmtMutatedLocals onlyBackEdge true b))
  | .switchStmt _ arms =>
    arms.foldl (fun acc a =>
      a.body.foldl (fun acc' st => setUnion acc' (stmtMutatedLocals onlyBackEdge true st)) acc) {}
  | .block ss =>
    let rec go (acc : Std.HashSet String) : List Stmt → Std.HashSet String
      | [] => acc
      | st :: rest =>
        let acc' := setUnion acc (stmtMutatedLocals onlyBackEdge inNestedBreakScope st)
        if onlyBackEdge && !stmtHasContinue st && stmtAlwaysExitsLoop inNestedBreakScope st &&
           !(rest.any stmtHasAnyLabel) then acc'
        else go acc' rest
    go {} ss
  | .labelStmt _ st => stmtMutatedLocals onlyBackEdge inNestedBreakScope st

end LeanQbe.T.Frontend.C0
