module

public import LeanQbe.T.Logic.SlabLayout
public meta import Lean.Elab.Command
public meta import Lean.Parser

/-!
# Lawful Lenses (`C0Lens`) & Declarative `c0_slab_layout!` DSL

* `C0Lens`: lawful per-field lenses (`comp`, `modify`, `set_list`) with `AgreesExcept` integration.
* `c0_slab_layout!`: declarative C-compatible slab layout generator emitting `LengthsOk`,
  `totalBytes`, `kindItems`, `flatSegs`, balanced `SepTree` (`Tree`/`At`), `@[c0_load]` /
  `@[c0_store]` accessors, `C0Lens` per field, `to_region`/`to_region_frame`, and
  `of_region`/`of_region_frame`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T

/-- Lawful lens into a C0 state record `σ` focusing field `α`. -/
structure C0Lens (σ α : Type) where
  get : σ → α
  set : σ → α → σ
  get_set : ∀ s v, get (set s v) = v
  set_get : ∀ s, set s (get s) = s
  set_set : ∀ s v w, set (set s v) w = set s w

namespace C0Lens

/-- Apply a pure function to the focused field. -/
@[expose] def modify {σ α : Type} (l : C0Lens σ α) (f : α → α) (s : σ) : σ :=
  l.set s (f (l.get s))

/-- Compose two lenses (`outer` into a sub-record such as `s.core`, `inner` into its field). -/
@[expose] def comp {σ τ α : Type} (outer : C0Lens σ τ) (inner : C0Lens τ α) : C0Lens σ α where
  get s := inner.get (outer.get s)
  set s v := outer.set s (inner.set (outer.get s) v)
  get_set s v := by rw [outer.get_set, inner.get_set]
  set_get s := by rw [inner.set_get, outer.set_get]
  set_set s v w := by rw [outer.get_set, inner.set_set, outer.set_set]

/-- Update element `i` of a list-valued field. -/
@[expose] def set_list {σ α : Type} (l : C0Lens σ (List α)) (s : σ) (i : Nat) (v : α) : σ :=
  l.set s ((l.get s).set i v)

end C0Lens

end LeanQbe.T

end

public section

namespace LeanQbe.T.C0Lens

theorem length_set_list {σ α : Type} (l : C0Lens σ (List α)) (s : σ) (i : Nat) (v : α) :
    (l.get (l.set_list s i v)).length = (l.get s).length := by
  simp only [set_list, l.get_set, List.length_set]

theorem getElem?_set_list_self {σ α : Type} (l : C0Lens σ (List α)) (s : σ) {i : Nat} (v : α)
    (hi : i < (l.get s).length) :
    (l.get (l.set_list s i v))[i]? = some v := by
  simp only [set_list, l.get_set, List.getElem?_set_self hi]

theorem getElem?_set_list_ne {σ α : Type} (l : C0Lens σ (List α)) (s : σ) {i j : Nat} (v : α)
    (hne : i ≠ j) :
    (l.get (l.set_list s i v))[j]? = (l.get s)[j]? := by
  simp only [set_list, l.get_set, List.getElem?_set_ne hne]

/-- Updating a field covered by `mask` satisfies `AgreesExcept mask`. -/
theorem agreesExcept_set {σ α : Type} (l : C0Lens σ α) (mask : σ → σ) (s : σ) (v : α)
    (hm : ∀ t x, mask (l.set t x) = mask t := by intro _ _; rfl) :
    AgreesExcept mask s (l.set s v) :=
  hm s v

/-- Project an unmasked field across `AgreesExcept mask`. -/
theorem get_of_agreesExcept {σ α : Type} (l : C0Lens σ α) {mask : σ → σ} {s s' : σ}
    (h : AgreesExcept mask s s')
    (hm : ∀ t, l.get (mask t) = l.get t := by intro _; rfl) :
    l.get s' = l.get s :=
  h.get l.get hm

end LeanQbe.T.C0Lens

end

/-! ## Declarative `c0_slab_layout!` DSL -/

meta section

namespace LeanQbe.T.SlabLayout

open Lean Lean.Elab.Command

meta inductive SlabSegSpec where
  | cell (elemBytes : Nat)
  | array (elemBytes : Nat) (lenTerm : String) (lenStatic? : Option Nat) (align8 : Bool)
  | bytes (lenTerm : String) (lenStatic? : Option Nat)
  | pad (lenTerm : String) (lenStatic? : Option Nat)

meta structure SlabFieldInfo where
  name : String
  spec : SlabSegSpec

meta structure PlacedSlabSeg where
  name : String
  spec : SlabSegSpec
  offStatic? : Option Nat
  offTerm : String
  isFirst : Bool
  strideStatic? : Option Nat
  strideTerm : String
  path : List Bool

meta def treePathsAux : Nat → Nat → List (List Bool)
  | 0, _ => []
  | _, 0 => []
  | _, 1 => [[]]
  | fuel + 1, n =>
    let mid := n / 2
    (treePathsAux fuel mid).map (false :: ·) ++ (treePathsAux fuel (n - mid)).map (true :: ·)

meta def treePaths (n : Nat) : List (List Bool) :=
  treePathsAux n n

meta def buildBalancedTreeAux : Nat → List String → String
  | 0, _ => "LeanQbe.T.SepTree.leaf Std.ExtHashMap.emp"
  | _, [] => "LeanQbe.T.SepTree.leaf Std.ExtHashMap.emp"
  | _, [x] => s!"(LeanQbe.T.SepTree.leaf ({x}))"
  | fuel + 1, xs =>
    let mid := xs.length / 2
    let l := buildBalancedTreeAux fuel (xs.take mid)
    let r := buildBalancedTreeAux fuel (xs.drop mid)
    s!"(LeanQbe.T.SepTree.node {l} {r})"

meta def buildBalancedTree (leaves : List String) : String :=
  buildBalancedTreeAux leaves.length leaves

meta def parseSlabTyBytes (id : Syntax) : CommandElabM Nat := do
  match id.getId.toString with
  | "i8" | "u8" | "bool" => return 1
  | "i16" | "u16" => return 2
  | "i32" | "u32" => return 4
  | "i64" | "u64" | "ptr" => return 8
  | other =>
    throwErrorAt id
      (s!"c0_slab_layout!: unsupported scalar type '{other}' " ++
       "(expected i8/u8/bool/i16/u16/i32/u32/i64/u64/ptr)")

private meta def termInfo (stx : Syntax) : String × Option Nat :=
  let s := (stx.reprint.getD "").trimAscii.toString
  (s, s.toNat?)

private meta def q (s : String) : String := s!"«{s}»"

private meta def ppPath (p : List Bool) : String :=
  let xs := p.map fun b => if b then "true" else "false"
  "[" ++ ", ".intercalate xs ++ "]"

private meta def placeSegs (fields : List SlabFieldInfo) :
    List PlacedSlabSeg × Option Nat × String :=
  let paths := treePaths fields.length
  let step := fun (acc, curStat?, curTerms) (f, idx) =>
    let isFirst := idx == 0
    let (offStatic?, offTerm) :=
      if isFirst then (some 0, "0")
      else match curStat? with
        | some n => (some n, toString n)
        | none => (none, "(" ++ " + ".intercalate curTerms ++ ")")
    let (strideStatic?, strideTerm) := match f.spec with
      | .cell eb => (some eb, toString eb)
      | .array eb lenTerm lenStat? al8 =>
        match lenStat?, al8 with
        | some k, false => let v := eb * k; (some v, toString v)
        | some k, true => let v := ((eb * k + 7) / 8) * 8; (some v, toString v)
        | none, false => (none, s!"({eb} * ({lenTerm}))")
        | none, true => (none, s!"LeanQbe.T.align8 ({eb} * ({lenTerm}))")
      | .bytes lenTerm lenStat? =>
        match lenStat? with
        | some k => (some k, toString k)
        | none => (none, s!"({lenTerm})")
      | .pad lenTerm lenStat? =>
        match lenStat? with
        | some k => (some k, toString k)
        | none => (none, s!"({lenTerm})")
    let nextStat? := match curStat?, strideStatic? with
      | some a, some b => some (a + b)
      | _, _ => none
    let nextTerms := curTerms ++ [strideTerm]
    let path := paths[idx]!
    let placed : PlacedSlabSeg := {
      name := f.name, spec := f.spec, offStatic?, offTerm, isFirst, strideStatic?,
      strideTerm, path
    }
    (acc ++ [placed], nextStat?, nextTerms)
  let (placed, totStat?, totTerms) :=
    fields.zipIdx.foldl (init := ([], some 0, ([] : List String))) step
  let totTerm := match totStat? with
    | some n => toString n
    | none => if totTerms.isEmpty then "0" else " + ".intercalate totTerms
  (placed, totStat?, totTerm)

private meta def addrExpr (p : PlacedSlabSeg) : String :=
  if p.isFirst then "p"
  else match p.offStatic? with
    | some 0 => "p"
    | some n => s!"(p + {n}#64)"
    | none => s!"(p + BitVec.ofNat 64 {p.offTerm})"

private meta def segIsPad : PlacedSlabSeg → Bool
  | p => match p.spec with | .pad .. => true | _ => false

private meta def segIsLen : PlacedSlabSeg → Bool
  | p => match p.spec with | .array .. | .bytes .. => true | _ => false

private meta def structFieldType : SlabSegSpec → String
  | .cell eb => s!"BitVec {8 * eb}"
  | .array eb _ _ _ => s!"List (BitVec {8 * eb})"
  | .bytes _ _ => "List UInt8"
  | .pad _ _ => "Unit"

private meta def mkStructUpdate (dataFields : List PlacedSlabSeg) (fname rhs : String) : String :=
  if dataFields.length == 1 then s!"\{ {q fname} := {rhs} }"
  else s!"\{ s with {q fname} := {rhs} }"

private meta def usesIdent (s ident : String) : Bool :=
  let tokens := s.splitToList (fun c => !c.isAlphanum && c != '_' && c != '\'')
  tokens.contains ident

private meta def slabCommands (S : String) (params : List (String × String))
    (fields : List SlabFieldInfo) (isModule : Bool) : List String := Id.run do
  let exp := if isModule then "@[expose] " else ""
  let (placed, _totStat?, totTerm) := placeSegs fields
  let dataFields := placed.filter (!segIsPad ·)
  let lenFields := placed.filter segIsLen
  let paramBinders := " ".intercalate (params.map fun (n, ty) => s!"({q n} : {ty})")
  let paramSp := if paramBinders.isEmpty then "" else paramBinders ++ " "
  let implBinders := " ".intercalate (params.map fun (n, ty) => s!"\{{q n} : {ty}}")
  let implSp := if implBinders.isEmpty then "" else implBinders ++ " "
  let paramArgs := " ".intercalate (params.map fun (n, _) => q n)
  let pArgsSp := if paramArgs.isEmpty then "" else " " ++ paramArgs
  let qs := q S
  let memTy := "Std.ExtHashMap (BitVec 64) UInt8"
  let mut cmds : List String := []
  -- 1. State record structure
  let fieldDecls := dataFields.map fun p => s!"  {q p.name} : {structFieldType p.spec}"
  let structBody := if fieldDecls.isEmpty then "" else "\n" ++ "\n".intercalate fieldDecls
  cmds := cmds ++ [s!"structure {qs} where{structBody}"]
  -- 2. LengthsOk structure
  let lenParamBinders := " ".intercalate (params.map fun (n, ty) =>
    let used := lenFields.any fun p => match p.spec with
      | .array _ lt _ _ | .bytes lt _ => usesIdent lt n
      | _ => false
    if used then s!"({q n} : {ty})" else s!"(_ : {ty})")
  let lenParamSp := if lenParamBinders.isEmpty then "" else lenParamBinders ++ " "
  let sBinder := if lenFields.isEmpty then s!"(_ : {qs})" else s!"(s : {qs})"
  let lenDecls := lenFields.map fun p => match p.spec with
    | .array _ lt _ _ | .bytes lt _ =>
      s!"  {q (p.name ++ "_len")} : s.{q p.name}.length = ({lt})"
    | _ => ""
  let lenBody := if lenDecls.isEmpty then "" else "\n" ++ "\n".intercalate lenDecls
  cmds := cmds ++ [s!"structure {qs}.LengthsOk {lenParamSp}{sBinder} : Prop where{lenBody}"]
  -- 3. totalBytes
  let totParamBinders := " ".intercalate (params.map fun (n, ty) =>
    if usesIdent totTerm n then s!"({q n} : {ty})" else s!"(_ : {ty})")
  let totParamSp := if totParamBinders.isEmpty then "" else totParamBinders ++ " "
  cmds := cmds ++ [s!"{exp}def {qs}.totalBytes {totParamSp}: Nat := {totTerm}"]
  -- 4. kindItems
  let kindParamBinders := " ".intercalate (params.map fun (n, ty) =>
    let used := placed.any fun p =>
      usesIdent p.offTerm n || usesIdent p.strideTerm n ||
      match p.spec with
      | .array _ lt _ _ | .bytes lt _ | .pad lt _ => usesIdent lt n
      | .cell _ => false
    if used then s!"({q n} : {ty})" else s!"(_ : {ty})")
  let kindParamSp := if kindParamBinders.isEmpty then "" else kindParamBinders ++ " "
  let kindElems := placed.map fun p =>
    let offTag := if p.isFirst then "none" else s!"some {p.offTerm}"
    let kindStr := match p.spec with
      | .cell eb => s!"LeanQbe.T.SlabSegKind.cell {eb}"
      | .array eb lt _ false => s!"LeanQbe.T.SlabSegKind.array {eb} ({lt})"
      | .array eb lt _ true =>
        s!"LeanQbe.T.SlabSegKind.arrayPad {eb} ({lt}) " ++
          s!"(LeanQbe.T.align8 ({eb} * ({lt}))) (LeanQbe.T.align8_ge _)"
      | .bytes lt _ => s!"LeanQbe.T.SlabSegKind.bytes ({lt})"
      | .pad lt _ => s!"LeanQbe.T.SlabSegKind.pad ({lt})"
    s!"({offTag}, {kindStr})"
  let kindList := "[" ++ ", ".intercalate kindElems ++ "]"
  cmds := cmds ++ [
    s!"{exp}def {qs}.kindItems {kindParamSp}: " ++
      s!"List (Option Nat × LeanQbe.T.SlabSegKind) := {kindList}"
  ]
  -- 5. flatSegItems & segs
  let itemParamBinders := " ".intercalate (params.map fun (n, ty) =>
    let used := placed.any fun p =>
      usesIdent p.offTerm n || usesIdent p.strideTerm n ||
      match p.spec with
      | .array _ lt _ _ | .bytes lt _ | .pad lt _ => usesIdent lt n
      | .cell _ => false
    if used then s!"({q n} : {ty})" else s!"(_ : {ty})")
  let itemParamSp := if itemParamBinders.isEmpty then "" else itemParamBinders ++ " "
  let flatSegElems := placed.map fun p =>
    let offTag := if p.isFirst then "none" else s!"some {p.offTerm}"
    let segStr := match p.spec with
      | .cell eb => s!"LeanQbe.T.SlabSeg.ofCell (.bits {8 * eb}) s.{q p.name}"
      | .array eb lt _ false =>
        s!"LeanQbe.T.SlabSeg.ofArrayExact (.bits {8 * eb}) s.{q p.name} ({eb} * ({lt})) " ++
          s!"(by rw [hlen.{q (p.name ++ "_len")}]; " ++
          "dsimp [LeanQbe.T.Ty.bytes, LeanQbe.T.Ty.size]; try omega)"
      | .array eb lt _ true =>
        s!"LeanQbe.T.SlabSeg.ofArrayAlign8 (.bits {8 * eb}) s.{q p.name} ({eb} * ({lt})) " ++
          s!"(by rw [hlen.{q (p.name ++ "_len")}]; " ++
          "dsimp [LeanQbe.T.Ty.bytes, LeanQbe.T.Ty.size]; try omega)"
      | .bytes lt _ =>
        s!"LeanQbe.T.SlabSeg.ofBytes s.{q p.name} ({lt}) hlen.{q (p.name ++ "_len")}"
      | .pad lt _ => s!"LeanQbe.T.SlabSeg.ofRegion ({lt})"
    s!"({offTag}, {segStr})"
  let segItemsBody := "[" ++ ", ".intercalate flatSegElems ++ "]"
  let segsSBinder :=
    if dataFields.isEmpty && lenFields.isEmpty then s!"(_ : {qs})" else s!"(s : {qs})"
  let segsHBinder :=
    if lenFields.isEmpty then s!"(_ : {qs}.LengthsOk{pArgsSp} s)"
    else s!"(hlen : {qs}.LengthsOk{pArgsSp} s)"
  cmds := cmds ++ [
    s!"{exp}def {qs}.flatSegs {itemParamSp}{segsSBinder} {segsHBinder} : " ++
      s!"List (Option Nat × LeanQbe.T.SlabSeg) := {segItemsBody}",
    s!"{exp}def {qs}.segs {itemParamSp}(s : {qs}) (hlen : {qs}.LengthsOk{pArgsSp} s) : " ++
      s!"List LeanQbe.T.SlabSeg := ({qs}.flatSegs{pArgsSp} s hlen).map Prod.snd"
  ]
  -- 6. Balanced SepTree & At + At_eq
  let treeLeaves := placed.map fun p =>
    let a := addrExpr p
    match p.spec with
    | .cell eb => s!"LeanQbe.T.cell (t := .bits {8 * eb}) {a} s.{q p.name}"
    | .array eb _ _ false => s!"LeanQbe.T.array (t := .bits {8 * eb}) {a} s.{q p.name}"
    | .array eb lt _ true =>
      s!"LeanQbe.T.array (t := .bits {8 * eb}) {a} s.{q p.name} ⋆ " ++
        s!"LeanQbe.T.region ({a} + BitVec.ofNat 64 ({eb} * ({lt}))) " ++
        s!"(LeanQbe.T.align8 ({eb} * ({lt})) - {eb} * ({lt}))"
    | .bytes _ _ => s!"LeanQbe.T.bytes {a} s.{q p.name}"
    | .pad lt _ => s!"LeanQbe.T.region {a} ({lt})"
  let treeBody := buildBalancedTree treeLeaves
  let treeParamBinders := " ".intercalate (params.map fun (n, ty) =>
    if usesIdent treeBody n then s!"({q n} : {ty})" else s!"(_ : {ty})")
  let treeParamSp := if treeParamBinders.isEmpty then "" else treeParamBinders ++ " "
  let treeSBinder := if dataFields.isEmpty then s!"(_ : {qs})" else s!"(s : {qs})"
  cmds := cmds ++ [
    s!"{exp}def {qs}.Tree {treeParamSp}(p : BitVec 64) {treeSBinder} : " ++
      s!"LeanQbe.T.SepTree := {treeBody}",
    s!"{exp}def {qs}.At {paramSp}(p : BitVec 64) (s : {qs}) : " ++
      s!"{memTy} → Prop := ({qs}.Tree{pArgsSp} p s).eval",
    s!"theorem {qs}.At_eq {paramSp}(p : BitVec 64) (s : {qs}) : " ++
      s!"{qs}.At{pArgsSp} p s = ({qs}.Tree{pArgsSp} p s).eval := rfl"
  ]
  -- 7. focus / unfocus, load / store, LengthsOk_set, lens per data field
  let lenOkCopy :=
    if lenFields.isEmpty then "⟨⟩"
    else
      let assigns := lenFields.map fun lp =>
        s!"{q (lp.name ++ "_len")} := hlen.{q (lp.name ++ "_len")}"
      "{" ++ ", ".intercalate assigns ++ "}"
  let lenOkHyp :=
    if lenFields.isEmpty then s!"(_ : {qs}.LengthsOk{pArgsSp} s)"
    else s!"(hlen : {qs}.LengthsOk{pArgsSp} s)"
  for p in dataFields do
    let a := addrExpr p
    let pathS := ppPath p.path
    let fName := p.name
    let qf := q fName
    match p.spec with
    | .cell eb =>
      let bits := 8 * eb
      let upd := mkStructUpdate dataFields fName "v"
      let leaf := s!"LeanQbe.T.cell (t := .bits {bits}) {a} s.{qf}"
      let leafV := s!"LeanQbe.T.cell (t := .bits {bits}) {a} v"
      let ctxHyps := s!"{implSp}\{p : BitVec 64} \{s : {qs}} \{R : {memTy} → Prop} \{m : {memTy}}"
      cmds := cmds ++ [
        s!"theorem {qs}.{q ("focus_" ++ fName)} {ctxHyps} " ++
          s!"(hm : ({qs}.At{pArgsSp} p s ⋆ R) m) : " ++
          s!"({leaf} ⋆ (({qs}.Tree{pArgsSp} p s).rest {pathS} ⋆ R)) m := by " ++
          s!"rw [{qs}.At_eq] at hm; exact LeanQbe.T.SepTree.focus {pathS} hm",
        s!"theorem {qs}.{q ("unfocus_" ++ fName)} {implSp}\{p : BitVec 64} \{s : {qs}} " ++
          s!"(v : BitVec {bits}) \{R : {memTy} → Prop} \{m : {memTy}} " ++
          s!"(hm : ({leafV} ⋆ (({qs}.Tree{pArgsSp} p s).rest {pathS} ⋆ R)) m) : " ++
          s!"({qs}.At{pArgsSp} p {upd} ⋆ R) m := by " ++
          s!"rw [{qs}.At_eq]; exact LeanQbe.T.SepTree.unfocus_eq {pathS} rfl hm",
        s!"@[c0_load] theorem {qs}.{q ("load_" ++ fName)} {ctxHyps} " ++
          s!"(hm : ({qs}.At{pArgsSp} p s ⋆ R) m) : " ++
          s!"LeanQbe.T.loadVal m (.bits {bits}) {a} = some s.{qf} := by " ++
          s!"rw [{qs}.At_eq] at hm; " ++
          s!"exact LeanQbe.T.sepTree_cell_get (t := {qs}.Tree{pArgsSp} p s) " ++
          s!"(p := {pathS}) rfl (by decide) hm",
        s!"@[c0_store] theorem {qs}.{q ("store_" ++ fName)} {ctxHyps} (v : BitVec {bits}) " ++
          s!"(hm : ({qs}.At{pArgsSp} p s ⋆ R) m) : " ++
          s!"LeanQbe.T.storeOk m (.bits {bits}) {a} ∧ " ++
          s!"({qs}.At{pArgsSp} p {upd} ⋆ R) (LeanQbe.T.storeMem m (.bits {bits}) {a} v) := by " ++
          s!"rw [{qs}.At_eq] at hm ⊢; " ++
          s!"exact LeanQbe.T.sepTree_cell_put (t := {qs}.Tree{pArgsSp} p s) " ++
          s!"(p := {pathS}) (M' := ({qs}.Tree{pArgsSp} p {upd}).eval) v rfl (by decide) " ++
          s!"(by dsimp only [{qs}.Tree, LeanQbe.T.SepTree.set]; try rfl) hm",
        s!"theorem {qs}.{q ("LengthsOk_set_" ++ fName)} {implSp}\{s : {qs}} {lenOkHyp} " ++
          s!"(v : BitVec {bits}) : {qs}.LengthsOk{pArgsSp} {upd} := {lenOkCopy}"
      ]
      match p.isFirst, p.offStatic? with
      | false, some n =>
        if n > 0 then
          let aOfNat := s!"(p + {n})"
          cmds := cmds ++ [
            s!"@[c0_load] theorem {qs}.{q ("load_" ++ fName ++ "_ofNat")} {ctxHyps} " ++
              s!"(hm : ({qs}.At{pArgsSp} p s ⋆ R) m) : " ++
              s!"LeanQbe.T.loadVal m (.bits {bits}) {aOfNat} = some s.{qf} := " ++
              s!"{qs}.{q ("load_" ++ fName)} hm",
            s!"@[c0_store] theorem {qs}.{q ("store_" ++ fName ++ "_ofNat")} {ctxHyps} " ++
              s!"(v : BitVec {bits}) (hm : ({qs}.At{pArgsSp} p s ⋆ R) m) : " ++
              s!"LeanQbe.T.storeOk m (.bits {bits}) {aOfNat} ∧ " ++
              s!"({qs}.At{pArgsSp} p {upd} ⋆ R) " ++
              s!"(LeanQbe.T.storeMem m (.bits {bits}) {aOfNat} v) := " ++
              s!"{qs}.{q ("store_" ++ fName)} v hm"
          ]
      | _, _ => pure ()
    | .array eb lt _ al8 =>
      let bits := 8 * eb
      let updSet := mkStructUpdate dataFields fName s!"(s.{qf}.set i v)"
      let updSetBv := mkStructUpdate dataFields fName s!"(s.{qf}.set i.toNat v)"
      let updWhole := mkStructUpdate dataFields fName "xs'"
      let qLen := q (fName ++ "_len")
      let (getNatThm, putNatThm, getBvThm, putBvThm) :=
        if al8 then
          ("sepTree_arr_pad_get", "sepTree_arr_pad_put",
           "sepTree_arr_pad_get_bv_at", "sepTree_arr_pad_put_bv_at")
        else
          ("sepTree_arr_get", "sepTree_arr_put",
           "sepTree_arr_get_bv_at", "sepTree_arr_put_bv_at")
      let (leaf, leafUpdWhole) :=
        if al8 then
          let tail :=
            s!"LeanQbe.T.region ({a} + BitVec.ofNat 64 ({eb} * ({lt}))) " ++
            s!"(LeanQbe.T.align8 ({eb} * ({lt})) - {eb} * ({lt}))"
          (s!"(LeanQbe.T.array (t := .bits {bits}) {a} s.{qf} ⋆ {tail})",
           s!"(LeanQbe.T.array (t := .bits {bits}) {a} xs' ⋆ {tail})")
        else
          (s!"LeanQbe.T.array (t := .bits {bits}) {a} s.{qf}",
           s!"LeanQbe.T.array (t := .bits {bits}) {a} xs'")
      let elemAddrNat :=
        if eb == 1 then s!"({a} + BitVec.ofNat 64 i)"
        else s!"({a} + BitVec.ofNat 64 ({eb} * i))"
      let getCall :=
        s!"LeanQbe.T.{getNatThm} (t := {qs}.Tree{pArgsSp} p s) (p := {pathS}) " ++
        "rfl (by decide) hi hm"
      let putCall :=
        s!"LeanQbe.T.{putNatThm} (t := {qs}.Tree{pArgsSp} p s) (p := {pathS}) " ++
        s!"(M' := ({qs}.Tree{pArgsSp} p {updSet}).eval) rfl (by decide) v hi rfl hm"
      let ctxHyps := s!"{implSp}\{p : BitVec 64} \{s : {qs}} \{R : {memTy} → Prop} \{m : {memTy}}"
      cmds := cmds ++ [
        s!"theorem {qs}.{q ("focus_" ++ fName)} {ctxHyps} " ++
          s!"(hm : ({qs}.At{pArgsSp} p s ⋆ R) m) : " ++
          s!"({leaf} ⋆ (({qs}.Tree{pArgsSp} p s).rest {pathS} ⋆ R)) m := by " ++
          s!"rw [{qs}.At_eq] at hm; exact LeanQbe.T.SepTree.focus {pathS} hm",
        s!"theorem {qs}.{q ("unfocus_" ++ fName)} {implSp}\{p : BitVec 64} \{s : {qs}} " ++
          s!"(xs' : List (BitVec {bits})) \{R : {memTy} → Prop} \{m : {memTy}} " ++
          s!"(hm : ({leafUpdWhole} ⋆ (({qs}.Tree{pArgsSp} p s).rest {pathS} ⋆ R)) m) : " ++
          s!"({qs}.At{pArgsSp} p {updWhole} ⋆ R) m := by " ++
          s!"rw [{qs}.At_eq]; exact LeanQbe.T.SepTree.unfocus_eq {pathS} rfl hm",
        s!"@[c0_load] theorem {qs}.{q ("load_" ++ fName)} {ctxHyps} (i : Nat) " ++
          s!"(hi : i < s.{qf}.length) (hm : ({qs}.At{pArgsSp} p s ⋆ R) m) : " ++
          s!"LeanQbe.T.loadVal m (.bits {bits}) {elemAddrNat} = some s.{qf}[i] := by " ++
          s!"rw [{qs}.At_eq] at hm; have h := {getCall}; " ++
          "try simp only [LeanQbe.T.Ty.bytes, LeanQbe.T.Ty.size] at h; exact h",
        s!"@[c0_store] theorem {qs}.{q ("store_" ++ fName)} {ctxHyps} (i : Nat) " ++
          s!"(v : BitVec {bits}) (hi : i < s.{qf}.length) " ++
          s!"(hm : ({qs}.At{pArgsSp} p s ⋆ R) m) : " ++
          s!"LeanQbe.T.storeOk m (.bits {bits}) {elemAddrNat} ∧ " ++
          s!"({qs}.At{pArgsSp} p {updSet} ⋆ R) " ++
          s!"(LeanQbe.T.storeMem m (.bits {bits}) {elemAddrNat} v) := by " ++
          s!"rw [{qs}.At_eq] at hm ⊢; have h := {putCall}; " ++
          "try simp only [LeanQbe.T.Ty.bytes, LeanQbe.T.Ty.size] at h; exact h",
        s!"theorem {qs}.{q ("LengthsOk_set_" ++ fName)} {implSp}\{s : {qs}} " ++
          s!"(hlen : {qs}.LengthsOk{pArgsSp} s) (i : Nat) (v : BitVec {bits}) : " ++
          s!"{qs}.LengthsOk{pArgsSp} {updSet} := " ++
          s!"\{ hlen with {qLen} := by rw [List.length_set]; exact hlen.{qLen} }"
      ]
      -- BV64 C0-aligned patterns
      if eb == 1 then
        let (getBv, putBv) :=
          if al8 then ("sepTree_arr_pad_get_byte", "sepTree_arr_pad_put_byte")
          else ("sepTree_arr_get_byte", "sepTree_arr_put_byte")
        let (getU32, putU32) :=
          if al8 then ("sepTree_arr_pad_get_byte_u32", "sepTree_arr_pad_put_byte_u32")
          else ("sepTree_arr_get_byte_u32", "sepTree_arr_put_byte_u32")
        let (addrBv, addrU32, offParam, hoffHyp, hoffSub) := match p.isFirst, p.offStatic? with
          | true, _ => ("(p + i)", "(p + BitVec.setWidth 64 i)", "", "", "")
          | false, some n =>
            if n == 0 then ("(p + i)", "(p + BitVec.setWidth 64 i)", "", "", "")
            else
              ("((p + off) + i)", "((p + off) + BitVec.setWidth 64 i)",
               "{off : BitVec 64} ", s!"(hoff : off = {n}#64) ", "subst hoff; ")
          | false, none => (s!"({a} + i)", s!"({a} + BitVec.setWidth 64 i)", "", "", "")
        let hoffArg := if hoffHyp.isEmpty then "" else "hoff "
        let bvHyps := s!"{implSp}\{p : BitVec 64} {offParam}\{s : {qs}} " ++
          s!"\{R : {memTy} → Prop} \{m : {memTy}}"
        cmds := cmds ++ [
          s!"@[c0_load] theorem {qs}.{q ("load_" ++ fName ++ "_bv")} {bvHyps} {hoffHyp}" ++
            s!"(i : BitVec 64) (hi : i.toNat < s.{qf}.length) " ++
            s!"(hm : ({qs}.At{pArgsSp} p s ⋆ R) m) : " ++
            s!"LeanQbe.T.loadVal m (.bits 8) {addrBv} = some s.{qf}[i.toNat] := by " ++
            s!"{hoffSub}rw [{qs}.At_eq] at hm; exact LeanQbe.T.{getBv} " ++
            s!"(t := {qs}.Tree{pArgsSp} p s) (p := {pathS}) rfl hi hm",
          s!"@[c0_load] theorem {qs}.{q ("load_" ++ fName ++ "_bv_ok")} {bvHyps} " ++
            s!"(hlen : {qs}.LengthsOk{pArgsSp} s) {hoffHyp}(i : BitVec 64) " ++
            s!"(hi : i.toNat < ({lt})) (hm : ({qs}.At{pArgsSp} p s ⋆ R) m) : " ++
            s!"LeanQbe.T.loadVal m (.bits 8) {addrBv} = " ++
            s!"some (s.{qf}[i.toNat]'(by rw [hlen.{qLen}]; exact hi)) := " ++
            s!"{qs}.{q ("load_" ++ fName ++ "_bv")} {hoffArg}i " ++
            s!"(by rw [hlen.{qLen}]; exact hi) hm",
          s!"@[c0_load] theorem {qs}.{q ("load_" ++ fName ++ "_u32_ok")} {bvHyps} " ++
            s!"(hlen : {qs}.LengthsOk{pArgsSp} s) {hoffHyp}(i : BitVec 32) " ++
            s!"(hi : i.toNat < ({lt})) (hm : ({qs}.At{pArgsSp} p s ⋆ R) m) : " ++
            s!"LeanQbe.T.loadVal m (.bits 8) {addrU32} = " ++
            s!"some (s.{qf}[i.toNat]'(by rw [hlen.{qLen}]; exact hi)) := by " ++
            s!"{hoffSub}rw [{qs}.At_eq] at hm; exact LeanQbe.T.{getU32} " ++
            s!"(t := {qs}.Tree{pArgsSp} p s) (p := {pathS}) rfl " ++
            s!"(by rw [hlen.{qLen}]; exact hi) hm",
          s!"@[c0_store] theorem {qs}.{q ("store_" ++ fName ++ "_bv")} {bvHyps} {hoffHyp}" ++
            s!"(i : BitVec 64) (v : BitVec 8) (hi : i.toNat < s.{qf}.length) " ++
            s!"(hm : ({qs}.At{pArgsSp} p s ⋆ R) m) : " ++
            s!"LeanQbe.T.storeOk m (.bits 8) {addrBv} ∧ " ++
            s!"({qs}.At{pArgsSp} p {updSetBv} ⋆ R) " ++
            s!"(LeanQbe.T.storeMem m (.bits 8) {addrBv} v) := by " ++
            s!"{hoffSub}rw [{qs}.At_eq] at hm ⊢; exact LeanQbe.T.{putBv} " ++
            s!"(t := {qs}.Tree{pArgsSp} p s) (p := {pathS}) rfl v hi rfl hm",
          s!"@[c0_store] theorem {qs}.{q ("store_" ++ fName ++ "_bv_ok")} {bvHyps} " ++
            s!"(hlen : {qs}.LengthsOk{pArgsSp} s) {hoffHyp}(i : BitVec 64) (v : BitVec 8) " ++
            s!"(hi : i.toNat < ({lt})) (hm : ({qs}.At{pArgsSp} p s ⋆ R) m) : " ++
            s!"LeanQbe.T.storeOk m (.bits 8) {addrBv} ∧ " ++
            s!"({qs}.At{pArgsSp} p {updSetBv} ⋆ R) " ++
            s!"(LeanQbe.T.storeMem m (.bits 8) {addrBv} v) := " ++
            s!"{qs}.{q ("store_" ++ fName ++ "_bv")} {hoffArg}i v " ++
            s!"(by rw [hlen.{qLen}]; exact hi) hm",
          s!"@[c0_store] theorem {qs}.{q ("store_" ++ fName ++ "_u32_ok")} {bvHyps} " ++
            s!"(hlen : {qs}.LengthsOk{pArgsSp} s) {hoffHyp}(i : BitVec 32) (v : BitVec 8) " ++
            s!"(hi : i.toNat < ({lt})) (hm : ({qs}.At{pArgsSp} p s ⋆ R) m) : " ++
            s!"LeanQbe.T.storeOk m (.bits 8) {addrU32} ∧ " ++
            s!"({qs}.At{pArgsSp} p {updSetBv} ⋆ R) " ++
            s!"(LeanQbe.T.storeMem m (.bits 8) {addrU32} v) := by " ++
            s!"{hoffSub}rw [{qs}.At_eq] at hm ⊢; exact LeanQbe.T.{putU32} " ++
            s!"(t := {qs}.Tree{pArgsSp} p s) (p := {pathS}) rfl v " ++
            s!"(by rw [hlen.{qLen}]; exact hi) rfl hm"
        ]
      else
        let (addrBv, addrU32, offParam, hoffHyp, hoffSub) := match p.isFirst, p.offStatic? with
          | true, _ => ("(p + i * w)", "(p + BitVec.setWidth 64 i * w)", "", "", "")
          | false, some n =>
            if n == 0 then ("(p + i * w)", "(p + BitVec.setWidth 64 i * w)", "", "", "")
            else
              ("((p + off) + i * w)", "((p + off) + BitVec.setWidth 64 i * w)",
               "{off : BitVec 64} ", s!"(hoff : off = {n}#64) ", "subst hoff; ")
          | false, none =>
            (s!"({a} + i * w)", s!"({a} + BitVec.setWidth 64 i * w)", "", "", "")
        let hwHyp := s!"(hw : w = {eb}#64)"
        let hoffArg := if hoffHyp.isEmpty then "" else "hoff "
        let bvHyps := s!"{implSp}\{p : BitVec 64} {offParam}\{w : BitVec 64} \{s : {qs}} " ++
          s!"\{R : {memTy} → Prop} \{m : {memTy}}"
        cmds := cmds ++ [
          s!"@[c0_load] theorem {qs}.{q ("load_" ++ fName ++ "_bv")} {bvHyps} " ++
            s!"{hoffHyp}{hwHyp} (i : BitVec 64) (hi : i.toNat < s.{qf}.length) " ++
            s!"(hm : ({qs}.At{pArgsSp} p s ⋆ R) m) : " ++
            s!"LeanQbe.T.loadVal m (.bits {bits}) {addrBv} = some s.{qf}[i.toNat] := by " ++
            s!"{hoffSub}rw [{qs}.At_eq] at hm; exact LeanQbe.T.{getBvThm} " ++
            s!"(t := {qs}.Tree{pArgsSp} p s) (p := {pathS}) rfl (by decide) " ++
            "(by rw [hw]; rfl) hi hm",
          s!"@[c0_load] theorem {qs}.{q ("load_" ++ fName ++ "_bv_ok")} {bvHyps} " ++
            s!"(hlen : {qs}.LengthsOk{pArgsSp} s) {hoffHyp}{hwHyp} (i : BitVec 64) " ++
            s!"(hi : i.toNat < ({lt})) (hm : ({qs}.At{pArgsSp} p s ⋆ R) m) : " ++
            s!"LeanQbe.T.loadVal m (.bits {bits}) {addrBv} = " ++
            s!"some (s.{qf}[i.toNat]'(by rw [hlen.{qLen}]; exact hi)) := " ++
            s!"{qs}.{q ("load_" ++ fName ++ "_bv")} {hoffArg}hw i " ++
            s!"(by rw [hlen.{qLen}]; exact hi) hm",
          s!"@[c0_load] theorem {qs}.{q ("load_" ++ fName ++ "_u32_ok")} {bvHyps} " ++
            s!"(hlen : {qs}.LengthsOk{pArgsSp} s) {hoffHyp}{hwHyp} (i : BitVec 32) " ++
            s!"(hi : i.toNat < ({lt})) (hm : ({qs}.At{pArgsSp} p s ⋆ R) m) : " ++
            s!"LeanQbe.T.loadVal m (.bits {bits}) {addrU32} = " ++
            s!"some (s.{qf}[i.toNat]'(by rw [hlen.{qLen}]; exact hi)) := by " ++
            s!"have h := {qs}.{q ("load_" ++ fName ++ "_bv_ok")} hlen {hoffArg}hw " ++
            "(BitVec.setWidth 64 i) " ++
            "(by rw [LeanQbe.T.sepTree_toNat_setWidth64]; exact hi) hm; " ++
            "simpa only [LeanQbe.T.sepTree_toNat_setWidth64] using h",
          s!"@[c0_store] theorem {qs}.{q ("store_" ++ fName ++ "_bv")} {bvHyps} " ++
            s!"{hoffHyp}{hwHyp} (i : BitVec 64) (v : BitVec {bits}) " ++
            s!"(hi : i.toNat < s.{qf}.length) (hm : ({qs}.At{pArgsSp} p s ⋆ R) m) : " ++
            s!"LeanQbe.T.storeOk m (.bits {bits}) {addrBv} ∧ " ++
            s!"({qs}.At{pArgsSp} p {updSetBv} ⋆ R) " ++
            s!"(LeanQbe.T.storeMem m (.bits {bits}) {addrBv} v) := by " ++
            s!"{hoffSub}rw [{qs}.At_eq] at hm ⊢; exact LeanQbe.T.{putBvThm} " ++
            s!"(t := {qs}.Tree{pArgsSp} p s) (p := {pathS}) rfl (by decide) " ++
            "(by rw [hw]; rfl) v hi rfl hm",
          s!"@[c0_store] theorem {qs}.{q ("store_" ++ fName ++ "_bv_ok")} {bvHyps} " ++
            s!"(hlen : {qs}.LengthsOk{pArgsSp} s) {hoffHyp}{hwHyp} (i : BitVec 64) " ++
            s!"(v : BitVec {bits}) (hi : i.toNat < ({lt})) " ++
            s!"(hm : ({qs}.At{pArgsSp} p s ⋆ R) m) : " ++
            s!"LeanQbe.T.storeOk m (.bits {bits}) {addrBv} ∧ " ++
            s!"({qs}.At{pArgsSp} p {updSetBv} ⋆ R) " ++
            s!"(LeanQbe.T.storeMem m (.bits {bits}) {addrBv} v) := " ++
            s!"{qs}.{q ("store_" ++ fName ++ "_bv")} {hoffArg}hw i v " ++
            s!"(by rw [hlen.{qLen}]; exact hi) hm",
          s!"@[c0_store] theorem {qs}.{q ("store_" ++ fName ++ "_u32_ok")} {bvHyps} " ++
            s!"(hlen : {qs}.LengthsOk{pArgsSp} s) {hoffHyp}{hwHyp} (i : BitVec 32) " ++
            s!"(v : BitVec {bits}) (hi : i.toNat < ({lt})) " ++
            s!"(hm : ({qs}.At{pArgsSp} p s ⋆ R) m) : " ++
            s!"LeanQbe.T.storeOk m (.bits {bits}) {addrU32} ∧ " ++
            s!"({qs}.At{pArgsSp} p {updSetBv} ⋆ R) " ++
            s!"(LeanQbe.T.storeMem m (.bits {bits}) {addrU32} v) := by " ++
            s!"have h := {qs}.{q ("store_" ++ fName ++ "_bv_ok")} hlen {hoffArg}hw " ++
            "(BitVec.setWidth 64 i) v " ++
            "(by rw [LeanQbe.T.sepTree_toNat_setWidth64]; exact hi) hm; " ++
            "simpa only [LeanQbe.T.sepTree_toNat_setWidth64] using h"
        ]
    | .bytes lt _ =>
      let updWhole := mkStructUpdate dataFields fName "bs'"
      let leaf := s!"LeanQbe.T.bytes {a} s.{qf}"
      let leafV := s!"LeanQbe.T.bytes {a} bs'"
      let qLen := q (fName ++ "_len")
      let ctxHyps := s!"{implSp}\{p : BitVec 64} \{s : {qs}} \{R : {memTy} → Prop} \{m : {memTy}}"
      cmds := cmds ++ [
        s!"theorem {qs}.{q ("focus_" ++ fName)} {ctxHyps} " ++
          s!"(hm : ({qs}.At{pArgsSp} p s ⋆ R) m) : " ++
          s!"({leaf} ⋆ (({qs}.Tree{pArgsSp} p s).rest {pathS} ⋆ R)) m := by " ++
          s!"rw [{qs}.At_eq] at hm; exact LeanQbe.T.SepTree.focus {pathS} hm",
        s!"theorem {qs}.{q ("unfocus_" ++ fName)} {implSp}\{p : BitVec 64} \{s : {qs}} " ++
          s!"(bs' : List UInt8) \{R : {memTy} → Prop} \{m : {memTy}} " ++
          s!"(hm : ({leafV} ⋆ (({qs}.Tree{pArgsSp} p s).rest {pathS} ⋆ R)) m) : " ++
          s!"({qs}.At{pArgsSp} p {updWhole} ⋆ R) m := by " ++
          s!"rw [{qs}.At_eq]; exact LeanQbe.T.SepTree.unfocus_eq {pathS} rfl hm",
        s!"@[c0_load] theorem {qs}.{q ("load_" ++ fName)} {ctxHyps} (i : Nat) " ++
          s!"(hi : i < s.{qf}.length) (hb : s.{qf}.length ≤ 2 ^ 64) " ++
          s!"(hm : ({qs}.At{pArgsSp} p s ⋆ R) m) : " ++
          s!"LeanQbe.T.loadVal m LeanQbe.T.i8 ({a} + BitVec.ofNat 64 i) = " ++
          s!"some (BitVec.ofNat 8 s.{qf}[i].toNat) := by " ++
          s!"rw [{qs}.At_eq] at hm; exact LeanQbe.T.sepTree_bytes_get " ++
          s!"(t := {qs}.Tree{pArgsSp} p s) (p := {pathS}) rfl hi hb hm",
        s!"@[c0_load] theorem {qs}.{q ("load_" ++ fName ++ "_ok")} {ctxHyps} " ++
          s!"(hlen : {qs}.LengthsOk{pArgsSp} s) (i : Nat) (hi : i < ({lt})) " ++
          s!"(hb : ({lt}) ≤ 2 ^ 64) (hm : ({qs}.At{pArgsSp} p s ⋆ R) m) : " ++
          s!"LeanQbe.T.loadVal m LeanQbe.T.i8 ({a} + BitVec.ofNat 64 i) = " ++
          s!"some (BitVec.ofNat 8 (s.{qf}[i]'(by rw [hlen.{qLen}]; exact hi)).toNat) := " ++
          s!"{qs}.{q ("load_" ++ fName)} i (by rw [hlen.{qLen}]; exact hi) " ++
          s!"(by rw [hlen.{qLen}]; exact hb) hm",
        s!"@[c0_load] theorem {qs}.{q ("load_" ++ fName ++ "_bv")} {ctxHyps} (i : BitVec 64) " ++
          s!"(hi : i.toNat < s.{qf}.length) (hb : s.{qf}.length ≤ 2 ^ 64) " ++
          s!"(hm : ({qs}.At{pArgsSp} p s ⋆ R) m) : " ++
          s!"LeanQbe.T.loadVal m LeanQbe.T.i8 ({a} + i) = " ++
          s!"some (BitVec.ofNat 8 s.{qf}[i.toNat].toNat) := by " ++
          s!"rw [{qs}.At_eq] at hm; exact LeanQbe.T.sepTree_bytes_get_bv " ++
          s!"(t := {qs}.Tree{pArgsSp} p s) (p := {pathS}) rfl hi hb hm",
        s!"theorem {qs}.{q ("LengthsOk_set_" ++ fName)} {implSp}\{s : {qs}} " ++
          s!"(hlen : {qs}.LengthsOk{pArgsSp} s) (bs' : List UInt8) " ++
          s!"(hnew : bs'.length = ({lt})) : {qs}.LengthsOk{pArgsSp} {updWhole} := " ++
          s!"\{ hlen with {qLen} := hnew }"
      ]
    | .pad _ _ => pure ()
    -- Lens
    let fTy := structFieldType p.spec
    let updL := mkStructUpdate dataFields fName "v"
    let lensSBinder := if dataFields.length == 1 then "_" else "s"
    cmds := cmds ++ [
      s!"{exp}def {qs}.{q ("lens_" ++ fName)} : LeanQbe.T.C0Lens {qs} ({fTy}) where\n" ++
        s!"  get s := s.{qf}\n  set {lensSBinder} v := {updL}\n" ++
        "  get_set := by intros; rfl\n  set_get := by intro s; cases s; rfl\n" ++
        "  set_set := by intros; rfl"
    ]
  -- 8. to_region / to_region_frame
  let hasCell := placed.any fun p => match p.spec with | .cell _ => true | _ => false
  let hasArrEx := placed.any fun p => match p.spec with | .array _ _ _ false => true | _ => false
  let hasArrPd := placed.any fun p => match p.spec with | .array _ _ _ true => true | _ => false
  let hasBytes := placed.any fun p => match p.spec with | .bytes _ _ => true | _ => false
  let hasPad := placed.any fun p => match p.spec with | .pad _ _ => true | _ => false
  let segConstrs : List String :=
    (if hasCell then ["LeanQbe.T.SlabSeg.ofCell"] else []) ++
    (if hasArrEx then ["LeanQbe.T.SlabSeg.ofArrayExact"] else []) ++
    (if hasArrPd then ["LeanQbe.T.SlabSeg.ofArrayAlign8", "LeanQbe.T.SlabSeg.ofArray"] else []) ++
    (if hasBytes then ["LeanQbe.T.SlabSeg.ofBytes"] else []) ++
    (if hasPad then ["LeanQbe.T.SlabSeg.ofRegion"] else [])
  let constrStr := if segConstrs.isEmpty then "" else ", " ++ ", ".intercalate segConstrs
  let segTotTac :=
    s!"by dsimp only [{qs}.flatSegs, {qs}.totalBytes, List.map, " ++
    s!"LeanQbe.T.SlabChain.totalBytesFlat, LeanQbe.T.Ty.bytes, " ++
    s!"LeanQbe.T.Ty.size{constrStr}]; try omega"
  let segContTac :=
    s!"by dsimp only [LeanQbe.T.SlabChain.Contiguous, {qs}.flatSegs, " ++
    s!"LeanQbe.T.SlabChain.flatAddr, LeanQbe.T.Ty.bytes, " ++
    s!"LeanQbe.T.Ty.size{constrStr}]; " ++
    "repeat (first | exact True.intro | constructor | rfl | omega)"
  let leavesEqFlat :=
    s!"have hls : ({qs}.Tree{pArgsSp} p s).leaves = " ++
    s!"(LeanQbe.T.SlabChain.flatAddrs p ({qs}.flatSegs{pArgsSp} s hlen)).map " ++
    s!"fun x => x.2.pred x.1 := (by dsimp only [{qs}.Tree, {qs}.flatSegs, " ++
    s!"LeanQbe.T.SlabChain.flatAddrs, LeanQbe.T.SlabChain.flatAddr{constrStr}, " ++
    "LeanQbe.T.SepTree.leaves, List.append, List.map]; try rfl)"
  cmds := cmds ++ [
    s!"theorem {qs}.to_region {implSp}\{p : BitVec 64} \{s : {qs}} \{m : {memTy}} " ++
      s!"(hlen : {qs}.LengthsOk{pArgsSp} s) (hfit : {qs}.totalBytes{pArgsSp} ≤ 2 ^ 64) " ++
      s!"(hm : {qs}.At{pArgsSp} p s m) : " ++
      s!"LeanQbe.T.region p ({qs}.totalBytes{pArgsSp}) m := by " ++
      s!"rw [{qs}.At_eq, LeanQbe.T.SepTree.eval_eq_evalPreds] at hm; {leavesEqFlat}; " ++
      s!"rw [hls] at hm; exact LeanQbe.T.SepTree.evalPreds_to_region_eq " ++
      s!"({segContTac}) ({segTotTac}) hfit hm",
    s!"theorem {qs}.to_region_frame {implSp}\{p : BitVec 64} \{s : {qs}} " ++
      s!"\{R : {memTy} → Prop} \{m : {memTy}} (hlen : {qs}.LengthsOk{pArgsSp} s) " ++
      s!"(hfit : {qs}.totalBytes{pArgsSp} ≤ 2 ^ 64) " ++
      s!"(hm : ({qs}.At{pArgsSp} p s ⋆ R) m) : " ++
      s!"(LeanQbe.T.region p ({qs}.totalBytes{pArgsSp}) ⋆ R) m := by " ++
      s!"rw [{qs}.At_eq, LeanQbe.T.SepTree.eval_eq_evalPreds] at hm; {leavesEqFlat}; " ++
      s!"rw [hls] at hm; exact LeanQbe.T.SepTree.evalPreds_to_region_frame_eq " ++
      s!"({segContTac}) ({segTotTac}) hfit hm"
  ]
  -- 9. of_region / of_region_frame via SlabSegKind
  let kindTotTac :=
    "by dsimp only [LeanQbe.T.SlabSegKind.totalBytes, LeanQbe.T.SlabSegKind.stride, " ++
    s!"List.map, {qs}.kindItems, {qs}.totalBytes]; try omega"
  let kindContTac :=
    "by dsimp only [LeanQbe.T.SlabSegKind.Contiguous, LeanQbe.T.SlabSegKind.stride, " ++
    s!"{qs}.kindItems]; repeat (first | exact True.intro | constructor | rfl | omega)"
  let patVars := (placed.zipIdx.map fun (p, idx) =>
    if segIsPad p then s!"_v{idx}" else s!"v{idx}").foldr (init := ".nil") fun v acc =>
      s!".cons {v} ({acc})"
  let structFieldInits := placed.zipIdx.filterMap fun (p, idx) =>
    match p.spec with
    | .cell _ => some s!"{q p.name} := v{idx}"
    | .array .. | .bytes .. => some s!"{q p.name} := v{idx}.1"
    | .pad _ _ => none
  let structLit :=
    if structFieldInits.isEmpty then "⟨⟩"
    else "{" ++ ", ".intercalate structFieldInits ++ "}"
  let lenFieldInits := placed.zipIdx.filterMap fun (p, idx) =>
    match p.spec with
    | .array .. | .bytes .. => some s!"{q (p.name ++ "_len")} := v{idx}.2"
    | _ => none
  let lenLit :=
    if lenFieldInits.isEmpty then "⟨⟩"
    else "{" ++ ", ".intercalate lenFieldInits ++ "}"
  let unpackBody (framed : Bool) :=
    if placed.isEmpty then
      s!"exact ⟨⟨⟩, ⟨⟩, by rw [{qs}.At_eq]; exact hm⟩"
    else
      let fnNm :=
        if framed then "LeanQbe.T.SlabSegKind.of_region_flat_frame"
        else "LeanQbe.T.SlabSegKind.of_region_flat"
      let prefixT :=
        s!"obtain ⟨vs, hev⟩ := {fnNm} (xs := {qs}.kindItems{pArgsSp}) " ++
        s!"({kindContTac}) ({kindTotTac}) hfit hm"
      let prep :=
        "rw [LeanQbe.T.SlabSegKind.evalFlat_eq_evalPreds] at hev; " ++
        s!"revert vs hev; dsimp only [{qs}.kindItems, List.map]; intro vs hev"
      let evalMatch :=
        s!"rw [{qs}.At_eq, LeanQbe.T.SepTree.eval_eq_evalPreds]; " ++
        s!"have hls : ({qs}.Tree{pArgsSp} p {structLit}).leaves = " ++
        s!"LeanQbe.T.SlabSegKind.toPredList p {kindList} ({patVars}) := " ++
        s!"(by dsimp only [{qs}.Tree, LeanQbe.T.SepTree.leaves, " ++
        "List.append, LeanQbe.T.SlabSegKind.toPredList, LeanQbe.T.SlabChain.flatAddr, " ++
        "LeanQbe.T.SlabSegKind.pred, List.map]; try rfl); rw [hls]; exact hev"
      s!"{prefixT}; {prep}; match vs with | {patVars} => " ++
        s!"refine ⟨{structLit}, {lenLit}, by {evalMatch}⟩"
  cmds := cmds ++ [
    s!"theorem {qs}.of_region {implSp}\{p : BitVec 64} \{m : {memTy}} " ++
      s!"(hfit : {qs}.totalBytes{pArgsSp} ≤ 2 ^ 64) " ++
      s!"(hm : LeanQbe.T.region p ({qs}.totalBytes{pArgsSp}) m) : " ++
      s!"∃ s : {qs}, {qs}.LengthsOk{pArgsSp} s ∧ {qs}.At{pArgsSp} p s m := by " ++
      s!"{unpackBody false}",
    s!"theorem {qs}.of_region_frame {implSp}\{p : BitVec 64} \{R : {memTy} → Prop} " ++
      s!"\{m : {memTy}} (hfit : {qs}.totalBytes{pArgsSp} ≤ 2 ^ 64) " ++
      s!"(hm : (LeanQbe.T.region p ({qs}.totalBytes{pArgsSp}) ⋆ R) m) : " ++
      s!"∃ s : {qs}, {qs}.LengthsOk{pArgsSp} s ∧ ({qs}.At{pArgsSp} p s ⋆ R) m := by " ++
      s!"{unpackBody true}"
  ]
  return cmds

private meta def parseSlabSegSpec (stx : Syntax) : CommandElabM SlabSegSpec := do
  let kind := stx.getKind
  match kind with
  | `LeanQbe.T.SlabLayout.«slabSegSpecSingle» =>
    match stx[0].getId.toString with
    | "cell8" => return .cell 1
    | "cell16" => return .cell 2
    | "cell32" => return .cell 4
    | "cell64" => return .cell 8
    | other => throwErrorAt stx s!"c0_slab_layout!: unexpected segment keyword '{other}'"
  | `LeanQbe.T.SlabLayout.«slabSegSpecPair» =>
    match stx[0].getId.toString with
    | "cell" => return .cell (← parseSlabTyBytes stx[1])
    | "region" | "pad" =>
      let (lt, ls) := termInfo stx[1]
      return .pad lt ls
    | other => throwErrorAt stx s!"c0_slab_layout!: unexpected segment '{other} ...'"
  | `LeanQbe.T.SlabLayout.«slabSegSpecNum» =>
    match stx[0].getId.toString with
    | "region" | "pad" =>
      let (lt, ls) := termInfo stx[1]
      return .pad lt ls
    | other => throwErrorAt stx s!"c0_slab_layout!: unexpected numeric segment '{other}'"
  | `LeanQbe.T.SlabLayout.«slabSegSpecCall» =>
    match stx[0].getId.toString with
    | "region" | "pad" =>
      let (lt, ls) := termInfo stx[2]
      return .pad lt ls
    | other => throwErrorAt stx s!"c0_slab_layout!: unexpected parenthesized segment '{other}'"
  | `LeanQbe.T.SlabLayout.«slabSegSpecArr» =>
    let (lt, ls) := termInfo stx[2]
    match stx[0].getId.toString with
    | "array8" => return .array 1 lt ls false
    | "array16" => return .array 2 lt ls false
    | "array32" => return .array 4 lt ls false
    | "array64" => return .array 8 lt ls false
    | "bytes" => return .bytes lt ls
    | "region" | "pad" => return .pad lt ls
    | other => throwErrorAt stx s!"c0_slab_layout!: unexpected bracketed segment '{other}'"
  | `LeanQbe.T.SlabLayout.«slabSegSpecArrTy» =>
    let eb ← parseSlabTyBytes stx[1]
    let (lt, ls) := termInfo stx[3]
    match stx[0].getId.toString with
    | "array" => return .array eb lt ls false
    | "array_align8" => return .array eb lt ls true
    | other => throwErrorAt stx s!"c0_slab_layout!: unexpected typed array segment '{other}'"
  | _ => throwErrorAt stx s!"c0_slab_layout!: unsupported segment specification ({kind})"

declare_syntax_cat slabParam
declare_syntax_cat slabSegSpec
declare_syntax_cat slabField

syntax "(" ident " : " term ")" : slabParam
syntax (name := slabSegSpecCall) withPosition(ident colGt "(" term ")") : slabSegSpec
syntax (name := slabSegSpecArrTy) withPosition(ident colGt ident "[" term "]") : slabSegSpec
syntax (name := slabSegSpecArr) withPosition(ident "[" term "]") : slabSegSpec
syntax (name := slabSegSpecPair) withPosition(ident colGt ident) : slabSegSpec
syntax (name := slabSegSpecNum) withPosition(ident colGt num) : slabSegSpec
syntax (name := slabSegSpecSingle) ident : slabSegSpec

syntax ident " : " slabSegSpec : slabField

/-- Declarative specification of a C-compatible slab layout with balanced `SepTree`,
`@[c0_load]`/`@[c0_store]` accessors, `to_region`/`of_region`, and `C0Lens` per field. -/
syntax withPosition("c0_slab_layout! " ident slabParam* " where" (colGt slabField)*) : command

elab_rules : command
  | `(c0_slab_layout! $name:ident $params:slabParam* where $fields:slabField*) => do
    let sName := name.getId.toString
    let mut paramList : List (String × String) := []
    for p in params do
      let pId := p.raw[1].getId.toString
      let (pTy, _) := termInfo p.raw[3]
      paramList := paramList ++ [(pId, pTy)]
    let mut fieldList : List SlabFieldInfo := []
    for f in fields do
      let fId := f.raw[0].getId.toString
      let spec ← parseSlabSegSpec f.raw[2]
      fieldList := fieldList ++ [{ name := fId, spec }]
    let env ← getEnv
    let cmds := slabCommands sName paramList fieldList env.header.isModule
    for c in cmds do
      match Lean.Parser.runParserCategory env `command c with
      | .error msg => throwError "c0_slab_layout! generated syntax error:\n{msg}\n{c}"
      | .ok stx => elabCommand stx

end LeanQbe.T.SlabLayout

end
