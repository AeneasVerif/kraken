/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.InlinePlan
public import LeanQbe.T.Main
public import LeanQbe.T.MainFlat

/-!
# Subsystem-Aligned Build Oracle Serializer (`SegCertOracleCommon`)

Pure compiled `IO` oracle library (zero `*Lemmas*`, zero `Lean` meta, zero arch crates) that:
1. Extracts exact per-subsystem `InlPlan`s from `policyToInlPlan` (`selectCandsForCaller` parity),
   determines minimal cross-subsystem `Exports` targets (`planExportsFor`), and computes DAG deps.
2. Serializes deterministic, `<= 100`-column Lean 4 data modules:
   - `Oracle/<S>.lean`: `def plan : InlPlan`
   - `Inl/<S>/Exports.lean`: pure `TFlatFn` leaf (zero import of `Src/<S>` or `Inl/<S>`)
   - `Oracle/{Amd64,Arm64}/<S>.lean`: `hints`, pruned `ext`, plus per-fn `hint_<fn>` / `ext_<fn>`
3. Emits subsystem manifest + per-fn size/bound JSON for `scripts/gen_build_segs.py`.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.SegCertOracle

open LeanQbe.T

/-- Named source subsystem input for oracle generation. -/
structure SegInput where
  name : String
  srcMod : String
  srcFns : String := "fns"
  fns : List Fn

/-- Computed arch-neutral plan, dependency, and export metadata for one subsystem. -/
structure SegPlanInfo where
  seg : SegInput
  plan : InlPlan
  deps : List String
  exportNames : List Sym
  inlinedFlats : List TFlatFn

/-! ## 1. Deterministic `Std.Format` Lean Literal Printers (`<= 96` cols) -/

private def fmtStr (s : String) : Std.Format :=
  repr s

private def fmtTy : Ty → Std.Format
  | .bool => ".bool"
  | .bits 8 => "i8"
  | .bits 16 => "i16"
  | .bits 32 => "i32"
  | .bits 64 => "i64"
  | .bits n => s!"(Ty.bits {n})"
  | .float .h => "f16"
  | .float .s => "f32"
  | .float .d => "f64"
  | .float .q => "f128"
  | .pair a b => Std.Format.paren (".pair " ++ fmtTy a ++ " " ++ fmtTy b)

private def fmtList (elems : List Std.Format) : Std.Format :=
  if elems.isEmpty then "[]"
  else Std.Format.bracket "[" (Std.Format.joinSep elems ("," ++ Std.Format.line)) "]"

private def fmtListTy (ts : List Ty) : Std.Format :=
  fmtList (ts.map fmtTy)

private def fmtFmt : Fmt → String
  | .h => ".h" | .s => ".s" | .d => ".d" | .q => ".q"

private def fmtCmpOp : CmpOp → String
  | .eq => ".eq" | .ne => ".ne" | .ult => ".ult" | .ule => ".ule" | .ugt => ".ugt"
  | .uge => ".uge" | .slt => ".slt" | .sle => ".sle" | .sgt => ".sgt" | .sge => ".sge"

private def fmtFCmpOp : FCmpOp → String
  | .eq => ".eq" | .ne => ".ne" | .lt => ".lt" | .le => ".le"
  | .gt => ".gt" | .ge => ".ge" | .ord => ".ord" | .uno => ".uno"

private def fmtVal : (t : Ty) → Val t → Std.Format
  | .bool, v => if v then "true" else "false"
  | .bits n, v => s!"BitVec.ofNat {n} {v.toNat}"
  | .float f, v => s!"BitVec.ofNat {f.width} {v.toNat}"
  | .pair a b, (x, y) => Std.Format.paren (fmtVal a x ++ ", " ++ fmtVal b y)

private def fmtArgK (t : Ty) : Arg K t → Std.Format
  | .var idx => s!"(.var {idx})"
  | .imm c => Std.Format.paren (".imm " ++ Std.Format.paren (fmtVal t c))

private def fmtTupArgK : (ts : List Ty) → Tup (Arg K) ts → Std.Format
  | [], () => "()"
  | t :: ts, (a, rest) => Std.Format.paren (fmtArgK t a ++ ", " ++ fmtTupArgK ts rest)

private def fmtOpCode {sig rs : List Ty} : OpCode sig rs → Std.Format
  | .copy t => ".copy " ++ fmtTy t
  | .add t => ".add " ++ fmtTy t
  | .sub t => ".sub " ++ fmtTy t
  | .mul t => ".mul " ++ fmtTy t
  | .neg t => ".neg " ++ fmtTy t
  | .and t => ".and " ++ fmtTy t
  | .or t => ".or " ++ fmtTy t
  | .xor t => ".xor " ++ fmtTy t
  | .not t => ".not " ++ fmtTy t
  | .ternlog t i => ".ternlog " ++ fmtTy t ++ s!" (BitVec.ofNat 8 {i.toNat})"
  | .shl t => ".shl " ++ fmtTy t
  | .lshr t => ".lshr " ++ fmtTy t
  | .ashr t => ".ashr " ++ fmtTy t
  | .rotl t => ".rotl " ++ fmtTy t
  | .rotr t => ".rotr " ++ fmtTy t
  | .fshl n => s!".fshl {n}"
  | .fshr n => s!".fshr {n}"
  | .bswap t => ".bswap " ++ fmtTy t
  | .clz n => s!".clz {n}"
  | .cls n => s!".cls {n}"
  | .rbit n => s!".rbit {n}"
  | .ctz n => s!".ctz {n}"
  | .popcnt n => s!".popcnt {n}"
  | .cmp o t m _ => s!".cmp {fmtCmpOp o} " ++ fmtTy t ++ " " ++ fmtTy m ++ " rfl"
  | .select t => ".select " ++ fmtTy t
  | .blend t m _ => ".blend " ++ fmtTy t ++ " " ++ fmtTy m ++ " rfl"
  | .zext m n => s!".zext {m} {n}"
  | .sext m n => s!".sext {m} {n}"
  | .trunc m n => s!".trunc {m} {n}"
  | .ofBool n => s!".ofBool {n}"
  | .addc n => s!".addc {n}"
  | .subb n => s!".subb {n}"
  | .umulw n => s!".umulw {n}"
  | .smulw n => s!".smulw {n}"
  | .udiv n => s!".udiv {n}"
  | .sdiv n => s!".sdiv {n}"
  | .urem n => s!".urem {n}"
  | .srem n => s!".srem {n}"
  | .udiv0 n => s!".udiv0 {n}"
  | .sdiv0 n => s!".sdiv0 {n}"
  | .mkpair a b => ".mkpair " ++ fmtTy a ++ " " ++ fmtTy b
  | .unpair a b => ".unpair " ++ fmtTy a ++ " " ++ fmtTy b
  | .bitcast t u _ => ".bitcast " ++ fmtTy t ++ " " ++ fmtTy u ++ " rfl"
  | .shufd t i => ".shufd " ++ fmtTy t ++ s!" (BitVec.ofNat 8 {i.toNat})"
  | .shufb t => ".shufb " ++ fmtTy t
  | .alignr t i => ".alignr " ++ fmtTy t ++ s!" (BitVec.ofNat 8 {i.toNat})"
  | .blendw t i => ".blendw " ++ fmtTy t ++ s!" (BitVec.ofNat 8 {i.toNat})"
  | .sha256rnds2 => ".sha256rnds2"
  | .sha256msg1 => ".sha256msg1"
  | .sha256msg2 => ".sha256msg2"
  | .fadd t => ".fadd " ++ fmtTy t
  | .fsub t => ".fsub " ++ fmtTy t
  | .fmul t => ".fmul " ++ fmtTy t
  | .fdiv t => ".fdiv " ++ fmtTy t
  | .ffma t => ".ffma " ++ fmtTy t
  | .fsqrt t => ".fsqrt " ++ fmtTy t
  | .fneg t => ".fneg " ++ fmtTy t
  | .fabs t => ".fabs " ++ fmtTy t
  | .fcmp o t m _ => s!".fcmp {fmtFCmpOp o} " ++ fmtTy t ++ " " ++ fmtTy m ++ " rfl"
  | .fptoui f n => s!".fptoui {fmtFmt f} {n}"
  | .fptosi f n => s!".fptosi {fmtFmt f} {n}"
  | .uitofp n f => s!".uitofp {n} {fmtFmt f}"
  | .sitofp n f => s!".sitofp {n} {fmtFmt f}"
  | .fcvt f g => s!".fcvt {fmtFmt f} {fmtFmt g}"

private def fmtOpK {rs : List Ty} (op : Op K rs) : Std.Format :=
  Std.Format.group <| Std.Format.nest 2 <|
    "⟨" ++ fmtOpCode op.code ++ "," ++ Std.Format.line ++ fmtTupArgK op.sig op.args ++ "⟩"

mutual
private def fmtTFlat {rs : List Ty} : TFlat rs → Std.Format
  | .let_ (ts := ts) op k =>
    Std.Format.group <| Std.Format.nest 2 <|
      "TFlat.let_ (ts := " ++ fmtListTy ts ++ ")" ++ Std.Format.line ++
        Std.Format.paren (fmtOpK op) ++ Std.Format.line ++ Std.Format.paren (fmtTFlat k)
  | .load t a k =>
    Std.Format.group <| Std.Format.nest 2 <|
      "TFlat.load " ++ fmtTy t ++ " " ++ fmtArgK i64 a ++ Std.Format.line ++
        Std.Format.paren (fmtTFlat k)
  | .store (t := t) v a k =>
    Std.Format.group <| Std.Format.nest 2 <|
      "TFlat.store " ++ fmtArgK t v ++ " " ++ fmtArgK i64 a ++ Std.Format.line ++
        Std.Format.paren (fmtTFlat k)
  | .call f (as := as) bs args k =>
    Std.Format.group <| Std.Format.nest 2 <|
      "TFlat.call " ++ fmtStr f ++ " (as := " ++ fmtListTy as ++ ") " ++ fmtListTy bs ++
        Std.Format.line ++ fmtTupArgK as args ++ Std.Format.line ++
        Std.Format.paren (fmtTFlat k)
  | .jnz c t e =>
    Std.Format.group <| Std.Format.nest 2 <|
      "TFlat.jnz " ++ fmtArgK .bool c ++ Std.Format.line ++
        Std.Format.paren (fmtTFlat t) ++ Std.Format.line ++ Std.Format.paren (fmtTFlat e)
  | .jump (ts := ts) j args =>
    Std.Format.group <| Std.Format.nest 2 <|
      s!"TFlat.jump (ts := " ++ fmtListTy ts ++ s!") {j} " ++ fmtTupArgK ts args
  | .ret vs =>
    "TFlat.ret " ++ fmtTupArgK rs vs
  | .exit f (as := as) args =>
    "TFlat.exit " ++ fmtStr f ++ " (as := " ++ fmtListTy as ++ ") " ++ fmtTupArgK as args
  | .hlt => "TFlat.hlt"
  | .group (sig := sig) bodies k =>
    Std.Format.group <| Std.Format.nest 2 <|
      "TFlat.group (sig := " ++ fmtList (sig.map fmtListTy) ++ ")" ++ Std.Format.line ++
        Std.Format.paren (fmtTBlocks bodies) ++ Std.Format.line ++
        Std.Format.paren (fmtTFlat k)

private def fmtTBlocks {rs : List Ty} : {sig : List (List Ty)} → TBlocks rs sig → Std.Format
  | _, .nil => "TBlocks.nil"
  | _, .cons (ts := ts) b bs =>
    Std.Format.group <| Std.Format.nest 2 <|
      "TBlocks.cons (ts := " ++ fmtListTy ts ++ ")" ++ Std.Format.line ++
        Std.Format.paren (fmtTFlat b) ++ Std.Format.line ++ Std.Format.paren (fmtTBlocks bs)
end

private def fmtTFlatFn (tf : TFlatFn) : Std.Format :=
  Std.Format.nest 2 <|
    "{" ++ Std.Format.line ++
    "name := " ++ fmtStr tf.name ++ "," ++ Std.Format.line ++
    "as := " ++ fmtListTy tf.as ++ "," ++ Std.Format.line ++
    "rs := " ++ fmtListTy tf.rs ++ "," ++ Std.Format.line ++
    "body := " ++ Std.Format.nest 2 (fmtTFlat tf.body) ++ Std.Format.line ++ "}"

private def fmtSigBound (entry : SigEntry × Nat) : Std.Format :=
  let ((nm, as, rs), b) := entry
  Std.Format.group <|
    "((" ++ fmtStr nm ++ ", " ++ fmtListTy as ++ ", " ++ fmtListTy rs ++ s!"), {b})"

private def fmtSlotWidth : SlotWidth → String
  | .w64 => ".w64" | .w128 => ".w128" | .w256 => ".w256" | .w512 => ".w512"

private def fmtVariantHint : VariantHint → Std.Format
  | .default => ".default"
  | .adcx => ".adcx"
  | .adox => ".adox"
  | .mulxFast => ".mulxFast"
  | .decInc => ".decInc"
  | .disp off => s!"(.disp (Int64.ofBitVec (BitVec.ofNat 64 {off.toBitVec.toNat})))"

private def fmtSymArg : SymArg → Std.Format
  | .var x => s!"(.var {x})"
  | .immBool b => if b then "(.immBool true)" else "(.immBool false)"
  | .immBits w c => s!"(.immBits {w} (BitVec.ofNat 64 {c.toNat}))"
  | .immVec w c => s!"(.immVec {fmtSlotWidth w} (BitVec.ofNat 512 {c.toNat}))"

private def fmtAtom (s : String) : String :=
  if s.contains ' ' then s!"({s})" else s

private def fmtLoc {R V C : Type} (fR : R → String) (fV : V → String) (fC : C → String) :
    Loc R V C → Std.Format
  | .gpr r => s!"(.gpr {fmtAtom (fR r)})"
  | .vec v => s!"(.vec {fmtAtom (fV v)})"
  | .flag c => s!"(.flag {fmtAtom (fC c)})"
  | .slot i w => s!"(.slot {i} {fmtSlotWidth w})"

private def fmtMove {R V C : Type} (fR : R → String) (fV : V → String) (fC : C → String) :
    Move R V C → Std.Format
  | .mov d s => s!"(.mov {fmtAtom (fR d)} {fmtAtom (fR s)})"
  | .movi d c => s!"(.movi {fmtAtom (fR d)} (BitVec.ofNat 64 {c.toNat}))"
  | .ld d i => s!"(.ld {fmtAtom (fR d)} {i})"
  | .st i s => s!"(.st {i} {fmtAtom (fR s)})"
  | .setcc d c => s!"(.setcc {fmtAtom (fR d)} {fmtAtom (fC c)})"
  | .vmov w d s => s!"(.vmov {fmtSlotWidth w} {fmtAtom (fV d)} {fmtAtom (fV s)})"
  | .vmovi w d c => s!"(.vmovi {fmtSlotWidth w} {fmtAtom (fV d)} (BitVec.ofNat 512 {c.toNat}))"
  | .vld w d i => s!"(.vld {fmtSlotWidth w} {fmtAtom (fV d)} {i})"
  | .vst w i s => s!"(.vst {fmtSlotWidth w} {i} {fmtAtom (fV s)})"

private def fmtPreStep {R V C : Type} (fR : R → String) (fV : V → String) (fC : C → String)
    (p : PreStep R V C) : Std.Format :=
  let cf := if p.clearFlags then "true" else "false"
  let ms := fmtList (p.moves.map (fmtMove fR fV fC))
  Std.Format.group <| Std.Format.nest 2 <|
    "{" ++ s!" clearFlags := {cf}," ++ Std.Format.line ++ "moves := " ++ ms ++ " }"

private def fmtBool (b : Bool) : Std.Format :=
  if b then "true" else "false"

private def fmtEntry {R V C : Type} (fR : R → String) (fV : V → String) (fC : C → String)
    (e : Entry R V C) : Std.Format :=
  let liveF := fmtList (e.live.map fun (a, l) =>
    Std.Format.group <| "(" ++ fmtSymArg a ++ ", " ++ fmtLoc fR fV fC l ++ ")")
  let plocF := fmtList (e.ploc.map (fmtLoc fR fV fC))
  let liveZF := fmtList (e.liveZ.map fmtBool)
  let plocZF := fmtList (e.plocZ.map fmtBool)
  Std.Format.group <| Std.Format.nest 2 <|
    "{ live := " ++ liveF ++ "," ++ Std.Format.line ++
    "ploc := " ++ plocF ++ "," ++ Std.Format.line ++
    "liveZ := " ++ liveZF ++ "," ++ Std.Format.line ++
    "plocZ := " ++ plocZF ++ " }"

private def fmtTrie {α : Type} (f : α → Std.Format) : Trie α → Std.Format
  | .empty => ".empty"
  | .node v e o =>
    let vF := match v with
      | none => "none"
      | some x => Std.Format.paren ("some " ++ f x)
    Std.Format.group <| Std.Format.nest 2 <|
      "(.node" ++ Std.Format.line ++ vF ++ Std.Format.line ++
        fmtTrie f e ++ Std.Format.line ++ fmtTrie f o ++ ")"

private def trieIsEmpty {α : Type} : Trie α → Bool
  | .empty => true
  | .node _ _ _ => false

private def fmtHints {R V C : Type} (fR : R → String) (fV : V → String) (fC : C → String)
    (h : Hints R V C) : Std.Format :=
  let fields : List Std.Format :=
    (if trieIsEmpty h.dest then [] else ["dest := " ++ fmtTrie (fmtLoc fR fV fC) h.dest]) ++
    (if trieIsEmpty h.entry then [] else ["entry := " ++ fmtTrie (fmtEntry fR fV fC) h.entry]) ++
    (if trieIsEmpty h.pre then [] else ["pre := " ++ fmtTrie (fmtPreStep fR fV fC) h.pre]) ++
    (if trieIsEmpty h.variant then [] else ["variant := " ++ fmtTrie fmtVariantHint h.variant]) ++
    (if trieIsEmpty h.elide then [] else ["elide := " ++ fmtTrie fmtBool h.elide]) ++
    (if trieIsEmpty h.invertJnz then [] else ["invertJnz := " ++ fmtTrie fmtBool h.invertJnz]) ++
    (if trieIsEmpty h.deferJnz then [] else ["deferJnz := " ++ fmtTrie fmtBool h.deferJnz]) ++
    (if trieIsEmpty h.deferLea then [] else ["deferLea := " ++ fmtTrie fmtBool h.deferLea]) ++
    (if trieIsEmpty h.deadFlags then [] else ["deadFlags := " ++ fmtTrie fmtBool h.deadFlags]) ++
    (if trieIsEmpty h.mulHiIps then [] else ["mulHiIps := " ++ fmtTrie fmtBool h.mulHiIps]) ++
    (if h.nslots == 0 then [] else [Std.Format.text s!"nslots := {h.nslots}"]) ++
    (if h.saved.isEmpty then [] else ["saved := " ++ fmtList (h.saved.map (Std.Format.text ∘ fR))])
  if fields.isEmpty then "{}"
  else Std.Format.nest 2 ("{" ++ Std.Format.line ++
    Std.Format.joinSep fields ("," ++ Std.Format.line) ++ " }")

private def pruneExt (callees : List SigEntry)
    (acc : List (SigEntry × Nat)) : List (SigEntry × Nat) :=
  let uniq := callees.foldl (fun seen g =>
    if seen.any (SigEntry.beq · g) then seen else seen ++ [g]) []
  uniq.filterMap fun g => (lookupBound acc g).map fun b => (g, b)

/-! ## 2. Per-Subsystem Plan, Exports, and Arch Oracle Generators -/

/-- Compute full `InlPlan` from `policy`, split by subsystem, and derive exact DAG deps and
minimal cross-subsystem `Exports`. -/
def computeSegPlans (policy : InlinePolicy) (segs : List SegInput)
    (externs : List Extern := []) (exits : List Sym := []) :
    InlPlan × List SegPlanInfo :=
  let fullMod : Module := { fns := segs.flatMap (·.fns), externs := externs, exits := exits }
  let fullPlan := policyToInlPlan policy fullMod
  let inlFull := inlineFnsPlan fullPlan [] fullMod.fns
  let flatFull := inlFull.map fun fn => ⟨fn.name, fn.as, fn.rs, reifyFunc fn.body⟩
  let rec split (ownerMap : List (Sym × String)) (remFlats : List TFlatFn) :
      List SegInput → List SegPlanInfo
    | [] => []
    | s :: rest =>
      let n := s.fns.length
      let sFlats := remFlats.take n
      let sNames := s.fns.map Fn.name
      let sPlan := fullPlan.filter fun (caller, _) => sNames.contains caller
      let sTargets := sPlan.flatMap Prod.snd
      let deps := sTargets.foldl (fun acc callee =>
        match ownerMap.find? (fun p => p.1 == callee) with
        | some (_, owner) =>
          if owner == s.name || acc.contains owner then acc else acc ++ [owner]
        | none => acc) []
      let expNames := planExportsFor fullPlan sNames
      let ownerMap' := ownerMap ++ sNames.map fun nm => (nm, s.name)
      { seg := s, plan := sPlan, deps := deps, exportNames := expNames,
        inlinedFlats := sFlats } :: split ownerMap' (remFlats.drop n) rest
  (fullPlan, split [] flatFull segs)

/-- Render `<Base>/Oracle/<S>.lean` carrying `def plan : InlPlan`. -/
def renderPlanOracleLean (modNs : String) (segPlan : InlPlan) : String :=
  let entries := segPlan.map fun (caller, callees) =>
    Std.Format.group <| "(" ++ fmtStr caller ++ ", " ++ fmtList (callees.map fmtStr) ++ ")"
  let body := (Std.Format.nest 2 ("@[expose] def plan : InlPlan :=" ++
    Std.Format.line ++ fmtList entries)).pretty 94
  String.intercalate "\n"
    [ "module"
    , ""
    , "public import LeanQbe.T.InlinePlan"
    , ""
    , "set_option autoImplicit false"
    , ""
    , "public section"
    , ""
    , s!"namespace {modNs}"
    , ""
    , "open LeanQbe.T"
    , ""
    , body
    , ""
    , s!"end {modNs}"
    , "" ]

/-- Render pure data leaf `<Base>/Inl/<S>/Exports.lean` (zero import of `Src` or `Inl`). -/
def renderExportsLean (modNs : String) (expFlats : List TFlatFn) : String :=
  let defs := expFlats.zipIdx.map fun (tf, i) =>
    let rhs := (fmtTFlatFn tf).pretty 92
    s!"@[expose] def flat{i} : TFlatFn :=\n  " ++ rhs.replace "\n" "\n  "
  let fnElems := (List.range expFlats.length).map fun i => Std.Format.text s!"flat{i}.toFn"
  let fnsLine := ("@[expose] def fns : List Fn :=" ++ Std.Format.line ++ fmtList fnElems).pretty 94
  String.intercalate "\n" <|
    [ "module"
    , ""
    , "public import LeanQbe.T.Flat"
    , "public import LeanQbe.T.Module"
    , ""
    , "set_option autoImplicit false"
    , ""
    , "public section"
    , ""
    , s!"namespace {modNs}"
    , ""
    , "open LeanQbe.T"
    , "" ] ++
    defs.intersperse "" ++
    [ ""
    , fnsLine
    , ""
    , s!"end {modNs}"
    , "" ]

/-- Compute oracle hints + pruned `ext` for one subsystem on target `(I, lt)`, returning
`(leanSource, nextExtAcc, perFnNameBoundSize)`. -/
def renderArchOracleLean (I : Isa) (fR : I.Reg → String) (fV : I.VReg → String)
    (fC : I.Cond → String) (lt : LegalTarget) (isaMod archNs isaExpr modNs : String)
    (ext0 : List (SigEntry × Nat)) (exits : List Sym) (nX maxBound : Nat)
    (segFlats : List TFlatFn) :
    IO (String × List (SigEntry × Nat) × List (Sym × Nat × Nat)) := do
  let mut acc := ext0
  let mut hintsRev : List (Sym × I.Hints × List (SigEntry × Nat)) := []
  let mut allCallees : List SigEntry := []
  let mut metricsRev : List (Sym × Nat × Nat) := []
  for f in segFlats do
    if !f.wfCheck then
      throw <| IO.userError s!"[SegCertOracle] {f.name}: flat wfCheck failed"
    let ef := earlyOptFlat f
    if !ef.supportsSource lt then
      throw <| IO.userError s!"[SegCertOracle] {f.name}: unsupported source op"
    let mf := midStageFlat lt ef
    let ext := TFlat.ext mf.body
    let h := Spill.hints I mf.toFn
    match checkAndBoundExt I I.frame.raBytes exits nX acc h ext with
    | none => throw <| IO.userError s!"[SegCertOracle] {f.name}: checkAndBoundExt failed"
    | some b =>
      if b > maxBound then
        throw <| IO.userError s!"[SegCertOracle] {f.name}: bound {b} > maxBound {maxBound}"
      let fnExt := pruneExt ext.callees acc
      allCallees := allCallees ++ ext.callees
      hintsRev := (f.name, h, fnExt) :: hintsRev
      metricsRev := (f.name, b, tflatSize mf.body) :: metricsRev
      acc := (mf.sig, b) :: acc
  let items := hintsRev.reverse
  let segExt := pruneExt allCallees ext0
  let perFnDefs := items.flatMap fun (nm, h, fnExt) =>
    let hStr := (fmtHints fR fV fC h).pretty 92
    let eStr := (fmtList (fnExt.map fmtSigBound)).pretty 92
    [ s!"@[expose] def hint_{nm} : {isaExpr}.Hints :=\n  " ++ hStr.replace "\n" "\n  "
    , s!"@[expose] def ext_{nm} : List (SigEntry × Nat) :=\n  " ++ eStr.replace "\n" "\n  "
    , "" ]
  let hintList := (fmtList (items.map fun (nm, _, _) => Std.Format.text s!"hint_{nm}")).pretty 92
  let segExtStr := (fmtList (segExt.map fmtSigBound)).pretty 92
  let src := String.intercalate "\n" <|
    [ "module"
    , ""
    , "public import LeanQbe.T.Main"
    , s!"public import {isaMod}"
    , ""
    , "set_option autoImplicit false"
    , ""
    , "public section"
    , ""
    , s!"namespace {modNs}"
    , ""
    , s!"open LeanQbe.T {archNs}"
    , "" ] ++
    perFnDefs ++
    [ s!"@[expose] def hints : List {isaExpr}.Hints :=\n  " ++ hintList.replace "\n" "\n  "
    , ""
    , s!"@[expose] def ext : List (SigEntry × Nat) :=\n  " ++ segExtStr.replace "\n" "\n  "
    , ""
    , s!"end {modNs}"
    , "" ]
  pure (src, acc, metricsRev.reverse)

/-- Format per-function `{name, bound, flat_size}` JSON for `gen_build_segs.py --profile`. -/
def formatProfileJson (rows : List (Sym × Nat × Nat)) : String :=
  let objs := rows.map fun (nm, b, sz) =>
    s!"  \{\"name\": \"{nm}\", \"bound\": {b}, \"flat_size\": {sz}}"
  "[\n" ++ String.intercalate ",\n" objs ++ "\n]\n"

/-- Format a JSON manifest consumed directly by `scripts/gen_build_segs.py --manifest`. -/
def formatManifestJson (baseNs srcFullMod srcFullModSym : String)
    (infos : List SegPlanInfo) : String :=
  let q := fun (s : String) => "\"" ++ s ++ "\""
  let qList := fun (xs : List String) => "[" ++ String.intercalate ", " (xs.map q) ++ "]"
  let segObjs := infos.map fun info =>
    let fnNames := info.seg.fns.map Fn.name
    "    {" ++
    s!"\"name\": {q info.seg.name}, \"src_mod\": {q info.seg.srcMod}, " ++
    s!"\"src_fns\": {q info.seg.srcFns}, \"fns\": {qList fnNames}, " ++
    s!"\"deps\": {qList info.deps}, \"exports\": {qList info.exportNames}" ++
    "}"
  "{\n" ++
  s!"  \"base_ns\": {q baseNs},\n" ++
  s!"  \"src_full_mod\": {q srcFullMod},\n" ++
  s!"  \"src_full_mod_sym\": {q srcFullModSym},\n" ++
  "  \"segs\": [\n" ++
  String.intercalate ",\n" segObjs ++
  "\n  ]\n}\n"

end LeanQbeTest.T.SegCertOracle
