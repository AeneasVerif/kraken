module

public import LeanQbe.T.Opt
public import LeanQbe.T.Legal
public import LeanQbe.T.Spill
public import LeanQbe.T.Rega
public import LeanQbe.T.Module

/-!
# Target-Parameterized PHOAS Compiler Driver

Executes the typed `LeanQbe.T` pipeline end-to-end above any `Target` without importing any
architecture crate or earlier untyped-IR module:

* `Fn.earlyOpt` / `Fn.lateOpt` / `Fn.mid`: `earlyOpt → Legal lt → lateOpt` staged mid-end lowering.
* `Expr.extAux` / `Fn.ext`: PHOAS traversal collecting `(calleeSym, as, bs)` triples and exit
  symbols matching `Rega.lowerExpr` (ignoring dead `.jnz (.imm b)` branches).
* `Fn.computeHints`: untrusted heuristic entry point calling `Spill.hints` (for meta/CLI hint
  splicing ONLY — never invoked by `compileFn`, `compile`, or `compileModule`).
* `compileFn`, `compile`, `calleesBound`, `checkAndBound`, `compileModule`: verified backend
  driver taking pre-computed literal `I.Hints` and checking callee bounds by legalized
  `SigEntry` (`Sym × List Ty × List Ty`) via `SigEntry.beq`, exit permissions, and 64-bit
  stack-frame overflow.
* `fnNameOk`, `stringsNodup`, `checkCompileResult`, `checkCompileResultWithLabels`,
  `extractCode`, `extractBounds`: single-pass kernel-reducible validity checkers and extractors.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T

/-! ## Mid-end pipeline and external hint computation -/

/-- Run legacy source-level PHOAS optimizations (`copy`, `gvn`, `fold`, `dce`) on a typed
function. -/
def Fn.opt (f : Fn) : Fn :=
  ⟨f.name, f.as, f.rs, Func.opt f.body⟩

/-- Run pre-`Legal` mid-end optimizations (`Func.earlyOpt`) on a named function. -/
def Fn.earlyOpt (f : Fn) : Fn :=
  ⟨f.name, f.as, f.rs, Func.earlyOpt f.body⟩

/-- Run post-`Legal` mid-end optimizations (`Func.lateOpt`) on a named function. -/
def Fn.lateOpt (f : Fn) : Fn :=
  ⟨f.name, f.as, f.rs, Func.lateOpt f.body⟩

/-- Data wrapper keeping materialized mid-end `Func` closures out of LCNF eta-expansion. -/
structure MidBody (as rs : List Ty) where
  body : Func as rs

/-- Materialize the post-`earlyOpt` mid-end pipeline (`Legal lt → lateCorePre → renorm →
lateCorePost → renorm → lateCfgPre → renorm → lateCfgPost → loopRotate → renorm →
lateCondThread → renorm`), using `Fn.renorm` at every stage boundary so PHOAS closures stay flat. -/
def Fn.midStage (lt : LegalTarget) (ef : Fn) :
    MidBody (lt.legalSig ef.as) (lt.legalSig ef.rs) :=
  let lf := ef.legal lt
  let s1 := Fn.renorm ⟨lf.name, lf.as, lf.rs, Func.lateCorePre lf.body⟩
  let s2 := Fn.renorm ⟨s1.name, s1.as, s1.rs, Func.lateCorePost s1.body⟩
  let s3 := Fn.renorm ⟨s2.name, s2.as, s2.rs, Func.lateCfgPreWith lt.foldAddrDisp s2.body⟩
  let s4 := Fn.renorm ⟨s3.name, s3.as, s3.rs, Func.lateLoopRotate s3.body⟩
  ⟨(Fn.renorm ⟨s4.name, s4.as, s4.rs, Func.lateCondThread s4.body⟩).body⟩

theorem Fn.midStage_eq (lt : LegalTarget) (ef : Fn) :
    (Fn.midStage lt ef).body =
      Func.renorm (Func.lateCondThread (Func.renorm (Func.lateLoopRotate
        (Func.renorm (Func.lateCfgPreWith lt.foldAddrDisp (Func.renorm (Func.lateCorePost
          (Func.renorm (Func.lateCorePre (Func.legal lt ef.body)))))))))) := by
  dsimp only [Fn.midStage, Fn.renorm, Fn.legal, Func.renorm]

attribute [irreducible] Fn.midStage

/-- Wrapper exposing `(ef.name, lt.legalSig ef.as, lt.legalSig ef.rs)` transparently while
keeping `Fn.midStage` irreducible to tactics/elaboration. -/
def Fn.midFromEarly (lt : LegalTarget) (ef : Fn) : Fn :=
  ⟨ef.name, lt.legalSig ef.as, lt.legalSig ef.rs, (Fn.midStage lt ef).body⟩

/-- Run the staged mid-end pipeline (`earlyOpt → Legal lt → lateOpt`) on a typed function,
materializing each stage boundary via `Fn.renorm`. -/
def Fn.mid (lt : LegalTarget) (f : Fn) : Fn :=
  Fn.midFromEarly lt f.earlyOpt

/-- Compute register-allocation / spill hints for `f.mid lt`. For meta/CLI hint splicing ONLY;
never invoked inside `compileFn`, `compile`, or `compileModule`. -/
def Fn.computeHints (I : Isa) (lt : LegalTarget) (f : Fn) : I.Hints :=
  Spill.hints I (f.mid lt)

/-! ## PHOAS `Rega.Ext` collection -/

def addCalleeSig (g : Sym) (as bs : List Ty) (cs : List SigEntry) : List SigEntry :=
  let e : SigEntry := (g, as, bs)
  if cs.any (SigEntry.beq e) then cs else e :: cs

def addExitSym (g : Sym) (xs : List Sym) : List Sym :=
  if xs.contains g then xs else g :: xs

mutual
/-- Collect deduplicated `(calleeSym, as, bs)` signatures and exit targets reachable during
`Rega.lowerExpr` traversal (pruning the statically dead arm of `.jnz (.imm b)`). -/
def Expr.extAux {rs : List Ty} :
    Expr (fun _ => Unit) (fun _ => Unit) rs →
    List SigEntry → List Sym → List SigEntry × List Sym
  | .let_ (ts := ts) _ k, cs, xs => Expr.extAux (k (Tup.units ts)) cs xs
  | .load _ _ k, cs, xs => Expr.extAux (k ()) cs xs
  | .store _ _ k, cs, xs => Expr.extAux k cs xs
  | .call g (as := as) (bs := bs) _ k, cs, xs =>
    Expr.extAux (k (Tup.units bs)) (addCalleeSig g as bs cs) xs
  | .jnz (.imm b) t e, cs, xs =>
    if b then Expr.extAux t cs xs else Expr.extAux e cs xs
  | .jnz (.var _) t e, cs, xs =>
    let (cs₁, xs₁) := Expr.extAux e cs xs
    Expr.extAux t cs₁ xs₁
  | .jump _ _, cs, xs | .ret _, cs, xs | .hlt, cs, xs => (cs, xs)
  | .exit g _, cs, xs => (cs, addExitSym g xs)
  | .group (sig := sig) bodies k, cs, xs =>
    let ls := Tup.units sig
    let (cs₁, xs₁) := Expr.extAux (k ls) cs xs
    Blocks.extAux (bodies ls) cs₁ xs₁

/-- Mutual helper for `Expr.extAux` over `Blocks`. -/
def Blocks.extAux {rs : List Ty} :
    {sig : List (List Ty)} → Blocks (fun _ => Unit) (fun _ => Unit) rs sig →
    List SigEntry → List Sym → List SigEntry × List Sym
  | _, .nil, cs, xs => (cs, xs)
  | _, .cons (ts := ts) b bs, cs, xs =>
    let (cs₁, xs₁) := Expr.extAux (b (Tup.units ts)) cs xs
    Blocks.extAux bs cs₁ xs₁
end

/-- Extract `Rega.Ext` (callee signatures and exit targets) from a typed function `f`. -/
def Fn.ext (f : Fn) : Rega.Ext :=
  let (cs, xs) := Expr.extAux (f.body (fun _ => Unit) (fun _ => Unit) (Tup.units f.as)) [] []
  ⟨cs.reverse, xs.reverse⟩

/-! ## Certified backend compilation and module linking -/

/-- Compile a single function with mid-end (`Opt → Legal lt → Opt`) and external `hints`. -/
def compileFn (I : Isa) (lt : LegalTarget) (hints : I.Hints) (f : Fn) :
    Except String (List I.Directive) :=
  let mf := f.mid lt
  Rega.lowerFn I hints mf.ext mf

/-- Compile a list of functions with aligned externally provided `hints`. -/
def compile (I : Isa) (lt : LegalTarget) :
    List Fn → List I.Hints → Except String (List I.Directive)
  | [], [] => .ok []
  | f :: fs, h :: hs =>
    match compileFn I lt h f, compile I lt fs hs with
    | .ok c, .ok cs => .ok (c ++ cs)
    | .error e, _ => .error s!"{f.name}: {e}"
    | _, .error e => .error e
  | _, _ => .error "compile: fn/hints length mismatch"

/-- Look up a stack bound keyed by legalized `SigEntry := Sym × List Ty × List Ty` via
`SigEntry.beq` (avoiding slow kernel `DecidableEq` on `List Ty`). -/
def lookupBound (bounds : List (SigEntry × Nat)) (g : SigEntry) : Option Nat :=
  (bounds.find? (fun p => SigEntry.beq p.1 g)).map Prod.snd

/-- Look up a stack bound by function name in the output of `compileModule`. -/
def lookupFnBound (bounds : List (Sym × Nat)) (g : Sym) : Option Nat :=
  (bounds.find? (fun p => p.1 == g)).map Prod.snd

/-- Compute the required stack bound for a caller with frame size `F`, checking that every
reachable callee signature `(g, as, bs)` is present in `bounds`. -/
def calleesBound (F raBytes : Nat) (bounds : List (SigEntry × Nat)) :
    List SigEntry → Option Nat
  | [] => some F
  | g :: gs =>
    match lookupBound bounds g, calleesBound F raBytes bounds gs with
    | some bg, some rest => some (Nat.max (F + raBytes + bg) rest)
    | _, _ => none

/-- Compute and check the stack bound given pre-extracted `ext : Rega.Ext` and `h : I.Hints`. -/
def checkAndBoundExt (I : Isa) (raBytes : Nat) (exits : List Sym) (nX : Nat)
    (bounds : List (SigEntry × Nat)) (h : I.Hints) (ext : Rega.Ext) : Option Nat :=
  match calleesBound (Rega.effFrame I h ext) raBytes bounds ext.callees with
  | none => none
  | some n₁ =>
    if ext.exits.all (fun g => exits.contains g) then
      let n := if ext.exits.isEmpty then n₁ else Nat.max n₁ nX
      if Nat.ble (n + raBytes) (2 ^ 64) then some n else none
    else none

/-- Compute and check the stack bound of a pre-lowered mid-end function `mf = f.mid lt`. -/
def checkAndBoundMid (I : Isa) (raBytes : Nat) (exits : List Sym) (nX : Nat)
    (bounds : List (SigEntry × Nat)) (h : I.Hints) (mf : Fn) : Option Nat :=
  checkAndBoundExt I raBytes exits nX bounds h mf.ext

/-- Compute and check the stack bound of `f` under legalization target `lt` and hints `h`. -/
def checkAndBound (I : Isa) (lt : LegalTarget) (raBytes : Nat) (exits : List Sym) (nX : Nat)
    (bounds : List (SigEntry × Nat)) (f : Fn) (h : I.Hints) : Option Nat :=
  checkAndBoundMid I raBytes exits nX bounds h (f.mid lt)

/-- Compile an acyclic callee-first list of functions with externally supplied `hints`, checking
source support (`supportsSource`), callee bounds (by legalized `SigEntry`), exit targets, and
64-bit stack bounds incrementally. -/
def compileModule (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (extCallees : List (SigEntry × Nat)) (exits : List Sym) (nX : Nat) :
    List Fn → List I.Hints → Except String (List I.Directive × List (Sym × Nat))
  | [], [] => .ok ([], [])
  | f :: fs, h :: hs =>
    let ef := f.earlyOpt
    if ef.body.supportsSource lt then
      let mf := Fn.midFromEarly lt ef
      let ext := mf.ext
      match Rega.lowerFn I h ext mf,
            checkAndBoundExt I raBytes exits nX extCallees h ext with
      | .ok c, some b =>
        match compileModule I lt raBytes ((mf.sig, b) :: extCallees) exits nX fs hs with
        | .ok (cs, bs) => .ok (c ++ cs, (f.name, b) :: bs)
        | .error e => .error e
      | .error e, _ => .error s!"{f.name}: {e}"
      | _, none => .error s!"{f.name}: unknown callee, undeclared exit, or stack overflow"
    else
      .error s!"{f.name}: unsupported source op for target"
  | _, _ => .error "compileModule: fn/hints length mismatch"

/-! ## Cross-function label hygiene, fast `Nodup`, and kernel check helpers -/

/-- Check whether a character list contains adjacent `'.' :: 'L'`. -/
def hasDotLChars : List Char → Bool
  | '.' :: 'L' :: _ => true
  | _ :: cs => hasDotLChars cs
  | [] => false

/-- Structural check forbidding `".L"` anywhere in a symbol name, guaranteeing cross-function
disjointness of `Rega.lname f a` and `g` without scanning internal block labels. -/
def fnNameOk (s : Sym) : Bool :=
  !(hasDotLChars s.toList)

/-- Fast kernel-reducible `Nodup` check on strings (reversing each string once so suffixes like
`.L14` vs `.L15` mismatch on the first character without building `Decidable` proof terms). -/
def stringsNodup (ss : List String) : Bool :=
  listNodup (ss.map fun (s : String) => s.toList.reverse)

/-- Convenience `labelsNodup` checker built from `stringsNodup` for directive types with an
optional label extractor. -/
def labelsNodupBy {D : Type} (labelOf? : D → Option Sym) (prog : List D) : Bool :=
  stringsNodup (prog.filterMap labelOf?)

/-- Kernel-reducible result check using structural `fnNameOk` + `stringsNodup (fnNames ++ exits)`
so cross-function label uniqueness requires no O(L²) scan over internal `.L` block labels. -/
def checkCompileResult {D : Type} (label : Sym → D) (progSmall : List D → Bool)
    (res : Except String (List D × List (Sym × Nat)))
    (fnNames exits : List Sym) (maxBound : Nat) : Bool :=
  match res with
  | .error _ => false
  | .ok (code, bounds) =>
    let prog := code ++ exits.map label
    fnNames.all fnNameOk &&
    exits.all fnNameOk &&
    stringsNodup (fnNames ++ exits) &&
    progSmall prog &&
    bounds.all (fun p => Nat.ble p.2 maxBound) &&
    fnNames.all (fun nm => (lookupFnBound bounds nm).isSome)

/-- Variant of `checkCompileResult` using an explicit `labelsNodup` predicate over the emitted
directive stream (e.g. for targets that verify label uniqueness via `stringsNodup`). -/
def checkCompileResultWithLabels {D : Type} (label : Sym → D)
    (labelsNodup progSmall : List D → Bool)
    (res : Except String (List D × List (Sym × Nat)))
    (fnNames exits : List Sym) (maxBound : Nat) : Bool :=
  match res with
  | .error _ => false
  | .ok (code, bounds) =>
    let prog := code ++ exits.map label
    labelsNodup prog &&
    progSmall prog &&
    bounds.all (fun p => Nat.ble p.2 maxBound) &&
    fnNames.all (fun nm => (lookupFnBound bounds nm).isSome)

/-- Extract the directive stream from a `compileModule` result. -/
def extractCode {D : Type} : Except String (List D × List (Sym × Nat)) → List D
  | .ok (c, _) => c
  | .error _ => []

/-- Extract the stack-bound map from a `compileModule` result. -/
def extractBounds {D : Type} : Except String (List D × List (Sym × Nat)) → List (Sym × Nat)
  | .ok (_, b) => b
  | .error _ => []

attribute [irreducible] extractCode extractBounds

end LeanQbe.T
