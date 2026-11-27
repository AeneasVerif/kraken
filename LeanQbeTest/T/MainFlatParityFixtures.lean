module

public import LeanQbe.T.MainFlatLemmas
public import LeanQbe.T.Examples.LitmusProgsProg
public import LeanQbe.T.Examples.LratBytesProg
public import LeanQbe.T.Examples.Kissat.Plain1
meta import LeanQbe.T.MainFlat
meta import LeanQbe.T.Examples.LitmusProgsProg
meta import LeanQbe.T.Examples.LratBytesProg
meta import LeanQbe.T.Examples.Kissat.Plain1

/-!
# Shared Arch-Neutral Differential Parity Fixtures (`MainFlatParityFixtures`)

Holds shared pure-generic `TFlatFn` and `Fn` test suites plus differential bit-exactness
and native wall-time benchmark helpers shared across `MainFlatParityTest` (SysV x64) and
`MainFlatParityArm64Test` (AArch64) without co-importing opposing Kraken backend crates.
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.MainFlatParityFixtures

open LeanQbe.T

/-- Reify an arbitrary closed `Fn` into `TFlatFn`. -/
@[expose] def fnToTFlat (f : Fn) : TFlatFn :=
  ⟨f.name, f.as, f.rs, reifyFunc f.body⟩

/-- Direct native `TFlatFn` exercising `.udiv`/`.urem`/`.sdiv`/`.srem` constants + 2-return
epilogue merging (`TFlat.mergeRets`, `divConstFlat`). -/
@[expose] def divModFlat : TFlatFn :=
  { name := "div_mod_flat"
    as := [i64]
    rs := [i64]
    body :=
      .let_ ⟨.udiv 64, (.var 0, .imm 10#64, ())⟩ <|
      .let_ ⟨.urem 64, (.var 1, .imm 7#64, ())⟩ <|
      .let_ ⟨.sdiv 64, (.var 2, .imm (-3#64), ())⟩ <|
      .let_ ⟨.srem 64, (.var 3, .imm 13#64, ())⟩ <|
      .let_ ⟨.add i64, (.var 3, .var 2, ())⟩ <|
      .let_ ⟨.add i64, (.var 2, .var 1, ())⟩ <|
      .let_ ⟨.cmp .ult i64, (.var 6, .imm 5#64, ())⟩ <|
      .jnz (.var 0) (.ret (.var 2, ())) (.ret (.var 1, ())) }

/-- Direct native `TFlatFn` exercising `.hlt` assumption elimination + loop over `[0..x)`. -/
@[expose] def assumeLoopFlat : TFlatFn :=
  { name := "assume_loop_flat"
    as := [i64]
    rs := [i64]
    body :=
      .let_ ⟨.cmp .eq i64, (.var 0, .imm 0#64, ())⟩ <|
      .jnz (.var 0) .hlt <|
      .group (sig := [[i64, i64]])
        (.cons
          (.let_ ⟨.cmp .ult i64, (.var 1, .var 3, ())⟩ <|
           .jnz (.var 0)
             (.let_ ⟨.add i64, (.var 2, .imm 1#64, ())⟩ <|
              .let_ ⟨.add i64, (.var 2, .var 3, ())⟩ <|
              .jump (ts := [i64, i64]) 0 (.var 1, .var 0, ()))
             (.ret (.var 1, ())))
          .nil)
        (.jump (ts := [i64, i64]) 0 (.imm 0#64, .imm 0#64, ())) }

/-- Native + Litmus parity module verified in the Lean kernel (`divConst`, `assumeElim`,
`mergeRets`, `tracer`, `ifelse`, `sumto`, `nested`). -/
@[expose] def litmusTFlatMod : List TFlatFn :=
  [ divModFlat
  , assumeLoopFlat
  , fnToTFlat Examples.Litmus.tracer
  , fnToTFlat Examples.Litmus.ifelse
  , fnToTFlat Examples.Litmus.sumto
  , fnToTFlat Examples.Litmus.nested ]

theorem divModFlat_wf : divModFlat.wfCheck = true := by decide
theorem assumeLoopFlat_wf : assumeLoopFlat.wfCheck = true := by decide
theorem litmusTFlatMod_wf : litmusTFlatMod.all TFlatFn.wfCheck = true := by decide

@[expose] def litmusAllTFlatMod : List TFlatFn :=
  Examples.Litmus.allFns.map fnToTFlat

@[expose] def lratBytesTFlatMod : List TFlatFn :=
  Examples.LratBytes.lratBytesFns.map fnToTFlat

@[expose] def plain1TFlatMod : List TFlatFn :=
  Examples.Kissat.Plain.plain1Module.fns.map fnToTFlat

@[expose] def firstByteDiff (a b : ByteArray) :
    Option (Nat × Option UInt8 × Option UInt8) := Id.run do
  let n := Nat.min a.size b.size
  for i in [:n] do
    if a[i]! != b[i]! then
      return some (i, some a[i]!, some b[i]!)
  if a.size != b.size then
    return some (n, if n < a.size then some a[n]! else none,
      if n < b.size then some b[n]! else none)
  return none

@[expose] def formatSpeedup (flatNs phoNs : Nat) : String :=
  if flatNs == 0 then "inf"
  else
    let tenths := (phoNs * 10 + flatNs / 2) / flatNs
    s!"{tenths / 10}.{tenths % 10}x"

@[expose] def checkSuiteParity (tag suiteName : String) (I : Isa) (lt : LegalTarget)
    (raBytes : Nat) (extCallees : List (SigEntry × Nat)) (exits : List Sym)
    (render : List I.Directive → String) (flatFns : List TFlatFn)
    (benchIters : Nat := 1) : IO (Nat × Nat) := do
  let fns : List Fn := flatFns.map TFlatFn.toFn
  for ff in flatFns do
    if !ff.wfCheck then
      throw <| IO.userError s!"{tag}/{suiteName}: wfCheck failed for {ff.name}"
  let hints := fns.map (Fn.computeHints I lt)
  let (flatCode, flatBounds) ← IO.ofExcept
    (compileModuleFlat I lt raBytes extCallees exits 0 flatFns hints)
  let (phoCode, phoBounds) ← IO.ofExcept
    (compileModule I lt raBytes extCallees exits 0 fns hints)
  if flatBounds != phoBounds then
    throw <| IO.userError
      s!"{tag}/{suiteName}: bounds mismatch: {flatBounds} vs {phoBounds}"
  let flatBytes := (render flatCode).toUTF8
  let phoBytes := (render phoCode).toUTF8
  if let some (pos, bf, bp) := firstByteDiff flatBytes phoBytes then
    throw <| IO.userError s!"{tag}/{suiteName}: assembly diff at byte {pos}: {bf} vs {bp}"
  for ((ff, fn), h) in (flatFns.zip fns).zip hints do
    let fDirs ← IO.ofExcept (compileFlatFn I lt h ff)
    let pDirs ← IO.ofExcept (compileFn I lt h fn)
    let fB := (render fDirs).toUTF8
    let pB := (render pDirs).toUTF8
    if let some (pos, bf, bp) := firstByteDiff fB pB then
      throw <| IO.userError
        s!"{tag}/{suiteName}: per-fn '{fn.name}' diff at byte {pos}: {bf} vs {bp}"
  let tf0 ← IO.monoNanosNow
  let mut flatAcc := 0
  for i in [:benchIters] do
    let inFns := if tf0 == 0 && i == 999999 then [] else flatFns
    match compileModuleFlat I lt raBytes extCallees exits 0 inFns hints with
    | .ok (c, _) => flatAcc := flatAcc + c.length
    | .error e => throw <| IO.userError s!"{tag}/{suiteName}: flat bench error: {e}"
  let tf1 ← IO.monoNanosNow
  let tp0 ← IO.monoNanosNow
  let mut phoAcc := 0
  for i in [:benchIters] do
    let inFns := if tp0 == 0 && i == 999999 then [] else fns
    match compileModule I lt raBytes extCallees exits 0 inFns hints with
    | .ok (c, _) => phoAcc := phoAcc + c.length
    | .error e => throw <| IO.userError s!"{tag}/{suiteName}: pho bench error: {e}"
  let tp1 ← IO.monoNanosNow
  if flatAcc != phoAcc then
    throw <| IO.userError s!"{tag}/{suiteName}: bench dir count mismatch"
  let flatNs := tf1 - tf0
  let phoNs := tp1 - tp0
  let flatUs := flatNs / 1000
  let phoUs := phoNs / 1000
  let spd := formatSpeedup flatNs phoNs
  IO.println (s!"OK ({tag}/{suiteName}): {fns.length} fns, {flatCode.length} dirs, " ++
    s!"{flatBytes.size} B, 0 diff | {benchIters}x flat={flatUs}us vs pho={phoUs}us ({spd})")
  pure (flatNs, phoNs)

@[expose] def checkTargetParity (tag : String) (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (render : List I.Directive → String) : IO Unit := do
  let coreFns : List TFlatFn := litmusTFlatMod ++ (plain1TFlatMod.take 2)
  let _ ← checkSuiteParity tag "core" I lt raBytes [] [] render coreFns 10
  let (f1, p1) ← checkSuiteParity tag "litmus_all" I lt raBytes [] ["fail"] render
    litmusAllTFlatMod 10
  let (f2, p2) ← checkSuiteParity tag "lrat_bytes" I lt raBytes [] [] render
    lratBytesTFlatMod 5
  let (f3, p3) ← checkSuiteParity tag "plain1" I lt raBytes [] [] render
    plain1TFlatMod 5
  let totFlatMs := (f1 + f2 + f3) / 1000000
  let totPhoMs := (p1 + p2 + p3) / 1000000
  let spd := formatSpeedup (f1 + f2 + f3) (p1 + p2 + p3)
  let totFns := litmusAllTFlatMod.length + lratBytesTFlatMod.length + plain1TFlatMod.length
  IO.println (s!"OK ({tag} total): {totFns} fns across 3 suites, 0 diff | " ++
    s!"flat={totFlatMs}ms vs pho={totPhoMs}ms ({spd})")

end LeanQbeTest.T.MainFlatParityFixtures
