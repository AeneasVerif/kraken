module

public import LeanQbe.T.MainFlatLemmas
public import LeanQbe.T.Examples.LitmusProgsProg
public import LeanQbe.T.Examples.Kissat.FullM7FidelitySched
meta import LeanQbe.T.MainFlat
meta import LeanQbe.T.Examples.LitmusProgsProg
meta import LeanQbe.T.Examples.Kissat.FullM7FidelitySched

/-!
# Shared Arch-Neutral Differential Parity Fixtures (`MainFlatParityFixtures`)

Holds shared pure-generic `TFlatFn` and `Fn` test suites plus differential bit-exactness
helpers shared across `MainFlatParityTest` (SysV x64) and `MainFlatParityArm64Test` (AArch64)
without co-importing opposing Kraken backend crates.
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

@[expose] def checkTargetParity (tag : String) (I : Isa) (lt : LegalTarget) (raBytes : Nat)
    (render : List I.Directive → String) : IO Unit := do
  let kissatFns : List TFlatFn :=
    (Examples.Kissat.FullM7FidelitySched.fidSchedFns.take 2).map fnToTFlat
  let flatFns : List TFlatFn := litmusTFlatMod ++ kissatFns
  let fns : List Fn := flatFns.map TFlatFn.toFn
  for ff in flatFns do
    if !ff.wfCheck then
      throw <| IO.userError s!"{tag}: wfCheck failed for {ff.name}"
  let hints := fns.map (Fn.computeHints I lt)
  let (flatCode, flatBounds) ← IO.ofExcept
    (compileModuleFlat I lt raBytes [] [] 0 flatFns hints)
  let (phoCode, phoBounds) ← IO.ofExcept
    (compileModule I lt raBytes [] [] 0 fns hints)
  if flatBounds != phoBounds then
    throw <| IO.userError s!"{tag}: bounds mismatch: {flatBounds} vs {phoBounds}"
  let flatBytes := (render flatCode).toUTF8
  let phoBytes := (render phoCode).toUTF8
  if let some (pos, bf, bp) := firstByteDiff flatBytes phoBytes then
    throw <| IO.userError s!"{tag}: assembly diff at byte {pos}: {bf} vs {bp}"
  for ((ff, fn), h) in (flatFns.zip fns).zip hints do
    let fDirs ← IO.ofExcept (compileFlatFn I lt h ff)
    let pDirs ← IO.ofExcept (compileFn I lt h fn)
    if let some (pos, bf, bp) := firstByteDiff (render fDirs).toUTF8 (render pDirs).toUTF8 then
      throw <| IO.userError s!"{tag}: per-fn '{fn.name}' diff at byte {pos}: {bf} vs {bp}"
  IO.println s!"OK ({tag}): {fns.length} fns, {flatCode.length} dirs, {flatBytes.size} B, 0 diff"

end LeanQbeTest.T.MainFlatParityFixtures
