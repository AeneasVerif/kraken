module

public import LeanQbe.T.OptFlatMem
public import LeanQbe.T.OptFlatMemLemmas
public import LeanQbe.T.MemLoad
public import LeanQbe.T.AssumeBits
public import LeanQbe.T.DivConst
public import LeanQbe.T.Examples.LitmusProgsProg
public import LeanQbe.T.Examples.Kissat.Plain1
meta import Lean
meta import LeanQbe.T.OptFlatMem
meta import LeanQbe.T.MemLoad
meta import LeanQbe.T.AssumeBits
meta import LeanQbe.T.DivConst
meta import LeanQbe.T.Flat
meta import LeanQbe.T.FlatDirect
meta import LeanQbe.T.Examples.LitmusProgsProg
meta import LeanQbe.T.Examples.Kissat.Plain1

/-!
# Differential Parity & Axiom Audit for `OptFlatMem` (`MainFlatMemParityTest`)

Verifies exact `TFlat` structural parity between `OptFlatMem.{memLoadFlat, assumeBitsFlat,
divConstFlat}` and `reifyFunc (Func.* (denoteFunc tf))` across rich native fixtures,
Litmus benchmarks, and Kissat schedule functions, and audits `OptFlatMemLemmas` axioms (`std3`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.MainFlatMemParityTest

open LeanQbe.T

/-- Reify an arbitrary closed `Fn` into `TFlatFn`. -/
def fnToTFlat (f : Fn) : TFlatFn :=
  ⟨f.name, f.as, f.rs, reifyFunc f.body⟩

/-- Exact structural equality on `Tup (Arg K) ts`. -/
def tupArgEq : {ts : List Ty} → Tup (Arg K) ts → Tup (Arg K) ts → Bool
  | [], (), () => true
  | _ :: _, (a, as), (b, bs) => decide (a = b) && tupArgEq as bs

/-- Exact structural equality on `Op K ts`. -/
def opEq {ts : List Ty} (a b : Op K ts) : Bool :=
  match a, b with
  | { sig := sa, code := ca, args := aa }, { sig := sb, code := cb, args := ab } =>
    match listTyDecEq sa sb with
    | isTrue rfl => decide (ca = cb) && tupArgEq aa ab
    | isFalse _ => false

mutual
/-- Exact structural equality on `TFlat rs`. -/
def tflatEq {rs : List Ty} : TFlat rs → TFlat rs → Bool
  | .let_ (ts := ts1) op1 k1, .let_ (ts := ts2) op2 k2 =>
    match listTyDecEq ts1 ts2 with
    | isTrue rfl => opEq op1 op2 && tflatEq k1 k2
    | isFalse _ => false
  | .load t1 a1 k1, .load t2 a2 k2 =>
    match tyDecEq t1 t2 with
    | isTrue rfl => decide (a1 = a2) && tflatEq k1 k2
    | isFalse _ => false
  | .store (t := t1) v1 a1 k1, .store (t := t2) v2 a2 k2 =>
    match tyDecEq t1 t2 with
    | isTrue rfl => decide (v1 = v2) && decide (a1 = a2) && tflatEq k1 k2
    | isFalse _ => false
  | .call f1 (as := as1) bs1 args1 k1, .call f2 (as := as2) bs2 args2 k2 =>
    f1 == f2 &&
      match listTyDecEq as1 as2, listTyDecEq bs1 bs2 with
      | isTrue rfl, isTrue rfl => tupArgEq args1 args2 && tflatEq k1 k2
      | _, _ => false
  | .jnz c1 t1 e1, .jnz c2 t2 e2 =>
    decide (c1 = c2) && tflatEq t1 t2 && tflatEq e1 e2
  | .jump (ts := ts1) j1 a1, .jump (ts := ts2) j2 a2 =>
    j1 == j2 &&
      match listTyDecEq ts1 ts2 with
      | isTrue rfl => tupArgEq a1 a2
      | isFalse _ => false
  | .ret v1, .ret v2 => tupArgEq v1 v2
  | .exit (as := as1) f1 a1, .exit (as := as2) f2 a2 =>
    f1 == f2 &&
      match listTyDecEq as1 as2 with
      | isTrue rfl => tupArgEq a1 a2
      | isFalse _ => false
  | .hlt, .hlt => true
  | .group (sig := s1) b1 k1, .group (sig := s2) b2 k2 =>
    match (decEq s1 s2 : Decidable (s1 = s2)) with
    | isTrue rfl => tblocksEq b1 b2 && tflatEq k1 k2
    | isFalse _ => false
  | _, _ => false

/-- Exact structural equality on `TBlocks rs sig`. -/
def tblocksEq {rs : List Ty} : {sig : List (List Ty)} →
    TBlocks rs sig → TBlocks rs sig → Bool
  | _, .nil, .nil => true
  | _, .cons b1 bs1, .cons b2 bs2 =>
    tflatEq b1 b2 && tblocksEq bs1 bs2
end

/-- Rich memory fixture testing CSE across `copy`+`add` aliasing, store-to-load forwarding,
disjoint store preservation, overlapping store invalidation, `.group` summary filtering, and
`.call` cache flush. -/
def memCseStoreForwardFlat : TFlatFn :=
  { name := "mem_cse_store_forward"
    as := [i64, i64]
    rs := [i64]
    body :=
      .let_ ⟨.copy i64, (.var 1, ())⟩ <|
      .let_ ⟨.add i64, (.var 0, .imm 8#64, ())⟩ <|
      .let_ ⟨.add i64, (.var 3, .imm 8#64, ())⟩ <|
      .load i64 (.var 1) <|
      .load i64 (.var 1) <|
      .let_ ⟨.add i64, (.var 6, .imm 16#64, ())⟩ <|
      .store (t := i64) (.var 6) (.var 0) <|
      .let_ ⟨.add i64, (.var 7, .imm 24#64, ())⟩ <|
      .let_ ⟨.trunc 64 32, (.var 7, ())⟩ <|
      .store (t := i32) (.var 0) (.var 1) <|
      .load i64 (.var 2) <|
      .let_ ⟨.add i64, (.var 10, .imm 18#64, ())⟩ <|
      .store (t := i32) (.var 2) (.var 0) <|
      .load i64 (.var 4) <|
      .group (sig := [[i64]])
        (.cons
          (.let_ ⟨.add i64, (.var 13, .imm 40#64, ())⟩ <|
           .store (t := i32) (.var 5) (.var 0) <|
           .ret (.var 1, ()))
          .nil)
        (.load i64 (.var 9) <|
         .call "ext_barrier" (as := [i64]) [i64] (.var 0, ()) <|
         .load i64 (.var 11) <|
         .let_ ⟨.add i64, (.var 0, .var 3, ())⟩ <|
         .let_ ⟨.add i64, (.var 0, .var 6, ())⟩ <|
         .let_ ⟨.add i64, (.var 0, .var 11, ())⟩ <|
         .let_ ⟨.cmp .eq i64, (.var 0, .imm 0#64, ())⟩ <|
         .jnz (.var 0) (.jump (ts := [i64]) 0 (.var 1, ())) (.ret (.var 1, ()))) }

/-- Known-bits & branch-implied fixture exercising `andKeeps`, `andKills`, `copy`, `or`, `lshr`,
`cmp`, `ofBool`, `select`, and `.jnz` path-sensitive simplification. -/
def assumeBitsComplexFlat : TFlatFn :=
  { name := "assume_bits_complex"
    as := [i64, i64]
    rs := [i64]
    body :=
      .let_ ⟨.and i64, (.var 1, .imm 255#64, ())⟩ <|
      .let_ ⟨.and i64, (.var 0, .imm 255#64, ())⟩ <|
      .let_ ⟨.and i64, (.var 0, .imm 65280#64, ())⟩ <|
      .let_ ⟨.copy i64, (.var 0, ())⟩ <|
      .let_ ⟨.or i64, (.var 3, .var 0, ())⟩ <|
      .let_ ⟨.lshr i64, (.var 0, .imm 4#64, ())⟩ <|
      .let_ ⟨.cmp .eq i64, (.var 5, .imm 7#64, ())⟩ <|
      .jnz (.var 0)
        (.let_ ⟨.cmp .eq i64, (.var 6, .imm 7#64, ())⟩ <|
         .let_ ⟨.ofBool 64, (.var 0, ())⟩ <|
         .let_ ⟨.add i64, (.var 0, .var 3, ())⟩ <|
         .ret (.var 0, ()))
        (.let_ ⟨.cmp .ne i64, (.var 6, .imm 7#64, ())⟩ <|
         .let_ ⟨.select i64, (.var 0, .var 2, .var 8, ())⟩ <|
         .ret (.var 0, ())) }

/-- Full `divConstFlat` fixture exercising 32/64-bit `udiv`, `urem`, `sdiv`, `srem` with `d=0`,
`d=1`, `d=-1`, `pow2` (`m=1` and `m>1`), `uNoAddCert`, `uAddShiftCert`, and signed magic pos/neg. -/
def divConstAllCasesFlat : TFlatFn :=
  { name := "div_const_all_cases"
    as := [i32, i64]
    rs := [i64]
    body :=
      .let_ ⟨.udiv 32, (.var 1, .imm 0#32, ())⟩ <|
      .let_ ⟨.udiv 32, (.var 2, .imm 1#32, ())⟩ <|
      .let_ ⟨.udiv 32, (.var 3, .imm 4#32, ())⟩ <|
      .let_ ⟨.udiv 32, (.var 4, .imm 3#32, ())⟩ <|
      .let_ ⟨.urem 32, (.var 5, .imm 7#32, ())⟩ <|
      .let_ ⟨.sdiv 32, (.var 6, .imm (-1#32), ())⟩ <|
      .let_ ⟨.sdiv 32, (.var 7, .imm 2#32, ())⟩ <|
      .let_ ⟨.sdiv 32, (.var 8, .imm (-5#32), ())⟩ <|
      .let_ ⟨.srem 32, (.var 9, .imm 3#32, ())⟩ <|
      .let_ ⟨.add i32, (.var 0, .var 1, ())⟩ <|
      .let_ ⟨.add i32, (.var 0, .var 3, ())⟩ <|
      .let_ ⟨.add i32, (.var 0, .var 6, ())⟩ <|
      .let_ ⟨.add i32, (.var 0, .var 8, ())⟩ <|
      .let_ ⟨.add i32, (.var 0, .var 10, ())⟩ <|
      .let_ ⟨.add i32, (.var 0, .var 12, ())⟩ <|
      .let_ ⟨.add i32, (.var 0, .var 14, ())⟩ <|
      .let_ ⟨.zext 32 64, (.var 0, ())⟩ <|
      .let_ ⟨.udiv 64, (.var 17, .imm 10#64, ())⟩ <|
      .let_ ⟨.urem 64, (.var 18, .imm 8#64, ())⟩ <|
      .let_ ⟨.sdiv 64, (.var 19, .imm (-3#64), ())⟩ <|
      .let_ ⟨.srem 64, (.var 20, .imm 8#64, ())⟩ <|
      .let_ ⟨.add i64, (.var 0, .var 1, ())⟩ <|
      .let_ ⟨.add i64, (.var 0, .var 3, ())⟩ <|
      .let_ ⟨.add i64, (.var 0, .var 5, ())⟩ <|
      .let_ ⟨.add i64, (.var 0, .var 7, ())⟩ <|
      .ret (.var 0, ()) }

/-- No-div/rem fixture verifying `divConstFlat`'s `hasDivRem = false` fast-path. -/
def noDivFastFlat : TFlatFn :=
  { name := "no_div_fast"
    as := [i64, i64]
    rs := [i64]
    body :=
      .let_ ⟨.add i64, (.var 1, .var 0, ())⟩ <|
      .let_ ⟨.cmp .ult i64, (.var 0, .imm 100#64, ())⟩ <|
      .jnz (.var 0) (.ret (.var 1, ())) (.ret (.var 2, ())) }

theorem memCseStoreForwardFlat_wf : memCseStoreForwardFlat.wfCheck = true := by decide
theorem assumeBitsComplexFlat_wf : assumeBitsComplexFlat.wfCheck = true := by decide
theorem divConstAllCasesFlat_wf : divConstAllCasesFlat.wfCheck = true := by decide
theorem noDivFastFlat_wf : noDivFastFlat.wfCheck = true := by decide

theorem memCseStoreForwardFlat_parity :
    OptFlatMem.memLoadFlat memCseStoreForwardFlat.as memCseStoreForwardFlat.body =
      reifyFunc (Func.memLoad memCseStoreForwardFlat.toFn.body) :=
  OptFlatMem.memLoadFlat_eq _ memCseStoreForwardFlat_wf

theorem assumeBitsComplexFlat_parity :
    OptFlatMem.assumeBitsFlat assumeBitsComplexFlat.as assumeBitsComplexFlat.body =
      reifyFunc (Func.assumeBits assumeBitsComplexFlat.toFn.body) :=
  OptFlatMem.assumeBitsFlat_eq _ assumeBitsComplexFlat_wf

theorem divConstAllCasesFlat_parity :
    OptFlatMem.divConstFlat divConstAllCasesFlat.as divConstAllCasesFlat.body =
      reifyFunc (Func.divConst divConstAllCasesFlat.toFn.body) :=
  OptFlatMem.divConstFlat_eq _ divConstAllCasesFlat_wf

def parityFixtures : List TFlatFn :=
  [ memCseStoreForwardFlat
  , assumeBitsComplexFlat
  , divConstAllCasesFlat
  , noDivFastFlat
  , fnToTFlat Examples.Litmus.tracer
  , fnToTFlat Examples.Litmus.ifelse
  , fnToTFlat Examples.Litmus.sumto
  , fnToTFlat Examples.Litmus.nested ]

def checkMemPassParity : IO Unit := do
  let kissatFns : List TFlatFn :=
    (Examples.Kissat.Plain.plain1Module.fns.take 2).map fnToTFlat
  let allFns := parityFixtures ++ kissatFns
  for f in allFns do
    if !f.wfCheck then
      throw <| IO.userError s!"wfCheck failed for {f.name}"
    let fn := f.toFn
    let mlFlat := OptFlatMem.memLoadFlat f.as f.body
    let mlPho := reifyFunc (Func.memLoad fn.body)
    if !tflatEq mlFlat mlPho then
      throw <| IO.userError s!"memLoadFlat mismatch on {f.name}"
    if !mlFlat.wfCheck (pushTypes f.as []) [] then
      throw <| IO.userError s!"memLoadFlat wfCheck failed on {f.name}"
    let abFlat := OptFlatMem.assumeBitsFlat f.as f.body
    let abPho := reifyFunc (Func.assumeBits fn.body)
    if !tflatEq abFlat abPho then
      throw <| IO.userError s!"assumeBitsFlat mismatch on {f.name}"
    if !abFlat.wfCheck (pushTypes f.as []) [] then
      throw <| IO.userError s!"assumeBitsFlat wfCheck failed on {f.name}"
    let dcFlat := OptFlatMem.divConstFlat f.as f.body
    let dcPho := reifyFunc (Func.divConst fn.body)
    if !tflatEq dcFlat dcPho then
      throw <| IO.userError s!"divConstFlat mismatch on {f.name}"
    if !dcFlat.wfCheck (pushTypes f.as []) [] then
      throw <| IO.userError s!"divConstFlat wfCheck failed on {f.name}"
  if tflatEq (OptFlatMem.memLoadFlat memCseStoreForwardFlat.as memCseStoreForwardFlat.body)
      memCseStoreForwardFlat.body then
    throw <| IO.userError "memLoadFlat failed to simplify memCseStoreForwardFlat"
  if tflatEq (OptFlatMem.assumeBitsFlat assumeBitsComplexFlat.as assumeBitsComplexFlat.body)
      assumeBitsComplexFlat.body then
    throw <| IO.userError "assumeBitsFlat failed to simplify assumeBitsComplexFlat"
  if tflatEq (OptFlatMem.divConstFlat divConstAllCasesFlat.as divConstAllCasesFlat.body)
      divConstAllCasesFlat.body then
    throw <| IO.userError "divConstFlat failed to rewrite divConstAllCasesFlat"
  if !tflatEq (OptFlatMem.divConstFlat noDivFastFlat.as noDivFastFlat.body)
      noDivFastFlat.body then
    throw <| IO.userError "divConstFlat modified noDivFastFlat"
  IO.println s!"OK (OptFlatMem parity): {allFns.length} fns x 3 passes, 0 diffs"

#eval checkMemPassParity

#print axioms LeanQbe.T.OptFlatMem.memLoadFlat_eq
#print axioms LeanQbe.T.OptFlatMem.memLoadFlat_wfCheck
#print axioms LeanQbe.T.OptFlatMem.denoteFunc_memLoadFlat
#print axioms LeanQbe.T.OptFlatMem.memLoadFlat_toFn
#print axioms LeanQbe.T.OptFlatMem.assumeBitsFlat_eq
#print axioms LeanQbe.T.OptFlatMem.assumeBitsFlat_wfCheck
#print axioms LeanQbe.T.OptFlatMem.denoteFunc_assumeBitsFlat
#print axioms LeanQbe.T.OptFlatMem.assumeBitsFlat_toFn
#print axioms LeanQbe.T.OptFlatMem.divConstFlat_eq
#print axioms LeanQbe.T.OptFlatMem.divConstFlat_wfCheck
#print axioms LeanQbe.T.OptFlatMem.denoteFunc_divConstFlat
#print axioms LeanQbe.T.OptFlatMem.divConstFlat_toFn
#print axioms memCseStoreForwardFlat_parity
#print axioms assumeBitsComplexFlat_parity
#print axioms divConstAllCasesFlat_parity

end LeanQbeTest.T.MainFlatMemParityTest
