module

public import LeanQbe.T.LeanLCNF.LExprSem
public import LeanQbe.T.LeanLCNF.Lower1
public import LeanQbe.T.LeanLCNF.LcnfC0Demo
public import LeanQbe.T.LeanLCNF.LcnfC0LoopDemo
public import LeanQbe.T.LeanLCNF.LcnfC0ArrayDemo
public import LeanQbe.T.LeanLCNF.LcnfC0RecDemo
public import LeanQbe.T.LeanLCNF.LcnfC0TreeDemo
public import LeanQbe.T.LeanLCNF.LcnfC0MutRecDemo
public import LeanQbe.T.Bootstrap0.Splice0
meta import LeanQbe.T.LeanLCNF.Lower1
meta import LeanQbe.T.Bootstrap0.Splice0

/-!
# Shard L1 Verification: Total Kernel-Reducible Lowering, `_lower` Theorems, and `LExprSem`

* `splitDot` parity with `String.splitOn "."` (`#guard`s).
* Kernel reduction of `lowerModule` (`decide +kernel`, `splice_lcnf_tflat!` `_lower` + `_perm`)
  on hand-written `LcModule`s covering `Nat.add`, `cases`, `jp`/`jmp`, `lit (.str / .nat)`,
  `pap`/`ap`, and `symsNodup`.
* Exact kernel-checked `_lower` / `_perm` witnesses across all six `LcnfC0*Demo` modules.
* Non-vacuity `LExpr.wp` + `lExprToTFlat_func_sound` + `TFlatFn.wp_of_lExpr` proofs on concrete
  straight-line and `.group`/`.jnz`/`.jump` `LExpr` programs (`<= std3`, `0` `sorry`/`axiom`).
-/

set_option autoImplicit false

public section

namespace LeanQbeTest.T.LcnfSemL1Test

open LeanQbe.T hiding TFlatFn
open LeanQbe.T.LeanLCNF
open LeanQbe.T.Frontend.C0 (LExpr LVar LArg LOp LFlatCtx TFlatFn lExprToTFlat VEnv JEnv)

/-! ## 1. `splitDot` parity with `String.splitOn "."` -/

private def dotSamples : List String :=
  [ "Nat.add", "UInt64.ofBitVec", "String.Pos.Raw.get", "getObjTagNat"
  , "System.Platform.getNumBits", "", ".", ".a.", "a..b", "plain" ]

#guard dotSamples.all fun s => splitDot s == s.splitOn "."

theorem mangle_nonascii_rfl : mangleLc "Sha256.σ₀" = "l_Sha256_u3c3_u2080_" := by
  rfl

/-! ## 2. Kernel reduction of `lowerModule` (`decide +kernel`, `_lower`, `_perm`) -/

/-- Hand-written `LcModule` exercising `fap` extern (`Nat.add`) and `ret`. -/
@[expose] def tinyAddLcMod : LcModule :=
  { name := "tinyAdd"
    roots := ["Tiny.add"]
    decls :=
      [ { name := "Tiny.add"
          params := [{ id := 0, ty := .object }, { id := 1, ty := .object }]
          retTy := .object
          body := .let_ 2 .object (.fap "Nat.add" [.var 0, .var 1]) (.ret (.var 2)) } ]
    externs := [{ name := "Nat.add", params := [.object, .object], retTy := .object }]
    snaps := [] }

/-- Hand-written `LcModule` exercising `cases`, `jp`/`jmp`, `lit` (`.str` and big `.nat`), and
`pap`/`ap` (`lcnf_apply_1` generation + `LEnv` assoc-list lookups). -/
@[expose] def tinyBranchLcMod : LcModule :=
  { name := "tinyBranch"
    roots := ["Tiny.branch"]
    decls :=
      [ { name := "Tiny.id"
          params := [{ id := 0, ty := .object }]
          retTy := .object
          body := .ret (.var 0) }
      , { name := "Tiny.branch"
          params := [{ id := 0, ty := .tobject }, { id := 1, ty := .object }]
          retTy := .object
          body :=
            .jp 9 [{ id := 2, ty := .object }] (.ret (.var 2)) <|
            .cases 0
              [ (.ctor 0 "Zero",
                  .let_ 3 .object (.lit (.str "zero")) (.jmp 9 [.var 3]))
              , (.dflt,
                  .let_ 4 .object (.lit (.nat (2 ^ 64 + 7))) <|
                  .let_ 5 .object (.pap "Tiny.id" []) <|
                  .let_ 6 .object (.ap 5 [.var 4]) (.jmp 9 [.var 6])) ] } ]
    externs := []
    snaps := [] }

theorem tinyAdd_isOk : (lowerModule tinyAddLcMod).isOk = true := by
  decide +kernel

theorem tinyBranch_isOk : (lowerModule tinyBranchLcMod).isOk = true := by
  decide +kernel

splice_lcnf_tflat! tinyAddTfs tinyAddLcMod
splice_lcnf_tflat! tinyBranchTfs tinyBranchLcMod

theorem tinyAdd_lower_perm :
    ∃ tfs, lowerModule tinyAddLcMod = .ok tfs ∧ tinyAddTfs.Perm tfs :=
  ⟨tinyAddTfs_raw, tinyAddTfs_lower, tinyAddTfs_perm⟩

theorem tinyBranch_lower_perm :
    ∃ tfs, lowerModule tinyBranchLcMod = .ok tfs ∧ tinyBranchTfs.Perm tfs :=
  ⟨tinyBranchTfs_raw, tinyBranchTfs_lower, tinyBranchTfs_perm⟩

/-! ## 3. Demo `_lower` and `_perm` theorem composition checks -/

theorem demoNatStr_lower_perm :
    ∃ tfs, lowerModule demoNatStrLcMod = .ok tfs ∧ demoNatStrTfs.Perm tfs :=
  ⟨demoNatStrTfs_raw, demoNatStrTfs_lower, demoNatStrTfs_perm⟩

theorem factLoop_lower_perm :
    ∃ tfs, lowerModule factLoopLcMod = .ok tfs ∧ factLoopTfs.Perm tfs :=
  ⟨factLoopTfs_raw, factLoopTfs_lower, factLoopTfs_perm⟩

theorem arrayDemo_lower_perm :
    ∃ tfs, lowerModule arrayDemoLcMod = .ok tfs ∧ arrayDemoTfs.Perm tfs :=
  ⟨arrayDemoTfs_raw, arrayDemoTfs_lower, arrayDemoTfs_perm⟩

theorem all_scc_demos_lower :
    lowerModule recDemoLcMod = .ok recDemoTfs ∧
    lowerModule treeDemoLcMod = .ok treeDemoTfs ∧
    lowerModule mutRecDemoLcMod = .ok mutRecDemoTfs :=
  ⟨recDemoTfs_lower, treeDemoTfs_lower, mutRecDemoTfs_lower⟩

/-! ## 4. Non-vacuity of `LExpr.wp` and `lExprToTFlat_func_sound` -/

/-- Parameter list `(x : i64, y : i64)` for the straight-line `LExpr` test. -/
@[expose] def tinyAddParams : List LVar :=
  [{ id := 0, name := "x", ty := i64 }, { id := 1, name := "y", ty := i64 }]

/-- Straight-line `LExpr`: `r := x + y; ret r`. -/
@[expose] def tinyAddLExpr : LExpr :=
  .let_ { rs := [i64], sig := [i64, i64], code := .add i64, args := [.var 0 i64, .var 1 i64] }
    [{ id := 2, name := "r", ty := i64 }]
    (.ret [i64] [.var 2 i64])

/-- De Bruijn `TFlat` lowered from `tinyAddLExpr`. -/
@[expose] def tinyAddTf : TFlat [i64] :=
  .let_ (op2 (.add i64) (.var 1) (.var 0)) (.ret (.var 0, ()))

theorem tinyAddLExpr_toFlat :
    lExprToTFlat (({} : LFlatCtx).pushVars tinyAddParams) [i64] tinyAddLExpr = .ok tinyAddTf := by
  rfl

theorem tinyAdd_tflat_wp (x y : BitVec 64) (m : Mem 64) :
    Func.wp (fun _ _ _ _ _ _ _ => False)
      (denoteFunc (as := [i64, i64]) tinyAddTf) (x, y, ()) m
      (fun r m' => r = (x + y, ()) ∧ m' = m) (fun _ _ _ _ => False) := by
  refine Frontend.C0.lExprToTFlat_func_sound tinyAddLExpr_toFlat _ (x, y, ()) m _ _ ?_
  refine ⟨rfl, (x, y, ()), rfl, ?_⟩
  exact ⟨rfl, (x + y, ()), rfl, rfl, rfl⟩

/-- Parameter list `(c : bool, x : i64, y : i64)` for the `.group`/`.jnz`/`.jump` test. -/
@[expose] def tinyGroupParams : List LVar :=
  [ { id := 0, name := "c", ty := .bool }
  , { id := 1, name := "x", ty := i64 }
  , { id := 2, name := "y", ty := i64 } ]

/-- Control-flow `LExpr` with `.group`, `.jnz`, and `.jump` to join label `10`. -/
@[expose] def tinyGroupLExpr : LExpr :=
  .group [(10, [{ id := 3, name := "z", ty := i64 }], .ret [i64] [.var 3 i64])]
    (.jnz (.var 0 .bool) (.jump 10 [i64] [.var 1 i64]) (.jump 10 [i64] [.var 2 i64]))

/-- De Bruijn `TFlat` lowered from `tinyGroupLExpr`. -/
@[expose] def tinyGroupTf : TFlat [i64] :=
  .group (sig := [[i64]]) (.cons (.ret (.var 0, ())) .nil)
    (.jnz (Arg.var 2) (.jump (ts := [i64]) 0 (.var 1, ()))
      (.jump (ts := [i64]) 0 (.var 0, ())))

theorem tinyGroupLExpr_toFlat :
    lExprToTFlat (({} : LFlatCtx).pushVars tinyGroupParams) [i64] tinyGroupLExpr =
      .ok tinyGroupTf := by
  rfl

theorem tinyGroup_tflat_wp (c : Bool) (x y : BitVec 64) (m : Mem 64) :
    Func.wp (fun _ _ _ _ _ _ _ => False)
      ({ name := "tinyGroup", as := [.bool, i64, i64], rs := [i64], flat := tinyGroupTf } :
        TFlatFn).toFn.body
      (c, x, y, ()) m
      (fun r m' => r = (if c then x else y, ()) ∧ m' = m) (fun _ _ _ _ => False) := by
  refine Frontend.C0.TFlatFn.wp_of_lExpr tinyGroupLExpr_toFlat _ (c, x, y, ()) m _ _ ?_
  intro Js hcl
  refine ⟨c, rfl, ?_, ?_⟩
  · intro hc
    refine ⟨Js.1, (x, ()), rfl, rfl, ?_⟩
    apply hcl.1 (x, ()) m
    exact ⟨rfl, (x, ()), rfl, by subst hc; exact ⟨rfl, rfl⟩⟩
  · intro hc
    refine ⟨Js.1, (y, ()), rfl, rfl, ?_⟩
    apply hcl.1 (y, ()) m
    exact ⟨rfl, (y, ()), rfl, by subst hc; exact ⟨rfl, rfl⟩⟩

/-! ## 5. Axiom audit (`<= std3`) -/

#print axioms Frontend.C0.lExprToTFlat_sound
#print axioms Frontend.C0.lBlocksToTBlocks_sound
#print axioms Frontend.C0.lExprToTFlat_func_sound
#print axioms Frontend.C0.TFlatFn.wp_of_lExpr
#print axioms mangle_nonascii_rfl
#print axioms tinyAdd_isOk
#print axioms tinyBranch_isOk
#print axioms tinyAddTfs_lower
#print axioms tinyAddTfs_perm
#print axioms tinyBranchTfs_lower
#print axioms tinyBranchTfs_perm
#print axioms demoNatStrTfs_lower
#print axioms factLoopTfs_lower
#print axioms arrayDemoTfs_lower
#print axioms recDemoTfs_lower
#print axioms treeDemoTfs_lower
#print axioms mutRecDemoTfs_lower
#print axioms tinyAdd_tflat_wp
#print axioms tinyGroup_tflat_wp

end LeanQbeTest.T.LcnfSemL1Test
