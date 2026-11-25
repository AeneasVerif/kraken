module

public import LeanQbe.T.MainCertInlineChunk
public import LeanQbeTest.T.Common.Fixtures
public meta import Lean
public meta import LeanQbe.T.MainCertInlineChunk
public meta import LeanQbeTest.T.Common.Fixtures

/-!
# Chunked `inline_mod!` Tests (`MainCertInlineChunkTest`)

Tests `inline_chunk_base!`, `inline_mod_chunk!`, and `inline_mod_join!` across:
1. Small multi-chunk inlining on `inlSrcMod` (`InlinePolicy.b5`), verifying `chunkMod.eq`,
   `chunkMod.fns_eq`, and full callee elimination.
2. Large `520`-function modules (`idx ≥ 448..519`, `cands.length > 448`) under BOTH
   `InlinePolicy.const 20` and a bounded `InlinePolicy` (`maxCallerSize := 200`),
   WITHOUT `set_option maxRecDepth`, ensuring zero `Meta.whnf` / kernel recursion overflow.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.MainCertInlineChunkTest

open LeanQbe.T
open LeanQbeTest.T.Common.Fixtures

/-! ## 1. Concrete `inlSrcMod` chunked inlining (`InlinePolicy.b5`) -/

inline_chunk_base! srcBase inlSrcMod InlinePolicy.b5
inline_mod_chunk! srcC0 srcBase inlSrcMod InlinePolicy.b5 0 2
inline_mod_chunk! srcC1 srcBase inlSrcMod InlinePolicy.b5 2 2 (prev := srcC0) (isLast := true)
inline_mod_join! srcChunkMod srcChunkFns inlSrcMod InlinePolicy.b5 srcBase [srcC0, srcC1]

private def dummyFn : Fn := ⟨"", [], [], fun _ _ _ => .hlt⟩

#guard (srcChunkMod.fns.getD 3 dummyFn).checkCallsOk [] []
#guard srcChunkMod.fns.length == 4

/-! ## 2. Large `520`-function chain (`idx ≥ 448..519`) without `set_option maxRecDepth` -/

private meta def mkChainMatFn (i : Nat) : MatFnData :=
  let v0 : Tup (Arg K) [i64] := (.var 0, ())
  let flat : TFlat [i64] :=
    if i == 0 then .ret v0
    else .call "f0" [i64] v0 (.ret v0)
  ⟨s!"f{i}", [i64], [i64], flat⟩

local elab "def_chain_mod! " id:ident n:num : command => open Lean Elab Command in do
  let ns ← getCurrNamespace
  let modNm := ns ++ id.getId
  let fnTy := Lean.mkConst ``LeanQbe.T.Fn
  let modTy := Lean.mkConst ``LeanQbe.T.Module
  let fns := (List.range n.getNat).map mkChainMatFn
  liftCoreM do
    let mut fnExprs : Array Lean.Expr := #[]
    for f in fns do
      fnExprs := fnExprs.push (InlineMeta.matFnToExpr f)
    let fnsLit := InlineMeta.mkListLit .one fnTy fnExprs.toList
    let modVal := mkApp3 (Lean.mkConst ``LeanQbe.T.Module.mk) fnsLit
      (InlineMeta.listExternToExpr []) (InlineMeta.listSymToExpr [])
    addCertDef modNm modTy modVal true

def_chain_mod! chain520Mod 520

inline_chunk_base! chConstBase chain520Mod (InlinePolicy.const 20)
inline_mod_chunk! chConst0 chConstBase chain520Mod (InlinePolicy.const 20) 0 64
inline_mod_chunk! chConst1 chConstBase chain520Mod (InlinePolicy.const 20) 64 64 (prev := chConst0)
inline_mod_chunk! chConst2 chConstBase chain520Mod (InlinePolicy.const 20) 128 64
  (prev := chConst1)
inline_mod_chunk! chConst3 chConstBase chain520Mod (InlinePolicy.const 20) 192 64
  (prev := chConst2)
inline_mod_chunk! chConst4 chConstBase chain520Mod (InlinePolicy.const 20) 256 64
  (prev := chConst3)
inline_mod_chunk! chConst5 chConstBase chain520Mod (InlinePolicy.const 20) 320 64
  (prev := chConst4)
inline_mod_chunk! chConst6 chConstBase chain520Mod (InlinePolicy.const 20) 384 64
  (prev := chConst5)
inline_mod_chunk! chConst7 chConstBase chain520Mod (InlinePolicy.const 20) 448 64
  (prev := chConst6)
inline_mod_chunk! chConst8 chConstBase chain520Mod (InlinePolicy.const 20) 512 8
  (prev := chConst7) (isLast := true)
inline_mod_join! chConstMod chConstFns chain520Mod (InlinePolicy.const 20) chConstBase
  [chConst0, chConst1, chConst2, chConst3, chConst4, chConst5, chConst6, chConst7, chConst8]

def chainPol : InlinePolicy :=
  { budget := fun _ => 20, maxCallerSize := 200, maxCallerCalls := 4 }

inline_chunk_base! chPolBase chain520Mod chainPol
inline_mod_chunk! chPol0 chPolBase chain520Mod chainPol 0 64
inline_mod_chunk! chPol1 chPolBase chain520Mod chainPol 64 64 (prev := chPol0)
inline_mod_chunk! chPol2 chPolBase chain520Mod chainPol 128 64 (prev := chPol1)
inline_mod_chunk! chPol3 chPolBase chain520Mod chainPol 192 64 (prev := chPol2)
inline_mod_chunk! chPol4 chPolBase chain520Mod chainPol 256 64 (prev := chPol3)
inline_mod_chunk! chPol5 chPolBase chain520Mod chainPol 320 64 (prev := chPol4)
inline_mod_chunk! chPol6 chPolBase chain520Mod chainPol 384 64 (prev := chPol5)
inline_mod_chunk! chPol7 chPolBase chain520Mod chainPol 448 64 (prev := chPol6)
inline_mod_chunk! chPol8 chPolBase chain520Mod chainPol 512 8 (prev := chPol7) (isLast := true)
inline_mod_join! chPolMod chPolFns chain520Mod chainPol chPolBase
  [chPol0, chPol1, chPol2, chPol3, chPol4, chPol5, chPol6, chPol7, chPol8]

#guard chConstMod.fns.length == 520
#guard chPolMod.fns.length == 520
example : chConst7.cand.c63.name = "f511" := rfl
example : chPol7.cand.c63.name = "f511" := rfl
#eval show Lean.Meta.MetaM Unit from do
  let d1 := evalChunkInlData chain520Mod (InlinePolicy.const 20)
    chConstBase.siteCounts chConstBase.loopCounts 0 512
  let d2 := evalChunkInlData chain520Mod chainPol chPolBase.siteCounts chPolBase.loopCounts 0 512
  if !d1.candFlags.all id || !d2.candFlags.all id then
    throwError "expected all 512 candidates accepted"
#guard chConstMod.fns.all fun f => f.checkCallsOk [] []
#guard chPolMod.fns.all fun f => f.checkCallsOk [] []

#print axioms srcChunkMod.eq
#print axioms chConstMod.eq
#print axioms chConstMod.fns_eq
#print axioms chPolMod.eq
#print axioms chPolMod.fns_eq

end LeanQbeTest.T.MainCertInlineChunkTest
