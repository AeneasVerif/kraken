module

public import LeanQbe.T.LeanLCNF.LcnfC0Rt
public import LeanQbe.T.LeanLCNF.LcnfC0RtSpec
public import LeanQbe.T.LeanLCNF.LcnfC0RtProof
public import LeanQbe.T.InterpKissat
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
meta import LeanQbe.T.LeanLCNF.LcnfC0Rt
meta import LeanQbe.T.LeanLCNF.LcnfC0RtSpec
meta import LeanQbe.T.LeanLCNF.LcnfC0RtProof
meta import LeanQbe.T.InterpKissat
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe

/-!
# Verification & C++ Emission Tests for `LcnfC0Rt` (`M0a` + `M0b`)

* Structural checks on `LcnfC0Rt` slab layout (`33024` prefix + `64 * 8` freelists + `LcnfC0Hdr`)
* Acyclicity (`rtR0Mod.checkAcyclic`, `rtR0ModM0a.checkAcyclic`), `Fn.Wf` on all 5 R0 runtime fns
* `PrintCpp.ppTModule` and `PrintQbe.module` emission checks on `rtR0Mod`
* Executable `interpModule rtR0Mod` checks on the concrete `Mem 64` 5-node constructor/closure DAG
  (`nvDagMem`) exercising cascading `lcnf_dec_ref_cold` free + shared decref and recursive
  `lcnf_mark_persistent` marking
* Standard axiom audit (`[propext, Classical.choice, Quot.sound]`) for M0a + M0b `Func.wp`,
  `rtR0Mod_ok`, and concrete `Mem 64` non-vacuity theorems
* `main` CLI writing `lcnf_c0_rt.hpp` for C++ differential execution against `test/lcnf/lcnf_rt.c`
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.LcnfC0RtTest

open LeanQbe.T
open LeanQbe.T.LeanLCNF

#guard rtR0Mod.checkAcyclic
#guard rtR0ModM0a.checkAcyclic
#guard rtR0Mod.fns.length == 5
#guard rtR0ModM0a.fns.length == 3
#guard rtR0Mod.exits == ["lcnf_panic"]
#guard rtR0ModM0a.exits == ["lcnf_panic"]
#guard LcnfC0Stats.sizeof == 64
#guard LcnfC0Hdr.sizeof == 136
#guard LcnfC0Rt.sizeof == 33672
#guard 32 * 8 + 4096 * 8 + 64 * 8 + LcnfC0Hdr.sizeof == LcnfC0Rt.sizeof
#guard rtMinObjBytes == 16
#guard rtMaxObjBytes == 268435456
#guard rtNumClasses == 64
#guard (PrintCpp.ppTModule rtR0Mod).isOk
#guard (PrintQbe.module rtR0Mod).isOk

/-! ## Executable `interpModule` DAG Checks (`lcnf_dec_ref_cold`, `lcnf_mark_persistent`) -/

/-- Executable check: `lcnf_dec_ref_cold` on root `A` (`rc=1`) frees `A` and closure `B`,
decrements shared `C` (`3 -> 1`), preserves persistent `P` (`0`) and unreachable `U` (`2`),
and a follow-up `lcnf_dec_ref_cold` on `C` frees `C` onto `free_list[3]` ahead of `A`. -/
def checkDecRefColdDag : Bool :=
  match interpModule rtR0Mod 10000 "lcnf_dec_ref_cold" [i64, i64] []
      (nvRtBase, nvAddrA, ()) nvDagMem with
  | .ok () m1 =>
    let ok1 :=
      loadVal m1 i64 (nvRtBase + 33656#64) == some 1#64 &&
      loadVal m1 i64 (nvRtBase + 33616#64) == some 2#64 &&
      loadVal m1 i64 (nvRtBase + 33048#64) == some nvAddrA &&
      loadVal m1 i64 (nvRtBase + 33056#64) == some nvAddrB &&
      loadVal m1 i64 nvAddrC == some (nvObjC.withRc 1#32).header &&
      loadVal m1 i64 nvAddrP == some nvObjP.header &&
      loadVal m1 i64 nvAddrU == some nvObjU.header
    if !ok1 then false
    else
      match interpModule rtR0Mod 10000 "lcnf_dec_ref_cold" [i64, i64] []
          (nvRtBase, nvAddrC, ()) m1 with
      | .ok () m2 =>
        loadVal m2 i64 (nvRtBase + 33656#64) == some 2#64 &&
        loadVal m2 i64 (nvRtBase + 33616#64) == some 3#64 &&
        loadVal m2 i64 (nvRtBase + 33048#64) == some nvAddrC &&
        loadVal m2 i64 (nvAddrC + 8#64) == some nvAddrA &&
        loadVal m2 i64 nvAddrP == some nvObjP.header &&
        loadVal m2 i64 nvAddrU == some nvObjU.header
      | _ => false
  | _ => false

/-- Executable check: `lcnf_mark_persistent` on root `A` recursively marks `A`, closure `B`,
and shared `C` persistent (`rc=0`), leaves `P` (`rc=0`) and unreachable `U` (`rc=2`) intact,
and is idempotent (with scalars as no-ops). -/
def checkMarkPersistentDag : Bool :=
  match interpModule rtR0Mod 10000 "lcnf_mark_persistent" [i64, i64] []
      (nvRtBase, nvAddrA, ()) nvDagMem with
  | .ok () m1 =>
    let ok1 :=
      loadVal m1 i64 nvAddrA == some (nvObjA.withRc 0#32).header &&
      loadVal m1 i64 nvAddrB == some (nvObjB.withRc 0#32).header &&
      loadVal m1 i64 nvAddrC == some (nvObjC.withRc 0#32).header &&
      loadVal m1 i64 nvAddrP == some nvObjP.header &&
      loadVal m1 i64 nvAddrU == some nvObjU.header &&
      loadVal m1 i64 (nvRtBase + 33640#64) == some 3#64
    let ok2 :=
      match interpModule rtR0Mod 10000 "lcnf_mark_persistent" [i64, i64] []
          (nvRtBase, nvAddrA, ()) m1 with
      | .ok () m2 =>
        loadVal m2 i64 (nvRtBase + 33640#64) == some 3#64 &&
        loadVal m2 i64 nvAddrU == some nvObjU.header
      | _ => false
    let okScalar :=
      match interpModule rtR0Mod 10000 "lcnf_mark_persistent" [i64, i64] []
          (nvRtBase, 7#64, ()) nvDagMem with
      | .ok () mS =>
        loadVal mS i64 (nvRtBase + 33640#64) == some 0#64 &&
        loadVal mS i64 nvAddrA == some nvObjA.header
      | _ => false
    ok1 && ok2 && okScalar
  | _ => false

#guard checkDecRefColdDag
#guard checkMarkPersistentDag

theorem r0_all_wf : ∀ f ∈ rtR0_fns, f.Wf := by
  intro f hf
  simp only [rtR0_fns, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact lcnf_alloc_wf
  · exact lcnf_free_obj_wf
  · exact lcnf_dec_ref_cold_wf
  · exact lcnf_mark_persistent_wf
  · exact lcnf_clo_under_wf

#print axioms lcnf_alloc_wf
#print axioms lcnf_free_obj_wf
#print axioms lcnf_dec_ref_cold_wf
#print axioms lcnf_mark_persistent_wf
#print axioms lcnf_clo_under_wf
#print axioms r0_all_wf
#print axioms lcnf_alloc_wp
#print axioms lcnf_free_obj_wp
#print axioms lcnf_dec_ref_cold_wp
#print axioms lcnf_mark_persistent_wp
#print axioms lcnf_clo_under_wp
#print axioms rtC0M0aEnv_alloc
#print axioms rtC0M0aEnv_free_obj
#print axioms rtC0M0aEnv_clo_under
#print axioms rtR0ModM0a_ok
#print axioms rtC0Env_dec_ref_cold_wp
#print axioms rtC0Env_mark_persistent_wp
#print axioms rtC0Env_clo_under_wp
#print axioms rtR0Mod_ok
#print axioms nvDagMem_ok
#print axioms nv_dec_ref_cold_dag
#print axioms nv_mark_persistent_dag

def emitLcnfC0Rt (outDir : String) : IO UInt32 := do
  match PrintCpp.ppTModule rtR0Mod with
  | .ok body =>
    IO.FS.writeFile s!"{outDir}/lcnf_c0_rt.hpp" body
    IO.println s!"Generated {outDir}/lcnf_c0_rt.hpp ({body.length} bytes)."
    pure 0
  | .error e =>
    throw (IO.userError s!"ppTModule rtR0Mod: {e}")

end LeanQbeTest.T.LcnfC0RtTest

def main (args : List String) : IO UInt32 :=
  LeanQbeTest.T.LcnfC0RtTest.emitLcnfC0Rt (args.headD "/tmp/lcnf_c0_rt_diff")
