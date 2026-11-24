module

public import LeanQbe.T.LeanLCNF.LcnfC0Rt
public import LeanQbe.T.LeanLCNF.LcnfC0RtSpec
public import LeanQbe.T.LeanLCNF.LcnfC0RtProof
public import LeanQbe.T.PrintCpp
public import LeanQbe.T.PrintQbe
meta import LeanQbe.T.LeanLCNF.LcnfC0Rt
meta import LeanQbe.T.LeanLCNF.LcnfC0RtSpec
meta import LeanQbe.T.LeanLCNF.LcnfC0RtProof
meta import LeanQbe.T.PrintCpp
meta import LeanQbe.T.PrintQbe

/-!
# Verification & C++ Emission Tests for `LcnfC0Rt` (`M0a`)

* Structural checks on `LcnfC0Rt` slab layout (`33024` prefix + `64 * 8` freelists + `LcnfC0Hdr`)
* Acyclicity (`rtR0Mod.checkAcyclic`, `rtR0ModM0a.checkAcyclic`), `Fn.Wf` on all 5 R0 runtime fns
* `PrintCpp.ppTModule` and `PrintQbe.module` emission checks on `rtR0Mod`
* Standard axiom audit (`[propext, Classical.choice, Quot.sound]`) for M0a `Func.wp` & `ModuleOk`
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
#print axioms lcnf_clo_under_wp
#print axioms rtC0M0aEnv_alloc
#print axioms rtC0M0aEnv_free_obj
#print axioms rtC0M0aEnv_clo_under
#print axioms rtR0ModM0a_ok
#print axioms rtC0Env_clo_under_wp

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
