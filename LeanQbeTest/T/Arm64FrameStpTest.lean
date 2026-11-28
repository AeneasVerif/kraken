module

import LeanQbe.T.Arm64.FrameLemmas
import LeanQbe.T.Arm64.TargLemmas
import LeanQbe.T.RegaLemmas
import LeanQbe.T.Spill
import Kraken.AArch64.Parser
meta import LeanQbe.T.Arm64.TargLemmas
meta import LeanQbe.T.Spill

/-!
# AAPCS64 Arm64 `STP`/`LDP` Callee-Saved Pairing Tests

Verifies:
1. Even (`4` regs) and odd (`3` regs) callee-saved save/restore pairing (`stp`/`ldp` + trailing
   `str`/`ldr`).
2. Signed 7-bit scaled offset boundary (`[sp, #504]` at slot `63` uses `stp`/`ldp`; `[sp, #512]`
   at slot `64` falls back cleanly to `str`/`ldr`).
3. End-to-end `checkCompile` / `compileModule` emission counts (`stp`/`ldp` vs `str`/`ldr`) on
   `armTarget` with `armLabelClean` and `armLayout`.
4. `armFrameSpec.saveRegs_spec` / `armFrameSpec.restoreRegs_spec` round-trip proof and standard
   `#print axioms` audit.
-/

set_option autoImplicit false

section

namespace LeanQbeTest.T.Arm64FrameStpTest

open LeanQbe.T LeanQbe.T.Arm64
open Kraken.AArch64 Kraken.AArch64.Parser
open Std Std.ExtHashMap

/-! ## 1. Directive counters and unit boundary checks -/

def isStp : Directive → Bool
  | .instr ⟨_, .STP _ _ _⟩ => true
  | _ => false

def isLdp : Directive → Bool
  | .instr ⟨_, .LDP _ _ _⟩ => true
  | _ => false

def isStr : Directive → Bool
  | .instr ⟨_, .STR _ _⟩ => true
  | _ => false

def isLdr : Directive → Bool
  | .instr ⟨_, .LDR _ (.addr _)⟩ => true
  | _ => false

def countDirs (p : Directive → Bool) (ds : List Directive) : Nat :=
  (ds.filter p).length

#guard countDirs isStp (armSaveRegs 0 [.reg .X19, .reg .X20, .reg .X21, .reg .X22]) == 2
#guard countDirs isStr (armSaveRegs 0 [.reg .X19, .reg .X20, .reg .X21, .reg .X22]) == 0
#guard countDirs isLdp (armRestoreRegs 0 [.reg .X19, .reg .X20, .reg .X21, .reg .X22]) == 2
#guard countDirs isLdr (armRestoreRegs 0 [.reg .X19, .reg .X20, .reg .X21, .reg .X22]) == 0

#guard countDirs isStp (armSaveRegs 1 [.reg .X19, .reg .X20, .reg .X21]) == 1
#guard countDirs isStr (armSaveRegs 1 [.reg .X19, .reg .X20, .reg .X21]) == 1
#guard countDirs isLdp (armRestoreRegs 1 [.reg .X19, .reg .X20, .reg .X21]) == 1
#guard countDirs isLdr (armRestoreRegs 1 [.reg .X19, .reg .X20, .reg .X21]) == 1

#guard countDirs isStp (armSaveRegs 63 [.reg .X19, .reg .X20]) == 1
#guard countDirs isStr (armSaveRegs 63 [.reg .X19, .reg .X20]) == 0
#guard countDirs isLdp (armRestoreRegs 63 [.reg .X19, .reg .X20]) == 1
#guard countDirs isLdr (armRestoreRegs 63 [.reg .X19, .reg .X20]) == 0

#guard countDirs isStp (armSaveRegs 64 [.reg .X19, .reg .X20]) == 0
#guard countDirs isStr (armSaveRegs 64 [.reg .X19, .reg .X20]) == 2
#guard countDirs isLdp (armRestoreRegs 64 [.reg .X19, .reg .X20]) == 0
#guard countDirs isLdr (armRestoreRegs 64 [.reg .X19, .reg .X20]) == 2

theorem armSaveRestore_parser_rfl :
    ⸨prog|
      stp x19, x20, [sp, #0]
      str x21, [sp, #16]
      ldp x19, x20, [sp, #0]
      ldr x21, [sp, #16]
    ⸩ =
      armSaveRegs 0 [.reg .X19, .reg .X20, .reg .X21] ++
        armRestoreRegs 0 [.reg .X19, .reg .X20, .reg .X21] := rfl

/-! ## 2. Verified `compileModule` / `checkCompile` checks on `armTarget` -/

meta def idFn : Fn :=
  ⟨"id", [i64], [i64], fun _ _ (x, ()) => .ret (.var x, ())⟩

meta def cs3Fn : Fn :=
  ⟨"cs3", [i64, i64, i64], [i64], fun _ _ (a, b, c, ()) =>
    .call "id" (as := [i64]) (bs := [i64]) (.var a, ()) fun (r, ()) =>
    .let_ (op2 (.add i64) (.var r) (.var a)) fun (t1, ()) =>
    .let_ (op2 (.add i64) (.var t1) (.var b)) fun (t2, ()) =>
    .let_ (op2 (.add i64) (.var t2) (.var c)) fun (t3, ()) => .ret (.var t3, ())⟩

meta def cs4Fn : Fn :=
  ⟨"cs4", [i64, i64, i64, i64], [i64], fun _ _ (a, b, c, d, ()) =>
    .call "id" (as := [i64]) (bs := [i64]) (.var a, ()) fun (r, ()) =>
    .let_ (op2 (.add i64) (.var r) (.var a)) fun (t1, ()) =>
    .let_ (op2 (.add i64) (.var t1) (.var b)) fun (t2, ()) =>
    .let_ (op2 (.add i64) (.var t2) (.var c)) fun (t3, ()) =>
    .let_ (op2 (.add i64) (.var t3) (.var d)) fun (t4, ()) => .ret (.var t4, ())⟩

meta def hintsOf (fs : List Fn) : List armTarget.toIsa.Hints :=
  fs.map (Fn.computeHints armTarget.toIsa armLegalTarget)

meta def chk (fs : List Fn) (hs : List armTarget.toIsa.Hints) : Bool :=
  checkCompile armTarget armLayout armLegalTarget [] [] 0 fs hs 4096

meta def codeOf (fs : List Fn) (hs : List armTarget.toIsa.Hints) : List Directive :=
  extractCode (compileModule armTarget.toIsa armLegalTarget 0 [] [] 0 fs hs)

meta def leafFn : Fn :=
  ⟨"leaf", [i64, i64], [i64], fun _ _ (a, b, ()) =>
    .let_ (op2 (.add i64) (.var a) (.var b)) fun (c, ()) => .ret (.var c, ())⟩

meta def hintWithSlots (ns : Nat) (sv : List Reg) : armTarget.toIsa.Hints :=
  { Fn.computeHints armTarget.toIsa armLegalTarget leafFn with nslots := ns, saved := sv }

meta def hCs3 : armTarget.toIsa.Hints :=
  hintWithSlots 0 [.reg .X19, .reg .X20, .reg .X21]

meta def hCs4 : armTarget.toIsa.Hints :=
  hintWithSlots 0 [.reg .X19, .reg .X20, .reg .X21, .reg .X22]

meta def hAt504 : armTarget.toIsa.Hints := hintWithSlots 63 [.reg .X19, .reg .X20]
meta def hAt512 : armTarget.toIsa.Hints := hintWithSlots 64 [.reg .X19, .reg .X20]

#guard chk [leafFn] [hCs3]
#guard chk [leafFn] [hCs4]
#guard countDirs isStp (codeOf [leafFn] [hCs3]) == 1
#guard countDirs isLdp (codeOf [leafFn] [hCs3]) == 1
#guard countDirs isStr (codeOf [leafFn] [hCs3]) == 2
#guard countDirs isLdr (codeOf [leafFn] [hCs3]) == 2
#guard countDirs isStp (codeOf [leafFn] [hCs4]) == 2
#guard countDirs isLdp (codeOf [leafFn] [hCs4]) == 2
#guard countDirs isStr (codeOf [leafFn] [hCs4]) == 1
#guard countDirs isLdr (codeOf [leafFn] [hCs4]) == 1

#guard chk [leafFn] [hAt504]
#guard chk [leafFn] [hAt512]
#guard countDirs isStp (codeOf [leafFn] [hAt504]) == 1
#guard countDirs isLdp (codeOf [leafFn] [hAt504]) == 1
#guard countDirs isStp (codeOf [leafFn] [hAt512]) == 0
#guard countDirs isLdp (codeOf [leafFn] [hAt512]) == 0
#guard countDirs isStr (codeOf [leafFn] [hAt512]) == 3
#guard countDirs isLdr (codeOf [leafFn] [hAt512]) == 3

/-! ## 3. Generic `armFrameSpec` `saveRegs_spec` + `restoreRegs_spec` round-trip -/

theorem armSaveRestore_roundtrip {h : Host} {k : Nat} {s : MachineData} {R : Mem 64 → Prop}
    {post : MachineState → Prop}
    (hsp : armFrameSpec.spOk (armMach.getGpr s armFrame.sp))
    (hmem : s.dmem =⋆ region (armMach.getGpr s armFrame.sp + 0#64) 24 ⋆ R)
    (hc : (armSaveRegs 0 [.reg .X19, .reg .X20, .reg .X21] ++
        armRestoreRegs 0 [.reg .X19, .reg .X20, .reg .X21]).IsInfixAt
      (armMach.prog h) k)
    (hk : ∀ s' : MachineData,
      armMach.getGpr s' (.reg .X19) = armMach.getGpr s (.reg .X19) →
      armMach.getGpr s' (.reg .X20) = armMach.getGpr s (.reg .X20) →
      armMach.getGpr s' (.reg .X21) = armMach.getGpr s (.reg .X21) →
      armMach.Run h (k + (armSaveRegs 0 [.reg .X19, .reg .X20, .reg .X21] ++
        armRestoreRegs 0 [.reg .X19, .reg .X20, .reg .X21]).length) s' post) :
    armMach.Run h k s post := by
  let rs : List Reg := [.reg .X19, .reg .X20, .reg .X21]
  have hsave : armFrame.saveRegs? = some armSaveRegs := rfl
  have hrest : armFrame.restoreRegs? = some armRestoreRegs := rfl
  have hrs : ∀ r ∈ rs, r ∉ armFrame.scratch := by simp [rs, armScratch]
  have hnd : rs.Nodup := by decide
  have hsub : ∀ r ∈ rs, r ∈ armFrame.calleeSaved := by simp [rs]
  refine armFrameSpec.saveRegs_spec hsave (by decide) hrs hsp hmem hc.append.1 fun s1 hm1 hfr1 => ?_
  refine armFrameSpec.restoreRegs_spec hrest hnd hsub (s₀ := s) (G := R) ?_ ?_ hc.append.2
    fun s2 hq2 _ => ?_
  · rw [hfr1.1 _ armFrameSpec.sp_disj.1]; exact hsp
  · rw [hfr1.1 _ armFrameSpec.sp_disj.1]; exact hm1
  · have hlen : k + (armSaveRegs 0 rs ++ armRestoreRegs 0 rs).length =
        k + (armSaveRegs 0 rs).length + (armRestoreRegs 0 rs).length := by
      simp [List.length_append, Nat.add_assoc]
    rw [← hlen]
    exact hk s2 (hq2.1 (.reg .X19) (by simp [rs])) (hq2.1 (.reg .X20) (by simp [rs]))
      (hq2.1 (.reg .X21) (by simp [rs]))

/-! ## 4. Axiom audit (`[propext, Classical.choice, Quot.sound]`) -/

#print axioms LeanQbe.T.Arm64.armFrameSpec
#print axioms LeanQbe.T.Arm64.armSaveRegs_noLab
#print axioms LeanQbe.T.Arm64.armRestoreRegs_noLab
#print axioms LeanQbe.T.Arm64.armLabelClean
#print axioms LeanQbe.T.Rega.lowerFn_correct
#print axioms LeanQbeTest.T.Arm64FrameStpTest.armSaveRestore_roundtrip

end LeanQbeTest.T.Arm64FrameStpTest
