module

public import LeanQbe.T.Amd64.VllFactorX640
public import LeanQbe.T.Amd64.VllAsmX64
import LeanQbe.T.TargetLemmas

/-!
# BedrockMach SysV x86-64 Zero-Idiom Proofs (`Amd64.VllFactorX64Zero`)

Semantics (`vllX64_moviDeadFlags_spec`) and 1:1 `asmX64List` parity
(`asmX64List_vllX64MoviDeadFlags`) for `vllX64MoviDeadFlags` (`xorl %ed, %ed` when `c == 0#64`,
`.movi` otherwise). Zero `*Lemmas*` public imports, zero `Arm64` imports.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64

open LeanQbe.T
open LeanQbe.T.Vll

theorem vllX64_moviDeadFlags_spec {h : VllHost x64Arch} {k : Nat} {rd : Reg64} {c : BitVec 64}
    {s : MachSt x64Arch} {post : Config x64Arch → Prop} :
    (vllMach x64Arch).FallsTo x64Arch.condReads h k (vllX64MoviDeadFlags rd c).1
      (rd :: x64Arch.abi.scratch) [] (vllX64MoviDeadFlags rd c).2 s
      (fun s' => s'.gpr rd = c ∧ s'.mem = s.mem) post := by
  dsimp only [vllX64MoviDeadFlags]
  split
  · rename_i hc
    have hc0 : c = 0#64 := beq_iff_eq.mp hc
    subst hc0
    refine Machine.FallsTo.conseq (Machine.FallsTo.weaken
      (vllMach_alu_spec x64Arch_wf (op := .xor) (w := .w32) (rd := rd) (lhs := rd)
        (rhs := .reg rd) (sf := true))
      (fun _ hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self)
      (fun _ h0 => nomatch h0) (flagMask_sub_refl _)) ?_
    intro s' ⟨hwr, _, _, hm⟩ _
    refine ⟨?_, hm⟩
    have hxor : ((s.gpr rd).setWidth 32 ^^^ (s.gpr rd).setWidth 32) = 0#32 := by
      apply BitVec.eq_of_getElem_eq; intro i hi; simp
    simpa [CoreAlu.eval, Src.evalW, Src.eval, hxor, writeSubX64] using hwr
  · exact fallsTo_weaken_rd (vllMach_movi_spec (A := x64Arch) (rd := rd) (imm := c))

theorem asmX64List_vllX64MoviDeadFlags (rd : Reg64) (c : BitVec 64) :
    (asmX64List (vllX64MoviDeadFlags rd c).1, (vllX64MoviDeadFlags rd c).2) =
      x64MoviDeadFlags rd c := by
  dsimp only [vllX64MoviDeadFlags, x64MoviDeadFlags]
  split
  · cases rd <;> rfl
  · rfl

end LeanQbe.T.Amd64
