module

public import LeanQbe.T.Examples.Kissat.KissatAbiCommon
public import LeanQbe.T.Amd64.TargLemmas

/-!
# SysV x64 `ArchKissatAbi` Instance (`Amd64.KissatAbi`)

Connects `ArchKissatAbi` (legacy-free `KissatAbiCommon`) to `x64Target`, `x64Layout`,
`x64LegalTarget`, `x64LabelClean`, and `x64Init`. Reducible so concrete Kraken-x64 theorem
statements unify definitionally without unfolding overhead.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64

open Std Std.ExtHashMap LeanQbe.T LeanQbe.T.Examples.Kissat.KissatCertCommon Kraken

/-- Concrete SysV x64 instance of `ArchKissatAbi` over `x64Target` and `x64Init`. -/
@[expose, reducible] def x64KissatAbi : ArchKissatAbi where
  T := x64Target
  L := x64Layout
  lt := x64LegalTarget
  hcl := x64LabelClean
  init := x64Init
  args5Ok s a0 a1 a2 a3 a4 :=
    s.regs.get64 .rdi = a0 ∧ s.regs.get64 .rsi = a1 ∧ s.regs.get64 .rdx = a2 ∧
      s.regs.get64 .rcx = a3 ∧ s.regs.get64 .r8 = a4
  stackPre s _ := (s.regs.get64 .rsp + 8#64).toNat % 16 = 0
  entryFrame s ra b :=
    region (s.regs.get64 .rsp - BitVec.ofNat 64 b) b ⋆ cell64 (s.regs.get64 .rsp) ra.toBitVec
  exitFrame s b := region (s.regs.get64 .rsp - BitVec.ofNat 64 b) (b + 8)
  calleeSpOk s s' :=
    (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], s'.regs.get64 r = s.regs.get64 r) ∧
      s'.regs.get64 .rsp = s.regs.get64 .rsp + 8#64
  retGpr s := s.regs.get64 .rax
  argsIn_of_args5 h :=
    ⟨_, rfl,
      .cons ⟨by decide, by simpa using h.1⟩
        (.cons ⟨by decide, by simpa using h.2.1⟩
          (.cons ⟨by decide, by simpa using h.2.2.1⟩
            (.cons ⟨by decide, by simpa using h.2.2.2.1⟩
              (.cons ⟨by decide, by simpa using h.2.2.2.2⟩ .nil))))⟩
  raReg_spEntry_of_stackPre h := ⟨trivial, h⟩
  entry_of_entryFrame h := h
  entryFrame_of_entry h := h
  exitFrame_of_exit h := h
  calleeSpOk_of_restored h := ⟨fun r hr => h.1 r hr, h.2⟩
  retGpr_eq_of_retsIn h := x64Init.retsIn_singleton _ _ h
  init_args5 b bs a0 a1 a2 a3 a4 := by
    obtain ⟨locs, hlocs, hrel⟩ :=
      x64Init.argsIn b bs (as := [i64, i64, i64, i64, i64]) (a0, a1, a2, a3, a4, ()) (by decide)
    change some (AbiReg.gpr .rdi, AbiReg.gpr .rsi, AbiReg.gpr .rdx,
      AbiReg.gpr .rcx, AbiReg.gpr .r8, ()) = some locs at hlocs
    injection hlocs with hlocs
    subst hlocs
    cases hrel with | cons h1 hrel =>
    cases hrel with | cons h2 hrel =>
    cases hrel with | cons h3 hrel =>
    cases hrel with | cons h4 hrel =>
    cases hrel with | cons h5 _ =>
    exact ⟨h1.2.trans (by simp), h2.2.trans (by simp), h3.2.trans (by simp),
      h4.2.trans (by simp), h5.2.trans (by simp)⟩
  init_stackPre := fun b bs {as} args => by
    have hsp := x64Init.spEntry
    dsimp only [x64Target, x64FrameTarget, x64FramePreds] at hsp ⊢
    rw [show (x64Init.initState b bs args).regs.get64 .rsp = x64Init.sp0 from
      x64Init.get_sp b bs args]
    exact hsp

end LeanQbe.T.Amd64
