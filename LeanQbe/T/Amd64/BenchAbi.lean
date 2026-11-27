module

public import LeanQbe.T.BenchmarkCertKit
public import LeanQbe.T.Amd64.TargLemmas

/-!
# SysV x64 `BenchAbi` Instance (`Amd64.BenchAbi`)

Connects `LeanQbe.T.BenchmarkCertKit.BenchAbi` to `x64Target`, `x64Layout`, `x64LegalTarget`,
`x64LabelClean`, and `x64Init`. Marked `@[expose, reducible]` so concrete Kraken-x64 theorem
statements unify definitionally without unfolding overhead.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64

open Std Std.ExtHashMap LeanQbe.T LeanQbe.T.BenchmarkCertKit Kraken

/-- Read the `i`-th SysV x64 `i64` argument GPR (`rdi, rsi, rdx, rcx, r8, r9`). -/
@[expose, reducible] def x64ArgAt (i : Fin 6) (s : MachineData) : BitVec 64 :=
  match i.1 with
  | 0 => s.regs.get64 .rdi
  | 1 => s.regs.get64 .rsi
  | 2 => s.regs.get64 .rdx
  | 3 => s.regs.get64 .rcx
  | 4 => s.regs.get64 .r8
  | _ => s.regs.get64 .r9

/-- Concrete SysV x64 instance of `BenchAbi` over `x64Target` and `x64Init`. -/
@[expose, reducible] def x64BenchAbi : BenchAbi where
  T := x64Target
  L := x64Layout
  lt := x64LegalTarget
  hcl := x64LabelClean
  init := x64Init
  legalSig_i64 := rfl
  assignArgs_i64 n hn := by
    rcases n with _ | _ | _ | _ | _ | _ | _ | n <;> first | decide | omega
  argAt := x64ArgAt
  stackPre s _ := (s.regs.get64 .rsp + 8#64).toNat % 16 = 0
  exitSpOk st := (st.regs.get64 .rsp + 8#64).toNat % 16 = 0
  entryFrame s ra b :=
    region (s.regs.get64 .rsp - BitVec.ofNat 64 b) b ⋆ cell64 (s.regs.get64 .rsp) ra.toBitVec
  exitFrame s b := region (s.regs.get64 .rsp - BitVec.ofNat 64 b) (b + 8)
  initExitFrame b := region (0x0ff8#64 - BitVec.ofNat 64 b) (b + 8)
  calleeSavedOk s s' :=
    ∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15], s'.regs.get64 r = s.regs.get64 r
  spRestored s s' := s'.regs.get64 .rsp = s.regs.get64 .rsp + 8#64
  retGpr s := s.regs.get64 .rax
  argsIn_1 {s a0} h0 :=
    ⟨_, rfl, .cons ⟨by decide, by simpa using show s.regs.get64 .rdi = a0 from h0⟩ .nil⟩
  argsIn_2 {s a0 a1} h0 h1 :=
    ⟨_, rfl, .cons ⟨by decide, by simpa using show s.regs.get64 .rdi = a0 from h0⟩
      (.cons ⟨by decide, by simpa using show s.regs.get64 .rsi = a1 from h1⟩ .nil)⟩
  argsIn_3 {s a0 a1 a2} h0 h1 h2 :=
    ⟨_, rfl, .cons ⟨by decide, by simpa using show s.regs.get64 .rdi = a0 from h0⟩
      (.cons ⟨by decide, by simpa using show s.regs.get64 .rsi = a1 from h1⟩
        (.cons ⟨by decide, by simpa using show s.regs.get64 .rdx = a2 from h2⟩ .nil))⟩
  argsIn_5 {s a0 a1 a2 a3 a4} h0 h1 h2 h3 h4 :=
    ⟨_, rfl, .cons ⟨by decide, by simpa using show s.regs.get64 .rdi = a0 from h0⟩
      (.cons ⟨by decide, by simpa using show s.regs.get64 .rsi = a1 from h1⟩
        (.cons ⟨by decide, by simpa using show s.regs.get64 .rdx = a2 from h2⟩
          (.cons ⟨by decide, by simpa using show s.regs.get64 .rcx = a3 from h3⟩
            (.cons ⟨by decide, by simpa using show s.regs.get64 .r8 = a4 from h4⟩ .nil))))⟩
  argsIn_6 {s a0 a1 a2 a3 a4 a5} h0 h1 h2 h3 h4 h5 :=
    ⟨_, rfl, .cons ⟨by decide, by simpa using show s.regs.get64 .rdi = a0 from h0⟩
      (.cons ⟨by decide, by simpa using show s.regs.get64 .rsi = a1 from h1⟩
        (.cons ⟨by decide, by simpa using show s.regs.get64 .rdx = a2 from h2⟩
          (.cons ⟨by decide, by simpa using show s.regs.get64 .rcx = a3 from h3⟩
            (.cons ⟨by decide, by simpa using show s.regs.get64 .r8 = a4 from h4⟩
              (.cons ⟨by decide, by simpa using show s.regs.get64 .r9 = a5 from h5⟩ .nil)))))⟩
  raReg_spEntry_of_stackPre h := ⟨trivial, h⟩
  entry_of_entryFrame h := h
  exitFrame_of_exit h := h
  initExitFrame_of_exit {b m} h := by
    simpa only [Target.Exit, x64Target, x64FrameTarget, x64FramePreds, x64Frame, x64Init] using h
  calleeSavedOk_of_restored h r hr := h.1 r hr
  spRestored_of_restored h := h.2
  retGpr_eq_of_retsIn h := x64Init.retsIn_singleton _ _ h
  arg0_eq_of_argsIn h := x64Init.argsIn_singleton _ _ h
  exitSpOk_of_spEntry h := h

end LeanQbe.T.Amd64
