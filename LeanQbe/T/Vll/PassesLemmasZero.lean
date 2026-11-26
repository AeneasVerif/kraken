module

public import LeanQbe.T.Vll.Passes
public import LeanQbe.T.Vll.Sem

/-!
# Soundness Helpers for `[.movi rd 0#64, .clearFlags]` Zero-Idiom Peephole (`Vll.PassesLemmasZero`)

100% architecture-free (`0` imports of `Amd64`, `Arm64`, or `Kraken.*`) proof that
`[.movi rd 0#64, .clearFlags]` and `[.alu .xor .w32 rd rd (.reg rd) true]` have identical
deterministic fall-through transitions whenever `A.writeSub .w32` zeroes 64 bits and
`A.aluFlags .xor .w32 true a a f = A.clearFlagsVal`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Vll

theorem movi_clearFlags_detFall_core {A : Arch} (symAddr : Sym → BitVec 64) (rd : A.Reg)
    (hxor : ∀ old a f,
      A.writeSub .w32 old 0#32 = 0#64 ∧ A.aluFlags .xor .w32 true a a f = A.clearFlagsVal)
    (s : MachSt A) :
    ∃ s₁ s₂,
      (∀ np o, instrRel A symAddr np (.movi rd 0#64) s o ↔ o = .fall s₁) ∧
      (∀ np o, instrRel A symAddr np .clearFlags s₁ o ↔ o = .fall s₂) ∧
      (∀ np o, instrRel A symAddr np (.alu .xor .w32 rd rd (.reg rd) true) s o ↔
        o = .fall s₂) := by
  let s₁ : MachSt A := s.setGpr rd 0#64
  let s₂ : MachSt A := s₁.setFlags A.clearFlagsVal
  refine ⟨s₁, s₂, fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ => ?_⟩
  have hxw := hxor (s.gpr rd) ((s.gpr rd).setWidth 32) s.flags
  have hev : CoreAlu.xor.eval .w32 ((s.gpr rd).setWidth 32)
      ((Src.reg rd).evalW .w32 s.gpr) = 0#32 := by
    dsimp only [CoreAlu.eval, Src.evalW, Src.eval]
    apply BitVec.eq_of_getElem_eq
    intro i hi
    simp
  have hx1 : A.writeSub .w32 (s.gpr rd) 0#32 = 0#64 := hxw.1
  have hx2 : A.aluFlags .xor .w32 true ((s.gpr rd).setWidth 32)
      ((Src.reg rd).evalW .w32 s.gpr) s.flags = A.clearFlagsVal := by
    simpa [Src.evalW, Src.eval] using hxw.2
  simp only [instrRel, MachSt.setGprW, hev, hx1, hx2]
  rfl

theorem movi_clearFlags_no_label_call {A : Arch} (rd : A.Reg) :
    ((∀ l, (Instr.movi rd 0#64 : Instr A) ≠ .label l) ∧
     (∀ l, (Instr.clearFlags : Instr A) ≠ .label l) ∧
     (∀ l, (Instr.alu .xor .w32 rd rd (.reg rd) true : Instr A) ≠ .label l)) ∧
    ((Instr.movi rd 0#64 : Instr A).isCall = false ∧
     (Instr.clearFlags : Instr A).isCall = false ∧
     (Instr.alu .xor .w32 rd rd (.reg rd) true : Instr A).isCall = false) :=
  ⟨⟨(fun _ e => by cases e), (fun _ e => by cases e), (fun _ e => by cases e)⟩, rfl, rfl, rfl⟩

end LeanQbe.T.Vll
