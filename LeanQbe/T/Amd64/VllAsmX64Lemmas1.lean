module

public import LeanQbe.T.Amd64.VllAsmX64Lemmas0
import LeanQbe.T.Amd64.IselStepRules
import LeanQbe.T.Amd64.IselLemmas1
import LeanQbe.T.Amd64.IselLemmas2
import LeanQbe.T.Amd64.IselLemmas3
import LeanQbe.T.Amd64.FrameLemmas
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.AbiLemmas

/-!
# Assembler Verification Part 1: ALU Compilation Proofs (`Amd64.VllAsmX64Lemmas1`)

Modular ALU simulation proofs for `asmX64` (`add`/`sub`/`and`/`or`/`xor`, `mul`,
`shl`/`lshr`/`ashr`) exporting `asmX64_alu_fallsTo`. Zero Arm64/AArch64 imports,
zero `@[expose]` on theorems/lemmas.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64

open LeanQbe.T
open LeanQbe.T.Vll
open Std Std.ExtHashMap

/-! ## 1. Private ALU Flag and Sub-Word Bridges -/

private theorem getLsbD_replaceLow {old : BitVec 64} {n : Nat} (hn : n ≤ 64) (new : BitVec n)
    {i : Nat} (hi : i < 64) :
    (old.replaceLow new).getLsbD i = if i < n then new.getLsbD i else old.getLsbD i := by
  simp only [BitVec.replaceLow, BitVec.getLsbD_setWidth, decide_eq_true hi, Bool.true_and]
  change (old.drop n ++ new).getLsbD i = _
  rw [BitVec.getLsbD_append]
  split
  · rfl
  · simp [BitVec.drop, show i - n < 64 - n by omega, show n + (i - n) = i by omega]

private theorem writeSubX64_self (w : Vll.Width) (hw : w ≠ .w32) (x : BitVec 64) :
    writeSubX64 w x (x.setWidth w.bits) = x := by
  cases w with
  | w8 =>
    rw [← replaceLow_8_eq_writeSubX64]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    rw [getLsbD_replaceLow (by decide) _ hi]
    by_cases hi8 : i < 8 <;> simp [hi8]
  | w16 =>
    rw [← replaceLow_16_eq_writeSubX64]
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    rw [getLsbD_replaceLow (by decide) _ hi]
    by_cases hi16 : i < 16 <;> simp [hi16]
  | w64 => simp [writeSubX64, BitVec.setWidth_eq]
  | w32 => exact absurd rfl hw

private theorem writeSubX64_of_pre (w : Vll.Width) (old s1r : BitVec 64) (v : BitVec w.bits)
    (h : s1r = old ∨ ∃ rv, s1r = writeSubX64 w old rv) :
    writeSubX64 w s1r v = writeSubX64 w old v := by
  rcases h with rfl | ⟨rv, rfl⟩
  · rfl
  · exact writeSubX64_idem w old rv v

private theorem setWidth_toNat_mod_wbits (w : Vll.Width) (v : BitVec 64) :
    (v.setWidth w.bits).toNat % w.bits = v.toNat % w.bits := by
  cases w with
  | w8 =>
    simp only [Vll.Width.bits, BitVec.toNat_setWidth]
    exact Nat.mod_mod_of_dvd v.toNat (by decide)
  | w16 =>
    simp only [Vll.Width.bits, BitVec.toNat_setWidth]
    exact Nat.mod_mod_of_dvd v.toNat (by decide)
  | w32 =>
    simp only [Vll.Width.bits, BitVec.toNat_setWidth]
    exact Nat.mod_mod_of_dvd v.toNat (by decide)
  | w64 => simp [Vll.Width.bits, BitVec.setWidth_eq]

private theorem cond_testSelf_aluFlags_eq (op : CoreAlu) (w : Vll.Width)
    (hop : op = .mul ∨ op = .shl ∨ op = .lshr ∨ op = .ashr)
    (a b : BitVec w.bits) (f : StatusFlags) (af : Bool) (cc : CondCode) :
    cc.interp (testFlags (op.eval w a b) (op.eval w a b) af) =
      cc.interp (x64AluFlags op w true a b f) := by
  rcases hop with rfl | rfl | rfl | rfl <;> cases cc <;>
    simp [CondCode.interp, testFlags, x64AluFlags, StatusFlags.from_result, BitVec.and_self]

private theorem aluFlags_add_comm (w : Vll.Width) (a b : BitVec w.bits) (f : StatusFlags)
    (cc : CondCode) :
    cc.interp (x64AluFlags .add w true b a f) = cc.interp (x64AluFlags .add w true a b f) := by
  apply cond_statusFlags_of_fields
  · simp only [x64AluFlags, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      StatusFlags.from_result, BitVec.add_comm b a]
    rw [Int.add_comm b.unsigned]
  · simp [x64AluFlags, StatusFlags.from_result, BitVec.add_comm b a]
  · simp [x64AluFlags, StatusFlags.from_result, BitVec.add_comm b a]
  · simp [x64AluFlags, StatusFlags.from_result, BitVec.add_comm b a]
  · simp [x64AluFlags, StatusFlags.from_result, BitVec.add_comm b a, Int.add_comm]

private theorem aluFlags_comm (k : AluBinKind) (op : CoreAlu) (w : Vll.Width)
    (hk : (op = .add ∧ k = .add) ∨ (op = .and ∧ k = .and) ∨
          (op = .or ∧ k = .or) ∨ (op = .xor ∧ k = .xor))
    (a b : BitVec w.bits) (f : StatusFlags) (cc : CondCode) :
    cc.interp (x64AluFlags op w true b a f) = cc.interp (x64AluFlags op w true a b f) := by
  rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact aluFlags_add_comm w a b f cc
  · simp [x64AluFlags, x64TestFlags, BitVec.and_comm]
  · simp [x64AluFlags, BitVec.or_comm]
  · simp [x64AluFlags, BitVec.xor_comm]

private theorem x64AluFlags_sf_true (op : CoreAlu) (w : Vll.Width) (a b : BitVec w.bits)
    (f₁ f₂ : StatusFlags) :
    x64AluFlags op w true a b f₁ = x64AluFlags op w true a b f₂ := by
  cases op <;> rfl

/-! ## 2. Private ALU Compilation Proofs -/

private def exactBinFlags (op : CoreAlu) (w : Vll.Width) (a b : BitVec w.bits)
    (f₀ st : StatusFlags) : Prop :=
  match op with
  | .add | .sub | .and | .or | .xor =>
    ∀ cc : CondCode, cc.interp st = cc.interp (x64AluFlags op w true a b f₀)
  | _ => True

private def coreAluToBin? : CoreAlu → Option AluBinKind
  | .add => some .add | .sub => some .sub | .and => some .and
  | .or => some .or | .xor => some .xor | .mul => some .mul | _ => none

private theorem mk_machineData_eq (s : MachineData) (rd : Reg64) (v₁ v₂ : BitVec 64)
    (st : StatusFlags) (hv : v₁ = v₂) :
    ({ regs := s.regs.set64 rd v₁, zmms := s.zmms, status := st, df := s.df,
       dmem := s.dmem } : MachineData) =
      { s with regs := s.regs.set64 rd v₂, status := st } := by
  subst hv; rfl

private theorem fallsTo_aluBinI_reg (op : CoreAlu) (k : AluBinKind) (w : Vll.Width)
    (hk : coreAluToBin? op = some k) (h8 : k = .mul → w ≠ .w8)
    (s : MachineData) (rd rs : Reg64) :
    Directive.FallsTo (.instr (aluBinI w.toX64 k rd (.reg (regW w.toX64 rs)))) s
      (fun s' => ∃ st, exactBinFlags op w ((s.regs.get64 rd).setWidth w.bits)
        ((s.regs.get64 rs).setWidth w.bits) s.status st ∧
        s' = { s with
          regs := s.regs.set64 rd (writeSubX64 w (s.regs.get64 rd)
            (k.eval ((s.regs.get64 rd).setWidth w.bits) ((s.regs.get64 rs).setWidth w.bits))),
          status := st }) := by
  intro _ _ _ _ _ hcont
  cases op with
  | shl | lshr | ashr => simp [coreAluToBin?] at hk
  | add =>
    simp only [coreAluToBin?, Option.some.injEq] at hk; subst hk
    cases w <;> simp only [Vll.Width.toX64, regW, t_step_simp, Reg64s.set] <;>
      refine hcont _ ⟨_, ?_, by
        congr 2; first
        | (rw [replaceLow_8_eq_writeSubX64, BitVec.add_comm]; rfl)
        | (rw [replaceLow_16_eq_writeSubX64, BitVec.add_comm]; rfl)
        | (simp only [writeSubX64, AluBinKind.eval]; (try repeat rw [BitVec.setWidth_eq]);
            try rw [BitVec.add_comm])⟩ <;>
      exact fun cc => by
        simp only [x64AluFlags, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          StatusFlags.from_result]
        dsimp only [Vll.Width.bits, _root_.Width.bits]
        repeat rw [BitVec.setWidth_eq]
        apply cond_statusFlags_of_fields <;>
          (dsimp only; first | rfl | (rw [BitVec.add_comm]; try rw [Int.add_comm]))
  | sub =>
    simp only [coreAluToBin?, Option.some.injEq] at hk; subst hk
    cases w <;> simp only [Vll.Width.toX64, regW, t_step_simp, Reg64s.set] <;>
      refine hcont _ ⟨_, ?_, mk_machineData_eq s rd _ _ _ (by
        first
        | rw [replaceLow_8_eq_writeSubX64]; rfl
        | rw [replaceLow_16_eq_writeSubX64]; rfl
        | (simp only [writeSubX64, AluBinKind.eval]; try rw [BitVec.zeroExtend_eq_setWidth]
           try repeat rw [BitVec.setWidth_eq]))⟩ <;>
      exact fun cc => by
        simp only [x64AluFlags, x64CmpFlags, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          StatusFlags.from_result]
        all_goals (
          dsimp only [Vll.Width.bits, _root_.Width.bits]
          try repeat rw [BitVec.setWidth_eq]
          try (apply cond_statusFlags_of_fields <;> dsimp only <;> rfl))
  | and | or | xor =>
    simp only [coreAluToBin?, Option.some.injEq] at hk; subst hk
    cases w <;> simp only [Vll.Width.toX64, regW, t_step_simp, Reg64s.set, Effects.All] <;>
      intro af <;> refine hcont _ ⟨_, ?_, mk_machineData_eq s rd _ _ _ (by
        first
        | rw [replaceLow_8_eq_writeSubX64]; rfl
        | rw [replaceLow_16_eq_writeSubX64]; rfl
        | (simp only [writeSubX64, AluBinKind.eval]; try rw [BitVec.zeroExtend_eq_setWidth]
           try repeat rw [BitVec.setWidth_eq]))⟩ <;>
      exact fun cc => by
        simp only [x64AluFlags, x64TestFlags, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          StatusFlags.from_result]
        dsimp only [Vll.Width.bits, _root_.Width.bits]
        try repeat rw [BitVec.setWidth_eq]
        apply cond_statusFlags_of_fields <;> dsimp only <;> rfl
  | mul =>
    simp only [coreAluToBin?, Option.some.injEq] at hk; subst hk
    cases w
    · exact absurd rfl (h8 rfl)
    · simp only [Vll.Width.toX64, regW, t_step_simp, Reg64s.set, Effects.All]
      intro _ _ _ _
      exact hcont _ ⟨_, trivial, mk_machineData_eq s rd _ _ _ (by
        rw [replaceLow_16_eq_writeSubX64]; dsimp only [writeSubX64, AluBinKind.eval, Vll.Width.bits]
        try repeat rw [BitVec.setWidth_eq])⟩
    · simp only [Vll.Width.toX64, regW, t_step_simp, Reg64s.set, Effects.All]
      intro _ _ _ _
      exact hcont _ ⟨_, trivial, mk_machineData_eq s rd _ _ _ (by
        dsimp only [writeSubX64, AluBinKind.eval, Vll.Width.bits]
        all_goals (try rw [BitVec.zeroExtend_eq_setWidth]; try repeat rw [BitVec.setWidth_eq]))⟩
    · simp only [Vll.Width.toX64, regW, t_step_simp, Reg64s.set, Effects.All]
      intro _ _ _ _
      exact hcont _ ⟨_, trivial, mk_machineData_eq s rd _ _ _ (by
        dsimp only [writeSubX64, AluBinKind.eval, Vll.Width.bits]
        try repeat rw [BitVec.setWidth_eq])⟩

private theorem fallsTo_aluBinI_imm (op : CoreAlu) (k : AluBinKind) (w : Vll.Width)
    (hk : coreAluToBin? op = some k) (h8 : k = .mul → w ≠ .w8)
    (s : MachineData) (rd : Reg64) (cb : BitVec w.toX64.bits) :
    Directive.FallsTo (.instr (aluBinI w.toX64 k rd (immBitsOp w.toX64 cb))) s
      (fun s' => ∃ st, exactBinFlags op w ((s.regs.get64 rd).setWidth w.bits)
        (cb.setWidth w.bits) s.status st ∧
        s' = { s with
          regs := s.regs.set64 rd (writeSubX64 w (s.regs.get64 rd)
            (k.eval ((s.regs.get64 rd).setWidth w.bits) (cb.setWidth w.bits))),
          status := st }) := by
  intro _ _ _ _ _ hcont
  cases op with
  | shl | lshr | ashr => simp [coreAluToBin?] at hk
  | add =>
    simp only [coreAluToBin?, Option.some.injEq] at hk; subst hk
    cases w <;>
      (simp only [Vll.Width.toX64, immBitsOp, regW, t_step_simp, Reg64s.set, BitVec.setWidth_eq]
       (try rw [Int64.toBitVec_ofBitVec, truncate_signExtend_64 (by decide)])
       (try rw [Int64.toBitVec_ofBitVec, BitVec.signExtend_eq])) <;>
      refine hcont _ ⟨_, ?_, by
        congr 2; first
        | (rw [replaceLow_8_eq_writeSubX64, BitVec.add_comm]; rfl)
        | (rw [replaceLow_16_eq_writeSubX64, BitVec.add_comm]; rfl)
        | (simp only [writeSubX64, AluBinKind.eval]; (try repeat rw [BitVec.setWidth_eq]);
            try rw [BitVec.add_comm])⟩ <;>
      exact fun cc => by
        simp only [x64AluFlags, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          StatusFlags.from_result]
        dsimp only [Vll.Width.bits, _root_.Width.bits]
        repeat rw [BitVec.setWidth_eq]
        apply cond_statusFlags_of_fields <;>
          (dsimp only; first | rfl | (rw [BitVec.add_comm]; try rw [Int.add_comm]))
  | sub =>
    simp only [coreAluToBin?, Option.some.injEq] at hk; subst hk
    cases w <;>
      (simp only [Vll.Width.toX64, immBitsOp, regW, t_step_simp, Reg64s.set, BitVec.setWidth_eq]
       (try rw [Int64.toBitVec_ofBitVec, truncate_signExtend_64 (by decide)])
       (try rw [Int64.toBitVec_ofBitVec, BitVec.signExtend_eq])) <;>
      refine hcont _ ⟨_, ?_, mk_machineData_eq s rd _ _ _ (by
        first
        | rw [replaceLow_8_eq_writeSubX64]; rfl
        | rw [replaceLow_16_eq_writeSubX64]; rfl
        | (simp only [writeSubX64, AluBinKind.eval]; try rw [BitVec.zeroExtend_eq_setWidth]
           try repeat rw [BitVec.setWidth_eq]))⟩ <;>
      exact fun cc => by
        simp only [x64AluFlags, x64CmpFlags, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          StatusFlags.from_result]
        all_goals (
          dsimp only [Vll.Width.bits, _root_.Width.bits]
          try repeat rw [BitVec.setWidth_eq]
          try (apply cond_statusFlags_of_fields <;> dsimp only <;> rfl))
  | and | or | xor =>
    simp only [coreAluToBin?, Option.some.injEq] at hk; subst hk
    cases w <;>
      (simp only [Vll.Width.toX64, immBitsOp, regW, t_step_simp, Reg64s.set,
         Effects.All, BitVec.setWidth_eq]
       (try rw [Int64.toBitVec_ofBitVec, truncate_signExtend_64 (by decide)])
       (try rw [Int64.toBitVec_ofBitVec, BitVec.signExtend_eq])) <;>
      intro af <;> refine hcont _ ⟨_, ?_, mk_machineData_eq s rd _ _ _ (by
        first
        | rw [replaceLow_8_eq_writeSubX64]; rfl
        | rw [replaceLow_16_eq_writeSubX64]; rfl
        | (simp only [writeSubX64, AluBinKind.eval]; try rw [BitVec.zeroExtend_eq_setWidth]
           try repeat rw [BitVec.setWidth_eq]))⟩ <;>
      exact fun cc => by
        simp only [x64AluFlags, x64TestFlags, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
          StatusFlags.from_result]
        dsimp only [Vll.Width.bits, _root_.Width.bits]
        try repeat rw [BitVec.setWidth_eq]
        apply cond_statusFlags_of_fields <;> dsimp only <;> rfl
  | mul =>
    simp only [coreAluToBin?, Option.some.injEq] at hk; subst hk
    cases w
    · exact absurd rfl (h8 rfl)
    · simp only [Vll.Width.toX64, immBitsOp, regW, t_step_simp, Reg64s.set, Effects.All]
      rw [Int64.toBitVec_ofBitVec, truncate_signExtend_64 (by decide)]
      intro _ _ _ _
      exact hcont _ ⟨_, trivial, mk_machineData_eq s rd _ _ _ (by
        rw [replaceLow_16_eq_writeSubX64]; dsimp only [writeSubX64, AluBinKind.eval, Vll.Width.bits]
        try repeat rw [BitVec.setWidth_eq])⟩
    · simp only [Vll.Width.toX64, immBitsOp, regW, t_step_simp, Reg64s.set, Effects.All]
      rw [Int64.toBitVec_ofBitVec, truncate_signExtend_64 (by decide)]
      intro _ _ _ _
      exact hcont _ ⟨_, trivial, mk_machineData_eq s rd _ _ _ (by
        dsimp only [writeSubX64, AluBinKind.eval, Vll.Width.bits]
        rw [BitVec.zeroExtend_eq_setWidth]; try repeat rw [BitVec.setWidth_eq])⟩
    · simp only [Vll.Width.toX64, immBitsOp, regW, t_step_simp, Reg64s.set, Effects.All,
        BitVec.setWidth_eq]
      rw [Int64.toBitVec_ofBitVec, BitVec.signExtend_eq]
      intro _ _ _ _
      exact hcont _ ⟨_, trivial, mk_machineData_eq s rd _ _ _ (by
        dsimp only [writeSubX64, AluBinKind.eval, Vll.Width.bits]
        try repeat rw [BitVec.setWidth_eq])⟩

private theorem wp_asmX64BinCore [Host] {E : Int64 → MachineData → Prop} (op : CoreAlu)
    (k : AluBinKind) (w : Vll.Width) (hk : coreAluToBin? op = some k) (h8 : k = .mul → w ≠ .w8)
    (s : MachineData) (rd lhs : Reg64) (rhs : Src x64Arch)
    (hrd : rd ∉ x64Scratch) (hlhs : lhs ∉ x64Scratch)
    (hrhs : ∀ rs, rhs = .reg rs → rs ∉ x64Scratch) :
    let a := (s.regs.get64 lhs).setWidth w.bits
    let b := rhs.evalW w s.regs.get64
    _root_.Program.wp (emitClean (asmX64BinCoreIns w.toX64 k rd lhs rhs))
      (fun s' => exactBinFlags op w a b s.status s'.status ∧
        s'.regs.get64 rd = writeSubX64 w (s.regs.get64 rd) (k.eval a b) ∧
        (∀ r, r ≠ rd → r ∉ x64Scratch → s'.regs.get64 r = s.regs.get64 r) ∧
        s'.zmms = s.zmms ∧ s'.dmem = s.dmem) E s := by
  intro a b
  have hlhs11 := (ne_of_not_mem_x64Scratch hlhs).2
  have hrd10 := (ne_of_not_mem_x64Scratch hrd).1
  have hrd11 := (ne_of_not_mem_x64Scratch hrd).2
  cases rhs with
  | reg rs =>
    have hrs := hrhs rs rfl
    have hrs11 := (ne_of_not_mem_x64Scratch hrs).2
    dsimp only [asmX64BinCoreIns]
    by_cases h1 : lhs == rd
    · have h1eq := (beq_reg64_iff lhs rd).1 h1; subst h1eq
      simp only [h1, ↓reduceIte, emitClean_cons, emitClean_nil]
      refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_aluBinI_reg op k w hk h8 s lhs rs)) ?_
      rintro s' ⟨st, hex, rfl⟩
      exact ⟨hex, Reg64s.get64_set64_same ..,
        fun r hr _ => Reg64s.get64_set64_of_ne _ lhs r _ hr.symm, rfl, rfl⟩
    · simp only [h1, Bool.false_eq_true, ↓reduceIte]
      by_cases h2 : k.isComm && (rs == rd)
      · have ⟨hc, hrs_eq⟩ : k.isComm = true ∧ rs = rd := by
          simp only [Bool.and_eq_true, beq_reg64_iff] at h2; exact h2
        subst hrs_eq
        simp only [h2, ↓reduceIte, emitClean_cons, emitClean_nil]
        have hcomm : (op = .add ∧ k = .add) ∨ (op = .and ∧ k = .and) ∨
            (op = .or ∧ k = .or) ∨ (op = .xor ∧ k = .xor) ∨ (op = .mul ∧ k = .mul) := by
          cases op <;> simp_all [coreAluToBin?] <;> cases k <;> simp_all [AluBinKind.isComm]
        refine Program.wp.mono (Directive.FallsTo.wp
          (fallsTo_aluBinI_reg op k w hk h8 s rs lhs)) ?_
        rintro s' ⟨st, hex, rfl⟩
        refine ⟨?_, ?_, fun r hr _ => Reg64s.get64_set64_of_ne _ rs r _ hr.symm, rfl, rfl⟩
        · rcases hcomm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact fun cc => (hex cc).trans (aluFlags_comm .add .add w (.inl ⟨rfl, rfl⟩) _ _ _ cc)
          · exact fun cc => (hex cc).trans
              (aluFlags_comm .and .and w (.inr (.inl ⟨rfl, rfl⟩)) _ _ _ cc)
          · exact fun cc => (hex cc).trans
              (aluFlags_comm .or .or w (.inr (.inr (.inl ⟨rfl, rfl⟩))) _ _ _ cc)
          · exact fun cc => (hex cc).trans
              (aluFlags_comm .xor .xor w (.inr (.inr (.inr ⟨rfl, rfl⟩))) _ _ _ cc)
          · exact trivial
        · rw [Reg64s.get64_set64_same]
          rcases hcomm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
            simp [AluBinKind.eval, a, b, Src.evalW, Src.eval, BitVec.add_comm, BitVec.and_comm,
              BitVec.or_comm, BitVec.xor_comm, BitVec.mul_comm]
      · simp only [h2, Bool.false_eq_true, ↓reduceIte]
        by_cases h3 : rs != rd
        · have h3ne := (bne_reg64_iff rs rd).1 h3
          simp only [h3, ↓reduceIte, emitClean_cons, emitClean_nil]
          refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_movSubW w s rd lhs)) ?_
          rintro s1 rfl
          refine Program.wp.mono (Directive.FallsTo.wp
            (fallsTo_aluBinI_reg op k w hk h8 _ rd rs)) ?_
          rintro s2 ⟨st, hex, rfl⟩
          have hrd1 : ((s.regs.set64 rd (writeSubX64 w (s.regs.get64 rd) a)).get64 rd).setWidth
              w.bits = a := by rw [Reg64s.get64_set64_same, writeSubX64_setWidth]
          have hrs1 : ((s.regs.set64 rd (writeSubX64 w (s.regs.get64 rd) a)).get64 rs).setWidth
              w.bits = b := by rw [Reg64s.get64_set64_of_ne _ rd rs _ h3ne.symm]; rfl
          dsimp only at hex ⊢
          rw [hrd1, hrs1] at hex
          refine ⟨hex, ?_, fun r hr _ => ?_, rfl, rfl⟩
          · rw [Reg64s.get64_set64_same, hrd1, hrs1, Reg64s.get64_set64_same, writeSubX64_idem]
          · rw [Reg64s.get64_set64_of_ne _ rd r _ hr.symm,
              Reg64s.get64_set64_of_ne _ rd r _ hr.symm]
        · simp only [h3, Bool.false_eq_true, ↓reduceIte, emitClean_cons, emitClean_nil]
          refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_movSubW w s .r11 lhs)) ?_
          rintro s1 rfl
          refine Program.wp.cons (Directive.FallsTo.wp
            (fallsTo_aluBinI_reg op k w hk h8 _ .r11 rs)) ?_
          rintro s2 ⟨st, hex, rfl⟩
          refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movSubW w _ rd .r11)) ?_
          rintro s3 rfl
          have h11_1 : ((s.regs.set64 .r11 (writeSubX64 w (s.regs.get64 .r11) a)).get64
              .r11).setWidth w.bits = a := by rw [Reg64s.get64_set64_same, writeSubX64_setWidth]
          have hrs_1 : ((s.regs.set64 .r11 (writeSubX64 w (s.regs.get64 .r11) a)).get64
              rs).setWidth w.bits = b := by
            rw [Reg64s.get64_set64_of_ne _ .r11 rs _ hrs11.symm]; rfl
          dsimp only at hex ⊢
          rw [h11_1, hrs_1] at hex
          refine ⟨hex, ?_, fun r hr hsc => ?_, rfl, rfl⟩
          · rw [Reg64s.get64_set64_same, Reg64s.get64_set64_of_ne _ .r11 rd _ hrd11.symm,
              Reg64s.get64_set64_of_ne _ .r11 rd _ hrd11.symm,
              Reg64s.get64_set64_same, h11_1, hrs_1, writeSubX64_setWidth]
          · have hr11 := (ne_of_not_mem_x64Scratch hsc).2
            rw [Reg64s.get64_set64_of_ne _ rd r _ hr.symm,
              Reg64s.get64_set64_of_ne _ .r11 r _ hr11.symm,
              Reg64s.get64_set64_of_ne _ .r11 r _ hr11.symm]
  | imm imm =>
    dsimp only [asmX64BinCoreIns]
    have runPre : ∀ (s₀ : MachineData)
        (hagree : ∀ r, r ≠ .r10 → s₀.regs.get64 r = s.regs.get64 r)
        (hzm : s₀.zmms = s.zmms) (hdm : s₀.dmem = s.dmem),
        _root_.Program.wp (emitClean (if lhs == rd then [] else [movSubWI w.toX64 rd lhs]))
          (fun s1 => (s1.regs.get64 rd).setWidth w.bits = a ∧
            s1.regs.get64 .r10 = s₀.regs.get64 .r10 ∧
            (∀ r, r ≠ rd → r ≠ .r10 → s1.regs.get64 r = s.regs.get64 r) ∧
            (s1.regs.get64 rd = s.regs.get64 rd ∨
              ∃ rv, s1.regs.get64 rd = writeSubX64 w (s.regs.get64 rd) rv) ∧
            s1.zmms = s.zmms ∧ s1.dmem = s.dmem ∧ s1.status = s₀.status) E s₀ := by
      intro s₀ hagree hzm hdm
      by_cases h1 : lhs == rd
      · have h1eq := (beq_reg64_iff lhs rd).1 h1; subst h1eq
        simp only [h1, ↓reduceIte, emitClean_nil]
        exact _root_.Program.wp_nil ⟨by rw [hagree lhs (ne_of_not_mem_x64Scratch hlhs).1], rfl,
          fun r _ hr10 => hagree r hr10, Or.inl (hagree lhs hrd10), hzm, hdm, rfl⟩
      · simp only [h1, Bool.false_eq_true, ↓reduceIte, emitClean_cons, emitClean_nil]
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movSubW w s₀ rd lhs)) ?_
        rintro s1 rfl
        have hlhs0 : s₀.regs.get64 lhs = s.regs.get64 lhs :=
          hagree lhs (ne_of_not_mem_x64Scratch hlhs).1
        have hrd0 : s₀.regs.get64 rd = s.regs.get64 rd := hagree rd hrd10
        refine ⟨by rw [Reg64s.get64_set64_same, writeSubX64_setWidth, hlhs0],
          Reg64s.get64_set64_of_ne _ rd .r10 _ hrd10,
          fun r hr hr10 => (Reg64s.get64_set64_of_ne _ rd r _ hr.symm).trans (hagree r hr10),
          Or.inr ⟨a, by rw [Reg64s.get64_set64_same, hrd0, hlhs0]⟩, hzm, hdm, rfl⟩
    split
    · simp only [emitClean_append]
      refine Program.wp.append (runPre s (fun _ _ => rfl) rfl rfl) ?_
      rintro s1 ⟨hrd1, _, hr1, hold1, hzm1, hdm1, hst1⟩
      simp only [emitClean_cons, emitClean_nil]
      refine Program.wp.mono (Directive.FallsTo.wp
        (fallsTo_aluBinI_imm op k w hk h8 s1 rd (imm.setWidth w.toX64.bits))) ?_
      rintro s2 ⟨st, hex, rfl⟩
      have hcb : (imm.setWidth w.toX64.bits).setWidth w.bits = b := by
        cases w <;> simp [Vll.Width.toX64, Vll.Width.bits, b, Src.evalW, Src.eval]
      rw [hcb, hst1, hrd1] at hex
      refine ⟨hex, ?_, fun r hr hsc => ?_, hzm1, hdm1⟩
      · rw [Reg64s.get64_set64_same, hrd1, hcb, writeSubX64_of_pre w _ _ _ hold1]
      · rw [Reg64s.get64_set64_of_ne _ rd r _ hr.symm]
        exact hr1 r hr (ne_of_not_mem_x64Scratch hsc).1
    · rename_i hnofit
      have hw64 : w = .w64 := by
        cases w with
        | w64 => rfl
        | w8 | w16 | w32 =>
          exact False.elim (hnofit (by simp only [Vll.Width.toX64,
            show (_root_.Width.W8 != .W64) = true from by decide,
            show (_root_.Width.W16 != .W64) = true from by decide,
            show (_root_.Width.W32 != .W64) = true from by decide, Bool.true_or]))
      subst hw64
      simp only [Vll.Width.toX64, Vll.Width.bits, BitVec.setWidth_eq, emitClean_append,
        emitClean_cons, emitClean_nil]
      refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s .r10 imm)) ?_
      rintro s1 rfl
      refine Program.wp.append (runPre _ (fun r hr => Reg64s.get64_set64_of_ne _ .r10 r _ hr.symm)
        rfl rfl) ?_
      rintro s2 ⟨hrd2, hr10_2, hr2, _, hzm2, hdm2, hst2⟩
      refine Program.wp.mono (Directive.FallsTo.wp
        (fallsTo_aluBinI_reg op k .w64 hk h8 s2 rd .r10)) ?_
      rintro s3 ⟨st, hex, rfl⟩
      have hr10_val : s2.regs.get64 .r10 = imm := by
        refine hr10_2.trans ?_; dsimp only; exact Reg64s.get64_set64_same ..
      have hrd2' : s2.regs.get64 rd = a := by
        simpa [Vll.Width.bits, BitVec.setWidth_eq] using hrd2
      have hex' : exactBinFlags op .w64 a b s.status st := by
        simpa [Vll.Width.bits, BitVec.setWidth_eq, hst2, hrd2', hr10_val, b,
          Src.evalW, Src.eval] using hex
      refine ⟨hex', ?_, fun r hr hsc => ?_, hzm2, hdm2⟩
      · simp only [Reg64s.get64_set64_same, Vll.Width.bits, BitVec.setWidth_eq,
          writeSubX64] at hrd2 ⊢
        rw [hrd2, hr10_val]; rfl
      · rw [Reg64s.get64_set64_of_ne _ rd r _ hr.symm]
        exact hr2 r hr (ne_of_not_mem_x64Scratch hsc).1

private theorem wp_shiftMaskRcx_low [Host] {E : Int64 → MachineData → Prop} (w : Vll.Width)
    (hw : w = .w8 ∨ w = .w16) (s s₀ : MachineData) (a b : BitVec w.bits)
    (hb : (s.regs.get64 .rcx).setWidth w.bits = b)
    (hr10 : s.regs.get64 .r10 = s₀.regs.get64 .rcx)
    (hr11 : (s.regs.get64 .r11).setWidth w.bits = a)
    (hkeep : ∀ r, r ≠ .rcx → r ∉ x64Scratch → s.regs.get64 r = s₀.regs.get64 r)
    (hzm : s.zmms = s₀.zmms) (hdm : s.dmem = s₀.dmem) :
    _root_.Program.wp (emitClean (shiftMaskRcxIns w.toX64)) (fun s4 =>
      (∀ [Labels] (p : Std.Rco Int64),
        ShiftCountExpr.cl.interpMasked s4 p w.toX64 = b.toNat % w.bits) ∧
      s4.regs.get64 .r10 = s₀.regs.get64 .rcx ∧
      (s4.regs.get64 .r11).setWidth w.bits = a ∧
      (∀ r, r ≠ .rcx → r ∉ x64Scratch → s4.regs.get64 r = s₀.regs.get64 r) ∧
      s4.zmms = s₀.zmms ∧ s4.dmem = s₀.dmem) E s := by
  rcases hw with rfl | rfl
  · simp only [Vll.Width.toX64, shiftMaskRcxIns, emitClean_cons, emitClean_nil]
    refine _root_.Program.wp_singleton fun _ _ => ?_
    simp only [t_step_simp, ConstExpr.interp, Effects.All]; intro _
    refine Or.inl ⟨trivial, ?_, ?_, ?_, ?_, hzm, hdm⟩
    · intro _ _
      have hm : (((s.regs.get64 .rcx).setWidth 32 &&&
          BitVec.setWidth 32 (7 : Int64).toBitVec).setWidth 64 |>.take 8).toNat =
          (s.regs.get64 .rcx).toNat % 8 := by
        rw [show BitVec.setWidth 32 (7 : Int64).toBitVec = BitVec.ofNat 32 (2 ^ 3 - 1) from rfl]
        simp only [BitVec.take, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
          BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (by decide : 2 ^ 3 - 1 < 2 ^ 32), Nat.and_two_pow_sub_one_eq_mod,
          Nat.mod_mod_of_dvd _ (by decide : 2 ^ 3 ∣ 2 ^ 32)]
        have hlt : (s.regs.get64 .rcx).toNat % 8 < 8 := Nat.mod_lt _ (by decide)
        rw [show (2 ^ 3 : Nat) = 8 from rfl,
          Nat.mod_eq_of_lt (by omega : (s.regs.get64 .rcx).toNat % 8 < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : (s.regs.get64 .rcx).toNat % 8 < 2 ^ 8)]
      have hlt8 : (s.regs.get64 .rcx).toNat % 8 < 8 := Nat.mod_lt _ (by decide)
      have hb8 : b.toNat % 8 = (s.regs.get64 .rcx).toNat % 8 := by
        rw [← hb, Vll.Width.bits, BitVec.toNat_setWidth, Nat.mod_mod_of_dvd _ (by decide)]
      have hrcx_val : ((s.regs.set64 .rcx (BitVec.zeroExtend 64
          ((s.regs.get64 .rcx).setWidth 32 &&&
            BitVec.truncate 32 (7 : Int64).toBitVec))).rcx.toBitVec) =
          ((s.regs.get64 .rcx).setWidth 32 &&&
            BitVec.setWidth 32 (7 : Int64).toBitVec).setWidth 64 := by
        change (s.regs.set64 .rcx _).get64 .rcx = _
        rw [Reg64s.get64_set64_same]
      simp only [Vll.Width.bits, hrcx_val]
      rw [hm, hb8, show (0x1f : Nat) = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
        Nat.mod_eq_of_lt (by omega : (s.regs.get64 .rcx).toNat % 8 < 32)]
    · rw [Reg64s.get64_set64_of_ne _ .rcx .r10 _ (by decide), hr10]
    · rw [Reg64s.get64_set64_of_ne _ .rcx .r11 _ (by decide), hr11]
    · intro r hr hsc; rw [Reg64s.get64_set64_of_ne _ .rcx r _ hr.symm]; exact hkeep r hr hsc
  · simp only [Vll.Width.toX64, shiftMaskRcxIns, emitClean_cons, emitClean_nil]
    refine _root_.Program.wp_singleton fun _ _ => ?_
    simp only [t_step_simp, ConstExpr.interp, Effects.All]; intro _
    refine Or.inl ⟨trivial, ?_, ?_, ?_, ?_, hzm, hdm⟩
    · intro _ _
      have hm : (((s.regs.get64 .rcx).setWidth 32 &&&
          BitVec.setWidth 32 (15 : Int64).toBitVec).setWidth 64 |>.take 8).toNat =
          (s.regs.get64 .rcx).toNat % 16 := by
        rw [show BitVec.setWidth 32 (15 : Int64).toBitVec = BitVec.ofNat 32 (2 ^ 4 - 1) from rfl]
        simp only [BitVec.take, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
          BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
        rw [Nat.mod_eq_of_lt (by decide : 2 ^ 4 - 1 < 2 ^ 32), Nat.and_two_pow_sub_one_eq_mod,
          Nat.mod_mod_of_dvd _ (by decide : 2 ^ 4 ∣ 2 ^ 32)]
        have hlt : (s.regs.get64 .rcx).toNat % 16 < 16 := Nat.mod_lt _ (by decide)
        rw [show (2 ^ 4 : Nat) = 16 from rfl,
          Nat.mod_eq_of_lt (by omega : (s.regs.get64 .rcx).toNat % 16 < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : (s.regs.get64 .rcx).toNat % 16 < 2 ^ 8)]
      have hlt16 : (s.regs.get64 .rcx).toNat % 16 < 16 := Nat.mod_lt _ (by decide)
      have hb16 : b.toNat % 16 = (s.regs.get64 .rcx).toNat % 16 := by
        rw [← hb, Vll.Width.bits, BitVec.toNat_setWidth, Nat.mod_mod_of_dvd _ (by decide)]
      have hrcx_val : ((s.regs.set64 .rcx (BitVec.zeroExtend 64
          ((s.regs.get64 .rcx).setWidth 32 &&&
            BitVec.truncate 32 (15 : Int64).toBitVec))).rcx.toBitVec) =
          ((s.regs.get64 .rcx).setWidth 32 &&&
            BitVec.setWidth 32 (15 : Int64).toBitVec).setWidth 64 := by
        change (s.regs.set64 .rcx _).get64 .rcx = _
        rw [Reg64s.get64_set64_same]
      simp only [Vll.Width.bits, hrcx_val]
      rw [hm, hb16, show (0x1f : Nat) = 2 ^ 5 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
        Nat.mod_eq_of_lt (by omega : (s.regs.get64 .rcx).toNat % 16 < 32)]
    · rw [Reg64s.get64_set64_of_ne _ .rcx .r10 _ (by decide), hr10]
    · rw [Reg64s.get64_set64_of_ne _ .rcx .r11 _ (by decide), hr11]
    · intro r hr hsc; rw [Reg64s.get64_set64_of_ne _ .rcx r _ hr.symm]; exact hkeep r hr hsc

private theorem fallsTo_shiftOp (w : Vll.Width) (op : CoreAlu) (sk : ShiftKind)
    (hsk : (op = .shl ∧ sk = .shl) ∨ (op = .lshr ∧ sk = .lshr) ∨ (op = .ashr ∧ sk = .ashr))
    (ce : ShiftCountExpr) (k : Nat) (hk_lt : k < w.bits) (hw32_nz : w = .w32 → k ≠ 0)
    (s₀ : MachineData) (dst : Reg64)
    (hk_eq : ∀ [Labels] (p : Std.Rco Int64), ce.interpMasked s₀ p w.toX64 = k) :
    Directive.FallsTo (insW w.toX64 (sk.toOp (.reg (regW w.toX64 dst)) ce)) s₀
      (fun s' => ∃ st, s' =
        { s₀ with
          regs := s₀.regs.set64 dst (writeSubX64 w (s₀.regs.get64 dst)
            (sk.eval ((s₀.regs.get64 dst).setWidth w.bits) k))
          status := st }) := by
  intro _ q nextk _ P hc
  have hkp' : ce.interpMasked s₀ q w.toX64 = k := hk_eq q
  have closeGoal : ∀ (st : StatusFlags) (v : BitVec 64),
      v = writeSubX64 w (s₀.regs.get64 dst)
        (sk.eval ((s₀.regs.get64 dst).setWidth w.bits) k) →
      Effects.All P (nextk { s₀ with regs := s₀.regs.set64 dst v, status := st }) := by
    intro st v hv; subst hv; exact hc _ ⟨st, rfl⟩
  cases w <;> rcases hsk with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;>
    (have hkp'' := hkp'
     dsimp only [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, Vll.Width.toX64] at hkp''
     simp only [ShiftKind.toOp, Vll.Width.toX64, insW, regW, t_step_simp, Reg64s.set]
     rw [hkp'']) <;>
    (by_cases hk0 : k = 0
     · subst hk0
       first
       | exact absurd rfl (hw32_nz rfl)
       | (simp only [beq_self_eq_true, ↓reduceIte]
          refine closeGoal s₀.status _ ?_
          simp only [ShiftKind.eval, BitVec.shiftLeft_zero, BitVec.ushiftRight_zero,
            BitVec.sshiftRight_zero]
          try rw [replaceLow_8_eq_writeSubX64]
          try rw [replaceLow_16_eq_writeSubX64]
          all_goals (dsimp only [writeSubX64, Vll.Width.bits]; try rw [BitVec.setWidth_eq]))
     · simp only [beq_false_of_ne hk0, Bool.false_eq_true, ↓reduceIte, Effects.All]
       (try (have hlt1 : k < _root_.Width.W8.bits := hk_lt; simp only [hlt1, ↓reduceIte]))
       (try (have hlt1 : k < _root_.Width.W16.bits := hk_lt; simp only [hlt1, ↓reduceIte]))
       (try (have hlt1 : k < _root_.Width.W32.bits := hk_lt; simp only [hlt1, ↓reduceIte]))
       (try (have hlt1 : k < _root_.Width.W64.bits := hk_lt; simp only [hlt1, ↓reduceIte]))
       intro _; split
       · refine closeGoal _ _ ?_
         first
         | rw [replaceLow_8_eq_writeSubX64]; rfl
         | rw [replaceLow_16_eq_writeSubX64]; rfl
         | (dsimp only [writeSubX64, ShiftKind.eval, _root_.Width.bits, Vll.Width.bits]
            try rw [BitVec.zeroExtend_eq_setWidth]
            try repeat rw [BitVec.setWidth_eq]
            try rfl)
       · simp only [Effects.All]; intro _; refine closeGoal _ _ ?_
         first
         | rw [replaceLow_8_eq_writeSubX64]; rfl
         | rw [replaceLow_16_eq_writeSubX64]; rfl
         | (dsimp only [writeSubX64, ShiftKind.eval, _root_.Width.bits, Vll.Width.bits]
            try rw [BitVec.zeroExtend_eq_setWidth]
            try repeat rw [BitVec.setWidth_eq]
            try rfl))

private theorem wp_asmX64AluShift [Host] {E : Int64 → MachineData → Prop} (op : CoreAlu)
    (sk : ShiftKind) (w : Vll.Width)
    (hsk : (op = .shl ∧ sk = .shl) ∨ (op = .lshr ∧ sk = .lshr) ∨ (op = .ashr ∧ sk = .ashr))
    (s : MachineData) (rd lhs : Reg64) (rhs : Src x64Arch) (sf : Bool)
    (hrd : rd ∉ x64Scratch) (_hlhs : lhs ∉ x64Scratch)
    (hrhs : ∀ rs, rhs = .reg rs → rs ∉ x64Scratch) :
    let a := (s.regs.get64 lhs).setWidth w.bits
    let b := rhs.evalW w s.regs.get64
    _root_.Program.wp (emitClean (asmX64AluShiftIns w.toX64 sk rd lhs rhs sf))
      (fun s' => s'.regs.get64 rd = writeSubX64 w (s.regs.get64 rd) (op.eval w a b) ∧
        (∀ r, r ≠ rd → r ∉ x64Scratch → s'.regs.get64 r = s.regs.get64 r) ∧
        s'.zmms = s.zmms ∧ s'.dmem = s.dmem ∧
        (sf = true → ∀ cc : CondCode,
          cc.interp s'.status = cc.interp (x64AluFlags op w true a b s.status))) E s := by
  intro a b
  have eval_eq : ∀ (x : BitVec w.bits) (cnt : Nat),
      cnt = b.toNat % w.bits → sk.eval x cnt = op.eval w x b := by
    intro x cnt hc; subst hc
    rcases hsk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  have hrd11 := (ne_of_not_mem_x64Scratch hrd).2
  have finish_sf : ∀ (core : List _root_.Instr),
      _root_.Program.wp (emitClean core) (fun s1 =>
        s1.regs.get64 rd = writeSubX64 w (s.regs.get64 rd) (op.eval w a b) ∧
        (∀ r, r ≠ rd → r ∉ x64Scratch → s1.regs.get64 r = s.regs.get64 r) ∧
        s1.zmms = s.zmms ∧ s1.dmem = s.dmem) E s →
      _root_.Program.wp (emitClean (if sf then core ++ [x64InsI w.toX64
          (.test (.reg (regW w.toX64 rd)) (.reg (regW w.toX64 rd)))] else core))
        (fun s' => s'.regs.get64 rd = writeSubX64 w (s.regs.get64 rd) (op.eval w a b) ∧
          (∀ r, r ≠ rd → r ∉ x64Scratch → s'.regs.get64 r = s.regs.get64 r) ∧
          s'.zmms = s.zmms ∧ s'.dmem = s.dmem ∧
          (sf = true → ∀ cc : CondCode,
            cc.interp s'.status = cc.interp (x64AluFlags op w true a b s.status))) E s := by
    intro core hcore
    cases sf
    · exact Program.wp.mono hcore fun s1 ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4, fun h => by cases h⟩
    · simp only [↓reduceIte, emitClean_append, emitClean_cons, emitClean_nil]
      refine Program.wp.append hcore ?_
      rintro s1 ⟨h1, h2, h3, h4⟩
      refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_test_reg w.toX64 s1 rd rd)) ?_
      rintro s2 ⟨af, rfl⟩
      have hop : op = .mul ∨ op = .shl ∨ op = .lshr ∨ op = .ashr := by
        rcases hsk with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
      refine ⟨h1, h2, h3, h4, fun _ cc => ?_⟩
      have hrdw : (s1.regs.get64 rd).setWidth w.bits = op.eval w a b := by
        have := congrArg (·.setWidth w.bits) h1
        simpa [writeSubX64_setWidth] using this
      dsimp only
      cases w <;> simp only [Vll.Width.toX64, Vll.Width.bits] at hrdw ⊢ <;> rw [hrdw] <;>
        exact cond_testSelf_aluFlags_eq op _ hop a b s.status af cc
  refine finish_sf _ ?_
  cases rhs with
  | imm imm =>
    dsimp only [asmX64AluShiftIns]
    have hwb : w.toX64.bits = w.bits := by cases w <;> rfl
    have hcnt_lt : imm.toNat % w.bits < w.bits := Nat.mod_lt _ (by cases w <;> decide)
    have hpre_step :
        _root_.Program.wp (emitClean
          (if lhs == rd && (imm.toNat % w.toX64.bits != 0 || w.toX64 != .W32)
            then [] else [movSubWI w.toX64 rd lhs]))
          (fun s1 => (imm.toNat % w.bits = 0 →
              s1.regs.get64 rd = writeSubX64 w (s.regs.get64 rd) a) ∧
            (s1.regs.get64 rd).setWidth w.bits = a ∧
            (∀ r, r ≠ rd → r ∉ x64Scratch → s1.regs.get64 r = s.regs.get64 r) ∧
            (s1.regs.get64 rd = s.regs.get64 rd ∨
              ∃ rv, s1.regs.get64 rd = writeSubX64 w (s.regs.get64 rd) rv) ∧
            s1.zmms = s.zmms ∧ s1.dmem = s.dmem) E s := by
      by_cases hcond : (lhs == rd && (imm.toNat % w.toX64.bits != 0 || w.toX64 != .W32)) = true
      · simp only [hcond, ↓reduceIte, emitClean_nil]
        simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_reg64_iff] at hcond
        rcases hcond with ⟨rfl, hnz_or⟩
        refine _root_.Program.wp_nil ⟨fun hz => ?_, rfl, fun _ _ _ => rfl, Or.inl rfl, rfl, rfl⟩
        have hwne : w ≠ .w32 := by
          rcases hnz_or with hnz | hw32
          · exact absurd (hwb ▸ hz) hnz
          · intro h; subst h; exact absurd hw32 (by decide)
        exact (writeSubX64_self w hwne (s.regs.get64 lhs)).symm
      · simp only [hcond, Bool.false_eq_true, ↓reduceIte, emitClean_cons, emitClean_nil]
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movSubW w s rd lhs)) ?_
        rintro s1 rfl
        exact ⟨fun _ => Reg64s.get64_set64_same ..,
          by rw [Reg64s.get64_set64_same, writeSubX64_setWidth],
          fun r hr _ => Reg64s.get64_set64_of_ne _ rd r _ hr.symm,
          Or.inr ⟨a, Reg64s.get64_set64_same ..⟩, rfl, rfl⟩
    by_cases hcz : (imm.toNat % w.toX64.bits == 0) = true
    · have hc0 : imm.toNat % w.bits = 0 := hwb ▸ beq_iff_eq.mp hcz
      simp only [hcz, ↓reduceIte]
      refine Program.wp.mono hpre_step ?_
      rintro s1 ⟨hz, _, hr1, _, hzm1, hdm1⟩
      have hev0 : op.eval w a b = a := by
        rw [← eval_eq a 0 (by
          dsimp only [b, Src.evalW, Src.eval]
          rw [setWidth_toNat_mod_wbits, hc0])]
        rcases hsk with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [ShiftKind.eval]
      exact ⟨(hz hc0).trans (by rw [hev0]), hr1, hzm1, hdm1⟩
    · have hce : ∀ (s1 : MachineData) [Labels] (p : Std.Rco Int64),
          (ShiftCountExpr.imm8 (.int64 (Int64.ofNat (imm.toNat % w.toX64.bits)))).interpMasked
            s1 p w.toX64 = imm.toNat % w.bits := by
        intro s1 _ p
        have h5 : (31 : Nat) = 2 ^ 5 - 1 := rfl
        have h6 : (63 : Nat) = 2 ^ 6 - 1 := rfl
        cases w <;>
          dsimp only [Vll.Width.toX64] <;>
          simp only [ShiftCountExpr.interpMasked, ShiftCountExpr.interp,
            ConstExpr.interp, BitVec.take, BitVec.extractLsb'_toNat, Int64.ofNat,
            Int64.toBitVec, BitVec.toNat_ofNat, _root_.Width.bits, Vll.Width.bits,
            Nat.shiftRight_zero, h5, h6, Nat.and_two_pow_sub_one_eq_mod]
        · have h := Nat.mod_lt imm.toNat (by decide : 0 < 8)
          rw [Nat.mod_eq_of_lt (Nat.lt_trans h (by decide : 8 < 2 ^ 64)),
            Nat.mod_eq_of_lt (Nat.lt_trans h (by decide : 8 < 2 ^ 8)),
            Nat.mod_eq_of_lt (Nat.lt_trans h (by decide : 8 < 32))]
        · have h := Nat.mod_lt imm.toNat (by decide : 0 < 16)
          rw [Nat.mod_eq_of_lt (Nat.lt_trans h (by decide : 16 < 2 ^ 64)),
            Nat.mod_eq_of_lt (Nat.lt_trans h (by decide : 16 < 2 ^ 8)),
            Nat.mod_eq_of_lt (Nat.lt_trans h (by decide : 16 < 32))]
        · have h := Nat.mod_lt imm.toNat (by decide : 0 < 32)
          rw [Nat.mod_eq_of_lt (Nat.lt_trans h (by decide : 32 < 2 ^ 64)),
            Nat.mod_eq_of_lt (Nat.lt_trans h (by decide : 32 < 2 ^ 8)),
            Nat.mod_eq_of_lt h]
        · have h := Nat.mod_lt imm.toNat (by decide : 0 < 64)
          rw [Nat.mod_eq_of_lt (Nat.lt_trans h (by decide : 64 < 2 ^ 64)),
            Nat.mod_eq_of_lt (Nat.lt_trans h (by decide : 64 < 2 ^ 8)),
            Nat.mod_eq_of_lt h]
      simp only [hcz, Bool.false_eq_true, ↓reduceIte, emitClean_append, emitClean_cons,
        emitClean_nil]
      refine Program.wp.append hpre_step ?_
      rintro s1 ⟨_, hrd1, hr1, hold1, hzm1, hdm1⟩
      refine Program.wp.mono (Directive.FallsTo.wp
        (fallsTo_shiftOp w op sk hsk _ (imm.toNat % w.bits) hcnt_lt
          (fun _ hz => hcz (beq_iff_eq.mpr (hwb.symm ▸ hz))) s1 rd (hce s1))) ?_
      rintro s2 ⟨st, rfl⟩
      refine ⟨?_, fun r hr hsc => ?_, hzm1, hdm1⟩
      · rw [Reg64s.get64_set64_same, hrd1, writeSubX64_of_pre w _ _ _ hold1,
          eval_eq a (imm.toNat % w.bits) (setWidth_toNat_mod_wbits w imm).symm]
      · rw [Reg64s.get64_set64_of_ne _ rd r _ hr.symm]; exact hr1 r hr hsc
  | reg rb =>
    have hrb := hrhs rb rfl
    have hrb10 := (ne_of_not_mem_x64Scratch hrb).1
    have hrb11 := (ne_of_not_mem_x64Scratch hrb).2
    dsimp only [asmX64AluShiftIns]
    by_cases hw3264 : (w.toX64 == .W32 || w.toX64 == .W64) = true
    · have hw : w = .w32 ∨ w = .w64 := by cases w <;> simp_all [Vll.Width.toX64]
      simp only [hw3264, ↓reduceIte, emitClean_cons, emitClean_nil]
      refine _root_.Program.wp_singleton fun _ _ => ?_
      rcases hw with rfl | rfl <;> rcases hsk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      all_goals
        simp only [Vll.Width.toX64, asmX64Bmi2Op, regW, _root_.Width.bits, t_step_simp, Effects.All,
          MachineData.setReg, Reg64s.set, BitVec.zeroExtend_eq_setWidth]
        refine Or.inl ⟨trivial, ?_, fun r hr _ => Reg64s.get64_set64_of_ne _ rd r _ hr.symm,
          trivial, trivial⟩
        first
        | (rw [Reg64s.get64_set64_same,
            show (32 - 1 : Nat) = 31 from rfl, show (31 : Nat) = 2 ^ 5 - 1 from rfl,
            Nat.and_two_pow_sub_one_eq_mod, show (2 ^ 5 : Nat) = 32 from rfl]; rfl)
        | (rw [Reg64s.get64_set64_same,
            show (64 - 1 : Nat) = 63 from rfl, show (63 : Nat) = 2 ^ 6 - 1 from rfl,
            Nat.and_two_pow_sub_one_eq_mod, show (2 ^ 6 : Nat) = 64 from rfl]; rfl)
    · have hw816 : w = .w8 ∨ w = .w16 := by cases w <;> simp_all [Vll.Width.toX64]
      simp only [hw3264, Bool.false_eq_true, ↓reduceIte, emitClean_cons, emitClean_append,
        emitClean_nil]
      refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_movSubW w s .r11 lhs)) ?_
      rintro s1 rfl
      refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_movD _ .r10 .rcx)) ?_
      rintro s2 rfl
      have hmvRcx : ∀ (s2 : MachineData),
          (s2.regs.get64 rb).setWidth w.bits = b →
          s2.regs.get64 .r10 = s.regs.get64 .rcx →
          (s2.regs.get64 .r11).setWidth w.bits = a →
          (∀ r, r ≠ .rcx → r ∉ x64Scratch → s2.regs.get64 r = s.regs.get64 r) →
          s2.zmms = s.zmms → s2.dmem = s.dmem →
          _root_.Program.wp (emitClean (if rb == .rcx then [] else [movI .rcx rb]))
            (fun s3 => (s3.regs.get64 .rcx).setWidth w.bits = b ∧
              s3.regs.get64 .r10 = s.regs.get64 .rcx ∧
              (s3.regs.get64 .r11).setWidth w.bits = a ∧
              (∀ r, r ≠ .rcx → r ∉ x64Scratch → s3.regs.get64 r = s.regs.get64 r) ∧
              s3.zmms = s.zmms ∧ s3.dmem = s.dmem) E s2 := by
        intro s2 hs2_rb hs2_r10 hs2_r11 hs2_keep hs2_zm hs2_dm
        by_cases hrc : rb == .rcx
        · have heq := (beq_reg64_iff rb .rcx).1 hrc; subst heq
          simp only [hrc, ↓reduceIte, emitClean_nil]
          exact _root_.Program.wp_nil ⟨hs2_rb, hs2_r10, hs2_r11, hs2_keep, hs2_zm, hs2_dm⟩
        · simp only [hrc, Bool.false_eq_true, ↓reduceIte, emitClean_cons, emitClean_nil]
          refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movD _ .rcx rb)) ?_
          rintro s3 rfl
          refine ⟨?_, ?_, ?_, fun r hr hsc => ?_, hs2_zm, hs2_dm⟩
          · rw [Reg64s.get64_set64_same, hs2_rb]
          · rw [Reg64s.get64_set64_of_ne _ .rcx .r10 _ (by decide), hs2_r10]
          · rw [Reg64s.get64_set64_of_ne _ .rcx .r11 _ (by decide), hs2_r11]
          · rw [Reg64s.get64_set64_of_ne _ .rcx r _ hr.symm]; exact hs2_keep r hr hsc
      have hr10_val :
          (s.regs.set64 .r11 (writeSubX64 w (s.regs.get64 .r11) a)).get64 .rcx =
            s.regs.get64 .rcx :=
        Reg64s.get64_set64_of_ne _ .r11 .rcx _ (by decide)
      have happ : ∀ (a b c : _root_.Program),
          ((([] : _root_.Program).append a).append b).append c = a ++ (b ++ c) :=
        fun a b c => List.append_assoc a b c
      rw [happ]
      refine Program.wp.append (hmvRcx
        { regs := (s.regs.set64 .r11 (writeSubX64 w (s.regs.get64 .r11) a)).set64 .r10
            ((s.regs.set64 .r11 (writeSubX64 w (s.regs.get64 .r11) a)).get64 .rcx)
          zmms := s.zmms, status := s.status, df := s.df, dmem := s.dmem }
        (by
          rw [Reg64s.get64_set64_of_ne _ .r10 rb _ hrb10.symm,
            Reg64s.get64_set64_of_ne _ .r11 rb _ hrb11.symm]; rfl)
        (by rw [Reg64s.get64_set64_same, hr10_val])
        (by
          rw [Reg64s.get64_set64_of_ne _ .r10 .r11 _ (by decide),
            Reg64s.get64_set64_same, writeSubX64_setWidth])
        (fun r _ hsc => by
          have hne := ne_of_not_mem_x64Scratch hsc
          rw [Reg64s.get64_set64_of_ne _ .r10 r _ hne.1.symm,
            Reg64s.get64_set64_of_ne _ .r11 r _ hne.2.symm]) rfl rfl) ?_
      rintro s3 ⟨hrcx3, hr10_3, hr11_3, hr3, hzm3, hdm3⟩
      refine Program.wp.append
        (wp_shiftMaskRcx_low w hw816 s3 s a b hrcx3 hr10_3 hr11_3 hr3 hzm3 hdm3) ?_
      rintro s4 ⟨hcl, hr10_4, hr11_4, hr4, hzm4, hdm4⟩
      refine Program.wp.cons (Directive.FallsTo.wp
        (fallsTo_shiftOp w op sk hsk .cl (b.toNat % w.bits)
          (Nat.mod_lt _ (by cases w <;> decide))
          (fun h => by rcases hw816 with rfl | rfl <;> cases h) s4 .r11 hcl)) ?_
      rintro s5 ⟨st5, rfl⟩
      refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_movD _ .rcx .r10)) ?_
      rintro s6 rfl
      refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movSubW w _ rd .r11)) ?_
      rintro s7 rfl
      have h11_res : ((s4.regs.set64 .r11 (writeSubX64 w (s4.regs.get64 .r11)
          (sk.eval ((s4.regs.get64 .r11).setWidth w.bits) (b.toNat % w.bits)))).get64
          .r11).setWidth w.bits = op.eval w a b := by
        rw [Reg64s.get64_set64_same, writeSubX64_setWidth, hr11_4, eval_eq a _ rfl]
      have hrcx_rest : (s4.regs.set64 .r11 (writeSubX64 w (s4.regs.get64 .r11)
          (sk.eval ((s4.regs.get64 .r11).setWidth w.bits) (b.toNat % w.bits)))).get64 .r10 =
          s.regs.get64 .rcx := by
        rw [Reg64s.get64_set64_of_ne _ .r11 .r10 _ (by decide), hr10_4]
      refine ⟨?_, fun r hr hsc => ?_, hzm4, hdm4⟩
      · rw [Reg64s.get64_set64_same, Reg64s.get64_set64_of_ne _ .rcx .r11 _ (by decide), h11_res]
        by_cases hrc : rd = .rcx
        · subst hrc; rw [Reg64s.get64_set64_same, hrcx_rest]
        · rw [Reg64s.get64_set64_of_ne _ .rcx rd _ (Ne.symm hrc),
            Reg64s.get64_set64_of_ne _ .r11 rd _ hrd11.symm, hr4 rd hrc hrd]
      · have hne := ne_of_not_mem_x64Scratch hsc
        rw [Reg64s.get64_set64_of_ne _ rd r _ hr.symm]
        by_cases hrc : r = .rcx
        · subst hrc; rw [Reg64s.get64_set64_same, hrcx_rest]
        · rw [Reg64s.get64_set64_of_ne _ .rcx r _ (Ne.symm hrc),
            Reg64s.get64_set64_of_ne _ .r11 r _ hne.2.symm, hr4 r hrc hsc]

private theorem wp_asmX64AluMul [Host] {E : Int64 → MachineData → Prop} (w : Vll.Width)
    (s : MachineData) (rd lhs : Reg64) (rhs : Src x64Arch) (sf : Bool)
    (hrd : rd ∉ x64Scratch) (hlhs : lhs ∉ x64Scratch)
    (hrhs : ∀ rs, rhs = .reg rs → rs ∉ x64Scratch) :
    let a := (s.regs.get64 lhs).setWidth w.bits
    let b := rhs.evalW w s.regs.get64
    _root_.Program.wp (emitClean (asmX64AluMulIns w.toX64 rd lhs rhs sf))
      (fun s' => s'.regs.get64 rd = writeSubX64 w (s.regs.get64 rd) (CoreAlu.mul.eval w a b) ∧
        (∀ r, r ≠ rd → r ∉ x64Scratch → s'.regs.get64 r = s.regs.get64 r) ∧
        s'.zmms = s.zmms ∧ s'.dmem = s.dmem ∧
        (sf = true → ∀ cc : CondCode,
          cc.interp s'.status = cc.interp (x64AluFlags .mul w true a b s.status))) E s := by
  intro a b
  have hrd11 := (ne_of_not_mem_x64Scratch hrd).2
  have hcore : _root_.Program.wp (emitClean (match w.toX64 with
      | .W8 =>
        match (generalizing := false) rhs with
        | .reg rs =>
          [movWI .W32 .r11 lhs, aluBinI .W32 .mul .r11 (.reg (d rs)), movSubWI .W8 rd .r11]
        | .imm imm =>
          let c := (imm.setWidth 8).setWidth 32
          [movWI .W32 .r11 lhs, aluBinI .W32 .mul .r11 (immBitsOp .W32 c), movSubWI .W8 rd .r11]
      | _ => asmX64BinCoreIns w.toX64 .mul rd lhs rhs))
      (fun s1 => s1.regs.get64 rd = writeSubX64 w (s.regs.get64 rd) (a * b) ∧
        (∀ r, r ≠ rd → r ∉ x64Scratch → s1.regs.get64 r = s.regs.get64 r) ∧
        s1.zmms = s.zmms ∧ s1.dmem = s.dmem) E s := by
    cases w
    · cases rhs with
      | reg rs =>
        have hrs11 := (ne_of_not_mem_x64Scratch (hrhs rs rfl)).2
        simp only [emitClean_cons, emitClean_nil]
        refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_movW .W32 s .r11 lhs)) ?_
        rintro s1 rfl
        refine Program.wp.cons (Directive.FallsTo.wp
          (fallsTo_aluBinI_reg .mul .mul .w32 rfl (fun _ => by decide) _ .r11 rs)) ?_
        rintro s2 ⟨st2, _, rfl⟩
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movSubW .w8 _ rd .r11)) ?_
        rintro s3 rfl
        let r11v := ((s.regs.get64 lhs).setWidth 32).setWidth 64
        let s1r := s.regs.set64 .r11 r11v
        have h11_8 : ((s1r.set64 .r11 (writeSubX64 .w32 (s1r.get64 .r11)
            (AluBinKind.mul.eval ((s1r.get64 .r11).setWidth 32)
              ((s1r.get64 rs).setWidth 32)))).get64 .r11).setWidth 8 = a * b := by
          simp only [s1r, r11v, writeSubX64, AluBinKind.eval]
          rw [Reg64s.get64_set64_same, Reg64s.get64_set64_same,
            BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
            BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq,
            Reg64s.get64_set64_of_ne _ .r11 rs _ hrs11.symm,
            setWidth_mul_le (by decide : 8 ≤ 32), BitVec.setWidth_setWidth_of_le _ (by decide),
            BitVec.setWidth_setWidth_of_le _ (by decide)]
          rfl
        refine ⟨?_, fun r hr hsc => ?_, rfl, rfl⟩
        · dsimp only
          rw [Reg64s.get64_set64_same, h11_8,
            Reg64s.get64_set64_of_ne _ .r11 rd _ hrd11.symm,
            Reg64s.get64_set64_of_ne _ .r11 rd _ hrd11.symm]
        · have hr11 := (ne_of_not_mem_x64Scratch hsc).2
          dsimp only
          rw [Reg64s.get64_set64_of_ne _ rd r _ hr.symm,
            Reg64s.get64_set64_of_ne _ .r11 r _ hr11.symm,
            Reg64s.get64_set64_of_ne _ .r11 r _ hr11.symm]
      | imm imm =>
        simp only [emitClean_cons, emitClean_nil]
        refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_movW .W32 s .r11 lhs)) ?_
        rintro s1 rfl
        refine Program.wp.cons (Directive.FallsTo.wp
          (fallsTo_aluBinI_imm .mul .mul .w32 rfl (fun _ => by decide) _ .r11
            ((imm.setWidth 8).setWidth 32))) ?_
        rintro s2 ⟨st2, _, rfl⟩
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movSubW .w8 _ rd .r11)) ?_
        rintro s3 rfl
        let r11v := ((s.regs.get64 lhs).setWidth 32).setWidth 64
        let s1r := s.regs.set64 .r11 r11v
        have h11_8 : ((s1r.set64 .r11 (writeSubX64 .w32 (s1r.get64 .r11)
            (AluBinKind.mul.eval ((s1r.get64 .r11).setWidth 32)
              (((imm.setWidth 8).setWidth 32).setWidth 32)))).get64 .r11).setWidth 8 = a * b := by
          simp only [s1r, r11v, writeSubX64, AluBinKind.eval]
          rw [Reg64s.get64_set64_same, Reg64s.get64_set64_same,
            BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
            BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq,
            BitVec.setWidth_eq, setWidth_mul_le (by decide : 8 ≤ 32),
            BitVec.setWidth_setWidth_of_le _ (by decide),
            BitVec.setWidth_setWidth_of_le _ (by decide)]
          rfl
        refine ⟨?_, fun r hr hsc => ?_, rfl, rfl⟩
        · dsimp only
          rw [Reg64s.get64_set64_same, h11_8,
            Reg64s.get64_set64_of_ne _ .r11 rd _ hrd11.symm,
            Reg64s.get64_set64_of_ne _ .r11 rd _ hrd11.symm]
        · have hr11 := (ne_of_not_mem_x64Scratch hsc).2
          dsimp only
          rw [Reg64s.get64_set64_of_ne _ rd r _ hr.symm,
            Reg64s.get64_set64_of_ne _ .r11 r _ hr11.symm,
            Reg64s.get64_set64_of_ne _ .r11 r _ hr11.symm]
    all_goals
      exact Program.wp.mono (wp_asmX64BinCore .mul .mul _ rfl (fun _ h => by cases h)
        s rd lhs rhs hrd hlhs hrhs) fun s1 ⟨_, h2, h3, h4, h5⟩ => ⟨h2, h3, h4, h5⟩
  dsimp only [asmX64AluMulIns]
  cases sf
  · exact Program.wp.mono hcore fun s1 ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, h4, fun h => by cases h⟩
  · simp only [↓reduceIte, emitClean_append, emitClean_cons, emitClean_nil]
    refine Program.wp.append hcore ?_
    rintro s1 ⟨h1, h2, h3, h4⟩
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_test_reg w.toX64 s1 rd rd)) ?_
    rintro s2 ⟨af, rfl⟩
    refine ⟨h1, h2, h3, h4, fun _ cc => ?_⟩
    have hrdw : (s1.regs.get64 rd).setWidth w.bits = CoreAlu.mul.eval w a b := by
      have := congrArg (·.setWidth w.bits) h1
      simpa [writeSubX64_setWidth, CoreAlu.eval] using this
    dsimp only
    cases w <;> simp only [Vll.Width.toX64, Vll.Width.bits] at hrdw ⊢ <;> rw [hrdw] <;>
      exact cond_testSelf_aluFlags_eq .mul _ (.inl rfl) a b s.status af cc

private theorem wp_asmX64AluBin [Host] {E : Int64 → MachineData → Prop} (op : CoreAlu)
    (k : AluBinKind) (w : Vll.Width) (hk : coreAluToBin? op = some k) (hk_nm : op ≠ .mul)
    (s : MachineData) (rd lhs : Reg64) (rhs : Src x64Arch) (sf : Bool)
    (hrd : rd ∉ x64Scratch) (hlhs : lhs ∉ x64Scratch)
    (hrhs : ∀ rs, rhs = .reg rs → rs ∉ x64Scratch) :
    let a := (s.regs.get64 lhs).setWidth w.bits
    let b := rhs.evalW w s.regs.get64
    _root_.Program.wp (emitClean (asmX64AluBinIns w.toX64 k rd lhs rhs sf))
      (fun s' => s'.regs.get64 rd = writeSubX64 w (s.regs.get64 rd) (op.eval w a b) ∧
        (∀ r, r ≠ rd → r ∉ x64Scratch → s'.regs.get64 r = s.regs.get64 r) ∧
        s'.zmms = s.zmms ∧ s'.dmem = s.dmem ∧
        (sf = true → ∀ cc : CondCode,
          cc.interp s'.status = cc.interp (x64AluFlags op w true a b s.status))) E s := by
  intro a b
  have hk8 : k = .mul → w ≠ .w8 := fun h => by
    subst h; cases op <;> simp [coreAluToBin?] at hk; exact absurd rfl hk_nm
  have heval : k.eval a b = op.eval w a b := by
    cases op with
    | add | sub | and | or | xor =>
      simp only [coreAluToBin?, Option.some.injEq] at hk; subst hk; rfl
    | mul => exact absurd rfl hk_nm
    | shl | lshr | ashr => simp [coreAluToBin?] at hk
  have hcore_spec := @wp_asmX64BinCore _ E op k w hk hk8 s rd lhs rhs hrd hlhs hrhs
  dsimp only [asmX64AluBinIns]
  cases sf
  · cases rhs with
    | reg rs =>
      cases hlea : opBinLeaReg? w.toX64 k lhs rs rd with
      | none =>
        simp only [hlea, Option.map_none]
        exact Program.wp.mono hcore_spec fun s' ⟨_, h2, h3, h4, h5⟩ =>
          ⟨by rw [← heval]; exact h2, h3, h4, h5, fun h => by cases h⟩
      | some res =>
        simp only [hlea, Option.map_some]
        have fallsTo_sib : ∀ (hw3264 : w = .w32 ∨ w = .w64) (ra rb : Reg64),
            Directive.FallsTo (insW w.toX64 (.lea (regW w.toX64 rd) (atSIB ra rb .s1 0)))
              s (· = { s with regs := s.regs.set64 rd (writeSubX64 w (s.regs.get64 rd)
                ((s.regs.get64 ra).setWidth w.bits + (s.regs.get64 rb).setWidth w.bits)) }) := by
          intro hw3264 ra rb _ p _ _ _ hkcont
          have hz0 : (0 : Int64).toBitVec = 0#64 := rfl
          have hsib := atSIB_interp s.regs ra rb .s1 0 p
          simp only [AddrScale.shift, BitVec.shiftLeft_zero, hz0, BitVec.add_zero] at hsib
          rcases hw3264 with rfl | rfl
          · simp only [Vll.Width.toX64, regW, insW, t_step_simp, Reg64s.set]
            have h32 : (@AddrExpr.interp _ ⟨.W64⟩ (atSIB ra rb .s1 0) s.regs p).zeroExtend 32 =
                (s.regs.get64 ra).setWidth 32 + (s.regs.get64 rb).setWidth 32 := by
              have h0 :
                  ((@AddrExpr.interp _ ⟨.W64⟩ (atSIB ra rb .s1 0) s.regs p).zeroExtend
                    64).setWidth 32 =
                  (@AddrExpr.interp _ ⟨.W64⟩ (atSIB ra rb .s1 0) s.regs p).setWidth 32 := by
                rw [BitVec.zeroExtend_eq_setWidth, BitVec.setWidth_setWidth_of_le _ (by decide)]
              rw [BitVec.zeroExtend_eq_setWidth, ← h0, hsib]
              exact setWidth_add_le (by decide) _ _
            rw [h32]; refine hkcont _ ?_; simp [writeSubX64]
          · simp only [Vll.Width.toX64, regW, insW, t_step_simp, Reg64s.set, hsib]
            refine hkcont _ ?_; simp [Vll.Width.bits, BitVec.setWidth_eq, writeSubX64]
        unfold opBinLeaReg? at hlea
        split at hlea
        · rename_i hcond
          simp only [Bool.and_eq_true, Bool.or_eq_true, beq_width_iff, beq_iff_eq] at hcond
          have hkadd : k = .add := hcond.1.1.1; subst hkadd
          have hop : op = .add := by cases op <;> simp_all [coreAluToBin?]
          subst hop
          have hw3264 : w = .w32 ∨ w = .w64 := by cases w <;> simp_all [Vll.Width.toX64]
          have lea_wp : ∀ (ra rb : Reg64),
              res.1 = [x64InsI w.toX64 (.lea (regW w.toX64 rd) (atSIB ra rb .s1 0))] →
              (s.regs.get64 ra).setWidth w.bits + (s.regs.get64 rb).setWidth w.bits =
                CoreAlu.add.eval w a b →
              _root_.Program.wp (emitClean res.1) (fun s' =>
                s'.regs.get64 rd = writeSubX64 w (s.regs.get64 rd) (CoreAlu.add.eval w a b) ∧
                (∀ r, r ≠ rd → r ∉ x64Scratch → s'.regs.get64 r = s.regs.get64 r) ∧
                s'.zmms = s.zmms ∧ s'.dmem = s.dmem ∧
                (false = true → ∀ cc : CondCode,
                  cc.interp s'.status = cc.interp (x64AluFlags .add w true a b s.status))) E s := by
            intro ra rb hres hev
            rw [hres]; simp only [emitClean_cons, emitClean_nil]
            refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_sib hw3264 ra rb)) ?_
            rintro s' rfl
            exact ⟨by rw [Reg64s.get64_set64_same, hev],
              fun r hr _ => Reg64s.get64_set64_of_ne _ rd r _ hr.symm, rfl, rfl,
              fun h => by cases h⟩
          split at hlea
          · simp only [Option.some.injEq] at hlea; subst res
            exact lea_wp lhs rs rfl rfl
          · split at hlea
            · simp only [Option.some.injEq] at hlea; subst res
              exact lea_wp rs lhs rfl (BitVec.add_comm _ _)
            · simp at hlea
        · simp at hlea
    | imm imm =>
      cases hlea : opBinLeaImm? w.toX64 k lhs (imm.setWidth w.toX64.bits) rd with
      | none =>
        simp only [hlea, Option.map_none]
        exact Program.wp.mono hcore_spec fun s' ⟨_, h2, h3, h4, h5⟩ =>
          ⟨by rw [← heval]; exact h2, h3, h4, h5, fun h => by cases h⟩
      | some res =>
        simp only [hlea, Option.map_some]
        have fallsTo_disp : ∀ (hw3264 : w = .w32 ∨ w = .w64) (off : Int64),
            Directive.FallsTo (insW w.toX64 (.lea (regW w.toX64 rd) (atDisp lhs off))) s
              (· = { s with regs := s.regs.set64 rd (writeSubX64 w (s.regs.get64 rd)
                ((s.regs.get64 lhs).setWidth w.bits + off.toBitVec.setWidth w.bits)) }) := by
          intro hw3264 off _ p _ _ _ hkcont
          have hdisp := atDisp_interp s.regs lhs off p
          rcases hw3264 with rfl | rfl
          · simp only [Vll.Width.toX64, regW, insW, t_step_simp, Reg64s.set]
            have h32 : (@AddrExpr.interp _ ⟨.W64⟩ (atDisp lhs off) s.regs p).zeroExtend 32 =
                (s.regs.get64 lhs).setWidth 32 + off.toBitVec.setWidth 32 := by
              have h0 :
                  ((@AddrExpr.interp _ ⟨.W64⟩ (atDisp lhs off) s.regs p).zeroExtend
                    64).setWidth 32 =
                  (@AddrExpr.interp _ ⟨.W64⟩ (atDisp lhs off) s.regs p).setWidth 32 := by
                rw [BitVec.zeroExtend_eq_setWidth, BitVec.setWidth_setWidth_of_le _ (by decide)]
              rw [BitVec.zeroExtend_eq_setWidth, ← h0, hdisp]
              exact setWidth_add_le (by decide) _ _
            rw [h32]; refine hkcont _ ?_; simp [writeSubX64]
          · simp only [Vll.Width.toX64, regW, insW, t_step_simp, Reg64s.set, hdisp]
            refine hkcont _ ?_; simp [Vll.Width.bits, BitVec.setWidth_eq, writeSubX64]
        unfold opBinLeaImm? at hlea
        split at hlea
        · rename_i hcond
          simp only [Bool.and_eq_true, Bool.or_eq_true, beq_width_iff, beq_iff_eq] at hcond
          have hw3264 : w = .w32 ∨ w = .w64 := by cases w <;> simp_all [Vll.Width.toX64]
          have finish_disp : ∀ (off : Int64),
              res.1 = [x64InsI w.toX64 (.lea (regW w.toX64 rd) (atDisp lhs off))] →
              (s.regs.get64 lhs).setWidth w.bits + off.toBitVec.setWidth w.bits =
                op.eval w a b →
              _root_.Program.wp (emitClean res.1) (fun s' =>
                s'.regs.get64 rd = writeSubX64 w (s.regs.get64 rd) (op.eval w a b) ∧
                (∀ r, r ≠ rd → r ∉ x64Scratch → s'.regs.get64 r = s.regs.get64 r) ∧
                s'.zmms = s.zmms ∧ s'.dmem = s.dmem ∧
                (false = true → ∀ cc : CondCode,
                  cc.interp s'.status = cc.interp (x64AluFlags op w true a b s.status))) E s := by
            intro off hres hev
            rw [hres]; simp only [emitClean_cons, emitClean_nil]
            refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_disp hw3264 off)) ?_
            rintro s' rfl
            exact ⟨by rw [Reg64s.get64_set64_same, hev],
              fun r hr _ => Reg64s.get64_set64_of_ne _ rd r _ hr.symm, rfl, rfl,
              fun h => by cases h⟩
          rcases hcond.2 with rfl | rfl
          · have hop : op = .add := by cases op <;> simp_all [coreAluToBin?]
            subst hop
            dsimp only at hlea
            simp only [beq_self_eq_true, ↓reduceIte] at hlea
            split at hlea
            · simp only [Option.some.injEq] at hlea; subst res
              refine finish_disp _ rfl ?_
              rcases hw3264 with rfl | rfl
              · simp [Vll.Width.toX64, Vll.Width.bits, CoreAlu.eval, a, b, Src.evalW, Src.eval,
                  Int64.toBitVec_ofBitVec, truncate_signExtend_64 (by decide : 32 ≤ 64)]
              · simp [Vll.Width.toX64, Vll.Width.bits, CoreAlu.eval, a, b, Src.evalW, Src.eval,
                  Int64.toBitVec_ofBitVec]
            · simp at hlea
          · have hop : op = .sub := by cases op <;> simp_all [coreAluToBin?]
            subst hop
            dsimp only at hlea
            simp only [show (AluBinKind.sub == AluBinKind.add) = false from rfl,
              Bool.false_eq_true, ↓reduceIte] at hlea
            split at hlea
            · simp only [Option.some.injEq] at hlea; subst res
              refine finish_disp _ rfl ?_
              rcases hw3264 with rfl | rfl
              · simp [Vll.Width.toX64, Vll.Width.bits, CoreAlu.eval, a, b, Src.evalW, Src.eval,
                  Int64.toBitVec_ofBitVec, truncate_signExtend_64 (by decide : 32 ≤ 64),
                  BitVec.sub_eq_add_neg]
              · simp [Vll.Width.toX64, Vll.Width.bits, CoreAlu.eval, a, b, Src.evalW, Src.eval,
                  Int64.toBitVec_ofBitVec, BitVec.sub_eq_add_neg]
            · simp at hlea
        · simp at hlea
  · simp only [↓reduceIte]
    refine Program.wp.mono hcore_spec fun s' ⟨hex, h2, h3, h4, h5⟩ =>
      ⟨by rw [← heval]; exact h2, h3, h4, h5, fun _ cc => by
        cases op with
        | add | sub | and | or | xor => exact hex cc
        | mul => exact absurd rfl hk_nm
        | shl | lshr | ashr => simp [coreAluToBin?] at hk⟩

private theorem wp_asmX64Alu [Host] {E : Int64 → MachineData → Prop} (op : CoreAlu) (w : Vll.Width)
    (s : MachineData) (rd lhs : Reg64) (rhs : Src x64Arch) (sf : Bool)
    (hrd : rd ∉ x64Scratch) (hlhs : lhs ∉ x64Scratch)
    (hrhs : ∀ rs, rhs = .reg rs → rs ∉ x64Scratch) :
    let a := (s.regs.get64 lhs).setWidth w.bits
    let b := rhs.evalW w s.regs.get64
    _root_.Program.wp (emitClean (asmX64AluIns op w.toX64 rd lhs rhs sf))
      (fun s' => s'.regs.get64 rd = writeSubX64 w (s.regs.get64 rd) (op.eval w a b) ∧
        (∀ r, r ≠ rd → r ∉ x64Scratch → s'.regs.get64 r = s.regs.get64 r) ∧
        s'.zmms = s.zmms ∧ s'.dmem = s.dmem ∧
        (sf = true → ∀ cc : CondCode,
          cc.interp s'.status = cc.interp (x64AluFlags op w true a b s.status))) E s := by
  cases op with
  | add | sub | and | or | xor =>
    exact wp_asmX64AluBin _ _ w rfl (fun h => by cases h) s rd lhs rhs sf hrd hlhs hrhs
  | mul => exact wp_asmX64AluMul w s rd lhs rhs sf hrd hlhs hrhs
  | shl => exact wp_asmX64AluShift .shl .shl w (.inl ⟨rfl, rfl⟩) s rd lhs rhs sf hrd hlhs hrhs
  | lshr =>
    exact wp_asmX64AluShift .lshr .lshr w (.inr (.inl ⟨rfl, rfl⟩)) s rd lhs rhs sf hrd hlhs hrhs
  | ashr =>
    exact wp_asmX64AluShift .ashr .ashr w (.inr (.inr ⟨rfl, rfl⟩)) s rd lhs rhs sf hrd hlhs hrhs

/-! ## 3. Public ALU Simulation Theorem -/

theorem asmX64_alu_fallsTo {h : Host} {k : Nat} {fMask : FlagMask} {op : CoreAlu} {w : Vll.Width}
    {rd lhs : Reg64} {rhs : Src x64Arch} {sf : Bool}
    {sv : MachSt x64Arch} {sk : MachineData} {post : MachineState → Prop}
    (hsim : SimState fMask sv sk) (hrd : rd ∉ x64Scratch) (hlhs : lhs ∉ x64Scratch)
    (hrhs : ∀ rs, rhs = .reg rs → rs ∉ x64Scratch) :
    let a := (sv.gpr lhs).setWidth w.bits
    let b := rhs.evalW w sv.gpr
    let sv' := (sv.setGprW w rd (op.eval w a b)).setFlags (x64AluFlags op w sf a b sv.flags)
    x64Mach.FallsTo x64CondReads h k (asmX64 (.alu op w rd lhs rhs sf))
      (rd :: x64Scratch) [] maskAll sk
      (fun sk' => instrRel x64Arch (hostSymAddr h)
          (Host.addrOf (k + (asmX64 (.alu op w rd lhs rhs sf)).length)).toBitVec
          (.alu op w rd lhs rhs sf) sv (.fall sv') ∧
        SimState (if sf then maskNone else maskAll) sv' sk') post := by
  intro a b sv'
  refine x64_fallsTo_of_wp fun {_} _ =>
    Program.wp.mono (wp_asmX64Alu op w sk rd lhs rhs sf hrd hlhs hrhs) ?_
  rintro sk' ⟨h1, h2, h3, h4, h5⟩
  have ha : (sk.regs.get64 lhs).setWidth w.bits = a := by rw [hsim.1 lhs hlhs]
  have hb : rhs.evalW w sk.regs.get64 = b := by
    cases rhs with
    | reg rs => dsimp only [b]; simp [Src.evalW, Src.eval, hsim.1 rs (hrhs rs rfl)]
    | imm _ => rfl
  refine ⟨⟨rfl, ?_⟩, x64_frame_of_eq (fun r hr => by
      simp only [List.mem_cons, not_or] at hr; exact h2 r hr.1
        (by simp [x64Scratch, hr.2.1, hr.2.2.1])) h3 (updFlags_maskAll _ _)⟩
  have hsim_core : (∀ r, r ∉ x64Scratch → sk'.regs.get64 r = sv'.gpr r) ∧
      (∀ vr, sk'.zmms.get512 vr = sv'.vreg vr) ∧ sk'.dmem = sv'.mem := by
    refine ⟨fun r hr => ?_, fun vr => by rw [h3]; exact hsim.2.1 vr, h4.trans hsim.2.2.1⟩
    by_cases hrr : r = rd
    · subst hrr; simp [sv', h1, ha, hb, hsim.1 r hr, x64Arch]
    · simp [sv', hrr, h2 r hrr hr, hsim.1 r hr]
  cases sf
  · exact SimState_maskAll hsim_core.1 hsim_core.2.1 hsim_core.2.2
  · exact ⟨hsim_core.1, hsim_core.2.1, hsim_core.2.2, fun cc _ => by
      dsimp only [sv', MachSt.flags_setFlags]
      exact (h5 rfl cc).trans (by rw [ha, hb, x64AluFlags_sf_true op w a b sk.status sv.flags])⟩

end LeanQbe.T.Amd64

end
