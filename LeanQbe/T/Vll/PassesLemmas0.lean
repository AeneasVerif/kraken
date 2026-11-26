module

public import LeanQbe.T.Vll.Passes
public import LeanQbe.T.Vll.Sem
public import LeanQbe.T.Vll.RegaInst
import LeanQbe.T.TargetLemmas
import LeanQbe.T.RegaLemmas

/-!
# Soundness & Structural Proofs for Target-Neutral VLLIR Peephole Passes (`Vll.PassesLemmas`)

100% architecture-free (`0` imports of `Arm64`, `Amd64`, `Kraken.X64`, `Kraken.AArch64`,
`Vll.Arm64*`, `Vll.AsmArm64*`, or `Vll.FactorArm64*`) verification of `LeanQbe.T.Vll.Passes`
over arbitrary `(A : Arch)` using only standard Lean axioms (`std3`):

1. **`Arch.PassWf` & `instrRel` equivalences:** exact `MachSt A` identities for 64-bit self-moves
   (`A.Wf`-only), zero-frame `.prologue 0`/`.epilogue 0`, 64-bit `.canonAbi (.bits 64) r`, and
   all 2-instruction straight-line peephole rules (`peepholePairCore?`, `peepholePair?`).
2. **Structural & label preservation:** `definedLabels (pass is) = definedLabels is`, `NoVllLab`,
   `LabelsUnique`, `Defined`, and `length_le` for every pass and composed pipeline (`passPipeWf`,
   `passPipeCore`, `passPipe`), including `vllLowerFn_passPipe_labelsUnique`.
3. **XCAP / `ExecBody` / `FallsTo` preservation:** exact `ExecBody` and `bodyWp` equivalence for
   `optBody` / `optBodyWf`, local `vllMach.FallsTo` / `Run` lemmas, open-module `Xcap.ModOk`
   preservation for `optCodeMapBody`, and full `VllCodeMap.wp` / `cptr` / `adequacy` preservation
   for `optCodeMap` (`threadCodeMap ∘ optCodeMapBody`).
4. **Small-step `VllHost` simulation & `FnSpec` transfer:** generic chunk-based twin-host
   simulation (`Chunk`, `ChunksValid`, `bwd_sim`, `twinHost_sim`, `fnSpec_transfer`), `threadJmp`
   1:1 host simulation, and end-to-end `vllLowerFn_passPipeWf_correct`,
   `vllLowerFn_passPipeCore_correct`, and `vllLowerFn_passPipe_correct`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Vll

open LeanQbe.T

/-! ## 1. `Arch.PassWf`, `MachSt` Helpers, & `instrRel` Equivalences -/

/-- Extended architectural well-formedness for flag-sensitive peephole passes (`elimZeroFrame`,
`elimCanonAbi64`, and `clearFlags` before `cmp`/`test`). Every pure `A.Wf` pass (`elimSelfMov`,
`elimRedundantWindowCore`, `invertJccJmp`, `elimFallthrough`, `threadJmp`, `passPipeWf`) requires
only `A.Wf`. -/
structure Arch.PassWf (A : Arch) : Prop extends A.Wf where
  prologue0_flags : A.isZeroPrologueNoop = true → ∀ f, A.prologueFlags 0 f = f
  epilogue0_flags : A.isZeroEpilogueNoop = true → ∀ f, A.epilogueFlags 0 f = f
  canonAbi64_flags : A.isCanonAbi64Noop = true → ∀ f, A.canonAbiFlags (.bits 64) f = f
  cmp_overwrite : ∀ w a b f, A.cmpFlags w a b A.clearFlagsVal = A.cmpFlags w a b f
  test_overwrite : ∀ w a b f, A.testFlags w a b A.clearFlagsVal = A.testFlags w a b f

private theorem MachSt.setGpr_self {A : Arch} (s : MachSt A) (r : A.Reg) :
    s.setGpr r (s.gpr r) = s := by
  cases s with
  | mk gpr vreg flags mem =>
    dsimp only [MachSt.setGpr]
    congr 1; funext q; by_cases h : q = r <;> simp [h]

private theorem MachSt.setGpr_setGpr_same {A : Arch} (s : MachSt A) (r : A.Reg)
    (v₁ v₂ : BitVec 64) : (s.setGpr r v₁).setGpr r v₂ = s.setGpr r v₂ := by
  cases s with
  | mk gpr vreg flags mem =>
    dsimp only [MachSt.setGpr]
    congr 1; funext q; by_cases h : q = r <;> simp [h]

private theorem MachSt.setFlags_self {A : Arch} (s : MachSt A) :
    s.setFlags s.flags = s := by
  cases s; rfl

private theorem MachSt.setFlags_setFlags {A : Arch} (s : MachSt A) (f₁ f₂ : A.Flags) :
    (s.setFlags f₁).setFlags f₂ = s.setFlags f₂ := by
  cases s; rfl

theorem isSelfMov64_rel {A : Arch} (hwf : A.Wf) {i : Instr A} (h : i.isSelfMov64 = true)
    (symAddr : Sym → BitVec 64) (np : BitVec 64) (s : MachSt A) (o : InstrOut A) :
    instrRel A symAddr np i s o ↔ o = .fall s := by
  cases i with
  | mov w rd rs =>
    cases w with
    | w64 =>
      simp only [Instr.isSelfMov64, beq_iff_eq] at h
      subst h
      simp only [instrRel, MachSt.setGprW, BitVec.setWidth_eq, hwf.writeSub_w64,
        MachSt.setGpr_self]
    | w8 | w16 | w32 => cases h
  | _ => cases h

theorem isZeroFrameNoop_rel {A : Arch} (hwf : A.PassWf) {i : Instr A}
    (h : i.isZeroFrameNoop A = true) (symAddr : Sym → BitVec 64) (np : BitVec 64)
    (s : MachSt A) (o : InstrOut A) :
    instrRel A symAddr np i s o ↔ o = .fall s := by
  cases i with
  | prologue ns =>
    cases ns with
    | zero =>
      dsimp only [Instr.isZeroFrameNoop] at h
      have hf := hwf.prologue0_flags h s.flags
      dsimp only [Arch.isZeroPrologueNoop] at h
      cases hkind : A.abi.raKind with
      | linkReg _ => simp [hkind] at h
      | stack =>
        simp only [hkind, Bool.and_eq_true, beq_iff_eq] at h
        simp only [instrRel, hkind, h.1, hf, BitVec.sub_zero, MachSt.setGpr_self,
          MachSt.setFlags_self]
    | succ _ => cases h
  | epilogue ns =>
    cases ns with
    | zero =>
      dsimp only [Instr.isZeroFrameNoop] at h
      have hf := hwf.epilogue0_flags h s.flags
      dsimp only [Arch.isZeroEpilogueNoop] at h
      cases hkind : A.abi.raKind with
      | linkReg _ => simp [hkind] at h
      | stack =>
        simp only [hkind, Bool.and_eq_true, beq_iff_eq] at h
        simp only [instrRel, hkind, h.1, hf, BitVec.add_zero, MachSt.setGpr_self,
          MachSt.setFlags_self]
    | succ _ => cases h
  | _ => cases h

theorem isCanonAbi64Noop_rel {A : Arch} (hwf : A.PassWf) {i : Instr A}
    (h : i.isCanonAbi64Noop A = true) (symAddr : Sym → BitVec 64) (np : BitVec 64)
    (s : MachSt A) (o : InstrOut A) :
    instrRel A symAddr np i s o ↔ o = .fall s := by
  cases i with
  | canonAbi t r =>
    cases t with
    | bits n =>
      cases n with
      | zero => cases h
      | succ k =>
        dsimp only [Instr.isCanonAbi64Noop] at h
        split at h
        · rename_i heq
          have h64 : k + 1 = 64 := by cases heq; rfl
          have hf := hwf.canonAbi64_flags h s.flags
          rw [h64]
          simp only [instrRel, canonAbiVal, BitVec.setWidth_eq, hf, MachSt.setGpr_self,
            MachSt.setFlags_self]
        · cases h
    | _ => cases h
  | _ => cases h

theorem isNoop_rel {A : Arch} (hwf : A.PassWf) {i : Instr A} (h : i.isNoop A = true)
    (symAddr : Sym → BitVec 64) (np : BitVec 64) (s : MachSt A) (o : InstrOut A) :
    instrRel A symAddr np i s o ↔ o = .fall s := by
  simp only [Instr.isNoop, Bool.or_eq_true] at h
  rcases h with (h1 | h2) | h3
  · exact isSelfMov64_rel hwf.toWf h1 symAddr np s o
  · exact isZeroFrameNoop_rel hwf h2 symAddr np s o
  · exact isCanonAbi64Noop_rel hwf h3 symAddr np s o

theorem isNoop_not_label {A : Arch} {i : Instr A} (h : i.isNoop A = true) (l : Sym) :
    i ≠ .label l := by
  cases i <;> simp [Instr.isNoop, Instr.isSelfMov64, Instr.isZeroFrameNoop,
    Instr.isCanonAbi64Noop] at h ⊢

theorem isSelfMov64_not_label {A : Arch} {i : Instr A} (h : i.isSelfMov64 = true) (l : Sym) :
    i ≠ .label l := by
  cases i <;> simp [Instr.isSelfMov64] at h ⊢

theorem isNoop_not_call {A : Arch} {i : Instr A} (h : i.isNoop A = true) : i.isCall = false := by
  cases i <;> simp [Instr.isNoop, Instr.isSelfMov64, Instr.isZeroFrameNoop,
    Instr.isCanonAbi64Noop, Instr.isCall] at h ⊢

/-- Two-instruction deterministic fall-through equivalence: `[i₁, i₂]` produces the exact same
next state as `[i']` on every `s : MachSt A`, independently of `nextPc`. -/
def DetFallPair (A : Arch) (symAddr : Sym → BitVec 64) (i₁ i₂ i' : Instr A) : Prop :=
  ∀ s, ∃ s₁ s₂,
    (∀ np o, instrRel A symAddr np i₁ s o ↔ o = .fall s₁) ∧
    (∀ np o, instrRel A symAddr np i₂ s₁ o ↔ o = .fall s₂) ∧
    (∀ np o, instrRel A symAddr np i' s o ↔ o = .fall s₂)

theorem DetFallPair.spec {A : Arch} {symAddr : Sym → BitVec 64} {i₁ i₂ i' : Instr A}
    (h : DetFallPair A symAddr i₁ i₂ i') (s : MachSt A) :
    ∃ s₁ s₂,
      (∀ np o, instrRel A symAddr np i₁ s o ↔ o = .fall s₁) ∧
      (∀ np o, instrRel A symAddr np i₂ s₁ o ↔ o = .fall s₂) ∧
      (∀ np o, instrRel A symAddr np i' s o ↔ o = .fall s₂) :=
  h s

private theorem pureGprWrite_det {A : Arch} (symAddr : Sym → BitVec 64) {i : Instr A} {r : A.Reg}
    (h : i.pureGprWriteDst? = some r) (s : MachSt A) :
    ∃ v : BitVec 64, ∀ np o, instrRel A symAddr np i s o ↔ o = .fall (s.setGpr r v) := by
  cases i with
  | mov w rd rs =>
    simp only [Instr.pureGprWriteDst?, Option.some.injEq] at h; subst h
    exact ⟨A.writeSub w (s.gpr rd) ((s.gpr rs).setWidth w.bits), fun _ _ => Iff.rfl⟩
  | movi rd imm =>
    simp only [Instr.pureGprWriteDst?, Option.some.injEq] at h; subst h
    exact ⟨imm, fun _ _ => Iff.rfl⟩
  | setcc rd c =>
    simp only [Instr.pureGprWriteDst?, Option.some.injEq] at h; subst h
    exact ⟨A.writeSub .w8 (s.gpr rd) (BitVec.ofNat 8 (A.evalCond s.flags c).toNat),
      fun _ _ => Iff.rfl⟩
  | symAddr sym rd =>
    simp only [Instr.pureGprWriteDst?, Option.some.injEq] at h; subst h
    exact ⟨symAddr sym, fun _ _ => Iff.rfl⟩
  | _ => cases h

private theorem overwritesFullGpr_det {A : Arch} (hwf : A.Wf) (symAddr : Sym → BitVec 64)
    {r : A.Reg} {i : Instr A} (h : i.overwritesFullGpr r = true) (s : MachSt A) (v₁ : BitVec 64) :
    ∃ s₂, (∀ np o, instrRel A symAddr np i (s.setGpr r v₁) o ↔ o = .fall s₂) ∧
      (∀ np o, instrRel A symAddr np i s o ↔ o = .fall s₂) := by
  cases i with
  | movi rd imm =>
    simp only [Instr.overwritesFullGpr, beq_iff_eq] at h; subst h
    refine ⟨s.setGpr rd imm, fun _ _ => ?_, fun _ _ => Iff.rfl⟩
    simp only [instrRel, MachSt.setGpr_setGpr_same]
  | mov w rd rs =>
    cases w with
    | w64 =>
      simp only [Instr.overwritesFullGpr, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at h
      rcases h with ⟨rfl, hne⟩
      refine ⟨s.setGpr rd (s.gpr rs), fun _ _ => ?_, fun _ _ => ?_⟩
      · simp only [instrRel, MachSt.setGprW, BitVec.setWidth_eq, hwf.writeSub_w64,
          MachSt.gpr_setGpr_ne s v₁ hne, MachSt.setGpr_setGpr_same]
      · simp only [instrRel, MachSt.setGprW, BitVec.setWidth_eq, hwf.writeSub_w64]
    | w8 | w16 | w32 => cases h
  | symAddr sym rd =>
    simp only [Instr.overwritesFullGpr, beq_iff_eq] at h; subst h
    refine ⟨s.setGpr rd (symAddr sym), fun _ _ => ?_, fun _ _ => Iff.rfl⟩
    simp only [instrRel, MachSt.setGpr_setGpr_same]
  | _ => cases h

theorem peepholePairCore?_detFall {A : Arch} (hwf : A.Wf) (symAddr : Sym → BitVec 64)
    {i₁ i₂ i' : Instr A} (h : peepholePairCore? A i₁ i₂ = some i') :
    DetFallPair A symAddr i₁ i₂ i' := by
  have hgen : ∀ (p₁ p₂ p' : Instr A),
      (match p₁.pureGprWriteDst? with
       | some r => if p₂.overwritesFullGpr r then some p₂ else none
       | none => none) = some p' → DetFallPair A symAddr p₁ p₂ p' := by
    intro p₁ p₂ p' hg s
    cases hp : p₁.pureGprWriteDst? with
    | none => simp [hp] at hg
    | some r =>
      simp only [hp] at hg
      cases ho : p₂.overwritesFullGpr r with
      | false => simp [ho] at hg
      | true =>
        simp only [ho, ↓reduceIte, Option.some.injEq] at hg; subst hg
        obtain ⟨v₁, hv₁⟩ := pureGprWrite_det symAddr hp s
        obtain ⟨s₂, hs₂a, hs₂b⟩ := overwritesFullGpr_det hwf symAddr ho s v₁
        exact ⟨s.setGpr r v₁, s₂, hv₁, hs₂a, hs₂b⟩
  cases i₁ with
  | clearFlags =>
    cases i₂ with
    | clearFlags =>
      simp only [peepholePairCore?, Option.some.injEq] at h; subst h
      intro s
      refine ⟨s.setFlags A.clearFlagsVal, s.setFlags A.clearFlagsVal,
        fun _ _ => Iff.rfl, fun _ _ => ?_, fun _ _ => Iff.rfl⟩
      simp only [instrRel, MachSt.setFlags_setFlags]
    | _ => exact hgen _ _ _ h
  | mov w rd rs =>
    cases w with
    | w64 =>
      cases i₂ with
      | mov w' rd' rs' =>
        cases w' with
        | w64 =>
          dsimp only [peepholePairCore?] at h
          split at h
          · rename_i hcond
            simp only [Option.some.injEq] at h; subst h
            simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hcond
            intro s
            refine ⟨s.setGpr rd (s.gpr rs), s.setGpr rd (s.gpr rs), fun _ _ => ?_,
              fun _ _ => ?_, fun _ _ => ?_⟩
            · simp only [instrRel, MachSt.setGprW, BitVec.setWidth_eq, hwf.writeSub_w64]
            · rcases hcond with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · by_cases heq : rd = rs
                · subst heq
                  simp only [instrRel, MachSt.setGprW, BitVec.setWidth_eq, hwf.writeSub_w64,
                    MachSt.setGpr_self]
                · simp only [instrRel, MachSt.setGprW, BitVec.setWidth_eq, hwf.writeSub_w64,
                    MachSt.gpr_setGpr_same]
                  have hst : (s.setGpr rd (s.gpr rs)).setGpr rs (s.gpr rs) =
                      s.setGpr rd (s.gpr rs) := by
                    have := MachSt.setGpr_self (s.setGpr rd (s.gpr rs)) rs
                    rwa [MachSt.gpr_setGpr_ne s (s.gpr rs) (Ne.symm heq)] at this
                  rw [hst]
              · by_cases heq : rd = rs
                · subst heq
                  simp only [instrRel, MachSt.setGprW, BitVec.setWidth_eq, hwf.writeSub_w64,
                    MachSt.setGpr_self]
                · simp only [instrRel, MachSt.setGprW, BitVec.setWidth_eq, hwf.writeSub_w64,
                    MachSt.gpr_setGpr_ne s (s.gpr rs) (Ne.symm heq), MachSt.setGpr_setGpr_same]
            · simp only [instrRel, MachSt.setGprW, BitVec.setWidth_eq, hwf.writeSub_w64]
          · split at h
            · rename_i _ hcond
              simp only [Option.some.injEq] at h; subst h
              simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hcond
              rcases hcond with ⟨rfl, hne⟩
              intro s
              refine ⟨s.setGpr rd (s.gpr rs), s.setGpr rd (s.gpr rs'), fun _ _ => ?_,
                fun _ _ => ?_, fun _ _ => ?_⟩
              · simp only [instrRel, MachSt.setGprW, BitVec.setWidth_eq, hwf.writeSub_w64]
              · simp only [instrRel, MachSt.setGprW, BitVec.setWidth_eq, hwf.writeSub_w64,
                  MachSt.gpr_setGpr_ne s (s.gpr rs) hne, MachSt.setGpr_setGpr_same]
              · simp only [instrRel, MachSt.setGprW, BitVec.setWidth_eq, hwf.writeSub_w64]
            · cases h
        | w8 | w16 | w32 => exact hgen _ _ _ h
      | _ => exact hgen _ _ _ h
    | w8 | w16 | w32 => exact hgen _ _ _ h
  | _ => exact hgen _ _ _ h

theorem peepholePair?_detFall {A : Arch} (hwf : A.PassWf) (symAddr : Sym → BitVec 64)
    {i₁ i₂ i' : Instr A} (h : peepholePair? A i₁ i₂ = some i') :
    DetFallPair A symAddr i₁ i₂ i' := by
  cases i₁ with
  | clearFlags =>
    dsimp only [peepholePair?] at h
    cases ho : i₂.overwritesClearFlags with
    | false => simp [ho] at h
    | true =>
      simp only [ho, ↓reduceIte, Option.some.injEq] at h; subst h
      cases i₂ with
      | clearFlags =>
        intro s
        refine ⟨s.setFlags A.clearFlagsVal, s.setFlags A.clearFlagsVal,
          fun _ _ => Iff.rfl, fun _ _ => ?_, fun _ _ => Iff.rfl⟩
        simp only [instrRel, MachSt.setFlags_setFlags]
      | cmp w lhs rhs =>
        intro s
        let a := (s.gpr lhs).setWidth w.bits
        let b := rhs.evalW w s.gpr
        refine ⟨s.setFlags A.clearFlagsVal, s.setFlags (A.cmpFlags w a b s.flags),
          fun _ _ => Iff.rfl, fun _ _ => ?_, fun _ _ => Iff.rfl⟩
        simp only [instrRel, MachSt.gpr_setFlags, MachSt.flags_setFlags,
          hwf.cmp_overwrite w a b s.flags, MachSt.setFlags_setFlags, a, b]
      | test w lhs rhs =>
        intro s
        let a := (s.gpr lhs).setWidth w.bits
        let b := rhs.evalW w s.gpr
        refine ⟨s.setFlags A.clearFlagsVal, s.setFlags (A.testFlags w a b s.flags),
          fun _ _ => Iff.rfl, fun _ _ => ?_, fun _ _ => Iff.rfl⟩
        simp only [instrRel, MachSt.gpr_setFlags, MachSt.flags_setFlags,
          hwf.test_overwrite w a b s.flags, MachSt.setFlags_setFlags, a, b]
      | _ => cases ho
  | _ => exact peepholePairCore?_detFall hwf.toWf symAddr h

theorem peepholePairCore?_no_label_call {A : Arch} {i₁ i₂ i' : Instr A}
    (h : peepholePairCore? A i₁ i₂ = some i') :
    ((∀ l, i₁ ≠ .label l) ∧ (∀ l, i₂ ≠ .label l) ∧ (∀ l, i' ≠ .label l)) ∧
    (i₁.isCall = false ∧ i₂.isCall = false ∧ i'.isCall = false) := by
  have hgen : ∀ (p₁ p₂ p' : Instr A),
      (match p₁.pureGprWriteDst? with
       | some r => if p₂.overwritesFullGpr r then some p₂ else none
       | none => none) = some p' →
      ((∀ l, p₁ ≠ .label l) ∧ (∀ l, p₂ ≠ .label l) ∧ (∀ l, p' ≠ .label l)) ∧
      (p₁.isCall = false ∧ p₂.isCall = false ∧ p'.isCall = false) := by
    intro p₁ p₂ p' hg
    cases hp : p₁.pureGprWriteDst? with
    | none => simp [hp] at hg
    | some r =>
      simp only [hp] at hg
      cases ho : p₂.overwritesFullGpr r with
      | false => simp [ho] at hg
      | true =>
        simp only [ho, ↓reduceIte, Option.some.injEq] at hg; subst hg
        have hp1 : (∀ l, p₁ ≠ .label l) ∧ p₁.isCall = false := by
          cases p₁ <;> simp only [Instr.pureGprWriteDst?] at hp <;> try cases hp
          all_goals exact ⟨(fun _ e => by cases e), rfl⟩
        have hp2 : (∀ l, p₂ ≠ .label l) ∧ p₂.isCall = false := by
          cases p₂ <;> simp only [Instr.overwritesFullGpr] at ho <;> try cases ho
          all_goals exact ⟨(fun _ e => by cases e), rfl⟩
        exact ⟨⟨hp1.1, hp2.1, hp2.1⟩, hp1.2, hp2.2, hp2.2⟩
  cases i₁ with
  | clearFlags =>
    cases i₂ with
    | clearFlags =>
      cases h; exact ⟨⟨(fun _ e => by cases e), (fun _ e => by cases e), (fun _ e => by cases e)⟩,
        rfl, rfl, rfl⟩
    | _ => exact hgen _ _ _ h
  | mov w rd rs =>
    cases w with
    | w64 =>
      cases i₂ with
      | mov w' rd' rs' =>
        cases w' with
        | w64 =>
          dsimp only [peepholePairCore?] at h
          split at h
          · cases h
            exact ⟨⟨(fun _ e => by cases e), (fun _ e => by cases e), (fun _ e => by cases e)⟩,
              rfl, rfl, rfl⟩
          · split at h
            · cases h
              exact ⟨⟨(fun _ e => by cases e), (fun _ e => by cases e), (fun _ e => by cases e)⟩,
                rfl, rfl, rfl⟩
            · cases h
        | w8 | w16 | w32 => exact hgen _ _ _ h
      | _ => exact hgen _ _ _ h
    | w8 | w16 | w32 => exact hgen _ _ _ h
  | _ => exact hgen _ _ _ h

theorem peepholePair?_no_label_call {A : Arch} {i₁ i₂ i' : Instr A}
    (h : peepholePair? A i₁ i₂ = some i') :
    ((∀ l, i₁ ≠ .label l) ∧ (∀ l, i₂ ≠ .label l) ∧ (∀ l, i' ≠ .label l)) ∧
    (i₁.isCall = false ∧ i₂.isCall = false ∧ i'.isCall = false) := by
  cases i₁ with
  | clearFlags =>
    dsimp only [peepholePair?] at h
    cases ho : i₂.overwritesClearFlags with
    | false => simp [ho] at h
    | true =>
      simp only [ho, ↓reduceIte, Option.some.injEq] at h; subst h
      cases i₂ <;> simp only [Instr.overwritesClearFlags] at ho <;> try cases ho
      all_goals
        exact ⟨⟨(fun _ e => by cases e), (fun _ e => by cases e), (fun _ e => by cases e)⟩,
          rfl, rfl, rfl⟩
  | _ => exact peepholePairCore?_no_label_call h

/-! ## 2. Structural Label Preservation (`definedLabels`, `NoVllLab`, `LabelsUnique`) -/

theorem definedLabels_append {A : Arch} : ∀ (xs ys : List (Instr A)),
    definedLabels (xs ++ ys) = definedLabels xs ++ definedLabels ys
  | [], _ => rfl
  | .label l :: xs, ys => by simp [definedLabels, definedLabels_append xs ys]
  | .mov .. :: xs, ys | .movi .. :: xs, ys | .alu .. :: xs, ys | .cmp .. :: xs, ys
  | .test .. :: xs, ys | .clearFlags :: xs, ys | .setcc .. :: xs, ys | .load .. :: xs, ys
  | .store .. :: xs, ys | .slotSt .. :: xs, ys | .slotLd .. :: xs, ys | .prologue .. :: xs, ys
  | .epilogue .. :: xs, ys | .canonAbi .. :: xs, ys | .jmp .. :: xs, ys | .jcc .. :: xs, ys
  | .jnzGpr .. :: xs, ys | .call .. :: xs, ys | .icall .. :: xs, ys | .ret :: xs, ys
  | .exitJmp .. :: xs, ys | .tailJmpR .. :: xs, ys | .symAddr .. :: xs, ys | .ijmp .. :: xs, ys
  | .pad .. :: xs, ys | .native .. :: xs, ys => definedLabels_append xs ys

theorem mem_definedLabels_iff {A : Arch} {l : Sym} :
    ∀ {is : List (Instr A)}, l ∈ definedLabels is ↔ ∃ k : Nat, is[k]? = some (Instr.label l)
  | [] => by simp [definedLabels]
  | i :: rest => by
    cases i with
    | label l' =>
      simp only [definedLabels, List.mem_cons, mem_definedLabels_iff]
      constructor
      · rintro (rfl | ⟨k, hk⟩)
        · exact ⟨0, rfl⟩
        · exact ⟨k + 1, hk⟩
      · rintro ⟨k, hk⟩
        cases k with
        | zero => simp only [List.getElem?_cons_zero, Option.some.injEq, Instr.label.injEq] at hk
                  exact Or.inl hk.symm
        | succ k => exact Or.inr ⟨k, hk⟩
    | _ =>
      dsimp only [definedLabels]
      rw [mem_definedLabels_iff]
      constructor
      · rintro ⟨k, hk⟩; exact ⟨k + 1, hk⟩
      · rintro ⟨k, hk⟩
        cases k with
        | zero => simp at hk
        | succ k => exact ⟨k, hk⟩

theorem noVllLab_iff_definedLabels_nil {A : Arch} (is : List (Instr A)) :
    NoVllLab is ↔ definedLabels is = [] := by
  constructor
  · intro h
    cases hd : definedLabels is with
    | nil => rfl
    | cons l _ =>
      have hm : l ∈ definedLabels is := by rw [hd]; exact List.mem_cons_self
      obtain ⟨k, hk⟩ := mem_definedLabels_iff.mp hm
      exact absurd (List.mem_of_getElem? hk) (h l)
  · intro h l hm
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hm
    have : l ∈ definedLabels is := mem_definedLabels_iff.mpr ⟨k, hk⟩
    rw [h] at this; cases this

theorem definedLabels_nodup_iff {A : Arch} : ∀ (is : List (Instr A)),
    (definedLabels is).Nodup ↔
      ∀ (i j : Nat) (l : Sym), is[i]? = some (.label l) → is[j]? = some (.label l) → i = j
  | [] => by simp [definedLabels]
  | x :: rest => by
    cases x with
    | label l0 =>
      simp only [definedLabels, List.nodup_cons, mem_definedLabels_iff, definedLabels_nodup_iff]
      constructor
      · rintro ⟨hnot, hrest⟩ i j l hi hj
        cases i with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq, Instr.label.injEq] at hi; subst hi
          cases j with
          | zero => rfl
          | succ j => exact absurd ⟨j, hj⟩ hnot
        | succ i =>
          cases j with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq, Instr.label.injEq] at hj
            subst hj
            exact absurd ⟨i, hi⟩ hnot
          | succ j => exact congrArg Nat.succ (hrest i j l hi hj)
      · intro h
        refine ⟨fun ⟨j, hj⟩ => ?_, fun i j l hi hj => ?_⟩
        · have := h 0 (j + 1) l0 rfl hj; omega
        · have := h (i + 1) (j + 1) l hi hj; omega
    | _ =>
      dsimp only [definedLabels]
      rw [definedLabels_nodup_iff rest]
      constructor
      · intro h i j l hi hj
        cases i with
        | zero => simp at hi
        | succ i =>
          cases j with
          | zero => simp at hj
          | succ j => exact congrArg Nat.succ (h i j l hi hj)
      · intro h i j l hi hj
        have := h (i + 1) (j + 1) l hi hj; omega

private theorem definedLabels_cons_nonlab {A : Arch} {i : Instr A} (hi : ∀ l, i ≠ .label l)
    (rest : List (Instr A)) : definedLabels (i :: rest) = definedLabels rest := by
  cases i with
  | label l => exact absurd rfl (hi l)
  | _ => rfl

theorem elimFilterBody_definedLabels {A : Arch} {p : Instr A → Bool}
    (hp : ∀ i, p i = true → ∀ l, i ≠ .label l) :
    ∀ is, definedLabels (elimFilterBody p is) = definedLabels is
  | [] => rfl
  | i :: rest => by
    dsimp only [elimFilterBody]
    cases hpi : p i with
    | true =>
      simp only [↓reduceIte, elimFilterBody_definedLabels hp rest,
        definedLabels_cons_nonlab (hp i hpi)]
    | false =>
      cases i with
      | label l => simp [definedLabels, elimFilterBody_definedLabels hp rest]
      | _ => simp [definedLabels, elimFilterBody_definedLabels hp rest]

theorem elimFilterAux_definedLabels {A : Arch} {p : Instr A → Bool}
    (hp : ∀ i, p i = true → ∀ l, i ≠ .label l) :
    ∀ ac is, definedLabels (elimFilterAux p ac is) = definedLabels is
  | _, [] => rfl
  | ac, i :: rest => by
    dsimp only [elimFilterAux]
    cases hac : (!ac && p i) with
    | true =>
      have hpi : p i = true := (Bool.and_eq_true _ _).mp hac |>.2
      simp only [↓reduceIte, elimFilterAux_definedLabels hp false rest,
        definedLabels_cons_nonlab (hp i hpi)]
    | false =>
      cases i with
      | label l => simp [definedLabels, elimFilterAux_definedLabels hp _ rest]
      | _ => simp [definedLabels, elimFilterAux_definedLabels hp _ rest]

theorem elimWindow_definedLabels {A : Arch} {rule : Instr A → Instr A → Option (Instr A)}
    (hr : ∀ i₁ i₂ i', rule i₁ i₂ = some i' →
      (∀ l, i₁ ≠ .label l) ∧ (∀ l, i₂ ≠ .label l) ∧ (∀ l, i' ≠ .label l)) :
    ∀ is, definedLabels (elimWindow rule is) = definedLabels is
  | [] => rfl
  | [_] => rfl
  | i₁ :: i₂ :: rest => by
    dsimp only [elimWindow]
    cases h : rule i₁ i₂ with
    | some i' =>
      obtain ⟨h1, h2, h3⟩ := hr i₁ i₂ i' h
      rw [definedLabels_cons_nonlab h3, elimWindow_definedLabels hr rest,
        definedLabels_cons_nonlab h1, definedLabels_cons_nonlab h2]
    | none =>
      cases i₁ with
      | label l => simp [definedLabels, elimWindow_definedLabels hr (i₂ :: rest)]
      | _ => simp [definedLabels, elimWindow_definedLabels hr (i₂ :: rest)]

theorem threadJmp_definedLabels {A : Arch} (is : List (Instr A)) :
    definedLabels (threadJmp A is) = definedLabels is := by
  have go : ∀ tbl xs, definedLabels (xs.map (threadInstr A tbl)) = definedLabels xs := by
    intro tbl xs
    induction xs with
    | nil => rfl
    | cons i rest ih =>
      cases i with
      | label l => simp [threadInstr, definedLabels, ih]
      | jmp l =>
        dsimp only [List.map, threadInstr]
        cases lookupJmpTable tbl l with
        | none => simp [definedLabels, ih]
        | some a => cases a <;> simp [definedLabels, ih]
      | jcc c l =>
        dsimp only [List.map, threadInstr]
        cases lookupJmpTable tbl l with
        | none => simp [definedLabels, ih]
        | some a => cases a <;> simp [definedLabels, ih]
      | jnzGpr r l =>
        dsimp only [List.map, threadInstr]
        cases lookupJmpTable tbl l with
        | none => simp [definedLabels, ih]
        | some a => cases a <;> simp [definedLabels, ih]
      | _ => simp [threadInstr, definedLabels, ih]
  exact go (buildJmpTable A is) is

theorem invertJccJmp_definedLabels {A : Arch} (is : List (Instr A)) :
    definedLabels (invertJccJmp A is) = definedLabels is := by
  fun_induction invertJccJmp A is with
  | case1 => rfl
  | case2 c l₁ l₂ l₃ rest hcond ih =>
    simp only [definedLabels, ih]
  | case3 c l₁ l₂ l₃ rest hcond ih =>
    simp only [definedLabels, ih]
  | case4 i rest hnot ih =>
    cases i <;> simp only [definedLabels, ih]

theorem elimFallthroughAux_definedLabels {A : Arch} (inc : Bool) (ac : Bool)
    (is : List (Instr A)) :
    definedLabels (elimFallthroughAux A inc ac is) = definedLabels is := by
  fun_induction elimFallthroughAux A inc ac is with
  | case1 _ => rfl
  | case2 _ l₁ l₂ rest _ ih => simp only [definedLabels, ih]
  | case3 _ l₁ l₂ rest _ ih => simp only [definedLabels, ih]
  | case4 _ c l₁ l₂ rest _ ih => simp only [definedLabels, ih]
  | case5 _ c l₁ l₂ rest _ ih => simp only [definedLabels, ih]
  | case6 _ i rest _ _ ih => cases i <;> simp only [definedLabels, ih]

theorem passPipeWf_definedLabels (A : Arch) (is : List (Instr A)) :
    definedLabels (passPipeWf A is) = definedLabels is := by
  dsimp only [passPipeWf, elimFallthrough, elimRedundantWindowCore, elimSelfMov, elimFilter]
  rw [elimFallthroughAux_definedLabels, invertJccJmp_definedLabels,
    elimWindow_definedLabels (fun _ _ _ h => (peepholePairCore?_no_label_call h).1),
    elimFilterAux_definedLabels (fun _ h => isSelfMov64_not_label h)]

theorem passPipeCore_definedLabels (A : Arch) (is : List (Instr A)) :
    definedLabels (passPipeCore A is) = definedLabels is := by
  dsimp only [passPipeCore, elimFallthrough, elimRedundantWindow, elimNoop, elimFilter]
  rw [elimFallthroughAux_definedLabels, invertJccJmp_definedLabels,
    elimWindow_definedLabels (fun _ _ _ h => (peepholePair?_no_label_call h).1),
    elimFilterAux_definedLabels (fun _ h => isNoop_not_label h)]

theorem passPipe_definedLabels (A : Arch) (is : List (Instr A)) :
    definedLabels (passPipe A is) = definedLabels is := by
  dsimp only [passPipe, elimFallthrough, elimRedundantWindow, elimNoop, elimFilter]
  rw [elimFallthroughAux_definedLabels, invertJccJmp_definedLabels, threadJmp_definedLabels,
    elimWindow_definedLabels (fun _ _ _ h => (peepholePair?_no_label_call h).1),
    elimFilterAux_definedLabels (fun _ h => isNoop_not_label h)]

theorem passPipe_noVllLab (A : Arch) (is : List (Instr A)) :
    NoVllLab (passPipe A is) ↔ NoVllLab is := by
  rw [noVllLab_iff_definedLabels_nil, noVllLab_iff_definedLabels_nil, passPipe_definedLabels]

theorem passPipeWf_noVllLab (A : Arch) (is : List (Instr A)) :
    NoVllLab (passPipeWf A is) ↔ NoVllLab is := by
  rw [noVllLab_iff_definedLabels_nil, noVllLab_iff_definedLabels_nil, passPipeWf_definedLabels]

theorem elimFilterBody_length_le {A : Arch} (p : Instr A → Bool) :
    ∀ is, (elimFilterBody p is).length ≤ is.length
  | [] => Nat.le_refl 0
  | i :: rest => by
    dsimp only [elimFilterBody]
    have ih := elimFilterBody_length_le p rest
    split <;> simp only [List.length_cons] <;> omega

theorem elimFilterAux_length_le {A : Arch} (p : Instr A → Bool) :
    ∀ ac is, (elimFilterAux p ac is).length ≤ is.length
  | _, [] => Nat.le_refl 0
  | ac, i :: rest => by
    dsimp only [elimFilterAux]
    split
    · have := elimFilterAux_length_le p false rest; simp only [List.length_cons]; omega
    · have := elimFilterAux_length_le p i.isCall rest; simp only [List.length_cons]; omega

theorem elimWindow_length_le {A : Arch} (rule : Instr A → Instr A → Option (Instr A)) :
    ∀ is, (elimWindow rule is).length ≤ is.length
  | [] => Nat.le_refl 0
  | [_] => Nat.le_refl 1
  | i₁ :: i₂ :: rest => by
    dsimp only [elimWindow]
    cases rule i₁ i₂ with
    | some _ =>
      have := elimWindow_length_le rule rest; simp only [List.length_cons] at *; omega
    | none =>
      have := elimWindow_length_le rule (i₂ :: rest); simp only [List.length_cons] at *; omega

theorem threadJmp_length (A : Arch) (is : List (Instr A)) :
    (threadJmp A is).length = is.length := List.length_map _

theorem invertJccJmp_length_le (A : Arch) (is : List (Instr A)) :
    (invertJccJmp A is).length ≤ is.length := by
  fun_induction invertJccJmp A is
  · exact Nat.le_refl 0
  all_goals simp only [List.length_cons] at *; omega

theorem elimFallthroughAux_length_le (A : Arch) (inc : Bool) (ac : Bool) (is : List (Instr A)) :
    (elimFallthroughAux A inc ac is).length ≤ is.length := by
  fun_induction elimFallthroughAux A inc ac is
  · exact Nat.le_refl 0
  all_goals simp only [List.length_cons] at *; omega

theorem passPipeWf_length_le (A : Arch) (is : List (Instr A)) :
    (passPipeWf A is).length ≤ is.length :=
  Nat.le_trans (elimFallthroughAux_length_le A true false _)
    (Nat.le_trans (invertJccJmp_length_le A _)
      (Nat.le_trans (elimWindow_length_le _ _) (elimFilterAux_length_le _ false is)))

theorem passPipeCore_length_le (A : Arch) (is : List (Instr A)) :
    (passPipeCore A is).length ≤ is.length :=
  Nat.le_trans (elimFallthroughAux_length_le A true false _)
    (Nat.le_trans (invertJccJmp_length_le A _)
      (Nat.le_trans (elimWindow_length_le _ _) (elimFilterAux_length_le _ false is)))

theorem passPipe_length_le (A : Arch) (is : List (Instr A)) :
    (passPipe A is).length ≤ is.length :=
  Nat.le_trans (elimFallthroughAux_length_le A true false _)
    (Nat.le_trans (invertJccJmp_length_le A _)
      (Nat.le_trans (Nat.le_of_eq (threadJmp_length A _))
        (Nat.le_trans (elimWindow_length_le _ _) (elimFilterAux_length_le _ false is))))

/-- Structural `Target.LabelsUnique` for `mkVllHost A (passPipe A code) hlen'` inherited directly
from `vllLowerFn`. -/
theorem vllLowerFn_passPipe_labelsUnique (A : Arch) (hwf : A.Wf) (P : VllPolicy A)
    (hnl : VllHooksNoLab A P.hooks) {hints : (vllIsa A P).Hints} {E : Rega.Ext} {f : Fn}
    {code : List (Instr A)} (hl : vllLowerFn A P hints E f = .ok code)
    (hlen : 4 * (passPipe A code).length < 2 ^ 64) :
    (vllTarget A hwf P).LabelsUnique (mkVllHost A (passPipe A code) hlen) := by
  have hcode : (definedLabels code).Nodup :=
    (definedLabels_nodup_iff code).mpr fun i j l hi hj =>
      Rega.lowerFn_labelsUnique (vllLabelClean A P hnl) hl i j l hi hj
  rw [← passPipe_definedLabels A code] at hcode
  exact (definedLabels_nodup_iff (passPipe A code)).mp hcode

/-! ## 3. Straight-Line `ExecBody`, `bodyWp`, `FallsTo`, & XCAP `VllCodeMap` Preservation -/

theorem elimFilterBody_execBody {A : Arch} {symAddr : Sym → BitVec 64} {p : Instr A → Bool}
    (hp : ∀ i, p i = true → ∀ s o, instrRel A symAddr 0#64 i s o ↔ o = .fall s) :
    ∀ (is : List (Instr A)) (s : MachSt A) (o : InstrOut A),
      ExecBody A symAddr (elimFilterBody p is) s o ↔ ExecBody A symAddr is s o
  | [], _, _ => Iff.rfl
  | i :: rest, s, o => by
    dsimp only [elimFilterBody]
    cases hpi : p i with
    | true =>
      simp only [↓reduceIte]
      rw [elimFilterBody_execBody hp rest s o]
      constructor
      · intro hr; exact .cons_fall ((hp i hpi s (.fall s)).mpr rfl) hr
      · intro hex
        cases hex with
        | cons_fall hr hrest =>
          have heq := (hp i hpi s _).mp hr; cases heq; exact hrest
        | cons_jump hr => have heq := (hp i hpi s _).mp hr; cases heq
        | cons_halt hr => have heq := (hp i hpi s _).mp hr; cases heq
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      constructor
      · intro hex
        cases hex with
        | cons_fall hr hrest =>
          exact .cons_fall hr ((elimFilterBody_execBody hp rest _ o).mp hrest)
        | cons_jump hr => exact .cons_jump hr
        | cons_halt hr => exact .cons_halt hr
      · intro hex
        cases hex with
        | cons_fall hr hrest =>
          exact .cons_fall hr ((elimFilterBody_execBody hp rest _ o).mpr hrest)
        | cons_jump hr => exact .cons_jump hr
        | cons_halt hr => exact .cons_halt hr

theorem elimWindow_execBody {A : Arch} {symAddr : Sym → BitVec 64}
    {rule : Instr A → Instr A → Option (Instr A)}
    (hr : ∀ i₁ i₂ i', rule i₁ i₂ = some i' → DetFallPair A symAddr i₁ i₂ i') :
    ∀ (is : List (Instr A)) (s : MachSt A) (o : InstrOut A),
      ExecBody A symAddr (elimWindow rule is) s o ↔ ExecBody A symAddr is s o
  | [], _, _ => Iff.rfl
  | [_], _, _ => Iff.rfl
  | i₁ :: i₂ :: rest, s, o => by
    dsimp only [elimWindow]
    cases hrule : rule i₁ i₂ with
    | some i' =>
      obtain ⟨s₁, s₂, h1, h2, h3⟩ := hr i₁ i₂ i' hrule s
      constructor
      · intro hex
        cases hex with
        | cons_fall hst hrest =>
          have heq := (h3 0#64 _).mp hst; cases heq
          exact .cons_fall ((h1 0#64 _).mpr rfl)
            (.cons_fall ((h2 0#64 _).mpr rfl)
              ((elimWindow_execBody hr rest s₂ o).mp hrest))
        | cons_jump hst => have heq := (h3 0#64 _).mp hst; cases heq
        | cons_halt hst => have heq := (h3 0#64 _).mp hst; cases heq
      · intro hex
        cases hex with
        | cons_fall hst1 hex2 =>
          have heq1 := (h1 0#64 _).mp hst1; cases heq1
          cases hex2 with
          | cons_fall hst2 hrest =>
            have heq2 := (h2 0#64 _).mp hst2; cases heq2
            exact .cons_fall ((h3 0#64 _).mpr rfl)
              ((elimWindow_execBody hr rest s₂ o).mpr hrest)
          | cons_jump hst2 => have heq2 := (h2 0#64 _).mp hst2; cases heq2
          | cons_halt hst2 => have heq2 := (h2 0#64 _).mp hst2; cases heq2
        | cons_jump hst1 => have heq1 := (h1 0#64 _).mp hst1; cases heq1
        | cons_halt hst1 => have heq1 := (h1 0#64 _).mp hst1; cases heq1
    | none =>
      constructor
      · intro hex
        cases hex with
        | cons_fall hst hrest =>
          exact .cons_fall hst ((elimWindow_execBody hr (i₂ :: rest) _ o).mp hrest)
        | cons_jump hst => exact .cons_jump hst
        | cons_halt hst => exact .cons_halt hst
      · intro hex
        cases hex with
        | cons_fall hst hrest =>
          exact .cons_fall hst ((elimWindow_execBody hr (i₂ :: rest) _ o).mpr hrest)
        | cons_jump hst => exact .cons_jump hst
        | cons_halt hst => exact .cons_halt hst

theorem optBodyWf_execBody {A : Arch} (hwf : A.Wf) (symAddr : Sym → BitVec 64)
    (is : List (Instr A)) (s : MachSt A) (o : InstrOut A) :
    ExecBody A symAddr (optBodyWf A is) s o ↔ ExecBody A symAddr is s o := by
  dsimp only [optBodyWf, elimRedundantWindowCore]
  rw [elimWindow_execBody (fun _ _ _ h => peepholePairCore?_detFall hwf symAddr h),
    elimFilterBody_execBody (fun _ h s o => isSelfMov64_rel hwf h symAddr 0#64 s o)]

theorem optBody_execBody {A : Arch} (hwf : A.PassWf) (symAddr : Sym → BitVec 64)
    (is : List (Instr A)) (s : MachSt A) (o : InstrOut A) :
    ExecBody A symAddr (optBody A is) s o ↔ ExecBody A symAddr is s o := by
  dsimp only [optBody, elimRedundantWindow, elimNoopBody]
  rw [elimWindow_execBody (fun _ _ _ h => peepholePair?_detFall hwf symAddr h),
    elimFilterBody_execBody (fun _ h s o => isNoop_rel hwf h symAddr 0#64 s o)]

private theorem elimFilterBody_bodyWp {A : Arch} {symAddr : Sym → BitVec 64} {p : Instr A → Bool}
    (hp : ∀ i, p i = true → ∀ s o, instrRel A symAddr 0#64 i s o ↔ o = .fall s)
    (K : MachSt A → Prop) (Ψ : Xcap.CodeSpec (MachSt A)) (H : Xcap.Halt (MachSt A)) :
    ∀ (is : List (Instr A)) (s : MachSt A),
      bodyWp A symAddr (elimFilterBody p is) K Ψ H s ↔ bodyWp A symAddr is K Ψ H s
  | [], _ => Iff.rfl
  | i :: rest, s => by
    dsimp only [elimFilterBody]
    cases hpi : p i with
    | true =>
      simp only [↓reduceIte, bodyWp, elimFilterBody_bodyWp hp K Ψ H rest s]
      constructor
      · intro hr; exact instrWp_det (hp i hpi s) hr
      · intro ⟨_, hf, _, _⟩; exact hf s ((hp i hpi s _).mpr rfl)
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, bodyWp, instrWp]
      constructor
      · rintro ⟨hex, hf, hj, hh⟩
        exact ⟨hex, fun s' hr => (elimFilterBody_bodyWp hp K Ψ H rest s').mp (hf s' hr), hj, hh⟩
      · rintro ⟨hex, hf, hj, hh⟩
        exact ⟨hex, fun s' hr => (elimFilterBody_bodyWp hp K Ψ H rest s').mpr (hf s' hr), hj, hh⟩

private theorem elimWindow_bodyWp {A : Arch} {symAddr : Sym → BitVec 64}
    {rule : Instr A → Instr A → Option (Instr A)}
    (hr : ∀ i₁ i₂ i', rule i₁ i₂ = some i' → DetFallPair A symAddr i₁ i₂ i')
    (K : MachSt A → Prop) (Ψ : Xcap.CodeSpec (MachSt A)) (H : Xcap.Halt (MachSt A)) :
    ∀ (is : List (Instr A)) (s : MachSt A),
      bodyWp A symAddr (elimWindow rule is) K Ψ H s ↔ bodyWp A symAddr is K Ψ H s
  | [], _ => Iff.rfl
  | [_], _ => Iff.rfl
  | i₁ :: i₂ :: rest, s => by
    dsimp only [elimWindow]
    cases hrule : rule i₁ i₂ with
    | some i' =>
      obtain ⟨s₁, s₂, h1, h2, h3⟩ := hr i₁ i₂ i' hrule s
      simp only [bodyWp]
      constructor
      · intro ⟨_, hf, _, _⟩
        have hrest := (elimWindow_bodyWp hr K Ψ H rest s₂).mp (hf s₂ ((h3 0#64 _).mpr rfl))
        exact instrWp_det (h1 0#64) (instrWp_det (h2 0#64) hrest)
      · intro ⟨_, hf1, _, _⟩
        have hwp2 := hf1 s₁ ((h1 0#64 _).mpr rfl)
        have hrest := (elimWindow_bodyWp hr K Ψ H rest s₂).mpr (hwp2.2.1 s₂ ((h2 0#64 _).mpr rfl))
        exact instrWp_det (h3 0#64) hrest
    | none =>
      simp only [bodyWp, instrWp]
      constructor
      · rintro ⟨hex, hf, hj, hh⟩
        exact ⟨hex, fun s' h => (elimWindow_bodyWp hr K Ψ H (i₂ :: rest) s').mp (hf s' h), hj, hh⟩
      · rintro ⟨hex, hf, hj, hh⟩
        exact ⟨hex, fun s' h => (elimWindow_bodyWp hr K Ψ H (i₂ :: rest) s').mpr (hf s' h), hj, hh⟩

theorem optBodyWf_bodyWp {A : Arch} (hwf : A.Wf) (symAddr : Sym → BitVec 64)
    (is : List (Instr A)) (K : MachSt A → Prop) (Ψ : Xcap.CodeSpec (MachSt A))
    (H : Xcap.Halt (MachSt A)) (s : MachSt A) :
    bodyWp A symAddr (optBodyWf A is) K Ψ H s ↔ bodyWp A symAddr is K Ψ H s := by
  dsimp only [optBodyWf, elimRedundantWindowCore]
  rw [elimWindow_bodyWp (fun _ _ _ h => peepholePairCore?_detFall hwf symAddr h),
    elimFilterBody_bodyWp (fun _ h s o => isSelfMov64_rel hwf h symAddr 0#64 s o)]

theorem optBody_bodyWp {A : Arch} (hwf : A.PassWf) (symAddr : Sym → BitVec 64)
    (is : List (Instr A)) (K : MachSt A → Prop) (Ψ : Xcap.CodeSpec (MachSt A))
    (H : Xcap.Halt (MachSt A)) (s : MachSt A) :
    bodyWp A symAddr (optBody A is) K Ψ H s ↔ bodyWp A symAddr is K Ψ H s := by
  dsimp only [optBody, elimRedundantWindow, elimNoopBody]
  rw [elimWindow_bodyWp (fun _ _ _ h => peepholePair?_detFall hwf symAddr h),
    elimFilterBody_bodyWp (fun _ h s o => isNoop_rel hwf h symAddr 0#64 s o)]

/-! ### Local `vllMach.FallsTo` & `vllMach.Run` Preservation Lemmas -/

theorem vllMach_noop_fallsTo {A : Arch} (hwf : A.PassWf) {h : VllHost A} {k : Nat}
    {i : Instr A} (hi : i.isNoop A = true) {s : MachSt A} {post : Config A → Prop} :
    (vllMach A).FallsTo A.condReads h k [i] [] [] FlagMask.none s (fun s' => s' = s) post := by
  intro hc cont
  have hk : h.prog[k]? = some i := List.isInfixAt_singleton.mp hc
  have hrel := isNoop_rel hwf hi h.labelAddr (h.addrOf (k + 1)) s
  refine step_cps (vllStep h) post ⟨s, h.addrOf k⟩ ⟨k, i, hk, rfl, ⟨.fall s, (hrel _).mpr rfl⟩,
    (fun s' hr => ?_), (fun _ _ hr => by cases (hrel _).mp hr),
    (fun _ _ hr => by cases (hrel _).mp hr)⟩
  cases (hrel _).mp hr
  exact cont s rfl (Machine.Frame.refl _ _ _ _ _)

theorem vllMach_selfMov64_fallsTo {A : Arch} (hwf : A.Wf) {h : VllHost A} {k : Nat}
    {rd : A.Reg} {s : MachSt A} {post : Config A → Prop} :
    (vllMach A).FallsTo A.condReads h k [.mov .w64 rd rd] [] [] FlagMask.none s
      (fun s' => s' = s) post := by
  intro hc cont
  have hk : h.prog[k]? = some (.mov .w64 rd rd) := List.isInfixAt_singleton.mp hc
  have hrel := isSelfMov64_rel hwf (i := .mov .w64 rd rd) (by simp [Instr.isSelfMov64])
    h.labelAddr (h.addrOf (k + 1)) s
  refine step_cps (vllStep h) post ⟨s, h.addrOf k⟩ ⟨k, .mov .w64 rd rd, hk, rfl,
    ⟨.fall s, (hrel _).mpr rfl⟩, (fun s' hr => ?_), (fun _ _ hr => by cases (hrel _).mp hr),
    (fun _ _ hr => by cases (hrel _).mp hr)⟩
  cases (hrel _).mp hr
  exact cont s rfl (Machine.Frame.refl _ _ _ _ _)

theorem vllMach_optBody_run {A : Arch} (hwf : A.PassWf) {h : VllHost A} {K : MachSt A → Prop}
    {post : Config A → Prop} {is : List (Instr A)} {k : Nat} {s : MachSt A}
    (hc : (optBody A is).IsInfixAt h.prog k)
    (hnc : ∀ i ∈ optBody A is, ∀ sym, i ≠ .call sym)
    (hnic : ∀ i ∈ optBody A is, ∀ r, i ≠ .icall r)
    (hwp : bodyWp A h.labelAddr is K (fun _ _ => False) (fun _ _ => False) s)
    (hcont : ∀ s', K s' → (vllMach A).Run h (k + (optBody A is).length) s' post) :
    (vllMach A).Run h k s post :=
  vllMach_run_of_bodyWp hc hnc hnic ((optBody_bodyWp hwf h.labelAddr is K _ _ s).mpr hwp) hcont

theorem vllMach_fallthroughJmp_run {A : Arch} {h : VllHost A} {k : Nat} {l : Sym}
    {s : MachSt A} {post : Config A → Prop}
    (hc : [Instr.jmp l, Instr.label l].IsInfixAt h.prog k)
    (hl : h.labelAddr l = h.addrOf (k + 1))
    (hnext : (vllMach A).Run h (k + 2) s post) :
    (vllMach A).Run h k s post := by
  obtain ⟨hk0, hc1⟩ := List.IsInfixAt.cons hc
  have hk1 : h.prog[k + 1]? = some (.label l) := List.isInfixAt_singleton.mp hc1
  exact vllMach_jmp_spec (List.isInfixAt_singleton.mpr hk0) hl (vllMach_label_spec hk1 hnext)

theorem vllMach_fallthroughJcc_run {A : Arch} {h : VllHost A} {k : Nat} {c : A.Cond} {l : Sym}
    {s : MachSt A} {post : Config A → Prop}
    (hc : [Instr.jcc c l, Instr.label l].IsInfixAt h.prog k)
    (hl : h.labelAddr l = h.addrOf (k + 1))
    (hnext : (vllMach A).Run h (k + 2) s post) :
    (vllMach A).Run h k s post := by
  obtain ⟨hk0, hc1⟩ := List.IsInfixAt.cons hc
  have hk1 : h.prog[k + 1]? = some (.label l) := List.isInfixAt_singleton.mp hc1
  exact vllMach_jcc_spec (List.isInfixAt_singleton.mpr hk0) hl
    (fun _ => vllMach_label_spec hk1 hnext) (fun _ => vllMach_label_spec hk1 hnext)

theorem vllMach_invertJccJmp_run {A : Arch} (hwf : A.Wf) {h : VllHost A} {k j₂ : Nat}
    {c : A.Cond} {l₁ l₂ : Sym} {s : MachSt A} {post : Config A → Prop}
    (hc : [Instr.jcc (A.negCond c) l₂, Instr.label l₁].IsInfixAt h.prog k)
    (hl₂ : h.labelAddr l₂ = h.addrOf j₂)
    (ht : A.evalCond s.flags c = true → (vllMach A).Run h (k + 2) s post)
    (hf : A.evalCond s.flags c = false → (vllMach A).Run h j₂ s post) :
    (vllMach A).Run h k s post := by
  obtain ⟨hk0, hc1⟩ := List.IsInfixAt.cons hc
  have hk1 : h.prog[k + 1]? = some (.label l₁) := List.isInfixAt_singleton.mp hc1
  refine vllMach_jcc_spec (List.isInfixAt_singleton.mpr hk0) hl₂ (fun hneg => ?_) (fun hneg => ?_)
  · rw [hwf.negCond_eval] at hneg
    have hfalse : A.evalCond s.flags c = false := by cases h' : A.evalCond s.flags c <;> simp_all
    exact hf hfalse
  · rw [hwf.negCond_eval] at hneg
    have htrue : A.evalCond s.flags c = true := by cases h' : A.evalCond s.flags c <;> simp_all
    exact vllMach_label_spec hk1 (ht htrue)

/-! ### Structured `Block A` & `VllCodeMap A` XCAP Preservation -/

theorem optBlockBody_blockExec {A : Arch} (hwf : A.PassWf) (symAddr : Sym → BitVec 64)
    (b : Block A) (s : MachSt A) (o : Xcap.Out (MachSt A)) :
    BlockExec A symAddr (optBlockBody A b) s o ↔ BlockExec A symAddr b s o := by
  constructor
  · intro h
    cases h with
    | fall hex ht => exact .fall ((optBody_execBody hwf symAddr b.body s _).mp hex) ht
    | earlyJump hex => exact .earlyJump ((optBody_execBody hwf symAddr b.body s _).mp hex)
    | earlyHalt hex => exact .earlyHalt ((optBody_execBody hwf symAddr b.body s _).mp hex)
  · intro h
    cases h with
    | fall hex ht => exact .fall ((optBody_execBody hwf symAddr b.body s _).mpr hex) ht
    | earlyJump hex => exact .earlyJump ((optBody_execBody hwf symAddr b.body s _).mpr hex)
    | earlyHalt hex => exact .earlyHalt ((optBody_execBody hwf symAddr b.body s _).mpr hex)

theorem optBlockBody_bwp {A : Arch} (hwf : A.PassWf) (symAddr : Sym → BitVec 64)
    (b : Block A) (Ψ : Xcap.CodeSpec (MachSt A)) (H : Xcap.Halt (MachSt A)) (s : MachSt A) :
    Xcap.bwp (vllXcapMach A symAddr) (optBlockBody A b) Ψ H s ↔
      Xcap.bwp (vllXcapMach A symAddr) b Ψ H s := by
  have heq := fun o => optBlockBody_blockExec hwf symAddr b s o
  simp only [Xcap.bwp, vllXcapMach, heq]

private theorem find?_map_block {A : Arch} (f : Block A → Block A) (p : Block A → Bool)
    (hp : ∀ b, p (f b) = p b) :
    ∀ bs : List (Block A), (bs.map f).find? p = (bs.find? p).map f
  | [] => rfl
  | b :: bs => by
    simp only [List.map_cons, List.find?, hp b]
    cases p b <;> simp [find?_map_block f p hp bs]

theorem optCodeMapBody_lookupPc {A : Arch} (cm : VllCodeMap A) (pc : BitVec 64) :
    (optCodeMapBody A cm).lookupPc pc = (cm.lookupPc pc).map (optBlockBody A) :=
  find?_map_block (optBlockBody A) (fun b => cm.symAddr b.label == pc) (fun _ => rfl) cm.blocks

theorem optCodeMapBody_lookupLabel {A : Arch} (cm : VllCodeMap A) (l : Sym) :
    (optCodeMapBody A cm).lookupLabel l = (cm.lookupLabel l).map (optBlockBody A) :=
  find?_map_block (optBlockBody A) (fun b => b.label == l) (fun _ => rfl) cm.blocks

theorem optCodeMapBody_labels {A : Arch} (cm : VllCodeMap A) :
    (optCodeMapBody A cm).labels = cm.labels := by
  simp [VllCodeMap.labels, optCodeMapBody, optBlocks, optBlockBody, List.map_map]

theorem optCodeMapBody_padsOk {A : Arch} (cm : VllCodeMap A) :
    (optCodeMapBody A cm).padsOk = cm.padsOk := by
  simp only [VllCodeMap.padsOk, optCodeMapBody_lookupLabel]
  congr 1; funext l
  cases cm.lookupLabel l <;> rfl

theorem optCodeMapBody_wf {A : Arch} {cm : VllCodeMap A} (hwf : cm.Wf) :
    (optCodeMapBody A cm).Wf where
  labels_nodup := by rw [optCodeMapBody_labels]; exact hwf.labels_nodup
  addrs_inj := by
    intro b₁ hb₁ b₂ hb₂ heq
    simp only [optCodeMapBody, optBlocks, List.mem_map] at hb₁ hb₂
    obtain ⟨x₁, hx₁, rfl⟩ := hb₁
    obtain ⟨x₂, hx₂, rfl⟩ := hb₂
    have := hwf.addrs_inj x₁ hx₁ x₂ hx₂ heq
    subst this; rfl
  pads_ok := by
    intro l hl b hb
    rw [optCodeMapBody_lookupLabel] at hb
    cases hlu : cm.lookupLabel l with
    | none => simp [hlu] at hb
    | some b0 =>
      simp only [hlu, Option.map_some, Option.some.injEq] at hb; subst hb
      exact hwf.pads_ok l hl b0 hlu

theorem threadCodeMap_lookupPc {A : Arch} (cm : VllCodeMap A) (pc : BitVec 64) :
    (threadCodeMap A cm).lookupPc pc =
      (cm.lookupPc pc).map (fun b => { b with term := threadTerm A cm b.term }) :=
  find?_map_block (fun b => { b with term := threadTerm A cm b.term })
    (fun b => cm.symAddr b.label == pc) (fun _ => rfl) cm.blocks

theorem threadCodeMap_lookupLabel {A : Arch} (cm : VllCodeMap A) (l : Sym) :
    (threadCodeMap A cm).lookupLabel l =
      (cm.lookupLabel l).map (fun b => { b with term := threadTerm A cm b.term }) :=
  find?_map_block (fun b => { b with term := threadTerm A cm b.term })
    (fun b => b.label == l) (fun _ => rfl) cm.blocks

theorem threadCodeMap_labels {A : Arch} (cm : VllCodeMap A) :
    (threadCodeMap A cm).labels = cm.labels := by
  simp [VllCodeMap.labels, threadCodeMap, List.map_map]

theorem threadCodeMap_padsOk {A : Arch} (cm : VllCodeMap A) :
    (threadCodeMap A cm).padsOk = cm.padsOk := by
  simp only [VllCodeMap.padsOk, threadCodeMap_lookupLabel]
  congr 1; funext l
  cases cm.lookupLabel l <;> rfl

theorem threadCodeMap_wf {A : Arch} {cm : VllCodeMap A} (hwf : cm.Wf) :
    (threadCodeMap A cm).Wf where
  labels_nodup := by rw [threadCodeMap_labels]; exact hwf.labels_nodup
  addrs_inj := by
    intro b₁ hb₁ b₂ hb₂ heq
    simp only [threadCodeMap, List.mem_map] at hb₁ hb₂
    obtain ⟨x₁, hx₁, rfl⟩ := hb₁
    obtain ⟨x₂, hx₂, rfl⟩ := hb₂
    have := hwf.addrs_inj x₁ hx₁ x₂ hx₂ heq
    subst this; rfl
  pads_ok := by
    intro l hl b hb
    rw [threadCodeMap_lookupLabel] at hb
    cases hlu : cm.lookupLabel l with
    | none => simp [hlu] at hb
    | some b0 =>
      simp only [hlu, Option.map_some, Option.some.injEq] at hb; subst hb
      exact hwf.pads_ok l hl b0 hlu

theorem optCodeMap_wf {A : Arch} {cm : VllCodeMap A} (hwf : cm.Wf) :
    (optCodeMap A cm).Wf :=
  threadCodeMap_wf (optCodeMapBody_wf hwf)

theorem optCodeMap_padsOk {A : Arch} (cm : VllCodeMap A) :
    (optCodeMap A cm).padsOk = cm.padsOk := by
  dsimp only [optCodeMap]; rw [threadCodeMap_padsOk, optCodeMapBody_padsOk]

theorem optCodeMap_labels {A : Arch} (cm : VllCodeMap A) :
    (optCodeMap A cm).labels = cm.labels := by
  dsimp only [optCodeMap]; rw [threadCodeMap_labels, optCodeMapBody_labels]

/-- Open-module XCAP `ModOk` preservation for `optCodeMapBody`: any open-module proof against
`cm` holds identically after optimizing every block body, with zero closedness assumptions. -/
theorem optCodeMapBody_modOk {A : Arch} (hwf : A.PassWf) (cm : VllCodeMap A)
    {H : Xcap.Halt (MachSt A)} {imps exps : Xcap.Iface (MachSt A)}
    (hok : Xcap.ModOk (vllXcapMach A cm.symAddr) cm.toXcapCode H imps exps) :
    Xcap.ModOk (vllXcapMach A cm.symAddr) (optCodeMapBody A cm).toXcapCode H imps exps := by
  intro big Ψ hsub hcl himp e he
  let big' : Xcap.Code (Block A) := fun pc =>
    match cm.lookupPc pc with
    | some b => some b
    | none => big pc
  have hsub' : Xcap.Sub cm.toXcapCode big' := by
    intro pc b hb; simp only [big', VllCodeMap.toXcapCode] at hb ⊢; rw [hb]
  have hcl' : Xcap.Closed (vllXcapMach A cm.symAddr) big' Ψ H := by
    intro pc b hb s hbw
    dsimp only [big'] at hb
    cases hlu : cm.lookupPc pc with
    | some b0 =>
      simp only [hlu, Option.some.injEq] at hb; subst hb
      have hopt : (optCodeMapBody A cm).toXcapCode pc = some (optBlockBody A b0) := by
        simp [VllCodeMap.toXcapCode, optCodeMapBody_lookupPc, hlu]
      exact hcl pc (optBlockBody A b0) (hsub pc _ hopt) s
        ((optBlockBody_bwp hwf cm.symAddr b0 Ψ H s).mpr hbw)
    | none =>
      simp only [hlu] at hb
      exact hcl pc b hb s hbw
  exact hok big' Ψ hsub' hcl' himp e he

theorem optCodeMapBody_wp {A : Arch} (hwf : A.PassWf) (cm : VllCodeMap A)
    {H : Xcap.Halt (MachSt A)} {pc : BitVec 64} {s : MachSt A} :
    (optCodeMapBody A cm).wp H pc s ↔ cm.wp H pc s := by
  constructor
  · intro h Ψ hcl
    refine h Ψ fun p b hb s' hbw => ?_
    simp only [VllCodeMap.toXcapCode, optCodeMapBody_lookupPc] at hb
    cases hlu : cm.lookupPc p with
    | none => simp [hlu] at hb
    | some b0 =>
      simp only [hlu, Option.map_some, Option.some.injEq] at hb; subst hb
      exact hcl p b0 hlu s' ((optBlockBody_bwp hwf cm.symAddr b0 Ψ H s').mp hbw)
  · intro h Ψ hcl
    refine h Ψ fun p b hb s' hbw => ?_
    have hopt : (optCodeMapBody A cm).toXcapCode p = some (optBlockBody A b) := by
      simp only [VllCodeMap.toXcapCode, optCodeMapBody_lookupPc]
      rw [show cm.lookupPc p = some b from hb]; rfl
    exact hcl p (optBlockBody A b) hopt s' ((optBlockBody_bwp hwf cm.symAddr b Ψ H s').mpr hbw)

/-- Equivalence between `Xcap.wp` and inductive `Xcap.Safe`. -/
theorem xcap_wp_iff_safe {σ Blk : Type} (M : Xcap.Mach σ Blk) (cm : Xcap.Code Blk)
    (H : Xcap.Halt σ) (pc : BitVec 64) (s : σ) :
    Xcap.wp M cm H pc s ↔ Xcap.Safe M cm H pc s := by
  constructor
  · intro h; exact h (Xcap.Safe M cm H) (Xcap.Safe.closed M cm H)
  · intro h
    induction h with
    | step hb he _ hh ih => exact Xcap.wp_block hb he ih hh

private theorem blockJmpAction_spec {A : Arch} {cm : VllCodeMap A} (hwf : cm.Wf) {l : Sym}
    {act : JmpAction} (h : blockJmpAction A cm l = some act) :
    ∃ b, cm.lookupPc (cm.symAddr l) = some b ∧ b.body = [] ∧
      match act with
      | .toLabel l' => (b.term = .jmp l' ∨ b.term = .fall l')
      | .toRet => b.term = .ret := by
  dsimp only [blockJmpAction] at h
  cases hlu : cm.lookupLabel l with
  | none => simp [hlu] at h
  | some b =>
    obtain ⟨hbmem, hblab⟩ := cm.lookupLabel_mem hlu
    have hpc : cm.lookupPc (cm.symAddr l) = some b := hblab ▸ cm.lookupPc_of_wf hwf hbmem
    simp only [hlu] at h
    cases hbody : b.body with
    | cons _ _ => simp [hbody] at h
    | nil =>
      simp only [hbody, List.isEmpty_nil, ↓reduceIte] at h
      cases ht : b.term with
      | jmp l' =>
        simp only [ht] at h
        split at h
        · cases h; exact ⟨b, hpc, hbody, Or.inl ht⟩
        · cases h
      | fall l' =>
        simp only [ht] at h
        split at h
        · cases h; exact ⟨b, hpc, hbody, Or.inr ht⟩
        · cases h
      | ret =>
        simp only [ht, Option.some.injEq] at h; subst h
        exact ⟨b, hpc, hbody, ht⟩
      | _ => simp [ht] at h

/-- Full `VllCodeMap.wp` preservation under `threadCodeMap` via strengthened `Xcap.Safe`
structural induction (zero step-indexing, supports arbitrary cyclic loops and `.native`). -/
theorem threadCodeMap_wp {A : Arch} {cm : VllCodeMap A} (hwf : cm.Wf)
    {H : Xcap.Halt (MachSt A)} {pc : BitVec 64} {s : MachSt A}
    (h : cm.wp H pc s) : (threadCodeMap A cm).wp H pc s := by
  let M := vllXcapMach A cm.symAddr
  let cm' := (threadCodeMap A cm).toXcapCode
  have hsafe : Xcap.Safe M cm.toXcapCode H pc s := (xcap_wp_iff_safe M _ H pc s).mp h
  clear h
  suffices hinv : Xcap.Safe M cm' H pc s ∧
      ∀ b, cm.lookupPc pc = some b → b.body = [] →
        (∀ l', b.term = .jmp l' → Xcap.Safe M cm' H (cm.symAddr l') s) ∧
        (∀ l', b.term = .fall l' → Xcap.Safe M cm' H (cm.symAddr l') s) ∧
        (b.term = .ret → termWp A cm.symAddr .ret (Xcap.Safe M cm' H) H s) by
    exact (xcap_wp_iff_safe M cm' H pc s).mpr hinv.1
  induction hsafe with
  | @step pc b s hb he hj hh ih =>
    have hinv2 : ∀ b0, cm.lookupPc pc = some b0 → b0.body = [] →
        (∀ l', b0.term = .jmp l' → Xcap.Safe M cm' H (cm.symAddr l') s) ∧
        (∀ l', b0.term = .fall l' → Xcap.Safe M cm' H (cm.symAddr l') s) ∧
        (b0.term = .ret → termWp A cm.symAddr .ret (Xcap.Safe M cm' H) H s) := by
      intro b0 hb0 hbody
      have heqb : b0 = b := Option.some.inj (hb0.symm.trans hb)
      subst heqb
      refine ⟨fun l' ht => ?_, fun l' ht => ?_, fun ht => ?_⟩
      · have hbd : ExecBody A cm.symAddr b0.body s (.fall s) := by rw [hbody]; exact .nil
        have hex : BlockExec A cm.symAddr b0 s (.jump (cm.symAddr l') s) :=
          .fall hbd (by rw [ht]; rfl)
        exact (ih (cm.symAddr l') s hex).1
      · have hbd : ExecBody A cm.symAddr b0.body s (.fall s) := by rw [hbody]; exact .nil
        have hex : BlockExec A cm.symAddr b0 s (.jump (cm.symAddr l') s) :=
          .fall hbd (by rw [ht]; rfl)
        exact (ih (cm.symAddr l') s hex).1
      · obtain ⟨o, ho⟩ := he
        have hex_ret : ∃ o', termExec A cm.symAddr .ret s o' := by
          cases ho with
          | fall hbd htm =>
            rw [hbody] at hbd; cases hbd; rw [ht] at htm; exact ⟨o, htm⟩
          | earlyJump hbd => rw [hbody] at hbd; cases hbd
          | earlyHalt hbd => rw [hbody] at hbd; cases hbd
        have hbd : ExecBody A cm.symAddr b0.body s (.fall s) := by rw [hbody]; exact .nil
        refine ⟨hex_ret, fun pc' s' htm => ?_, fun c s' htm => ?_⟩
        · have hbe : BlockExec A cm.symAddr b0 s (.jump pc' s') := .fall hbd (ht ▸ htm)
          exact (ih pc' s' hbe).1
        · have hbe : BlockExec A cm.symAddr b0 s (.halt c s') := .fall hbd (ht ▸ htm)
          exact hh c s' hbe
    refine ⟨?_, hinv2⟩
    have hb' : cm' pc = some { b with term := threadTerm A cm b.term } := by
      simp only [cm', VllCodeMap.toXcapCode, threadCodeMap_lookupPc]
      rw [show cm.lookupPc pc = some b from hb]; rfl
    have hthr_lbl : ∀ l s₁,
        (Xcap.Safe M cm' H (cm.symAddr l) s₁ ∧
          ∀ b0, cm.lookupPc (cm.symAddr l) = some b0 → b0.body = [] →
            (∀ l', b0.term = .jmp l' → Xcap.Safe M cm' H (cm.symAddr l') s₁) ∧
            (∀ l', b0.term = .fall l' → Xcap.Safe M cm' H (cm.symAddr l') s₁) ∧
            (b0.term = .ret → termWp A cm.symAddr .ret (Xcap.Safe M cm' H) H s₁)) →
        Xcap.Safe M cm' H
          (cm.symAddr (match blockJmpAction A cm l with | some (.toLabel lt) => lt | _ => l))
          s₁ := by
      intro l s₁ h1
      cases hact : blockJmpAction A cm l with
      | none => exact h1.1
      | some act =>
        cases act with
        | toRet => exact h1.1
        | toLabel l' =>
          obtain ⟨b0, hb0pc, hb0body, hb0term⟩ := blockJmpAction_spec hwf hact
          rcases hb0term with hjm | hfl
          · exact (h1.2 b0 hb0pc hb0body).1 l' hjm
          · exact (h1.2 b0 hb0pc hb0body).2.1 l' hfl
    have hthr_uncond : ∀ l s₁,
        (Xcap.Safe M cm' H (cm.symAddr l) s₁ ∧
          ∀ b0, cm.lookupPc (cm.symAddr l) = some b0 → b0.body = [] →
            (∀ l', b0.term = .jmp l' → Xcap.Safe M cm' H (cm.symAddr l') s₁) ∧
            (∀ l', b0.term = .fall l' → Xcap.Safe M cm' H (cm.symAddr l') s₁) ∧
            (b0.term = .ret → termWp A cm.symAddr .ret (Xcap.Safe M cm' H) H s₁)) →
        (∃ o, termExec A cm.symAddr
          (match blockJmpAction A cm l with
           | some (.toLabel l') => Term.jmp l'
           | some .toRet => Term.ret
           | none => Term.jmp l) s₁ o) ∧
        (∀ pc' s', termExec A cm.symAddr
          (match blockJmpAction A cm l with
           | some (.toLabel l') => Term.jmp l'
           | some .toRet => Term.ret
           | none => Term.jmp l) s₁ (.jump pc' s') → Xcap.Safe M cm' H pc' s') ∧
        (∀ c s', termExec A cm.symAddr
          (match blockJmpAction A cm l with
           | some (.toLabel l') => Term.jmp l'
           | some .toRet => Term.ret
           | none => Term.jmp l) s₁ (.halt c s') → H c s') := by
      intro l s₁ h1
      cases hact : blockJmpAction A cm l with
      | none =>
        refine ⟨⟨_, rfl⟩, fun pc' s' hm => ?_, fun _ _ hm => by cases hm⟩
        cases hm; exact h1.1
      | some act =>
        obtain ⟨b0, hb0pc, hb0body, hb0term⟩ := blockJmpAction_spec hwf hact
        cases act with
        | toLabel l' =>
          refine ⟨⟨_, rfl⟩, fun pc' s' hm => ?_, fun _ _ hm => by cases hm⟩
          cases hm
          rcases hb0term with hjm | hfl
          · exact (h1.2 b0 hb0pc hb0body).1 l' hjm
          · exact (h1.2 b0 hb0pc hb0body).2.1 l' hfl
        | toRet =>
          exact (h1.2 b0 hb0pc hb0body).2.2 hb0term
    cases hbt : b.term with
    | call _ _ | icall _ _ | ret | exitJmp _ | tailJmpR _ | ijmp _ | halt _ | nativeTerm _ =>
      have hteq : threadTerm A cm b.term = b.term := by rw [hbt]; rfl
      have hbeq : { b with term := threadTerm A cm b.term } = b := by rw [hteq]
      rw [hbeq] at hb'
      exact Xcap.Safe.step hb' he (fun pc' s' h => (ih pc' s' h).1) hh
    | fall l =>
      have hterm_eq : ∀ s₁ o,
          termExec A cm.symAddr (threadTerm A cm (.fall l)) s₁ o ↔
            termExec A cm.symAddr
              (match blockJmpAction A cm l with
               | some (.toLabel l') => Term.jmp l'
               | some .toRet => Term.ret
               | none => Term.jmp l) s₁ o := by
        intro s₁ o; dsimp only [threadTerm]
        cases blockJmpAction A cm l with
        | none => rfl
        | some act => cases act <;> rfl
      refine Xcap.Safe.step hb' ?_ ?_ ?_
      · obtain ⟨o, ho⟩ := he
        cases ho with
        | earlyJump hbd => exact ⟨_, .earlyJump hbd⟩
        | earlyHalt hbd => exact ⟨_, .earlyHalt hbd⟩
        | fall hbd htm =>
          rw [hbt] at htm; cases htm
          obtain ⟨⟨o', ho'⟩, _, _⟩ := hthr_uncond l _ (ih _ _ (.fall hbd (by rw [hbt]; rfl)))
          exact ⟨o', .fall hbd (by rw [hbt]; exact (hterm_eq _ _).mpr ho')⟩
      · intro pc' s' hbe
        cases hbe with
        | earlyJump hbd => exact (ih pc' s' (.earlyJump hbd)).1
        | fall hbd htm =>
          rw [hbt] at htm
          have h1 := hthr_uncond l _ (ih _ _ (.fall hbd (by rw [hbt]; rfl)))
          exact h1.2.1 pc' s' ((hterm_eq _ _).mp htm)
      · intro c s' hbe
        cases hbe with
        | earlyHalt hbd => exact hh c s' (.earlyHalt hbd)
        | fall hbd htm =>
          rw [hbt] at htm
          have h1 := hthr_uncond l _ (ih _ _ (.fall hbd (by rw [hbt]; rfl)))
          exact h1.2.2 c s' ((hterm_eq _ _).mp htm)
    | jmp l =>
      refine Xcap.Safe.step hb' ?_ ?_ ?_
      · obtain ⟨o, ho⟩ := he
        cases ho with
        | earlyJump hbd => exact ⟨_, .earlyJump hbd⟩
        | earlyHalt hbd => exact ⟨_, .earlyHalt hbd⟩
        | fall hbd htm =>
          rw [hbt] at htm; cases htm
          obtain ⟨⟨o', ho'⟩, _, _⟩ := hthr_uncond l _ (ih _ _ (.fall hbd (by rw [hbt]; rfl)))
          exact ⟨o', .fall hbd (by rw [hbt]; exact ho')⟩
      · intro pc' s' hbe
        cases hbe with
        | earlyJump hbd => exact (ih pc' s' (.earlyJump hbd)).1
        | fall hbd htm =>
          rw [hbt] at htm
          have h1 := hthr_uncond l _ (ih _ _ (.fall hbd (by rw [hbt]; rfl)))
          exact h1.2.1 pc' s' htm
      · intro c s' hbe
        cases hbe with
        | earlyHalt hbd => exact hh c s' (.earlyHalt hbd)
        | fall hbd htm =>
          rw [hbt] at htm
          have h1 := hthr_uncond l _ (ih _ _ (.fall hbd (by rw [hbt]; rfl)))
          exact h1.2.2 c s' htm
    | jcc c t f =>
      refine Xcap.Safe.step hb' ?_ ?_ ?_
      · obtain ⟨o, ho⟩ := he
        cases ho with
        | earlyJump hbd => exact ⟨_, .earlyJump hbd⟩
        | earlyHalt hbd => exact ⟨_, .earlyHalt hbd⟩
        | fall hbd _ => exact ⟨_, .fall hbd (by rw [hbt]; exact rfl)⟩
      · intro pc' s' hbe
        cases hbe with
        | earlyJump hbd => exact (ih pc' s' (.earlyJump hbd)).1
        | fall hbd htm =>
          simp only [hbt, threadTerm, termExec, Xcap.Out.jump.injEq] at htm
          rcases htm with ⟨rfl, rfl⟩
          have hstep := ih _ _ (.fall hbd (by rw [hbt]; rfl))
          cases hev : A.evalCond s'.flags c <;>
            simp only [hev, ↓reduceIte, Bool.false_eq_true] at hstep ⊢
          · exact hthr_lbl f s' hstep
          · exact hthr_lbl t s' hstep
      · intro cv s' hbe
        cases hbe with
        | earlyHalt hbd => exact hh cv s' (.earlyHalt hbd)
        | fall _ htm => simp [hbt, threadTerm, termExec] at htm
    | jnzGpr r t f =>
      refine Xcap.Safe.step hb' ?_ ?_ ?_
      · obtain ⟨o, ho⟩ := he
        cases ho with
        | earlyJump hbd => exact ⟨_, .earlyJump hbd⟩
        | earlyHalt hbd => exact ⟨_, .earlyHalt hbd⟩
        | fall hbd _ => exact ⟨_, .fall hbd (by rw [hbt]; exact rfl)⟩
      · intro pc' s' hbe
        cases hbe with
        | earlyJump hbd => exact (ih pc' s' (.earlyJump hbd)).1
        | fall hbd htm =>
          simp only [hbt, threadTerm, termExec, Xcap.Out.jump.injEq] at htm
          rcases htm with ⟨rfl, rfl⟩
          have hstep := ih _ _ (.fall hbd (by rw [hbt]; rfl))
          cases hnz : ((_ : BitVec 8) != 0#8) <;>
            simp only [hnz, ↓reduceIte, Bool.false_eq_true] at hstep ⊢
          · exact hthr_lbl f _ hstep
          · exact hthr_lbl t _ hstep
      · intro cv s' hbe
        cases hbe with
        | earlyHalt hbd => exact hh cv s' (.earlyHalt hbd)
        | fall _ htm => simp [hbt, threadTerm, termExec] at htm

theorem optCodeMap_wp {A : Arch} (hwf : A.PassWf) {cm : VllCodeMap A} (hcm : cm.Wf)
    {H : Xcap.Halt (MachSt A)} {pc : BitVec 64} {s : MachSt A}
    (h : cm.wp H pc s) : (optCodeMap A cm).wp H pc s :=
  threadCodeMap_wp (optCodeMapBody_wf hcm) ((optCodeMapBody_wp hwf cm).mpr h)

theorem optCodeMap_cptr {A : Arch} (hwf : A.PassWf) {cm : VllCodeMap A} (hcm : cm.Wf)
    {H : Xcap.Halt (MachSt A)} {pc : BitVec 64} {P : MachSt A → Prop}
    (h : Xcap.cptr (cm.wp H) pc P) : Xcap.cptr ((optCodeMap A cm).wp H) pc P :=
  fun s hs => optCodeMap_wp hwf hcm (h s hs)

theorem optCodeMap_adequate {A : Arch} (hwf : A.PassWf) {cm : VllCodeMap A} (hcm : cm.Wf)
    {H : Xcap.Halt (MachSt A)} {pc : BitVec 64} {s : MachSt A}
    (h : cm.wp H pc s) : ∃ c s', (optCodeMap A cm).Halts pc s c s' ∧ H c s' :=
  (optCodeMap A cm).adequacy (optCodeMap_wp hwf hcm h)

/-! ## 4. `threadJmp` 1:1 Length-Preserving `VllHost` Simulation -/

theorem getElem?_some_lt {α : Type} {xs : List α} {i : Nat} {a : α}
    (h : xs[i]? = some a) : i < xs.length :=
  (List.getElem?_eq_some_iff.mp h).1

private theorem vllStep_label_cps {A : Arch} {h : VllHost A} {k : Nat} {l : Sym}
    {s : MachSt A} {post : Config A → Prop}
    (hk : h.prog[k]? = some (.label l))
    (hcont : Eventually (vllStep h) post ⟨s, h.addrOf (k + 1)⟩) :
    Eventually (vllStep h) post ⟨s, h.addrOf k⟩ :=
  step_cps (vllStep h) post ⟨s, h.addrOf k⟩
    ⟨k, .label l, hk, rfl, ⟨.fall s, rfl⟩,
      (fun _ hr => by cases hr; exact hcont),
      (fun _ _ hr => by cases hr),
      (fun _ _ hr => by cases hr)⟩

theorem buildJmpTable_spec {A : Arch} {code : List (Instr A)} {l : Sym} {act : JmpAction}
    (hlu : lookupJmpTable (buildJmpTable A code) l = some act) :
    ∃ k, code[k]? = some (.label l) ∧
      match act with
      | .toLabel l' =>
        l ≠ l' ∧ (code[k + 1]? = some (.label l') ∨ code[k + 1]? = some (.jmp l'))
      | .toRet => code[k + 1]? = some .ret := by
  suffices ∀ n (code : List (Instr A)), code.length ≤ n →
      lookupJmpTable (buildJmpTable A code) l = some act →
      ∃ k, code[k]? = some (.label l) ∧
        match act with
        | .toLabel l' =>
          l ≠ l' ∧ (code[k + 1]? = some (.label l') ∨ code[k + 1]? = some (.jmp l'))
        | .toRet => code[k + 1]? = some .ret from
    this code.length code (Nat.le_refl _) hlu
  intro n
  induction n with
  | zero =>
    intro code hlen h
    cases code with
    | nil => simp [buildJmpTable, lookupJmpTable] at h
    | cons _ _ => simp at hlen
  | succ n ih =>
    intro code hlen h
    cases code with
    | nil => simp [buildJmpTable, lookupJmpTable] at h
    | cons i rest =>
      cases i with
      | label l0 =>
        cases rest with
        | nil => simp [buildJmpTable, lookupJmpTable] at h
        | cons nxt rest' =>
          cases nxt with
          | label l' =>
            dsimp only [buildJmpTable] at h
            by_cases hne : (l0 != l') = true
            · simp only [hne, ↓reduceIte, lookupJmpTable, List.find?] at h
              cases heq : (l0 == l) with
              | true =>
                simp only [heq, Option.map_some, Option.some.injEq] at h; subst h
                have hl0 : l0 = l := beq_iff_eq.mp heq; subst hl0
                exact ⟨0, rfl, bne_iff_ne.mp hne, Or.inl rfl⟩
              | false =>
                simp only [heq] at h
                obtain ⟨k, hk, hact⟩ := ih (.label l' :: rest') (by simp at hlen; omega) h
                exact ⟨k + 1, hk, hact⟩
            · simp only [hne, Bool.false_eq_true, ↓reduceIte] at h
              obtain ⟨k, hk, hact⟩ := ih (.label l' :: rest') (by simp at hlen; omega) h
              exact ⟨k + 1, hk, hact⟩
          | jmp l' =>
            dsimp only [buildJmpTable] at h
            by_cases hne : (l0 != l') = true
            · simp only [hne, ↓reduceIte, lookupJmpTable, List.find?] at h
              cases heq : (l0 == l) with
              | true =>
                simp only [heq, Option.map_some, Option.some.injEq] at h; subst h
                have hl0 : l0 = l := beq_iff_eq.mp heq; subst hl0
                exact ⟨0, rfl, bne_iff_ne.mp hne, Or.inr rfl⟩
              | false =>
                simp only [heq] at h
                obtain ⟨k, hk, hact⟩ := ih (.jmp l' :: rest') (by simp at hlen; omega) h
                exact ⟨k + 1, hk, hact⟩
            · simp only [hne, Bool.false_eq_true, ↓reduceIte] at h
              obtain ⟨k, hk, hact⟩ := ih (.jmp l' :: rest') (by simp at hlen; omega) h
              exact ⟨k + 1, hk, hact⟩
          | ret =>
            simp only [buildJmpTable, lookupJmpTable, List.find?] at h
            cases heq : (l0 == l) with
            | true =>
              simp only [heq, Option.map_some, Option.some.injEq] at h; subst h
              have hl0 : l0 = l := beq_iff_eq.mp heq; subst hl0
              exact ⟨0, rfl, rfl⟩
            | false =>
              simp only [heq] at h
              obtain ⟨k, hk, hact⟩ := ih rest' (by simp at hlen; omega) h
              exact ⟨k + 2, hk, hact⟩
          | _ =>
            simp only [buildJmpTable] at h
            obtain ⟨k, hk, hact⟩ := ih rest' (by simp at hlen; omega) h
            exact ⟨k + 2, hk, hact⟩
      | _ =>
        simp only [buildJmpTable] at h
        obtain ⟨k, hk, hact⟩ := ih rest (by simp at hlen; omega) h
        exact ⟨k + 1, hk, hact⟩

theorem threadInstr_label_iff {A : Arch} (tbl : List (Sym × JmpAction))
    (i : Instr A) (l : Sym) :
    threadInstr A tbl i = .label l ↔ i = .label l := by
  cases i with
  | label _ => rfl
  | jmp l0 =>
    dsimp only [threadInstr]
    cases lookupJmpTable tbl l0 with | none => simp | some a => cases a <;> simp
  | jcc c l0 =>
    dsimp only [threadInstr]
    cases lookupJmpTable tbl l0 with | none => simp | some a => cases a <;> simp
  | jnzGpr r l0 =>
    dsimp only [threadInstr]
    cases lookupJmpTable tbl l0 with | none => simp | some a => cases a <;> simp
  | _ => simp [threadInstr]

def mkUnthreadedHost {A : Arch} {pre code suf : List (Instr A)}
    (h₂ : VllHost A) (hp₂ : h₂.prog = pre ++ threadJmp A code ++ suf) : VllHost A where
  prog := pre ++ code ++ suf
  addrOf := h₂.addrOf
  labelAddr := h₂.labelAddr
  addrOf_inj := by
    intro i j hi hj heq
    have hlen : (pre ++ code ++ suf).length = h₂.prog.length := by
      simp [hp₂, threadJmp_length]
    exact h₂.addrOf_inj (hlen ▸ hi) (hlen ▸ hj) heq
  labelAddr_wf := by
    have hget_iff : ∀ (idx : Nat) (s : Sym), (pre ++ code ++ suf)[idx]? = some (Instr.label s) ↔
        h₂.prog[idx]? = some (Instr.label s) := by
      intro idx s
      rw [hp₂]
      by_cases h1 : idx < pre.length
      · simp [List.getElem?_append_left, h1]
      · by_cases h2 : idx < pre.length + code.length
        · have h2' : idx < (pre ++ code).length := by simp; omega
          have h2'' : idx < (pre ++ threadJmp A code).length := by
            simp [threadJmp_length]; omega
          rw [List.getElem?_append_left h2', List.getElem?_append_left h2'',
            List.getElem?_append_right (Nat.le_of_not_lt h1),
            List.getElem?_append_right (Nat.le_of_not_lt h1)]
          dsimp only [threadJmp]
          rw [List.getElem?_map]
          cases code[idx - pre.length]? with
          | none => simp
          | some ins => simp [threadInstr_label_iff]
        · have hge1 : (pre ++ code).length ≤ idx := by simp; omega
          have hge2 : (pre ++ threadJmp A code).length ≤ idx := by
            simp [threadJmp_length]; omega
          rw [List.getElem?_append_right hge1, List.getElem?_append_right hge2]
          simp [threadJmp_length]
    intro k l hk hfirst
    exact h₂.labelAddr_wf ((hget_iff k l).mp hk)
      (fun j hj heq => hfirst j hj ((hget_iff j l).mpr heq))

theorem mkUnthreadedHost_prog {A : Arch} {pre code suf : List (Instr A)}
    (h₂ : VllHost A) (hp₂ : h₂.prog = pre ++ threadJmp A code ++ suf) :
    (mkUnthreadedHost h₂ hp₂).prog = pre ++ code ++ suf := by
  rfl

theorem mkUnthreadedHost_addrOf {A : Arch} {pre code suf : List (Instr A)}
    (h₂ : VllHost A) (hp₂ : h₂.prog = pre ++ threadJmp A code ++ suf) :
    (mkUnthreadedHost h₂ hp₂).addrOf = h₂.addrOf := by
  rfl

theorem mkUnthreadedHost_labelAddr {A : Arch} {pre code suf : List (Instr A)}
    (h₂ : VllHost A) (hp₂ : h₂.prog = pre ++ threadJmp A code ++ suf) :
    (mkUnthreadedHost h₂ hp₂).labelAddr = h₂.labelAddr := by
  rfl

theorem threadJmp_bwd_sim {A : Arch} {pre code suf : List (Instr A)}
    {h₂ : VllHost A} (hp₂ : h₂.prog = pre ++ threadJmp A code ++ suf)
    (hu₂ : ∀ (i j : Nat) (l : Sym),
      h₂.prog[i]? = some (Instr.label l) → h₂.prog[j]? = some (Instr.label l) → i = j)
    {post : Config A → Prop} {st : Config A}
    (hev : Eventually (vllStep h₂) post st) :
    Eventually (vllStep (mkUnthreadedHost h₂ hp₂)) post st := by
  let h₁ := mkUnthreadedHost h₂ hp₂
  let tbl := buildJmpTable A code
  have hcode_get : ∀ k, k < code.length →
      h₂.prog[pre.length + k]? = (code[k]?).map (threadInstr A tbl) := by
    intro k hk
    rw [hp₂, List.getElem?_append_left (by simp [threadJmp_length]; omega),
      List.getElem?_append_right (Nat.le_add_right pre.length k)]
    simp [threadJmp, tbl]
  have h1_get : ∀ k, k < code.length → h₁.prog[pre.length + k]? = code[k]? := by
    intro k hk
    dsimp only [h₁, mkUnthreadedHost]
    rw [List.getElem?_append_left (by simp; omega),
      List.getElem?_append_right (Nat.le_add_right pre.length k)]
    simp
  have hlab_at : ∀ (k : Nat) (l : Sym),
      h₁.prog[k]? = some (Instr.label l) → h₁.labelAddr l = h₁.addrOf k := by
    intro k l hk
    refine h₁.labelAddr_wf hk fun j hj heq => ?_
    have h1_iff : ∀ (idx : Nat) (s : Sym),
        h₁.prog[idx]? = some (Instr.label s) → h₂.prog[idx]? = some (Instr.label s) := by
      intro idx s hs
      rw [hp₂]; dsimp only [h₁, mkUnthreadedHost] at hs
      by_cases hb1 : idx < pre.length
      · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left hb1] at hs
        rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left hb1]; exact hs
      · by_cases hb2 : idx < pre.length + code.length
        · rw [List.getElem?_append_left (by simp; omega),
            List.getElem?_append_right (Nat.le_of_not_lt hb1)] at hs
          rw [List.getElem?_append_left (by simp [threadJmp_length]; omega),
            List.getElem?_append_right (Nat.le_of_not_lt hb1)]
          simp [threadJmp, List.getElem?_map, hs, threadInstr]
        · rw [List.getElem?_append_right (by simp; omega)] at hs
          rw [List.getElem?_append_right (by simp [threadJmp_length]; omega)]
          simpa [threadJmp_length] using hs
    have := hu₂ j k l (h1_iff j l heq) (h1_iff k l hk); omega
  have hhop_lbl : ∀ l l' s, lookupJmpTable tbl l = some (.toLabel l') →
      Eventually (vllStep h₁) post ⟨s, h₁.labelAddr l'⟩ →
      Eventually (vllStep h₁) post ⟨s, h₁.labelAddr l⟩ := by
    intro l l' s hlu hcont
    obtain ⟨m, hm, _, hm1⟩ := buildJmpTable_spec hlu
    have hmlt : m < code.length := getElem?_some_lt hm
    have hprog_m : h₁.prog[pre.length + m]? = some (.label l) := by rw [h1_get m hmlt, hm]
    rw [hlab_at (pre.length + m) l hprog_m]
    refine vllStep_label_cps hprog_m ?_
    rcases hm1 with hlab' | hjmp'
    · have hm1lt : m + 1 < code.length := getElem?_some_lt hlab'
      have hprog_m1 : h₁.prog[pre.length + m + 1]? = some (.label l') := by
        rw [Nat.add_assoc, h1_get (m + 1) hm1lt, hlab']
      rw [← hlab_at (pre.length + m + 1) l' hprog_m1]; exact hcont
    · have hm1lt : m + 1 < code.length := getElem?_some_lt hjmp'
      have hprog_m1 : h₁.prog[pre.length + m + 1]? = some (.jmp l') := by
        rw [Nat.add_assoc, h1_get (m + 1) hm1lt, hjmp']
      refine step_cps (vllStep h₁) post ⟨s, h₁.addrOf (pre.length + m + 1)⟩
        ⟨pre.length + m + 1, .jmp l', hprog_m1, rfl, ⟨.jump (h₁.labelAddr l') s, rfl⟩,
          (fun _ hr => by cases hr), (fun _ _ hr => by cases hr; exact hcont),
          (fun _ _ hr => by cases hr)⟩
  induction hev with
  | done st hp => exact .done st hp
  | step st mid_p hstep _ ih =>
    obtain ⟨k, i₂, hk₂, hpc, hex, hfall, hjump, hhalt⟩ := hstep
    by_cases hlt1 : k < pre.length
    · have hk₁ : h₁.prog[k]? = some i₂ := by
        rw [hp₂, List.getElem?_append_left (by simp; omega), List.getElem?_append_left hlt1] at hk₂
        dsimp only [h₁, mkUnthreadedHost]
        rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left hlt1]; exact hk₂
      exact step_cps (vllStep h₁) post st ⟨k, i₂, hk₁, hpc, hex,
        fun s' hr => ih _ (hfall s' hr), fun pc' s' hr => ih _ (hjump pc' s' hr), hhalt⟩
    · by_cases hlt2 : k < pre.length + code.length
      · have hidx : k = pre.length + (k - pre.length) := by omega
        have hklt : k - pre.length < code.length := by omega
        have hget₂ := hcode_get (k - pre.length) hklt
        rw [← hidx, hk₂] at hget₂
        cases hc : code[k - pre.length]? with
        | none => simp [hc] at hget₂
        | some i₁ =>
          simp only [hc, Option.map_some, Option.some.injEq] at hget₂
          have hk₁ : h₁.prog[k]? = some i₁ := by rw [hidx, h1_get _ hklt, hc]
          cases i₁ with
          | jmp l =>
            dsimp only [threadInstr] at hget₂
            cases hlu : lookupJmpTable tbl l with
            | none =>
              rw [hlu] at hget₂; subst hget₂
              exact step_cps (vllStep h₁) post st ⟨k, .jmp l, hk₁, hpc, hex,
                fun s' hr => ih _ (hfall s' hr), fun pc' s' hr => ih _ (hjump pc' s' hr), hhalt⟩
            | some act =>
              cases act with
              | toLabel l' =>
                rw [hlu] at hget₂; subst hget₂
                have hnext := ih ⟨st.data, h₂.labelAddr l'⟩ (hjump (h₂.labelAddr l') st.data rfl)
                refine step_cps (vllStep h₁) post st ⟨k, .jmp l, hk₁, hpc,
                  ⟨.jump (h₁.labelAddr l) st.data, rfl⟩, (fun _ hr => by cases hr),
                  (fun _ _ hr => by cases hr; exact hhop_lbl l l' st.data hlu hnext),
                  (fun _ _ hr => by cases hr)⟩
              | toRet =>
                rw [hlu] at hget₂; subst hget₂
                obtain ⟨m, hm, hmret⟩ := buildJmpTable_spec hlu
                have hmlt : m < code.length := getElem?_some_lt hm
                have hm1lt : m + 1 < code.length := getElem?_some_lt hmret
                have hprog_m : h₁.prog[pre.length + m]? = some (.label l) := by
                  rw [h1_get m hmlt, hm]
                have hprog_m1 : h₁.prog[pre.length + m + 1]? = some .ret := by
                  rw [Nat.add_assoc, h1_get (m + 1) hm1lt, hmret]
                refine step_cps (vllStep h₁) post st ⟨k, .jmp l, hk₁, hpc,
                  ⟨.jump (h₁.labelAddr l) st.data, rfl⟩, (fun _ hr => by cases hr),
                  (fun _ _ hr => ?_), (fun _ _ hr => by cases hr)⟩
                cases hr
                rw [hlab_at (pre.length + m) l hprog_m]
                refine vllStep_label_cps hprog_m ?_
                have hret_rel : ∀ np₁ np₂ o,
                    instrRel A h₁.labelAddr np₁ .ret st.data o ↔
                    instrRel A h₂.labelAddr np₂ .ret st.data o := fun _ _ _ => by
                  cases hkind : A.abi.raKind <;> simp [instrRel, hkind]
                obtain ⟨o₀, ho₀⟩ := hex
                exact step_cps (vllStep h₁) post ⟨st.data, h₁.addrOf (pre.length + m + 1)⟩
                  ⟨pre.length + m + 1, .ret, hprog_m1, rfl, ⟨o₀, (hret_rel _ _ _).mpr ho₀⟩,
                    (fun _ hr => by cases hkind : A.abi.raKind <;> simp [instrRel, hkind] at hr),
                    (fun pc' s' hr => ih _ (hjump pc' s' ((hret_rel _ _ _).mp hr))),
                    (fun c s' hr => hhalt c s' ((hret_rel _ _ _).mp hr))⟩
          | jcc c l =>
            dsimp only [threadInstr] at hget₂
            cases hlu : lookupJmpTable tbl l with
            | none =>
              rw [hlu] at hget₂; subst hget₂
              exact step_cps (vllStep h₁) post st ⟨k, .jcc c l, hk₁, hpc, hex,
                fun s' hr => ih _ (hfall s' hr), fun pc' s' hr => ih _ (hjump pc' s' hr), hhalt⟩
            | some act =>
              cases act with
              | toRet =>
                rw [hlu] at hget₂; subst hget₂
                exact step_cps (vllStep h₁) post st ⟨k, .jcc c l, hk₁, hpc, hex,
                  fun s' hr => ih _ (hfall s' hr), fun pc' s' hr => ih _ (hjump pc' s' hr), hhalt⟩
              | toLabel l' =>
                rw [hlu] at hget₂; subst hget₂
                cases hev_c : A.evalCond st.data.flags c with
                | true =>
                  have hnext := ih ⟨st.data, h₂.labelAddr l'⟩
                    (hjump (h₂.labelAddr l') st.data (by simp [instrRel, hev_c]))
                  refine step_cps (vllStep h₁) post st ⟨k, .jcc c l, hk₁, hpc,
                    ⟨.jump (h₁.labelAddr l) st.data, by simp [instrRel, hev_c]⟩,
                    (fun _ hr => by simp [instrRel, hev_c] at hr), (fun _ _ hr => ?_),
                    (fun _ _ hr => by simp [instrRel, hev_c] at hr)⟩
                  simp only [instrRel, hev_c, ↓reduceIte, InstrOut.jump.injEq] at hr
                  rcases hr with ⟨rfl, rfl⟩; exact hhop_lbl l l' st.data hlu hnext
                | false =>
                  have hnext := ih ⟨st.data, h₂.addrOf (k + 1)⟩
                    (hfall st.data (by simp [instrRel, hev_c]))
                  refine step_cps (vllStep h₁) post st ⟨k, .jcc c l, hk₁, hpc,
                    ⟨.fall st.data, by simp [instrRel, hev_c]⟩, (fun s' hr => ?_),
                    (fun _ _ hr => by simp [instrRel, hev_c] at hr),
                    (fun _ _ hr => by simp [instrRel, hev_c] at hr)⟩
                  simp only [instrRel, hev_c, Bool.false_eq_true, ↓reduceIte,
                    InstrOut.fall.injEq] at hr
                  subst hr; exact hnext
          | jnzGpr r l =>
            dsimp only [threadInstr] at hget₂
            cases hlu : lookupJmpTable tbl l with
            | none =>
              rw [hlu] at hget₂; subst hget₂
              exact step_cps (vllStep h₁) post st ⟨k, .jnzGpr r l, hk₁, hpc, hex,
                fun s' hr => ih _ (hfall s' hr), fun pc' s' hr => ih _ (hjump pc' s' hr), hhalt⟩
            | some act =>
              cases act with
              | toRet =>
                rw [hlu] at hget₂; subst hget₂
                exact step_cps (vllStep h₁) post st ⟨k, .jnzGpr r l, hk₁, hpc, hex,
                  fun s' hr => ih _ (hfall s' hr), fun pc' s' hr => ih _ (hjump pc' s' hr), hhalt⟩
              | toLabel l' =>
                rw [hlu] at hget₂; subst hget₂
                let s' := st.data.setFlags (A.jnzGprFlags (st.data.gpr r) st.data.flags)
                cases hnz : ((st.data.gpr r).setWidth 8 != 0#8) with
                | true =>
                  have hnext := ih ⟨s', h₂.labelAddr l'⟩
                    (hjump (h₂.labelAddr l') s' (by simp [instrRel, hnz, s']))
                  refine step_cps (vllStep h₁) post st ⟨k, .jnzGpr r l, hk₁, hpc,
                    ⟨.jump (h₁.labelAddr l) s', by simp [instrRel, hnz, s']⟩,
                    (fun _ hr => by simp [instrRel, hnz] at hr), (fun _ _ hr => ?_),
                    (fun _ _ hr => by simp [instrRel, hnz] at hr)⟩
                  simp only [instrRel, hnz, ↓reduceIte, InstrOut.jump.injEq] at hr
                  rcases hr with ⟨rfl, rfl⟩; exact hhop_lbl l l' s' hlu hnext
                | false =>
                  have hnext := ih ⟨s', h₂.addrOf (k + 1)⟩
                    (hfall s' (by simp [instrRel, hnz, s']))
                  refine step_cps (vllStep h₁) post st ⟨k, .jnzGpr r l, hk₁, hpc,
                    ⟨.fall s', by simp [instrRel, hnz, s']⟩, (fun s1 hr => ?_),
                    (fun _ _ hr => by simp [instrRel, hnz] at hr),
                    (fun _ _ hr => by simp [instrRel, hnz] at hr)⟩
                  simp only [instrRel, hnz, Bool.false_eq_true, ↓reduceIte,
                    InstrOut.fall.injEq] at hr
                  subst hr; exact hnext
          | label _ | pad _ | mov _ _ _ | movi _ _ | alu _ _ _ _ _ _ | cmp _ _ _ | test _ _ _
          | clearFlags | setcc _ _ | load _ _ _ _ | store _ _ _ | slotSt _ _ | slotLd _ _
          | prologue _ | epilogue _ | canonAbi _ _ | call _ | icall _ | ret | exitJmp _
          | tailJmpR _ | symAddr _ _ | ijmp _ | native _ =>
            dsimp only [threadInstr] at hget₂; subst hget₂
            exact step_cps (vllStep h₁) post st ⟨k, _, hk₁, hpc, hex,
              fun s' hr => ih _ (hfall s' hr), fun pc' s' hr => ih _ (hjump pc' s' hr), hhalt⟩
      · have hk₁ : h₁.prog[k]? = some i₂ := by
          rw [hp₂, List.getElem?_append_right (by simp [threadJmp_length]; omega)] at hk₂
          dsimp only [h₁, mkUnthreadedHost]
          rw [List.getElem?_append_right (by simp; omega)]
          simpa [threadJmp_length] using hk₂
        exact step_cps (vllStep h₁) post st ⟨k, i₂, hk₁, hpc, hex,
          fun s' hr => ih _ (hfall s' hr), fun pc' s' hr => ih _ (hjump pc' s' hr), hhalt⟩

theorem threadJmp_fwd_sim {A : Arch} {pre code suf : List (Instr A)}
    {h₂ : VllHost A} (hp₂ : h₂.prog = pre ++ threadJmp A code ++ suf)
    (hu₂ : ∀ (i j : Nat) (l : Sym),
      h₂.prog[i]? = some (Instr.label l) → h₂.prog[j]? = some (Instr.label l) → i = j)
    {post : Config A → Prop}
    (hnoTramp : ∀ (k : Nat) (l : Sym) (act : JmpAction), code[k]? = some (.label l) →
      lookupJmpTable (buildJmpTable A code) l = some act →
      ∀ s, ¬post ⟨s, h₂.addrOf (pre.length + k)⟩ ∧
        ((∀ l', code[k + 1]? ≠ some (.label l')) →
          ¬post ⟨s, h₂.addrOf (pre.length + k + 1)⟩))
    {st : Config A}
    (hev : Eventually (vllStep (mkUnthreadedHost h₂ hp₂)) post st) :
    Eventually (vllStep h₂) post st := by
  let h₁ := mkUnthreadedHost h₂ hp₂
  let tbl := buildJmpTable A code
  have hcode_get : ∀ k, k < code.length →
      h₂.prog[pre.length + k]? = (code[k]?).map (threadInstr A tbl) := by
    intro k hk
    rw [hp₂, List.getElem?_append_left (by simp [threadJmp_length]; omega),
      List.getElem?_append_right (Nat.le_add_right pre.length k)]
    simp [threadJmp, tbl]
  have h1_get : ∀ k, k < code.length → h₁.prog[pre.length + k]? = code[k]? := by
    intro k hk
    dsimp only [h₁, mkUnthreadedHost]
    rw [List.getElem?_append_left (by simp; omega),
      List.getElem?_append_right (Nat.le_add_right pre.length k)]
    simp
  have hlab_at : ∀ (k : Nat) (l : Sym),
      h₁.prog[k]? = some (Instr.label l) → h₁.labelAddr l = h₁.addrOf k := by
    intro k l hk
    refine h₁.labelAddr_wf hk fun j hj heq => ?_
    have h1_iff : ∀ (idx : Nat) (s : Sym),
        h₁.prog[idx]? = some (Instr.label s) → h₂.prog[idx]? = some (Instr.label s) := by
      intro idx s hs
      rw [hp₂]; dsimp only [h₁, mkUnthreadedHost] at hs
      by_cases hb1 : idx < pre.length
      · rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left hb1] at hs
        rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left hb1]; exact hs
      · by_cases hb2 : idx < pre.length + code.length
        · rw [List.getElem?_append_left (by simp; omega),
            List.getElem?_append_right (Nat.le_of_not_lt hb1)] at hs
          rw [List.getElem?_append_left (by simp [threadJmp_length]; omega),
            List.getElem?_append_right (Nat.le_of_not_lt hb1)]
          simp [threadJmp, List.getElem?_map, hs, threadInstr]
        · rw [List.getElem?_append_right (by simp; omega)] at hs
          rw [List.getElem?_append_right (by simp [threadJmp_length]; omega)]
          simpa [threadJmp_length] using hs
    have := hu₂ j k l (h1_iff j l heq) (h1_iff k l hk); omega
  have huniq_m : ∀ (m m0 : Nat) (l : Sym),
      code[m]? = some (.label l) → code[m0]? = some (.label l) → m0 = m := by
    intro m m0 l hm hm0
    have h1m : h₁.prog[pre.length + m]? = some (.label l) := by
      rw [h1_get m (getElem?_some_lt hm), hm]
    have h1m0 : h₁.prog[pre.length + m0]? = some (.label l) := by
      rw [h1_get m0 (getElem?_some_lt hm0), hm0]
    have heqA := (hlab_at _ l h1m0).symm.trans (hlab_at _ l h1m)
    have := h₁.addrOf_inj (getElem?_some_lt h1m0) (getElem?_some_lt h1m) heqA
    omega
  suffices hinv :
      Eventually (vllStep h₂) post st ∧
      (∀ m l act, code[m]? = some (.label l) → lookupJmpTable tbl l = some act →
        st.pc = h₂.addrOf (pre.length + m) →
        match act with
        | .toLabel l' => Eventually (vllStep h₂) post ⟨st.data, h₂.labelAddr l'⟩
        | .toRet =>
          (∃ o, instrRel A h₂.labelAddr 0#64 .ret st.data o) ∧
          (∀ pc' s', instrRel A h₂.labelAddr 0#64 .ret st.data (.jump pc' s') →
            Eventually (vllStep h₂) post ⟨s', pc'⟩)) ∧
      (∀ m l act, code[m]? = some (.label l) → lookupJmpTable tbl l = some act →
        st.pc = h₂.addrOf (pre.length + m + 1) →
        match act with
        | .toLabel l' => Eventually (vllStep h₂) post ⟨st.data, h₂.labelAddr l'⟩
        | .toRet =>
          (∃ o, instrRel A h₂.labelAddr 0#64 .ret st.data o) ∧
          (∀ pc' s', instrRel A h₂.labelAddr 0#64 .ret st.data (.jump pc' s') →
            Eventually (vllStep h₂) post ⟨s', pc'⟩)) from hinv.1
  induction hev with
  | done st hp =>
    refine ⟨.done st hp, fun m l act hm hlu hpc => ?_, fun m l act hm hlu hpc => ?_⟩
    · exact absurd (by cases st; simp only at hpc; subst hpc; exact hp)
        (hnoTramp m l act hm hlu st.data).1
    · obtain ⟨m0, hm0, hspec0⟩ := buildJmpTable_spec hlu
      have := huniq_m m m0 l hm hm0; subst this
      cases act with
      | toLabel l' =>
        rcases hspec0.2 with hlab' | hjmp'
        · have hm1lt : m0 + 1 < code.length := getElem?_some_lt hlab'
          have hprog_m1 : h₁.prog[pre.length + m0 + 1]? = some (.label l') := by
            rw [Nat.add_assoc, h1_get (m0 + 1) hm1lt, hlab']
          have hlab'A : h₂.labelAddr l' = h₂.addrOf (pre.length + m0 + 1) :=
            hlab_at (pre.length + m0 + 1) l' hprog_m1
          dsimp only; rw [hlab'A, ← hpc]
          exact .done st hp
        · have hnotL : ∀ l'', code[m0 + 1]? ≠ some (.label l'') := fun l'' h => by
            rw [hjmp'] at h; cases h
          exact absurd (by cases st; simp only at hpc; subst hpc; exact hp)
            ((hnoTramp m0 l (.toLabel l') hm0 hlu st.data).2 hnotL)
      | toRet =>
        have hnotL : ∀ l'', code[m0 + 1]? ≠ some (.label l'') := fun l'' h => by
          rw [hspec0] at h; cases h
        exact absurd (by cases st; simp only at hpc; subst hpc; exact hp)
          ((hnoTramp m0 l .toRet hm0 hlu st.data).2 hnotL)
  | step st mid_p hstep _ ih =>
    obtain ⟨k, i₁, hk₁, hpc, hex, hfall, hjump, hhalt⟩ := hstep
    have hklt : k < h₁.prog.length := getElem?_some_lt hk₁
    have hinv3 : ∀ m l act, code[m]? = some (.label l) → lookupJmpTable tbl l = some act →
        st.pc = h₂.addrOf (pre.length + m + 1) →
        match act with
        | .toLabel l' => Eventually (vllStep h₂) post ⟨st.data, h₂.labelAddr l'⟩
        | .toRet =>
          (∃ o, instrRel A h₂.labelAddr 0#64 .ret st.data o) ∧
          (∀ pc' s', instrRel A h₂.labelAddr 0#64 .ret st.data (.jump pc' s') →
            Eventually (vllStep h₂) post ⟨s', pc'⟩) := by
      intro m l act hm hlu hpc3
      obtain ⟨m0, hm0, hspec0⟩ := buildJmpTable_spec hlu
      have := huniq_m m m0 l hm hm0; subst this
      cases act with
      | toLabel l' =>
        rcases hspec0.2 with hlab' | hjmp'
        · have hm1lt : m0 + 1 < code.length := getElem?_some_lt hlab'
          have hprog_m1 : h₁.prog[pre.length + m0 + 1]? = some (.label l') := by
            rw [Nat.add_assoc, h1_get (m0 + 1) hm1lt, hlab']
          have heqk : k = pre.length + m0 + 1 :=
            h₁.addrOf_inj hklt (getElem?_some_lt hprog_m1) (hpc.trans hpc3)
          subst heqk
          have heqi : i₁ = .label l' := Option.some.inj (hk₁.symm.trans hprog_m1)
          subst heqi
          have hlab'A : h₂.labelAddr l' = h₂.addrOf (pre.length + m0 + 1) :=
            hlab_at (pre.length + m0 + 1) l' hprog_m1
          dsimp only; rw [hlab'A]
          have h2_m1 : h₂.prog[pre.length + m0 + 1]? = some (.label l') := by
            rw [Nat.add_assoc, hcode_get (m0 + 1) hm1lt, hlab']; rfl
          exact vllStep_label_cps h2_m1 (ih _ (hfall st.data rfl)).1
        · have hm1lt : m0 + 1 < code.length := getElem?_some_lt hjmp'
          have hprog_m1 : h₁.prog[pre.length + m0 + 1]? = some (.jmp l') := by
            rw [Nat.add_assoc, h1_get (m0 + 1) hm1lt, hjmp']
          have heqk : k = pre.length + m0 + 1 :=
            h₁.addrOf_inj hklt (getElem?_some_lt hprog_m1) (hpc.trans hpc3)
          subst heqk
          have heqi : i₁ = .jmp l' := Option.some.inj (hk₁.symm.trans hprog_m1)
          subst heqi
          exact (ih ⟨st.data, h₂.labelAddr l'⟩ (hjump (h₁.labelAddr l') st.data rfl)).1
      | toRet =>
        have hm1lt : m0 + 1 < code.length := getElem?_some_lt hspec0
        have hprog_m1 : h₁.prog[pre.length + m0 + 1]? = some .ret := by
          rw [Nat.add_assoc, h1_get (m0 + 1) hm1lt, hspec0]
        have heqk : k = pre.length + m0 + 1 :=
          h₁.addrOf_inj hklt (getElem?_some_lt hprog_m1) (hpc.trans hpc3)
        subst heqk
        have heqi : i₁ = .ret := Option.some.inj (hk₁.symm.trans hprog_m1)
        subst heqi
        have hret_rel : ∀ np₁ np₂ o,
            instrRel A h₁.labelAddr np₁ .ret st.data o ↔
            instrRel A h₂.labelAddr np₂ .ret st.data o := fun _ _ _ => by
          cases hkind : A.abi.raKind <;> simp [instrRel, hkind]
        obtain ⟨o₀, ho₀⟩ := hex
        exact ⟨⟨o₀, (hret_rel _ _ _).mp ho₀⟩,
          fun pc' s' hr => (ih ⟨s', pc'⟩ (hjump pc' s' ((hret_rel _ _ _).mpr hr))).1⟩
    have hinv2 : ∀ m l act, code[m]? = some (.label l) → lookupJmpTable tbl l = some act →
        st.pc = h₂.addrOf (pre.length + m) →
        match act with
        | .toLabel l' => Eventually (vllStep h₂) post ⟨st.data, h₂.labelAddr l'⟩
        | .toRet =>
          (∃ o, instrRel A h₂.labelAddr 0#64 .ret st.data o) ∧
          (∀ pc' s', instrRel A h₂.labelAddr 0#64 .ret st.data (.jump pc' s') →
            Eventually (vllStep h₂) post ⟨s', pc'⟩) := by
      intro m l act hm hlu hpc2
      have hmlt : m < code.length := getElem?_some_lt hm
      have hprog_m : h₁.prog[pre.length + m]? = some (.label l) := by rw [h1_get m hmlt, hm]
      have heqk : k = pre.length + m :=
        h₁.addrOf_inj hklt (getElem?_some_lt hprog_m) (hpc.trans hpc2)
      subst heqk
      have heqi : i₁ = .label l := Option.some.inj (hk₁.symm.trans hprog_m)
      subst heqi
      exact (ih ⟨st.data, h₁.addrOf (pre.length + m + 1)⟩ (hfall st.data rfl)).2.2
        m l act hm hlu rfl
    refine ⟨?_, hinv2, hinv3⟩
    by_cases hlt1 : k < pre.length
    · have hk₂ : h₂.prog[k]? = some i₁ := by
        dsimp only [h₁, mkUnthreadedHost] at hk₁
        rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left hlt1] at hk₁
        rw [hp₂, List.getElem?_append_left (by simp; omega), List.getElem?_append_left hlt1]
        exact hk₁
      exact step_cps (vllStep h₂) post st ⟨k, i₁, hk₂, hpc, hex,
        fun s' hr => (ih _ (hfall s' hr)).1, fun pc' s' hr => (ih _ (hjump pc' s' hr)).1, hhalt⟩
    · by_cases hlt2 : k < pre.length + code.length
      · have hidx : k = pre.length + (k - pre.length) := by omega
        have hkltC : k - pre.length < code.length := by omega
        have hc : code[k - pre.length]? = some i₁ := by
          have := h1_get (k - pre.length) hkltC; rw [← hidx, hk₁] at this; exact this.symm
        have hk₂ : h₂.prog[k]? = some (threadInstr A tbl i₁) := by
          rw [hidx, hcode_get (k - pre.length) hkltC, hc]; rfl
        have hjump_toLabel : ∀ l l' s', lookupJmpTable tbl l = some (.toLabel l') →
            mid_p ⟨s', h₁.labelAddr l⟩ → Eventually (vllStep h₂) post ⟨s', h₂.labelAddr l'⟩ := by
          intro l l' s' hlu hmid
          obtain ⟨m, hm, _⟩ := buildJmpTable_spec hlu
          have hmlt : m < code.length := getElem?_some_lt hm
          have hprog_m : h₁.prog[pre.length + m]? = some (.label l) := by rw [h1_get m hmlt, hm]
          have hlab := hlab_at (pre.length + m) l hprog_m
          exact (ih ⟨s', h₁.labelAddr l⟩ hmid).2.1 m l (.toLabel l') hm hlu hlab
        cases i₁ with
        | jmp l =>
          dsimp only [threadInstr] at hk₂
          cases hlu : lookupJmpTable tbl l with
          | none =>
            rw [hlu] at hk₂
            exact step_cps (vllStep h₂) post st ⟨k, .jmp l, hk₂, hpc, hex,
              fun s' hr => (ih _ (hfall s' hr)).1,
              fun pc' s' hr => (ih _ (hjump pc' s' hr)).1, hhalt⟩
          | some act =>
            cases act with
            | toLabel l' =>
              rw [hlu] at hk₂
              refine step_cps (vllStep h₂) post st ⟨k, .jmp l', hk₂, hpc,
                ⟨.jump (h₂.labelAddr l') st.data, rfl⟩, (fun _ hr => by cases hr),
                (fun _ _ hr => ?_), (fun _ _ hr => by cases hr)⟩
              cases hr; exact hjump_toLabel l l' st.data hlu (hjump (h₁.labelAddr l) st.data rfl)
            | toRet =>
              rw [hlu] at hk₂
              obtain ⟨m, hm, _⟩ := buildJmpTable_spec hlu
              have hmlt : m < code.length := getElem?_some_lt hm
              have hprog_m : h₁.prog[pre.length + m]? = some (.label l) := by
                rw [h1_get m hmlt, hm]
              have hret := (ih ⟨st.data, h₁.labelAddr l⟩ (hjump (h₁.labelAddr l) st.data rfl)).2.1
                m l .toRet hm hlu (hlab_at (pre.length + m) l hprog_m)
              have hret_rel : ∀ np₁ np₂ o,
                  instrRel A h₂.labelAddr np₁ .ret st.data o ↔
                  instrRel A h₂.labelAddr np₂ .ret st.data o := fun _ _ _ => by
                cases hkind : A.abi.raKind <;> simp [instrRel, hkind]
              obtain ⟨o₀, ho₀⟩ := hret.1
              refine step_cps (vllStep h₂) post st ⟨k, .ret, hk₂, hpc,
                ⟨o₀, (hret_rel _ _ _).mpr ho₀⟩,
                (fun _ hr => by cases hkind : A.abi.raKind <;> simp [instrRel, hkind] at hr),
                (fun pc' s' hr => hret.2 pc' s' ((hret_rel _ _ _).mp hr)),
                (fun _ _ hr => by cases hkind : A.abi.raKind <;> simp [instrRel, hkind] at hr)⟩
        | jcc c l =>
          dsimp only [threadInstr] at hk₂
          cases hlu : lookupJmpTable tbl l with
          | none =>
            rw [hlu] at hk₂
            exact step_cps (vllStep h₂) post st ⟨k, .jcc c l, hk₂, hpc, hex,
              fun s' hr => (ih _ (hfall s' hr)).1,
              fun pc' s' hr => (ih _ (hjump pc' s' hr)).1, hhalt⟩
          | some act =>
            cases act with
            | toRet =>
              rw [hlu] at hk₂
              exact step_cps (vllStep h₂) post st ⟨k, .jcc c l, hk₂, hpc, hex,
                fun s' hr => (ih _ (hfall s' hr)).1,
                fun pc' s' hr => (ih _ (hjump pc' s' hr)).1, hhalt⟩
            | toLabel l' =>
              rw [hlu] at hk₂
              cases hev_c : A.evalCond st.data.flags c with
              | true =>
                refine step_cps (vllStep h₂) post st ⟨k, .jcc c l', hk₂, hpc,
                  ⟨.jump (h₂.labelAddr l') st.data, by simp [instrRel, hev_c]⟩,
                  (fun _ hr => by simp [instrRel, hev_c] at hr), (fun _ _ hr => ?_),
                  (fun _ _ hr => by simp [instrRel, hev_c] at hr)⟩
                simp only [instrRel, hev_c, ↓reduceIte, InstrOut.jump.injEq] at hr
                rcases hr with ⟨rfl, rfl⟩
                exact hjump_toLabel l l' st.data hlu
                  (hjump (h₁.labelAddr l) st.data (by simp [instrRel, hev_c, h₁]))
              | false =>
                refine step_cps (vllStep h₂) post st ⟨k, .jcc c l', hk₂, hpc,
                  ⟨.fall st.data, by simp [instrRel, hev_c]⟩, (fun s' hr => ?_),
                  (fun _ _ hr => by simp [instrRel, hev_c] at hr),
                  (fun _ _ hr => by simp [instrRel, hev_c] at hr)⟩
                simp only [instrRel, hev_c, Bool.false_eq_true, ↓reduceIte,
                  InstrOut.fall.injEq] at hr
                subst hr; exact (ih _ (hfall st.data (by simp [instrRel, hev_c]))).1
        | jnzGpr r l =>
          dsimp only [threadInstr] at hk₂
          cases hlu : lookupJmpTable tbl l with
          | none =>
            rw [hlu] at hk₂
            exact step_cps (vllStep h₂) post st ⟨k, .jnzGpr r l, hk₂, hpc, hex,
              fun s' hr => (ih _ (hfall s' hr)).1,
              fun pc' s' hr => (ih _ (hjump pc' s' hr)).1, hhalt⟩
          | some act =>
            cases act with
            | toRet =>
              rw [hlu] at hk₂
              exact step_cps (vllStep h₂) post st ⟨k, .jnzGpr r l, hk₂, hpc, hex,
                fun s' hr => (ih _ (hfall s' hr)).1,
                fun pc' s' hr => (ih _ (hjump pc' s' hr)).1, hhalt⟩
            | toLabel l' =>
              rw [hlu] at hk₂
              let s' := st.data.setFlags (A.jnzGprFlags (st.data.gpr r) st.data.flags)
              cases hnz : ((st.data.gpr r).setWidth 8 != 0#8) with
              | true =>
                refine step_cps (vllStep h₂) post st ⟨k, .jnzGpr r l', hk₂, hpc,
                  ⟨.jump (h₂.labelAddr l') s', by simp [instrRel, hnz, s']⟩,
                  (fun _ hr => by simp [instrRel, hnz] at hr), (fun _ _ hr => ?_),
                  (fun _ _ hr => by simp [instrRel, hnz] at hr)⟩
                simp only [instrRel, hnz, ↓reduceIte, InstrOut.jump.injEq] at hr
                rcases hr with ⟨rfl, rfl⟩
                exact hjump_toLabel l l' s' hlu
                  (hjump (h₁.labelAddr l) s' (by simp [instrRel, hnz, s', h₁]))
              | false =>
                refine step_cps (vllStep h₂) post st ⟨k, .jnzGpr r l', hk₂, hpc,
                  ⟨.fall s', by simp [instrRel, hnz, s']⟩, (fun s1 hr => ?_),
                  (fun _ _ hr => by simp [instrRel, hnz] at hr),
                  (fun _ _ hr => by simp [instrRel, hnz] at hr)⟩
                simp only [instrRel, hnz, Bool.false_eq_true, ↓reduceIte,
                  InstrOut.fall.injEq] at hr
                subst hr; exact (ih _ (hfall s' (by simp [instrRel, hnz, s']))).1
        | label _ | pad _ | mov _ _ _ | movi _ _ | alu _ _ _ _ _ _ | cmp _ _ _ | test _ _ _
        | clearFlags | setcc _ _ | load _ _ _ _ | store _ _ _ | slotSt _ _ | slotLd _ _
        | prologue _ | epilogue _ | canonAbi _ _ | call _ | icall _ | ret | exitJmp _
        | tailJmpR _ | symAddr _ _ | ijmp _ | native _ =>
          dsimp only [threadInstr] at hk₂
          exact step_cps (vllStep h₂) post st ⟨k, _, hk₂, hpc, hex,
            fun s' hr => (ih _ (hfall s' hr)).1,
            fun pc' s' hr => (ih _ (hjump pc' s' hr)).1, hhalt⟩
      · have hk₂ : h₂.prog[k]? = some i₁ := by
          dsimp only [h₁, mkUnthreadedHost] at hk₁
          rw [List.getElem?_append_right (by simp; omega)] at hk₁
          rw [hp₂, List.getElem?_append_right (by simp [threadJmp_length]; omega)]
          simpa [threadJmp_length] using hk₁
        exact step_cps (vllStep h₂) post st ⟨k, i₁, hk₂, hpc, hex,
          fun s' hr => (ih _ (hfall s' hr)).1,
          fun pc' s' hr => (ih _ (hjump pc' s' hr)).1, hhalt⟩

end LeanQbe.T.Vll
