module

public import LeanQbe.T.Vll.RegaInst
public import LeanQbe.T.Arm64.VllArm64
public import LeanQbe.T.Arm64.VllAsmArm64
public import LeanQbe.T.Arm64.Targ
import LeanQbe.T.TargetLemmas
import LeanQbe.T.AbiLemmas

/-!
# AArch64 `BedrockMach` L1 Core 32-Bit Zero-Extension Op Proofs (`Arm64.VllFactorArm64CoreLemmas`)

Factored out of `Arm64.VllFactorArm641` (`sext32_shl_ashr`, `vllCoreOp_zero32`) to keep every
module well under `2,500` LOC with zero `@[expose]` on theorems/lemmas.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open LeanQbe.T
open LeanQbe.T.Vll

private theorem setWidth_setWidth_self64 {n : Nat} (hn : n ≤ 64) (v : BitVec n) :
    (v.setWidth 64).setWidth n = v :=
  (BitVec.setWidth_setWidth_of_le v hn).trans (BitVec.setWidth_eq v)

theorem sext32_shl_ashr {m : Nat} (hm : m = 8 ∨ m = 16 ∨ m = 32) (x : BitVec 64) :
    let sh := ((BitVec.ofNat 64 (32 - m)).setWidth 32).toNat % 32
    ((x.setWidth 32) <<< sh).sshiftRight sh = (x.setWidth m).signExtend 32 := by
  have hsh : ((BitVec.ofNat 64 (32 - m)).setWidth 32).toNat % 32 = 32 - m := by
    rcases hm with rfl | rfl | rfl <;> decide
  have hm1 : 1 ≤ m := by omega
  have hm32 : m ≤ 32 := by omega
  dsimp only; rw [hsh]
  apply BitVec.eq_of_getElem_eq; intro i hi
  rw [BitVec.getElem_sshiftRight, BitVec.getElem_signExtend]
  by_cases him : i < m
  · have hlt : 32 - m + i < 32 := by omega
    have hge : ¬(32 - m + i < 32 - m) := by omega
    have hsub : 32 - m + i - (32 - m) = i := by omega
    have hi64 : i < 64 := by omega
    simp [hlt, him, BitVec.getElem_shiftLeft, hge, hsub, BitVec.getElem_setWidth, hi64]
  · have hnlt : ¬(32 - m + i < 32) := by omega
    have hmsb : ((x.setWidth 32) <<< (32 - m)).msb = (x.setWidth m).msb := by
      rw [BitVec.msb_eq_getLsbD_last, BitVec.msb_eq_getLsbD_last]
      have hge : ¬(31 < 32 - m) := by omega
      have hsub : 31 - (32 - m) = m - 1 := by omega
      have hm_lt : m - 1 < m := by omega
      simp [hge, hsub, hm_lt]
    simp [hnlt, him, hmsb]

theorem vllCoreOp_zero32 {h : VllHost arm64Arch} {k : Nat} {sig : List Ty}
    {code : OpCode sig [.bits 32]} {pas : Tup (PArg Arm64.Reg Empty ArmCond) sig}
    {rd : Arm64.Reg} {vh : VariantHint} {c : List (Instr arm64Arch)} {clob : FlagMask}
    {vs : Tup Val sig} {P : Tup Val [.bits 32] → Prop}
    {s : MachSt arm64Arch} {post : Config arm64Arch → Prop}
    (hop : vllCoreOp arm64Arch (some ∘ armCmpCond) code pas (.gpr rd, ()) vh = some (c, clob))
    (ha : ∀ r ∈ tupArgGprs pas, r ∉ armScratch)
    (hrel : TRel ((vllMach arm64Arch).PArgHolds s) pas vs) (hwp : code.wp vs P) :
    (vllMach arm64Arch).FallsTo arm64Arch.condReads h k c (rd :: armScratch) [] clob s
      (fun s' => (∃ rv : BitVec 32, P (rv, ()) ∧ s'.gpr rd = rv.setWidth 64) ∧
        s'.mem = s.mem) post := by
  have alu32 : ∀ {op : CoreAlu} {pa pb : PArg Arm64.Reg Empty ArmCond (.bits 32)}
      {va vb : BitVec 32},
      vllCoreAlu arm64Arch op .w32 pa pb rd = some (c, clob) →
      (∀ r ∈ pb.gprs, r ∉ armScratch) →
      (vllMach arm64Arch).PArgHolds s (.bits 32) pa va →
      (vllMach arm64Arch).PArgHolds s (.bits 32) pb vb →
      P (op.eval .w32 va vb, ()) →
      (vllMach arm64Arch).FallsTo arm64Arch.condReads h k c (rd :: armScratch) [] clob s
        (fun s' => (∃ rv : BitVec 32, P (rv, ()) ∧ s'.gpr rd = rv.setWidth 64) ∧
          s'.mem = s.mem) post := by
    intro op pa pb va vb halu hpb_ns hpa hpb hP
    unfold vllCoreAlu at halu
    have hpb_val : ∀ (sb : Src arm64Arch) (s1 : MachSt arm64Arch),
        vllSrcOfPArg (A := arm64Arch) .w32 pb = some sb →
        (vllMach arm64Arch).KeepsGpr s s1 armScratch →
        sb.evalW .w32 s1.gpr = vb := by
      intro sb s1 hsb hkp
      cases pb with
      | vec v => exact v.elim
      | gpr rb =>
        cases hsb; dsimp only [Src.evalW, Src.eval]
        have hrb : s1.gpr rb = s.gpr rb := hkp rb (hpb_ns rb List.mem_cons_self)
        rw [hrb]; exact hpb.2
      | imm cb =>
        cases hsb; have hEq : cb = vb := hpb; subst hEq
        exact setWidth_setWidth_self64 (by decide) cb
    cases hsb : vllSrcOfPArg (A := arm64Arch) .w32 pb with
    | none => simp [hsb] at halu
    | some sb =>
      cases pa with
      | vec v => exact v.elim
      | gpr ra =>
        simp only [vllRegOfPArg, hsb, Option.some.injEq, Prod.mk.injEq] at halu
        rcases halu with ⟨rfl, rfl⟩
        have hra : (s.gpr ra).setWidth 32 = va := hpa.2
        refine Machine.FallsTo.conseq (fallsTo_weaken_rd
          (vllMach_alu_spec arm64Arch_wf (op := op) (w := .w32) (rd := rd) (lhs := ra)
            (rhs := sb) (sf := false))) fun s' ⟨hg, _, _, hm⟩ _ => ?_
        have hsb0 := hpb_val sb s hsb (fun _ _ => rfl)
        dsimp only [Width.bits] at hg
        rw [hra, hsb0] at hg
        exact ⟨⟨_, hP, hg⟩, hm⟩
      | imm ca =>
        have hEq : ca = va := hpa; subst hEq
        simp only [vllRegOfPArg, arm64Arch, arm64Abi, armScratch, List.head?_cons, Option.map_some,
          hsb, Option.some.injEq, Prod.mk.injEq] at halu
        rcases halu with ⟨rfl, rfl⟩
        have hcomp : (vllMach arm64Arch).FallsTo arm64Arch.condReads h k
            ([.movi (.reg .X16) (ca.setWidth 64)] ++ [.alu op .w32 rd (.reg .X16) sb false])
            (armScratch ++ [rd]) ([] ++ []) (maskNone ||| arm64Arch.aluClob op false) s
            (fun s' => (∃ rv : BitVec 32, P (rv, ()) ∧ s'.gpr rd = rv.setWidth 64) ∧
              s'.mem = s.mem) post :=
          Machine.FallsTo.comp
            (Machine.FallsTo.weaken (g₂ := armScratch)
              (vllMach_movi_spec (A := arm64Arch) (s := s) (rd := .reg .X16)
                (imm := ca.setWidth 64))
              (fun r hr => by
                simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self)
              (fun _ hr => False.elim (List.not_mem_nil hr)) (flagMask_none_sub _))
            fun s1 ⟨hg1, hm1⟩ hfr1 => Machine.FallsTo.conseq
              (vllMach_alu_spec arm64Arch_wf (op := op) (w := .w32) (rd := rd)
                (lhs := .reg .X16) (rhs := sb) (sf := false)) fun s2 ⟨hg2, _, _, hm2⟩ _ => by
                  have hg1' : s1.gpr (.reg .X16) = ca.setWidth 64 := hg1
                  have ha1 : (s1.gpr (.reg .X16)).setWidth 32 = ca := by
                    rw [hg1']; exact setWidth_setWidth_self64 (by decide) ca
                  have hb1 := hpb_val sb s1 hsb hfr1.1
                  dsimp only [Width.bits] at hg2
                  rw [ha1, hb1] at hg2
                  exact ⟨⟨_, hP, hg2⟩, hm2.trans hm1⟩
        exact Machine.FallsTo.weaken hcomp
          (fun r hr => by
            rcases List.mem_append.mp hr with h1 | h2
            · exact List.mem_cons_of_mem rd h1
            · simp only [List.mem_singleton] at h2; subst h2; exact List.mem_cons_self)
          (fun _ hr => False.elim (List.not_mem_nil hr)) (by cases op <;> decide)
  cases code with
  | copy t =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
    rcases hrel with _ | ⟨hpa, hnil⟩; cases hnil
    cases pa with
    | vec v => exact v.elim
    | gpr r =>
      cases hop
      have hr : (s.gpr r).setWidth 32 = va := hpa.2
      refine Machine.FallsTo.conseq (fallsTo_weaken_rd
        (vllMach_movW_spec arm64Arch_wf (w := .w32) (rd := rd) (rs := r))) ?_
      intro s' ⟨hg, _, hm⟩ _; dsimp only [Width.bits] at hg; rw [hr] at hg
      exact ⟨⟨va, hwp, hg⟩, hm⟩
    | imm cv =>
      cases hop; have hEq : cv = va := hpa; subst hEq
      refine Machine.FallsTo.conseq (fallsTo_weaken_rd
        (vllMach_movi_spec (A := arm64Arch) (rd := rd) (imm := cv.setWidth 64))) ?_
      intro s' ⟨hg, hm⟩ _; exact ⟨⟨cv, hwp, hg⟩, hm⟩
  | bitcast t u hsz =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
    rcases hrel with _ | ⟨hpa, hnil⟩; cases hnil
    cases t with
    | bool | float _ | pair _ _ => cases hop
    | bits m =>
      have hmn : m = 32 := hsz; subst hmn
      cases pa with
      | vec v => exact v.elim
      | gpr r =>
        cases hop
        have hr : (s.gpr r).setWidth 32 = va := hpa.2
        refine Machine.FallsTo.conseq (fallsTo_weaken_rd
          (vllMach_movW_spec arm64Arch_wf (w := .w32) (rd := rd) (rs := r))) ?_
        intro s' ⟨hg, _, hm⟩ _; dsimp only [Width.bits] at hg; rw [hr] at hg
        exact ⟨⟨va, by simpa [OpCode.wp, ofBits, toBits] using hwp, hg⟩, hm⟩
      | imm cv =>
        cases hop; have hEq : cv = va := hpa; subst hEq
        refine Machine.FallsTo.conseq (fallsTo_weaken_rd
          (vllMach_movi_spec (A := arm64Arch) (rd := rd) (imm := cv.setWidth 64))) ?_
        intro s' ⟨hg, hm⟩ _
        exact ⟨⟨cv, by simpa [OpCode.wp, ofBits, toBits] using hwp, hg⟩, hm⟩
  | add _ | sub _ | mul _ | and _ | or _ | xor _ | shl _ | lshr _ | ashr _ =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
    rcases hrel with _ | ⟨hpa, hrel2⟩; rcases hrel2 with _ | ⟨hpb, hnil⟩; cases hnil
    have hpb_ns : ∀ r ∈ pb.gprs, r ∉ armScratch := fun r hr =>
      ha r (List.mem_append_right _ (List.mem_append_left _ hr))
    exact alu32 hop hpb_ns hpa hpb hwp
  | neg _ =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
    rcases hrel with _ | ⟨hpa, hnil⟩; cases hnil
    dsimp only [vllCoreOp, vllCoreNeg, withWidth, vllCoreNegW] at hop
    cases hsb : vllSrcOfPArg (A := arm64Arch) .w32 pa with
    | none => simp [hsb] at hop
    | some sb =>
      simp only [arm64Arch, arm64Abi, armScratch, List.head?_cons, hsb] at hop
      cases hop
      have hcomp : (vllMach arm64Arch).FallsTo arm64Arch.condReads h k
          ([.movi (.reg .X16) 0#64] ++ [.alu .sub .w32 rd (.reg .X16) sb false])
          (armScratch ++ [rd]) ([] ++ []) (maskNone ||| arm64Arch.aluClob .sub false) s
          (fun s' => (∃ rv : BitVec 32, P (rv, ()) ∧ s'.gpr rd = rv.setWidth 64) ∧
            s'.mem = s.mem) post :=
        Machine.FallsTo.comp
          (Machine.FallsTo.weaken (g₂ := armScratch)
            (vllMach_movi_spec (A := arm64Arch) (s := s) (rd := .reg .X16) (imm := 0#64))
            (fun r hr => by
              simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self)
            (fun _ hr => False.elim (List.not_mem_nil hr)) (flagMask_none_sub _))
          fun s1 ⟨hg1, hm1⟩ hfr1 => Machine.FallsTo.conseq
            (vllMach_alu_spec arm64Arch_wf (op := .sub) (w := .w32) (rd := rd)
              (lhs := .reg .X16) (rhs := sb) (sf := false)) fun s2 ⟨hg2, _, _, hm2⟩ _ => by
                have hg1' : s1.gpr (.reg .X16) = 0#64 := hg1
                have hsb1 : sb.evalW .w32 s1.gpr = va := by
                  cases pa with
                  | vec v => exact v.elim
                  | gpr r =>
                    cases hsb; dsimp only [Src.evalW, Src.eval]
                    have hr1 : s1.gpr r = s.gpr r :=
                      hfr1.1 r (ha r (List.mem_append_left _ List.mem_cons_self))
                    rw [hr1]; exact hpa.2
                  | imm cv =>
                    cases hsb; have hEq : cv = va := hpa; subst hEq
                    exact setWidth_setWidth_self64 (by decide) cv
                dsimp only [Width.bits] at hg2; rw [hg1', hsb1] at hg2
                have hsub : CoreAlu.sub.eval .w32 ((0#64).setWidth 32) va = -va :=
                  BitVec.zero_sub va
                rw [hsub] at hg2; exact ⟨⟨-va, hwp, hg2⟩, hm2.trans hm1⟩
      exact Machine.FallsTo.weaken hcomp
        (fun r hr => by
          rcases List.mem_append.mp hr with h1 | h2
          · exact List.mem_cons_of_mem rd h1
          · simp only [List.mem_singleton] at h2; subst h2; exact List.mem_cons_self)
        (fun _ hr => False.elim (List.not_mem_nil hr)) (by decide)
  | not _ =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
    rcases hrel with _ | ⟨hpa, hnil⟩; cases hnil
    dsimp only [vllCoreOp, vllCoreNot, withWidth, vllCoreNotW] at hop
    have hxor : CoreAlu.xor.eval .w32 va ((~~~0#64).setWidth 32) = ~~~va := by
      show va ^^^ ~~~0#32 = ~~~va; exact BitVec.xor_allOnes
    cases pa with
    | vec v => exact v.elim
    | gpr r =>
      cases hop
      have hr : (s.gpr r).setWidth 32 = va := hpa.2
      refine Machine.FallsTo.conseq (fallsTo_weaken_rd
        (vllMach_alu_spec arm64Arch_wf (op := .xor) (w := .w32) (rd := rd) (lhs := r)
          (rhs := .imm (~~~0#64)) (sf := false))) fun s' ⟨hg, _, _, hm⟩ _ => by
            dsimp only [Width.bits, Src.evalW, Src.eval] at hg; rw [hr, hxor] at hg
            exact ⟨⟨~~~va, hwp, hg⟩, hm⟩
    | imm cv =>
      have hEq : cv = va := hpa; subst hEq; cases hop
      have hcomp : (vllMach arm64Arch).FallsTo arm64Arch.condReads h k
          ([.movi (.reg .X16) (cv.setWidth 64)] ++
            [.alu .xor .w32 rd (.reg .X16) (.imm (~~~0#64)) false])
          (armScratch ++ [rd]) ([] ++ []) (maskNone ||| arm64Arch.aluClob .xor false) s
          (fun s' => (∃ rv : BitVec 32, P (rv, ()) ∧ s'.gpr rd = rv.setWidth 64) ∧
            s'.mem = s.mem) post :=
        Machine.FallsTo.comp
          (Machine.FallsTo.weaken (g₂ := armScratch)
            (vllMach_movi_spec (A := arm64Arch) (s := s) (rd := .reg .X16)
              (imm := cv.setWidth 64))
            (fun r hr => by
              simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self)
            (fun _ hr => False.elim (List.not_mem_nil hr)) (flagMask_none_sub _))
          fun s1 ⟨hg1, hm1⟩ _ => Machine.FallsTo.conseq
            (vllMach_alu_spec arm64Arch_wf (op := .xor) (w := .w32) (rd := rd) (lhs := .reg .X16)
              (rhs := .imm (~~~0#64)) (sf := false)) fun s2 ⟨hg2, _, _, hm2⟩ _ => by
                have hg1' : s1.gpr (.reg .X16) = cv.setWidth 64 := hg1
                dsimp only [Width.bits, Src.evalW, Src.eval] at hg2
                rw [hg1', setWidth_setWidth_self64 (by decide), hxor] at hg2
                exact ⟨⟨~~~cv, hwp, hg2⟩, hm2.trans hm1⟩
      exact Machine.FallsTo.weaken hcomp
        (fun r hr => by
          rcases List.mem_append.mp hr with h1 | h2
          · exact List.mem_cons_of_mem rd h1
          · simp only [List.mem_singleton] at h2; subst h2; exact List.mem_cons_self)
        (fun _ hr => False.elim (List.not_mem_nil hr)) (by decide)
  | zext m _ =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
    rcases hrel with _ | ⟨hpa, hnil⟩; cases hnil
    dsimp only [vllCoreOp, vllCoreZext] at hop
    cases hok : (arm64Arch.abi.bitWidths.contains m && arm64Arch.abi.bitWidths.contains 32 &&
        (Width.ofBits? m).isSome && (Width.ofBits? 32).isSome && Nat.ble m 32) <;>
      simp only [hok, Bool.false_eq_true, ↓reduceIte] at hop
    · cases hop
    · have hm32 : m ≤ 32 := by simp only [Bool.and_eq_true, Nat.ble_eq] at hok; exact hok.2
      have hmIn : m ∈ arm64Arch.abi.bitWidths := by
        simp only [Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq] at hok
        exact hok.1.1.1.1
      have hP : P (va.setWidth 32, ()) := hwp.2
      cases pa with
      | vec v => exact v.elim
      | imm cv =>
        cases hop; have hEq : cv = va := hpa; subst hEq
        refine Machine.FallsTo.conseq (fallsTo_weaken_rd
          (vllMach_movi_spec (A := arm64Arch) (rd := rd)
            (imm := (cv.setWidth 32).setWidth 64)))
          fun s' ⟨hg, hm⟩ _ => ⟨⟨cv.setWidth 32, hP, hg⟩, hm⟩
      | gpr r =>
        cases hop
        have hcomp : (vllMach arm64Arch).FallsTo arm64Arch.condReads h k
            ([.mov .w64 rd r] ++ [.canonAbi (.bits m) rd])
            ([rd] ++ (rd :: armScratch)) ([] ++ [])
            (maskNone ||| arm64Arch.abi.canonAbiClob (.bits m)) s
            (fun s' => (∃ rv : BitVec 32, P (rv, ()) ∧ s'.gpr rd = rv.setWidth 64) ∧
              s'.mem = s.mem) post :=
          Machine.FallsTo.comp (vllMach_mov_spec arm64Arch_wf (rd := rd) (rs := r))
            fun s1 ⟨hg1, hm1⟩ _ => Machine.FallsTo.conseq
              (vllMach_canonAbi_spec arm64Arch_wf (t := .bits m) (r := rd) (v := va)
                (Or.inr ⟨m, hmIn, rfl⟩) (by
                  have hg1' : s1.gpr rd = s.gpr r := hg1; rw [hg1']; exact hpa))
              fun s2 ⟨hab, hm2⟩ _ => by
                have h2 : s2.gpr rd = va.setWidth 64 := hab.2
                have h3 : (va.setWidth 32).setWidth 64 = va.setWidth 64 := by
                  apply BitVec.eq_of_getLsbD_eq; intro j
                  by_cases hj : j < 64
                  · by_cases hjm : j < m
                    · simp [hj, show j < 32 by omega]
                    · have h0 : va.getLsbD j = false :=
                        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le va.isLt
                          (Nat.pow_le_pow_right (by decide) (by omega)))
                      simp [h0]
                  · simp [hj]
                exact ⟨⟨va.setWidth 32, hP, h2.trans h3.symm⟩, hm2.trans hm1⟩
        exact Machine.FallsTo.weaken hcomp
          (fun r hr => by
            simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
            rcases hr with rfl | rfl | hr'
            · exact List.mem_cons_self
            · exact List.mem_cons_self
            · exact List.mem_cons_of_mem rd (by simpa [armScratch] using hr'))
          (fun _ hr => False.elim (List.not_mem_nil hr))
          (by dsimp only [arm64Arch, arm64Abi, Abi.canonAbiClob]; decide)
  | sext m _ =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
    rcases hrel with _ | ⟨hpa, hnil⟩; cases hnil
    dsimp only [vllCoreOp, vllCoreSext, withWidth, vllCoreSextW] at hop
    cases hw1 : (Width.ofBits? m).isSome <;> simp only [hw1, Bool.false_eq_true, ↓reduceIte] at hop
    · cases hop
    · cases hok : (arm64Arch.abi.bitWidths.contains m && arm64Arch.abi.bitWidths.contains 32 &&
          Nat.ble 1 m && Nat.ble m 32) <;> simp only [hok, Bool.false_eq_true, ↓reduceIte] at hop
      · cases hop
      · have hm : m = 8 ∨ m = 16 ∨ m = 32 := by
          simp only [Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq, List.mem_cons,
            List.not_mem_nil, or_false, Nat.ble_eq] at hok
          rcases hok.1.1.1 with rfl | rfl | rfl | rfl <;> omega
        have hP : P (va.signExtend 32, ()) := hwp.2
        cases pa with
        | vec v => exact v.elim
        | imm cv =>
          cases hop; have hEq : cv = va := hpa; subst hEq
          refine Machine.FallsTo.conseq (fallsTo_weaken_rd
            (vllMach_movi_spec (A := arm64Arch) (rd := rd)
              (imm := (cv.signExtend 32).setWidth 64)))
            fun s' ⟨hg, hm'⟩ _ => ⟨⟨cv.signExtend 32, hP, hg⟩, hm'⟩
        | gpr r =>
          cases hop
          have hr : (s.gpr r).setWidth m = va := hpa.2
          have hcomp : (vllMach arm64Arch).FallsTo arm64Arch.condReads h k
              ([.alu .shl .w32 rd r (.imm (BitVec.ofNat 64 (32 - m))) false] ++
                [.alu .ashr .w32 rd rd (.imm (BitVec.ofNat 64 (32 - m))) false])
              ([rd] ++ [rd]) ([] ++ [])
              (arm64Arch.aluClob .shl false ||| arm64Arch.aluClob .ashr false) s
              (fun s' => (∃ rv : BitVec 32, P (rv, ()) ∧ s'.gpr rd = rv.setWidth 64) ∧
                s'.mem = s.mem) post :=
            Machine.FallsTo.comp
              (vllMach_alu_spec arm64Arch_wf (op := .shl) (w := .w32) (rd := rd) (lhs := r)
                (rhs := .imm (BitVec.ofNat 64 (32 - m))) (sf := false))
              fun s1 ⟨hg1, _, _, hm1⟩ _ => Machine.FallsTo.conseq
                (vllMach_alu_spec arm64Arch_wf (op := .ashr) (w := .w32) (rd := rd) (lhs := rd)
                  (rhs := .imm (BitVec.ofNat 64 (32 - m))) (sf := false))
                fun s2 ⟨hg2, _, _, hm2⟩ _ => by
                  have h2 : s2.gpr rd = (va.signExtend 32).setWidth 64 := by
                    rw [hg2, hg1]; dsimp only [arm64Arch, writeSubZeroExtend, CoreAlu.eval,
                      Src.evalW, Src.eval, Width.bits]
                    rw [setWidth_setWidth_self64 (by decide), sext32_shl_ashr hm, hr]
                  exact ⟨⟨va.signExtend 32, hP, h2⟩, hm2.trans hm1⟩
          exact Machine.FallsTo.weaken hcomp
            (fun r hr => by
              simp only [List.mem_append, List.mem_singleton] at hr
              rcases hr with rfl | rfl <;> exact List.mem_cons_self)
            (fun _ hr => False.elim (List.not_mem_nil hr)) (by decide)
  | trunc m _ =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
    rcases hrel with _ | ⟨hpa, hnil⟩; cases hnil
    dsimp only [vllCoreOp, vllCoreTrunc, withWidth, vllCoreTruncW] at hop
    cases hw1 : (Width.ofBits? m).isSome <;> simp only [hw1, Bool.false_eq_true, ↓reduceIte] at hop
    · cases hop
    · cases hok : (arm64Arch.abi.bitWidths.contains m && arm64Arch.abi.bitWidths.contains 32 &&
          Nat.ble 32 m) <;> simp only [hok, Bool.false_eq_true, ↓reduceIte] at hop
      · cases hop
      · have h32m : 32 ≤ m := by simp only [Bool.and_eq_true, Nat.ble_eq] at hok; exact hok.2
        have hP : P (va.setWidth 32, ()) := hwp.2
        cases pa with
        | vec v => exact v.elim
        | imm cv =>
          cases hop; have hEq : cv = va := hpa; subst hEq
          refine Machine.FallsTo.conseq (fallsTo_weaken_rd
            (vllMach_movi_spec (A := arm64Arch) (rd := rd)
              (imm := (cv.setWidth 32).setWidth 64)))
            fun s' ⟨hg, hm⟩ _ => ⟨⟨cv.setWidth 32, hP, hg⟩, hm⟩
        | gpr r =>
          cases hop
          have hr : (s.gpr r).setWidth m = va := hpa.2
          refine Machine.FallsTo.conseq (fallsTo_weaken_rd
            (vllMach_movW_spec arm64Arch_wf (w := .w32) (rd := rd) (rs := r)))
            fun s' ⟨hg, _, hm⟩ _ => by
              dsimp only [Width.bits] at hg
              rw [show (s.gpr r).setWidth 32 = va.setWidth 32 by
                rw [← hr, BitVec.setWidth_setWidth_of_le _ h32m]] at hg
              exact ⟨⟨va.setWidth 32, hP, hg⟩, hm⟩
  | ofBool _ =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
    rcases hrel with _ | ⟨hpa, hnil⟩; cases hnil
    have h32b : BitVec.ofNat 64 va.toNat = (BitVec.ofNat 32 va.toNat).setWidth 64 := by
      cases va <;> rfl
    cases pa with
    | vec v => exact v.elim
    | imm b =>
      cases hop; have hEq : b = va := hpa; subst hEq
      refine Machine.FallsTo.conseq (fallsTo_weaken_rd
        (vllMach_movi_spec (A := arm64Arch) (rd := rd) (imm := BitVec.ofNat 64 b.toNat)))
        fun s' ⟨hg, hm⟩ _ => ⟨⟨BitVec.ofNat 32 b.toNat, hwp, hg.trans h32b⟩, hm⟩
    | gpr r =>
      cases hop
      have hcomp : (vllMach arm64Arch).FallsTo arm64Arch.condReads h k
          ([.mov .w64 rd r] ++ [.canonAbi .bool rd])
          ([rd] ++ (rd :: armScratch)) ([] ++ [])
          (maskNone ||| arm64Arch.abi.canonAbiClob .bool) s
          (fun s' => (∃ rv : BitVec 32, P (rv, ()) ∧ s'.gpr rd = rv.setWidth 64) ∧
            s'.mem = s.mem) post :=
        Machine.FallsTo.comp (vllMach_mov_spec arm64Arch_wf (rd := rd) (rs := r))
          fun s1 ⟨hg1, hm1⟩ _ => Machine.FallsTo.conseq
            (vllMach_canonAbi_spec arm64Arch_wf (t := .bool) (r := rd) (Or.inl rfl)
              (by have hg1' : s1.gpr rd = s.gpr r := hg1; rw [hg1']; exact hpa))
            fun s2 ⟨hab, hm2⟩ _ => ⟨⟨BitVec.ofNat 32 va.toNat, hwp, hab.trans h32b⟩, hm2.trans hm1⟩
      exact Machine.FallsTo.weaken hcomp
        (fun r hr => by
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | hr'
          · exact List.mem_cons_self
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem rd (by simpa [armScratch] using hr'))
        (fun _ hr => False.elim (List.not_mem_nil hr)) (by decide)
    | flag cf =>
      cases hop
      have hcomp : (vllMach arm64Arch).FallsTo arm64Arch.condReads h k
          ([.setcc rd cf] ++ [.canonAbi .bool rd])
          ([rd] ++ (rd :: armScratch)) ([] ++ [])
          (maskNone ||| arm64Arch.abi.canonAbiClob .bool) s
          (fun s' => (∃ rv : BitVec 32, P (rv, ()) ∧ s'.gpr rd = rv.setWidth 64) ∧
            s'.mem = s.mem) post :=
        Machine.FallsTo.comp
          (vllMach_setcc_spec arm64Arch_wf (rd := rd) (c := cf))
          fun s1 ⟨hg1, hm1⟩ _ => Machine.FallsTo.conseq
            (vllMach_canonAbi_spec arm64Arch_wf (t := .bool) (r := rd) (Or.inl rfl)
              (by rw [hpa] at hg1; exact hg1))
            fun s2 ⟨hab, hm2⟩ _ => ⟨⟨BitVec.ofNat 32 va.toNat, hwp, hab.trans h32b⟩, hm2.trans hm1⟩
      exact Machine.FallsTo.weaken hcomp
        (fun r hr => by
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | hr'
          · exact List.mem_cons_self
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem rd (by simpa [armScratch] using hr'))
        (fun _ hr => False.elim (List.not_mem_nil hr)) (by decide)
  | cmp _ t _ hm => cases t <;> cases hm
  | _ => cases hop

end LeanQbe.T.Arm64
