module

public import LeanQbe.T.Arm64.IselNarrow
public import LeanQbe.T.Arm64.IselShiftLemmas
public import LeanQbe.T.Arm64.IselLemmas3
import LeanQbe.T.Arm64.IselFlagHooksLemmas
import Kraken.AArch64.Parser

/-!
# Arm64 Rank-9 Narrow Compare & Fused Load-Compare Proofs (`IselNarrowLemmas`)

Verifies `armMach.FallsTo` simulation, `FlagCmpOk`, label-freedom, and `ParserChecks` for:
* `armCmpZextOp`: zero-provenance `8`/`16`-bit compare eliding `UBFM #0, #7`/`#15`.
* `armCmpZeroZextJcc`: 1-instruction `CBZ`/`CBNZ w_x, l` under `AbiGprHolds`.
* `armCmpMem` & `armCmpMemFlagsOut`: `GprTarget.cmpMem_spec` and `cmpMem_flags_spec`
  (`LDRSB`/`LDRSH`/`LDRB`/`LDRH`/`LDR` + `CMP`, plus the reversed `pb - mem` swapped-condition
  form `armCmpMemSwapSeq`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open LeanQbe.T

/-! ## 1. Shared `armCmpSeqFinish` & Arithmetic Helpers -/

theorem setWidth32_eq_iff {n : Nat} (hn : n ≤ 32) (a b : BitVec n) :
    (a.setWidth 32 == b.setWidth 32) = (a == b) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  constructor
  · intro h
    have h' := congrArg (BitVec.setWidth n) h
    rwa [BitVec.setWidth_setWidth_of_le _ hn, BitVec.setWidth_setWidth_of_le _ hn,
      BitVec.setWidth_eq, BitVec.setWidth_eq] at h'
  · rintro rfl; rfl

private theorem armCmpSeqFinish_wp [Host] {cmpCode : List Instr} {cond : ArmCond}
    {dst : PDst Reg Empty ArmCond .bool} {c : List Instr} {clob : FlagMask}
    {res : Bool} {s : MachineData} {fk : MachineData → Prop}
    (hcmp : _root_.Program.wp (emitClean cmpCode) (fun sx =>
      cond.interp sx.status = res ∧ fk sx ∧ sx.dmem = s.dmem ∧
      armMach.Frame armCondReads s sx armScratch [] maskNZCV) (fun _ _ => False) s)
    (hfk : ∀ sx sy : MachineData, fk sx → sy.status = sx.status → fk sy)
    (hfin : armCmpSeqFinish cmpCode cond dst = some (c, clob)) :
    _root_.Program.wp (emitClean c) (fun s' =>
      armMach.PDstHolds s' .bool dst res ∧
      (∀ rd, dst = .gpr rd → AbiGprHolds (armMach.getGpr s' rd) .bool res) ∧
      fk s' ∧ armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (dst.gprs ++ armScratch) [] clob)
      (fun _ _ => False) s := by
  cases dst with
  | vec v => exact v.elim
  | flag cf =>
    dsimp only [armCmpSeqFinish] at hfin; split at hfin
    · rename_i heq; simp only [beq_iff_eq] at heq; subst heq
      rcases Option.some.inj hfin with ⟨rfl, rfl⟩
      refine armWp_mono hcmp ?_; rintro sx ⟨hcc, hfx, hdm, hfr⟩
      exact ⟨by simpa [Machine.PDstHolds, Machine.evalCond] using hcc,
        (fun _ h => nomatch h), hfx, hdm, hfr⟩
    · cases hfin
  | gpr r => cases r with
    | SP => cases hfin
    | reg d =>
      rcases Option.some.inj hfin with ⟨rfl, rfl⟩
      rw [emitClean_append, emitClean_cons, emitClean_nil]
      refine armWp_append hcmp ?_; rintro sx ⟨hcc, hfx, hdm, hfr⟩
      refine armWp_mono (armCset64_wp d cond sx) ?_; rintro sy rfl
      have habi : AbiGprHolds (armMach.getGpr (wr sx d
          (BitVec.ofNat 64 (cond.interp sx.status).toNat)) (.reg d)) .bool res := by
        simp only [AbiGprHolds, get_wr_same, hcc]
      refine ⟨habi.toGprHolds, (fun _ h => by cases h; exact habi),
        hfk sx (wr sx d _) hfx rfl, hdm, armFrame_nzcv fun r hr => ?_⟩
      · have hne : r ≠ .reg d ∧ r ∉ armScratch :=
          ⟨fun e => hr (e ▸ List.mem_cons_self), fun hm => hr (List.mem_cons_of_mem _ hm)⟩
        rw [get_wr_of_ne sx d _ r hne.1]; exact hfr.1 r hne.2

private theorem cmp_subword_signed_32 {m : Nat} (hm : m = 8 ∨ m = 16) (o : CmpOp)
    (x y : BitVec m) :
    o.evalBits (x.signExtend 32) (y.signExtend 32) = o.evalBits x y := by
  by_cases hs : armIsSignedCmp o = true
  · exact cmp_subword_signed hm o hs x y
  · have hle : m ≤ 32 := by rcases hm with rfl | rfl <;> decide
    have hmsb : ∀ z : BitVec m, (z.signExtend 32).msb = z.msb := fun z => by
      rw [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_signExtend]
      have hz : z.msb = z.getLsbD (m - 1) := by
        rcases hm with rfl | rfl <;> exact BitVec.msb_eq_getLsbD_last z
      rw [hz]; rcases hm with rfl | rfl <;> simp
    have hseNat : ∀ z : BitVec m,
        (z.signExtend 32).toNat =
          if z.msb then 2 ^ 32 - 2 ^ m + z.toNat else z.toNat := fun z => by
      have hltz := z.isLt
      have hlt32 := (z.signExtend 32).isLt
      have hti := BitVec.toInt_signExtend_of_le (x := z) hle
      rw [BitVec.toInt_eq_msb_cond, BitVec.toInt_eq_msb_cond, hmsb z] at hti
      cases hz : z.msb <;> simp only [hz, ↓reduceIte, Bool.false_eq_true] at hti ⊢ <;>
        rcases hm with rfl | rfl <;> omega
    have hmle : ∀ z : BitVec m, z.msb = true ↔ 2 ^ (m - 1) ≤ z.toNat := fun z => by
      rw [BitVec.msb_eq_decide, decide_eq_true_eq]
    have hult : ∀ a b : BitVec m,
        (a.signExtend 32).ult (b.signExtend 32) = a.ult b := fun a b => by
      have ha := a.isLt; have hb := b.isLt
      simp only [BitVec.ult, hseNat]
      cases ha' : a.msb <;> cases hb' : b.msb
      · simp only [Bool.false_eq_true, ↓reduceIte]
      · have ha2 : ¬(2 ^ (m - 1) ≤ a.toNat) := fun h => by
          have := (hmle a).mpr h; rw [ha'] at this; cases this
        have hb2 : 2 ^ (m - 1) ≤ b.toNat := (hmle b).mp hb'
        rw [Bool.eq_iff_iff]; simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq]
        rcases hm with rfl | rfl <;>
          simp only [Nat.reduceSub, Nat.reducePow] at ha2 hb2 <;> omega
      · have ha2 : 2 ^ (m - 1) ≤ a.toNat := (hmle a).mp ha'
        have hb2 : ¬(2 ^ (m - 1) ≤ b.toNat) := fun h => by
          have := (hmle b).mpr h; rw [hb'] at this; cases this
        rw [Bool.eq_iff_iff]; simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq]
        rcases hm with rfl | rfl <;>
          simp only [Nat.reduceSub, Nat.reducePow] at ha2 hb2 <;> omega
      · have ha2 : 2 ^ (m - 1) ≤ a.toNat := (hmle a).mp ha'
        have hb2 : 2 ^ (m - 1) ≤ b.toNat := (hmle b).mp hb'
        rw [Bool.eq_iff_iff]; simp only [↓reduceIte, decide_eq_true_eq]
        rcases hm with rfl | rfl <;>
          simp only [Nat.reduceSub, Nat.reducePow] at ha2 hb2 <;> omega
    have heq : (x.signExtend 32 = y.signExtend 32) ↔ x = y := by
      refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
      have h' := congrArg (BitVec.setWidth m) h
      simpa only [setWidth_signExtend_self hle] using h'
    have hule : ∀ a b : BitVec m,
        (a.signExtend 32).ule (b.signExtend 32) = a.ule b := fun a b => by
      have ha := a.isLt; have hb := b.isLt
      simp only [BitVec.ule, hseNat]
      cases ha' : a.msb <;> cases hb' : b.msb
      · simp only [Bool.false_eq_true, ↓reduceIte]
      · have ha2 : ¬(2 ^ (m - 1) ≤ a.toNat) := fun h => by
          have := (hmle a).mpr h; rw [ha'] at this; cases this
        have hb2 : 2 ^ (m - 1) ≤ b.toNat := (hmle b).mp hb'
        rw [Bool.eq_iff_iff]; simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq]
        rcases hm with rfl | rfl <;>
          simp only [Nat.reduceSub, Nat.reducePow] at ha2 hb2 <;> omega
      · have ha2 : 2 ^ (m - 1) ≤ a.toNat := (hmle a).mp ha'
        have hb2 : ¬(2 ^ (m - 1) ≤ b.toNat) := fun h => by
          have := (hmle b).mpr h; rw [hb'] at this; cases this
        rw [Bool.eq_iff_iff]; simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq]
        rcases hm with rfl | rfl <;>
          simp only [Nat.reduceSub, Nat.reducePow] at ha2 hb2 <;> omega
      · have ha2 : 2 ^ (m - 1) ≤ a.toNat := (hmle a).mp ha'
        have hb2 : 2 ^ (m - 1) ≤ b.toNat := (hmle b).mp hb'
        rw [Bool.eq_iff_iff]; simp only [↓reduceIte, decide_eq_true_eq]
        rcases hm with rfl | rfl <;>
          simp only [Nat.reduceSub, Nat.reducePow] at ha2 hb2 <;> omega
    cases o with
    | eq => simp only [CmpOp.evalBits]; rw [Bool.eq_iff_iff]; simp [heq]
    | ne => simp only [CmpOp.evalBits]; rw [Bool.eq_iff_iff]; simp [heq]
    | ult => exact hult x y
    | ule => exact hule x y
    | ugt => simpa [CmpOp.evalBits] using hult y x
    | uge => simpa [CmpOp.evalBits] using hule y x
    | slt | sle | sgt | sge => exact absurd (by rfl : armIsSignedCmp _ = true) hs

/-! ## 2. Zero-Provenance Narrow Compare (`armCmpZextOp`, `armCmpZeroZextJcc`) -/

/-- Label-freedom for `armCmpZextOp`. -/
theorem armCmpZextOp_noLab {o : CmpOp} {n : Nat} {az bz : Bool}
    {pa pb : PArg Reg Empty ArmCond (.bits n)} {dst : PDst Reg Empty ArmCond .bool}
    {c : List Directive} {clob : FlagMask}
    (hc : armCmpZextOp o n az bz pa pb dst = some (c, clob)) (l : Sym) :
    Kraken.Directive.label l ∉ c :=
  emitCleanPair_noLab hc l

theorem armAbi32 {n : Nat} (_hn : n ≤ 32) {s : MachineData} {rx : XReg} {v : BitVec n}
    (h : AbiGprHolds (armMach.getGpr s (.reg rx)) (.bits n) v) :
    (s.regs.getXReg rx).toBitVec.setWidth 32 = v.setWidth 32 := by
  have h1 := h.2
  simp only [get_reg] at h1
  rw [h1, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)]

/-- `FallsTo` specification for `armCmpZextOp` under `AbiGprHolds` provenance (`az`/`bz`). -/
theorem armCmpZextOp_spec {h : Host} {k : Nat} {o : CmpOp} {n : Nat} {az bz : Bool}
    {pa pb : PArg Reg Empty ArmCond (.bits n)} {dst : PDst Reg Empty ArmCond .bool}
    {c : List Directive} {clob : FlagMask} {va vb : BitVec n} {s : MachineData}
    {post : MachineState → Prop}
    (hc_in : armCmpZextOp o n az bz pa pb dst = some (c, clob))
    (hargs : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ armScratch)
    (hd : ∀ r ∈ dst.gprs, r ∉ armScratch)
    (hpa : if az then ∃ rx, pa = .gpr rx ∧ AbiGprHolds (armMach.getGpr s rx) (.bits n) va
           else armMach.PArgHolds s (.bits n) pa va)
    (hpb : if bz then ∃ ry, pb = .gpr ry ∧ AbiGprHolds (armMach.getGpr s ry) (.bits n) vb
           else armMach.PArgHolds s (.bits n) pb vb) :
    armMach.FallsTo armCondReads h k c (dst.gprs ++ armScratch) [] clob s
      (fun s' => armMach.PDstHolds s' .bool dst (o.evalBits va vb) ∧
        armMach.mem s' = armMach.mem s) post := by
  letI := h
  obtain ⟨ci, hc, rfl⟩ := emitCleanPair_eq_some.mp hc_in
  have hga : ∀ r ∈ pa.gprs, r ∉ armScratch := fun r hr => hargs r (List.mem_append_left _ hr)
  have hgb : ∀ r ∈ pb.gprs, r ∉ armScratch := fun r hr => hargs r (List.mem_append_right _ hr)
  have hpa0 : armMach.PArgHolds s (.bits n) pa va := by
    cases az
    · exact hpa
    · rcases hpa with ⟨rx, rfl, ha⟩; exact ha.toGprHolds
  have hpb0 : armMach.PArgHolds s (.bits n) pb vb := by
    cases bz
    · exact hpb
    · rcases hpb with ⟨ry, rfl, hb⟩; exact hb.toGprHolds
  have fallback : armCmpOpIns o n pa pb dst = some (ci, clob) →
      armMach.FallsTo armCondReads h k (emitClean ci) (dst.gprs ++ armScratch) [] clob s
        (fun s' => armMach.PDstHolds s' .bool dst (o.evalBits va vb) ∧
          armMach.mem s' = armMach.mem s) post := fun hf => by
    have hd' : ∀ r ∈ tupDstGprs (ts := [.bool]) (dst, ()), r ∉ armScratch := by
      simpa [tupDstGprs] using hd
    refine armFallsTo_of_wp (armWp_mono (armCmpOp_wp o pa pb dst hf hga hgb hd' hpa0 hpb0) ?_)
    rintro s' ⟨hpd, _, hdm, hfr⟩
    rw [show tupDstGprs (ts := [.bool]) (dst, ()) = dst.gprs by simp [tupDstGprs]] at hfr
    exact ⟨⟨hpd, hdm⟩, hfr⟩
  dsimp only [armCmpZextOpIns] at hc
  by_cases hcond : ((n == 8 || n == 16) && !armIsSignedCmp o) = true
  · simp only [hcond, ↓reduceIte] at hc
    have h816 : n = 8 ∨ n = 16 := by
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hcond; exact hcond.1
    have hsgn : armIsSignedCmp o = false := by
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond; exact hcond.2
    have hn32 : n ≤ 32 := by rcases h816 with rfl | rfl <;> decide
    cases pa with
    | vec v => exact v.elim
    | imm ca => cases pb with
      | vec v => exact v.elim
      | imm _ => exact fallback hc
      | gpr r2 => cases r2 with
        | SP => exact fallback hc
        | reg rb =>
          cases bz
          · exact fallback hc
          · simp only [↓reduceIte] at hc hpb
            rcases hpb with ⟨ry, hry, hbi⟩
            have hry' : ry = .reg rb := (PArg.gpr.inj hry).symm
            subst hry'
            have hrb32 := armAbi32 hn32 hbi
            rw [show ca = va from hpa0] at hc
            have heval : o.swap.evalBits (vb.setWidth 32) (va.setWidth 32) = o.evalBits va vb := by
              rw [cmp_subword_unsigned h816 o.swap
                (by cases o <;> first | exact absurd hsgn (by decide) | rfl)
                vb va, CmpOp.swap_evalBits]
            cases hci : armCmpImmIns? .W32 rb (va.setWidth 32) with
            | some cmp =>
              simp only [hci] at hc
              refine armFallsTo_of_wp (armWp_mono (armCmpSeqFinish_wp
                (res := o.evalBits va vb) (fk := fun _ => True) ?_ (fun _ _ h _ => h) hc) ?_)
              · refine armWp_mono (armCmpImm_wp (Or.inl rfl) .W32 rfl rb (va.setWidth 32) hci s) ?_
                rintro sx ⟨hst, hdm, hfr⟩
                rw [hrb32] at hst
                exact ⟨by rw [hst, armCmpCond_subs (Or.inl rfl), heval], trivial, hdm, hfr⟩
              · rintro s' ⟨hpd, _, _, hdm, hfr⟩; exact ⟨⟨hpd, hdm⟩, hfr⟩
            | none =>
              simp only [hci] at hc
              refine armFallsTo_of_wp (armWp_mono (armCmpSeqFinish_wp
                (res := o.evalBits va vb) (fk := fun _ => True) ?_ (fun _ _ h _ => h) hc) ?_)
              · rw [emitClean_append, emitClean_cons, emitClean_nil]
                refine armWp_append (armMovImm_wp .X16 ((va.setWidth 32).setWidth 64) s) ?_
                rintro s₁ rfl
                have hfr₁ :=
                  frame_wr (s := s) .X16 ((va.setWidth 32).setWidth 64) x16_mem_scratch maskNone
                have hrb' : (s.regs.getXReg rb).toBitVec.setWidth 32 = vb.setWidth 32 := hrb32
                have hne : rb ≠ .X16 :=
                  fun e => hgb (.reg rb) (by simp) (e ▸ x16_mem_scratch)
                have hev2 : o.evalBits (va.setWidth 32) (vb.setWidth 32) = o.evalBits va vb :=
                  cmp_subword_unsigned h816 o hsgn va vb
                refine armWp_mono (armStatusScratch_after (s := s)
                  (armDirFallsTo_wp fun {_} p next jmp Q hk => by
                    simp only [t_step_simp, Reg64s.setRegOrZr_xzr, Int64.toInt_zero,
                      Int.toNat_zero, BitVec.shiftLeft_zero, RegWidth.bits, MemWidth.bits,
                      Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec,
                      BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq,
                      Reg64s.getXReg_setXReg_of_ne _ _ _ _ hne.symm, hrb']
                    exact hk _ rfl) rfl hfr₁) ?_
                rintro s₂ ⟨_, hst₂, hdm₂, hfr₂⟩
                exact ⟨by rw [hst₂, armCmpCond_subs (Or.inl rfl), hev2], trivial, hdm₂, hfr₂⟩
              · rintro s' ⟨hpd, _, _, hdm, hfr⟩; exact ⟨⟨hpd, hdm⟩, hfr⟩
    | gpr r1 => cases r1 with
      | SP => exact fallback hc
      | reg ra => cases pb with
        | vec v => exact v.elim
        | imm cb =>
          cases az
          · exact fallback hc
          · simp only [↓reduceIte] at hc hpa
            rcases hpa with ⟨rx, hrx, hai⟩
            have hrx' : rx = .reg ra := (PArg.gpr.inj hrx).symm
            subst hrx'
            have hra32 := armAbi32 hn32 hai
            rw [show cb = vb from hpb0] at hc
            have heval : o.evalBits (va.setWidth 32) (vb.setWidth 32) = o.evalBits va vb :=
              cmp_subword_unsigned h816 o hsgn va vb
            refine armFallsTo_of_wp (armWp_mono (armCmpSeqFinish_wp (res := o.evalBits va vb)
              (fk := fun _ => True) ?_ (fun _ _ h _ => h) hc) ?_)
            · dsimp only [armCmpZextRegImm32]
              cases hci : armCmpImmIns? .W32 ra (vb.setWidth 32) with
              | some cmp =>
                dsimp only
                refine armWp_mono (armCmpImm_wp (Or.inl rfl) .W32 rfl ra (vb.setWidth 32) hci s) ?_
                rintro sx ⟨hst, hdm, hfr⟩
                rw [hra32] at hst
                exact ⟨by rw [hst, armCmpCond_subs (Or.inl rfl), heval], trivial, hdm, hfr⟩
              | none =>
                dsimp only
                rw [emitClean_append, emitClean_cons, emitClean_nil]
                refine armWp_append (armMovImm_wp .X17 ((vb.setWidth 32).setWidth 64) s) ?_
                rintro s₁ rfl
                have hfr₁ :=
                  frame_wr (s := s) .X17 ((vb.setWidth 32).setWidth 64) x17_mem_scratch maskNone
                have hne : ra ≠ .X17 :=
                  fun e => hga (.reg ra) (by simp) (e ▸ x17_mem_scratch)
                refine armWp_mono (armStatusScratch_after (s := s)
                  (armDirFallsTo_wp fun {_} p next jmp Q hk => by
                    simp only [t_step_simp, Reg64s.setRegOrZr_xzr, Int64.toInt_zero,
                      Int.toNat_zero, BitVec.shiftLeft_zero, RegWidth.bits, MemWidth.bits,
                      Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec,
                      BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq,
                      Reg64s.getXReg_setXReg_of_ne _ _ _ _ hne.symm, hra32]
                    exact hk _ rfl) rfl hfr₁) ?_
                rintro s₂ ⟨_, hst₂, hdm₂, hfr₂⟩
                exact ⟨by rw [hst₂, armCmpCond_subs (Or.inl rfl), heval], trivial, hdm₂, hfr₂⟩
            · rintro s' ⟨hpd, _, _, hdm, hfr⟩; exact ⟨⟨hpd, hdm⟩, hfr⟩
        | gpr r2 => cases r2 with
          | SP => exact fallback hc
          | reg rb =>
            by_cases hboth : az && bz = true
            · have haz : az = true := by simp_all
              have hbz : bz = true := by simp_all
              subst haz hbz
              simp only [Bool.and_self, ↓reduceIte] at hc hpa hpb
              rcases hpa with ⟨rx, hrx, hai⟩; rcases hpb with ⟨ry, hry, hbi⟩
              cases PArg.gpr.inj hrx; cases PArg.gpr.inj hry
              have hra32 := armAbi32 hn32 hai
              have hrb32 := armAbi32 hn32 hbi
              have heval : o.evalBits (va.setWidth 32) (vb.setWidth 32) = o.evalBits va vb :=
                cmp_subword_unsigned h816 o hsgn va vb
              refine armFallsTo_of_wp (armWp_mono (armCmpSeqFinish_wp (res := o.evalBits va vb)
                (fk := fun _ => True) ?_ (fun _ _ h _ => h) hc) ?_)
              · rw [emitClean_cons, emitClean_nil]
                have hfr0 := Machine.Frame.refl (M := armMach) armCondReads s armScratch [] maskNone
                refine armWp_mono (armStatusScratch_after
                  (armDirFallsTo_wp fun {_} p next jmp Q hk => by
                    simp only [t_step_simp, Reg64s.setRegOrZr_xzr, Int64.toInt_zero,
                      Int.toNat_zero, BitVec.shiftLeft_zero, RegWidth.bits, MemWidth.bits,
                      hra32, hrb32]
                    exact hk _ rfl) rfl hfr0) ?_
                rintro s₁ ⟨_, hst₁, hdm₁, hfr₁⟩
                exact ⟨by rw [hst₁, armCmpCond_subs (Or.inl rfl), heval], trivial, hdm₁, hfr₁⟩
              · rintro s' ⟨hpd, _, _, hdm, hfr⟩; exact ⟨⟨hpd, hdm⟩, hfr⟩
            · have hfalse : (az && bz) = false := Bool.eq_false_iff.mpr hboth
              simp only [hfalse, Bool.false_eq_true, ↓reduceIte] at hc
              exact fallback hc
  · have hfalse : ((n == 8 || n == 16) && !armIsSignedCmp o) = false := Bool.eq_false_iff.mpr hcond
    simp only [hfalse, Bool.false_eq_true, ↓reduceIte] at hc
    exact fallback hc

/-- Label-freedom for `armCmpZeroZextJcc`. -/
theorem armCmpZeroZextJcc_noLab {isZext : Bool} {co : CmpOp} {n : Nat} {r : Reg} {l : Sym}
    {c : List Directive} {clob : FlagMask}
    (hc : armCmpZeroZextJcc isZext co n r l = some (c, clob)) (lab : Sym) :
    Kraken.Directive.label lab ∉ c :=
  emitCleanPair_noLab hc lab

/-! ## 3. Fused Memory-Operand Compare (`armCmpMem`) Specification -/

/-- Label-freedom for `armCmpMem`. -/
theorem armCmpMem_noLab {o : CmpOp} {n : Nat} {a : AddrArg Reg}
    {pb : PArg Reg Empty ArmCond (.bits n)} {dst : PDst Reg Empty ArmCond .bool}
    {c : List Directive} {clob : FlagMask}
    (hc : armCmpMem o n a pb dst = some (c, clob)) (l : Sym) :
    Kraken.Directive.label l ∉ c :=
  emitCleanPair_noLab hc l

/-- The swapped-condition form never reports reusable flags (`armCmpMemFlagsOut`). -/
private theorem armCmpMemFlagsOut_swapped {o : CmpOp} {n : Nat}
    {pb : PArg Reg Empty ArmCond (.bits n)} {dst : PDst Reg Empty ArmCond .bool}
    (hsw : armCmpMemSwapped o dst = true) : armCmpMemFlagsOut o n pb dst = none := by
  cases dst with
  | vec v => exact v.elim
  | gpr r => simp [armCmpMemSwapped] at hsw
  | flag cf =>
    simp only [armCmpMemSwapped, Bool.and_eq_true, bne_iff_ne, ne_eq] at hsw
    simp [armCmpMemFlagsOut, hsw.1]

/-- Reversed `SUBS zr, rb, x17` sets `subs (y - x) y x`. -/
private theorem armSubsRev_wp [Host] (w : RegWidth) {rb : XReg} {x y : BitVec w.bits}
    {s s₃ : MachineData}
    (hy : (s₃.regs.getXReg rb).toBitVec.setWidth w.bits = y)
    (hx : (s₃.regs.getXReg .X17).toBitVec.setWidth w.bits = x)
    (hd₃ : s₃.dmem = s.dmem) (hfr₃ : armMach.Frame armCondReads s s₃ armScratch [] maskNone) :
    _root_.Program.wp (emitClean [armIselInsI (.SUBS_s (xzr w) (zr rb w) (sh .X17))])
      (fun sx => sx.status = StatusFlags.subs (y - x) y x ∧ sx.dmem = s.dmem ∧
        armMach.Frame armCondReads s sx armScratch [] maskNZCV) (fun _ _ => False) s₃ := by
  rw [emitClean_cons, emitClean_nil]
  cases w
  all_goals
    refine armWp_mono (armStatusScratch_after (armDirFallsTo_wp fun {_} p next jmp Q hk => by
      simp only [t_step_simp, Reg64s.setRegOrZr_xzr, Int64.toInt_zero, Int.toNat_zero,
        BitVec.shiftLeft_zero, RegWidth.bits, MemWidth.bits, hx, hy]
      exact hk _ rfl) hd₃ hfr₃) ?_
    rintro sx ⟨_, hst, hdm, hfr⟩; exact ⟨hst, hdm, hfr⟩

/-- Reversed compare `pb - x17` (`armCmpMemSwapSeq`) decides `o.evalBits va vb` under
`armCmpCond o.swap` (`o.swap.evalBits vb va = o.evalBits va vb`). -/
private theorem armCmpMemSwapSeq_wp [Host] {o : CmpOp} {n : Nat}
    {pb : PArg Reg Empty ArmCond (.bits n)} {sq : List Instr} {va vb : BitVec n}
    {s s₂ : MachineData}
    (hsq : armCmpMemSwapSeq (armIsSignedCmp o) n pb = some sq)
    (hn : (n = 8 ∨ n = 16) ∨ (n = 32 ∨ n = 64))
    (hgb : ∀ r ∈ pb.gprs, r ∉ armScratch) (hpb : armMach.PArgHolds s (.bits n) pb vb)
    (h17a : n = 8 ∨ n = 16 → (s₂.regs.getXReg .X17).toBitVec.setWidth 32 =
      if armIsSignedCmp o then va.signExtend 32 else va.setWidth 32)
    (h17b : n = 32 ∨ n = 64 → (s₂.regs.getXReg .X17).toBitVec.setWidth n = va)
    (hkeep : ∀ x, x ≠ .X16 → x ≠ .X17 → s₂.regs.getXReg x = s.regs.getXReg x)
    (hdm₂ : s₂.dmem = s.dmem) (hfr₂ : armMach.Frame armCondReads s s₂ armScratch [] maskNone) :
    _root_.Program.wp (emitClean sq) (fun sx =>
      (armCmpCond o.swap).interp sx.status = o.evalBits va vb ∧ sx.dmem = s.dmem ∧
      armMach.Frame armCondReads s sx armScratch [] maskNZCV) (fun _ _ => False) s₂ := by
  generalize hsg : armIsSignedCmp o = sgn at hsq h17a
  have hev816 : ∀ (_ : n = 8 ∨ n = 16) {st : StatusFlags},
      st = StatusFlags.subs ((if sgn then vb.signExtend 32 else vb.setWidth 32) -
        (if sgn then va.signExtend 32 else va.setWidth 32))
        (if sgn then vb.signExtend 32 else vb.setWidth 32)
        (if sgn then va.signExtend 32 else va.setWidth 32) →
      (armCmpCond o.swap).interp st = o.evalBits va vb := fun hw {st} hst => by
    rw [hst, armCmpCond_subs (Or.inl rfl), CmpOp.swap_evalBits]
    cases sgn
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact cmp_subword_unsigned hw o hsg va vb
    · simp only [↓reduceIte]; exact cmp_subword_signed hw o hsg va vb
  have hev3264 : ∀ (_ : n = 32 ∨ n = 64) {st : StatusFlags},
      st = StatusFlags.subs (vb - va) vb va → (armCmpCond o.swap).interp st = o.evalBits va vb :=
    fun hw {st} hst => by rw [hst, armCmpCond_subs hw, CmpOp.swap_evalBits]
  have hfrX16 : ∀ v, armMach.Frame armCondReads s (wr s₂ .X16 v) armScratch [] maskNone :=
    fun v => armFrame_scratch_trans hfr₂ (frame_wr .X16 v x16_mem_scratch maskNone)
  have h16v : ∀ (v : BitVec 32), ((wr s₂ .X16 (v.setWidth 64)).regs.getXReg .X16).toBitVec.setWidth
      (RegWidth.W32).bits = v := fun v => by
    simp [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
  have h17k : ∀ v m, ((wr s₂ .X16 v).regs.getXReg .X17).toBitVec.setWidth m =
      (s₂.regs.getXReg .X17).toBitVec.setWidth m := fun v m => by
    simp [Reg64s.getXReg_setXReg_of_ne _ _ _ _ (by decide : XReg.X16 ≠ .X17)]
  cases pb with
  | vec v => exact v.elim
  | gpr r => cases r with
    | SP => simp [armCmpMemSwapSeq] at hsq
    | reg rb =>
      have hne : rb ≠ .X16 ∧ rb ≠ .X17 := by
        simpa using ne_of_not_mem_armScratch (hgb (.reg rb) (by simp))
      have hrb : (s₂.regs.getXReg rb).toBitVec.setWidth n = vb := by
        rw [hkeep rb hne.1 hne.2]; simpa [Machine.PArgHolds, GprHolds, get_reg] using hpb.2
      rcases hn with hw | hw
      · have hb : (n == 8 || n == 16) = true := by rcases hw with rfl | rfl <;> rfl
        have hn0 : 0 < n := by rcases hw with rfl | rfl <;> decide
        have hn32 : n ≤ 32 := by rcases hw with rfl | rfl <;> decide
        simp only [armCmpMemSwapSeq, hb, ↓reduceIte, Option.some.injEq] at hsq; subst hsq
        rw [emitClean_cons]
        refine armWp_cons (armExt32_wp sgn hn0 hn32 .X16 rb s₂ vb hrb) ?_
        rintro s₃ rfl
        exact armWp_mono (armSubsRev_wp .W32 (h16v _) ((h17k _ _).trans (h17a hw)) hdm₂
          (hfrX16 _)) fun _ ⟨hst, hdm, hfr⟩ => ⟨hev816 hw hst, hdm, hfr⟩
      · have hb : (n == 8 || n == 16) = false := by rcases hw with rfl | rfl <;> rfl
        simp only [armCmpMemSwapSeq, hb, Bool.false_eq_true, ↓reduceIte,
          Option.some.injEq] at hsq
        subst hsq
        rcases hw with rfl | rfl
        · exact armWp_mono (armSubsRev_wp .W32 hrb (h17b (Or.inl rfl)) hdm₂ hfr₂)
            fun _ ⟨hst, hdm, hfr⟩ => ⟨hev3264 (Or.inl rfl) hst, hdm, hfr⟩
        · exact armWp_mono (armSubsRev_wp .W64 hrb (h17b (Or.inr rfl)) hdm₂ hfr₂)
            fun _ ⟨hst, hdm, hfr⟩ => ⟨hev3264 (Or.inr rfl) hst, hdm, hfr⟩
  | imm cb =>
    rw [show cb = vb from hpb] at hsq
    rcases hn with hw | hw
    · have hb : (n == 8 || n == 16) = true := by rcases hw with rfl | rfl <;> rfl
      simp only [armCmpMemSwapSeq, hb, ↓reduceIte, Option.some.injEq] at hsq; subst hsq
      rw [emitClean_append]
      refine armWp_append (armMovImm_wp .X16
        ((if sgn then vb.signExtend 32 else vb.setWidth 32).setWidth 64) s₂) ?_
      rintro s₃ rfl
      exact armWp_mono (armSubsRev_wp .W32 (h16v _) ((h17k _ _).trans (h17a hw)) hdm₂
        (hfrX16 _)) fun _ ⟨hst, hdm, hfr⟩ => ⟨hev816 hw hst, hdm, hfr⟩
    · have hb : (n == 8 || n == 16) = false := by rcases hw with rfl | rfl <;> rfl
      simp only [armCmpMemSwapSeq, hb, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hsq
      subst hsq
      rw [emitClean_append]
      refine armWp_append (armMovImm_wp .X16 (vb.setWidth 64) s₂) ?_
      rintro s₃ rfl
      rcases hw with rfl | rfl
      · exact armWp_mono (armSubsRev_wp .W32 (y := vb) (x := va) (by simp [BitVec.setWidth_eq])
          ((h17k _ _).trans (h17b (Or.inl rfl))) hdm₂ (hfrX16 _))
          fun _ ⟨hst, hdm, hfr⟩ => ⟨hev3264 (Or.inl rfl) hst, hdm, hfr⟩
      · exact armWp_mono (armSubsRev_wp .W64 (y := vb) (x := va) (by simp [BitVec.setWidth_eq])
          ((h17k _ _).trans (h17b (Or.inr rfl))) hdm₂ (hfrX16 _))
          fun _ ⟨hst, hdm, hfr⟩ => ⟨hev3264 (Or.inr rfl) hst, hdm, hfr⟩

theorem armCmpMem_core_wp [Host] {o : CmpOp} {n : Nat} {a : AddrArg Reg}
    {pb : PArg Reg Empty ArmCond (.bits n)} {dst : PDst Reg Empty ArmCond .bool}
    {ci : List Instr} {clob : FlagMask} {va vb : BitVec n} {s : MachineData}
    (hc : armCmpMemIns o n a pb dst = some (ci, clob))
    (hargs : ∀ r ∈ a.regs ++ pb.gprs, r ∉ armScratch)
    (hload : loadVal (armMach.mem s) (.bits n) (a.eval (armMach.getGpr s)) = some va)
    (hpb : armMach.PArgHolds s (.bits n) pb vb) :
    _root_.Program.wp (emitClean ci) (fun s' =>
      armMach.PDstHolds s' .bool dst (o.evalBits va vb) ∧
      (∀ rd, dst = .gpr rd → AbiGprHolds (armMach.getGpr s' rd) .bool (o.evalBits va vb)) ∧
      (∀ {lf}, armCmpMemFlagsOut o n pb dst = some lf →
        FlagCmpOk armMach armGpr s' (if lf then va else vb) (if lf then vb else va) false) ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (dst.gprs ++ armScratch) [] clob)
      (fun _ _ => False) s := by
  have haregs : ∀ r ∈ a.regs, r ∉ armScratch := fun r hr => hargs r (List.mem_append_left _ hr)
  have hgb : ∀ r ∈ pb.gprs, r ∉ armScratch := fun r hr => hargs r (List.mem_append_right _ hr)
  dsimp only [armCmpMemIns] at hc
  split at hc
  · simp at hc
  · rename_i hn
    replace hn := not_not_eq_true hn
    simp only [List.contains_eq_mem, decide_eq_true_eq] at hn
    have hn_mem := mem_armWidths hn
    have hn64 := mem_armWidths_le_64 hn
    have hn_sc : ∃ scale, armMemScale (.bits n) = some scale := by
      rcases hn_mem with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩
    rcases hn_sc with ⟨scale, hscale⟩
    simp only [bind, Option.bind_some, hscale] at hc
    by_cases hva : armAddrValid scale a = true
    · have hvaf : (!armAddrValid scale a) = false := by simp [hva]
      simp only [hvaf, Bool.false_eq_true, ↓reduceIte] at hc
      let sgn := armIsSignedCmp o
      let rw := armWidthOf n
      have hif_bind : ∀ {α β} (b : Bool) (x y : Option α) (f : α → Option β),
          (if b = true then x.bind f else y.bind f) = (if b = true then x else y).bind f := by
        intro α β b x y f; cases b <;> rfl
      rw [hif_bind] at hc
      have hsetup := armSetupAddr_wp scale a s haregs hva
      generalize armSetupAddrIns scale a = sa at hc hsetup
      rcases sa with ⟨setup, addr⟩
      rcases hsetup with ⟨hnoSp, hwpSetup⟩
      rcases Option.bind_eq_some_iff.mp hc with ⟨ldDir, hldDir, hc'⟩
      dsimp only at hc'
      let lhs32 : BitVec rw.bits :=
        if h : n = 8 ∨ n = 16 then
          have : rw = .W32 := by rcases h with rfl | rfl <;> rfl
          this ▸ (if sgn then va.signExtend 32 else va.setWidth 32)
        else
          have : rw.bits = n := by
            rcases hn_mem with rfl | rfl | rfl | rfl
            · exact absurd (Or.inl rfl) h
            · exact absurd (Or.inr rfl) h
            · decide
            · decide
          this ▸ va
      have hld_wp : _root_.Program.wp (emitClean (setup ++ [ldDir])) (fun s₂ =>
          (s₂.regs.getXReg .X17).toBitVec.setWidth rw.bits = lhs32 ∧
          (∀ x, x ≠ .X16 → x ≠ .X17 → s₂.regs.getXReg x = s.regs.getXReg x) ∧
          s₂.dmem = s.dmem ∧ armMach.Frame armCondReads s s₂ armScratch [] maskNone)
          (fun _ _ => False) s := by
        rw [emitClean_append, emitClean_cons, emitClean_nil]
        refine armWp_append hwpSetup ?_
        rintro s₁ ⟨heval, hx16, hsp₁, hdmem₁, hst₁, hfr₁⟩
        have hload₁ : loadVal s₁.dmem (.bits n) (a.eval (get s)) = some va := by
          simpa [armMach, hdmem₁] using hload
        have hfr₁' : armMach.Frame armCondReads s s₁ armScratch [] maskNone :=
          ⟨fun r hr => hfr₁.1 r (fun hm => hr (List.mem_singleton.mp hm ▸ x16_mem_scratch)),
           hfr₁.2⟩
        cases h816 : ((n == 8 || n == 16) && sgn)
        · simp only [sgn] at h816; dsimp only at hldDir
          rw [h816] at hldDir; simp only [Bool.false_eq_true, ↓reduceIte] at hldDir
          refine armWp_mono (armLoadDir_wp hldDir hnoSp heval hload₁) ?_
          rintro s₂ ⟨w64, rfl, habi⟩
          refine ⟨?_, fun x hx6 hx7 => ?_, hdmem₁, ?_⟩
          · rw [Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec, habi.2]
            rcases hn_mem with rfl | rfl | rfl | rfl
            · have hsgnF : sgn = false := by
                cases hs : sgn
                · rfl
                · simp [sgn, hs] at h816
              simp [lhs32, rw, armWidthOf, hsgnF,
                BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)]
            · have hsgnF : sgn = false := by
                cases hs : sgn
                · rfl
                · simp [sgn, hs] at h816
              simp [lhs32, rw, armWidthOf, hsgnF,
                BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)]
            · simp [lhs32, rw, armWidthOf, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
                BitVec.setWidth_eq]
            · simp [lhs32, rw, armWidthOf, BitVec.setWidth_eq]
          · rw [Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx7.symm]; exact hx16 x hx6
          · exact armFrame_scratch_trans hfr₁' (frame_wr .X17 _ x17_mem_scratch maskNone)
        · simp only [sgn] at h816; dsimp only at hldDir
          rw [h816] at hldDir; simp only [↓reduceIte] at hldDir
          have h816' : n = 8 ∨ n = 16 := by
            simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h816; exact h816.1
          have hsgn' : sgn = true := by
            simp only [Bool.and_eq_true] at h816; exact h816.2
          have hse32 : ∀ {m : Nat} (v : BitVec m),
              (v.signExtend 64).setWidth 32 = v.signExtend 32 := fun v => by
            apply BitVec.eq_of_getLsbD_eq; intro i hi
            simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, decide_eq_true hi,
              decide_eq_true (Nat.lt_trans hi (by decide : 32 < 64)), Bool.true_and]
          refine armWp_mono (armLoadSextDir_wp hldDir hnoSp heval hload₁) ?_
          rintro s₂ rfl
          refine ⟨?_, fun x hx6 hx7 => ?_, hdmem₁, ?_⟩
          · rw [Reg64s.getXReg_setXReg_same, UInt64.toBitVec_ofBitVec]
            rcases h816' with rfl | rfl <;>
              simp [lhs32, rw, armWidthOf, hsgn', hse32 va]
          · rw [Reg64s.getXReg_setXReg_of_ne _ _ _ _ hx7.symm]; exact hx16 x hx6
          · exact armFrame_scratch_trans hfr₁' (frame_wr .X17 _ x17_mem_scratch maskNone)
      have hev_fn : ∀ (sx sy : MachineData),
          (∀ {lf}, armCmpMemFlagsOut o n pb dst = some lf →
            FlagCmpOk armMach armGpr sx (if lf then va else vb) (if lf then vb else va) false) →
          sy.status = sx.status →
          ∀ {lf}, armCmpMemFlagsOut o n pb dst = some lf →
            FlagCmpOk armMach armGpr sy (if lf then va else vb) (if lf then vb else va) false :=
        fun sx sy hfc hsy lf hfl co' cnd' hm hco => by
          simpa [Machine.evalCond, hsy] using hfc hfl co' cnd' hm hco
      have hrw_cases : (n = 8 ∨ n = 16) ∨ (n = 32 ∨ n = 64) := by
        rcases hn_mem with rfl | rfl | rfl | rfl <;> omega
      have hSub3264 : ∀ {sx : MachineData} (hw : n = 32 ∨ n = 64),
          sx.status = StatusFlags.subs (va - vb) va vb →
          (armCmpCond o).interp sx.status = o.evalBits va vb ∧
          FlagCmpOk armMach armGpr sx va vb false := fun hw hst => by
        refine ⟨by rw [hst]; exact armCmpCond_subs hw o va vb, fun co cnd _ hco => ?_⟩
        cases hco; dsimp only [Machine.evalCond, armMach]; rw [hst]
        exact armCmpCond_subs hw co va vb
      have hflTrue : ∀ {pb' : PArg Reg Empty ArmCond (.bits n)} {lf : Bool},
          armCmpMemFlagsOut o n pb' dst = some lf → lf = true := fun {pb'} {lf} hfl => by
        dsimp only [armCmpMemFlagsOut] at hfl
        split at hfl; · cases hfl
        split at hfl; · cases hfl
        · cases pb' with
          | vec v => exact v.elim
          | gpr r => cases r with
            | SP => simp at hfl
            | reg _ => cases dst with
              | vec v => exact v.elim
              | gpr r' => cases r' <;> simp at hfl <;> exact hfl
              | flag cf =>
                by_cases hcf : (cf == armCmpCond o) = true <;> simp [hcf] at hfl
                exact hfl
          | imm _ => cases dst with
            | vec v => exact v.elim
            | gpr r' => cases r' <;> simp at hfl <;> exact hfl
            | flag cf =>
              by_cases hcf : (cf == armCmpCond o) = true <;> simp [hcf] at hfl
              exact hfl
      have hSub816 : ∀ {sx : MachineData} (hw : n = 8 ∨ n = 16),
          sx.status = StatusFlags.subs
            ((if sgn then va.signExtend 32 else va.setWidth 32) -
             (if sgn then vb.signExtend 32 else vb.setWidth 32))
            (if sgn then va.signExtend 32 else va.setWidth 32)
            (if sgn then vb.signExtend 32 else vb.setWidth 32) →
          (armCmpCond o).interp sx.status = o.evalBits va vb ∧
          (∀ {lf}, armCmpMemFlagsOut o n pb dst = some lf →
            FlagCmpOk armMach armGpr sx (if lf then va else vb) (if lf then vb else va) false) := by
        intro sx hw hst
        refine ⟨?_, fun {lf} hfl => ?_⟩
        · rw [hst, armCmpCond_subs (Or.inl rfl)]
          cases hs : sgn
          · simp only [Bool.false_eq_true, ↓reduceIte]
            exact cmp_subword_unsigned hw o hs va vb
          · simp only [↓reduceIte]; exact cmp_subword_signed hw o hs va vb
        · have hsgnT : sgn = true := by
            dsimp only [armCmpMemFlagsOut] at hfl
            split at hfl; · cases hfl
            split at hfl; · cases hfl
            · rename_i hc2
              cases h : armIsSignedCmp o
              · have ht' : (n == 8 || n == 16) = true := by rcases hw with rfl | rfl <;> rfl
                simp [ht', h] at hc2
              · exact h
          obtain rfl := hflTrue hfl
          rw [hsgnT] at hst
          intro co cnd _ hco; cases hco; dsimp only [Machine.evalCond, armMach]; rw [hst]
          exact (armCmpCond_subs (Or.inl rfl) co _ _).trans (cmp_subword_signed_32 hw co va vb)
      by_cases hsw : armCmpMemSwapped o dst = true
      · simp only [hsw, ↓reduceIte] at hc'
        rcases Option.bind_eq_some_iff.mp hc' with ⟨sq, hsq, hfin⟩
        refine armWp_mono (armCmpSeqFinish_wp (res := o.evalBits va vb)
          (fk := fun sx => ∀ {lf}, armCmpMemFlagsOut o n pb dst = some lf →
            FlagCmpOk armMach armGpr sx (if lf then va else vb) (if lf then vb else va) false)
          ?_ hev_fn hfin) fun _ h => h
        rw [emitClean_append]
        refine armWp_append hld_wp ?_
        rintro s₂ ⟨hx17, hkeep, hdmem₂, hfr₂⟩
        refine armWp_mono (armCmpMemSwapSeq_wp (va := va) hsq hrw_cases hgb hpb ?_ ?_ hkeep hdmem₂
          hfr₂) ?_
        · intro hw; rcases hw with rfl | rfl <;> simpa [lhs32, rw, armWidthOf] using hx17
        · intro hw; rcases hw with rfl | rfl <;> simpa [lhs32, rw, armWidthOf] using hx17
        · rintro sx ⟨hcc, hdm, hfr⟩
          exact ⟨hcc, fun hfl => absurd (hfl.symm.trans (armCmpMemFlagsOut_swapped hsw))
            (by simp), hdm, hfr⟩
      simp only [Bool.eq_false_iff.mpr hsw, Bool.false_eq_true, ↓reduceIte] at hc'
      have ⟨cmpSeq, hcmpSeq, hfin⟩ : ∃ cmpSeq,
          (match pb with
            | .gpr (.reg rb) =>
              if n == 8 || n == 16 then
                some [armExt32I sgn n .X16 rb,
                  armIselInsI (.SUBS_s (xzr .W32) (zr .X17 .W32) (sh .X16))]
              else some [armIselInsI (.SUBS_s (xzr rw) (zr .X17 rw) (sh rb))]
            | .imm cb =>
              if n == 8 || n == 16 then
                let c32 := if sgn then cb.signExtend 32 else cb.setWidth 32
                match armCmpImmIns? .W32 .X17 c32 with
                | some cmp => some cmp
                | none => some (armMovImmI .X16 (c32.setWidth 64) ++
                    [armIselInsI (.SUBS_s (xzr .W32) (zr .X17 .W32) (sh .X16))])
              else
                match armCmpImmIns? rw .X17 cb with
                | some cmp => some cmp
                | none => some (armMovImmI .X16 (cb.setWidth 64) ++
                    [armIselInsI (.SUBS_s (xzr rw) (zr .X17 rw) (sh .X16))])
            | .gpr .SP | .vec _ => none) = some cmpSeq ∧
          armCmpSeqFinish (setup ++ [ldDir] ++ cmpSeq) (armCmpCond o) dst = some (ci, clob) := by
        cases pb with
        | vec vr => exact vr.elim
        | gpr r2 => cases r2 with
          | SP => simp at hc'
          | reg rb =>
            by_cases h816p : (n == 8 || n == 16) = true
            · simp only [h816p, ↓reduceIte] at hc' ⊢; exact ⟨_, rfl, hc'⟩
            · simp only [h816p, Bool.false_eq_true, ↓reduceIte] at hc' ⊢; exact ⟨_, rfl, hc'⟩
        | imm cb =>
          dsimp only [sgn, rw] at hc' ⊢
          by_cases h816p : (n == 8 || n == 16) = true
          · simp only [h816p, ↓reduceIte] at hc' ⊢
            cases hci : armCmpImmIns? .W32 .X17
                (if armIsSignedCmp o then cb.signExtend 32 else cb.setWidth 32) with
            | some cmp => simp only [hci] at hc'; exact ⟨cmp, rfl, hc'⟩
            | none => simp only [hci] at hc'; exact ⟨_, rfl, hc'⟩
          · simp only [h816p, Bool.false_eq_true, ↓reduceIte] at hc' ⊢
            cases hci : armCmpImmIns? (armWidthOf n) .X17 cb with
            | some cmp => simp only [hci] at hc'; exact ⟨cmp, rfl, hc'⟩
            | none => simp only [hci] at hc'; exact ⟨_, rfl, hc'⟩
      refine armWp_mono (armCmpSeqFinish_wp (res := o.evalBits va vb)
        (fk := fun sx => ∀ {lf}, armCmpMemFlagsOut o n pb dst = some lf →
          FlagCmpOk armMach armGpr sx (if lf then va else vb) (if lf then vb else va) false)
        ?_ hev_fn hfin) ?_
      · rw [emitClean_append]
        refine armWp_append hld_wp ?_
        rintro s₂ ⟨hx17, hkeep, hdmem₂, hfr₂⟩
        cases pb with
        | vec vr => exact vr.elim
        | gpr r2 => cases r2 with
          | SP => cases hcmpSeq
          | reg rb =>
            have hne : rb ≠ .X16 ∧ rb ≠ .X17 := by
              simpa using ne_of_not_mem_armScratch (hgb (.reg rb) (by simp))
            have hrb' : (s₂.regs.getXReg rb).toBitVec.setWidth n = vb := by
              rw [hkeep rb hne.1 hne.2]; simpa [Machine.PArgHolds, GprHolds, get_reg] using hpb.2
            rcases hrw_cases with h816 | h3264
            · have h816b : (n == 8 || n == 16) = true := by rcases h816 with rfl | rfl <;> rfl
              have hn0 : 0 < n := by rcases h816 with rfl | rfl <;> decide
              have hnw32 : n ≤ 32 := by rcases h816 with rfl | rfl <;> decide
              simp only [h816b, ↓reduceIte, Option.some.injEq] at hcmpSeq; subst hcmpSeq
              have hx17' : (s₂.regs.getXReg .X17).toBitVec.setWidth 32 =
                  if sgn then va.signExtend 32 else va.setWidth 32 := by
                rcases h816 with rfl | rfl <;> simpa [lhs32, rw, armWidthOf] using hx17
              rw [emitClean_cons, emitClean_cons, emitClean_nil]
              refine armWp_cons (armExt32_wp sgn hn0 hnw32 .X16 rb s₂ vb hrb') ?_
              rintro s₃ h3
              have hfr₃ := armFrame_scratch_trans hfr₂
                (h3.symm ▸ frame_wr .X16 _ x16_mem_scratch maskNone)
              have h17_3 : (s₃.regs.getXReg .X17).toBitVec.setWidth 32 =
                  if sgn then va.signExtend 32 else va.setWidth 32 := by
                rw [h3]
                simpa [Reg64s.getXReg_setXReg_of_ne _ _ _ _ (by decide : XReg.X16 ≠ .X17)]
                  using hx17'
              have h16_3 : (s₃.regs.getXReg .X16).toBitVec.setWidth 32 =
                  if sgn then vb.signExtend 32 else vb.setWidth 32 := by
                rw [h3]
                simp [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
              have hdmem₃ : s₃.dmem = s.dmem := by rw [h3]; exact hdmem₂
              refine armWp_mono (armStatusScratch_after (armDirFallsTo_wp fun {_} p next jmp Q hk =>
                by
                  simp only [t_step_simp, Reg64s.setRegOrZr_xzr, Int64.toInt_zero, Int.toNat_zero,
                    BitVec.shiftLeft_zero, RegWidth.bits, MemWidth.bits, h17_3, h16_3]
                  exact hk _ rfl) hdmem₃ hfr₃) ?_
              rintro s₄ ⟨_, hst₄, hdm₄, hfr₄⟩
              obtain ⟨hcc, hfc⟩ := hSub816 h816 hst₄
              exact ⟨hcc, hfc, hdm₄, hfr₄⟩
            · have hnot816 : (n == 8 || n == 16) = false := by rcases h3264 with rfl | rfl <;> rfl
              simp only [hnot816, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hcmpSeq
              subst hcmpSeq
              rw [emitClean_cons, emitClean_nil]
              rcases h3264 with rfl | rfl
              · have hx17' : (s₂.regs.getXReg .X17).toBitVec.setWidth 32 = va := by
                  simpa [lhs32, rw, armWidthOf] using hx17
                refine armWp_mono (armStatusScratch_after
                  (armDirFallsTo_wp fun {_} p next jmp Q hk => by
                    rw [show rw = .W32 by rfl]
                    simp only [t_step_simp, Reg64s.setRegOrZr_xzr, Int64.toInt_zero,
                      Int.toNat_zero, BitVec.shiftLeft_zero, RegWidth.bits, MemWidth.bits,
                      hx17', hrb']
                    exact hk _ rfl) hdmem₂ hfr₂) ?_
                rintro s₃ ⟨_, hst₃, hdm₃, hfr₃⟩
                obtain ⟨hcc, hfc⟩ := hSub3264 (Or.inl rfl) hst₃
                refine ⟨hcc, fun {lf} hfl => ?_, hdm₃, hfr₃⟩
                obtain rfl := hflTrue hfl; exact hfc
              · have hx17' : (s₂.regs.getXReg .X17).toBitVec.setWidth 64 = va := by
                  simpa [lhs32, rw, armWidthOf] using hx17
                refine armWp_mono (armStatusScratch_after
                  (armDirFallsTo_wp fun {_} p next jmp Q hk => by
                    rw [show rw = .W64 by rfl]
                    simp only [t_step_simp, Reg64s.setRegOrZr_xzr, Int64.toInt_zero,
                      Int.toNat_zero, BitVec.shiftLeft_zero, RegWidth.bits, MemWidth.bits,
                      hx17', hrb']
                    exact hk _ rfl) hdmem₂ hfr₂) ?_
                rintro s₃ ⟨_, hst₃, hdm₃, hfr₃⟩
                obtain ⟨hcc, hfc⟩ := hSub3264 (Or.inr rfl) hst₃
                refine ⟨hcc, fun {lf} hfl => ?_, hdm₃, hfr₃⟩
                obtain rfl := hflTrue hfl; exact hfc
        | imm cb =>
          rw [show cb = vb from hpb] at hcmpSeq
          rcases hrw_cases with h816 | h3264
          · have h816b : (n == 8 || n == 16) = true := by rcases h816 with rfl | rfl <;> rfl
            simp only [h816b, ↓reduceIte] at hcmpSeq
            have hx17' : (s₂.regs.getXReg .X17).toBitVec.setWidth 32 =
                if sgn then va.signExtend 32 else va.setWidth 32 := by
              rcases h816 with rfl | rfl <;> simpa [lhs32, rw, armWidthOf] using hx17
            cases hci : armCmpImmIns? .W32 .X17
                (if sgn then vb.signExtend 32 else vb.setWidth 32) with
            | some cmp =>
              rw [hci] at hcmpSeq
              injection hcmpSeq with hcmpSeq; subst hcmpSeq
              refine armWp_mono (armCmpImm_wp (Or.inl rfl) .W32 rfl .X17
                (if sgn then vb.signExtend 32 else vb.setWidth 32) hci s₂) ?_
              rintro s₃ ⟨hst₃, hdm₃, hfr₃⟩
              rw [hx17'] at hst₃
              obtain ⟨hcc, hfc⟩ := hSub816 h816 hst₃
              exact ⟨hcc, hfc, hdm₃.trans hdmem₂, armFrame_nzcv fun r hr =>
                (hfr₃.1 r hr).trans (hfr₂.1 r hr)⟩
            | none =>
              rw [hci] at hcmpSeq
              injection hcmpSeq with hcmpSeq; subst hcmpSeq
              rw [emitClean_append, emitClean_cons, emitClean_nil]
              refine armWp_append (armMovImm_wp .X16
                ((if sgn then vb.signExtend 32 else vb.setWidth 32).setWidth 64) s₂) ?_
              rintro s₃ h3
              have hfr₃ := armFrame_scratch_trans hfr₂
                (h3.symm ▸ frame_wr .X16 _ x16_mem_scratch maskNone)
              have h17_3 : (s₃.regs.getXReg .X17).toBitVec.setWidth 32 =
                  if sgn then va.signExtend 32 else va.setWidth 32 := by
                rw [h3]
                simpa [Reg64s.getXReg_setXReg_of_ne _ _ _ _ (by decide : XReg.X16 ≠ .X17)]
                  using hx17'
              have h16_3 : (s₃.regs.getXReg .X16).toBitVec.setWidth 32 =
                  if sgn then vb.signExtend 32 else vb.setWidth 32 := by
                rw [h3]
                simp [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
              have hdmem₃ : s₃.dmem = s.dmem := by rw [h3]; exact hdmem₂
              refine armWp_mono (armStatusScratch_after (armDirFallsTo_wp fun {_} p next jmp Q hk =>
                by
                  simp only [t_step_simp, Reg64s.setRegOrZr_xzr, Int64.toInt_zero, Int.toNat_zero,
                    BitVec.shiftLeft_zero, RegWidth.bits, MemWidth.bits, h17_3, h16_3]
                  exact hk _ rfl) hdmem₃ hfr₃) ?_
              rintro s₄ ⟨_, hst₄, hdm₄, hfr₄⟩
              obtain ⟨hcc, hfc⟩ := hSub816 h816 hst₄
              exact ⟨hcc, hfc, hdm₄, hfr₄⟩
          · have hnot816 : (n == 8 || n == 16) = false := by rcases h3264 with rfl | rfl <;> rfl
            simp only [hnot816, Bool.false_eq_true, ↓reduceIte] at hcmpSeq
            have hrw_bits : rw.bits = n := by rcases h3264 with rfl | rfl <;> rfl
            have h32rw : n = 32 → rw = .W32 := fun e => by subst e; rfl
            have hx17' : (s₂.regs.getXReg .X17).toBitVec.setWidth n = va := by
              rcases h3264 with rfl | rfl <;> simpa [lhs32, rw, armWidthOf] using hx17
            cases hci : armCmpImmIns? rw .X17 vb with
            | some cmp =>
              simp only [hci, Option.some.injEq] at hcmpSeq; subst hcmpSeq
              refine armWp_mono (armCmpImm_wp h3264 rw hrw_bits .X17 vb hci s₂) ?_
              rintro s₃ ⟨hst₃, hdm₃, hfr₃⟩
              rw [hx17'] at hst₃
              obtain ⟨hcc, hfc⟩ := hSub3264 h3264 hst₃
              refine ⟨hcc, fun {lf} hfl => ?_, hdm₃.trans hdmem₂, armFrame_nzcv fun r hr =>
                (hfr₃.1 r hr).trans (hfr₂.1 r hr)⟩
              obtain rfl := hflTrue hfl; exact hfc
            | none =>
              simp only [hci, Option.some.injEq] at hcmpSeq; subst hcmpSeq
              rw [emitClean_append, emitClean_cons, emitClean_nil]
              refine armWp_append (armMovImm_wp .X16 (vb.setWidth 64) s₂) ?_
              rintro s₃ h3
              have hfr₃ := armFrame_scratch_trans hfr₂
                (h3.symm ▸ frame_wr .X16 _ x16_mem_scratch maskNone)
              have hdmem₃ : s₃.dmem = s.dmem := by rw [h3]; exact hdmem₂
              rcases h3264 with rfl | rfl
              · refine armWp_mono (armStatusScratch_after
                  (armDirFallsTo_wp fun {_} p next jmp Q hk => by
                    have h17' : (s₃.regs.getXReg .X17).toBitVec.setWidth 32 = va := by
                      rw [h3, Reg64s.getXReg_setXReg_of_ne _ _ _ _ (by decide : XReg.X16 ≠ .X17)]
                      exact hx17'
                    have h16' : (s₃.regs.getXReg .X16).toBitVec.setWidth 32 = vb := by
                      rw [h3]
                      simp [BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
                        BitVec.setWidth_eq]
                    rw [show rw = .W32 by rfl]
                    simp only [t_step_simp, Reg64s.setRegOrZr_xzr, Int64.toInt_zero,
                      Int.toNat_zero, BitVec.shiftLeft_zero, RegWidth.bits, MemWidth.bits,
                      h17', h16']
                    exact hk _ rfl) hdmem₃ hfr₃) ?_
                rintro s₄ ⟨_, hst₄, hdm₄, hfr₄⟩
                obtain ⟨hcc, hfc⟩ := hSub3264 (Or.inl rfl) hst₄
                refine ⟨hcc, fun {lf} hfl => ?_, hdm₄, hfr₄⟩
                obtain rfl := hflTrue hfl; exact hfc
              · refine armWp_mono (armStatusScratch_after
                  (armDirFallsTo_wp fun {_} p next jmp Q hk => by
                    have h17' : (s₃.regs.getXReg .X17).toBitVec.setWidth 64 = va := by
                      rw [h3, Reg64s.getXReg_setXReg_of_ne _ _ _ _ (by decide : XReg.X16 ≠ .X17)]
                      exact hx17'
                    have h16' : (s₃.regs.getXReg .X16).toBitVec.setWidth 64 = vb := by
                      rw [h3]; simp [BitVec.setWidth_eq]
                    rw [show rw = .W64 by rfl]
                    simp only [t_step_simp, Reg64s.setRegOrZr_xzr, Int64.toInt_zero,
                      Int.toNat_zero, BitVec.shiftLeft_zero, RegWidth.bits, MemWidth.bits,
                      h17', h16']
                    exact hk _ rfl) hdmem₃ hfr₃) ?_
                rintro s₄ ⟨_, hst₄, hdm₄, hfr₄⟩
                obtain ⟨hcc, hfc⟩ := hSub3264 (Or.inr rfl) hst₄
                refine ⟨hcc, fun {lf} hfl => ?_, hdm₄, hfr₄⟩
                obtain rfl := hflTrue hfl; exact hfc
      · exact fun _ h => h
    · have hvat : (!armAddrValid scale a) = true := by simp [hva]
      simp [hvat] at hc

/-- `FallsTo` specification matching `GprTarget.cmpMem_spec` for `armCmpMem`. -/
theorem armCmpMem_spec {h : Host} {k : Nat} {co : CmpOp} {w : Nat} {a : AddrArg Reg}
    {pb : PArg Reg Empty ArmCond (.bits w)} {pd : PDst Reg Empty ArmCond .bool}
    {c : List Directive} {clob : FlagMask} {va vb : BitVec w} {s : MachineData}
    {post : MachineState → Prop}
    (hc_in : armCmpMem co w a pb pd = some (c, clob))
    (hargs : ∀ r ∈ a.regs ++ pb.gprs, r ∉ armScratch)
    (_hd : ∀ r ∈ pd.gprs, r ∉ armScratch)
    (hload : loadVal (armMach.mem s) (.bits w) (a.eval (armMach.getGpr s)) = some va)
    (hpb : armMach.PArgHolds s (.bits w) pb vb) :
    armMach.FallsTo armCondReads h k c (pd.gprs ++ armScratch) [] clob s
      (fun s' => armMach.PDstHolds s' .bool pd (co.evalBits va vb) ∧
        armMach.mem s' = armMach.mem s) post := by
  letI := h
  obtain ⟨ci, hc, rfl⟩ := emitCleanPair_eq_some.mp hc_in
  exact armFallsTo_of_wp (armWp_mono (armCmpMem_core_wp hc hargs hload hpb)
    fun _ ⟨hpd, _, _, hdm, hfr⟩ => ⟨⟨hpd, hdm⟩, hfr⟩)

/-- Flag-reuse `FallsTo` specification matching `GprTarget.cmpMem_flags_spec` for `armCmpMem`. -/
theorem armCmpMem_flags_spec {h : Host} {k : Nat} {co : CmpOp} {w : Nat} {a : AddrArg Reg}
    {pb : PArg Reg Empty ArmCond (.bits w)} {pd : PDst Reg Empty ArmCond .bool}
    {lhsFirst : Bool} {c : List Directive} {clob : FlagMask} {va vb : BitVec w} {s : MachineData}
    {post : MachineState → Prop}
    (hfl : armCmpMemFlagsOut co w pb pd = some lhsFirst)
    (hc_in : armCmpMem co w a pb pd = some (c, clob))
    (hargs : ∀ r ∈ a.regs ++ pb.gprs, r ∉ armScratch)
    (_hd : ∀ r ∈ pd.gprs, r ∉ armScratch)
    (hload : loadVal (armMach.mem s) (.bits w) (a.eval (armMach.getGpr s)) = some va)
    (hpb : armMach.PArgHolds s (.bits w) pb vb) :
    armMach.FallsTo armCondReads h k c (pd.gprs ++ armScratch) [] clob s
      (fun s' => armMach.PDstHolds s' .bool pd (co.evalBits va vb) ∧
        FlagCmpOk armMach armGpr s' (if lhsFirst then va else vb)
          (if lhsFirst then vb else va) false ∧
        armMach.mem s' = armMach.mem s) post := by
  letI := h
  obtain ⟨ci, hc, rfl⟩ := emitCleanPair_eq_some.mp hc_in
  exact armFallsTo_of_wp (armWp_mono (armCmpMem_core_wp hc hargs hload hpb)
    fun _ ⟨hpd, _, hfc, hdm, hfr⟩ => ⟨⟨hpd, hfc hfl, hdm⟩, hfr⟩)

private theorem armAluShift_eval {w : Nat} (sh : AluShift) (v : BitVec w) (k : Nat) :
    (armAluShift sh).eval v k = sh.eval v k := by
  cases sh <;> rfl

/-- `GprTarget.shiftAlu_spec` for `armShiftAlu` (via `armShiftedAlu_spec`). -/
theorem armShiftAlu_spec {h : Host} {k w : Nat} {code : OpCode [.bits w, .bits w] [.bits w]}
    {ra rb : Reg} {sh : AluShift} {n : Nat} {rd : Reg} {c : List Directive} {clob : FlagMask}
    {va vb : BitVec w} {s : MachineData} {post : MachineState → Prop}
    (hc : armGpr.shiftAlu w code ra rb sh n rd = some (c, clob))
    (_ : ra ∉ armScratch) (_ : rb ∉ armScratch) (_ : rd ∉ armScratch)
    (ha : GprHolds (armMach.getGpr s ra) (.bits w) va)
    (hb : GprHolds (armMach.getGpr s rb) (.bits w) vb) :
    armMach.FallsTo armCondReads h k c (rd :: armScratch) [] clob s
      (fun s' => code.wp (va, sh.eval vb n, ()) (fun (res, ()) =>
        GprHolds (armMach.getGpr s' rd) (.bits w) res) ∧ armMach.mem s' = armMach.mem s) post :=
  (armShiftedAlu_spec h code ra rb (armAluShift sh) n rd c clob hc s va vb ha hb post).conseq
    fun _ ⟨hw, hm, _⟩ _ => ⟨by rw [armAluShift_eval] at hw; exact hw, hm⟩

/-- `GprTarget.shiftAlu_zero32` for `armShiftAlu` (via `armShiftedAlu_zero32`). -/
theorem armShiftAlu_zero32 {h : Host} {k : Nat} {code : OpCode [.bits 32, .bits 32] [.bits 32]}
    {ra rb : Reg} {sh : AluShift} {n : Nat} {rd : Reg} {c : List Directive} {clob : FlagMask}
    {va vb : BitVec 32} {s : MachineData} {post : MachineState → Prop}
    (hc : armGpr.shiftAlu 32 code ra rb sh n rd = some (c, clob))
    (_ : ra ∉ armScratch) (_ : rb ∉ armScratch) (_ : rd ∉ armScratch)
    (ha : GprHolds (armMach.getGpr s ra) (.bits 32) va)
    (hb : GprHolds (armMach.getGpr s rb) (.bits 32) vb) :
    armMach.FallsTo armCondReads h k c (rd :: armScratch) [] clob s
      (fun s' => code.wp (va, sh.eval vb n, ()) (fun (res, ()) =>
        armMach.getGpr s' rd = res.setWidth 64) ∧ armMach.mem s' = armMach.mem s) post :=
  (armShiftedAlu_zero32 h code ra rb (armAluShift sh) n rd c clob hc s va vb ha hb post).conseq
    fun _ ⟨hw, hm, _⟩ _ => ⟨by rw [armAluShift_eval] at hw; exact hw, hm⟩

/-- `GprTarget.shiftCmp_spec` for `armShiftCmp` (via `armShiftedCmp_spec`). -/
theorem armShiftCmp_spec {h : Host} {k : Nat} {o : CmpOp} {w : Nat} {ra rb : Reg}
    {sh : AluShift} {n : Nat} {lhsShift : Bool} {pd : PDst Reg Empty ArmCond .bool}
    {c : List Directive} {clob : FlagMask} {va vb : BitVec w} {s : MachineData}
    {post : MachineState → Prop}
    (hc : armGpr.shiftCmp o w ra rb sh n lhsShift pd = some (c, clob))
    (_ : ra ∉ armScratch) (_ : rb ∉ armScratch) (_ : ∀ r ∈ pd.gprs, r ∉ armScratch)
    (ha : GprHolds (armMach.getGpr s ra) (.bits w) va)
    (hb : GprHolds (armMach.getGpr s rb) (.bits w) vb) :
    let lhs := if lhsShift then sh.eval va n else va
    let rhs := if lhsShift then vb else sh.eval vb n
    armMach.FallsTo armCondReads h k c (pd.gprs ++ armScratch) [] clob s
      (fun s' => armMach.PDstHolds s' .bool pd (o.evalBits lhs rhs) ∧
        armMach.mem s' = armMach.mem s) post :=
  (armShiftedCmp_spec h ra rb (armAluShift sh) n lhsShift pd c clob hc s va vb ha hb post).conseq
    fun _ ⟨hpd, _, hdm⟩ _ => by simp only [armAluShift_eval] at hpd; exact ⟨hpd, hdm⟩

/-- `GprTarget.shiftCmp_flags_spec` for `armShiftCmp` (via `armShiftedCmp_spec`). -/
theorem armShiftCmp_flags_spec {h : Host} {k : Nat} {o : CmpOp} {w : Nat} {ra rb : Reg}
    {sh : AluShift} {n : Nat} {lhsShift : Bool} {pd : PDst Reg Empty ArmCond .bool} {lf : Bool}
    {c : List Directive} {clob : FlagMask} {va vb : BitVec w} {s : MachineData}
    {post : MachineState → Prop}
    (hfl : armGpr.shiftCmpFlagsOut? o w lhsShift pd = some lf)
    (hc : armGpr.shiftCmp o w ra rb sh n lhsShift pd = some (c, clob))
    (_ : ra ∉ armScratch) (_ : rb ∉ armScratch) (_ : ∀ r ∈ pd.gprs, r ∉ armScratch)
    (ha : GprHolds (armMach.getGpr s ra) (.bits w) va)
    (hb : GprHolds (armMach.getGpr s rb) (.bits w) vb) :
    let lhs := if lhsShift then sh.eval va n else va
    let rhs := if lhsShift then vb else sh.eval vb n
    armMach.FallsTo armCondReads h k c (pd.gprs ++ armScratch) [] clob s
      (fun s' => armMach.PDstHolds s' .bool pd (o.evalBits lhs rhs) ∧
        FlagCmpOk armMach armGpr s' (if lf then lhs else rhs) (if lf then rhs else lhs) false ∧
        armMach.mem s' = armMach.mem s) post :=
  (armShiftedCmp_spec h ra rb (armAluShift sh) n lhsShift pd c clob hc s va vb ha hb post).conseq
    fun _ ⟨hpd, hfc, hdm⟩ _ => by
      simp only [armAluShift_eval] at hpd hfc
      exact ⟨hpd, hfc hfl, hdm⟩

section ParserChecks

open Kraken.AArch64.Parser

private example :
    ⸨prog|
      subs wzr, w1, #112
      subs wzr, w2, w3
      cbz w4, L_tgt
      cbnz w5, L_tgt
      ldrsb x17, [x1]
      subs wzr, w17, #0
      csinc x0, xzr, xzr, le
      ldrb w17, [x1, #4]
      subs wzr, w17, #42
      ldrsh x17, [x1, x2, lsl #1]
      sbfm w16, w3, #0, #15
      subs wzr, w17, w16
    ⸩ =
      (armCmpZextOp .eq 8 true false (.gpr (.reg .X1)) (.imm 112#8)
        (.flag .eq)).elim [] Prod.fst ++
      (armCmpZextOp .ult 8 true true (.gpr (.reg .X2)) (.gpr (.reg .X3))
        (.flag .cc)).elim [] Prod.fst ++
      (armCmpZeroZextJcc true .eq 8 (.reg .X4) "L_tgt").elim [] Prod.fst ++
      (armCmpZeroZextJcc true .ne 16 (.reg .X5) "L_tgt").elim [] Prod.fst ++
      (armCmpMem .sgt 8 (.baseDisp (.reg .X1) 0) (.imm 0#8)
        (.gpr (.reg .X0))).elim [] Prod.fst ++
      (armCmpMem .eq 8 (.baseDisp (.reg .X1) 4) (.imm 42#8)
        (.flag .eq)).elim [] Prod.fst ++
      (armCmpMem .slt 16 (.baseIdxDisp (.reg .X1) (.reg .X2) .s2 0) (.gpr (.reg .X3))
        (.flag .lt)).elim [] Prod.fst := by rfl

/-- Swapped-condition (`cc = armCmpCond o.swap`) reversed-operand `pb - mem` forms. -/
private example :
    ⸨prog|
      ldr x17, [x1]
      subs xzr, x3, x17
      ldrsb x17, [x1]
      movz x16, #5
      subs wzr, w16, w17
      ldrb w17, [x1, #4]
      ubfm w16, w3, #0, #7
      subs wzr, w16, w17
    ⸩ =
      (armCmpMem .ult 64 (.baseDisp (.reg .X1) 0) (.gpr (.reg .X3))
        (.flag .hi)).elim [] Prod.fst ++
      (armCmpMem .slt 8 (.baseDisp (.reg .X1) 0) (.imm 5#8)
        (.flag .gt)).elim [] Prod.fst ++
      (armCmpMem .ult 8 (.baseDisp (.reg .X1) 4) (.gpr (.reg .X3))
        (.flag .hi)).elim [] Prod.fst := by rfl

end ParserChecks

end LeanQbe.T.Arm64
