module

public import LeanQbe.T.Amd64.IselVecLemmas2
import Kraken.X64.Parser

/-!
# SysV x64 Vector Target Verification — Part 3

* `x64EmitTernlog_wp`, `x64WideTernlogBin_wp`, `x64UniformShiftI32_wp`, `x64BinInPlace128_wp`.
* `mkpair`/`unpair` pack-unpack bridge soundness (`x64EmitMkpair_spec`, `x64EmitUnpair_spec`).
* `x64Vop_spec`, `x64Vop_noLab`, `x64VecSpec : VecTarget ...`, and kernel `rfl` `ParserChecks`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64

open Std

section OpSpecs

private theorem ternlog_1vec_finish {t : Ty} (ht : t.size ≤ 512)
    {x f0 f1 : BitVec 512} {rhs : BitVec t.size}
    (hbit : ∀ i, i < t.size → i < 512 →
      ((x.getLsbD i && (f1.getLsbD i ^^ f0.getLsbD i)) ^^ f0.getLsbD i) = rhs.getLsbD i) :
    ((x &&& (f1 ^^^ f0)) ^^^ f0).setWidth t.size = rhs := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simpa only [BitVec.getLsbD_setWidth, show i < t.size from hi, decide_true, Bool.true_and,
    BitVec.getLsbD_xor, BitVec.getLsbD_and] using hbit i hi (by omega)

private theorem x64EmitTernlog_wp [Host] (w : SlotWidth) {t : Ty} (ht : t.size = w.bits)
    {vd : RegMm} {imm : BitVec 8} {pa pb pc : PArg Reg64 RegMm CondCode t}
    {va vb vc : Val t} {c : List Instr} {s : MachineData}
    (hc : x64EmitTernlogIns w t vd imm pa pb pc = some c) (hvd : vd ∉ x64VecScratch)
    (hpaV : ∀ vr ∈ pargVecs pa, vr ∉ x64VecScratch)
    (hpbV : ∀ vr ∈ pargVecs pb, vr ∉ x64VecScratch)
    (hpcV : ∀ vr ∈ pargVecs pc, vr ∉ x64VecScratch)
    (hha : x64Mach.PArgHolds s t pa va) (hhb : x64Mach.PArgHolds s t pb vb)
    (hhc : x64Mach.PArgHolds s t pc vc) :
    @Program.wp _ (emitClean c) (fun s' => VecStepFrame vd s s' ∧
      (s'.zmms.get512 vd).setWidth t.size =
        BitVec.ternaryLogic (toBits t va) (toBits t vb) (toBits t vc) imm)
      (fun _ _ => False) s := by
  have h14d : (.mm14 : RegMm) ≠ vd := (ne_of_not_mem_x64VecScratch hvd).1.symm
  have h15d : (.mm15 : RegMm) ≠ vd := (ne_of_not_mem_x64VecScratch hvd).2.symm
  have h145 : (.mm14 : RegMm) ≠ .mm15 := by decide
  have h154 : (.mm15 : RegMm) ≠ .mm14 := by decide
  have swHold : ∀ {vr : RegMm} {v : Val t}, x64Mach.PArgHolds s t (.vec vr) v →
      (s.zmms.get512 vr).setWidth w.bits = (toBits t v).setWidth w.bits :=
    fun hh => (setWidth_vecHolds ht _ _ hh).trans (setWidth_of_eq ht _).symm
  cases pa <;> cases pb <;> cases pc <;>
    try (dsimp only [x64EmitTernlogIns] at hc; cases hc; done)
  · -- .vec, .vec, .vec
    rename_i ra rb rc
    have hra := hpaV ra (by dsimp only [pargVecs]; exact List.mem_cons_self)
    have hrb := hpbV rb (by dsimp only [pargVecs]; exact List.mem_cons_self)
    have hrc := hpcV rc (by dsimp only [pargVecs]; exact List.mem_cons_self)
    dsimp only [x64EmitTernlogIns] at hc
    simp only [Option.some.injEq] at hc; subst hc
    simp only [emitClean_ite, emitClean_append, emitClean_cons, emitClean_nil]
    exact ternlog_3reg_wp w ht hvd hra (ne_of_not_mem_x64VecScratch hrb).2
      (ne_of_not_mem_x64VecScratch hrc).2 (swHold hha) (swHold hhb) (swHold hhc)
  · -- .vec, .vec, .imm
    rename_i ra rb cc
    rcases hhc with rfl
    have hra := hpaV ra (by dsimp only [pargVecs]; exact List.mem_cons_self)
    have hrb := hpbV rb (by dsimp only [pargVecs]; exact List.mem_cons_self)
    dsimp only [x64EmitTernlogIns] at hc
    cases hv : x64VmoviWithIns .mm15 w .mm14 ((toBits t cc).setWidth 512) with
    | none => simp [hv] at hc
    | some pimm =>
      rw [hv] at hc; simp only [Option.map_some, Option.some.injEq] at hc; subst hc
      simp only [emitClean_ite, emitClean_append, emitClean_cons, emitClean_nil]
      have hsplit : (if ra == vd then emitClean pimm ++ [.instr (x64TernlogI w vd rb .mm14 imm)]
          else if rb != vd then
            emitClean pimm ++ emitClean (x64VmovIns w vd ra) ++
              [.instr (x64TernlogI w vd rb .mm14 imm)]
          else
            emitClean pimm ++ emitClean (x64VmovIns w .mm15 vd) ++
              emitClean (x64VmovIns w vd ra) ++
              [.instr (x64TernlogI w vd .mm15 .mm14 imm)]) =
          emitClean pimm ++ (if ra == vd then [x64TernlogD w vd rb .mm14 imm]
          else if rb != vd && .mm14 != vd then x64Vmov w vd ra ++ [x64TernlogD w vd rb .mm14 imm]
          else x64Vmov w .mm15 vd ++ x64Vmov w vd ra ++
            [x64TernlogD w vd (if rb == vd then .mm15 else rb)
              (if .mm14 == vd then .mm15 else .mm14) imm]) := by
        simp only [bne, regMm_beq_false h14d, x64TernlogD, x64Vmov]
        by_cases h1 : ra = vd
        · simp [regMm_beq_true h1]
        · by_cases h2 : rb = vd <;>
            simp [regMm_beq_false h1, regMm_beq_true, regMm_beq_false, h2, List.append_assoc]
      rw [hsplit]
      refine Program.wp.append (x64Vmovi_step .mm15 w .mm14 vd (by simp [x64VecScratch])
        (by simp [x64VecScratch]) h154 _ hv s) ?_
      rintro s1 ⟨hf1, hz1, h14⟩
      have hrb1 : s1.zmms.get512 rb = s.zmms.get512 rb :=
        hz1 rb (ne_of_not_mem_x64VecScratch hrb).1 (ne_of_not_mem_x64VecScratch hrb).2
      have hra1 : s1.zmms.get512 ra = s.zmms.get512 ra :=
        hz1 ra (ne_of_not_mem_x64VecScratch hra).1 (ne_of_not_mem_x64VecScratch hra).2
      have h14' : (s1.zmms.get512 .mm14).setWidth w.bits = (toBits t cc).setWidth w.bits := by
        rw [h14, BitVec.setWidth_setWidth_of_le _ w.bits_le_512]
      refine Program.wp.mono (ternlog_3reg_wp w ht hvd hra (ne_of_not_mem_x64VecScratch hrb).2 h145
        (by rw [hra1]; exact swHold hha) (by rw [hrb1]; exact swHold hhb) h14') ?_
      rintro s' ⟨hf2, hres⟩; exact ⟨hf1.trans hf2, hres⟩
  · -- .vec, .imm, .vec
    rename_i ra cb rc
    rcases hhb with rfl
    have hra := hpaV ra (by dsimp only [pargVecs]; exact List.mem_cons_self)
    have hrc := hpcV rc (by dsimp only [pargVecs]; exact List.mem_cons_self)
    dsimp only [x64EmitTernlogIns] at hc
    cases hv : x64VmoviWithIns .mm15 w .mm14 ((toBits t cb).setWidth 512) with
    | none => simp [hv] at hc
    | some pimm =>
      rw [hv] at hc; simp only [Option.map_some, Option.some.injEq] at hc; subst hc
      simp only [emitClean_ite, emitClean_append, emitClean_cons, emitClean_nil]
      have hsplit : (if ra == vd then emitClean pimm ++ [.instr (x64TernlogI w vd .mm14 rc imm)]
          else if rc != vd then
            emitClean pimm ++ emitClean (x64VmovIns w vd ra) ++
              [.instr (x64TernlogI w vd .mm14 rc imm)]
          else
            emitClean pimm ++ emitClean (x64VmovIns w .mm15 vd) ++
              emitClean (x64VmovIns w vd ra) ++
              [.instr (x64TernlogI w vd .mm14 .mm15 imm)]) =
          emitClean pimm ++ (if ra == vd then [x64TernlogD w vd .mm14 rc imm]
          else if .mm14 != vd && rc != vd then x64Vmov w vd ra ++ [x64TernlogD w vd .mm14 rc imm]
          else x64Vmov w .mm15 vd ++ x64Vmov w vd ra ++
            [x64TernlogD w vd (if .mm14 == vd then .mm15 else .mm14)
              (if rc == vd then .mm15 else rc) imm]) := by
        simp only [bne, regMm_beq_false h14d, x64TernlogD, x64Vmov]
        by_cases h1 : ra = vd
        · simp [regMm_beq_true h1]
        · by_cases h2 : rc = vd <;>
            simp [regMm_beq_false h1, regMm_beq_true, regMm_beq_false, h2, List.append_assoc]
      rw [hsplit]
      refine Program.wp.append (x64Vmovi_step .mm15 w .mm14 vd (by simp [x64VecScratch])
        (by simp [x64VecScratch]) h154 _ hv s) ?_
      rintro s1 ⟨hf1, hz1, h14⟩
      have hra1 : s1.zmms.get512 ra = s.zmms.get512 ra :=
        hz1 ra (ne_of_not_mem_x64VecScratch hra).1 (ne_of_not_mem_x64VecScratch hra).2
      have hrc1 : s1.zmms.get512 rc = s.zmms.get512 rc :=
        hz1 rc (ne_of_not_mem_x64VecScratch hrc).1 (ne_of_not_mem_x64VecScratch hrc).2
      have h14' : (s1.zmms.get512 .mm14).setWidth w.bits = (toBits t cb).setWidth w.bits := by
        rw [h14, BitVec.setWidth_setWidth_of_le _ w.bits_le_512]
      refine Program.wp.mono (ternlog_3reg_wp w ht hvd hra h145 (ne_of_not_mem_x64VecScratch hrc).2
        (by rw [hra1]; exact swHold hha) h14' (by rw [hrc1]; exact swHold hhc)) ?_
      rintro s' ⟨hf2, hres⟩; exact ⟨hf1.trans hf2, hres⟩
  · -- .vec, .imm, .imm
    rename_i ra cb cc
    rcases hhb with rfl; rcases hhc with rfl
    dsimp only [x64EmitTernlogIns] at hc
    refine Program.wp.mono (x64EmitTernlog1Vec_wp w (x := (toBits t va).setWidth 512) hc hvd (by
      rw [swHold hha, BitVec.setWidth_setWidth_of_le _ w.bits_le_512])) ?_
    rintro s' ⟨hf, hvd'⟩; refine ⟨hf, ?_⟩
    rw [← ht] at hvd'; rw [hvd']
    refine ternlog_1vec_finish (ht ▸ w.bits_le_512) fun i hi hi512 => ?_
    simp only [t_ternaryLogic_eq]
    rw [getLsbD_ternaryLogic _ _ _ imm i hi512, getLsbD_ternaryLogic _ _ _ imm i hi512,
      getLsbD_ternaryLogic _ _ _ imm i hi]
    simp only [BitVec.getLsbD_allOnes, BitVec.getLsbD_zero, hi512, decide_true, Bool.true_and,
      BitVec.getLsbD_setWidth]
    cases (toBits t va).getLsbD i <;> cases (toBits t cb).getLsbD i <;>
      cases (toBits t cc).getLsbD i <;> simp
  · -- .imm, .vec, .vec
    rename_i ca rb rc
    rcases hha with rfl
    have hrb := hpbV rb (by dsimp only [pargVecs]; exact List.mem_cons_self)
    have hrc := hpcV rc (by dsimp only [pargVecs]; exact List.mem_cons_self)
    dsimp only [x64EmitTernlogIns] at hc
    cases hv : x64VmoviIns w vd ((toBits t ca).setWidth 512) with
    | none => simp [hv] at hc
    | some p =>
      rw [hv] at hc; simp only [Option.map_some, Option.some.injEq] at hc; subst hc
      simp only [emitClean_ite, emitClean_append, emitClean_cons, emitClean_nil]
      by_cases hbc : rb ≠ vd ∧ rc ≠ vd
      · simp only [bne, regMm_beq_false hbc.1, regMm_beq_false hbc.2,
          Bool.not_false, Bool.and_self, ↓reduceIte]
        refine Program.wp.append (x64Vmovi_step .mm14 w vd vd (by simp)
          (by simp [x64VecScratch]) h14d _ hv s) ?_
        rintro s1 ⟨hf1, hz1, hvd1⟩
        refine Program.wp.mono (x64TernlogD_step w vd vd rb rc (by simp) imm s1) ?_
        rintro s' ⟨hf2, hvd'⟩
        refine ⟨hf1.trans hf2, ?_⟩
        have h0 : (s'.zmms.get512 vd).setWidth w.bits =
            BitVec.ternaryLogic ((toBits t ca).setWidth w.bits) ((toBits t vb).setWidth w.bits)
              ((toBits t vc).setWidth w.bits) imm := by
          rw [hvd', hvd1, BitVec.setWidth_setWidth_of_le _ w.bits_le_512,
            hz1 rb hbc.1 (ne_of_not_mem_x64VecScratch hrb).1, swHold hhb,
            hz1 rc hbc.2 (ne_of_not_mem_x64VecScratch hrc).1, swHold hhc]
        have h1' := congrArg (BitVec.setWidth t.size) h0
        simpa only [BitVec.setWidth_setWidth_of_le _ (by omega : t.size ≤ w.bits),
          setWidth_ternaryLogic (by omega : t.size ≤ w.bits), BitVec.setWidth_eq] using h1'
      · have hnot : (rb != vd && rc != vd) = false := by
          cases hbd : (rb == vd) <;> cases hcd : (rc == vd)
          · exact absurd ⟨fun e => by subst e; simp [regMm_beq_true rfl] at hbd,
              fun e => by subst e; simp [regMm_beq_true rfl] at hcd⟩ hbc
          all_goals simp [bne, hbd, hcd]
        simp only [hnot, Bool.false_eq_true, ↓reduceIte, List.append_assoc]
        refine Program.wp.append (x64Vmov_step w .mm15 vd vd (by simp [x64VecScratch]) s) ?_
        rintro s1 ⟨hf1, hz1, h15⟩
        refine Program.wp.append (x64Vmovi_step .mm14 w vd vd (by simp)
          (by simp [x64VecScratch]) h14d _ hv s1) ?_
        rintro s2 ⟨hf2, hz2, hvd2⟩
        have hsrc : ∀ (r : RegMm) (v : Val t), r ∉ x64VecScratch →
            x64Mach.PArgHolds s t (.vec r) v →
            (s2.zmms.get512 (if r == vd then .mm15 else r)).setWidth w.bits =
              (toBits t v).setWidth w.bits := by
          intro r v hr hh
          by_cases hrd : r = vd
          · subst hrd
            simp only [regMm_beq_true rfl, ↓reduceIte, hz2 .mm15 h15d h145.symm, h15, swHold hh]
          · simp only [regMm_beq_false hrd, Bool.false_eq_true, ↓reduceIte,
              hz2 r hrd (ne_of_not_mem_x64VecScratch hr).1,
              hz1 r (ne_of_not_mem_x64VecScratch hr).2, swHold hh]
        refine Program.wp.mono (x64TernlogD_step w vd vd _ _ (by simp) imm s2) ?_
        rintro s' ⟨hf3, hvd'⟩
        refine ⟨(hf1.trans hf2).trans hf3, ?_⟩
        have h0 : (s'.zmms.get512 vd).setWidth w.bits =
            BitVec.ternaryLogic ((toBits t ca).setWidth w.bits) ((toBits t vb).setWidth w.bits)
              ((toBits t vc).setWidth w.bits) imm := by
          rw [hvd', hvd2, BitVec.setWidth_setWidth_of_le _ w.bits_le_512,
            hsrc rb vb hrb hhb, hsrc rc vc hrc hhc]
        have h1' := congrArg (BitVec.setWidth t.size) h0
        simpa only [BitVec.setWidth_setWidth_of_le _ (by omega : t.size ≤ w.bits),
          setWidth_ternaryLogic (by omega : t.size ≤ w.bits), BitVec.setWidth_eq] using h1'
  · -- .imm, .vec, .imm
    rename_i ca rb cc
    rcases hha with rfl; rcases hhc with rfl
    dsimp only [x64EmitTernlogIns] at hc
    refine Program.wp.mono (x64EmitTernlog1Vec_wp w (x := (toBits t vb).setWidth 512) hc hvd (by
      rw [swHold hhb, BitVec.setWidth_setWidth_of_le _ w.bits_le_512])) ?_
    rintro s' ⟨hf, hvd'⟩; refine ⟨hf, ?_⟩
    rw [← ht] at hvd'; rw [hvd']
    refine ternlog_1vec_finish (ht ▸ w.bits_le_512) fun i hi hi512 => ?_
    simp only [t_ternaryLogic_eq]
    rw [getLsbD_ternaryLogic _ _ _ imm i hi512, getLsbD_ternaryLogic _ _ _ imm i hi512,
      getLsbD_ternaryLogic _ _ _ imm i hi]
    simp only [BitVec.getLsbD_allOnes, BitVec.getLsbD_zero, hi512, decide_true, Bool.true_and,
      BitVec.getLsbD_setWidth]
    cases (toBits t ca).getLsbD i <;> cases (toBits t vb).getLsbD i <;>
      cases (toBits t cc).getLsbD i <;> simp
  · -- .imm, .imm, .vec
    rename_i ca cb rc
    rcases hha with rfl; rcases hhb with rfl
    dsimp only [x64EmitTernlogIns] at hc
    refine Program.wp.mono (x64EmitTernlog1Vec_wp w (x := (toBits t vc).setWidth 512) hc hvd (by
      rw [swHold hhc, BitVec.setWidth_setWidth_of_le _ w.bits_le_512])) ?_
    rintro s' ⟨hf, hvd'⟩; refine ⟨hf, ?_⟩
    rw [← ht] at hvd'; rw [hvd']
    refine ternlog_1vec_finish (ht ▸ w.bits_le_512) fun i hi hi512 => ?_
    simp only [t_ternaryLogic_eq]
    rw [getLsbD_ternaryLogic _ _ _ imm i hi512, getLsbD_ternaryLogic _ _ _ imm i hi512,
      getLsbD_ternaryLogic _ _ _ imm i hi]
    simp only [BitVec.getLsbD_allOnes, BitVec.getLsbD_zero, hi512, decide_true, Bool.true_and,
      BitVec.getLsbD_setWidth]
    cases (toBits t ca).getLsbD i <;> cases (toBits t cb).getLsbD i <;>
      cases (toBits t vc).getLsbD i <;> simp
  · -- .imm, .imm, .imm
    rename_i ca cb cc
    rcases hha with rfl; rcases hhb with rfl; rcases hhc with rfl
    dsimp only [x64EmitTernlogIns] at hc
    refine Program.wp.mono (x64Vmovi_step .mm14 w vd vd (by simp)
      (by simp [x64VecScratch]) h14d _ hc s) ?_
    rintro s' ⟨hf, _, hvd'⟩; refine ⟨hf, ?_⟩
    have hlt512 : t.size ≤ 512 := ht ▸ w.bits_le_512
    rw [← ht] at hvd'
    rw [hvd', BitVec.setWidth_setWidth_of_le _ hlt512, BitVec.setWidth_eq, t_ternaryLogic_eq]

private theorem x64WideTernlogBin_wp [Host] {t : Ty} {imm : BitVec 8}
    {fv : ∀ {m : Nat}, BitVec m → BitVec m → BitVec m}
    (htern : ∀ {m : Nat} (x y : BitVec m), BitVec.ternaryLogic x y y imm = fv x y)
    {pas : Tup (PArg Reg64 RegMm CondCode) [t, t]} {dsts : Tup (PDst Reg64 RegMm CondCode) [t]}
    {c : List Instr} {clob : FlagMask} {va vb : Val t} {s : MachineData}
    (hc : x64WideTernlogBinIns imm pas dsts = some (c, clob))
    (hpaV : ∀ vr ∈ tupArgVecs pas, vr ∉ x64VecScratch)
    (hdV : ∀ vr ∈ tupDstVecs dsts, vr ∉ x64VecScratch)
    (hhold : TRel (x64Mach.PArgHolds s) pas (va, vb, ())) :
    ∃ vd, dsts = (.vec vd, ()) ∧ clob = maskNone ∧ x64IsVecBits t = true ∧ t.size ≤ 512 ∧
      @Program.wp _ (emitClean c) (fun s' => VecStepFrame vd s s' ∧
        (s'.zmms.get512 vd).setWidth t.size = fv (toBits t va) (toBits t vb))
        (fun _ _ => False) s := by
  rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨d, ⟨⟩⟩
  dsimp only [x64WideTernlogBinIns] at hc
  cases hw : x64VecSlotWidth t with
  | none => simp [hw] at hc
  | some w =>
    rw [hw] at hc
    cases d with
    | gpr _ | flag _ => simp at hc
    | vec vd =>
      by_cases hw64 : w = .w64
      · subst hw64; simp at hc
      · simp only [beq_iff_eq, hw64, ↓reduceIte, Option.map_eq_some_iff, Prod.mk.injEq] at hc
        obtain ⟨c0, hc0, rfl, rfl⟩ := hc
        have ht : t.size = w.bits := (x64VecSlotWidth_bits_eq hw).symm
        have haw : (x64AwOf w).bits = w.bits := x64AwOf_bits_of_ne_w64 hw64
        have hvb : x64IsVecBits t = true := x64IsVecBits_of_slot hw
        have hle : t.size ≤ 512 := x64VecSlotWidth_le_512 hw
        have hvd : vd ∉ x64VecScratch := hdV vd (by simp [tupDstVecs])
        rcases hhold with _ | ⟨hha, hrest⟩
        rcases hrest with _ | ⟨hhb, _⟩
        refine ⟨vd, rfl, rfl, hvb, hle, ?_⟩
        refine Program.wp.mono (x64EmitBinInPlace_wp w ht (upd := fun _ x y =>
            (BitVec.ternaryLogic (x.setWidth (x64AwOf w).bits) (y.setWidth (x64AwOf w).bits)
              (y.setWidth (x64AwOf w).bits) imm).setWidth 512)
            (res := fun x y => fv (x.cast ht.symm) (y.cast ht.symm))
            (fun _ x y => by
              rw [BitVec.setWidth_setWidth_of_le _ (ht ▸ w.bits_le_512),
                setWidth_ternaryLogic (ht ▸ x64W_bits_le_awBits w),
                BitVec.setWidth_setWidth_of_le _ (ht ▸ x64W_bits_le_awBits w),
                BitVec.setWidth_setWidth_of_le _ (ht ▸ x64W_bits_le_awBits w),
                htern, setWidth_of_eq ht.symm, setWidth_of_eq ht.symm])
            (fun dd src st => fallsTo_mono (x64Vpternlogd_fallsTo w dd src src imm st) <| by
              rintro st' rfl
              refine ⟨rfl, rfl, rfl, fun vr hvr => RegZmms.get512_set_avx_of_ne _ w hvr.symm _, ?_⟩
              rw [RegZmms.get512_set_avx_same, haw, BitVec.setWidth_eq, BitVec.setWidth_eq])
            hc0 hvd (fun vr h => hpaV vr (pargVecs_sub_2_1 pa pb vr h))
            (fun vr h => hpaV vr (pargVecs_sub_2_2 pa pb vr h)) hha hhb) ?_
        rintro s' ⟨hf, hval⟩; exact ⟨hf, hval⟩

private theorem mapLanes32_cast {p q : Nat} (f : BitVec 32 → BitVec 32) (h : p = q) (x : BitVec p) :
    (x.mapLanes 32 f).cast h = (x.cast h).mapLanes 32 f := by
  subst h; rfl

private theorem x64UniformShiftI32_wp [Host] {t : Ty}
    {mk : SlotWidth → Nat → RegMm → RegMm → Instr}
    {f : Nat → BitVec 32 → BitVec 32}
    (hmop : ∀ (w : SlotWidth) (cnt : Nat) (d src : RegMm) (st : MachineData), w ≠ .w64 → cnt < 32 →
      Directive.FallsTo (.instr (mk w cnt d src)) st
        (fun st' => st' = { st with zmms := (st.zmms.set (x64AvxRegOf w d)
          (((st.zmms.get512 src).setWidth (x64AwOf w).bits).mapLanes 32 (f cnt))) }))
    {pas : Tup (PArg Reg64 RegMm CondCode) [t, t]} {dsts : Tup (PDst Reg64 RegMm CondCode) [t]}
    {c : List Instr} {clob : FlagMask} {va vb : Val t} {s : MachineData}
    (hc : x64UniformShiftI32Ins pas dsts mk = some (c, clob))
    (hdV : ∀ vr ∈ tupDstVecs dsts, vr ∉ x64VecScratch)
    (hhold : TRel (x64Mach.PArgHolds s) pas (va, vb, ())) :
    ∃ vd, dsts = (.vec vd, ()) ∧ clob = maskNone ∧ x64IsI32Vec t = true ∧ t.size ≤ 512 ∧
      ∃ cnt, x64UniformI32Splat? t vb = some cnt ∧
      @Program.wp _ (emitClean c) (fun s' => VecStepFrame vd s s' ∧
        (s'.zmms.get512 vd).setWidth t.size = (toBits t va).mapLanes 32 (f cnt))
        (fun _ _ => False) s := by
  rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨d, ⟨⟩⟩
  dsimp only [x64UniformShiftI32Ins] at hc
  cases hi32 : x64IsI32Vec t
  · simp [hi32] at hc
  · simp only [hi32, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hc
    cases hw : x64VecSlotWidth t with
    | none => simp [hw] at hc
    | some w =>
      rw [hw] at hc
      cases pb with
      | gpr _ | vec _ | flag _ => simp at hc
      | imm cb =>
        cases d with
        | gpr _ | flag _ => simp at hc
        | vec vd =>
          by_cases hw64 : w = .w64
          · subst hw64; simp at hc
          · simp only [beq_iff_eq, hw64, ↓reduceIte, Option.bind] at hc
            cases hsp : x64UniformI32Splat? t cb with
            | none => simp [hsp] at hc
            | some cnt =>
              rw [hsp] at hc
              simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hc
              obtain ⟨c0, hc0, rfl, rfl⟩ := hc
              have ht : t.size = w.bits := (x64VecSlotWidth_bits_eq hw).symm
              have haw : (x64AwOf w).bits = w.bits := x64AwOf_bits_of_ne_w64 hw64
              have hle : t.size ≤ 512 := x64VecSlotWidth_le_512 hw
              have hcnt : cnt < 32 := x64UniformI32Splat?_lt32 hi32 hsp
              rcases hhold with _ | ⟨hha, hrest⟩
              rcases hrest with _ | ⟨hhb, _⟩
              rcases hhb with rfl
              refine ⟨vd, rfl, rfl, rfl, hle, cnt, hsp, ?_⟩
              refine Program.wp.mono (x64EmitUnary_wp w ht (upd := fun _ x =>
                  ((x.setWidth (x64AwOf w).bits).mapLanes 32 (f cnt)).setWidth 512)
                  (res := fun x => (x.cast ht.symm).mapLanes 32 (f cnt))
                  (fun _ x => by
                    rw [BitVec.setWidth_setWidth_of_le _ (ht ▸ w.bits_le_512),
                      haw, BitVec.setWidth_eq, setWidth_of_eq ht.symm, mapLanes32_cast])
                  (fun dd src st => fallsTo_mono (hmop w cnt dd src st hw64 hcnt) <| by
                    rintro st' rfl
                    refine ⟨rfl, rfl, rfl,
                      fun vr hvr => RegZmms.get512_set_avx_of_ne _ w hvr.symm _, ?_⟩
                    rw [RegZmms.get512_set_avx_same, haw, BitVec.setWidth_eq])
                  hc0 (hdV vd (by simp [tupDstVecs])) hha) ?_
              rintro s' ⟨hf, hval⟩; exact ⟨hf, hval⟩

private theorem x64BinInPlace128_wp [Host] {t : Ty} {ok : Bool}
    (hok : ok = true → t.size = 128)
    {pas : Tup (PArg Reg64 RegMm CondCode) [t, t]} {dsts : Tup (PDst Reg64 RegMm CondCode) [t]}
    {emit : RegMm → RegMm → Instr} {f : BitVec 128 → BitVec 128 → BitVec 128}
    (hemit : ∀ d src st, Directive.FallsTo (.instr (emit d src)) st
      (fun st' => st' = { st with zmms := (st.zmms.setLegacy (.xmm d)
        (f ((st.zmms.get512 d).setWidth 128) ((st.zmms.get512 src).setWidth 128))) }))
    {c : List Instr} {clob : FlagMask} {va vb : Val t} {s : MachineData}
    (hc : x64BinInPlace128Ins ok pas dsts emit = some (c, clob))
    (hpaV : ∀ vr ∈ tupArgVecs pas, vr ∉ x64VecScratch)
    (hdV : ∀ vr ∈ tupDstVecs dsts, vr ∉ x64VecScratch)
    (hhold : TRel (x64Mach.PArgHolds s) pas (va, vb, ())) :
    ∃ (vd : RegMm) (ht : t.size = 128), ok = true ∧ dsts = (.vec vd, ()) ∧ clob = maskNone ∧
      @Program.wp _ (emitClean c) (fun s' => VecStepFrame vd s s' ∧
        (s'.zmms.get512 vd).setWidth t.size =
          (f ((toBits t va).cast ht) ((toBits t vb).cast ht)).cast ht.symm)
        (fun _ _ => False) s := by
  rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨d, ⟨⟩⟩
  dsimp only [x64BinInPlace128Ins] at hc
  cases hokv : ok
  · simp [hokv] at hc
  · simp only [hokv, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hc
    cases d with
    | gpr _ | flag _ => simp at hc
    | vec vd =>
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hc
      obtain ⟨c0, hc0, rfl, rfl⟩ := hc
      have ht : t.size = 128 := hok hokv
      rcases hhold with _ | ⟨hha, hrest⟩
      rcases hrest with _ | ⟨hhb, _⟩
      refine ⟨vd, ht, rfl, rfl, rfl, ?_⟩
      refine Program.wp.mono (x64EmitBinInPlace_wp .w128 ht
          (upd := fun old x y => old.replaceLow (f x y))
          (res := fun x y => (f x y).cast ht.symm)
          (fun old x y => by
            rw [← BitVec.setWidth_setWidth_of_le (old.replaceLow (f x y)) (by omega : t.size ≤ 128),
              setWidth_replaceLow (by decide), setWidth_of_eq ht.symm])
          (fun dd src st => fallsTo_mono (hemit dd src st) <| by
            rintro st' rfl
            refine ⟨rfl, rfl, rfl,
              fun vr hvr => RegZmms.get512_setLegacy_xmm_of_ne _ hvr.symm _, ?_⟩
            rw [RegZmms.get512_setLegacy_xmm])
          hc0 (hdV vd (by simp [tupDstVecs]))
          (fun vr h => hpaV vr (pargVecs_sub_2_1 pa pb vr h))
          (fun vr h => hpaV vr (pargVecs_sub_2_2 pa pb vr h)) hha hhb) ?_
      rintro s' ⟨hf, hval⟩; exact ⟨hf, hval⟩

private theorem x64LoadI32ToGpr_wp [Host] (rd : Reg64) {pa : PArg Reg64 RegMm CondCode i32}
    {va : Val i32} {c : List Instr} {s : MachineData}
    (hc : x64LoadI32ToGprIns rd pa = some c) (hhold : x64Mach.PArgHolds s i32 pa va) :
    @Program.wp _ (emitClean c) (fun s' => s'.dmem = s.dmem ∧ s'.zmms = s.zmms ∧
      (∀ r, r ≠ rd → s'.regs.get64 r = s.regs.get64 r) ∧
      s'.regs.get64 rd = va.setWidth 64) (fun _ _ => False) s := by
  cases pa with
  | vec _ => dsimp only [x64LoadI32ToGprIns] at hc; cases hc
  | gpr r =>
    dsimp only [x64LoadI32ToGprIns] at hc
    simp only [Option.some.injEq] at hc; subst hc
    obtain ⟨_, h32⟩ := hhold
    refine Program.wp.mono (Directive.FallsTo.wp (x64Mov32_fallsTo rd r s)) ?_
    rintro s' rfl
    refine ⟨rfl, rfl, fun rr hrr => Reg64s.get64_set64_of_ne _ _ _ _ hrr.symm, ?_⟩
    rw [Reg64s.get64_set64_same, h32]
  | imm ca =>
    rcases hhold with rfl
    dsimp only [x64LoadI32ToGprIns] at hc
    simp only [Option.some.injEq] at hc; subst hc
    refine Program.wp.mono (Directive.FallsTo.wp (x64MoviD_fallsTo rd (ca.setWidth 64) s)) ?_
    rintro s' rfl
    exact ⟨rfl, rfl, fun rr hrr => Reg64s.get64_set64_of_ne _ _ _ _ hrr.symm,
      Reg64s.get64_set64_same _ _ _⟩

private theorem x64LoadSubVec64_wp [Host] {t : Ty} (ht : t.size = 64) (d vd : RegMm)
    (hd : d ∈ vd :: x64VecScratch) {pa : PArg Reg64 RegMm CondCode t} {va : Val t}
    {c : List Instr} {s : MachineData}
    (hc : x64LoadSubVec64Ins ht d pa = some c) (hhold : x64Mach.PArgHolds s t pa va) :
    @Program.wp _ (emitClean c) (fun s' => VecStepFrame vd s s' ∧
      (∀ vr, vr ≠ d → s'.zmms.get512 vr = s.zmms.get512 vr) ∧
      (s'.zmms.get512 d).setWidth 128 = ((toBits t va).cast ht).setWidth 128)
      (fun _ _ => False) s := by
  cases pa with
  | gpr _ | flag _ => dsimp only [x64LoadSubVec64Ins] at hc; cases hc
  | vec r =>
    dsimp only [x64LoadSubVec64Ins] at hc
    simp only [Option.some.injEq] at hc; subst hc
    refine Program.wp.mono (Directive.FallsTo.wp (x64Vmovq_fallsTo d r s)) ?_
    rintro s' rfl
    refine ⟨⟨rfl, rfl, fun _ _ => rfl, fun vr hvr =>
      RegZmms.get512_set_xmm_of_ne _ (fun e => hvr (by subst e; exact hd)) _⟩,
      fun vr hvr => RegZmms.get512_set_xmm_of_ne _ hvr.symm _, ?_⟩
    rw [RegZmms.get512_set_xmm_same, BitVec.setWidth_setWidth_of_le _ (by decide : 128 ≤ 512),
      BitVec.setWidth_eq, setWidth_vecHolds ht _ _ hhold]
  | imm ca =>
    rcases hhold with rfl
    dsimp only [x64LoadSubVec64Ins] at hc
    simp only [Option.some.injEq] at hc; subst hc
    refine Program.wp.mono (x64Movi64_wp d _ s) ?_
    rintro s' ⟨hd', hs', hr', hz', hval⟩
    refine ⟨⟨hd', hs', hr', fun vr hvr => hz' vr (fun e => hvr (by subst e; exact hd))⟩, hz', ?_⟩
    rw [hval, BitVec.setWidth_setWidth_of_le _ (by decide : 128 ≤ 512), BitVec.setWidth_eq]

private theorem mkpair32_bits (a b : BitVec 32) :
    (a.setWidth 64 ||| (b.setWidth 64 <<< (32 : Nat))) =
      (b ++ a).cast (by decide : 32 + 32 = 64) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_cast, BitVec.getLsbD_append, show i < 64 from hi, decide_true, Bool.true_and]
  by_cases h : i < 32
  · simp [h, BitVec.getLsbD_eq_getElem]
  · have ha : a.getLsbD i = false := Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le a.isLt (Nat.pow_le_pow_right (by decide) (by omega : 32 ≤ i)))
    rw [ha]
    simp [h, show i - 32 < 64 by omega, show i - 32 < 32 by omega]

private theorem x64EmitMkpair_subvec_aux {a b : Ty} (h32 : ¬(a = .bits 32 ∧ b = .bits 32))
    {pas : Tup (PArg Reg64 RegMm CondCode) [a, b]}
    {dsts : Tup (PDst Reg64 RegMm CondCode) [.pair a b]}
    {vd : RegMm} (hd : dsts = (.vec vd, ())) {c : List Instr} {clob : FlagMask}
    (hc : x64EmitMkpairIns pas dsts = some (c, clob)) :
    ∃ pa pb, ∃ (h : a = b ∧ x64IsBridgeSubVec a ∧ a.size = 64),
      pas = (pa, pb, ()) ∧
      ((x64LoadSubVec64Ins h.2.2 .mm14 pa).bind fun la =>
        (x64LoadSubVec64Ins (h.1 ▸ h.2.2 : b.size = 64) vd pb).bind fun lb =>
          some (la ++ lb ++ [x64Avx128I (.pshufd (.avx (.xmm vd)) (.avx (.xmm vd)) (.int64 0x4e)),
            x64TernlogI .w128 vd .mm14 .mm14 0xFE], maskNone)) = some (c, clob) := by
  dsimp only [x64EmitMkpairIns] at hc
  split at hc
  · exact absurd ⟨rfl, rfl⟩ h32
  · rename_i pa pb vd'
    cases hd
    split at hc
    · rename_i hcond; exact ⟨pa, pb, hcond, rfl, hc⟩
    · simp at hc
  · simp at hc

private theorem x64EmitMkpair_spec {h : Host} {k : Nat} {a b : Ty}
    {pas : Tup (PArg Reg64 RegMm CondCode) [a, b]}
    {dsts : Tup (PDst Reg64 RegMm CondCode) [.pair a b]}
    {c : List Instr} {clob : FlagMask} {va : Val a} {vb : Val b} {P : Tup Val [.pair a b] → Prop}
    {s : MachineData} {post : MachineState → Prop}
    (hc : x64EmitMkpairIns pas dsts = some (c, clob))
    (hpaG : ∀ r ∈ tupArgGprs pas, r ∉ x64Scratch)
    (hpaV : ∀ vr ∈ tupArgVecs pas, vr ∉ x64VecScratch)
    (hdV : ∀ vr ∈ tupDstVecs dsts, vr ∉ x64VecScratch)
    (hhold : TRel (x64Mach.PArgHolds s) pas (va, vb, ()))
    (hwp : P ((va, vb), ())) :
    x64Mach.FallsTo x64CondReads h k (emitClean c) (tupDstGprs dsts ++ x64Scratch)
      (tupDstVecs dsts ++ x64VecScratch) clob s
      (fun s' => (∃ rvs, P rvs ∧ TRel (x64Mach.PDstHolds s') dsts rvs) ∧
        x64Mach.mem s' = x64Mach.mem s) post := by
  have hdv : ∃ vd, dsts = (.vec vd, ()) := by
    dsimp only [x64EmitMkpairIns] at hc
    split at hc <;> first
      | cases hc
      | exact ⟨_, rfl⟩
      | (split at hc <;> first | cases hc | exact ⟨_, rfl⟩)
  rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨d, ⟨⟩⟩
  cases d with
  | gpr _ => obtain ⟨_, h⟩ := hdv; cases congrArg Prod.fst h
  | vec vd =>
    have hvd : vd ∉ x64VecScratch := hdV vd (by simp [tupDstVecs])
    have h14d : (.mm14 : RegMm) ≠ vd := (ne_of_not_mem_x64VecScratch hvd).1.symm
    rcases hhold with _ | ⟨hha, hrest⟩
    rcases hrest with _ | ⟨hhb, _⟩
    by_cases h32 : a = .bits 32 ∧ b = .bits 32
    · rcases h32 with ⟨rfl, rfl⟩
      dsimp only [x64EmitMkpairIns] at hc
      simp only [Bind.bind, Option.bind] at hc
      cases hla : x64LoadI32ToGprIns .r10 pa with
      | none => simp [hla] at hc
      | some la =>
        cases hlb : x64LoadI32ToGprIns .r11 pb with
        | none => simp [hla, hlb] at hc
        | some lb =>
          rw [hla, hlb] at hc; simp only [Option.some.injEq, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          apply vecFallsTo_of_wp
          simp only [emitClean_append, emitClean_cons, emitClean_nil, List.append_assoc]
          refine Program.wp.append (x64LoadI32ToGpr_wp .r10 hla hha) ?_
          rintro s1 ⟨hd1, hz1, hg1, h10_1⟩
          have hhb1 : x64Mach.PArgHolds s1 i32 pb vb := by
            cases pb with
            | imm _ => exact hhb
            | vec _ => dsimp only [x64LoadI32ToGprIns] at hlb; cases hlb
            | gpr r =>
              have hr10 : r ≠ .r10 := (ne_of_not_mem_x64Scratch
                (hpaG r (by cases pa <;> simp [tupArgGprs]))).1
              refine ⟨hhb.1, ?_⟩
              change (s1.zmms.get512 |> fun _ => (s1.regs.get64 r).setWidth 32) = vb
              rw [hg1 r hr10]; exact hhb.2
          refine Program.wp.append (x64LoadI32ToGpr_wp .r11 hlb hhb1) ?_
          rintro s2 ⟨hd2, hz2, hg2, h11_2⟩
          refine Program.wp.cons (Directive.FallsTo.wp (x64Shl32Imm_fallsTo .r11 s2)) ?_
          rintro s3 ⟨hd3, hz3, hr3⟩
          refine Program.wp.cons (Directive.FallsTo.wp (x64Or64_fallsTo .r10 .r11 s3)) ?_
          rintro s4 ⟨hd4, hz4, hr4⟩
          refine Program.wp.mono (Directive.FallsTo.wp (x64VmovIn64_reg_fallsTo vd .r10 s4)) ?_
          rintro s' hs'
          have h10_2 : s2.regs.get64 .r10 = va.setWidth 64 := by rw [hg2 .r10 (by decide), h10_1]
          have h10_4 : s4.regs.get64 .r10 = (vb ++ va).cast (by decide : 32 + 32 = 64) := by
            rw [hr4, Reg64s.get64_set64_same, hr3, Reg64s.get64_set64_of_ne _ _ _ _ (by decide),
              h10_2, Reg64s.get64_set64_same, h11_2, mkpair32_bits]
          have hvd_out : x64Mach.PDstHolds s' (.pair i32 i32) (.vec vd) (va, vb) := by
            refine ⟨by decide, ?_⟩
            change (s'.zmms.get512 vd).setWidth 64 = toBits (.pair i32 i32) (va, vb)
            rw [hs']; dsimp only [toBits]
            rw [RegZmms.get512_set_xmm_same,
              BitVec.setWidth_setWidth_of_le _ (by decide : 64 ≤ 512),
              BitVec.setWidth_setWidth_of_le _ (by decide : 64 ≤ 128), BitVec.setWidth_eq, h10_4]
          have hfr_out : ∀ r, r ∉ tupDstGprs (R := Reg64) (V := RegMm) (C := CondCode)
              (ts := [.pair i32 i32]) (.vec vd, ()) ++ x64Scratch →
              s'.regs.get64 r = s.regs.get64 r := by
            intro r hrm
            have hr10 : r ≠ .r10 := fun e => hrm (by simp [e, x64Scratch])
            have hr11 : r ≠ .r11 := fun e => hrm (by simp [e, x64Scratch])
            rw [hs']; dsimp only
            rw [hr4, Reg64s.get64_set64_of_ne _ _ _ _ hr10.symm,
              hr3, Reg64s.get64_set64_of_ne _ _ _ _ hr11.symm, hg2 r hr11, hg1 r hr10]
          have hvm_out : ∀ vr, vr ∉ tupDstVecs (R := Reg64) (V := RegMm) (C := CondCode)
              (ts := [.pair i32 i32]) (.vec vd, ()) ++ x64VecScratch →
              s'.zmms.get512 vr = s.zmms.get512 vr := by
            intro vr hvm
            have hv : vr ≠ vd := fun e => hvm (by simp [e, tupDstVecs])
            rw [hs']; dsimp only
            rw [RegZmms.get512_set_xmm_of_ne _ hv.symm, hz4, hz3, hz2, hz1]
          have hd_out : x64Mach.mem s' = x64Mach.mem s := by
            change s'.dmem = s.dmem; rw [hs']; dsimp only; rw [hd4, hd3, hd2, hd1]
          refine ⟨⟨⟨((va, vb), ()), hwp, TRel.cons hvd_out .nil⟩, hd_out⟩,
            vecFrame_upd hfr_out hvm_out (Or.inl rfl)⟩
    · obtain ⟨pa', pb', hcond, heq, hc'⟩ := x64EmitMkpair_subvec_aux h32 rfl hc
      rcases heq with ⟨rfl, rfl⟩
      have hb64 : b.size = 64 := hcond.1 ▸ hcond.2.2
      cases hla : x64LoadSubVec64Ins hcond.2.2 .mm14 pa with
      | none => simp [hla] at hc'
      | some la =>
        cases hlb : x64LoadSubVec64Ins hb64 vd pb with
        | none => simp [hla, hlb] at hc'
        | some lb =>
          rw [hla, hlb] at hc'
          simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hc'
          rcases hc' with ⟨rfl, rfl⟩
          have hle : (Ty.pair a b).size ≤ 512 := by simp only [Ty.size]; omega
          apply vecFallsTo_of_wp
          simp only [emitClean_append, emitClean_cons, emitClean_nil, List.append_assoc]
          refine Program.wp.append
            (x64LoadSubVec64_wp hcond.2.2 .mm14 vd (by simp [x64VecScratch]) hla hha) ?_
          rintro s1 ⟨hf1, hz1, h14_1⟩
          have hpb1 : x64Mach.PArgHolds s1 b pb vb := by
            cases pb with
            | gpr _ | flag _ => dsimp only [x64LoadSubVec64Ins] at hlb; cases hlb
            | imm _ => exact hhb
            | vec rb =>
              have hrb14 : rb ≠ .mm14 := (ne_of_not_mem_x64VecScratch
                (hpaV rb (by cases pa <;> simp [tupArgVecs]))).1
              refine ⟨hhb.1, ?_⟩
              change (s1.zmms.get512 rb).setWidth b.size = toBits b vb
              rw [hz1 rb hrb14]; exact hhb.2
          refine Program.wp.append (x64LoadSubVec64_wp hb64 vd vd (by simp) hlb hpb1) ?_
          rintro s2 ⟨hf2, hz2, hvd2⟩
          refine Program.wp.cons (Directive.FallsTo.wp (x64Pshufd_fallsTo vd vd 0x4e#8 s2)) ?_
          rintro s3 rfl
          refine Program.wp.mono (x64TernlogD_step .w128 vd vd .mm14 .mm14 (by simp) 0xFE#8 _) ?_
          rintro s' ⟨hf4, hvd'⟩
          have hf3 : VecStepFrame vd s2 { s2 with zmms := (s2.zmms.setLegacy (.xmm vd)
              (((s2.zmms.get512 vd).setWidth 128).shuffleDwords 0x4e#8)) } :=
            ⟨rfl, rfl, fun _ _ => rfl, fun vr hvr =>
              RegZmms.get512_setLegacy_xmm_of_ne _ (fun e => hvr (by simp [e])) _⟩
          obtain ⟨hd, hs, hr, hz⟩ := ((hf1.trans hf2).trans hf3).trans hf4
          have hfr_sv : ∀ r, r ∉ tupDstGprs (R := Reg64) (V := RegMm) (C := CondCode)
              (ts := [Ty.pair a b]) (.vec vd, ()) ++ x64Scratch →
              s'.regs.get64 r = s.regs.get64 r := by
            intro r hrm
            exact hr r (fun e => hrm (by simp [e, x64Scratch]))
          have hvm_sv : ∀ vr, vr ∉ tupDstVecs (R := Reg64) (V := RegMm) (C := CondCode)
              (ts := [Ty.pair a b]) (.vec vd, ()) ++ x64VecScratch →
              s'.zmms.get512 vr = s.zmms.get512 vr := by
            intro vr hvm
            exact hz vr (fun e => hvm (by simp [e, tupDstVecs]))
          refine ⟨⟨⟨((va, vb), ()), hwp, TRel.cons ⟨hle, ?_⟩ .nil⟩, hd⟩,
            vecFrame_upd hfr_sv hvm_sv (Or.inr hs)⟩
          have hsz128 : (Ty.pair a b).size = 128 := by simp only [Ty.size]; omega
          change (s'.zmms.get512 vd).setWidth (Ty.pair a b).size = toBits (Ty.pair a b) (va, vb)
          change (s'.zmms.get512 vd).setWidth 128 = _ at hvd'
          rw [← BitVec.setWidth_setWidth_of_le (s'.zmms.get512 vd)
              (by omega : (Ty.pair a b).size ≤ 128),
            hvd', RegZmms.get512_setLegacy_xmm_of_ne _ h14d.symm, RegZmms.get512_setLegacy_xmm,
            setWidth_replaceLow (by decide), hz2 .mm14 h14d, hvd2, h14_1, ternaryLogic_or,
            shufd_0x4e_combine128]
          apply BitVec.eq_of_getLsbD_eq; intro i hi
          simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_cast, toBits, BitVec.getLsbD_append,
            show i < (Ty.pair a b).size from hi, decide_true, Bool.true_and]
          by_cases hlt : i < a.size
          · simp [hlt, show i < 64 by omega]
          · simp [hlt, show ¬(i < 64) by omega, show i - a.size = i - 64 by omega]

private theorem shufd_0x4e_hi64 (hi64 lo64 : BitVec 64) :
    (((hi64 ++ lo64).cast (by decide : 64 + 64 = 128)).shuffleDwords 0x4e#8).setWidth 64 =
      hi64 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hi64' : i < 64 := hi
  rw [BitVec.getLsbD_setWidth, BitVec.shuffleDwords,
    getLsbD_ofLanes _ (by decide) (by decide) i (by omega)]
  simp only [BitVec.lane, BitVec.getLsbD_extractLsb', BitVec.getLsbD_cast, BitVec.getLsbD_append,
    show i % 32 < 32 from Nat.mod_lt _ (by decide), hi64', decide_true, Bool.true_and]
  have hq : i / 32 = 0 ∨ i / 32 = 1 := by omega
  have hidx : 4 * ((i / 32) / 4) +
      ((0x4e#8 : BitVec 8).toNat >>> (2 * ((i / 32) % 4))) % 4 = i / 32 + 2 := by
    rcases hq with h | h <;> simp [h]
  rw [hidx]
  have hsum : 32 * (i / 32 + 2) + i % 32 = 64 + i := by omega
  simp [hsum]

private theorem x64EmitUnpair_spec {h : Host} {k : Nat} {a b : Ty}
    {pas : Tup (PArg Reg64 RegMm CondCode) [.pair a b]}
    {dsts : Tup (PDst Reg64 RegMm CondCode) [a, b]}
    {c : List Instr} {clob : FlagMask} {v : Val (.pair a b)} {P : Tup Val [a, b] → Prop}
    {s : MachineData} {post : MachineState → Prop}
    (hc : x64EmitUnpairIns pas dsts = some (c, clob))
    (hpaV : ∀ vr ∈ tupArgVecs pas, vr ∉ x64VecScratch)
    (hdG : ∀ r ∈ tupDstGprs dsts, r ∉ x64Scratch)
    (hdV : ∀ vr ∈ tupDstVecs dsts, vr ∉ x64VecScratch)
    (hhold : TRel (x64Mach.PArgHolds s) pas (v, ()))
    (hwp : P (v.1, v.2, ())) :
    x64Mach.FallsTo x64CondReads h k (emitClean c) (tupDstGprs dsts ++ x64Scratch)
      (tupDstVecs dsts ++ x64VecScratch) clob s
      (fun s' => (∃ rvs, P rvs ∧ TRel (x64Mach.PDstHolds s') dsts rvs) ∧
        x64Mach.mem s' = x64Mach.mem s) post := by
  have hunp : (∃ r0 r1, a = .bits 32 ∧ b = .bits 32 ∧ dsts = (.gpr r0, .gpr r1, ())) ∨
      (∃ v0 v1, dsts = (.vec v0, .vec v1, ())) := by
    dsimp only [x64EmitUnpairIns] at hc
    split at hc <;>
      first
      | cases hc
      | exact Or.inl ⟨_, _, rfl, rfl, rfl⟩
      | exact Or.inr ⟨_, _, rfl⟩
      | (split at hc <;>
          first
          | cases hc
          | exact Or.inl ⟨_, _, rfl, rfl, rfl⟩
          | exact Or.inr ⟨_, _, rfl⟩)
  rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨d0, d1, ⟨⟩⟩
  rcases hhold with _ | ⟨hhv, _⟩
  cases d0 <;> cases d1 <;>
    try (exfalso; rcases hunp with ⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ <;>
      (try cases congrArg Prod.fst h) <;> cases congrArg (Prod.fst ∘ Prod.snd) h; done)
  · -- .gpr d0, .gpr d1
    rename_i r0 r1
    by_cases h32 : a = .bits 32 ∧ b = .bits 32
    · rcases h32 with ⟨rfl, rfl⟩
      dsimp only [x64EmitUnpairIns] at hc
      by_cases heq : (r0 == r1) = true
      · simp [heq] at hc
      · have hne : r0 ≠ r1 := fun e => heq (by subst e; cases r0 <;> rfl)
        have hr0 : r0 ∉ x64Scratch := hdG r0 (by simp [tupDstGprs])
        have hr1 : r1 ∉ x64Scratch := hdG r1 (by simp [tupDstGprs])
        have hr0_10 : r0 ≠ .r10 := (ne_of_not_mem_x64Scratch hr0).1
        have h10 : ∃ lp, (match pa with
            | .vec vs => some [.instr (x64Avx128I (.vmovOut .W64 (.reg (q .r10)) (.xmm vs)))]
            | .imm cc => some [.instr (x64MoviI .r10 (toBits (.pair i32 i32) cc))]
            | _ => none) = some lp ∧
            emitClean c = lp ++ [ins32 (.mov (.reg (d r0)) (.reg (d .r10))),
              ins (.shr (.reg (q .r10)) (.imm8 (.int64 32))),
              ins32 (.mov (.reg (d r1)) (.reg (d .r10)))] ∧ clob = maskAll ∧
            @Program.wp _ lp (fun s1 => s1.dmem = s.dmem ∧ s1.zmms = s.zmms ∧
              (∀ r, r ≠ .r10 → s1.regs.get64 r = s.regs.get64 r) ∧
              s1.regs.get64 .r10 = (toBits (.pair i32 i32) v)) (fun _ _ => False) s := by
          cases pa with
          | gpr _ => simp [heq] at hc
          | vec vs =>
            simp only [heq, Bool.false_eq_true, ↓reduceIte,
              Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc
            rcases hc with ⟨rfl, rfl⟩
            refine ⟨_, rfl, by simp [emitClean_cons, emitClean_nil], rfl,
              Program.wp.mono (Directive.FallsTo.wp (x64VmovOut64_reg_fallsTo .r10 vs s)) ?_⟩
            rintro s1 rfl
            exact ⟨rfl, rfl, fun r hr => Reg64s.get64_set64_of_ne _ _ _ _ hr.symm, by
              rw [Reg64s.get64_set64_same]; exact hhv.2⟩
          | imm cc =>
            rcases hhv with rfl
            simp only [heq, Bool.false_eq_true, ↓reduceIte,
              Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc
            rcases hc with ⟨rfl, rfl⟩
            refine ⟨_, rfl, by simp [emitClean_cons, emitClean_nil], rfl,
              Program.wp.mono (Directive.FallsTo.wp (x64MoviD_fallsTo .r10 _ s)) ?_⟩
            rintro s1 rfl
            exact ⟨rfl, rfl, fun r hr => Reg64s.get64_set64_of_ne _ _ _ _ hr.symm,
              by dsimp only; exact Reg64s.get64_set64_same _ _ _⟩
        obtain ⟨lp, _, heqc, rfl, hlp⟩ := h10
        apply vecFallsTo_of_wp
        rw [heqc]
        refine Program.wp.append hlp ?_
        rintro s1 ⟨hd1, hz1, hg1, h10⟩
        refine Program.wp.cons (Directive.FallsTo.wp (x64Mov32_fallsTo r0 .r10 s1)) ?_
        rintro s2 rfl
        refine Program.wp.cons (Directive.FallsTo.wp (x64Shr32Imm_fallsTo .r10 _)) ?_
        rintro s3 ⟨hd3, hz3, hr3⟩
        refine Program.wp.mono (Directive.FallsTo.wp (x64Mov32_fallsTo r1 .r10 s3)) ?_
        rintro s' rfl
        have hv1 : ((toBits (.pair i32 i32) v).setWidth 32) = v.1 := by
          apply BitVec.eq_of_getLsbD_eq; intro i hi
          simp [toBits, BitVec.getLsbD_append, show i < 32 from hi]
        have hv2 : ((toBits (.pair i32 i32) v).ushiftRight 32).setWidth 32 = v.2 := by
          ext i hi
          simp [toBits, BitVec.getElem_append, show i < 32 from hi, show ¬(32 + i < 32) by omega]
        have hg_r0 : s3.regs.get64 r0 = (v.1).setWidth 64 := by
          rw [hr3]; dsimp only
          rw [Reg64s.get64_set64_of_ne _ _ _ _ hr0_10.symm, Reg64s.get64_set64_same, h10, hv1]
        have hg_r1 : ((s3.regs.get64 .r10).setWidth 32) = v.2 := by
          rw [hr3, Reg64s.get64_set64_same]; dsimp only
          rw [Reg64s.get64_set64_of_ne _ _ _ _ hr0_10, h10, hv2]
        have hr0_out : x64Mach.PDstHolds
            { s3 with regs :=
              s3.regs.set64 r1 (BitVec.setWidth 64 (BitVec.setWidth 32 (s3.regs.get64 .r10))) }
            i32 (.gpr r0) v.1 := by
          refine ⟨by decide, ?_⟩; dsimp only
          rw [Reg64s.get64_set64_of_ne _ _ _ _ hne.symm, hg_r0,
            BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
        have hr1_out : x64Mach.PDstHolds
            { s3 with regs :=
              s3.regs.set64 r1 (BitVec.setWidth 64 (BitVec.setWidth 32 (s3.regs.get64 .r10))) }
            i32 (.gpr r1) v.2 := by
          refine ⟨by decide, ?_⟩; dsimp only
          rw [Reg64s.get64_set64_same, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
            BitVec.setWidth_eq, hg_r1]
        have hfr_out : ∀ r, r ∉ tupDstGprs (R := Reg64) (V := RegMm) (C := CondCode)
            (ts := [i32, i32]) (.gpr r0, .gpr r1, ()) ++ x64Scratch →
            ({ s3 with regs :=
              s3.regs.set64 r1 (BitVec.setWidth 64 (BitVec.setWidth 32 (s3.regs.get64 .r10)))
            }.regs).get64 r =
              s.regs.get64 r := by
          intro r hrm
          have hn0 : r ≠ r0 := fun e => hrm (by simp [e, tupDstGprs])
          have hn1 : r ≠ r1 := fun e => hrm (by simp [e, tupDstGprs])
          have hnr10 : r ≠ .r10 := fun e => hrm (by simp [e, x64Scratch])
          dsimp only
          rw [Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hn1), hr3,
            Reg64s.get64_set64_of_ne _ _ _ _ hnr10.symm]; dsimp only
          rw [Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hn0), hg1 r hnr10]
        refine ⟨⟨⟨(v.1, v.2, ()), hwp, TRel.cons hr0_out (TRel.cons hr1_out .nil)⟩,
          by rw [hd3, hd1]⟩,
          vecFrame_upd hfr_out (fun vr _ => by rw [hz3, hz1]) (Or.inl rfl)⟩
    · exfalso; rcases hunp with ⟨_, _, ha, hb, _⟩ | ⟨_, _, h⟩
      · exact h32 ⟨ha, hb⟩
      · cases congrArg Prod.fst h
  · -- .vec v0, .vec v1
    rename_i v0 v1
    dsimp only [x64EmitUnpairIns] at hc
    by_cases heq : (v0 == v1) = true
    · simp [heq] at hc
    · have hv01 : v0 ≠ v1 := fun e => heq (by subst e; exact regMm_beq_true rfl)
      have hv0 : v0 ∉ x64VecScratch := hdV v0 (by simp [tupDstVecs])
      have hv1 : v1 ∉ x64VecScratch := hdV v1 (by simp [tupDstVecs])
      have h14_v0 : (.mm14 : RegMm) ≠ v0 := (ne_of_not_mem_x64VecScratch hv0).1.symm
      simp only [heq, Bool.false_eq_true, ↓reduceIte] at hc
      split at hc
      · rename_i hcond
        have hb64 : b.size = 64 := hcond.1 ▸ hcond.2.2
        have hle128 : (Ty.pair a b).size = 128 := by simp only [Ty.size]; omega
        cases pa with
        | gpr _ => simp at hc
        | vec vs =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          have hvs : vs ∉ x64VecScratch := hpaV vs (by simp [tupArgVecs])
          have h14_vs : (.mm14 : RegMm) ≠ vs := (ne_of_not_mem_x64VecScratch hvs).1.symm
          apply vecFallsTo_of_wp
          refine Program.wp.cons (Directive.FallsTo.wp (x64Pshufd_fallsTo .mm14 vs 0x4e#8 s)) ?_
          rintro s1 rfl
          refine Program.wp.cons (Directive.FallsTo.wp (x64Vmovq_fallsTo v0 vs _)) ?_
          rintro s2 rfl
          refine Program.wp.mono (Directive.FallsTo.wp (x64Vmovq_fallsTo v1 .mm14 _)) ?_
          rintro s' rfl
          have hvs_eq : (s.zmms.get512 vs).setWidth 128 =
              (((toBits b v.2).cast hb64 ++ (toBits a v.1).cast hcond.2.2).cast
                (by decide : 64 + 64 = 128)) := by
            apply BitVec.eq_of_getLsbD_eq; intro i hi
            have hbit := congrArg (fun bv => bv.getLsbD i) hhv.2
            simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_cast, BitVec.getLsbD_append,
              show i < 128 from hi, show i < (Ty.pair a b).size by omega,
              decide_true, Bool.true_and,
              toBits] at hbit ⊢
            rw [hbit]
            by_cases hlt : i < a.size
            · simp [hlt, show i < 64 by omega]
            · simp [hlt, show ¬(i < 64) by omega, show i - a.size = i - 64 by omega]
          let zm1 := s.zmms.setLegacy (.xmm .mm14)
            (((s.zmms.get512 vs).setWidth 128).shuffleDwords 0x4e#8)
          let zm2 := zm1.set (.xmm v0) (((zm1.get512 vs).setWidth 64).setWidth 128)
          let zm3 := zm2.set (.xmm v1) (((zm2.get512 .mm14).setWidth 64).setWidth 128)
          have hv0_out : x64Mach.PDstHolds { s with zmms := zm3 } a (.vec v0) v.1 := by
            refine ⟨by omega, ?_⟩; dsimp only [zm3, zm2, zm1]
            rw [RegZmms.get512_set_xmm_of_ne _ hv01.symm, RegZmms.get512_set_xmm_same,
              BitVec.setWidth_setWidth_of_le _ (by omega : a.size ≤ 512),
              BitVec.setWidth_setWidth_of_le _ (by omega : a.size ≤ 128),
              BitVec.setWidth_setWidth_of_le _ (by omega : a.size ≤ 64),
              RegZmms.get512_setLegacy_xmm_of_ne _ h14_vs]
            apply BitVec.eq_of_getLsbD_eq; intro i hi
            have hbit := congrArg (fun bv => bv.getLsbD i) hhv.2
            simp only [BitVec.getLsbD_setWidth, toBits, BitVec.getLsbD_cast, BitVec.getLsbD_append,
              show i < a.size from hi, show i < (Ty.pair a b).size by omega,
              decide_true, Bool.true_and] at hbit ⊢
            exact hbit
          have hv1_out : x64Mach.PDstHolds { s with zmms := zm3 } b (.vec v1) v.2 := by
            refine ⟨by omega, ?_⟩; dsimp only [zm3, zm2, zm1]
            rw [RegZmms.get512_set_xmm_same,
              BitVec.setWidth_setWidth_of_le _ (by omega : b.size ≤ 512),
              BitVec.setWidth_setWidth_of_le _ (by omega : b.size ≤ 128),
              BitVec.setWidth_setWidth_of_le _ (by omega : b.size ≤ 64),
              RegZmms.get512_set_xmm_of_ne _ h14_v0.symm, RegZmms.get512_setLegacy_xmm,
              ← BitVec.setWidth_setWidth_of_le _ (by omega : b.size ≤ 128),
              setWidth_replaceLow (by decide), hvs_eq,
              ← BitVec.setWidth_setWidth_of_le _ (by omega : b.size ≤ 64),
              shufd_0x4e_hi64]
            apply BitVec.eq_of_getLsbD_eq; intro i hi
            simp [show i < b.size from hi]
          have hvm_out : ∀ vr, vr ∉ tupDstVecs (R := Reg64) (V := RegMm) (C := CondCode)
              (ts := [a, b]) (.vec v0, .vec v1, ()) ++ x64VecScratch →
              zm3.get512 vr = s.zmms.get512 vr := by
            intro vr hvm
            have hn0 : vr ≠ v0 := fun e => hvm (by simp [e, tupDstVecs])
            have hn1 : vr ≠ v1 := fun e => hvm (by simp [e, tupDstVecs])
            have h14 : vr ≠ .mm14 := fun e => hvm (by simp [e, x64VecScratch])
            dsimp only [zm3, zm2, zm1]
            rw [RegZmms.get512_set_xmm_of_ne _ (Ne.symm hn1),
              RegZmms.get512_set_xmm_of_ne _ (Ne.symm hn0),
              RegZmms.get512_setLegacy_xmm_of_ne _ h14.symm]
          refine ⟨⟨⟨(v.1, v.2, ()), hwp, TRel.cons hv0_out (TRel.cons hv1_out .nil)⟩, rfl⟩,
            vecFrame_upd (fun _ _ => rfl) hvm_out (Or.inr rfl)⟩
        | imm cc =>
          rcases hhv with rfl
          simp only [Option.some.injEq, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          apply vecFallsTo_of_wp
          rw [emitClean_append]
          refine Program.wp.append (x64Movi64_wp v0 _ s) ?_
          rintro s1 ⟨hd1, hs1, hr1, hz1, hv0_1⟩
          refine Program.wp.mono (x64Movi64_wp v1 _ s1) ?_
          rintro s' ⟨hd2, hs2, hr2, hz2, hv1_2⟩
          have hv0_imm : x64Mach.PDstHolds s' a (.vec v0) cc.1 := by
            refine ⟨by omega, ?_⟩
            change (s'.zmms.get512 v0).setWidth a.size = toBits a cc.1
            rw [hz2 v0 hv01, hv0_1, BitVec.setWidth_setWidth_of_le _ (by omega : a.size ≤ 512),
              BitVec.setWidth_setWidth_of_le _ (by omega : a.size ≤ 128),
              setWidth_of_eq hcond.2.2.symm]
            rfl
          have hv1_imm : x64Mach.PDstHolds s' b (.vec v1) cc.2 := by
            refine ⟨by omega, ?_⟩
            change (s'.zmms.get512 v1).setWidth b.size = toBits b cc.2
            rw [hv1_2, BitVec.setWidth_setWidth_of_le _ (by omega : b.size ≤ 512),
              BitVec.setWidth_setWidth_of_le _ (by omega : b.size ≤ 128), setWidth_of_eq hb64.symm]
            rfl
          have hfr_imm : ∀ r, r ∉ tupDstGprs (R := Reg64) (V := RegMm) (C := CondCode)
              (ts := [a, b]) (.vec v0, .vec v1, ()) ++ x64Scratch →
              s'.regs.get64 r = s.regs.get64 r := by
            intro r hrm
            have hr10 : r ≠ .r10 := fun e => hrm (by simp [e, x64Scratch])
            rw [hr2 r hr10, hr1 r hr10]
          have hvm_imm : ∀ vr, vr ∉ tupDstVecs (R := Reg64) (V := RegMm) (C := CondCode)
              (ts := [a, b]) (.vec v0, .vec v1, ()) ++ x64VecScratch →
              s'.zmms.get512 vr = s.zmms.get512 vr := by
            intro vr hvm
            have hn0 : vr ≠ v0 := fun e => hvm (by simp [e, tupDstVecs])
            have hn1 : vr ≠ v1 := fun e => hvm (by simp [e, tupDstVecs])
            rw [hz2 vr hn1, hz1 vr hn0]
          refine ⟨⟨⟨(cc.1, cc.2, ()), hwp, TRel.cons hv0_imm (TRel.cons hv1_imm .nil)⟩,
            hd2.trans hd1⟩,
            vecFrame_upd hfr_imm hvm_imm (Or.inr (hs2.trans hs1))⟩
      · simp at hc

private theorem shuffleDwords_cast {p q : Nat} (h : p = q) (x : BitVec p) (imm : BitVec 8) :
    (x.cast h).shuffleDwords imm = (x.shuffleDwords imm).cast h := by subst h; rfl

private theorem shuffleBytes_cast {p q : Nat} (h : p = q) (a m : BitVec p) :
    (a.cast h).shuffleBytes (m.cast h) = (a.shuffleBytes m).cast h := by subst h; rfl

private theorem alignBytes_cast {p q : Nat} (h : p = q) (a b : BitVec p) (imm : BitVec 8) :
    BitVec.alignBytes (a.cast h) (b.cast h) imm = (BitVec.alignBytes a b imm).cast h := by
  subst h; rfl

private theorem blendWords_cast {p q : Nat} (h : p = q) (a b : BitVec p) (imm : BitVec 8) :
    (a.cast h).blendWords (b.cast h) imm = (a.blendWords b imm).cast h := by subst h; rfl

private theorem x64FloatBin128_wp {h : Host} {k : Nat} {t : Ty}
    (op : Float32 → Float32 → Float32)
    (mop : Float.Model.Format → Float.Model.UnpackedFloat →
      Float.Model.UnpackedFloat → Float.Model.UnpackedFloat)
    (hlane : ∀ x y k, floatResultWp .s (mop .binary32 (unpackFloat .s x) (unpackFloat .s y)) k →
      k (sseBinOp op x y))
    {emit : RegMm → RegMm → Instr}
    (hemit : ∀ d src st, Directive.FallsTo (.instr (emit d src)) st
      (fun st' => st' = { st with zmms := (st.zmms.setLegacy (.xmm d)
        (BitVec.packedBinOp 32 (sseBinOp op)
          ((st.zmms.get512 d).setWidth 128) ((st.zmms.get512 src).setWidth 128))) }))
    {pas : Tup (PArg Reg64 RegMm CondCode) [t, t]} {dsts : Tup (PDst Reg64 RegMm CondCode) [t]}
    {c : List Instr} {clob : FlagMask} {va vb : Val t} {P : Tup Val [t] → Prop}
    {s : MachineData} {post : MachineState → Prop}
    (hc : x64BinInPlace128Ins (x64IsF32Vec t && t.size == 128) pas dsts emit = some (c, clob))
    (hpaV : ∀ vr ∈ tupArgVecs pas, vr ∉ x64VecScratch)
    (hdV : ∀ vr ∈ tupDstVecs dsts, vr ∉ x64VecScratch)
    (hhold : TRel (x64Mach.PArgHolds s) pas (va, vb, ()))
    (hwp : (if !t.isFloatTree then False else liftFloatRel2 mop t va vb (fun r => P (r, ())))) :
    x64Mach.FallsTo x64CondReads h k (emitClean c) (tupDstGprs dsts ++ x64Scratch)
      (tupDstVecs dsts ++ x64VecScratch) clob s
      (fun s' => (∃ rvs, P rvs ∧ TRel (x64Mach.PDstHolds s') dsts rvs) ∧
        x64Mach.mem s' = x64Mach.mem s) post := by
  obtain ⟨vd, _, hok, rfl, rfl, hwp0⟩ := x64BinInPlace128_wp (ok := x64IsF32Vec t && t.size == 128)
    (f := BitVec.packedBinOp 32 (sseBinOp op))
    (fun hh => by simp only [Bool.and_eq_true, beq_iff_eq] at hh; exact hh.2)
    hemit hc hpaV hdV hhold
  simp only [Bool.and_eq_true, beq_iff_eq] at hok
  have ht_eq := x64IsF32Vec_128_eq hok.1 hok.2
  subst ht_eq
  dsimp only [Ty.isFloatTree, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hwp
  have hp := sseBinOp_v4f32_spec op mop hlane va vb (fun r => P (r, ())) hwp
  refine vecOpFallsTo_P (by decide) hp (Program.wp.mono hwp0 ?_)
  rintro s' ⟨hf, hval⟩; exact ⟨hf, by rw [hval]; exact (toBits_ofBits v4f32 _).symm⟩

theorem x64Vop_spec {h : Host} {k : Nat} {sig rs : List Ty} {code : OpCode sig rs}
    {pas : Tup (PArg Reg64 RegMm CondCode) sig} {dsts : Tup (PDst Reg64 RegMm CondCode) rs}
    {vh : VariantHint} {c : List Directive} {clob : FlagMask} {vs : Tup Val sig}
    {P : Tup Val rs → Prop} {s : MachineData} {post : MachineState → Prop}
    (hc_in : x64Vop code pas dsts vh = some (c, clob))
    (_hpaG : ∀ r ∈ tupArgGprs pas, r ∉ x64Scratch)
    (hpaV : ∀ vr ∈ tupArgVecs pas, vr ∉ x64VecScratch)
    (hdG : ∀ r ∈ tupDstGprs dsts, r ∉ x64Scratch)
    (hdV : ∀ vr ∈ tupDstVecs dsts, vr ∉ x64VecScratch)
    (hhold : TRel (x64Mach.PArgHolds s) pas vs) (hwp : code.wp vs P) :
    x64Mach.FallsTo x64CondReads h k c (tupDstGprs dsts ++ x64Scratch)
      (tupDstVecs dsts ++ x64VecScratch) clob s
      (fun s' => (∃ rvs, P rvs ∧ TRel (x64Mach.PDstHolds s') dsts rvs) ∧
        x64Mach.mem s' = x64Mach.mem s) post := by
  dsimp only [x64Vop] at hc_in
  obtain ⟨ci, hc, rfl⟩ := emitCleanPair_eq_some.mp hc_in
  cases code with
  | copy t =>
    rcases vs with ⟨va, ⟨⟩⟩; rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨d, ⟨⟩⟩
    dsimp only [x64VopIns] at hc
    cases hw : x64VecSlotWidth t with
    | none => simp [hw] at hc
    | some w =>
      rw [hw] at hc
      cases d with
      | gpr _ | flag _ => simp at hc
      | vec vd =>
        have ht := x64VecSlotWidth_bits_eq hw
        have hle := x64VecSlotWidth_le_512 hw
        have hvd : vd ∉ x64VecScratch := hdV vd (by simp [tupDstVecs])
        have h14d : (.mm14 : RegMm) ≠ vd := (ne_of_not_mem_x64VecScratch hvd).1.symm
        rcases hhold with _ | ⟨hha, _⟩
        cases pa with
        | gpr _ | flag _ => simp at hc
        | vec vs =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          refine vecOpFallsTo_P hle hwp (Program.wp.mono (x64Vmov_step w vd vs vd (by simp) s) ?_)
          rintro s' ⟨hf, _, hval⟩; refine ⟨hf, ?_⟩
          have h1 := congrArg (BitVec.setWidth t.size) hval
          rw [BitVec.setWidth_setWidth_of_le _ (ht ▸ le_refl _),
            BitVec.setWidth_setWidth_of_le _ (ht ▸ le_refl _)] at h1
          exact h1.trans hha.2
        | imm ca =>
          rcases hha with rfl
          dsimp only at hc
          cases hv : x64VmoviIns w vd ((toBits t ca).setWidth 512) with
          | none => simp [hv] at hc
          | some p =>
            rw [hv] at hc; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc
            rcases hc with ⟨rfl, rfl⟩
            refine vecOpFallsTo_P hle hwp (Program.wp.mono (x64Vmovi_step .mm14 w vd vd (by simp)
              (by simp [x64VecScratch]) h14d _ hv s) ?_)
            rintro s' ⟨hf, _, hval⟩; refine ⟨hf, ?_⟩
            have h1 := congrArg (BitVec.setWidth t.size) hval
            rw [BitVec.setWidth_setWidth_of_le (s'.zmms.get512 vd) (ht ▸ le_refl _),
              BitVec.setWidth_setWidth_of_le (BitVec.setWidth 512 (toBits t ca)) (ht ▸ le_refl _),
              BitVec.setWidth_setWidth_of_le _ hle, BitVec.setWidth_eq] at h1
            exact h1
  | add t =>
    rcases vs with ⟨va, vb, ⟨⟩⟩; rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨d, ⟨⟩⟩
    dsimp only [x64VopIns] at hc
    cases hi32 : x64IsI32Vec t
    · simp [hi32] at hc
    · simp only [hi32, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hc
      cases hw : x64VecSlotWidth t with
      | none => simp [hw] at hc
      | some w =>
        rw [hw] at hc
        cases d with
        | gpr _ | flag _ => simp at hc
        | vec vd =>
          by_cases hw64 : w = .w64
          · subst hw64; simp at hc
          · simp only [beq_iff_eq, hw64, ↓reduceIte, Option.map_eq_some_iff, Prod.mk.injEq] at hc
            obtain ⟨c0, hc0, rfl, rfl⟩ := hc
            have ht : t.size = w.bits := (x64VecSlotWidth_bits_eq hw).symm
            have hle := x64VecSlotWidth_le_512 hw
            simp only [OpCode.wp_add, x64IsI32Vec_not_hasFloat hi32,
              Bool.false_eq_true, ↓reduceIte] at hwp
            rcases hhold with _ | ⟨hha, _ | ⟨hhb, _⟩⟩
            refine vecOpFallsTo_P hle hwp ?_
            refine Program.wp.mono (x64EmitVpaddd_wp w hw64 ht hc0 (hdV vd (by simp [tupDstVecs]))
              (fun vr hr => hpaV vr (pargVecs_sub_2_1 pa pb vr hr))
              (fun vr hr => hpaV vr (pargVecs_sub_2_2 pa pb vr hr)) hha hhb) ?_
            rintro s' ⟨hf, hval⟩; refine ⟨hf, ?_⟩
            rw [hval, toBits_lift2_add hi32, ← packedBinOp32_cast]
            congr 1 <;> simp [BitVec.cast_cast]
  | «and» t =>
    rcases vs with ⟨va, vb, ⟨⟩⟩
    obtain ⟨vd, rfl, rfl, hvb, hle, hwp0⟩ :=
      x64WideTernlogBin_wp ternaryLogic_0xC0 hc hpaV hdV hhold
    refine vecOpFallsTo_P hle hwp (Program.wp.mono hwp0 ?_)
    rintro s' ⟨hf, hval⟩
    exact ⟨hf, by
      rw [hval, toBits_lift2_bitwise (· &&& ·) (· && ·)
        (fun _ _ _ _ => BitVec.getLsbD_and) hvb]⟩
  | «or» t =>
    rcases vs with ⟨va, vb, ⟨⟩⟩
    obtain ⟨vd, rfl, rfl, hvb, hle, hwp0⟩ :=
      x64WideTernlogBin_wp ternaryLogic_0xFC hc hpaV hdV hhold
    refine vecOpFallsTo_P hle hwp (Program.wp.mono hwp0 ?_)
    rintro s' ⟨hf, hval⟩
    exact ⟨hf, by
      rw [hval, toBits_lift2_bitwise (· ||| ·) (· || ·)
        (fun _ _ _ _ => BitVec.getLsbD_or) hvb]⟩
  | xor t =>
    rcases vs with ⟨va, vb, ⟨⟩⟩
    obtain ⟨vd, rfl, rfl, hvb, hle, hwp0⟩ :=
      x64WideTernlogBin_wp ternaryLogic_0x3C hc hpaV hdV hhold
    refine vecOpFallsTo_P hle hwp (Program.wp.mono hwp0 ?_)
    rintro s' ⟨hf, hval⟩
    exact ⟨hf, by
      rw [hval, toBits_lift2_bitwise (· ^^^ ·) (· ^^ ·)
        (fun _ _ _ _ => BitVec.getLsbD_xor) hvb]⟩
  | not t =>
    rcases vs with ⟨va, ⟨⟩⟩; rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨d, ⟨⟩⟩
    dsimp only [x64VopIns] at hc
    cases hw : x64VecSlotWidth t with
    | none => simp [hw] at hc
    | some w =>
      rw [hw] at hc
      cases d with
      | gpr _ | flag _ => simp at hc
      | vec vd =>
        by_cases hw64 : w = .w64
        · subst hw64; simp at hc
        · simp only [beq_iff_eq, hw64, ↓reduceIte, Option.map_eq_some_iff, Prod.mk.injEq] at hc
          obtain ⟨c0, hc0, rfl, rfl⟩ := hc
          have ht : t.size = w.bits := (x64VecSlotWidth_bits_eq hw).symm
          have haw : (x64AwOf w).bits = w.bits := x64AwOf_bits_of_ne_w64 hw64
          have hvb := x64IsVecBits_of_slot hw
          have hle := x64VecSlotWidth_le_512 hw
          rcases hhold with _ | ⟨hha, _⟩
          refine vecOpFallsTo_P hle hwp ?_
          refine Program.wp.mono (x64EmitUnary_wp w ht (upd := fun old x =>
              (BitVec.ternaryLogic (old.setWidth (x64AwOf w).bits) (x.setWidth (x64AwOf w).bits)
                (x.setWidth (x64AwOf w).bits) 0x33#8).setWidth 512)
              (res := fun x => ~~~(x.cast ht.symm))
              (fun old x => by
                rw [BitVec.setWidth_setWidth_of_le _ (ht ▸ w.bits_le_512), haw,
                  setWidth_ternaryLogic (ht ▸ le_refl _),
                  BitVec.setWidth_setWidth_of_le _ (ht ▸ le_refl _),
                  BitVec.setWidth_setWidth_of_le _ (ht ▸ le_refl _),
                  ternaryLogic_0x33, setWidth_of_eq ht.symm])
              (fun dd src st => fallsTo_mono (x64Vpternlogd_fallsTo w dd src src 0x33#8 st) <| by
                rintro st' rfl
                refine ⟨rfl, rfl, rfl,
                  fun vr hvr => RegZmms.get512_set_avx_of_ne _ w hvr.symm _, ?_⟩
                rw [RegZmms.get512_set_avx_same, haw, BitVec.setWidth_eq])
              hc0 (hdV vd (by simp [tupDstVecs])) hha) ?_
          rintro s' ⟨hf, hval⟩
          exact ⟨hf, by rw [hval, BitVec.cast_cast, BitVec.cast_eq, toBits_lift1_not hvb]⟩
  | ternlog t imm =>
    rcases vs with ⟨va, vb, vc, ⟨⟩⟩; rcases pas with ⟨pa, pb, pc, ⟨⟩⟩; rcases dsts with ⟨d, ⟨⟩⟩
    dsimp only [x64VopIns] at hc
    cases hw : x64VecSlotWidth t with
    | none => simp [hw] at hc
    | some w =>
      rw [hw] at hc
      cases d with
      | gpr _ | flag _ => simp at hc
      | vec vd =>
        by_cases hw64 : w = .w64
        · subst hw64; simp at hc
        · simp only [beq_iff_eq, hw64, ↓reduceIte, Option.map_eq_some_iff, Prod.mk.injEq] at hc
          obtain ⟨c0, hc0, rfl, rfl⟩ := hc
          have ht : t.size = w.bits := (x64VecSlotWidth_bits_eq hw).symm
          have hvb := x64IsVecBits_of_slot hw
          have hle := x64VecSlotWidth_le_512 hw
          rcases hhold with _ | ⟨hha, _ | ⟨hhb, _ | ⟨hhc, _⟩⟩⟩
          refine vecOpFallsTo_P hle hwp ?_
          refine Program.wp.mono (x64EmitTernlog_wp w ht hc0 (hdV vd (by simp [tupDstVecs]))
            (fun vr hr => hpaV vr (pargVecs_sub_3_1 pa pb pc vr hr))
            (fun vr hr => hpaV vr (pargVecs_sub_3_2 pa pb pc vr hr))
            (fun vr hr => hpaV vr (pargVecs_sub_3_3 pa pb pc vr hr)) hha hhb hhc) ?_
          rintro s' ⟨hf, hval⟩
          exact ⟨hf, by rw [hval, toBits_lift3_ternlog hvb]⟩
  | rotr t =>
    rcases vs with ⟨va, vb, ⟨⟩⟩
    obtain ⟨vd, rfl, rfl, hi32, hle, cnt, hsp, hwp0⟩ := x64UniformShiftI32_wp
      (f := fun c x => x.rotateRight c) (fun w cnt d src st _ hcnt => by
        refine fallsTo_mono (x64Vprord_fallsTo w d src cnt hcnt st) ?_
        rintro st' rfl; rfl) hc hdV hhold
    simp only [OpCode.wp_rotr, x64IsI32Vec_not_hasFloat hi32, Bool.false_eq_true, ↓reduceIte] at hwp
    refine vecOpFallsTo_P hle hwp (Program.wp.mono hwp0 ?_)
    rintro s' ⟨hf, hval⟩
    exact ⟨hf, by rw [hval, toBits_lift2_splat32 (fun x y => x.rotateRight (y.toNat % _))
      (fun c x => x.rotateRight c) cnt (fun _ _ hy => by rw [hy]) hi32 _ va vb hsp]⟩
  | lshr t =>
    rcases vs with ⟨va, vb, ⟨⟩⟩
    obtain ⟨vd, rfl, rfl, hi32, hle, cnt, hsp, hwp0⟩ := x64UniformShiftI32_wp
      (f := fun c x => x >>> c) (fun w cnt d src st _ hcnt => by
        refine fallsTo_mono (x64Vpsrld_fallsTo w d src cnt hcnt st) ?_
        rintro st' rfl; rfl) hc hdV hhold
    simp only [OpCode.wp_lshr, x64IsI32Vec_not_hasFloat hi32, Bool.false_eq_true, ↓reduceIte] at hwp
    refine vecOpFallsTo_P hle hwp (Program.wp.mono hwp0 ?_)
    rintro s' ⟨hf, hval⟩
    exact ⟨hf, by rw [hval, toBits_lift2_splat32 (fun x y => x >>> (y.toNat % _))
      (fun c x => x >>> c) cnt (fun _ _ hy => by rw [hy]) hi32 _ va vb hsp]⟩
  | shufd t imm =>
    rcases vs with ⟨va, ⟨⟩⟩; rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨d, ⟨⟩⟩
    dsimp only [x64VopIns] at hc
    cases h128 : x64Is128Vec t
    · simp [h128] at hc
    · simp only [h128, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hc
      cases d with
      | gpr _ | flag _ => simp at hc
      | vec vd =>
        simp only [Option.map_eq_some_iff, Prod.mk.injEq] at hc
        obtain ⟨c0, hc0, rfl, rfl⟩ := hc
        have ht : t.size = 128 := by
          simp only [x64Is128Vec, Bool.and_eq_true, beq_iff_eq] at h128; exact h128.2
        dsimp only [OpCode.wp] at hwp
        rcases hhold with _ | ⟨hha, _⟩
        refine vecOpFallsTo_P (by omega) hwp.2.2 ?_
        refine Program.wp.mono (x64EmitUnary_wp .w128 ht
            (upd := fun old x => old.replaceLow (x.shuffleDwords imm))
            (res := fun x => (x.shuffleDwords imm).cast ht.symm)
            (fun old x => by
              rw [← BitVec.setWidth_setWidth_of_le (old.replaceLow (x.shuffleDwords imm))
                  (by omega : t.size ≤ 128),
                setWidth_replaceLow (by decide), setWidth_of_eq ht.symm])
            (fun dd src st => fallsTo_mono (x64Pshufd_fallsTo dd src imm st) <| by
              rintro st' rfl
              refine ⟨rfl, rfl, rfl,
              fun vr hvr => RegZmms.get512_setLegacy_xmm_of_ne _ hvr.symm _, ?_⟩
              rw [RegZmms.get512_setLegacy_xmm])
            hc0 (hdV vd (by simp [tupDstVecs])) hha) ?_
        rintro s' ⟨hf, hval⟩; refine ⟨hf, ?_⟩
        rw [hval, shuffleDwords_cast, BitVec.cast_cast, BitVec.cast_eq, ← shuffleDwords_eq]
        exact (toBits_ofBits t _).symm
  | shufb t =>
    rcases vs with ⟨va, vb, ⟨⟩⟩
    dsimp only [x64VopIns] at hc
    obtain ⟨vd, ht, _, rfl, rfl, hwp0⟩ := x64BinInPlace128_wp (ok := x64Is128Vec t)
      (fun h => by simp only [x64Is128Vec, Bool.and_eq_true, beq_iff_eq] at h; exact h.2)
      x64Pshufb_fallsTo hc hpaV hdV hhold
    dsimp only [OpCode.wp] at hwp
    refine vecOpFallsTo_P (by omega) hwp.2.2 (Program.wp.mono hwp0 ?_)
    rintro s' ⟨hf, hval⟩; refine ⟨hf, ?_⟩
    rw [hval, shuffleBytes_cast, BitVec.cast_cast, BitVec.cast_eq, ← shuffleBytes_eq]
    exact (toBits_ofBits t _).symm
  | alignr t imm =>
    rcases vs with ⟨va, vb, ⟨⟩⟩
    dsimp only [x64VopIns] at hc
    obtain ⟨vd, ht, _, rfl, rfl, hwp0⟩ := x64BinInPlace128_wp (ok := x64Is128Vec t)
      (f := fun a b => BitVec.alignBytes a b imm)
      (fun h => by simp only [x64Is128Vec, Bool.and_eq_true, beq_iff_eq] at h; exact h.2)
      (fun d s st => x64Palignr_fallsTo d s imm st) hc hpaV hdV hhold
    dsimp only [OpCode.wp] at hwp
    refine vecOpFallsTo_P (by omega) hwp.2.2 (Program.wp.mono hwp0 ?_)
    rintro s' ⟨hf, hval⟩; refine ⟨hf, ?_⟩
    rw [hval, alignBytes_cast, BitVec.cast_cast, BitVec.cast_eq, ← alignBytes_eq]
    exact (toBits_ofBits t _).symm
  | blendw t imm =>
    rcases vs with ⟨va, vb, ⟨⟩⟩
    dsimp only [x64VopIns] at hc
    obtain ⟨vd, ht, _, rfl, rfl, hwp0⟩ := x64BinInPlace128_wp (ok := x64Is128Vec t)
      (f := fun a b => a.blendWords b imm)
      (fun h => by simp only [x64Is128Vec, Bool.and_eq_true, beq_iff_eq] at h; exact h.2)
      (fun d s st => x64Pblendw_fallsTo d s imm st) hc hpaV hdV hhold
    dsimp only [OpCode.wp] at hwp
    refine vecOpFallsTo_P (by omega) hwp.2.2 (Program.wp.mono hwp0 ?_)
    rintro s' ⟨hf, hval⟩; refine ⟨hf, ?_⟩
    rw [hval, blendWords_cast, BitVec.cast_cast, BitVec.cast_eq, ← blendWords_eq]
    exact (toBits_ofBits t _).symm
  | fadd t =>
    rcases vs with ⟨va, vb, ⟨⟩⟩
    exact x64FloatBin128_wp (· + ·) Float.Model.UnpackedFloat.add sseBinOp_add_wp
      x64Addps_fallsTo hc hpaV hdV hhold hwp
  | fsub t =>
    rcases vs with ⟨va, vb, ⟨⟩⟩
    exact x64FloatBin128_wp (· - ·) Float.Model.UnpackedFloat.sub sseBinOp_sub_wp
      x64Subps_fallsTo hc hpaV hdV hhold hwp
  | mkpair _ _ =>
    rcases vs with ⟨va, vb, ⟨⟩⟩
    exact x64EmitMkpair_spec hc _hpaG hpaV hdV hhold hwp
  | unpair _ _ =>
    rcases vs with ⟨v, ⟨⟩⟩
    exact x64EmitUnpair_spec hc hpaV hdG hdV hhold hwp
  | _ => dsimp only [x64VopIns] at hc; cases hc

end OpSpecs

/-! ## 4. `NoLab` theorems and `x64VecSpec : VecTarget` -/

section NoLab

theorem x64Vop_noLab {sig rs : List Ty} {code : OpCode sig rs}
    {pas : Tup (PArg Reg64 RegMm CondCode) sig} {dsts : Tup (PDst Reg64 RegMm CondCode) rs}
    {vh : VariantHint} {c : List Directive} {clob : FlagMask}
    (h : x64Vop code pas dsts vh = some (c, clob)) (l : Sym) :
    Kraken.Directive.label l ∉ c :=
  emitCleanPair_noLab h l

end NoLab

/-- Certified `VecTarget` instance for SysV x64 (`x64Vec`). -/
theorem x64VecSpec :
    VecTarget x64Mach x64Vec x64CondReads x64Frame.sp x64Scratch x64FrameSpec.spOk where
  vecScratch_disj := x64Vec_disj
  vecArgRegs_nodup := x64VecArgRegs_nodup
  vecRetRegs_nodup := x64VecRetRegs_nodup
  abiVec_slot := x64AbiVec_slot
  vmov_spec := x64Vmov_spec
  vmovi_spec := x64Vmovi_spec
  vslotSt_spec := x64VslotSt_spec
  vslotLd_spec := x64VslotLd_spec
  vop_spec := fun {_ _ _ _ _ _ _ vh _ _ _ _ _ _} hc =>
    x64Vop_spec (vh := vh) hc
  vload_spec := x64Vload_spec
  vstore_spec := x64Vstore_spec

/-! ## 5. Kernel `rfl` `ParserChecks` (`Kraken.X64.Parser`) -/

section ParserChecks

open Kraken.X64.Parser

private theorem parser_evex_rfl :
    ⸨prog| vmovdqu32 %xmm1, %xmm0 ⸩ = x64Vec.vmov .w128 .mm0 .mm1 ∧
    ⸨prog| vmovdqu32 %ymm1, %ymm0 ⸩ = x64Vec.vmov .w256 .mm0 .mm1 ∧
    ⸨prog| vmovdqu32 %zmm1, %zmm0 ⸩ = x64Vec.vmov .w512 .mm0 .mm1 ∧
    some (⸨prog| vpaddd %ymm2, %ymm1, %ymm0 ⸩, maskNone) =
      x64Vec.vop (.add v8i32) (.vec .mm1, .vec .mm2, ()) (.vec .mm0, ()) .default ∧
    some (⸨prog| vprord $7, %xmm1, %xmm0 ⸩, maskNone) =
      x64Vec.vop (.rotr v4i32) (.vec .mm1, .imm ((7#32, 7#32), (7#32, 7#32)), ())
        (.vec .mm0, ()) .default ∧
    some (⸨prog| vpternlogd $0xca, %xmm2, %xmm1, %xmm0 ⸩, maskNone) =
      x64Vec.vop (.ternlog v4i32 0xca#8) (.vec .mm0, .vec .mm1, .vec .mm2, ())
        (.vec .mm0, ()) .default ∧
    some ⸨prog| vpternlogd $0x00, %ymm0, %ymm0, %ymm0 ⸩ =
      x64Vec.vmovi .w256 .mm0 (BitVec.zero 512) ∧
    some ⸨prog| vpternlogd $0xff, %ymm0, %ymm0, %ymm0 ⸩ =
      x64Vec.vmovi .w256 .mm0 ((BitVec.allOnes 256).setWidth 512) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem parser_sse_mem_bridge_rfl :
    some (⸨prog| pshufd $0x4e, %xmm1, %xmm0 ⸩, maskNone) =
      x64Vec.vop (.shufd v4i32 0x4e#8) (.vec .mm1, ()) (.vec .mm0, ()) .default ∧
    some (⸨prog| pshufb %xmm1, %xmm0 ⸩, maskNone) =
      x64Vec.vop (.shufb v4i32) (.vec .mm0, .vec .mm1, ()) (.vec .mm0, ()) .default ∧
    some (⸨prog| palignr $8, %xmm1, %xmm0 ⸩, maskNone) =
      x64Vec.vop (OpCode.alignr v4i32 8#8) (.vec .mm0, .vec .mm1, ()) (.vec .mm0, ()) .default ∧
    some (⸨prog| pblendw $0xf0, %xmm1, %xmm0 ⸩, maskNone) =
      x64Vec.vop (.blendw v4i32 0xf0#8) (.vec .mm0, .vec .mm1, ()) (.vec .mm0, ()) .default ∧
    some (⸨prog| addps %xmm1, %xmm0 ⸩, maskNone) =
      x64Vec.vop (.fadd v4f32) (.vec .mm0, .vec .mm1, ()) (.vec .mm0, ()) .default ∧
    some (⸨prog| subps %xmm1, %xmm0 ⸩, maskNone) =
      x64Vec.vop (.fsub v4f32) (.vec .mm0, .vec .mm1, ()) (.vec .mm0, ()) .default ∧
    ⸨prog| vmovdqu32 %xmm0, (%rsp) ⸩ = x64Vec.vslotSt .w128 0 .mm0 ∧
    ⸨prog| vmovdqu32 16(%rsp), %xmm0 ⸩ = x64Vec.vslotLd .w128 .mm0 2 ∧
    ⸨prog| vmovq %xmm0, (%rsp); vmovq (%rsp), %xmm1 ⸩ =
      x64Vec.vslotSt .w64 0 .mm0 ++ x64Vec.vslotLd .w64 .mm1 0 ∧
    ⸨prog| movabs $4294967296, %r10; vmovdqu32 (%rsp, %r10, 1), %ymm0 ⸩ =
      x64Vec.vslotLd .w256 .mm0 (2 ^ 29) ∧
    some (⸨prog| movabs $2147483648, %r10; leaq (%rbx, %r10, 1), %r10; vmovdqu32 (%r10), %xmm0 ⸩,
      maskNone) =
      x64Vec.vload v4i32 .mm0 (.baseDisp .rbx 2147483648) ∧
    some (
    ⸨prog| movl %edi, %r10d; movl %esi, %r11d; shlq $32, %r11; orq %r11, %r10; vmovq %r10, %xmm0 ⸩,
      maskAll) =
      x64Vec.vop (.mkpair i32 i32) (.gpr .rdi, .gpr .rsi, ()) (.vec .mm0, ()) .default ∧
    some (⸨prog| pshufd $0x4e, %xmm0, %xmm14; vmovq %xmm0, %xmm1; vmovq %xmm14, %xmm2 ⸩, maskNone) =
      x64Vec.vop (.unpair (Ty.vec 1 i32) (Ty.vec 1 i32)) (.vec .mm0, ())
        (.vec .mm1, .vec .mm2, ()) .default ∧
    some (⸨prog| vmovq %xmm0, %r10; movl %r10d, %eax; shrq $32, %r10; movl %r10d, %edx ⸩, maskAll) =
      x64Vec.vop (.unpair i32 i32) (.vec .mm0, ()) (.gpr .rax, .gpr .rdx, ()) .default := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end ParserChecks

end LeanQbe.T.Amd64
