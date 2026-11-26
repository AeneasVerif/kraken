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

private theorem ternlog_1vec_wp [Host] (w : SlotWidth) {t : Ty} (ht : t.size = w.bits)
    {vd r : RegMm} {c : List Instr} {f0 f1 : BitVec 512}
    {xv rhs : BitVec t.size} {s : MachineData}
    (hc : x64EmitTernlog1VecIns w vd r f0 f1 = some c) (hvd : vd ∉ x64VecScratch)
    (hr : (s.zmms.get512 r).setWidth w.bits = xv.setWidth w.bits)
    (hbit : ∀ i, i < t.size → i < 512 →
      ((xv.getLsbD i && (f1.getLsbD i ^^ f0.getLsbD i)) ^^ f0.getLsbD i) = rhs.getLsbD i) :
    @Program.wp _ (emitClean c) (fun s' => VecStepFrame vd s s' ∧
      (s'.zmms.get512 vd).setWidth t.size = rhs) (fun _ _ => False) s := by
  refine Program.wp.mono (x64EmitTernlog1Vec_wp w (x := xv.setWidth 512) hc hvd
    (by rw [hr, BitVec.setWidth_setWidth_of_le _ w.bits_le_512])) ?_
  rintro s' ⟨hf, hvd'⟩; refine ⟨hf, ?_⟩
  rw [← ht] at hvd'; rw [hvd']
  exact ternlog_1vec_finish (ht ▸ w.bits_le_512) fun i hi hi512 => by
    rw [BitVec.getLsbD_setWidth]
    simpa only [hi512, decide_true, Bool.true_and] using hbit i hi hi512

private theorem ternlog_1vec_bit {n : Nat} {va vb vc x : BitVec n} {f0 f1 : BitVec 512}
    {imm : BitVec 8} {i : Nat} (hi : i < n) (hi512 : i < 512) {a0 b0 c0 a1 b1 c1 : BitVec 512}
    (hf0 : f0 = BitVec.ternaryLogic a0 b0 c0 imm) (hf1 : f1 = BitVec.ternaryLogic a1 b1 c1 imm)
    (h0 : x.getLsbD i = false →
      a0.getLsbD i = va.getLsbD i ∧ b0.getLsbD i = vb.getLsbD i ∧ c0.getLsbD i = vc.getLsbD i)
    (h1 : x.getLsbD i = true →
      a1.getLsbD i = va.getLsbD i ∧ b1.getLsbD i = vb.getLsbD i ∧ c1.getLsbD i = vc.getLsbD i) :
    ((x.getLsbD i && (f1.getLsbD i ^^ f0.getLsbD i)) ^^ f0.getLsbD i) =
      (BitVec.ternaryLogic va vb vc imm).getLsbD i := by
  subst hf0 hf1
  rw [getLsbD_ternaryLogic _ _ _ imm i hi512, getLsbD_ternaryLogic _ _ _ imm i hi512,
    getLsbD_ternaryLogic _ _ _ imm i hi]
  cases hx : x.getLsbD i
  · obtain ⟨ha, hb, hc⟩ := h0 hx; simp [ha, hb, hc]
  · obtain ⟨ha, hb, hc⟩ := h1 hx; simp [ha, hb, hc]

private theorem ternlog_2vec_imm14_wp [Host] (w : SlotWidth) {t : Ty} (ht : t.size = w.bits)
    {vd ra rx : RegMm} {imm : BitVec 8} {ci : BitVec t.size} {pimm : List Instr}
    {va vx : BitVec t.size} {s : MachineData} (swap : Bool)
    (hv : x64VmoviWithIns .mm15 w .mm14 (ci.setWidth 512) = some pimm)
    (hvd : vd ∉ x64VecScratch) (hra : ra ∉ x64VecScratch) (hrx : rx ∉ x64VecScratch)
    (ha : (s.zmms.get512 ra).setWidth w.bits = va.setWidth w.bits)
    (hx : (s.zmms.get512 rx).setWidth w.bits = vx.setWidth w.bits) :
    @Program.wp _ (emitClean (if ra == vd then pimm ++ [x64TernlogI w vd
          (if swap then .mm14 else rx) (if swap then rx else .mm14) imm]
        else if rx != vd then pimm ++ x64VmovIns w vd ra ++ [x64TernlogI w vd
          (if swap then .mm14 else rx) (if swap then rx else .mm14) imm]
        else pimm ++ x64VmovIns w .mm15 vd ++ x64VmovIns w vd ra ++ [x64TernlogI w vd
          (if swap then .mm14 else .mm15) (if swap then .mm15 else .mm14) imm]))
      (fun s' => VecStepFrame vd s s' ∧ (s'.zmms.get512 vd).setWidth t.size =
        if swap then BitVec.ternaryLogic va ci vx imm else BitVec.ternaryLogic va vx ci imm)
      (fun _ _ => False) s := by
  have h14d : (.mm14 : RegMm) ≠ vd := (ne_of_not_mem_x64VecScratch hvd).1.symm
  have h145 : (.mm14 : RegMm) ≠ .mm15 := by decide
  have h154 : (.mm15 : RegMm) ≠ .mm14 := by decide
  rw [show emitClean _ = emitClean pimm ++ (if ra == vd then [x64TernlogD w vd
          (if swap then .mm14 else rx) (if swap then rx else .mm14) imm]
        else if (if swap then .mm14 else rx) != vd &&
            (if swap then rx else .mm14) != vd then
          x64Vmov w vd ra ++ [x64TernlogD w vd
            (if swap then .mm14 else rx) (if swap then rx else .mm14) imm]
        else x64Vmov w .mm15 vd ++ x64Vmov w vd ra ++ [x64TernlogD w vd
          (if (if swap then .mm14 else rx) == vd then .mm15 else (if swap then .mm14 else rx))
          (if (if swap then rx else .mm14) == vd then .mm15 else (if swap then rx else .mm14))
          imm]) from by
    cases swap <;>
      simp only [emitClean_ite, emitClean_append, emitClean_cons, emitClean_nil,
        bne, Bool.false_eq_true, ↓reduceIte, x64TernlogD, x64Vmov] <;>
      (by_cases h1 : ra = vd
       · simp [regMm_beq_true h1]
       · by_cases h2 : rx = vd <;>
           simp [regMm_beq_false h1, regMm_beq_true, regMm_beq_false,
             regMm_beq_false h14d, h2, List.append_assoc])]
  refine Program.wp.append (x64Vmovi_step .mm15 w .mm14 vd (by simp [x64VecScratch])
    (by simp [x64VecScratch]) h154 _ hv s) ?_
  rintro s1 ⟨hf1, hz1, h14⟩
  have hrx1 : s1.zmms.get512 rx = s.zmms.get512 rx :=
    hz1 rx (ne_of_not_mem_x64VecScratch hrx).1 (ne_of_not_mem_x64VecScratch hrx).2
  have hra1 : s1.zmms.get512 ra = s.zmms.get512 ra :=
    hz1 ra (ne_of_not_mem_x64VecScratch hra).1 (ne_of_not_mem_x64VecScratch hra).2
  have h14' : (s1.zmms.get512 .mm14).setWidth w.bits = ci.setWidth w.bits := by
    rw [h14, BitVec.setWidth_setWidth_of_le _ w.bits_le_512]
  cases swap with
  | false =>
    refine Program.wp.mono (ternlog_3reg_wp w ht hvd hra (ne_of_not_mem_x64VecScratch hrx).2 h145
      (by rw [hra1]; exact ha)
      (by simp only [Bool.false_eq_true, ↓reduceIte]; rw [hrx1]; exact hx) h14')
      (fun s' ⟨hf2, hres⟩ => ⟨hf1.trans hf2, hres⟩)
  | true =>
    refine Program.wp.mono (ternlog_3reg_wp w ht hvd hra h145 (ne_of_not_mem_x64VecScratch hrx).2
      (by rw [hra1]; exact ha) h14'
      (by simp only [↓reduceIte]; rw [hrx1]; exact hx))
      (fun s' ⟨hf2, hres⟩ => ⟨hf1.trans hf2, hres⟩)

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
    | none => rw [hv] at hc; cases hc
    | some pimm =>
      rw [hv] at hc; simp only [Option.map_some, Option.some.injEq] at hc; subst hc
      simpa only [Bool.false_eq_true, ↓reduceIte] using
        ternlog_2vec_imm14_wp w ht (imm := imm) false hv hvd hra hrb (swHold hha) (swHold hhb)
  · -- .vec, .imm, .vec
    rename_i ra cb rc
    rcases hhb with rfl
    have hra := hpaV ra (by dsimp only [pargVecs]; exact List.mem_cons_self)
    have hrc := hpcV rc (by dsimp only [pargVecs]; exact List.mem_cons_self)
    dsimp only [x64EmitTernlogIns] at hc
    cases hv : x64VmoviWithIns .mm15 w .mm14 ((toBits t cb).setWidth 512) with
    | none => rw [hv] at hc; cases hc
    | some pimm =>
      rw [hv] at hc; simp only [Option.map_some, Option.some.injEq] at hc; subst hc
      simpa only [↓reduceIte] using
        ternlog_2vec_imm14_wp w ht (imm := imm) true hv hvd hra hrc (swHold hha) (swHold hhc)
  · -- .vec, .imm, .imm
    rename_i ra cb cc
    rcases hhb with rfl; rcases hhc with rfl
    dsimp only [x64EmitTernlogIns] at hc
    refine ternlog_1vec_wp w ht hc hvd (swHold hha) fun i hi hi512 => ?_
    rw [t_ternaryLogic_eq]
    exact ternlog_1vec_bit hi hi512 rfl rfl
      (fun hx => by
        simp only [hx, BitVec.getLsbD_zero, BitVec.getLsbD_setWidth,
          hi512, decide_true, Bool.true_and, and_self])
      (fun hx => by
        simp only [hx, BitVec.getLsbD_allOnes, BitVec.getLsbD_setWidth,
          hi512, decide_true, Bool.true_and, and_self])
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
        refine Program.wp.mono (x64TernlogD_step_ty w ht vd rb rc _ _ _ imm s1
          (by rw [hvd1, BitVec.setWidth_setWidth_of_le _ w.bits_le_512])
          (by rw [hz1 rb hbc.1 (ne_of_not_mem_x64VecScratch hrb).1, swHold hhb])
          (by rw [hz1 rc hbc.2 (ne_of_not_mem_x64VecScratch hrc).1, swHold hhc])) ?_
        rintro s' ⟨hf2, hres⟩; exact ⟨hf1.trans hf2, hres⟩
      · have hnot : (rb != vd && rc != vd) = false := by
          by_cases h1 : rb = vd
          · simp [bne, regMm_beq_true h1]
          · by_cases h2 : rc = vd
            · simp [bne, regMm_beq_true h2]
            · exact absurd ⟨h1, h2⟩ hbc
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
          · subst r
            simp only [regMm_beq_true rfl, ↓reduceIte, hz2 .mm15 h15d h145.symm, h15, swHold hh]
          · simp only [regMm_beq_false hrd, Bool.false_eq_true, ↓reduceIte,
              hz2 r hrd (ne_of_not_mem_x64VecScratch hr).1,
              hz1 r (ne_of_not_mem_x64VecScratch hr).2, swHold hh]
        refine Program.wp.mono (x64TernlogD_step_ty w ht vd _ _ _ _ _ imm s2
          (by rw [hvd2, BitVec.setWidth_setWidth_of_le _ w.bits_le_512])
          (hsrc rb vb hrb hhb) (hsrc rc vc hrc hhc)) ?_
        rintro s' ⟨hf3, hres⟩; exact ⟨(hf1.trans hf2).trans hf3, hres⟩
  · -- .imm, .vec, .imm
    rename_i ca rb cc
    rcases hha with rfl; rcases hhc with rfl
    dsimp only [x64EmitTernlogIns] at hc
    refine ternlog_1vec_wp w ht hc hvd (swHold hhb) fun i hi hi512 => ?_
    rw [t_ternaryLogic_eq]
    exact ternlog_1vec_bit hi hi512 rfl rfl
      (fun hx => by
        simp only [hx, BitVec.getLsbD_zero, BitVec.getLsbD_setWidth,
          hi512, decide_true, Bool.true_and, and_self])
      (fun hx => by
        simp only [hx, BitVec.getLsbD_allOnes, BitVec.getLsbD_setWidth,
          hi512, decide_true, Bool.true_and, and_self])
  · -- .imm, .imm, .vec
    rename_i ca cb rc
    rcases hha with rfl; rcases hhb with rfl
    dsimp only [x64EmitTernlogIns] at hc
    refine ternlog_1vec_wp w ht hc hvd (swHold hhc) fun i hi hi512 => ?_
    rw [t_ternaryLogic_eq]
    exact ternlog_1vec_bit hi hi512 rfl rfl
      (fun hx => by
        simp only [hx, BitVec.getLsbD_zero, BitVec.getLsbD_setWidth,
          hi512, decide_true, Bool.true_and, and_self])
      (fun hx => by
        simp only [hx, BitVec.getLsbD_allOnes, BitVec.getLsbD_setWidth,
          hi512, decide_true, Bool.true_and, and_self])
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

private theorem withWide_elim {t : Ty} (dsts : Tup (PDst Reg64 RegMm CondCode) [t])
    {f : SlotWidth → RegMm → Option (List Instr)} {c : List Instr} {clob : FlagMask}
    (hc : (match x64VecSlotWidth t, dsts with
      | some w, (.vec vd, ()) => if w == .w64 then none else (f w vd).map (·, maskNone)
      | _, _ => none) = some (c, clob)) :
    ∃ (w : SlotWidth) (vd : RegMm) (c0 : List Instr),
      x64VecSlotWidth t = some w ∧ w ≠ .w64 ∧ dsts = (.vec vd, ()) ∧
      f w vd = some c0 ∧ c = c0 ∧ clob = maskNone := by
  rcases dsts with ⟨d, ⟨⟩⟩
  cases hw : x64VecSlotWidth t with
  | none => rw [hw] at hc; cases d <;> cases hc
  | some w =>
    rw [hw] at hc
    cases d with
    | gpr _ | flag _ => cases hc
    | vec vd =>
      by_cases hw64 : w = .w64
      · subst hw64; dsimp only at hc; cases hc
      · have hb : (w == .w64) = false := by cases w <;> first | exact absurd rfl hw64 | rfl
        dsimp only at hc; rw [hb] at hc
        simp only [Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff, Prod.mk.injEq] at hc
        obtain ⟨c0, hc0, rfl, rfl⟩ := hc
        exact ⟨w, vd, c0, rfl, hw64, rfl, hc0, rfl, rfl⟩

private theorem avx_fallsTo_frame {w : SlotWidth}
    {dd : RegMm} {ins : Instr} {v : BitVec (x64AwOf w).bits} {val512 : BitVec 512}
    {st : MachineData}
    (hv : v.setWidth 512 = val512)
    (h : Directive.FallsTo (.instr ins) st
      (fun st' => st' = { st with zmms := st.zmms.set (x64AvxRegOf w dd) v })) :
    Directive.FallsTo (.instr ins) st (fun st' =>
      st'.dmem = st.dmem ∧ st'.status = st.status ∧ st'.regs = st.regs ∧
      (∀ vr, vr ≠ dd → st'.zmms.get512 vr = st.zmms.get512 vr) ∧
      st'.zmms.get512 dd = val512) := by
  refine fallsTo_mono h ?_
  rintro st' rfl
  refine ⟨rfl, rfl, rfl, fun vr hvr => RegZmms.get512_set_avx_of_ne _ w hvr.symm _, ?_⟩
  rw [RegZmms.get512_set_avx_same, hv]

private theorem xmm_fallsTo_frame {dd : RegMm} {ins : Instr} {v : BitVec 128} {st : MachineData}
    (h : Directive.FallsTo (.instr ins) st
      (fun st' => st' = { st with zmms := st.zmms.setLegacy (.xmm dd) v })) :
    Directive.FallsTo (.instr ins) st (fun st' =>
      st'.dmem = st.dmem ∧ st'.status = st.status ∧ st'.regs = st.regs ∧
      (∀ vr, vr ≠ dd → st'.zmms.get512 vr = st.zmms.get512 vr) ∧
      st'.zmms.get512 dd = (st.zmms.get512 dd).replaceLow v) := by
  refine fallsTo_mono h ?_
  rintro st' rfl
  refine ⟨rfl, rfl, rfl, fun vr hvr => RegZmms.get512_setLegacy_xmm_of_ne _ hvr.symm _, ?_⟩
  rw [RegZmms.get512_setLegacy_xmm]

private theorem mapLanes32_cast {p q : Nat} (f : BitVec 32 → BitVec 32) (h : p = q) (x : BitVec p) :
    (x.mapLanes 32 f).cast h = (x.cast h).mapLanes 32 f := by
  subst h; rfl

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
  cases hokv : ok <;> rw [hokv] at hc
  · cases hc
  · cases d with
    | gpr _ | flag _ => cases hc
    | vec vd =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        Option.map_eq_some_iff, Prod.mk.injEq] at hc
      obtain ⟨c0, hc0, rfl, rfl⟩ := hc
      have ht : t.size = 128 := hok hokv
      rcases hhold with _ | ⟨hha, _ | ⟨hhb, _⟩⟩
      refine ⟨vd, ht, rfl, rfl, rfl, ?_⟩
      refine Program.wp.mono (x64EmitBinInPlace_wp .w128 ht
          (upd := fun old x y => old.replaceLow (f x y))
          (res := fun x y => (f x y).cast ht.symm)
          (fun old x y => by
            rw [← BitVec.setWidth_setWidth_of_le (old.replaceLow (f x y)) (by omega : t.size ≤ 128),
              setWidth_replaceLow (by decide), setWidth_of_eq ht.symm])
          (fun dd src st => xmm_fallsTo_frame (hemit dd src st))
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

private theorem toBits_pair64_eq {a b : Ty} (heq : a = b) (ha : a.size = 64)
    (va : Val a) (vb : Val b) :
    (toBits (.pair a b) (va, vb)).cast (by simp [Ty.size, ← heq, ha] : (Ty.pair a b).size = 128) =
      ((toBits b vb).cast (heq ▸ ha : b.size = 64) ++ (toBits a va).cast ha).cast
        (by decide : 64 + 64 = 128) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_cast, toBits, BitVec.getLsbD_append]
  by_cases hlt : i < a.size
  · simp [hlt, show i < 64 by omega]
  · simp [hlt, show ¬(i < 64) by omega, show i - a.size = i - 64 by omega]

private theorem x64EmitMkpair_dstVec {a b : Ty} {pas : Tup (PArg Reg64 RegMm CondCode) [a, b]}
    {dsts : Tup (PDst Reg64 RegMm CondCode) [.pair a b]} {c : List Instr} {clob : FlagMask}
    (hc : x64EmitMkpairIns pas dsts = some (c, clob)) :
    ∃ vd, dsts = (.vec vd, ()) := by
  rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨d, ⟨⟩⟩
  cases d with
  | vec vd => exact ⟨vd, rfl⟩
  | gpr _ =>
    exfalso
    cases a with
    | bool | float _ | pair _ _ => cases hc
    | bits na =>
      by_cases ha : na = 32
      · subst na; cases b with
        | bool | float _ | pair _ _ => cases hc
        | bits nb =>
          by_cases hb : nb = 32
          · subst nb; cases hc
          · unfold x64EmitMkpairIns x64EmitMkpairIns.match_1 at hc
            simp only [dite_eq_right (fun h => absurd h hb)] at hc; cases hc
      · unfold x64EmitMkpairIns x64EmitMkpairIns.match_1 at hc
        simp only [dite_eq_right (fun h => absurd h ha)] at hc; cases hc

private theorem x64EmitMkpair_subvec_aux {a b : Ty} (h32 : ¬(a = .bits 32 ∧ b = .bits 32))
    {pa : PArg Reg64 RegMm CondCode a} {pb : PArg Reg64 RegMm CondCode b} {vd : RegMm}
    {c : List Instr} {clob : FlagMask}
    (hc : x64EmitMkpairIns (pa, pb, ()) (.vec vd, ()) = some (c, clob)) :
    ∃ (h : a = b ∧ x64IsBridgeSubVec a ∧ a.size = 64),
      ((x64LoadSubVec64Ins h.2.2 .mm14 pa).bind fun la =>
        (x64LoadSubVec64Ins (h.1 ▸ h.2.2 : b.size = 64) vd pb).bind fun lb =>
          some (la ++ lb ++ [x64Avx128I (.pshufd (.avx (.xmm vd)) (.avx (.xmm vd)) (.int64 0x4e)),
            x64TernlogI .w128 vd .mm14 .mm14 0xFE], maskNone)) = some (c, clob) := by
  have hsub : (if h : a = b ∧ x64IsBridgeSubVec a ∧ a.size = 64 then
      (x64LoadSubVec64Ins h.2.2 .mm14 pa).bind fun la =>
        (x64LoadSubVec64Ins (h.1 ▸ h.2.2 : b.size = 64) vd pb).bind fun lb =>
          some (la ++ lb ++ [x64Avx128I (.pshufd (.avx (.xmm vd)) (.avx (.xmm vd)) (.int64 0x4e)),
            x64TernlogI .w128 vd .mm14 .mm14 0xFE], maskNone) else none) = some (c, clob) := by
    cases a with
    | bool | float _ | pair _ _ => exact hc
    | bits na =>
      by_cases ha : na = 32
      · subst na; cases b with
        | bool | float _ | pair _ _ => exact hc
        | bits nb =>
          by_cases hb : nb = 32
          · subst nb; exact absurd ⟨rfl, rfl⟩ h32
          · unfold x64EmitMkpairIns x64EmitMkpairIns.match_1 at hc
            simp only [dite_eq_right (fun h => absurd h hb)] at hc; exact hc
      · unfold x64EmitMkpairIns x64EmitMkpairIns.match_1 at hc
        simp only [dite_eq_right (fun h => absurd h ha)] at hc; exact hc
  by_cases hcond : a = b ∧ x64IsBridgeSubVec a ∧ a.size = 64
  · simp only [eq_true hcond, ↓reduceDIte] at hsub; exact ⟨hcond, hsub⟩
  · simp only [eq_false hcond, ↓reduceDIte] at hsub; cases hsub

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
  obtain ⟨vd, hdv⟩ := x64EmitMkpair_dstVec hc
  rcases pas with ⟨pa, pb, ⟨⟩⟩; subst hdv
  have hvd : vd ∉ x64VecScratch := hdV vd (by simp [tupDstVecs, tupFlatMap, PDst.vecs])
  have h14d : (.mm14 : RegMm) ≠ vd := (ne_of_not_mem_x64VecScratch hvd).1.symm
  rcases hhold with _ | ⟨hha, hrest⟩
  rcases hrest with _ | ⟨hhb, _⟩
  by_cases h32 : a = .bits 32 ∧ b = .bits 32
  · rcases h32 with ⟨rfl, rfl⟩
    change Option.bind (x64LoadI32ToGprIns .r10 pa) (fun la =>
      Option.bind (x64LoadI32ToGprIns .r11 pb) (fun lb =>
        some (la ++ lb ++ [insI (.shl (↑(q .r11)) (.imm8 (.int64 32))),
          insI (.or (↑(q .r10)) (.reg (q .r11))),
          x64Avx128I (.vmovIn .W64 (.xmm vd) ↑(q .r10))], maskAll))) =
      some (c, clob) at hc
    cases hla : x64LoadI32ToGprIns .r10 pa with
    | none => rw [hla] at hc; cases hc
    | some la =>
      cases hlb : x64LoadI32ToGprIns .r11 pb with
      | none => rw [hla, hlb] at hc; cases hc
      | some lb =>
        rw [hla, hlb] at hc
        simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hc
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
        have h10_4 : s4.regs.get64 .r10 = (vb ++ va).cast (by decide : 32 + 32 = 64) := by
          rw [hr4, Reg64s.get64_set64_same, hr3, Reg64s.get64_set64_of_ne _ _ _ _ (by decide),
            hg2 .r10 (by decide), h10_1, Reg64s.get64_set64_same, h11_2, mkpair32_bits]
        have hvd_out : x64Mach.PDstHolds s' (.pair i32 i32) (.vec vd) (va, vb) := by
          refine ⟨by decide, ?_⟩
          change (s'.zmms.get512 vd).setWidth 64 = toBits (.pair i32 i32) (va, vb)
          rw [hs']; dsimp only [toBits]
          rw [RegZmms.get512_set_xmm_same,
            BitVec.setWidth_setWidth_of_le _ (by decide : 64 ≤ 512),
            BitVec.setWidth_setWidth_of_le _ (by decide : 64 ≤ 128), BitVec.setWidth_eq, h10_4]
        refine ⟨⟨⟨((va, vb), ()), hwp, TRel.cons hvd_out .nil⟩,
            by change s'.dmem = s.dmem; rw [hs']; dsimp only; rw [hd4, hd3, hd2, hd1]⟩,
          vecFrame_upd (fun r hrm => by
              have hr10 : r ≠ .r10 := fun e => hrm (by simp [e, x64Scratch])
              have hr11 : r ≠ .r11 := fun e => hrm (by simp [e, x64Scratch])
              rw [hs']; dsimp only
              rw [hr4, Reg64s.get64_set64_of_ne _ _ _ _ hr10.symm,
                hr3, Reg64s.get64_set64_of_ne _ _ _ _ hr11.symm, hg2 r hr11, hg1 r hr10])
            (fun vr hvm => by
              have hv : vr ≠ vd := fun e => hvm (by simp [e, tupDstVecs, tupFlatMap, PDst.vecs])
              rw [hs']; dsimp only
              rw [RegZmms.get512_set_xmm_of_ne _ hv.symm, hz4, hz3, hz2, hz1])
            (Or.inl rfl)⟩
  · obtain ⟨hcond, hc'⟩ := x64EmitMkpair_subvec_aux h32 hc
    have hb64 : b.size = 64 := hcond.1 ▸ hcond.2.2
    cases hla : x64LoadSubVec64Ins hcond.2.2 .mm14 pa with
    | none => rw [hla] at hc'; cases hc'
    | some la =>
      cases hlb : x64LoadSubVec64Ins hb64 vd pb with
      | none => rw [hla, hlb] at hc'; cases hc'
      | some lb =>
        rw [hla, hlb] at hc'
        simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hc'
        rcases hc' with ⟨rfl, rfl⟩
        have hle : (Ty.pair a b).size ≤ 512 := by simp only [Ty.size]; omega
        refine vecOpFallsTo_P hle hwp ?_
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
        refine ⟨((hf1.trans hf2).trans hf3).trans hf4, ?_⟩
        have hsz128 : (Ty.pair a b).size = 128 := by simp only [Ty.size, ← hcond.1, hcond.2.2]
        change (s'.zmms.get512 vd).setWidth (Ty.pair a b).size = toBits (Ty.pair a b) (va, vb)
        change (s'.zmms.get512 vd).setWidth 128 = _ at hvd'
        rw [← BitVec.setWidth_setWidth_of_le (s'.zmms.get512 vd)
            (by omega : (Ty.pair a b).size ≤ 128),
          hvd', RegZmms.get512_setLegacy_xmm_of_ne _ h14d.symm, RegZmms.get512_setLegacy_xmm,
          setWidth_replaceLow (by decide), hz2 .mm14 h14d, hvd2, h14_1, ternaryLogic_or,
          shufd_0x4e_combine128, ← toBits_pair64_eq hcond.1 hcond.2.2 va vb]
        apply BitVec.eq_of_getLsbD_eq; intro i hi
        simp [show i < (Ty.pair a b).size from hi]

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

private theorem x64EmitUnpair_none_of_dst {a b : Ty}
    (pa : PArg Reg64 RegMm CondCode (.pair a b))
    (d0 : PDst Reg64 RegMm CondCode a) (d1 : PDst Reg64 RegMm CondCode b)
    (hgpr : ¬(a = .bits 32 ∧ b = .bits 32 ∧ ∃ r0 r1, d0 = .gpr r0 ∧ d1 = .gpr r1))
    (hvec : ¬(∃ v0 v1, d0 = .vec v0 ∧ d1 = .vec v1)) :
    x64EmitUnpairIns (pa, ()) (d0, d1, ()) = none := by
  cases a with
  | bool | float _ | pair _ _ =>
    cases d0 <;> cases d1 <;> first | exact absurd ⟨_, _, rfl, rfl⟩ hvec | rfl
  | bits na =>
    by_cases ha : na = 32
    · subst na; cases b with
      | bool | float _ | pair _ _ =>
        cases d0 <;> cases d1 <;> first | exact absurd ⟨_, _, rfl, rfl⟩ hvec | rfl
      | bits nb =>
        by_cases hb : nb = 32
        · subst nb
          cases d0 <;> cases d1 <;> first
            | exact absurd ⟨rfl, rfl, _, _, rfl, rfl⟩ hgpr
            | exact absurd ⟨_, _, rfl, rfl⟩ hvec
            | rfl
        · cases d0 <;> cases d1 <;> first
            | exact absurd ⟨_, _, rfl, rfl⟩ hvec
            | (unfold x64EmitUnpairIns x64EmitUnpairIns.match_3
               simp only [dite_eq_right (fun h => absurd h hb)]; rfl)
    · cases d0 <;> cases d1 <;> first
        | exact absurd ⟨_, _, rfl, rfl⟩ hvec
        | rfl
        | (unfold x64EmitUnpairIns x64EmitUnpairIns.match_3
           simp only [dite_eq_right (fun h => absurd h ha)]; try rfl)

private theorem x64EmitUnpair_vec_eq {a b : Ty} (pa : PArg Reg64 RegMm CondCode (.pair a b))
    (v0 v1 : RegMm) :
    x64EmitUnpairIns (pa, ()) (.vec v0, .vec v1, ()) =
      if v0 == v1 then none
      else if h : a = b ∧ x64IsBridgeSubVec a ∧ a.size = 64 then
        match pa with
        | .vec vs =>
          some ([x64Avx128I (.pshufd (.avx (.xmm .mm14)) (.avx (.xmm vs)) (.int64 0x4e)),
            x64Avx128I (.vmovq (.xmm v0) (.xmm vs)),
            x64Avx128I (.vmovq (.xmm v1) (.xmm .mm14))], maskNone)
        | .imm c =>
          some (x64Movi64Ins v0 (BitVec.cast h.2.2 (toBits a c.1)) ++
            x64Movi64Ins v1 (BitVec.cast (h.1 ▸ h.2.2) (toBits b c.2)), maskNone)
        | _ => none
      else none := by
  cases a with
  | bool | float _ | pair _ _ => rfl
  | bits na =>
    by_cases ha : na = 32
    · subst na; cases b with
      | bool | float _ | pair _ _ => rfl
      | bits nb =>
        by_cases hb : nb = 32
        · subst nb; rfl
        · unfold x64EmitUnpairIns x64EmitUnpairIns.match_3
          simp only [dite_eq_right (fun h => absurd h hb)]; rfl
    · unfold x64EmitUnpairIns x64EmitUnpairIns.match_3
      simp only [dite_eq_right (fun h => absurd h ha)]; rfl

private theorem pDstHolds_gpr32 {s : MachineData} {r : Reg64} {v : BitVec 32}
    (h : (s.regs.get64 r).setWidth 32 = v) : x64Mach.PDstHolds s i32 (.gpr r) v :=
  ⟨by decide, h⟩

private theorem zmms_set_xmm64_width {zm : RegZmms} {v : RegMm} {x : BitVec 512}
    {sz : Nat} (hsz : sz ≤ 64) :
    ((zm.set (.xmm v) ((x.setWidth 64).setWidth 128)).get512 v).setWidth sz = x.setWidth sz := by
  rw [RegZmms.get512_set_xmm_same, BitVec.setWidth_setWidth_of_le _ (by omega : sz ≤ 512),
    BitVec.setWidth_setWidth_of_le _ (by omega : sz ≤ 128), BitVec.setWidth_setWidth_of_le _ hsz]

private theorem pDstHolds_vec64 {s : MachineData} {t : Ty} (ht : t.size = 64)
    {v : RegMm} (c : Val t)
    (h : s.zmms.get512 v = (((toBits t c).cast ht).setWidth 128).setWidth 512) :
    x64Mach.PDstHolds s t (.vec v) c := by
  refine ⟨by omega, ?_⟩
  change (s.zmms.get512 v).setWidth t.size = toBits t c
  rw [h, BitVec.setWidth_setWidth_of_le _ (by omega : t.size ≤ 512),
    BitVec.setWidth_setWidth_of_le _ (by omega : t.size ≤ 128), setWidth_of_eq ht.symm]
  rfl

private theorem x64EmitUnpair_gpr32_eq (pa : PArg Reg64 RegMm CondCode (i32.pair i32))
    (r0 r1 : Reg64) :
    x64EmitUnpairIns (pa, ()) (.gpr r0, .gpr r1, ()) =
      if (r0 == r1) = true then none else
        Option.map (fun lp => (lp ++ [ins32I (.mov (↑(d r0)) (.reg (d .r10))),
          insI (.shr (↑(q .r10)) (.imm8 (.int64 32))),
          ins32I (.mov (↑(d r1)) (.reg (d .r10)))], maskAll))
          (match pa with
           | .vec vs => some [x64Avx128I (.vmovOut .W64 (↑(q .r10)) (.xmm vs))]
           | .imm cc => some [x64MoviI .r10 (toBits (i32.pair i32) cc)]
           | _ => none) := by
  cases pa <;> rfl

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
  rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨d0, d1, ⟨⟩⟩
  rcases hhold with _ | ⟨hhv, _⟩
  cases d0 <;> cases d1
  case gpr.gpr r0 r1 =>
    by_cases h32 : a = .bits 32 ∧ b = .bits 32
    · rcases h32 with ⟨rfl, rfl⟩
      rw [x64EmitUnpair_gpr32_eq] at hc
      cases heq : (r0 == r1)
      · have hne : r0 ≠ r1 := fun e => Bool.false_ne_true (by
          rw [← heq]; subst e; cases r0 <;> rfl)
        have hr0 : r0 ∉ x64Scratch := hdG r0 (by simp [tupDstGprs])
        have hr1 : r1 ∉ x64Scratch := hdG r1 (by simp [tupDstGprs])
        have hr0_10 : r0 ≠ .r10 := (ne_of_not_mem_x64Scratch hr0).1
        rw [heq, ite_eq_right Bool.false_ne_true] at hc
        have h10 : ∃ lp, emitClean c = lp ++ [ins32 (.mov (.reg (d r0)) (.reg (d .r10))),
              ins (.shr (.reg (q .r10)) (.imm8 (.int64 32))),
              ins32 (.mov (.reg (d r1)) (.reg (d .r10)))] ∧ clob = maskAll ∧
            @Program.wp _ lp (fun s1 => s1.dmem = s.dmem ∧ s1.zmms = s.zmms ∧
              (∀ r, r ≠ .r10 → s1.regs.get64 r = s.regs.get64 r) ∧
              s1.regs.get64 .r10 = (toBits (.pair i32 i32) v)) (fun _ _ => False) s := by
          cases pa with
          | gpr _ => cases hc
          | vec vs =>
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc
            rcases hc with ⟨rfl, rfl⟩
            refine ⟨_, by simp [emitClean_cons, emitClean_nil], rfl,
              Program.wp.mono (Directive.FallsTo.wp (x64VmovOut64_reg_fallsTo .r10 vs s)) ?_⟩
            rintro s1 rfl
            exact ⟨rfl, rfl, fun r hr => Reg64s.get64_set64_of_ne _ _ _ _ hr.symm, by
              rw [Reg64s.get64_set64_same]; exact hhv.2⟩
          | imm cc =>
            rcases hhv with rfl
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hc
            rcases hc with ⟨rfl, rfl⟩
            refine ⟨[x64MoviD .r10 (toBits (i32.pair i32) cc)],
              by simp [emitClean_cons, emitClean_nil, x64MoviD], rfl,
              Program.wp.mono (Directive.FallsTo.wp (x64MoviD_fallsTo .r10 _ s)) ?_⟩
            rintro s1 rfl
            exact ⟨rfl, rfl, fun r hr => Reg64s.get64_set64_of_ne _ _ _ _ hr.symm,
              by dsimp only; exact Reg64s.get64_set64_same _ _ _⟩
        obtain ⟨lp, heqc, rfl, hlp⟩ := h10
        apply vecFallsTo_of_wp
        rw [heqc]
        refine Program.wp.append hlp ?_
        rintro s1 ⟨hd1, hz1, hg1, h10⟩
        refine Program.wp.cons (Directive.FallsTo.wp (x64Mov32_fallsTo r0 .r10 s1)) ?_
        rintro s2 rfl
        refine Program.wp.cons (Directive.FallsTo.wp (x64Shr32Imm_fallsTo .r10 _)) ?_
        rintro s3 ⟨hd3, hz3, hr3⟩
        refine Program.wp.mono (Directive.FallsTo.wp (x64Mov32_fallsTo r1 .r10 s3)) ?_
        rintro s' hs'
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
        refine ⟨⟨⟨(v.1, v.2, ()), hwp, TRel.cons
              (pDstHolds_gpr32 <| by
                change (s'.regs.get64 r0).setWidth 32 = v.1; rw [hs']; dsimp only
                rw [Reg64s.get64_set64_of_ne _ _ _ _ hne.symm, hg_r0,
                  BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq])
              (TRel.cons (pDstHolds_gpr32 <| by
                change (s'.regs.get64 r1).setWidth 32 = v.2; rw [hs']; dsimp only
                rw [Reg64s.get64_set64_same,
                  BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
                  BitVec.setWidth_eq, hg_r1]) .nil)⟩,
          by rw [hs']; dsimp only; exact hd3.trans hd1⟩,
          vecFrame_upd (fun r hrm => by
              have hn0 : r ≠ r0 := fun e => hrm (by simp [e, tupDstGprs])
              have hn1 : r ≠ r1 := fun e => hrm (by simp [e, tupDstGprs])
              have hnr10 : r ≠ .r10 := fun e => hrm (by simp [e, x64Scratch])
              rw [hs']; dsimp only
              rw [Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hn1), hr3,
                Reg64s.get64_set64_of_ne _ _ _ _ hnr10.symm]; dsimp only
              rw [Reg64s.get64_set64_of_ne _ _ _ _ (Ne.symm hn0), hg1 r hnr10])
            (fun vr _ => by rw [hs']; dsimp only; rw [hz3, hz1]) (Or.inl rfl)⟩
      · rw [heq, ite_eq_left rfl] at hc; cases hc
    · rw [x64EmitUnpair_none_of_dst] at hc <;> first
        | cases hc
        | exact fun ⟨h0, h1, _⟩ => h32 ⟨h0, h1⟩
        | (rintro ⟨_, _, h0, _⟩; cases h0)
  case vec.vec v0 v1 =>
    rw [x64EmitUnpair_vec_eq] at hc
    by_cases heq : (v0 == v1) = true
    · rw [ite_eq_left heq] at hc; cases hc
    · have hv01 : v0 ≠ v1 := fun e => heq (by subst e; exact regMm_beq_true rfl)
      have hv0 : v0 ∉ x64VecScratch := hdV v0 (by simp [tupDstVecs, tupFlatMap, PDst.vecs])
      have hv1 : v1 ∉ x64VecScratch := hdV v1 (by simp [tupDstVecs, tupFlatMap, PDst.vecs])
      have h14_v0 : (.mm14 : RegMm) ≠ v0 := (ne_of_not_mem_x64VecScratch hv0).1.symm
      rw [ite_eq_right heq] at hc
      by_cases hcond : a = b ∧ x64IsBridgeSubVec a ∧ a.size = 64
      · rw [dite_eq_left hcond] at hc
        have hb64 : b.size = 64 := hcond.1 ▸ hcond.2.2
        have hle128 : (Ty.pair a b).size = 128 := by simp only [Ty.size, ← hcond.1, hcond.2.2]
        cases pa with
        | gpr _ => cases hc
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
            rw [← BitVec.setWidth_setWidth_of_le (s.zmms.get512 vs)
                (by omega : 128 ≤ (Ty.pair a b).size),
              hhv.2, setWidth_of_eq hle128, toBits_pair64_eq hcond.1 hcond.2.2 v.1 v.2]
          let zm1 := s.zmms.setLegacy (.xmm .mm14)
            (((s.zmms.get512 vs).setWidth 128).shuffleDwords 0x4e#8)
          let zm2 := zm1.set (.xmm v0) (((zm1.get512 vs).setWidth 64).setWidth 128)
          let zm3 := zm2.set (.xmm v1) (((zm2.get512 .mm14).setWidth 64).setWidth 128)
          have hv0_out : x64Mach.PDstHolds { s with zmms := zm3 } a (.vec v0) v.1 := by
            refine ⟨by omega, ?_⟩; dsimp only [zm3, zm2, zm1]
            rw [RegZmms.get512_set_xmm_of_ne _ hv01.symm,
              zmms_set_xmm64_width (by omega : a.size ≤ 64),
              RegZmms.get512_setLegacy_xmm_of_ne _ h14_vs,
              ← BitVec.setWidth_setWidth_of_le (s.zmms.get512 vs) (by omega : a.size ≤ 128),
              hvs_eq]
            apply BitVec.eq_of_getLsbD_eq; intro i hi
            simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_cast, BitVec.getLsbD_append,
              show i < a.size from hi, show i < 64 by omega, decide_true, Bool.true_and, ↓reduceIte]
          have hv1_out : x64Mach.PDstHolds { s with zmms := zm3 } b (.vec v1) v.2 := by
            refine ⟨by omega, ?_⟩; dsimp only [zm3, zm2, zm1]
            rw [zmms_set_xmm64_width (by omega : b.size ≤ 64),
              RegZmms.get512_set_xmm_of_ne _ h14_v0.symm, RegZmms.get512_setLegacy_xmm,
              ← BitVec.setWidth_setWidth_of_le _ (by omega : b.size ≤ 128),
              setWidth_replaceLow (by decide), hvs_eq,
              ← BitVec.setWidth_setWidth_of_le _ (by omega : b.size ≤ 64),
              shufd_0x4e_hi64]
            apply BitVec.eq_of_getLsbD_eq; intro i hi
            simp [show i < b.size from hi]
          refine ⟨⟨⟨(v.1, v.2, ()), hwp, TRel.cons hv0_out (TRel.cons hv1_out .nil)⟩, rfl⟩,
            vecFrame_upd (fun _ _ => rfl) (fun vr hvm => by
              have hn0 : vr ≠ v0 := fun e => hvm (by simp [e, tupDstVecs, tupFlatMap, PDst.vecs])
              have hn1 : vr ≠ v1 := fun e => hvm (by simp [e, tupDstVecs, tupFlatMap, PDst.vecs])
              have h14 : vr ≠ .mm14 := fun e => hvm (by simp [e, x64VecScratch])
              dsimp only [zm3, zm2, zm1]
              rw [RegZmms.get512_set_xmm_of_ne _ (Ne.symm hn1),
                RegZmms.get512_set_xmm_of_ne _ (Ne.symm hn0),
                RegZmms.get512_setLegacy_xmm_of_ne _ h14.symm]) (Or.inr rfl)⟩
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
          refine ⟨⟨⟨(cc.1, cc.2, ()), hwp, TRel.cons
              (pDstHolds_vec64 hcond.2.2 cc.1 (by rw [hz2 v0 hv01, hv0_1]))
              (TRel.cons (pDstHolds_vec64 hb64 cc.2 hv1_2) .nil)⟩, hd2.trans hd1⟩,
            vecFrame_upd (fun r hrm => by
                have hr10 : r ≠ .r10 := fun e => hrm (by simp [e, x64Scratch])
                rw [hr2 r hr10, hr1 r hr10])
              (fun vr hvm => by
                have hn0 : vr ≠ v0 := fun e => hvm (by simp [e, tupDstVecs, tupFlatMap, PDst.vecs])
                have hn1 : vr ≠ v1 := fun e => hvm (by simp [e, tupDstVecs, tupFlatMap, PDst.vecs])
                rw [hz2 vr hn1, hz1 vr hn0])
              (Or.inr (hs2.trans hs1))⟩
      · rw [dite_eq_right (fun h => absurd h hcond)] at hc; cases hc
  all_goals
    rw [x64EmitUnpair_none_of_dst] at hc <;> first
      | cases hc
      | (rintro ⟨_, _, _, _, h0, h1⟩; first | (cases h0; done) | (cases h1; done))
      | (rintro ⟨_, _, h0, h1⟩; first | (cases h0; done) | (cases h1; done))

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

private theorem x64Vop_wideBitwise_wp [Host] {h : Host} {k : Nat} {t : Ty} {imm : BitVec 8}
    {fv : ∀ {m : Nat}, BitVec m → BitVec m → BitVec m} {gb : Bool → Bool → Bool}
    (htern : ∀ {m : Nat} (x y : BitVec m), BitVec.ternaryLogic x y y imm = fv x y)
    (hbit : ∀ {n} (x y : BitVec n) i, i < n → (fv x y).getLsbD i = gb (x.getLsbD i) (y.getLsbD i))
    {pas : Tup (PArg Reg64 RegMm CondCode) [t, t]} {dsts : Tup (PDst Reg64 RegMm CondCode) [t]}
    {c : List Instr} {clob : FlagMask} {va vb : Val t} {P : Tup Val [t] → Prop}
    {s : MachineData} {post : MachineState → Prop}
    (hc : x64WideTernlogBinIns imm pas dsts = some (c, clob))
    (hpaV : ∀ vr ∈ tupArgVecs pas, vr ∉ x64VecScratch)
    (hdV : ∀ vr ∈ tupDstVecs dsts, vr ∉ x64VecScratch)
    (hhold : TRel (x64Mach.PArgHolds s) pas (va, vb, ()))
    (hwp : P (lift2 fv gb t va vb, ())) :
    x64Mach.FallsTo x64CondReads h k (emitClean c) (tupDstGprs dsts ++ x64Scratch)
      (tupDstVecs dsts ++ x64VecScratch) clob s
      (fun s' => (∃ rvs, P rvs ∧ TRel (x64Mach.PDstHolds s') dsts rvs) ∧
        x64Mach.mem s' = x64Mach.mem s) post := by
  rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨d, ⟨⟩⟩
  dsimp only [x64WideTernlogBinIns] at hc
  cases hw : x64VecSlotWidth t with
  | none => rw [hw] at hc; cases d <;> cases hc
  | some w =>
    rw [hw] at hc
    cases d with
    | gpr _ | flag _ => cases hc
    | vec vd =>
      by_cases hw64 : w = .w64
      · subst hw64; dsimp only at hc; cases hc
      · have hb : (w == .w64) = false := by cases w <;> first | exact absurd rfl hw64 | rfl
        dsimp only at hc; rw [hb] at hc
        simp only [Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff, Prod.mk.injEq] at hc
        obtain ⟨c0, hc0, rfl, rfl⟩ := hc
        have ht : t.size = w.bits := (x64VecSlotWidth_bits_eq hw).symm
        have haw : (x64AwOf w).bits = w.bits := x64AwOf_bits_of_ne_w64 hw64
        have hvb := x64IsVecBits_of_slot hw
        rcases hhold with _ | ⟨hha, _ | ⟨hhb, _⟩⟩
        refine vecOpFallsTo_P (x64VecSlotWidth_le_512 hw) hwp ?_
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
            (fun dd src st => avx_fallsTo_frame
              (by rw [haw, BitVec.setWidth_eq, BitVec.setWidth_eq])
              (x64Vpternlogd_fallsTo w dd src src imm st))
            hc0 (hdV vd (by simp [tupDstVecs])) (fun vr h => hpaV vr (pargVecs_sub_2_1 pa pb vr h))
            (fun vr h => hpaV vr (pargVecs_sub_2_2 pa pb vr h)) hha hhb) ?_
        rintro s' ⟨hf, hval⟩
        simp only [BitVec.cast_cast, BitVec.cast_eq] at hval
        exact ⟨hf, by rw [hval, toBits_lift2_bitwise fv gb hbit hvb]⟩

private theorem x64Vop_uniformShift_wp [Host] {h : Host} {k : Nat} {t : Ty}
    {mk : SlotWidth → Nat → RegMm → RegMm → Instr}
    {op : ∀ {m : Nat}, BitVec m → BitVec m → BitVec m} {gb : Bool → Bool → Bool}
    {f : Nat → BitVec 32 → BitVec 32}
    (hmop : ∀ (w : SlotWidth) (cnt : Nat) (d src : RegMm) (st : MachineData), w ≠ .w64 → cnt < 32 →
      Directive.FallsTo (.instr (mk w cnt d src)) st
        (fun st' => st' = { st with zmms := (st.zmms.set (x64AvxRegOf w d)
          (((st.zmms.get512 src).setWidth (x64AwOf w).bits).mapLanes 32 (f cnt))) }))
    (hstep : ∀ {cnt : Nat} (x y : BitVec 32), y.toNat % 32 = cnt → op x y = f cnt x)
    {pas : Tup (PArg Reg64 RegMm CondCode) [t, t]} {dsts : Tup (PDst Reg64 RegMm CondCode) [t]}
    {c : List Instr} {clob : FlagMask} {va vb : Val t} {P : Tup Val [t] → Prop}
    {s : MachineData} {post : MachineState → Prop}
    (hc : x64UniformShiftI32Ins pas dsts mk = some (c, clob))
    (hdV : ∀ vr ∈ tupDstVecs dsts, vr ∉ x64VecScratch)
    (hhold : TRel (x64Mach.PArgHolds s) pas (va, vb, ()))
    (hwp : t.hasFloat = false → P (lift2 op gb t va vb, ())) :
    x64Mach.FallsTo x64CondReads h k (emitClean c) (tupDstGprs dsts ++ x64Scratch)
      (tupDstVecs dsts ++ x64VecScratch) clob s
      (fun s' => (∃ rvs, P rvs ∧ TRel (x64Mach.PDstHolds s') dsts rvs) ∧
        x64Mach.mem s' = x64Mach.mem s) post := by
  rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨d, ⟨⟩⟩
  dsimp only [x64UniformShiftI32Ins] at hc
  cases hi32 : x64IsI32Vec t
  · rw [hi32] at hc; cases hc
  · rw [hi32, Bool.not_true, ite_eq_right Bool.false_ne_true] at hc
    cases hw : x64VecSlotWidth t with
    | none => rw [hw] at hc; cases pb <;> cases d <;> cases hc
    | some w =>
      rw [hw] at hc
      cases pb with
      | gpr _ | vec _ | flag _ => cases d <;> cases hc
      | imm cb =>
        cases d with
        | gpr _ | flag _ => cases hc
        | vec vd =>
          by_cases hw64 : w = .w64
          · subst hw64; dsimp only at hc; cases hc
          · have hb : (w == .w64) = false := by cases w <;> first | exact absurd rfl hw64 | rfl
            dsimp only at hc; rw [hb] at hc
            simp only [Bool.false_eq_true, ↓reduceIte] at hc
            cases hsp : x64UniformI32Splat? t cb with
            | none => rw [hsp] at hc; cases hc
            | some cnt =>
              rw [hsp] at hc
              simp only [Option.bind_some, Option.map_eq_some_iff, Prod.mk.injEq] at hc
              obtain ⟨c0, hc0, rfl, rfl⟩ := hc
              have ht : t.size = w.bits := (x64VecSlotWidth_bits_eq hw).symm
              have haw : (x64AwOf w).bits = w.bits := x64AwOf_bits_of_ne_w64 hw64
              have hcnt : cnt < 32 := x64UniformI32Splat?_lt32 hi32 hsp
              rcases hhold with _ | ⟨hha, _ | ⟨hhb, _⟩⟩
              have hcb : cb = vb := hhb; subst hcb
              refine vecOpFallsTo_P (x64VecSlotWidth_le_512 hw)
                (hwp (x64IsI32Vec_not_hasFloat hi32)) ?_
              refine Program.wp.mono (x64EmitUnary_wp w ht (upd := fun _ x =>
                  ((x.setWidth (x64AwOf w).bits).mapLanes 32 (f cnt)).setWidth 512)
                  (res := fun x => (x.cast ht.symm).mapLanes 32 (f cnt))
                  (fun _ x => by
                    rw [BitVec.setWidth_setWidth_of_le _ (ht ▸ w.bits_le_512),
                      haw, BitVec.setWidth_eq, setWidth_of_eq ht.symm, mapLanes32_cast])
                  (fun dd src st => avx_fallsTo_frame (by rw [haw, BitVec.setWidth_eq])
                    (hmop w cnt dd src st hw64 hcnt))
                  hc0 (hdV vd (by simp [tupDstVecs])) hha) ?_
              rintro s' ⟨hf, hval⟩
              simp only [BitVec.cast_cast, BitVec.cast_eq] at hval
              exact ⟨hf, by rw [hval, toBits_lift2_splat32 op f cnt hstep hi32 gb va cb hsp]⟩

private theorem x64Vop_bin128_wp [Host] {h : Host} {k : Nat} {t : Ty}
    {pas : Tup (PArg Reg64 RegMm CondCode) [t, t]} {dsts : Tup (PDst Reg64 RegMm CondCode) [t]}
    {emit : RegMm → RegMm → Instr} {f : BitVec 128 → BitVec 128 → BitVec 128}
    {fN : ∀ {n : Nat}, BitVec n → BitVec n → BitVec n}
    (hemit : ∀ d src st, Directive.FallsTo (.instr (emit d src)) st
      (fun st' => st' = { st with zmms := (st.zmms.setLegacy (.xmm d)
        (f ((st.zmms.get512 d).setWidth 128) ((st.zmms.get512 src).setWidth 128))) }))
    (hcast : ∀ {p : Nat} (heq : p = 128) (a b : BitVec p),
      f (a.cast heq) (b.cast heq) = (fN a b).cast heq)
    {c : List Instr} {clob : FlagMask} {va vb : Val t} {P : Tup Val [t] → Prop}
    {s : MachineData} {post : MachineState → Prop}
    (hc : x64BinInPlace128Ins (x64Is128Vec t) pas dsts emit = some (c, clob))
    (hpaV : ∀ vr ∈ tupArgVecs pas, vr ∉ x64VecScratch)
    (hdV : ∀ vr ∈ tupDstVecs dsts, vr ∉ x64VecScratch)
    (hhold : TRel (x64Mach.PArgHolds s) pas (va, vb, ()))
    (hwp : t.size ≠ 0 ∧ t.size % 128 = 0 ∧ P (ofBits t (fN (toBits t va) (toBits t vb)), ())) :
    x64Mach.FallsTo x64CondReads h k (emitClean c) (tupDstGprs dsts ++ x64Scratch)
      (tupDstVecs dsts ++ x64VecScratch) clob s
      (fun s' => (∃ rvs, P rvs ∧ TRel (x64Mach.PDstHolds s') dsts rvs) ∧
        x64Mach.mem s' = x64Mach.mem s) post := by
  obtain ⟨vd, ht, _, rfl, rfl, hwp0⟩ := x64BinInPlace128_wp (ok := x64Is128Vec t)
    (fun h => by simp only [x64Is128Vec, Bool.and_eq_true, beq_iff_eq] at h; exact h.2)
    hemit hc hpaV hdV hhold
  refine vecOpFallsTo_P (by omega) hwp.2.2 (Program.wp.mono hwp0 ?_)
  rintro s' ⟨hf, hval⟩; refine ⟨hf, ?_⟩
  rw [hval, hcast ht, BitVec.cast_cast, BitVec.cast_eq]
  exact (toBits_ofBits t _).symm

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
    | none => rw [hw] at hc; cases pa <;> cases d <;> cases hc
    | some w =>
      rw [hw] at hc
      cases d with
      | gpr _ | flag _ => cases pa <;> cases hc
      | vec vd =>
        have ht := x64VecSlotWidth_bits_eq hw
        have hle := x64VecSlotWidth_le_512 hw
        have hvd : vd ∉ x64VecScratch := hdV vd (by simp [tupDstVecs])
        have h14d : (.mm14 : RegMm) ≠ vd := (ne_of_not_mem_x64VecScratch hvd).1.symm
        rcases hhold with _ | ⟨hha, _⟩
        cases pa with
        | gpr _ | flag _ => cases hc
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
          | none => rw [hv] at hc; cases hc
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
    rcases vs with ⟨va, vb, ⟨⟩⟩; rcases pas with ⟨pa, pb, ⟨⟩⟩
    dsimp only [x64VopIns] at hc
    cases hi32 : x64IsI32Vec t
    · rw [hi32] at hc; cases hc
    · rw [hi32, Bool.not_true, ite_eq_right Bool.false_ne_true] at hc
      obtain ⟨w, vd, c0, hw, hw64, rfl, hc0, rfl, rfl⟩ := withWide_elim dsts hc
      have ht : t.size = w.bits := (x64VecSlotWidth_bits_eq hw).symm
      have hle := x64VecSlotWidth_le_512 hw
      simp only [OpCode.wp_add, x64IsI32Vec_not_hasFloat hi32,
        Bool.false_eq_true, ↓reduceIte] at hwp
      rcases hhold with _ | ⟨hha, _ | ⟨hhb, _⟩⟩
      refine vecOpFallsTo_P hle hwp ?_
      refine Program.wp.mono (x64EmitVpaddd_wp w hw64 ht hc0
        (hdV vd (by simp [tupDstVecs, tupFlatMap, PDst.vecs]))
        (fun vr hr => hpaV vr (pargVecs_sub_2_1 pa pb vr hr))
        (fun vr hr => hpaV vr (pargVecs_sub_2_2 pa pb vr hr)) hha hhb) ?_
      rintro s' ⟨hf, hval⟩; refine ⟨hf, ?_⟩
      rw [hval, toBits_lift2_add hi32, ← packedBinOp32_cast]
      congr 1 <;> simp [BitVec.cast_cast]
  | «and» t =>
    rcases vs with ⟨va, vb, ⟨⟩⟩
    exact x64Vop_wideBitwise_wp ternaryLogic_0xC0 (fun _ _ _ _ => BitVec.getLsbD_and)
      hc hpaV hdV hhold hwp
  | «or» t =>
    rcases vs with ⟨va, vb, ⟨⟩⟩
    exact x64Vop_wideBitwise_wp ternaryLogic_0xFC (fun _ _ _ _ => BitVec.getLsbD_or)
      hc hpaV hdV hhold hwp
  | xor t =>
    rcases vs with ⟨va, vb, ⟨⟩⟩
    exact x64Vop_wideBitwise_wp ternaryLogic_0x3C (fun _ _ _ _ => BitVec.getLsbD_xor)
      hc hpaV hdV hhold hwp
  | not t =>
    rcases vs with ⟨va, ⟨⟩⟩; rcases pas with ⟨pa, ⟨⟩⟩
    dsimp only [x64VopIns] at hc
    obtain ⟨w, vd, c0, hw, hw64, rfl, hc0, rfl, rfl⟩ := withWide_elim dsts hc
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
        (fun dd src st => avx_fallsTo_frame (by rw [haw, BitVec.setWidth_eq])
          (x64Vpternlogd_fallsTo w dd src src 0x33#8 st))
        hc0 (hdV vd (by simp [tupDstVecs, tupFlatMap, PDst.vecs])) hha) ?_
    rintro s' ⟨hf, hval⟩
    exact ⟨hf, by rw [hval, BitVec.cast_cast, BitVec.cast_eq, toBits_lift1_not hvb]⟩
  | ternlog t imm =>
    rcases vs with ⟨va, vb, vc, ⟨⟩⟩; rcases pas with ⟨pa, pb, pc, ⟨⟩⟩
    dsimp only [x64VopIns] at hc
    obtain ⟨w, vd, c0, hw, _, rfl, hc0, rfl, rfl⟩ := withWide_elim dsts hc
    have ht : t.size = w.bits := (x64VecSlotWidth_bits_eq hw).symm
    have hvb := x64IsVecBits_of_slot hw
    have hle := x64VecSlotWidth_le_512 hw
    rcases hhold with _ | ⟨hha, _ | ⟨hhb, _ | ⟨hhc, _⟩⟩⟩
    refine vecOpFallsTo_P hle hwp ?_
    refine Program.wp.mono (x64EmitTernlog_wp w ht hc0
      (hdV vd (by simp [tupDstVecs, tupFlatMap, PDst.vecs]))
      (fun vr hr => hpaV vr (pargVecs_sub_3_1 pa pb pc vr hr))
      (fun vr hr => hpaV vr (pargVecs_sub_3_2 pa pb pc vr hr))
      (fun vr hr => hpaV vr (pargVecs_sub_3_3 pa pb pc vr hr)) hha hhb hhc) ?_
    rintro s' ⟨hf, hval⟩
    exact ⟨hf, by rw [hval, toBits_lift3_ternlog hvb]⟩
  | rotr t =>
    rcases vs with ⟨va, vb, ⟨⟩⟩
    exact x64Vop_uniformShift_wp (op := fun {n} x y => x.rotateRight (y.toNat % n))
      (fun w cnt d src st _ hcnt => fallsTo_mono (x64Vprord_fallsTo w d src cnt hcnt st)
        (by rintro st' rfl; rfl))
      (fun _ _ hy => by rw [hy]) hc hdV hhold
      (fun hf => by
        simp only [OpCode.wp_rotr, hf, Bool.false_eq_true, ↓reduceIte] at hwp; exact hwp)
  | lshr t =>
    rcases vs with ⟨va, vb, ⟨⟩⟩
    exact x64Vop_uniformShift_wp (op := fun {n} x y => x >>> (y.toNat % n))
      (fun w cnt d src st _ hcnt => fallsTo_mono (x64Vpsrld_fallsTo w d src cnt hcnt st)
        (by rintro st' rfl; rfl))
      (fun _ _ hy => by rw [hy]) hc hdV hhold
      (fun hf => by
        simp only [OpCode.wp_lshr, hf, Bool.false_eq_true, ↓reduceIte] at hwp; exact hwp)
  | shufd t imm =>
    rcases vs with ⟨va, ⟨⟩⟩; rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨d, ⟨⟩⟩
    dsimp only [x64VopIns] at hc
    cases h128 : x64Is128Vec t
    · rw [h128] at hc; cases hc
    · rw [h128, Bool.not_true, ite_eq_right Bool.false_ne_true] at hc
      cases d with
      | gpr _ | flag _ => cases hc
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
            (fun dd src st => xmm_fallsTo_frame (x64Pshufd_fallsTo dd src imm st))
            hc0 (hdV vd (by simp [tupDstVecs])) hha) ?_
        rintro s' ⟨hf, hval⟩; refine ⟨hf, ?_⟩
        rw [hval, shuffleDwords_cast, BitVec.cast_cast, BitVec.cast_eq, ← shuffleDwords_eq]
        exact (toBits_ofBits t _).symm
  | shufb t =>
    rcases vs with ⟨va, vb, ⟨⟩⟩
    dsimp only [OpCode.wp] at hwp
    rw [shuffleBytes_eq] at hwp
    exact x64Vop_bin128_wp x64Pshufb_fallsTo shuffleBytes_cast hc hpaV hdV hhold hwp
  | alignr t imm =>
    rcases vs with ⟨va, vb, ⟨⟩⟩
    dsimp only [OpCode.wp] at hwp
    rw [alignBytes_eq] at hwp
    exact x64Vop_bin128_wp (f := fun a b => BitVec.alignBytes a b imm)
      (fN := fun {n} a b => BitVec.alignBytes a b imm)
      (fun d s st => x64Palignr_fallsTo d s imm st)
      (fun h a b => alignBytes_cast h a b imm) hc hpaV hdV hhold hwp
  | blendw t imm =>
    rcases vs with ⟨va, vb, ⟨⟩⟩
    dsimp only [OpCode.wp] at hwp
    rw [blendWords_eq] at hwp
    exact x64Vop_bin128_wp (f := fun a b => a.blendWords b imm)
      (fN := fun {n} a b => a.blendWords b imm)
      (fun d s st => x64Pblendw_fallsTo d s imm st)
      (fun h a b => blendWords_cast h a b imm) hc hpaV hdV hhold hwp
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
