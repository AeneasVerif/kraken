module

public import LeanQbe.T.Amd64.IselLemmas2

/-!
# x64 Scalar `GprTarget` Proofs — Part 3 (`T8`)

Completes `opCmp`, `opSelect`, `opShift`, and `opFunnel` correctness
(`opDiv`/`opAddc`/`opSubb`/`opMulw`, `supportsScalarOp` 1-for-1, and `x64GprSpec`
continue in `IselLemmas4` and `IselLemmas5`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64

open LeanQbe.T

/-! ## 1. `opCmp_spec`, `testOp_spec`, `cmpMem_spec`, and `testMem_spec` -/

private theorem wp_cmpRegImm [Host] {E : Int64 → MachineData → Prop} (w : Width)
    (rx : Reg64) (cy va : BitVec w.bits) (s : MachineData)
    (hrx_sc : rx ∉ x64Scratch) (hrx : (s.regs.get64 rx).setWidth w.bits = va) :
    _root_.Program.wp (emitClean (cmpRegImmIns w rx cy)) (fun s' =>
      (∀ r, r ∉ x64Scratch → s'.regs.get64 r = s.regs.get64 r) ∧
      s'.dmem = s.dmem ∧ s'.zmms = s.zmms ∧
      ∀ cc : CondCode, cc.interp s'.status = cc.interp (subFlags va cy)) E s := by
  unfold cmpRegImmIns
  split
  · rename_i h0
    have hcy : cy = 0#w.bits := beq_iff_eq.mp h0; subst hcy
    simp only [emitClean_cons, emitClean_nil]
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_test_reg w s rx rx)) ?_
    rintro s' ⟨af, rfl⟩
    exact ⟨fun _ _ => rfl, rfl, rfl, fun cc => by rw [hrx]; exact cond_testFlags_self va af cc⟩
  · split
    · simp only [emitClean_cons, emitClean_nil]
      refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_cmp_imm w s rx cy)) ?_
      rintro s' rfl; exact ⟨fun _ _ => rfl, rfl, rfl, fun _ => by rw [hrx]⟩
    · simp only [emitClean_cons, emitClean_nil]
      have hrx10 := (ne_of_not_mem_x64Scratch hrx_sc).1
      refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s .r10 (cy.setWidth 64))) ?_
      rintro s1 rfl
      refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_cmp_reg w _ rx .r10)) ?_
      rintro s2 rfl
      refine ⟨fun r hr => Reg64s.get64_set64_of_ne _ .r10 r _
        (ne_of_not_mem_x64Scratch hr).1.symm, rfl, rfl, fun _ => ?_⟩
      rw [Reg64s.get64_set64_of_ne _ .r10 rx _ hrx10.symm, hrx,
        Reg64s.get64_set64_same, setWidth_64_setWidth]

private theorem wp_cmpDirect [Host] {E : Int64 → MachineData → Prop} (w : Width)
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {c : List Instr}
    {va vb : BitVec w.bits} {s : MachineData}
    (hc : cmpDirectIns w pa pb = some c)
    (hargs : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ x64Scratch)
    (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va)
    (hpb : x64Mach.PArgHolds s (.bits w.bits) pb vb) :
    _root_.Program.wp (emitClean c) (fun s' =>
      (∀ r, r ∉ x64Scratch → s'.regs.get64 r = s.regs.get64 r) ∧
      s'.dmem = s.dmem ∧ s'.zmms = s.zmms ∧
      ∀ cc : CondCode, cc.interp s'.status = cc.interp (subFlags va vb)) E s := by
  cases pa <;> cases pb <;> simp only [cmpDirectIns] at hc <;> try contradiction
  · rename_i rx ry; simp only [Option.some.injEq] at hc; subst hc
    simp only [emitClean_cons, emitClean_nil]
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_cmp_reg w s rx ry)) ?_
    rintro s' rfl; exact ⟨fun _ _ => rfl, rfl, rfl, fun _ => by rw [hpa.2, hpb.2]⟩
  · rename_i rx cy; rcases hpb with rfl; simp only [Option.some.injEq] at hc; subst hc
    exact wp_cmpRegImm w rx cy va s (hargs rx (by simp [PArg.gprs])) hpa.2
  · rename_i cx ry; rcases hpa with rfl; simp only [Option.some.injEq] at hc; subst hc
    simp only [emitClean_cons, emitClean_nil]
    have hry := (ne_of_not_mem_x64Scratch (hargs ry (by simp [PArg.gprs]))).1
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s .r10 (cx.setWidth 64))) ?_
    rintro s1 rfl
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_cmp_reg w _ .r10 ry)) ?_
    rintro s2 rfl
    refine ⟨fun r hr => Reg64s.get64_set64_of_ne _ .r10 r _
      (ne_of_not_mem_x64Scratch hr).1.symm, rfl, rfl, fun _ => ?_⟩
    rw [Reg64s.get64_set64_of_ne _ .r10 ry _ hry.symm, hpb.2,
      Reg64s.get64_set64_same, setWidth_64_setWidth]
  · rename_i cx cy; rcases hpa with rfl; rcases hpb with rfl
    simp only [Option.some.injEq] at hc; subst hc
    simp only [emitClean_cons, emitClean_nil]
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s .r11 (cx.setWidth 64))) ?_
    rintro s1 rfl
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD _ .r10 (cy.setWidth 64))) ?_
    rintro s2 rfl
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_cmp_reg w _ .r11 .r10)) ?_
    rintro s3 rfl
    refine ⟨fun r hr => ?_, rfl, rfl, fun _ => ?_⟩
    · have hne := ne_of_not_mem_x64Scratch hr
      rw [Reg64s.get64_set64_of_ne _ .r10 r _ hne.1.symm,
        Reg64s.get64_set64_of_ne _ .r11 r _ hne.2.symm]
    · rw [Reg64s.get64_set64_of_ne _ .r10 .r11 _ (by decide), Reg64s.get64_set64_same,
        Reg64s.get64_set64_same, setWidth_64_setWidth, setWidth_64_setWidth]

theorem opCmp_spec [Host] {E : Int64 → MachineData → Prop} (w : Width) (co : CmpOp)
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {pd : PDst Reg64 RegMm CondCode .bool}
    {c : List Instr} {clob : FlagMask} {va vb : BitVec w.bits} {s : MachineData}
    (hc : opCmpIns w co pa pb pd = some (c, clob))
    (hargs : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ x64Scratch)
    (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va)
    (hpb : x64Mach.PArgHolds s (.bits w.bits) pb vb) :
    _root_.Program.wp (emitClean c) (OpPostDst1 .bool pd (co.evalBits va vb) clob s) E s := by
  have hwn : w.bits = 8 ∨ w.bits = 16 ∨ w.bits = 32 ∨ w.bits = 64 := by
    cases w <;> simp [Width.bits]
  cases pd with
  | vec _ => simp [opCmpIns] at hc
  | gpr rd =>
    have useSetcc (pre : List Instr) (x y : BitVec w.bits) (cond : CondCode)
        (hcond : cond.interp (subFlags x y) = co.evalBits va vb)
        (hc_eq : c = pre ++ setccMoveIns rd cond) (hcl_eq : clob = maskAll)
        (hpre : _root_.Program.wp (emitClean pre) (fun s1 =>
          (∀ r, r ∉ x64Scratch → s1.regs.get64 r = s.regs.get64 r) ∧
          s1.dmem = s.dmem ∧ s1.zmms = s.zmms ∧
          ∀ cc : CondCode, cc.interp s1.status = cc.interp (subFlags x y)) E s) :
        _root_.Program.wp (emitClean c)
          (OpPostDst1 .bool (.gpr rd) (co.evalBits va vb) clob s) E s := by
      subst hc_eq; subst hcl_eq
      simp only [emitClean_append]
      refine Program.wp.append hpre ?_
      rintro s1 ⟨hr1, hm1, hz1, hst1⟩
      refine Program.wp.mono (wp_setccMove s1 rd cond) ?_
      rintro s2 rfl
      refine ⟨?_, hm1, x64_frame_of_eq ?_ hz1 (updFlags_maskAll _ _)⟩
      · dsimp only [Machine.PDstHolds, GprHolds]
        rw [Reg64s.get64_set64_same, hst1 cond, hcond]; cases co.evalBits va vb <;> rfl
      · intro r hr
        simp only [tupDstGprs_cons, tupDstGprs_nil, PDst.gprs, List.cons_append,
          List.nil_append, List.mem_cons, not_or] at hr
        rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1),
          hr1 r (by simp only [x64Scratch, List.mem_cons, List.mem_nil_iff, or_false]; exact fun h => h.elim hr.2.1 hr.2.2.1)]
    cases pa with
    | imm cx =>
      cases pb with
      | imm cy =>
        simp only [opCmpIns, Option.some.injEq, Prod.mk.injEq] at hc
        rcases hc with ⟨rfl, rfl⟩; rcases hpa with rfl; rcases hpb with rfl
        simp only [emitClean_cons, emitClean_nil]
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_moviD s rd _)) ?_
        rintro s' rfl
        exact opPostDst_gpr_bool (by cases co.evalBits cx cy <;> rfl) (updFlags_of_status_eq rfl _)
      | gpr ry =>
        rcases hpa with rfl; simp only [opCmpIns] at hc
        split at hc
        · simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
          exact useSetcc _ vb cx (condOf co.swap)
            (by rw [cond_subFlags hwn, CmpOp.swap_evalBits]) rfl rfl
            (wp_cmpRegImm w ry cx vb s (hargs ry (by simp [PArg.gprs])) hpb.2)
        · simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
          refine useSetcc _ cx vb (condOf co) (cond_subFlags hwn _ _ _) rfl rfl ?_
          simp only [emitClean_cons, emitClean_nil]
          have hry := (ne_of_not_mem_x64Scratch (hargs ry (by simp [PArg.gprs]))).1
          refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s .r10 (cx.setWidth 64))) ?_
          rintro s1 rfl
          refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_cmp_reg w _ .r10 ry)) ?_
          rintro s2 rfl
          refine ⟨fun r hr => Reg64s.get64_set64_of_ne _ .r10 r _
            (ne_of_not_mem_x64Scratch hr).1.symm, rfl, rfl, fun _ => ?_⟩
          rw [Reg64s.get64_set64_of_ne _ .r10 ry _ hry.symm, hpb.2,
            Reg64s.get64_set64_same, setWidth_64_setWidth]
      | vec _ => simp [opCmpIns, cmpDirectIns] at hc
    | gpr rx =>
      cases pb with
      | vec _ => simp [opCmpIns, cmpDirectIns] at hc
      | gpr _ | imm _ =>
        simp only [opCmpIns, Option.bind_eq_bind] at hc
        rcases Option.bind_eq_some_iff.mp hc with ⟨seq, hseq, hm⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩
        exact useSetcc _ va vb (condOf co) (cond_subFlags hwn _ _ _) rfl rfl
          (wp_cmpDirect w hseq hargs hpa hpb)
    | vec _ => simp [opCmpIns, cmpDirectIns] at hc
  | flag cc =>
    have finish (pre : List Instr) (x y : BitVec w.bits)
        (hcc : cc.interp (subFlags x y) = co.evalBits va vb)
        (hc_eq : c = pre) (hcl_eq : clob = maskAll)
        (hpre : _root_.Program.wp (emitClean pre) (fun s1 =>
          (∀ r, r ∉ x64Scratch → s1.regs.get64 r = s.regs.get64 r) ∧
          s1.dmem = s.dmem ∧ s1.zmms = s.zmms ∧
          ∀ c0 : CondCode, c0.interp s1.status = c0.interp (subFlags x y)) E s) :
        _root_.Program.wp (emitClean c)
          (OpPostDst1 .bool (.flag cc) (co.evalBits va vb) clob s) E s := by
      subst hc_eq; subst hcl_eq
      refine Program.wp.mono hpre ?_
      rintro s1 ⟨hr1, hm1, hz1, hst1⟩
      refine ⟨?_, hm1, x64_frame_of_eq ?_ hz1 (updFlags_maskAll _ _)⟩
      · dsimp only [Machine.PDstHolds]; rw [hst1 cc, hcc]
      · intro r hr; exact hr1 r (by simpa [tupDstGprs] using hr)
    cases pa with
    | imm cx =>
      cases pb with
      | gpr ry =>
        rcases hpa with rfl; simp only [opCmpIns] at hc
        split at hc
        · rename_i hcond
          have hcc := (beq_cond_iff cc _).1 ((Bool.and_eq_true ..).mp hcond).1
          simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
          exact finish _ vb cx (by rw [hcc, cond_subFlags hwn, CmpOp.swap_evalBits]) rfl rfl
            (wp_cmpRegImm w ry cx vb s (hargs ry (by simp [PArg.gprs])) hpb.2)
        · split at hc
          · rename_i hcc; have hcc' := (beq_cond_iff cc _).1 hcc
            simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
            refine finish _ cx vb (by rw [hcc', cond_subFlags hwn]) rfl rfl ?_
            simp only [emitClean_cons, emitClean_nil]
            have hry := (ne_of_not_mem_x64Scratch (hargs ry (by simp [PArg.gprs]))).1
            refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s .r10 (cx.setWidth 64))) ?_
            rintro s1 rfl
            refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_cmp_reg w _ .r10 ry)) ?_
            rintro s2 rfl
            refine ⟨fun r hr => Reg64s.get64_set64_of_ne _ .r10 r _
              (ne_of_not_mem_x64Scratch hr).1.symm, rfl, rfl, fun _ => ?_⟩
            rw [Reg64s.get64_set64_of_ne _ .r10 ry _ hry.symm, hpb.2,
              Reg64s.get64_set64_same, setWidth_64_setWidth]
          · split at hc <;> try contradiction
            rename_i hcc; have hcc' := (beq_cond_iff cc _).1 hcc
            simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
            refine finish _ vb cx (by rw [hcc', cond_subFlags hwn, CmpOp.swap_evalBits]) rfl rfl ?_
            simp only [emitClean_cons, emitClean_nil]
            have hry := (ne_of_not_mem_x64Scratch (hargs ry (by simp [PArg.gprs]))).1
            refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s .r10 (cx.setWidth 64))) ?_
            rintro s1 rfl
            refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_cmp_reg w _ ry .r10)) ?_
            rintro s2 rfl
            refine ⟨fun r hr => Reg64s.get64_set64_of_ne _ .r10 r _
              (ne_of_not_mem_x64Scratch hr).1.symm, rfl, rfl, fun _ => ?_⟩
            rw [Reg64s.get64_set64_of_ne _ .r10 ry _ hry.symm, hpb.2,
              Reg64s.get64_set64_same, setWidth_64_setWidth]
      | imm cy =>
        simp only [opCmpIns, Option.bind_eq_bind] at hc
        split at hc
        · rename_i hcc; have hcc' := (beq_cond_iff cc _).1 hcc
          rcases Option.bind_eq_some_iff.mp hc with ⟨seq, hseq, hm⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at hm; rcases hm with ⟨rfl, rfl⟩
          exact finish _ va vb (by rw [hcc', cond_subFlags hwn]) rfl rfl
            (wp_cmpDirect w hseq hargs hpa hpb)
        · split at hc <;> try contradiction
          rename_i hcc; have hcc' := (beq_cond_iff cc _).1 hcc
          rcases Option.bind_eq_some_iff.mp hc with ⟨seq, hseq, hm⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at hm; rcases hm with ⟨rfl, rfl⟩
          have hargs' : ∀ r ∈ (PArg.imm cy : PArg Reg64 RegMm CondCode (.bits w.bits)).gprs ++
              (PArg.imm cx : PArg Reg64 RegMm CondCode (.bits w.bits)).gprs, r ∉ x64Scratch :=
            fun r hr => by simp [PArg.gprs] at hr
          exact finish _ vb va (by rw [hcc', cond_subFlags hwn, CmpOp.swap_evalBits]) rfl rfl
            (wp_cmpDirect w hseq hargs' hpb hpa)
      | vec _ => simp [opCmpIns, cmpDirectIns] at hc
    | gpr rx =>
      cases pb with
      | vec _ => simp [opCmpIns, cmpDirectIns] at hc
      | gpr _ | imm _ =>
        simp only [opCmpIns, Option.bind_eq_bind] at hc
        split at hc
        · rename_i hcc; have hcc' := (beq_cond_iff cc _).1 hcc
          rcases Option.bind_eq_some_iff.mp hc with ⟨seq, hseq, hm⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at hm; rcases hm with ⟨rfl, rfl⟩
          exact finish _ va vb (by rw [hcc', cond_subFlags hwn]) rfl rfl
            (wp_cmpDirect w hseq hargs hpa hpb)
        · split at hc <;> try contradiction
          rename_i hcc; have hcc' := (beq_cond_iff cc _).1 hcc
          rcases Option.bind_eq_some_iff.mp hc with ⟨seq, hseq, hm⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at hm; rcases hm with ⟨rfl, rfl⟩
          have hargs' :
              ∀ r ∈ _ ++ (PArg.gpr rx : PArg Reg64 RegMm CondCode (.bits w.bits)).gprs,
                r ∉ x64Scratch :=
            fun r hr => hargs r (by simp only [List.mem_append] at hr ⊢; exact hr.symm)
          exact finish _ vb va (by rw [hcc', cond_subFlags hwn, CmpOp.swap_evalBits]) rfl rfl
            (wp_cmpDirect w hseq hargs' hpb hpa)
    | vec _ => simp [opCmpIns, cmpDirectIns] at hc

private theorem wp_testRegImm [Host] {E : Int64 → MachineData → Prop} (w : Width)
    (rx : Reg64) (cy va : BitVec w.bits) (s : MachineData)
    (hrx_sc : rx ∉ x64Scratch) (hrx : (s.regs.get64 rx).setWidth w.bits = va) :
    _root_.Program.wp (emitClean (if w != .W64 || fitsImm32 (cy.setWidth 64) then
        [x64InsI w (.test (.reg (regW w rx)) (immBitsOp w cy))]
      else
        [moviI .r10 (cy.setWidth 64), x64InsI w (.test (.reg (regW w rx)) (.reg (regW w .r10)))]))
      (fun s' =>
        (∀ r, r ∉ x64Scratch → s'.regs.get64 r = s.regs.get64 r) ∧
        s'.dmem = s.dmem ∧ s'.zmms = s.zmms ∧
        ∃ af, s'.status = testFlags va cy af) E s := by
  split
  · simp only [emitClean_cons, emitClean_nil]
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_test_imm w s rx cy)) ?_
    rintro s' ⟨af, rfl⟩; exact ⟨fun _ _ => rfl, rfl, rfl, af, by rw [hrx]⟩
  · simp only [emitClean_cons, emitClean_nil]
    have hrx10 := (ne_of_not_mem_x64Scratch hrx_sc).1
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s .r10 (cy.setWidth 64))) ?_
    rintro s1 rfl
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_test_reg w _ rx .r10)) ?_
    rintro s2 ⟨af, rfl⟩
    refine ⟨fun r hr => Reg64s.get64_set64_of_ne _ .r10 r _
      (ne_of_not_mem_x64Scratch hr).1.symm, rfl, rfl, af, ?_⟩
    rw [Reg64s.get64_set64_of_ne _ .r10 rx _ hrx10.symm, hrx,
      Reg64s.get64_set64_same, setWidth_64_setWidth]

private theorem wp_testDirect [Host] {E : Int64 → MachineData → Prop} (w : Width)
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {c : List Instr}
    {va vb : BitVec w.bits} {s : MachineData}
    (hc : testDirectIns w pa pb = some c)
    (hargs : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ x64Scratch)
    (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va)
    (hpb : x64Mach.PArgHolds s (.bits w.bits) pb vb) :
    _root_.Program.wp (emitClean c) (fun s' =>
      (∀ r, r ∉ x64Scratch → s'.regs.get64 r = s.regs.get64 r) ∧
      s'.dmem = s.dmem ∧ s'.zmms = s.zmms ∧
      ∃ af, s'.status = testFlags va vb af) E s := by
  cases pa <;> cases pb <;> simp only [testDirectIns] at hc <;> try contradiction
  · rename_i rx ry; simp only [Option.some.injEq] at hc; subst hc
    simp only [emitClean_cons, emitClean_nil]
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_test_reg w s rx ry)) ?_
    rintro s' ⟨af, rfl⟩; exact ⟨fun _ _ => rfl, rfl, rfl, af, by rw [hpa.2, hpb.2]⟩
  · rename_i rx cy; rcases hpb with rfl; simp only [Option.some.injEq] at hc; subst hc
    exact wp_testRegImm w rx cy va s (hargs rx (by simp [PArg.gprs])) hpa.2
  · rename_i cx ry; rcases hpa with rfl; simp only [Option.some.injEq] at hc; subst hc
    refine Program.wp.mono (wp_testRegImm w ry cx vb s (hargs ry (by simp [PArg.gprs])) hpb.2) ?_
    rintro s' ⟨hr, hm, hz, af, hst⟩
    exact ⟨hr, hm, hz, af, by rw [hst, testFlags, testFlags, BitVec.and_comm]⟩
  · rename_i cx cy; rcases hpa with rfl; rcases hpb with rfl
    simp only [Option.some.injEq] at hc; subst hc
    simp only [emitClean_cons, emitClean_nil]
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s .r11 (cx.setWidth 64))) ?_
    rintro s1 rfl
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD _ .r10 (cy.setWidth 64))) ?_
    rintro s2 rfl
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_test_reg w _ .r11 .r10)) ?_
    rintro s3 ⟨af, rfl⟩
    refine ⟨fun r hr => ?_, rfl, rfl, af, ?_⟩
    · have hne := ne_of_not_mem_x64Scratch hr
      rw [Reg64s.get64_set64_of_ne _ .r10 r _ hne.1.symm,
        Reg64s.get64_set64_of_ne _ .r11 r _ hne.2.symm]
    · rw [Reg64s.get64_set64_of_ne _ .r10 .r11 _ (by decide), Reg64s.get64_set64_same,
        Reg64s.get64_set64_same, setWidth_64_setWidth, setWidth_64_setWidth]

private theorem finish_boolDst_wp [Host] {E : Int64 → MachineData → Prop}
    {pd : PDst Reg64 RegMm CondCode .bool} {want : Bool} {s : MachineData}
    {pre : List Instr} {cc : CondCode}
    (hpre : _root_.Program.wp (emitClean pre) (fun s1 =>
      (∀ r, r ∉ x64Scratch → s1.regs.get64 r = s.regs.get64 r) ∧
      s1.dmem = s.dmem ∧ s1.zmms = s.zmms ∧ cc.interp s1.status = want) E s) :
    match pd with
    | .gpr rd =>
      _root_.Program.wp (emitClean (pre ++ setccMoveIns rd cc))
        (fun s' => (x64Mach.PDstHolds s' .bool (.gpr rd) want ∧ s'.dmem = s.dmem) ∧
          x64Mach.Frame x64CondReads s s' (rd :: x64Scratch) [] maskAll) E s
    | .flag c0 =>
      c0 = cc →
      _root_.Program.wp (emitClean pre)
        (fun s' => (x64Mach.PDstHolds s' .bool (.flag c0) want ∧ s'.dmem = s.dmem) ∧
          x64Mach.Frame x64CondReads s s' x64Scratch [] maskAll) E s
    | .vec _ => True := by
  cases pd with
  | vec _ => trivial
  | gpr rd =>
    simp only [emitClean_append]
    refine Program.wp.append hpre ?_
    rintro s1 ⟨hr1, hm1, hz1, hcc⟩
    refine Program.wp.mono (wp_setccMove s1 rd cc) ?_
    rintro s2 rfl
    refine ⟨⟨?_, hm1⟩, x64_frame_of_eq ?_ hz1 (updFlags_maskAll _ _)⟩
    · dsimp only [Machine.PDstHolds, GprHolds]
      rw [Reg64s.get64_set64_same, hcc]; cases want <;> rfl
    · intro r hr
      simp only [List.mem_cons, not_or] at hr
      rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1),
        hr1 r (by
          simp only [x64Scratch, List.mem_cons, List.mem_nil_iff, or_false]
          exact fun h => h.elim hr.2.1 hr.2.2.1)]
  | flag c0 =>
    rintro rfl
    refine Program.wp.mono hpre ?_
    rintro s1 ⟨hr1, hm1, hz1, hcc⟩
    exact ⟨⟨hcc, hm1⟩, x64_frame_of_eq hr1 hz1 (updFlags_maskAll _ _)⟩

theorem x64Gpr_testOp_spec {h : x64Mach.Host} {k n : Nat} {neg : Bool}
    {pa pb : PArg Reg64 RegMm CondCode (.bits n)} {pd : PDst Reg64 RegMm CondCode .bool}
    {c : List Directive} {clob : FlagMask} {va vb : BitVec n} {s : MachineData}
    {post : MachineState → Prop}
    (hc0 : x64Gpr.testOp n neg pa pb pd = some (c, clob))
    (hargs : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ x64Scratch) (_hdst : ∀ r ∈ pd.gprs, r ∉ x64Scratch)
    (hpa : x64Mach.PArgHolds s (.bits n) pa va) (hpb : x64Mach.PArgHolds s (.bits n) pb vb) :
    x64Mach.FallsTo x64Gpr.condReads h k c (pd.gprs ++ x64Scratch) [] clob s
      (fun s' => x64Mach.PDstHolds s' .bool pd
          ((if neg then CmpOp.ne else CmpOp.eq).evalBits (va &&& vb) 0#n) ∧
        x64Mach.mem s' = x64Mach.mem s) post := by
  dsimp only [x64Gpr, x64TestOp] at hc0
  obtain ⟨ci, hc, rfl⟩ := emitCleanPair_eq_some.mp hc0
  refine withWidth_elim hc fun w hn hw => ?_
  subst hn
  let want := (if neg then CmpOp.ne else CmpOp.eq).evalBits (va &&& vb) 0#w.bits
  let wantCc : CondCode := if neg then .nz else .z
  cases pd with
  | vec _ => simp at hw
  | gpr rd =>
    cases pa with
    | imm cx =>
      cases pb with
      | imm cy =>
        rcases hpa with rfl; rcases hpb with rfl
        simp only [Option.some.injEq, Prod.mk.injEq] at hw; rcases hw with ⟨rfl, rfl⟩
        refine x64_fallsTo_of_wp fun {_} _ => ?_
        simp only [emitClean_cons, emitClean_nil]
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_moviD s rd _)) ?_
        rintro s' rfl
        refine ⟨⟨?_, rfl⟩, x64_frame_of_eq ?_ rfl (updFlags_of_status_eq rfl _)⟩
        · dsimp only [Machine.PDstHolds, GprHolds]
          rw [Reg64s.get64_set64_same]
          cases (if neg then CmpOp.ne else CmpOp.eq).evalBits (cx &&& cy) 0#w.bits <;> rfl
        · intro r hr; simp only [PDst.gprs, List.cons_append, List.nil_append, List.mem_cons,
            not_or] at hr
          exact Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1)
      | gpr _ | vec _ =>
        simp only [Option.bind_eq_bind] at hw
        rcases Option.bind_eq_some_iff.mp hw with ⟨t, ht, hm⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at hm; rcases hm with ⟨rfl, rfl⟩
        refine x64_fallsTo_of_wp fun {_} _ =>
          finish_boolDst_wp (pd := .gpr rd) (cc := wantCc) (want := want)
            (Program.wp.mono (wp_testDirect w ht hargs hpa hpb) fun s1 ⟨hr, hm, hz, af, hst⟩ =>
              ⟨hr, hm, hz, by rw [hst]; exact cond_testFlags_z va vb af neg⟩)
    | gpr _ | vec _ =>
      simp only [Option.bind_eq_bind] at hw
      rcases Option.bind_eq_some_iff.mp hw with ⟨t, ht, hm⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at hm; rcases hm with ⟨rfl, rfl⟩
      refine x64_fallsTo_of_wp fun {_} _ =>
        finish_boolDst_wp (pd := .gpr rd) (cc := wantCc) (want := want)
          (Program.wp.mono (wp_testDirect w ht hargs hpa hpb) fun s1 ⟨hr, hm, hz, af, hst⟩ =>
            ⟨hr, hm, hz, by rw [hst]; exact cond_testFlags_z va vb af neg⟩)
  | flag cc =>
    simp only [Option.bind_eq_bind] at hw
    by_cases hcc : cc == wantCc
    · simp only [wantCc] at hcc
      simp only [hcc, ↓reduceIte] at hw
      have hcc' : cc = wantCc := (beq_cond_iff cc wantCc).1 hcc
      rcases Option.bind_eq_some_iff.mp hw with ⟨t, ht, hm⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at hm; rcases hm with ⟨rfl, rfl⟩
      refine x64_fallsTo_of_wp fun {_} _ =>
        finish_boolDst_wp (pd := .flag cc) (cc := wantCc) (want := want)
          (Program.wp.mono (wp_testDirect w ht hargs hpa hpb) fun s1 ⟨hr, hm, hz, af, hst⟩ =>
            ⟨hr, hm, hz, by rw [hst]; exact cond_testFlags_z va vb af neg⟩) hcc'
    · simp only [wantCc] at hcc
      simp [hcc] at hw

private theorem wp_cmp_mem_reg [Host] {E : Int64 → MachineData → Prop} (w : Width)
    (s : MachineData) (addr : AddrExpr) (addrVal : BitVec 64) (va : BitVec w.bits) (ry : Reg64)
    (haddr : ∀ [Labels] (p : Std.Rco Int64),
      (@AddrExpr.interp _ ⟨.W64⟩ addr s.regs p).zeroExtend 64 = addrVal)
    (hlv : loadVal s.dmem (.bits w.bits) addrVal = some va) :
    _root_.Program.wp [insW w (.cmp (.mem addr) (.reg (regW w ry)))]
      (· = { s with status := subFlags va ((s.regs.get64 ry).setWidth w.bits) }) E s := by
  obtain ⟨i, hi, rfl⟩ := loadVal_width_spec w hlv
  refine _root_.Program.wp_singleton fun _ _ => ?_
  cases w <;> simp only [insW, regW, t_step_simp, MachineData.load, Effects.All_require_read_access,
    haddr, hi] <;> exact Or.inl ⟨trivial, rfl⟩

private theorem wp_cmp_reg_mem [Host] {E : Int64 → MachineData → Prop} (w : Width)
    (s : MachineData) (addr : AddrExpr) (addrVal : BitVec 64) (va : BitVec w.bits) (ry : Reg64)
    (haddr : ∀ [Labels] (p : Std.Rco Int64),
      (@AddrExpr.interp _ ⟨.W64⟩ addr s.regs p).zeroExtend 64 = addrVal)
    (hlv : loadVal s.dmem (.bits w.bits) addrVal = some va) :
    _root_.Program.wp [insW w (.cmp (.reg (regW w ry)) (.regOrMem (.mem addr)))]
      (· = { s with status := subFlags ((s.regs.get64 ry).setWidth w.bits) va }) E s := by
  obtain ⟨i, hi, rfl⟩ := loadVal_width_spec w hlv
  refine _root_.Program.wp_singleton fun _ _ => ?_
  cases w <;> simp only [insW, regW, t_step_simp, MachineData.load, Effects.All_require_read_access,
    haddr, hi] <;> exact Or.inl ⟨trivial, rfl⟩

theorem wp_cmp_mem_imm [Host] {E : Int64 → MachineData → Prop} (w : Width)
    (s : MachineData) (addr : AddrExpr) (addrVal : BitVec 64) (va cy : BitVec w.bits)
    (haddr : ∀ [Labels] (p : Std.Rco Int64),
      (@AddrExpr.interp _ ⟨.W64⟩ addr s.regs p).zeroExtend 64 = addrVal)
    (hlv : loadVal s.dmem (.bits w.bits) addrVal = some va) :
    _root_.Program.wp [insW w (.cmp (.mem addr) (immBitsOp w cy))]
      (· = { s with status := subFlags va cy }) E s := by
  obtain ⟨i, hi, rfl⟩ := loadVal_width_spec w hlv
  have htr : (cy.signExtend 64).truncate w.bits = cy :=
    truncate_signExtend_64 (width_bits_le_64 w) cy
  refine _root_.Program.wp_singleton fun _ _ => ?_
  cases w <;> simp only [insW, immBitsOp, t_step_simp, Int64.toBitVec_ofBitVec, htr,
    MachineData.load, Effects.All_require_read_access, haddr, hi] <;> exact Or.inl ⟨trivial, rfl⟩

private theorem wp_test_mem_reg [Host] {E : Int64 → MachineData → Prop} (w : Width)
    (s : MachineData) (addr : AddrExpr) (addrVal : BitVec 64) (va : BitVec w.bits) (ry : Reg64)
    (haddr : ∀ [Labels] (p : Std.Rco Int64),
      (@AddrExpr.interp _ ⟨.W64⟩ addr s.regs p).zeroExtend 64 = addrVal)
    (hlv : loadVal s.dmem (.bits w.bits) addrVal = some va) :
    _root_.Program.wp [insW w (.test (.mem addr) (.reg (regW w ry)))]
      (fun s' => ∃ af,
        s' = { s with status := testFlags va ((s.regs.get64 ry).setWidth w.bits) af })
      E s := by
  obtain ⟨i, hi, rfl⟩ := loadVal_width_spec w hlv
  refine _root_.Program.wp_singleton fun _ _ => ?_
  cases w <;> simp only [insW, regW, t_step_simp, MachineData.load, Effects.All_require_read_access,
    haddr, hi, Effects.All] <;> intro af <;> exact Or.inl ⟨trivial, af, rfl⟩

private theorem wp_test_mem_imm [Host] {E : Int64 → MachineData → Prop} (w : Width)
    (s : MachineData) (addr : AddrExpr) (addrVal : BitVec 64) (va cy : BitVec w.bits)
    (haddr : ∀ [Labels] (p : Std.Rco Int64),
      (@AddrExpr.interp _ ⟨.W64⟩ addr s.regs p).zeroExtend 64 = addrVal)
    (hlv : loadVal s.dmem (.bits w.bits) addrVal = some va) :
    _root_.Program.wp [insW w (.test (.mem addr) (immBitsOp w cy))]
      (fun s' => ∃ af, s' = { s with status := testFlags va cy af }) E s := by
  obtain ⟨i, hi, rfl⟩ := loadVal_width_spec w hlv
  have htr : (cy.signExtend 64).truncate w.bits = cy :=
    truncate_signExtend_64 (width_bits_le_64 w) cy
  refine _root_.Program.wp_singleton fun _ _ => ?_
  cases w <;> simp only [insW, immBitsOp, t_step_simp, Int64.toBitVec_ofBitVec, htr,
    MachineData.load, Effects.All_require_read_access, haddr, hi, Effects.All] <;>
    intro af <;> exact Or.inl ⟨trivial, af, rfl⟩

private theorem wp_cmpMemCore [Host] {E : Int64 → MachineData → Prop} (w : Width)
    (a : AddrArg Reg64) (swapped : Bool)
    {pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {core : List Instr}
    {va vb : BitVec w.bits} {s : MachineData}
    (hcore : cmpMemCoreIns w (addrToExprIns a).2.1 swapped pb = some core)
    (hregs : ∀ r ∈ a.regs ++ pb.gprs, r ∉ x64Scratch)
    (hlv : loadVal s.dmem (.bits w.bits) (a.eval s.regs.get64) = some va)
    (hpb : x64Mach.PArgHolds s (.bits w.bits) pb vb) :
    _root_.Program.wp (emitClean ((addrToExprIns a).1 ++ core)) (fun s' =>
      (∀ r, r ∉ x64Scratch → s'.regs.get64 r = s.regs.get64 r) ∧
      s'.dmem = s.dmem ∧ s'.zmms = s.zmms ∧
      s'.status = if swapped then subFlags vb va else subFlags va vb) E s := by
  have ha : ∀ r ∈ a.regs, r ∉ x64Scratch := fun r hr => hregs r (List.mem_append_left _ hr)
  rw [emitClean_append]
  refine Program.wp.append (wp_addrToExpr s s a ha fun _ _ => rfl) ?_
  rintro s1 ⟨_, hr1, hm1, hz1, haddr1, _⟩
  dsimp only [addrToExpr] at haddr1
  have hregs11 (v : BitVec 64) : ∀ r ∈ .r10 :: a.regs,
      (s1.regs.set64 .r11 v).get64 r = s1.regs.get64 r := by
    intro r hr; rcases List.mem_cons.mp hr with rfl | hr
    · exact Reg64s.get64_set64_of_ne _ .r11 .r10 _ (by decide)
    · exact Reg64s.get64_set64_of_ne _ .r11 r _ (ne_of_not_mem_x64Scratch (ha r hr)).2.symm
  cases pb with
  | vec _ => simp [cmpMemCoreIns] at hcore
  | gpr ry =>
    have hry10 := (ne_of_not_mem_x64Scratch (hregs ry (by simp [PArg.gprs]))).1
    have hry : (s1.regs.get64 ry).setWidth w.bits = vb := by rw [hr1 ry hry10, hpb.2]
    cases swapped
    · simp only [cmpMemCoreIns, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hcore
      subst hcore; simp only [emitClean_cons, emitClean_nil]
      refine Program.wp.mono (wp_cmp_mem_reg w s1 _ (a.eval s.regs.get64) va ry
        (fun {_} p => haddr1 s1.regs (fun _ _ => rfl) p) (hm1 ▸ hlv)) ?_
      rintro s2 rfl
      exact ⟨fun r hr => hr1 r (ne_of_not_mem_x64Scratch hr).1, hm1, hz1, by simp [hry]⟩
    · simp only [cmpMemCoreIns, ↓reduceIte, Option.some.injEq] at hcore
      subst hcore; simp only [emitClean_cons, emitClean_nil]
      refine Program.wp.mono (wp_cmp_reg_mem w s1 _ (a.eval s.regs.get64) va ry
        (fun {_} p => haddr1 s1.regs (fun _ _ => rfl) p) (hm1 ▸ hlv)) ?_
      rintro s2 rfl
      exact ⟨fun r hr => hr1 r (ne_of_not_mem_x64Scratch hr).1, hm1, hz1, by simp [hry]⟩
  | imm cy =>
    rcases hpb with rfl; cases swapped
    · simp only [cmpMemCoreIns, Bool.false_eq_true, ↓reduceIte] at hcore
      split at hcore
      · simp only [Option.some.injEq] at hcore; subst hcore
        simp only [emitClean_cons, emitClean_nil]
        refine Program.wp.mono (wp_cmp_mem_imm w s1 _ (a.eval s.regs.get64) va cy
          (fun {_} p => haddr1 s1.regs (fun _ _ => rfl) p) (hm1 ▸ hlv)) ?_
        rintro s2 rfl
        exact ⟨fun r hr => hr1 r (ne_of_not_mem_x64Scratch hr).1, hm1, hz1, rfl⟩
      · simp only [Option.some.injEq] at hcore; subst hcore
        simp only [emitClean_cons, emitClean_nil]
        refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s1 .r11 (cy.setWidth 64))) ?_
        rintro s2 rfl
        refine Program.wp.mono (wp_cmp_mem_reg w _ _ (a.eval s.regs.get64) va .r11
          (fun {_} p => haddr1 _ (hregs11 _) p) (hm1 ▸ hlv)) ?_
        rintro s3 rfl
        refine ⟨fun r hr => ?_, hm1, hz1, ?_⟩
        · have hne := ne_of_not_mem_x64Scratch hr
          rw [Reg64s.get64_set64_of_ne _ .r11 r _ hne.2.symm, hr1 r hne.1]
        · simp [Reg64s.get64_set64_same, setWidth_64_setWidth]
    · simp only [cmpMemCoreIns, ↓reduceIte, Option.some.injEq] at hcore
      subst hcore; simp only [emitClean_cons, emitClean_nil]
      refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s1 .r11 (cy.setWidth 64))) ?_
      rintro s2 rfl
      refine Program.wp.mono (wp_cmp_reg_mem w _ _ (a.eval s.regs.get64) va .r11
        (fun {_} p => haddr1 _ (hregs11 _) p) (hm1 ▸ hlv)) ?_
      rintro s3 rfl
      refine ⟨fun r hr => ?_, hm1, hz1, ?_⟩
      · have hne := ne_of_not_mem_x64Scratch hr
        rw [Reg64s.get64_set64_of_ne _ .r11 r _ hne.2.symm, hr1 r hne.1]
      · simp [Reg64s.get64_set64_same, setWidth_64_setWidth]

theorem x64Gpr_cmpMem_spec {h : x64Mach.Host} {k : Nat} {co : CmpOp} {n : Nat}
    {a : AddrArg Reg64} {pb : PArg Reg64 RegMm CondCode (.bits n)}
    {pd : PDst Reg64 RegMm CondCode .bool} {c : List Directive} {clob : FlagMask}
    {va vb : BitVec n} {s : MachineData} {post : MachineState → Prop}
    (hc0 : x64Gpr.cmpMem co n a pb pd = some (c, clob))
    (hregs : ∀ r ∈ a.regs ++ pb.gprs, r ∉ x64Scratch) (_hdst : ∀ r ∈ pd.gprs, r ∉ x64Scratch)
    (hlv : loadVal (x64Mach.mem s) (.bits n) (a.eval (x64Mach.getGpr s)) = some va)
    (hpb : x64Mach.PArgHolds s (.bits n) pb vb) :
    x64Mach.FallsTo x64Gpr.condReads h k c (pd.gprs ++ x64Scratch) [] clob s
      (fun s' => x64Mach.PDstHolds s' .bool pd (co.evalBits va vb) ∧
        x64Mach.mem s' = x64Mach.mem s) post := by
  dsimp only [x64Gpr, x64CmpMem] at hc0
  obtain ⟨ci, hc, rfl⟩ := emitCleanPair_eq_some.mp hc0
  have hva : x64AddrValid a = true := by cases hv : x64AddrValid a <;> simp_all [x64CmpMemIns]
  simp only [x64CmpMemIns, hva, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hc
  refine withWidth_elim hc fun w hn hw => ?_
  subst hn
  have hwn : w.bits = 8 ∨ w.bits = 16 ∨ w.bits = 32 ∨ w.bits = 64 := by
    cases w <;> simp [Width.bits]
  cases pd with
  | vec _ => simp at hw
  | gpr rd =>
    simp only [Option.bind_eq_bind] at hw
    rcases Option.bind_eq_some_iff.mp hw with ⟨core, hcore, hm⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at hm; rcases hm with ⟨rfl, rfl⟩
    refine x64_fallsTo_of_wp fun {_} _ =>
      finish_boolDst_wp (pd := .gpr rd) (cc := condOf co) (want := co.evalBits va vb)
        (Program.wp.mono (wp_cmpMemCore w a false hcore hregs hlv hpb) fun s1 ⟨hr, hm, hz, hst⟩ =>
          ⟨hr, hm, hz, by rw [hst]; exact cond_subFlags hwn co va vb⟩)
  | flag cc =>
    simp only [Option.bind_eq_bind] at hw
    split at hw
    · rename_i hcc; have hcc' := (beq_cond_iff cc (condOf co)).1 hcc
      rcases Option.bind_eq_some_iff.mp hw with ⟨core, hcore, hm⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at hm; rcases hm with ⟨rfl, rfl⟩
      refine x64_fallsTo_of_wp fun {_} _ =>
        finish_boolDst_wp (pd := .flag cc) (cc := condOf co) (want := co.evalBits va vb)
          (Program.wp.mono (wp_cmpMemCore w a false hcore hregs hlv hpb) fun s1 ⟨hr, hm, hz, hst⟩ =>
            ⟨hr, hm, hz, by rw [hst]; exact cond_subFlags hwn co va vb⟩) hcc'
    · split at hw <;> try contradiction
      rename_i hcc; have hcc' := (beq_cond_iff cc (condOf co.swap)).1 hcc
      rcases Option.bind_eq_some_iff.mp hw with ⟨core, hcore, hm⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at hm; rcases hm with ⟨rfl, rfl⟩
      refine x64_fallsTo_of_wp fun {_} _ =>
        finish_boolDst_wp (pd := .flag cc) (cc := condOf co.swap) (want := co.evalBits va vb)
          (Program.wp.mono (wp_cmpMemCore w a true hcore hregs hlv hpb) fun s1 ⟨hr, hm, hz, hst⟩ =>
            ⟨hr, hm, hz, by rw [hst]; simp [cond_subFlags hwn, CmpOp.swap_evalBits]⟩) hcc'

private theorem wp_testMemCore [Host] {E : Int64 → MachineData → Prop} (w : Width) (neg : Bool)
    (a : AddrArg Reg64) {pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {core : List Instr}
    {va vb : BitVec w.bits} {s : MachineData}
    (hcore : (match pb with
      | .gpr ry => some [x64InsI w (.test (.mem (addrToExprIns a).2.1) (.reg (regW w ry)))]
      | .imm cy =>
        if w != .W64 || fitsImm32 (cy.setWidth 64) then
          some [x64InsI w (.test (.mem (addrToExprIns a).2.1) (immBitsOp w cy))]
        else
          some [moviI .r11 (cy.setWidth 64),
                x64InsI w (.test (.mem (addrToExprIns a).2.1) (.reg (regW w .r11)))]
      | .vec _ => none) = some core)
    (hregs : ∀ r ∈ a.regs ++ pb.gprs, r ∉ x64Scratch)
    (hlv : loadVal s.dmem (.bits w.bits) (a.eval s.regs.get64) = some va)
    (hpb : x64Mach.PArgHolds s (.bits w.bits) pb vb) :
    _root_.Program.wp (emitClean ((addrToExprIns a).1 ++ core)) (fun s' =>
      (∀ r, r ∉ x64Scratch → s'.regs.get64 r = s.regs.get64 r) ∧
      s'.dmem = s.dmem ∧ s'.zmms = s.zmms ∧
      (if neg then CondCode.nz else .z).interp s'.status =
        (if neg then CmpOp.ne else .eq).evalBits (va &&& vb) 0#w.bits) E s := by
  have ha : ∀ r ∈ a.regs, r ∉ x64Scratch := fun r hr => hregs r (List.mem_append_left _ hr)
  rw [emitClean_append]
  refine Program.wp.append (wp_addrToExpr s s a ha fun _ _ => rfl) ?_
  rintro s1 ⟨_, hr1, hm1, hz1, haddr1, _⟩
  dsimp only [addrToExpr] at haddr1
  cases pb with
  | vec _ => simp at hcore
  | gpr ry =>
    simp only [Option.some.injEq] at hcore; subst hcore; simp only [emitClean_cons, emitClean_nil]
    have hry10 := (ne_of_not_mem_x64Scratch (hregs ry (by simp [PArg.gprs]))).1
    have hry : (s1.regs.get64 ry).setWidth w.bits = vb := by rw [hr1 ry hry10, hpb.2]
    refine Program.wp.mono (wp_test_mem_reg w s1 _ (a.eval s.regs.get64) va ry
      (fun {_} p => haddr1 s1.regs (fun _ _ => rfl) p) (hm1 ▸ hlv)) ?_
    rintro s2 ⟨af, rfl⟩
    exact ⟨fun r hr => hr1 r (ne_of_not_mem_x64Scratch hr).1, hm1, hz1,
      by rw [hry]; exact cond_testFlags_z va vb af neg⟩
  | imm cy =>
    rcases hpb with rfl; dsimp only at hcore; split at hcore
    · simp only [Option.some.injEq] at hcore; subst hcore; simp only [emitClean_cons, emitClean_nil]
      refine Program.wp.mono (wp_test_mem_imm w s1 _ (a.eval s.regs.get64) va cy
        (fun {_} p => haddr1 s1.regs (fun _ _ => rfl) p) (hm1 ▸ hlv)) ?_
      rintro s2 ⟨af, rfl⟩
      exact ⟨fun r hr => hr1 r (ne_of_not_mem_x64Scratch hr).1, hm1, hz1,
        cond_testFlags_z va cy af neg⟩
    · simp only [Option.some.injEq] at hcore; subst hcore; simp only [emitClean_cons, emitClean_nil]
      refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s1 .r11 (cy.setWidth 64))) ?_
      rintro s2 rfl
      have hregs11 : ∀ r ∈ .r10 :: a.regs,
          (s1.regs.set64 .r11 (cy.setWidth 64)).get64 r = s1.regs.get64 r := by
        intro r hr; rcases List.mem_cons.mp hr with rfl | hr
        · exact Reg64s.get64_set64_of_ne _ .r11 .r10 _ (by decide)
        · exact Reg64s.get64_set64_of_ne _ .r11 r _ (ne_of_not_mem_x64Scratch (ha r hr)).2.symm
      refine Program.wp.mono (wp_test_mem_reg w _ _ (a.eval s.regs.get64) va .r11
        (fun {_} p => haddr1 _ hregs11 p) (hm1 ▸ hlv)) ?_
      rintro s3 ⟨af, rfl⟩
      refine ⟨fun r hr => ?_, hm1, hz1, ?_⟩
      · have hne := ne_of_not_mem_x64Scratch hr
        rw [Reg64s.get64_set64_of_ne _ .r11 r _ hne.2.symm, hr1 r hne.1]
      · rw [Reg64s.get64_set64_same, setWidth_64_setWidth]
        exact cond_testFlags_z va cy af neg

theorem x64Gpr_testMem_spec {h : x64Mach.Host} {k n : Nat} {neg : Bool}
    {a : AddrArg Reg64} {pb : PArg Reg64 RegMm CondCode (.bits n)}
    {pd : PDst Reg64 RegMm CondCode .bool} {c : List Directive} {clob : FlagMask}
    {va vb : BitVec n} {s : MachineData} {post : MachineState → Prop}
    (hc0 : x64Gpr.testMem n neg a pb pd = some (c, clob))
    (hregs : ∀ r ∈ a.regs ++ pb.gprs, r ∉ x64Scratch) (_hdst : ∀ r ∈ pd.gprs, r ∉ x64Scratch)
    (hlv : loadVal (x64Mach.mem s) (.bits n) (a.eval (x64Mach.getGpr s)) = some va)
    (hpb : x64Mach.PArgHolds s (.bits n) pb vb) :
    x64Mach.FallsTo x64Gpr.condReads h k c (pd.gprs ++ x64Scratch) [] clob s
      (fun s' => x64Mach.PDstHolds s' .bool pd
          ((if neg then CmpOp.ne else CmpOp.eq).evalBits (va &&& vb) 0#n) ∧
        x64Mach.mem s' = x64Mach.mem s) post := by
  dsimp only [x64Gpr, x64TestMem] at hc0
  obtain ⟨ci, hc, rfl⟩ := emitCleanPair_eq_some.mp hc0
  have hva : x64AddrValid a = true := by cases hv : x64AddrValid a <;> simp_all [x64TestMemIns]
  simp only [x64TestMemIns, hva, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hc
  refine withWidth_elim hc fun w hn hw => ?_
  subst hn
  let want := (if neg then CmpOp.ne else CmpOp.eq).evalBits (va &&& vb) 0#w.bits
  let wantCc : CondCode := if neg then .nz else .z
  cases pd with
  | vec _ => simp at hw
  | gpr rd =>
    simp only [Option.bind_eq_bind] at hw
    rcases Option.bind_eq_some_iff.mp hw with ⟨core, hcore, hm⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at hm; rcases hm with ⟨rfl, rfl⟩
    refine x64_fallsTo_of_wp fun {_} _ =>
      finish_boolDst_wp (pd := .gpr rd) (cc := wantCc) (want := want)
        (wp_testMemCore w neg a hcore hregs hlv hpb)
  | flag cc =>
    simp only [Option.bind_eq_bind] at hw
    by_cases hcc : cc == wantCc
    · simp only [wantCc] at hcc
      simp only [hcc, ↓reduceIte] at hw
      have hcc' := (beq_cond_iff cc wantCc).1 hcc
      rcases Option.bind_eq_some_iff.mp hw with ⟨core, hcore, hm⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at hm; rcases hm with ⟨rfl, rfl⟩
      refine x64_fallsTo_of_wp fun {_} _ =>
        finish_boolDst_wp (pd := .flag cc) (cc := wantCc) (want := want)
          (wp_testMemCore w neg a hcore hregs hlv hpb) hcc'
    · simp only [wantCc] at hcc
      simp [hcc] at hw

/-! ## 2. `opSelect_spec` (`cmovcc`, never branching) -/

theorem fallsTo_cmovcc (cw : Width) (hcw : cw = .W32 ∨ cw = .W64) (cc : CondCode)
    (s : MachineData) (rd rs : Reg64) :
    Directive.FallsTo (insW cw (.cmovcc cc (regW cw rd) (.reg (regW cw rs)))) s
      (· = { s with regs := (s.regs.set64 rd
        ((if cc.interp s.status then (s.regs.get64 rs).setWidth cw.bits
          else (s.regs.get64 rd).setWidth cw.bits).setWidth 64)) }) := by
  intro _ _ _ _ _ hk
  rcases hcw with rfl | rfl
  · simp only [insW, regW, t_step_simp, Reg64s.set, BitVec.zeroExtend_eq_setWidth, Width.bits]
    exact hk _ rfl
  · simp only [insW, regW, t_step_simp, Reg64s.set]
    exact hk _ rfl

private theorem wp_selectFlagSeq_z [Host] {E : Int64 → MachineData → Prop} (z32 : Bool)
    (w : Width) (cc : CondCode)
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64} {c : List Instr}
    {va vb : BitVec w.bits} {s : MachineData}
    (hz : z32 = true → w = .W32 ∧ ∀ ra, ¬(pa = .gpr ra ∧ pb = .gpr ra ∧ ra = rd))
    (hc : selectFlagSeqIns w cc pa pb rd = some c)
    (hrd : rd ∉ x64Scratch)
    (hargs : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ x64Scratch)
    (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va)
    (hpb : x64Mach.PArgHolds s (.bits w.bits) pb vb) :
    _root_.Program.wp (emitClean c) (fun s' =>
      ((s'.regs.get64 rd).setWidth w.bits = if cc.interp s.status then va else vb) ∧
      (z32 = true → w = .W32 →
        s'.regs.get64 rd = (if cc.interp s.status then va else vb).setWidth 64) ∧
      (∀ r, r ≠ rd → r ∉ x64Scratch → s'.regs.get64 r = s.regs.get64 r) ∧
      s'.dmem = s.dmem ∧ s'.zmms = s.zmms ∧ s'.status = s.status) E s := by
  let cw : Width := if w == .W64 then .W64 else .W32
  have hcw : cw = .W32 ∨ cw = .W64 := by cases w <;> simp [cw]
  have hwle : w.bits ≤ cw.bits := by cases w <;> simp [cw, Width.bits]
  have hrd10 := (ne_of_not_mem_x64Scratch hrd).1
  cases pa with
  | vec _ => cases pb <;> simp [selectFlagSeqIns] at hc
  | gpr ra =>
    cases pb with
    | vec _ => simp [selectFlagSeqIns] at hc
    | gpr rb =>
      simp only [selectFlagSeqIns] at hc
      by_cases hab : ra == rb
      · have heq := (beq_reg64_iff ra rb).1 hab; subst rb
        simp only [hab, ↓reduceIte] at hc
        by_cases har : ra == rd
        · have heq := (beq_reg64_iff ra rd).1 har; subst ra
          simp only [har, ↓reduceIte, Option.some.injEq] at hc; subst hc
          refine _root_.Program.wp_nil ⟨?_, fun hz1 _ => absurd ⟨rfl, rfl, rfl⟩ ((hz hz1).2 rd),
            fun _ _ _ => rfl, rfl, rfl, rfl⟩
          rw [hpa.2]
          have hv : va = vb := hpa.2.symm.trans hpb.2
          subst hv; cases cc.interp s.status <;> rfl
        · simp only [har, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hc; subst hc
          simp only [emitClean_cons, emitClean_nil]
          refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movW cw s rd ra)) ?_
          rintro s' rfl
          have hv : va = vb := hpa.2.symm.trans hpb.2
          refine ⟨?_, fun _ hw => ?_, fun r hr _ => Reg64s.get64_set64_of_ne _ rd r _ hr.symm,
            rfl, rfl, rfl⟩
          · rw [Reg64s.get64_set64_same, BitVec.setWidth_setWidth_of_le _ (width_bits_le_64 w),
              BitVec.setWidth_setWidth_of_le _ hwle, hpa.2, hv]
            cases cc.interp s.status <;> rfl
          · subst hw; rw [show cw = .W32 from rfl]
            rw [Reg64s.get64_set64_same, hpa.2, hv]; cases cc.interp s.status <;> rfl
      · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hc
        have hab_ne : ra ≠ rb := fun h => hab ((beq_reg64_iff ra rb).2 h)
        by_cases hrbd : rd == rb
        · have heq := (beq_reg64_iff rd rb).1 hrbd; subst rb
          simp only [hrbd, ↓reduceIte, Option.some.injEq] at hc; subst hc
          simp only [emitClean_cons, emitClean_nil]
          refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_cmovcc cw hcw cc s rd ra)) ?_
          rintro s' rfl
          refine ⟨?_, fun _ hw => ?_, fun r hr _ => Reg64s.get64_set64_of_ne _ rd r _ hr.symm,
            rfl, rfl, rfl⟩
          · rw [Reg64s.get64_set64_same, BitVec.setWidth_setWidth_of_le _ (width_bits_le_64 w)]
            cases cc.interp s.status <;> simp [BitVec.setWidth_setWidth_of_le _ hwle, hpa.2, hpb.2]
          · subst hw; rw [show cw = .W32 from rfl]
            rw [Reg64s.get64_set64_same]; cases cc.interp s.status <;> simp [hpa.2, hpb.2]
        · simp only [hrbd, Bool.false_eq_true, ↓reduceIte] at hc
          by_cases hrad : rd == ra
          · have heq := (beq_reg64_iff rd ra).1 hrad; subst ra
            simp only [hrad, ↓reduceIte, Option.some.injEq] at hc; subst hc
            simp only [emitClean_cons, emitClean_nil]
            refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_cmovcc cw hcw (x64NegCond cc) s rd rb)) ?_
            rintro s' rfl
            refine ⟨?_, fun _ hw => ?_, fun r hr _ => Reg64s.get64_set64_of_ne _ rd r _ hr.symm,
              rfl, rfl, rfl⟩
            · rw [Reg64s.get64_set64_same, BitVec.setWidth_setWidth_of_le _ (width_bits_le_64 w),
                x64NegCond_interp]
              cases cc.interp s.status <;>
                simp [BitVec.setWidth_setWidth_of_le _ hwle, hpa.2, hpb.2]
            · subst hw; rw [show cw = .W32 from rfl]
              rw [Reg64s.get64_set64_same, x64NegCond_interp]
              cases cc.interp s.status <;> simp [hpa.2, hpb.2]
          · simp only [hrad, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hc; subst hc
            simp only [emitClean_cons, emitClean_nil]
            have hrad_ne : ra ≠ rd := fun h => hrad ((beq_reg64_iff rd ra).2 h.symm)
            refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_movW cw s rd rb)) ?_
            rintro s1 rfl
            refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_cmovcc cw hcw cc _ rd ra)) ?_
            rintro s2 rfl
            refine ⟨?_, fun _ hw => ?_, fun r hr _ => ?_, rfl, rfl, rfl⟩
            · rw [Reg64s.get64_set64_same, BitVec.setWidth_setWidth_of_le _ (width_bits_le_64 w)]
              cases cc.interp s.status
              · simp [BitVec.setWidth_setWidth_of_le _ hwle,
                  BitVec.setWidth_setWidth_of_le _ (width_bits_le_64 cw),
                  Reg64s.get64_set64_same, hpb.2]
              · simp [BitVec.setWidth_setWidth_of_le _ hwle,
                  Reg64s.get64_set64_of_ne _ rd ra _ hrad_ne.symm, hpa.2]
            · subst hw; rw [show cw = .W32 from rfl]
              rw [Reg64s.get64_set64_same]
              cases cc.interp s.status
              · simp [Reg64s.get64_set64_same, setWidth_64_setWidth .W32, hpb.2]
              · simp [Reg64s.get64_set64_of_ne _ rd ra _ hrad_ne.symm, hpa.2]
            · rw [Reg64s.get64_set64_of_ne _ rd r _ hr.symm, Reg64s.get64_set64_of_ne _ rd r _ hr.symm]
    | imm cb =>
      rcases hpb with rfl; simp only [selectFlagSeqIns] at hc
      have ha10 := (ne_of_not_mem_x64Scratch (hargs ra (by simp [PArg.gprs]))).1
      by_cases hrad : rd == ra
      · have heq := (beq_reg64_iff rd ra).1 hrad; subst ra
        simp only [hrad, ↓reduceIte, Option.some.injEq] at hc; subst hc
        simp only [emitClean_cons, emitClean_nil]
        have hrd10' : rd ≠ .r10 := ha10
        refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s .r10 (cb.setWidth 64))) ?_
        rintro s1 rfl
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_cmovcc cw hcw (x64NegCond cc) _ rd .r10)) ?_
        rintro s2 rfl
        refine ⟨?_, fun _ hw => ?_, fun r hr hsc => ?_, rfl, rfl, rfl⟩
        · rw [Reg64s.get64_set64_same, BitVec.setWidth_setWidth_of_le _ (width_bits_le_64 w),
            x64NegCond_interp]
          cases cc.interp s.status
          · simp [BitVec.setWidth_setWidth_of_le _ hwle,
              BitVec.setWidth_setWidth_of_le _ (width_bits_le_64 cw), Reg64s.get64_set64_same]
          · simp [BitVec.setWidth_setWidth_of_le _ hwle,
              Reg64s.get64_set64_of_ne _ .r10 rd _ hrd10'.symm, hpa.2]
        · subst hw; rw [show cw = .W32 from rfl]
          rw [Reg64s.get64_set64_same, x64NegCond_interp]
          cases cc.interp s.status
          · simp [Reg64s.get64_set64_same, setWidth_64_setWidth .W32]
          · simp [Reg64s.get64_set64_of_ne _ .r10 rd _ hrd10'.symm, hpa.2]
        · rw [Reg64s.get64_set64_of_ne _ rd r _ hr.symm,
            Reg64s.get64_set64_of_ne _ .r10 r _ (ne_of_not_mem_x64Scratch hsc).1.symm]
      · simp only [hrad, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hc; subst hc
        simp only [emitClean_cons, emitClean_nil]
        have hrad_ne : ra ≠ rd := fun h => hrad ((beq_reg64_iff rd ra).2 h.symm)
        refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s rd (cb.setWidth 64))) ?_
        rintro s1 rfl
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_cmovcc cw hcw cc _ rd ra)) ?_
        rintro s2 rfl
        refine ⟨?_, fun _ hw => ?_, fun r hr _ => ?_, rfl, rfl, rfl⟩
        · rw [Reg64s.get64_set64_same, BitVec.setWidth_setWidth_of_le _ (width_bits_le_64 w)]
          cases cc.interp s.status
          · simp [BitVec.setWidth_setWidth_of_le _ hwle,
              BitVec.setWidth_setWidth_of_le _ (width_bits_le_64 cw), Reg64s.get64_set64_same]
          · simp [BitVec.setWidth_setWidth_of_le _ hwle,
              Reg64s.get64_set64_of_ne _ rd ra _ hrad_ne.symm, hpa.2]
        · subst hw; rw [show cw = .W32 from rfl]
          rw [Reg64s.get64_set64_same]
          cases cc.interp s.status
          · simp [Reg64s.get64_set64_same, setWidth_64_setWidth .W32]
          · simp [Reg64s.get64_set64_of_ne _ rd ra _ hrad_ne.symm, hpa.2]
        · rw [Reg64s.get64_set64_of_ne _ rd r _ hr.symm, Reg64s.get64_set64_of_ne _ rd r _ hr.symm]
  | imm ca =>
    rcases hpa with rfl
    cases pb with
    | vec _ => simp [selectFlagSeqIns] at hc
    | gpr rb =>
      simp only [selectFlagSeqIns] at hc
      have hb10 := (ne_of_not_mem_x64Scratch (hargs rb (by simp [PArg.gprs]))).1
      by_cases hrbd : rd == rb
      · have heq := (beq_reg64_iff rd rb).1 hrbd; subst rb
        simp only [hrbd, ↓reduceIte, Option.some.injEq] at hc; subst hc
        simp only [emitClean_cons, emitClean_nil]
        have hrd10' : rd ≠ .r10 := hb10
        refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s .r10 (ca.setWidth 64))) ?_
        rintro s1 rfl
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_cmovcc cw hcw cc _ rd .r10)) ?_
        rintro s2 rfl
        refine ⟨?_, fun _ hw => ?_, fun r hr hsc => ?_, rfl, rfl, rfl⟩
        · rw [Reg64s.get64_set64_same, BitVec.setWidth_setWidth_of_le _ (width_bits_le_64 w)]
          cases cc.interp s.status
          · simp [BitVec.setWidth_setWidth_of_le _ hwle,
              Reg64s.get64_set64_of_ne _ .r10 rd _ hrd10'.symm, hpb.2]
          · simp [BitVec.setWidth_setWidth_of_le _ hwle,
              BitVec.setWidth_setWidth_of_le _ (width_bits_le_64 cw), Reg64s.get64_set64_same]
        · subst hw; rw [show cw = .W32 from rfl]
          rw [Reg64s.get64_set64_same]
          cases cc.interp s.status
          · simp [Reg64s.get64_set64_of_ne _ .r10 rd _ hrd10'.symm, hpb.2]
          · simp [Reg64s.get64_set64_same, setWidth_64_setWidth .W32]
        · rw [Reg64s.get64_set64_of_ne _ rd r _ hr.symm,
            Reg64s.get64_set64_of_ne _ .r10 r _ (ne_of_not_mem_x64Scratch hsc).1.symm]
      · simp only [hrbd, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hc; subst hc
        simp only [emitClean_cons, emitClean_nil]
        have hrbd_ne : rb ≠ rd := fun h => hrbd ((beq_reg64_iff rd rb).2 h.symm)
        refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s rd (ca.setWidth 64))) ?_
        rintro s1 rfl
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_cmovcc cw hcw (x64NegCond cc) _ rd rb)) ?_
        rintro s2 rfl
        refine ⟨?_, fun _ hw => ?_, fun r hr _ => ?_, rfl, rfl, rfl⟩
        · rw [Reg64s.get64_set64_same, BitVec.setWidth_setWidth_of_le _ (width_bits_le_64 w),
            x64NegCond_interp]
          cases cc.interp s.status
          · simp [BitVec.setWidth_setWidth_of_le _ hwle,
              Reg64s.get64_set64_of_ne _ rd rb _ hrbd_ne.symm, hpb.2]
          · simp [BitVec.setWidth_setWidth_of_le _ hwle,
              BitVec.setWidth_setWidth_of_le _ (width_bits_le_64 cw), Reg64s.get64_set64_same]
        · subst hw; rw [show cw = .W32 from rfl]
          rw [Reg64s.get64_set64_same, x64NegCond_interp]
          cases cc.interp s.status
          · simp [Reg64s.get64_set64_of_ne _ rd rb _ hrbd_ne.symm, hpb.2]
          · simp [Reg64s.get64_set64_same, setWidth_64_setWidth .W32]
        · rw [Reg64s.get64_set64_of_ne _ rd r _ hr.symm, Reg64s.get64_set64_of_ne _ rd r _ hr.symm]
    | imm cb =>
      rcases hpb with rfl; simp only [selectFlagSeqIns] at hc
      simp only [Option.some.injEq] at hc; subst hc
      simp only [emitClean_cons, emitClean_nil]
      refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s rd (cb.setWidth 64))) ?_
      rintro s1 rfl
      refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD _ .r10 (ca.setWidth 64))) ?_
      rintro s2 rfl
      refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_cmovcc cw hcw cc _ rd .r10)) ?_
      rintro s3 rfl
      refine ⟨?_, fun _ hw => ?_, fun r hr hsc => ?_, rfl, rfl, rfl⟩
      · rw [Reg64s.get64_set64_same, BitVec.setWidth_setWidth_of_le _ (width_bits_le_64 w)]
        cases cc.interp s.status
        · simp [BitVec.setWidth_setWidth_of_le _ hwle,
            BitVec.setWidth_setWidth_of_le _ (width_bits_le_64 cw),
            Reg64s.get64_set64_of_ne _ .r10 rd _ hrd10.symm, Reg64s.get64_set64_same]
        · simp [BitVec.setWidth_setWidth_of_le _ hwle,
            BitVec.setWidth_setWidth_of_le _ (width_bits_le_64 cw), Reg64s.get64_set64_same]
      · subst hw; rw [show cw = .W32 from rfl]
        rw [Reg64s.get64_set64_same]
        cases cc.interp s.status
        · simp [Reg64s.get64_set64_of_ne _ .r10 rd _ hrd10.symm, Reg64s.get64_set64_same,
            setWidth_64_setWidth .W32]
        · simp [Reg64s.get64_set64_same, setWidth_64_setWidth .W32]
      · rw [Reg64s.get64_set64_of_ne _ rd r _ hr.symm,
          Reg64s.get64_set64_of_ne _ .r10 r _ (ne_of_not_mem_x64Scratch hsc).1.symm,
          Reg64s.get64_set64_of_ne _ rd r _ hr.symm]

private theorem opSelect_z [Host] {E : Int64 → MachineData → Prop} (z32 : Bool) (w : Width)
    {pc : PArg Reg64 RegMm CondCode .bool}
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64}
    {c : List Instr} {clob : FlagMask} {b : Bool} {va vb : BitVec w.bits} {s : MachineData}
    (hz : z32 = true → w = .W32 ∧
      match pc with
      | .imm b0 => (if b0 then pa else pb) ≠ .gpr rd
      | .flag _ | .gpr _ => ∀ ra, ¬(pa = .gpr ra ∧ pb = .gpr ra ∧ ra = rd)
      | .vec _ => False)
    (hc : opSelectIns w pc pa pb rd = some (c, clob))
    (hrd : rd ∉ x64Scratch)
    (hargs : ∀ r ∈ pc.gprs ++ pa.gprs ++ pb.gprs, r ∉ x64Scratch)
    (hpc : x64Mach.PArgHolds s .bool pc b)
    (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va)
    (hpb : x64Mach.PArgHolds s (.bits w.bits) pb vb) :
    _root_.Program.wp (emitClean c)
      (OpPostZ z32 w rd (if b then va else vb) clob s) E s := by
  have hab : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ x64Scratch := fun r hr => hargs r (by simp_all)
  cases pc with
  | vec _ => simp [opSelectIns] at hc
  | imm b0 =>
    rcases hpc with rfl; unfold opSelectIns at hc
    cases z32
    · cases b0 <;> exact Program.wp.mono (opCopyBits_spec w hc (by assumption))
        fun _ h => ⟨h, fun h0 => by cases h0⟩
    · obtain ⟨rfl, hne⟩ := hz rfl
      cases b0 <;> exact opCopyBits_zero32_spec hne hc (by assumption)
  | flag cc =>
    simp only [opSelectIns] at hc
    rcases Option.map_eq_some_iff.mp hc with ⟨seq, hseq, hm⟩
    simp only [Prod.mk.injEq] at hm; rcases hm with ⟨rfl, rfl⟩
    have hcc : cc.interp s.status = b := hpc
    refine Program.wp.mono (wp_selectFlagSeq_z z32 w cc hz hseq hrd hab hpa hpb) ?_
    rintro s' ⟨hrd', hzr, hfr, hm', hz', hst'⟩
    refine ⟨⟨(GprHolds.bits_iff w _ _).2 (by rw [hrd', hcc]), hm',
      x64_frame_of_eq ?_ hz' (updFlags_of_status_eq hst' _)⟩,
      fun hz1 hw => by rw [hzr hz1 hw, hcc]⟩
    intro r hr; simp only [List.mem_cons, not_or] at hr
    exact hfr r hr.1 (by simp only [x64Scratch, List.mem_cons, List.mem_nil_iff, or_false]; exact fun h => h.elim hr.2.1 hr.2.2.1)
  | gpr rc =>
    simp only [opSelectIns] at hc
    rcases Option.map_eq_some_iff.mp hc with ⟨seq, hseq, hm⟩
    simp only [Prod.mk.injEq] at hm; rcases hm with ⟨rfl, rfl⟩
    simp only [emitClean_cons]
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_testb_self s rc hpc)) ?_
    rintro s1 ⟨st1, rfl, hnz⟩
    have hpa1 : x64Mach.PArgHolds { s with status := st1 } (.bits w.bits) pa va := by
      cases pa <;> exact hpa
    have hpb1 : x64Mach.PArgHolds { s with status := st1 } (.bits w.bits) pb vb := by
      cases pb <;> exact hpb
    refine Program.wp.mono (wp_selectFlagSeq_z z32 w .nz hz hseq hrd hab hpa1 hpb1) ?_
    rintro s2 ⟨hrd', hzr, hfr, hm', hz', _⟩
    refine ⟨⟨(GprHolds.bits_iff w _ _).2 (by rw [hrd', hnz]), hm',
      x64_frame_of_eq ?_ hz' (updFlags_maskAll _ _)⟩,
      fun hz1 hw => by rw [hzr hz1 hw, hnz]⟩
    intro r hr; simp only [List.mem_cons, not_or] at hr
    exact hfr r hr.1 (by simp only [x64Scratch, List.mem_cons, List.mem_nil_iff, or_false]; exact fun h => h.elim hr.2.1 hr.2.2.1)

theorem opSelect_spec [Host] {E : Int64 → MachineData → Prop} (w : Width)
    {pc : PArg Reg64 RegMm CondCode .bool}
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64}
    {c : List Instr} {clob : FlagMask} {b : Bool} {va vb : BitVec w.bits} {s : MachineData}
    (hc : opSelectIns w pc pa pb rd = some (c, clob))
    (hrd : rd ∉ x64Scratch)
    (hargs : ∀ r ∈ pc.gprs ++ pa.gprs ++ pb.gprs, r ∉ x64Scratch)
    (hpc : x64Mach.PArgHolds s .bool pc b)
    (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va)
    (hpb : x64Mach.PArgHolds s (.bits w.bits) pb vb) :
    _root_.Program.wp (emitClean c)
      (OpPost1 (.bits w.bits) rd (if b then va else vb) clob s) E s :=
  Program.wp.mono (opSelect_z false w (fun h => by cases h) hc hrd hargs hpc hpa hpb) fun _ h => h.1

theorem opSelect_zero32_spec [Host] {E : Int64 → MachineData → Prop}
    {pc : PArg Reg64 RegMm CondCode .bool}
    {pa pb : PArg Reg64 RegMm CondCode (.bits 32)} {rd : Reg64}
    {c : List Instr} {clob : FlagMask} {b : Bool} {va vb : BitVec 32} {s : MachineData}
    (hz : match pc with
      | .imm b0 => (if b0 then pa else pb) ≠ .gpr rd
      | .flag _ | .gpr _ => ∀ ra, ¬(pa = .gpr ra ∧ pb = .gpr ra ∧ ra = rd)
      | .vec _ => False)
    (hc : opSelectIns .W32 pc pa pb rd = some (c, clob))
    (hrd : rd ∉ x64Scratch)
    (hargs : ∀ r ∈ pc.gprs ++ pa.gprs ++ pb.gprs, r ∉ x64Scratch)
    (hpc : x64Mach.PArgHolds s .bool pc b)
    (hpa : x64Mach.PArgHolds s (.bits 32) pa va)
    (hpb : x64Mach.PArgHolds s (.bits 32) pb vb) :
    _root_.Program.wp (emitClean c)
      (OpPostZ true .W32 rd (if b then va else vb) clob s) E s :=
  opSelect_z true .W32 (fun _ => ⟨rfl, hz⟩) hc hrd hargs hpc hpa hpb

/-! ## 3. `opShift_spec` (`shl`/`lshr`/`ashr`/`rotl`/`rotr`, BMI2 + 8/16-bit mask trap) -/

theorem reg64s_ext {r1 r2 : Reg64s} (h : ∀ r : Reg64, r1.get64 r = r2.get64 r) :
    r1 = r2 := by
  have ui : ∀ u1 u2 : UInt64, u1.toBitVec = u2.toBitVec → u1 = u2 := fun ⟨_⟩ ⟨_⟩ he => by
    cases he; rfl
  rcases r1 with ⟨a, b, c, d, e, f, g, h0, i, j, k, l, m, n, o, p⟩
  rcases r2 with ⟨a', b', c', d', e', f', g', h0', i', j', k', l', m', n', o', p'⟩
  simp only [Reg64s.mk.injEq]
  exact ⟨ui _ _ (h .rax), ui _ _ (h .rbx), ui _ _ (h .rcx), ui _ _ (h .rdx),
    ui _ _ (h .rsi), ui _ _ (h .rdi), ui _ _ (h .rsp), ui _ _ (h .rbp),
    ui _ _ (h .r8), ui _ _ (h .r9), ui _ _ (h .r10), ui _ _ (h .r11),
    ui _ _ (h .r12), ui _ _ (h .r13), ui _ _ (h .r14), ui _ _ (h .r15)⟩

theorem ShiftKind.eval_zero {n : Nat} (sk : ShiftKind) (x : BitVec n) : sk.eval x 0 = x := by
  cases sk with
  | rotl | rotr => apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [ShiftKind.eval, hi]
  | shl | lshr | ashr => simp [ShiftKind.eval]

private theorem shiftMask_imm_eq (w : Width) (c : BitVec w.bits) :
    ∀ [Labels] (p : Std.Rco Int64) (s : MachineData),
      (ShiftCountExpr.imm8 (.int64 (Int64.ofNat (c.toNat % w.bits)))).interpMasked s p w =
        c.toNat % w.bits := by
  intro _ p s
  have hlt := Nat.mod_lt c.toNat (width_bits_pos w)
  have h5 : (31 : Nat) = 2 ^ 5 - 1 := rfl
  have h6 : (63 : Nat) = 2 ^ 6 - 1 := rfl
  cases w <;>
    simp only [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, ConstExpr.interp,
      BitVec.take, BitVec.extractLsb'_toNat, Int64.ofNat, Int64.toBitVec,
      BitVec.toNat_ofNat, Width.bits, Nat.shiftRight_zero, h5, h6,
      Nat.and_two_pow_sub_one_eq_mod] at hlt ⊢ <;> omega

private theorem setRegW_eq_set64_z (w : Width) (s : MachineData) (rd : Reg64) (v : w.type)
    (st : StatusFlags) :
    ∃ rv, rv.setWidth w.bits = v ∧ (w = .W32 → rv = v.setWidth 64) ∧
      ({ s with regs := s.regs.set (regW w rd) v, status := st } : MachineData) =
        { s with regs := s.regs.set64 rd rv, status := st } := by
  cases w <;> simp only [regW, Reg64s.set]
  · exact ⟨_, replaceLow_setWidth_le (by decide) _ _, (fun h => by cases h), rfl⟩
  · exact ⟨_, replaceLow_setWidth_le (by decide) _ _, (fun h => by cases h), rfl⟩
  · exact ⟨_, by simp [Width.bits], (fun _ => by simp), rfl⟩
  · exact ⟨_, rfl, (fun h => by cases h), rfl⟩

theorem setRegW_eq_set64 (w : Width) (s : MachineData) (rd : Reg64) (v : w.type)
    (st : StatusFlags) :
    ∃ rv, rv.setWidth w.bits = v ∧
      ({ s with regs := s.regs.set (regW w rd) v, status := st } : MachineData) =
        { s with regs := s.regs.set64 rd rv, status := st } :=
  let ⟨rv, h1, _, h2⟩ := setRegW_eq_set64_z w s rd v st; ⟨rv, h1, h2⟩

private theorem fallsTo_shiftW_z (w : Width) (sk : ShiftKind) (s : MachineData) (rd : Reg64)
    (ce : ShiftCountExpr) (k : Nat) (hk_lt : k < w.bits)
    (hk : ∀ [Labels] (p : Std.Rco Int64), ce.interpMasked s p w = k) :
    Directive.FallsTo (insW w (sk.toOp (.reg (regW w rd)) ce)) s (fun s' =>
      ∃ rv status, rv.setWidth w.bits = sk.eval ((s.regs.get64 rd).setWidth w.bits) k ∧
        (w = .W32 → rv = (sk.eval ((s.regs.get64 rd).setWidth w.bits) k).setWidth 64) ∧
        (sk.isRot = true → status.pf = s.status.pf ∧ status.zf = s.status.zf ∧ status.sf = s.status.sf) ∧
        s' = { s with regs := s.regs.set64 rd rv, status }) := by
  intro _ p _ _ _ hcont
  have hkp := hk p
  simp only [ShiftCountExpr.interpMasked, ShiftCountExpr.interp] at hkp
  by_cases hk0 : k = 0
  · subst hk0
    cases ce <;> cases sk <;> cases w <;>
      simp only [ShiftKind.toOp, insW, regW, t_step_simp] at hkp ⊢ <;>
      rw [hkp] <;> simp only [beq_self_eq_true, ↓reduceIte] <;>
      { obtain ⟨rv, hrv, hrvz, hs⟩ := setRegW_eq_set64_z _ s rd _ s.status
        exact hcont _ ⟨rv, s.status, hrv.trans (ShiftKind.eval_zero _ _).symm,
          fun hw => (hrvz hw).trans (by rw [ShiftKind.eval_zero]), fun _ => ⟨rfl, rfl, rfl⟩, hs⟩ }
  · have hk0' : (k == 0) = false := beq_false_of_ne hk0
    have hlt8 : w = .W8 → k < 8 := fun h => by rw [h] at hk_lt; exact hk_lt
    have hlt16 : w = .W16 → k < 16 := fun h => by rw [h] at hk_lt; exact hk_lt
    have hlt32 : w = .W32 → k < 32 := fun h => by rw [h] at hk_lt; exact hk_lt
    have hlt64 : w = .W64 → k < 64 := fun h => by rw [h] at hk_lt; exact hk_lt
    cases ce <;> cases sk <;> cases w <;>
      simp only [ShiftKind.toOp, insW, regW, t_step_simp, Effects.All] at hkp ⊢ <;>
      rw [hkp] <;>
      (try simp only [hk0', Bool.false_eq_true, ↓reduceIte]) <;>
      (try simp only [hlt8 rfl, ↓reduceIte]) <;>
      (try simp only [hlt16 rfl, ↓reduceIte]) <;>
      (try simp only [hlt32 rfl, ↓reduceIte]) <;>
      (try simp only [hlt64 rfl, ↓reduceIte]) <;>
      (try intro af) <;>
      { by_cases hk1 : k = 1
        · subst hk1; simp only [beq_self_eq_true, ↓reduceIte]
          try dsimp only [ShiftKind.eval, ShiftKind.isRot]
          obtain ⟨rv, hrv, hrvz, hs⟩ := setRegW_eq_set64_z _ s rd _ _
          exact hcont _ ⟨rv, _, hrv, hrvz,
            (fun h => by solve | cases h | exact ⟨rfl, rfl, rfl⟩), hs⟩
        · simp only [beq_false_of_ne hk1, Bool.false_eq_true, ↓reduceIte]; intro _
          try dsimp only [ShiftKind.eval, ShiftKind.isRot]
          obtain ⟨rv, hrv, hrvz, hs⟩ := setRegW_eq_set64_z _ s rd _ _
          exact hcont _ ⟨rv, _, hrv, hrvz,
            (fun h => by solve | cases h | exact ⟨rfl, rfl, rfl⟩), hs⟩ }

private theorem fallsTo_shiftW (w : Width) (sk : ShiftKind) (s : MachineData) (rd : Reg64)
    (ce : ShiftCountExpr) (k : Nat) (hk_lt : k < w.bits)
    (hk : ∀ [Labels] (p : Std.Rco Int64), ce.interpMasked s p w = k) :
    Directive.FallsTo (insW w (sk.toOp (.reg (regW w rd)) ce)) s (fun s' =>
      ∃ rv status, rv.setWidth w.bits = sk.eval ((s.regs.get64 rd).setWidth w.bits) k ∧
        (sk.isRot = true → status.pf = s.status.pf ∧ status.zf = s.status.zf ∧
          status.sf = s.status.sf) ∧
        s' = { s with regs := s.regs.set64 rd rv, status }) := by
  intro _ _ _ _ _ hcont
  exact fallsTo_shiftW_z w sk s rd ce k hk_lt hk _ _ _ _ fun s' ⟨rv, st, h1, _, hrot, h2⟩ =>
    hcont s' ⟨rv, st, h1, hrot, h2⟩

private theorem cl_interpMasked_of_eq (w : Width) (s : MachineData) (vb : BitVec w.bits)
    (hmod : (s.regs.get64 .rcx).toNat % 2 ^ 8 = vb.toNat % w.bits)
    (hw_lt : w = .W8 ∨ w = .W16 → (s.regs.get64 .rcx).toNat % 2 ^ 8 < w.bits) :
    ∀ [Labels] (p : Std.Rco Int64), ShiftCountExpr.cl.interpMasked s p w = vb.toNat % w.bits := by
  intro _ p
  have h5 : (31 : Nat) = 2 ^ 5 - 1 := rfl
  have h6 : (63 : Nat) = 2 ^ 6 - 1 := rfl
  dsimp only [Reg64s.get64, Width.bits] at hmod hw_lt
  cases w with
  | W8 =>
    have h := hw_lt (Or.inl rfl)
    simp only [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, BitVec.take,
      BitVec.extractLsb'_toNat, Nat.shiftRight_zero, Width.bits, h5, Nat.and_two_pow_sub_one_eq_mod]
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h (by decide))]; exact hmod
  | W16 =>
    have h := hw_lt (Or.inr rfl)
    simp only [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, BitVec.take,
      BitVec.extractLsb'_toNat, Nat.shiftRight_zero, Width.bits, h5, Nat.and_two_pow_sub_one_eq_mod]
    rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h (by decide))]; exact hmod
  | W32 =>
    dsimp only [Reg64s.get64, Width.bits] at hmod
    simp only [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, BitVec.take,
      BitVec.extractLsb'_toNat, Nat.shiftRight_zero, Width.bits, h5, Nat.and_two_pow_sub_one_eq_mod]
    rw [Nat.mod_mod_of_dvd _ (by decide : 2 ^ 5 ∣ 2 ^ 8), show (2 ^ 5 : Nat) = 32 from rfl,
      ← Nat.mod_mod_of_dvd _ (by decide : 32 ∣ 2 ^ 8), hmod, Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))]
  | W64 =>
    dsimp only [Reg64s.get64, Width.bits] at hmod
    simp only [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, BitVec.take,
      BitVec.extractLsb'_toNat, Nat.shiftRight_zero, Width.bits, h6, Nat.and_two_pow_sub_one_eq_mod]
    rw [Nat.mod_mod_of_dvd _ (by decide : 2 ^ 6 ∣ 2 ^ 8), show (2 ^ 6 : Nat) = 64 from rfl,
      ← Nat.mod_mod_of_dvd _ (by decide : 64 ∣ 2 ^ 8), hmod, Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))]

private theorem wp_shiftMaskRcx [Host] {E : Int64 → MachineData → Prop}
    (w : Width) (s : MachineData) (regs0 : Reg64s) {rcxVal : BitVec 64} {vb : BitVec w.bits}
    (hget : regs0.get64 .rcx = rcxVal) (hvb : rcxVal.setWidth w.bits = vb) :
    _root_.Program.wp (shiftMaskRcx w) (fun s' => ∃ rcxM stM,
      (∀ [Labels] (p : Std.Rco Int64), ShiftCountExpr.cl.interpMasked s' p w = vb.toNat % w.bits) ∧
      (w = .W32 ∨ w = .W64 → stM.pf = s.status.pf ∧ stM.zf = s.status.zf ∧ stM.sf = s.status.sf) ∧
      s' = { s with regs := regs0.set64 .rcx rcxM, status := stM }) E { s with regs := regs0 } := by
  have hlt : ∀ {m : Nat} (hm : m = 3 ∨ m = 4),
      Directive.FallsTo (ins32 (.and (.reg (d .rcx)) (.imm (.int64 (Int64.ofInt (2 ^ m - 1))))))
        { s with regs := regs0 } (fun s' => ∃ st',
          (s'.regs.get64 .rcx).toNat = rcxVal.toNat % 2 ^ m ∧
          s' = { s with regs := regs0.set64 .rcx (s'.regs.get64 .rcx), status := st' }) := by
    intro m hm _ _ _ _ _ hk
    rcases hm with rfl | rfl <;>
      (simp only [t_step_simp, ConstExpr.interp, Effects.All, Reg64s.set, hget]; intro _; refine hk _ ⟨_, ?_, rfl⟩)
    · have h7 : (Int64.toBitVec (Int64.ofInt (2 ^ 3 - 1))).truncate Width.W32.bits = 7#32 := by decide
      rw [h7, BitVec.zeroExtend_eq_setWidth, Reg64s.get64_set64_same, BitVec.toNat_setWidth, BitVec.toNat_and,
        show (7#32 : BitVec 32).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_setWidth]
      simp only [Width.bits]
      rw [Nat.mod_mod_of_dvd _ (by decide : 2 ^ 3 ∣ 2 ^ 32),
        Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide : 2 ^ 3 ≤ 2 ^ 64))]
    · have h15 : (Int64.toBitVec (Int64.ofInt (2 ^ 4 - 1))).truncate Width.W32.bits = 15#32 := by decide
      rw [h15, BitVec.zeroExtend_eq_setWidth, Reg64s.get64_set64_same, BitVec.toNat_setWidth, BitVec.toNat_and,
        show (15#32 : BitVec 32).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_setWidth]
      simp only [Width.bits]
      rw [Nat.mod_mod_of_dvd _ (by decide : 2 ^ 4 ∣ 2 ^ 32),
        Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide : 2 ^ 4 ≤ 2 ^ 64))]
  have hvb_nat := congrArg BitVec.toNat hvb
  simp only [BitVec.toNat_setWidth, Width.bits] at hvb_nat
  have hrcx0 : regs0.rcx.toBitVec = rcxVal := hget
  have hregs_eq : regs0 = regs0.set64 .rcx rcxVal := reg64s_ext fun r => by
    by_cases hr : r = .rcx
    · rw [hr, Reg64s.get64_set64_same, hget]
    · rw [Reg64s.get64_set64_of_ne _ .rcx r _ (Ne.symm hr)]
  cases w with
  | W32 =>
    simp only [shiftMaskRcx]; refine _root_.Program.wp_nil ⟨rcxVal, s.status, ?_, fun _ => ⟨rfl, rfl, rfl⟩, ?_⟩
    · intro _ p
      have h5 : (31 : Nat) = 2 ^ 5 - 1 := rfl
      simp only [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, BitVec.take,
        BitVec.extractLsb'_toNat, Nat.shiftRight_zero, hrcx0, Width.bits, h5, Nat.and_two_pow_sub_one_eq_mod]
      rw [Nat.mod_mod_of_dvd _ (by decide : 2 ^ 5 ∣ 2 ^ 8), show (2 ^ 5 : Nat) = 32 from rfl,
        ← hvb_nat, Nat.mod_mod_of_dvd _ (by decide : 32 ∣ 2 ^ 32)]
    · exact congrArg (fun rg => { s with regs := rg }) hregs_eq
  | W64 =>
    simp only [shiftMaskRcx]; refine _root_.Program.wp_nil ⟨rcxVal, s.status, ?_, fun _ => ⟨rfl, rfl, rfl⟩, ?_⟩
    · intro _ p
      have h6 : (63 : Nat) = 2 ^ 6 - 1 := rfl
      simp only [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, BitVec.take,
        BitVec.extractLsb'_toNat, Nat.shiftRight_zero, hrcx0, Width.bits, h6, Nat.and_two_pow_sub_one_eq_mod]
      rw [Nat.mod_mod_of_dvd _ (by decide : 2 ^ 6 ∣ 2 ^ 8), show (2 ^ 6 : Nat) = 64 from rfl,
        ← hvb_nat, Nat.mod_mod_of_dvd _ (by decide : 64 ∣ 2 ^ 64)]
    · exact congrArg (fun rg => { s with regs := rg }) hregs_eq
  | W8 =>
    simp only [shiftMaskRcx]
    refine Program.wp.mono (Directive.FallsTo.wp (hlt (Or.inl rfl))) ?_
    rintro s' ⟨st', hnat, hs'⟩
    have hlt8 : (s'.regs.get64 .rcx).toNat < 8 := hnat ▸ Nat.mod_lt _ (by decide)
    have hmod8 : (s'.regs.get64 .rcx).toNat % 2 ^ 8 = vb.toNat % 8 := by
      rw [hnat, Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)),
        ← hvb_nat, Nat.mod_mod_of_dvd _ (by decide)]
    refine ⟨s'.regs.get64 .rcx, st', cl_interpMasked_of_eq .W8 s' vb hmod8
        (fun _ => by rw [Nat.mod_eq_of_lt (Nat.lt_trans hlt8 (by decide))]; exact hlt8), ?_, ?_⟩
    · intro h; rcases h with h | h <;> cases h
    · rw [hs']; dsimp only; rw [Reg64s.get64_set64_same]
  | W16 =>
    simp only [shiftMaskRcx]
    refine Program.wp.mono (Directive.FallsTo.wp (hlt (Or.inr rfl))) ?_
    rintro s' ⟨st', hnat, hs'⟩
    have hlt16 : (s'.regs.get64 .rcx).toNat < 16 := hnat ▸ Nat.mod_lt _ (by decide)
    have hmod16 : (s'.regs.get64 .rcx).toNat % 2 ^ 8 = vb.toNat % 16 := by
      rw [hnat, Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt _ (by decide)) (by decide)),
        ← hvb_nat, Nat.mod_mod_of_dvd _ (by decide)]
    refine ⟨s'.regs.get64 .rcx, st', cl_interpMasked_of_eq .W16 s' vb hmod16
        (fun _ => by rw [Nat.mod_eq_of_lt (Nat.lt_trans hlt16 (by decide))]; exact hlt16), ?_, ?_⟩
    · intro h; rcases h with h | h <;> cases h
    · rw [hs']; dsimp only; rw [Reg64s.get64_set64_same]

private theorem rotateRight_sub_eq_rotateLeft {n : Nat} (a : BitVec n) {k : Nat}
    (hk0 : 0 < k) (hk : k < n) :
    a.rotateRight (n - k) = a.rotateLeft k := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_rotateRight, BitVec.getLsbD_rotateLeft, hi, decide_true, Bool.true_and,
    Nat.mod_eq_of_lt (show n - k < n by omega), Nat.mod_eq_of_lt hk,
    show n - (n - k) = k from by omega]

private theorem fallsTo_bmi2ShiftW_z (w : Width) (hw : w = .W32 ∨ w = .W64) (sk : ShiftKind)
    {bmiOp : Reg w → RegOrMem w → Reg w → Operation w} (hbmi : sk.toBmi2Op? = some bmiOp)
    (s : MachineData) (rd ra rb : Reg64) :
    Directive.FallsTo (insW w (bmiOp (regW w rd) (.reg (regW w ra)) (regW w rb))) s (fun s' =>
      ∃ rv, rv.setWidth w.bits = sk.eval ((s.regs.get64 ra).setWidth w.bits)
          (((s.regs.get64 rb).setWidth w.bits).toNat % w.bits) ∧
        (w = .W32 → rv = (sk.eval ((s.regs.get64 ra).setWidth w.bits)
          (((s.regs.get64 rb).setWidth w.bits).toNat % w.bits)).setWidth 64) ∧
        s' = { s with regs := s.regs.set64 rd rv }) := by
  intro _ _ _ _ _ hcont
  have h5 : (31 : Nat) = 2 ^ 5 - 1 := rfl
  have h6 : (63 : Nat) = 2 ^ 6 - 1 := rfl
  have hm32 : ∀ n : Nat, n &&& 31 = n % 32 := fun n => by
    rw [h5, Nat.and_two_pow_sub_one_eq_mod]
  have hm64 : ∀ n : Nat, n &&& 63 = n % 64 := fun n => by
    rw [h6, Nat.and_two_pow_sub_one_eq_mod]
  cases sk <;> simp only [ShiftKind.toBmi2Op?, Option.some.injEq, reduceCtorEq] at hbmi
  all_goals
    subst hbmi; rcases hw with rfl | rfl
    · simp only [insW, regW, t_step_simp, MachineData.setReg, Reg64s.set]
      refine hcont _ ⟨_, ?_, ?_, rfl⟩
      · simp only [Width.bits, ShiftKind.eval, show (32 - 1 : Nat) = 31 from rfl,
          BitVec.zeroExtend_eq_setWidth, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64),
          BitVec.setWidth_eq, hm32]; try rfl
      · intro _; simp only [Width.bits, ShiftKind.eval, show (32 - 1 : Nat) = 31 from rfl,
          BitVec.zeroExtend_eq_setWidth, hm32]; try rfl
    · simp only [insW, regW, t_step_simp, MachineData.setReg, Reg64s.set]
      refine hcont _ ⟨_, ?_, (fun h => by cases h), rfl⟩
      simp only [Width.bits, ShiftKind.eval, show (64 - 1 : Nat) = 63 from rfl,
        BitVec.setWidth_eq, hm64]; try rfl

private theorem fallsTo_bmi2ShiftW (w : Width) (hw : w = .W32 ∨ w = .W64) (sk : ShiftKind)
    {bmiOp : Reg w → RegOrMem w → Reg w → Operation w} (hbmi : sk.toBmi2Op? = some bmiOp)
    (s : MachineData) (rd ra rb : Reg64) :
    Directive.FallsTo (insW w (bmiOp (regW w rd) (.reg (regW w ra)) (regW w rb))) s (fun s' =>
      ∃ rv, rv.setWidth w.bits = sk.eval ((s.regs.get64 ra).setWidth w.bits)
          (((s.regs.get64 rb).setWidth w.bits).toNat % w.bits) ∧
        s' = { s with regs := s.regs.set64 rd rv }) := by
  intro _ _ _ _ _ hcont
  exact fallsTo_bmi2ShiftW_z w hw sk hbmi s rd ra rb _ _ _ _ fun s' ⟨rv, h1, _, h2⟩ =>
    hcont s' ⟨rv, h1, h2⟩

private theorem fallsTo_rorxW_z (w : Width) (hw : w = .W32 ∨ w = .W64)
    (s : MachineData) (rd ra : Reg64) (cnt : Nat) (hcnt : cnt < w.bits) :
    Directive.FallsTo (insW w (.rorx (regW w rd) (.reg (regW w ra)) (.int64 (Int64.ofNat cnt)))) s
      (fun s' =>
        ∃ rv, rv.setWidth w.bits = ((s.regs.get64 ra).setWidth w.bits).rotateRight cnt ∧
          (w = .W32 → rv = (((s.regs.get64 ra).setWidth w.bits).rotateRight cnt).setWidth 64) ∧
          s' = { s with regs := s.regs.set64 rd rv }) := by
  intro _ _ _ _ _ hcont
  have h5 : (31 : Nat) = 2 ^ 5 - 1 := rfl
  have h6 : (63 : Nat) = 2 ^ 6 - 1 := rfl
  have h256 : cnt < 256 := by rcases hw with rfl | rfl <;> simp only [Width.bits] at hcnt <;> omega
  have htk : ((Int64.ofNat cnt).toBitVec.take 8).toNat = cnt := by
    simp only [BitVec.take, BitVec.extractLsb'_toNat, Int64.ofNat, Int64.toBitVec,
      BitVec.toNat_ofNat, Nat.shiftRight_zero]
    rw [Nat.mod_eq_of_lt (Nat.lt_trans h256 (by decide)), Nat.mod_eq_of_lt h256]
  rcases hw with rfl | rfl <;>
    simp only [insW, regW, t_step_simp, MachineData.setReg, Reg64s.set,
      Width.bits, ConstExpr.interp, htk] at hcnt ⊢
  · rw [show (32 - 1 : Nat) = 31 from rfl, h5, Nat.and_two_pow_sub_one_eq_mod,
      show (2 ^ 5 : Nat) = 32 from rfl, Nat.mod_eq_of_lt hcnt]
    exact hcont _ ⟨_, by simp, (fun _ => by simp), rfl⟩
  · rw [show (64 - 1 : Nat) = 63 from rfl, h6, Nat.and_two_pow_sub_one_eq_mod,
      show (2 ^ 6 : Nat) = 64 from rfl, Nat.mod_eq_of_lt hcnt]
    exact hcont _ ⟨_, by simp, (fun h => by cases h), rfl⟩

private theorem fallsTo_rorxW (w : Width) (hw : w = .W32 ∨ w = .W64)
    (s : MachineData) (rd ra : Reg64) (cnt : Nat) (hcnt : cnt < w.bits) :
    Directive.FallsTo (insW w (.rorx (regW w rd) (.reg (regW w ra)) (.int64 (Int64.ofNat cnt)))) s
      (fun s' =>
        ∃ rv, rv.setWidth w.bits = ((s.regs.get64 ra).setWidth w.bits).rotateRight cnt ∧
          s' = { s with regs := s.regs.set64 rd rv }) := by
  intro _ _ _ _ _ hcont
  exact fallsTo_rorxW_z w hw s rd ra cnt hcnt _ _ _ _ fun s' ⟨rv, h1, _, h2⟩ =>
    hcont s' ⟨rv, h1, h2⟩

private theorem opShift_z [Host] {E : Int64 → MachineData → Prop} (z32 : Bool) (w : Width)
    (sk : ShiftKind) {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64}
    {c : List Instr} {clob : FlagMask} {va vb : BitVec w.bits} {s : MachineData}
    (hz32 : z32 = true → w = .W32 ∧ match pb with
      | .imm cb => cb.toNat % 32 ≠ 0 | .gpr _ => true | _ => False)
    (hc : opShiftIns w sk pa pb rd = some (c, clob))
    (_hrd : rd ∉ x64Scratch)
    (hargs : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ x64Scratch)
    (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va)
    (hpb : x64Mach.PArgHolds s (.bits w.bits) pb vb) :
    _root_.Program.wp (emitClean c)
      (OpPostZ z32 w rd (sk.eval va (vb.toNat % w.bits)) clob s) E s := by
  cases pb with
  | vec _ => simp [opShiftIns] at hc
  | imm cb =>
    rcases hpb with rfl; dsimp only [opShiftIns] at hc
    by_cases hcnt : (cb.toNat % w.bits == 0) = true
    · simp only [hcnt, ↓reduceIte] at hc
      have hnz : z32 = false := by
        cases hb : z32
        · rfl
        · have ⟨hw, hne⟩ := hz32 hb; subst hw; simp_all
      subst hnz
      rw [beq_iff_eq.1 hcnt, sk.eval_zero]
      exact Program.wp.mono (opCopyBits_spec w hc hpa) fun _ h => ⟨h, fun h0 => by cases h0⟩
    · have hcnt_ne : cb.toNat % w.bits ≠ 0 := fun h => hcnt ((beq_iff_eq).2 h)
      have hcnt_pos : 0 < cb.toNat % w.bits := Nat.pos_of_ne_zero hcnt_ne
      have hcnt_lt : cb.toNat % w.bits < w.bits := Nat.mod_lt _ (width_bits_pos w)
      simp only [hcnt, Bool.false_eq_true, ↓reduceIte] at hc
      by_cases hbmi : ((w == .W32 || w == .W64) && sk.isRot) = true
      · simp only [hbmi, ↓reduceIte] at hc
        have hw : w = .W32 ∨ w = .W64 := by cases w <;> simp_all
        have hrot : sk.isRot = true := (Bool.and_eq_true .. |>.mp hbmi).2
        have hrot_eq : va.rotateRight (if sk == .rotl then w.bits - cb.toNat % w.bits
            else cb.toNat % w.bits) = sk.eval va (cb.toNat % w.bits) := by
          cases sk <;> simp [ShiftKind.isRot] at hrot
          · simp only [beq_self_eq_true, ↓reduceIte, ShiftKind.eval]
            exact rotateRight_sub_eq_rotateLeft va hcnt_pos hcnt_lt
          · rfl
        have hrot_lt : (if sk == .rotl then w.bits - cb.toNat % w.bits
            else cb.toNat % w.bits) < w.bits := by
          split <;> omega
        cases pa with
        | vec _ => cases hc
        | gpr ra =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
          simp only [emitClean_cons, emitClean_nil]
          refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_rorxW_z w hw s rd ra _ hrot_lt)) ?_
          rintro s' ⟨rv, hrv, hrvz, rfl⟩
          refine ⟨⟨(GprHolds.bits_iff w _ _).2 (by rw [Reg64s.get64_set64_same, hrv,
            (GprHolds.bits_iff w _ _).1 hpa, hrot_eq]), rfl,
            x64_frame_of_eq (fun r hr => ?_) rfl (updFlags_of_status_eq rfl _)⟩, fun _ hw32 => by
            rw [Reg64s.get64_set64_same, hrvz hw32, (GprHolds.bits_iff w _ _).1 hpa, hrot_eq]⟩
          simp only [List.mem_cons, not_or] at hr
          exact Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1)
        | imm ca =>
          rcases hpa with rfl
          simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
          simp only [emitClean_cons, emitClean_nil]
          refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_moviD s rd _)) ?_
          rintro s' rfl
          exact OpPostZ.of_set64 (setWidth_64_setWidth w _) (fun _ _ => rfl)
            (updFlags_of_status_eq rfl _)
      · simp only [hbmi, Bool.false_eq_true, ↓reduceIte] at hc
        have hsetup : ∃ seq : List Instr, c = seq ++ [x64InsI w (sk.toOp (.reg (regW w rd))
            (.imm8 (.int64 (Int64.ofNat (cb.toNat % w.bits)))))] ∧
            clob = (if sk.isRot then maskCF ||| maskOF else maskAll) ∧
            _root_.Program.wp (emitClean seq) (fun s1 => (s1.regs.get64 rd).setWidth w.bits = va ∧
              (∀ r, r ≠ rd → s1.regs.get64 r = s.regs.get64 r) ∧
              s1.dmem = s.dmem ∧ s1.zmms = s.zmms ∧ s1.status = s.status) E s := by
          cases pa with
          | vec _ => cases hc
          | gpr ra =>
            rcases hc with ⟨rfl, rfl⟩
            exact ⟨_, rfl, rfl, by
              simpa [apply_ite emitClean, emitClean_cons, emitClean_nil, movW, movWI] using
                wp_optMovW w s rd ra (GprHolds.bits_iff w _ _ |>.1 hpa)⟩
          | imm ca =>
            rcases hpa with rfl
            rcases hc with ⟨rfl, rfl⟩
            refine ⟨_, rfl, rfl, ?_⟩
            simp only [emitClean_cons, emitClean_nil]
            refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_moviD s rd (ca.setWidth 64))) ?_
            rintro s1 rfl
            exact ⟨by simp [setWidth_64_setWidth],
              fun r hr => Reg64s.get64_set64_of_ne _ rd r _ hr.symm, rfl, rfl, rfl⟩
        rcases hsetup with ⟨seq, rfl, rfl, hwp⟩
        simp only [emitClean_append, emitClean_cons, emitClean_nil]
        refine Program.wp.append hwp ?_; rintro s1 ⟨hrd1, hfr1, hm1, hz1, hst1⟩
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_shiftW_z w sk s1 rd
          (.imm8 (.int64 (Int64.ofNat (cb.toNat % w.bits)))) (cb.toNat % w.bits)
          hcnt_lt (fun p => shiftMask_imm_eq w cb p s1))) ?_
        rintro s2 ⟨rv, st, hrv, hrvz, hrot, rfl⟩
        refine ⟨⟨(GprHolds.bits_iff w _ _).2 (by rw [Reg64s.get64_set64_same, hrv, hrd1]), hm1,
          x64_frame_of_eq (fun r hr => ?_) hz1 ?_⟩, fun _ hw32 => by
          rw [Reg64s.get64_set64_same, hrvz hw32, hrd1]⟩
        · simp only [List.mem_cons, not_or] at hr
          rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1), hfr1 r hr.1]
        · by_cases hr : sk.isRot = true
          · simp only [hr, ↓reduceIte]; obtain ⟨h1, h2, h3⟩ := hrot hr
            exact updFlags_maskCF_OF (h1.trans (congrArg StatusFlags.pf hst1))
              (h2.trans (congrArg StatusFlags.zf hst1)) (h3.trans (congrArg StatusFlags.sf hst1))
          · simp only [hr, Bool.false_eq_true, ↓reduceIte]; exact updFlags_maskAll _ _
  | gpr rb =>
    dsimp only [opShiftIns] at hc
    have hvb : (s.regs.get64 rb).setWidth w.bits = vb := (GprHolds.bits_iff w _ _).1 hpb
    by_cases hbmi : ((w == .W32 || w == .W64) && !sk.isRot) = true
    · simp only [hbmi, ↓reduceIte] at hc
      have hw : w = .W32 ∨ w = .W64 := by cases w <;> simp_all
      have hnrot : !sk.isRot = true := (Bool.and_eq_true .. |>.mp hbmi).2
      obtain ⟨bmiOp, hbmiOp⟩ : ∃ bmiOp, sk.toBmi2Op? = some bmiOp := by
        cases sk <;> simp [ShiftKind.isRot] at hnrot <;> exact ⟨_, rfl⟩
      rw [hbmiOp] at hc
      cases pa with
      | vec _ => simp at hc
      | gpr ra =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
        simp only [emitClean_cons, emitClean_nil]
        refine Program.wp.mono
          (Directive.FallsTo.wp (fallsTo_bmi2ShiftW_z w hw sk hbmiOp s rd ra rb)) ?_
        rintro s' ⟨rv, hrv, hrvz, rfl⟩
        refine ⟨⟨(GprHolds.bits_iff w _ _).2 (by rw [Reg64s.get64_set64_same, hrv,
          (GprHolds.bits_iff w _ _).1 hpa, hvb]), rfl,
          x64_frame_of_eq (fun r hr => ?_) rfl (updFlags_of_status_eq rfl _)⟩, fun _ hw32 => by
          rw [Reg64s.get64_set64_same, hrvz hw32, (GprHolds.bits_iff w _ _).1 hpa, hvb]⟩
        simp only [List.mem_cons, not_or] at hr
        exact Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1)
      | imm ca =>
        rcases hpa with rfl
        simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
        simp only [emitClean_cons, emitClean_nil]
        have hrb_ne := (ne_of_not_mem_x64Scratch (hargs rb (by simp [PArg.gprs]))).2
        refine Program.wp.cons
          (Directive.FallsTo.wp (fallsTo_moviD s .r11 (ca.setWidth 64))) ?_
        rintro s1 rfl
        refine Program.wp.mono
          (Directive.FallsTo.wp (fallsTo_bmi2ShiftW_z w hw sk hbmiOp _ rd .r11 rb)) ?_
        rintro s2 ⟨rv, hrv, hrvz, rfl⟩
        refine ⟨⟨(GprHolds.bits_iff w _ _).2 (by
          rw [Reg64s.get64_set64_same, hrv, Reg64s.get64_set64_same, setWidth_64_setWidth,
            Reg64s.get64_set64_of_ne _ .r11 rb _ hrb_ne.symm, hvb]),
          rfl, x64_frame_of_eq (fun r hr => ?_) rfl (updFlags_of_status_eq rfl _)⟩, fun _ hw32 => by
          rw [Reg64s.get64_set64_same, hrvz hw32, Reg64s.get64_set64_same, setWidth_64_setWidth,
            Reg64s.get64_set64_of_ne _ .r11 rb _ hrb_ne.symm, hvb]⟩
        simp only [List.mem_cons, not_or] at hr
        rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1),
          Reg64s.get64_set64_of_ne _ .r11 r _ (Ne.symm hr.2.2.1)]
    · simp only [hbmi, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind] at hc
      rcases Option.bind_eq_some_iff.mp hc with ⟨d1, hd1, hm⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at hm; rcases hm with ⟨rfl, rfl⟩
      simp only [emitClean_append, emitClean_ite, emitClean_cons, emitClean_nil]
      refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_argToBits s .r11 hd1 hpa)) ?_
      rintro s1 ⟨rv11, hrv11, rfl⟩
      refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_movD _ .r10 .rcx)) ?_; rintro s2 rfl
      dsimp only; rw [Reg64s.get64_set64_of_ne _ .r11 .rcx _ (by decide)]
      have hrcx_step : _root_.Program.wp (if rb == .rcx then [] else [movW w .rcx rb])
          (fun s3 => ∃ rcxVal, rcxVal.setWidth w.bits = vb ∧
            s3 = { s with
              regs := ((s.regs.set64 .r11 rv11).set64 .r10 (s.regs.get64 .rcx)).set64
                .rcx rcxVal }) E
          { s with regs := (s.regs.set64 .r11 rv11).set64 .r10 (s.regs.get64 .rcx) } := by
        by_cases hrc : rb == .rcx
        · have heq := (beq_reg64_iff rb .rcx).1 hrc; subst heq; simp only [hrc, ↓reduceIte]
          refine _root_.Program.wp_nil ⟨s.regs.get64 .rcx, hvb, ?_⟩
          congr 1
        · simp only [hrc, Bool.false_eq_true, ↓reduceIte]
          refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movW w _ .rcx rb)) ?_
          rintro s3 rfl
          have hrb_ne := ne_of_not_mem_x64Scratch (hargs rb (by simp [PArg.gprs]))
          exact ⟨_, by rw [setWidth_64_setWidth, Reg64s.get64_set64_of_ne _ .r10 rb _ hrb_ne.1.symm,
            Reg64s.get64_set64_of_ne _ .r11 rb _ hrb_ne.2.symm, hvb], rfl⟩
      simp only [List.append_eq, List.nil_append, List.append_assoc]
      refine Program.wp.append hrcx_step ?_; rintro s3 ⟨rcxVal, hrcxVal, rfl⟩
      refine Program.wp.append (wp_shiftMaskRcx w s _ (Reg64s.get64_set64_same _ _ _) hrcxVal) ?_
      rintro s4 ⟨rcxM, stM, hcl, hstM, rfl⟩
      refine Program.wp.cons
        (Directive.FallsTo.wp (fallsTo_shiftW w sk _ .r11 .cl (vb.toNat % w.bits)
          (Nat.mod_lt _ (width_bits_pos w)) hcl)) ?_
      rintro s5 ⟨rv11', st5, hrv11', hrot5, rfl⟩
      refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_movD _ .rcx .r10)) ?_; rintro s6 rfl
      refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movW w _ rd .r11)) ?_; rintro s7 rfl
      have hva11 : ((((s.regs.set64 .r11 rv11).set64 .r10 (s.regs.get64 .rcx)).set64
          .rcx rcxM).get64 .r11).setWidth w.bits = va := by
        rw [Reg64s.get64_set64_of_ne _ .rcx .r11 _ (by decide),
          Reg64s.get64_set64_of_ne _ .r10 .r11 _ (by decide),
          Reg64s.get64_set64_same, hrv11]
      have hres11 : rv11'.setWidth w.bits = sk.eval va (vb.toNat % w.bits) := by
        rw [hrv11', Reg64s.set64_set64_same, hva11]
      refine ⟨⟨(GprHolds.bits_iff w _ _).2 (by
          rw [Reg64s.get64_set64_same, setWidth_64_setWidth,
            Reg64s.get64_set64_of_ne _ .rcx .r11 _ (by decide),
            Reg64s.get64_set64_same, hres11]),
        rfl, x64_frame_of_eq (fun r hr => ?_) rfl ?_⟩, fun _ hw32 => by
        subst hw32
        rw [Reg64s.get64_set64_same, Reg64s.get64_set64_of_ne _ .rcx .r11 _ (by decide),
          Reg64s.get64_set64_same, hres11]⟩
      · simp only [List.mem_cons, not_or] at hr
        have hne10 : r ≠ .r10 := hr.2.1; have hne11 : r ≠ .r11 := hr.2.2.1
        rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1)]
        by_cases hrc : r = .rcx
        · subst hrc; simp only [Reg64s.get64_set64_same,
            Reg64s.get64_set64_of_ne _ .r11 .r10 _ (by decide),
            Reg64s.get64_set64_of_ne _ .rcx .r10 _ (by decide)]
        · simp only [Reg64s.get64_set64_of_ne _ .rcx r _ (Ne.symm hrc),
            Reg64s.get64_set64_of_ne _ .r10 r _ hne10.symm,
            Reg64s.get64_set64_of_ne _ .r11 r _ hne11.symm]
      · by_cases hw32 : w = .W8 ∨ w = .W16
        · rw [show (if w == .W8 || w == .W16 then maskAll
              else if sk.isRot then maskCF ||| maskOF else maskAll) = maskAll by
            rcases hw32 with rfl | rfl <;> rfl]
          exact updFlags_maskAll _ _
        · have hw32' : w = .W32 ∨ w = .W64 := by cases w <;> simp at hw32 ⊢
          simp only [show (w == .W8 || w == .W16) = false by rcases hw32' with rfl | rfl <;> rfl,
            Bool.false_eq_true, ↓reduceIte]
          by_cases hrot : sk.isRot = true
          · simp only [hrot, ↓reduceIte]
            obtain ⟨p1, z1, s1⟩ := hrot5 hrot; obtain ⟨p0, z0, s0⟩ := hstM hw32'
            exact updFlags_maskCF_OF (p1.trans p0) (z1.trans z0) (s1.trans s0)
          · simp only [hrot, Bool.false_eq_true, ↓reduceIte]; exact updFlags_maskAll _ _

theorem opShift_spec [Host] {E : Int64 → MachineData → Prop} (w : Width) (sk : ShiftKind)
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64}
    {c : List Instr} {clob : FlagMask} {va vb : BitVec w.bits} {s : MachineData}
    (hc : opShiftIns w sk pa pb rd = some (c, clob))
    (hrd : rd ∉ x64Scratch) (hargs : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ x64Scratch)
    (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va)
    (hpb : x64Mach.PArgHolds s (.bits w.bits) pb vb) :
    _root_.Program.wp (emitClean c)
      (OpPost1 (.bits w.bits) rd (sk.eval va (vb.toNat % w.bits)) clob s) E s :=
  Program.wp.mono (opShift_z false w sk (fun h => by cases h) hc hrd hargs hpa hpb) fun _ h => h.1

theorem opShift_zero32_spec [Host] {E : Int64 → MachineData → Prop} (sk : ShiftKind)
    {pa pb : PArg Reg64 RegMm CondCode (.bits 32)} {rd : Reg64}
    {c : List Instr} {clob : FlagMask} {va vb : BitVec 32} {s : MachineData}
    (hz : match pb with | .imm cb => cb.toNat % 32 ≠ 0 | .gpr _ => true | _ => False)
    (hc : opShiftIns .W32 sk pa pb rd = some (c, clob))
    (hrd : rd ∉ x64Scratch) (hargs : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ x64Scratch)
    (hpa : x64Mach.PArgHolds s (.bits 32) pa va)
    (hpb : x64Mach.PArgHolds s (.bits 32) pb vb) :
    _root_.Program.wp (emitClean c)
      (OpPostZ true .W32 rd (sk.eval va (vb.toNat % 32)) clob s) E s :=
  opShift_z true .W32 sk (fun _ => ⟨rfl, by cases pb <;> exact hz⟩) hc hrd hargs hpa hpb

/-! ## 4. `opFunnel_spec` (`fshl`/`fshr` via `shld`/`shrd` on `.W32`/`.W64`) -/

private theorem drop_append_shl_eq (n : Nat) (a b : BitVec n) (k : Nat) :
    (((a.append b) <<< k).drop n).setWidth n = ((a ++ b) <<< k).extractLsb' n n := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, decide_eq_true hi, Bool.true_and, BitVec.drop,
    BitVec.getLsbD_extractLsb', show i < (n + n - n) by omega, BitVec.getLsbD_shiftLeft]; rfl

private theorem take_append_shr_eq (n : Nat) (b a : BitVec n) (k : Nat) :
    (((b.append a) >>> k).take n).setWidth n = ((b ++ a) >>> k).extractLsb' 0 n := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_setWidth, Bool.true_and, BitVec.take,
    BitVec.getLsbD_extractLsb', Nat.zero_add, decide_eq_true hi, BitVec.getLsbD_ushiftRight]; rfl

private theorem extractLsb'_hi_append (n : Nat) (a b : BitVec n) :
    ((a ++ b) <<< 0).extractLsb' n n = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.shiftLeft_zero, BitVec.getLsbD_append]
  rw [decide_eq_true hi, Bool.true_and]; split <;> first | omega | simp [Nat.add_sub_cancel_left]

private theorem extractLsb'_lo_append (n : Nat) (b a : BitVec n) :
    ((b ++ a) >>> 0).extractLsb' 0 n = a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [BitVec.getLsbD_append, hi]

private theorem fallsTo_funnelW (w : Width) (hw : w = .W32 ∨ w = .W64) (isRight : Bool)
    (s : MachineData) (ce : ShiftCountExpr) (k : Nat) (hk_lt : k < w.bits)
    (hk : ∀ [Labels] (p : Std.Rco Int64), ce.interpMasked s p w = k) :
    Directive.FallsTo (insW w (if isRight then .shrd (.reg (regW w .r11)) (regW w .r10) ce
      else .shld (.reg (regW w .r11)) (regW w .r10) ce)) s (fun s' => ∃ rv status,
      (let va := (s.regs.get64 .r11).setWidth w.bits; let vb := (s.regs.get64 .r10).setWidth w.bits
       rv.setWidth w.bits = if isRight then ((vb ++ va) >>> k).extractLsb' 0 w.bits else ((va ++ vb) <<< k).extractLsb' w.bits w.bits) ∧
      s' = { s with regs := s.regs.set64 .r11 rv, status }) := by
  intro _ p _ _ _ hcont; have hkp := hk p
  simp only [ShiftCountExpr.interpMasked, ShiftCountExpr.interp] at hkp
  by_cases hk0 : k = 0
  · subst hk0
    cases ce <;> rcases hw with rfl | rfl <;> cases isRight <;>
      ((try simp only [Bool.false_eq_true, ↓reduceIte]); (try simp only [↓reduceIte])) <;>
      simp only [insW, regW, t_step_simp, Reg.interp] at hkp ⊢ <;>
      rw [hkp] <;> simp only [beq_self_eq_true, ↓reduceIte] <;>
      first
      | exact hcont _ ⟨s.regs.get64 .r11, s.status, by first | exact (extractLsb'_lo_append _ _ _).symm | exact (extractLsb'_hi_append _ _ _).symm, rfl⟩
      | (obtain ⟨rv, hrv, hs⟩ := setRegW_eq_set64 .W32 s .r11 ((s.regs.get64 .r11).setWidth 32) s.status
         refine hcont _ ⟨rv, s.status, ?_, hs⟩; rw [hrv]; first | exact (extractLsb'_lo_append _ _ _).symm | exact (extractLsb'_hi_append _ _ _).symm)
  · have hk0' : (k == 0) = false := beq_false_of_ne hk0
    have hle : ¬ (w.bits < k) := Nat.not_lt.2 (Nat.le_of_lt hk_lt)
    have hle32 : w = .W32 → ¬ (Width.W32.bits < k) := fun h => by rw [h] at hle; exact hle
    have hle64 : w = .W64 → ¬ (Width.W64.bits < k) := fun h => by rw [h] at hle; exact hle
    cases ce <;> rcases hw with rfl | rfl <;> cases isRight <;>
      ((try simp only [Bool.false_eq_true, ↓reduceIte]); (try simp only [↓reduceIte])) <;>
      simp only [insW, regW, t_step_simp, Reg.interp, Effects.All] at hkp ⊢ <;>
      rw [hkp] <;> simp only [hk0', Bool.false_eq_true, ↓reduceIte] <;>
      (try simp only [hle32 rfl, ↓reduceIte]) <;> (try simp only [hle64 rfl, ↓reduceIte]) <;>
      { intro _
        by_cases hk1 : k = 1
        · subst hk1; simp only [beq_self_eq_true, ↓reduceIte]
          obtain ⟨rv, hrv, hs⟩ := setRegW_eq_set64 _ s .r11 _ _
          exact hcont _ ⟨rv, _, hrv.trans (by first | exact drop_append_shl_eq _ _ _ _ | exact take_append_shr_eq _ _ _ _), hs⟩
        · simp only [beq_false_of_ne hk1, Bool.false_eq_true, ↓reduceIte]; intro _
          obtain ⟨rv, hrv, hs⟩ := setRegW_eq_set64 _ s .r11 _ _
          exact hcont _ ⟨rv, _, hrv.trans (by first | exact drop_append_shl_eq _ _ _ _ | exact take_append_shr_eq _ _ _ _), hs⟩ }

private theorem wp_xorSwap64 [Host] {E : Int64 → MachineData → Prop} (s : MachineData)
    (a b : Reg64) (hne : a ≠ b) {rest : List Directive} {Q : MachineData → Prop}
    (hk : ∀ st', _root_.Program.wp rest Q E
      { s with regs := (s.regs.set64 a (s.regs.get64 b)).set64 b (s.regs.get64 a), status := st' }) :
    _root_.Program.wp (ins (.xor (.reg (q a)) (.reg (q b))) ::
        ins (.xor (.reg (q b)) (.reg (q a))) :: ins (.xor (.reg (q a)) (.reg (q b))) :: rest) Q E s := by
  have xor1 : ∀ (st : MachineData) (x y : Reg64), Directive.FallsTo (ins (.xor (.reg (q x)) (.reg (q y)))) st fun st' =>
      ∃ s1, st' = { st with regs := st.regs.set64 x (st.regs.get64 x ^^^ st.regs.get64 y), status := s1 } := by
    intro st x y _ _ _ _ _ hkt; simp only [q, t_step_simp, Effects.All, Reg64s.set]; intro _; exact hkt _ ⟨_, rfl⟩
  refine Program.wp.cons (Directive.FallsTo.wp (xor1 s a b)) ?_; rintro s1 ⟨st1, rfl⟩
  refine Program.wp.cons (Directive.FallsTo.wp (xor1 _ b a)) ?_; rintro s2 ⟨st2, rfl⟩
  refine Program.wp.cons (Directive.FallsTo.wp (xor1 _ a b)) ?_; rintro s3 ⟨st3, rfl⟩; dsimp only
  refine Eq.mp (congrArg (fun rg => _root_.Program.wp rest Q E { s with regs := rg, status := st3 })
    (reg64s_ext (r2 := (s.regs.set64 a (s.regs.get64 b)).set64 b (s.regs.get64 a)) fun r => ?_)).symm (hk st3)
  simp only [Reg64s.get64_set64_same, Reg64s.get64_set64_of_ne _ a b _ hne, Reg64s.get64_set64_of_ne _ b a _ hne.symm]
  by_cases ha : r = a
  · rw [ha]; simp only [Reg64s.get64_set64_same, Reg64s.get64_set64_of_ne _ b a _ hne.symm]
    apply BitVec.eq_of_getLsbD_eq; intro i _; simp only [BitVec.getLsbD_xor]
    cases (s.regs.get64 a).getLsbD i <;> cases (s.regs.get64 b).getLsbD i <;> rfl
  · by_cases hb : r = b
    · rw [hb]; simp only [Reg64s.get64_set64_same, Reg64s.get64_set64_of_ne _ a b _ hne]
      apply BitVec.eq_of_getLsbD_eq; intro i _; simp only [BitVec.getLsbD_xor]
      cases (s.regs.get64 a).getLsbD i <;> cases (s.regs.get64 b).getLsbD i <;> rfl
    · simp only [Reg64s.get64_set64_of_ne _ a r _ (Ne.symm ha), Reg64s.get64_set64_of_ne _ b r _ (Ne.symm hb)]

theorem wp_argPair11_10 [Host] {E : Int64 → MachineData → Prop} (w : Width) (s : MachineData)
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {va vb : BitVec w.bits} {d1 d2 : Instr}
    (hd1 : argToBitsI w .r11 pa = some d1) (hd2 : argToBitsI w .r10 pb = some d2)
    (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va) (hpb : x64Mach.PArgHolds s (.bits w.bits) pb vb)
    (hpb_sc : ∀ r ∈ pb.gprs, r ∉ x64Scratch) {rest : List Directive} {Q : MachineData → Prop}
    (hk : ∀ rv11 rv10, rv11.setWidth w.bits = va → rv10.setWidth w.bits = vb →
      _root_.Program.wp rest Q E { s with regs := (s.regs.set64 .r11 rv11).set64 .r10 rv10 }) :
    _root_.Program.wp (.instr d1 :: .instr d2 :: rest) Q E s := by
  refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_argToBits s .r11 hd1 hpa)) ?_; rintro s1 ⟨rv11, hrv11, rfl⟩
  have hpb1 : x64Mach.PArgHolds { s with regs := s.regs.set64 .r11 rv11 } (.bits w.bits) pb vb := by
    cases pb with | vec _ => simp [argToBitsI] at hd2 | imm _ => exact hpb | gpr rx =>
      have hx := (ne_of_not_mem_x64Scratch (hpb_sc rx (by simp [PArg.gprs]))).2
      dsimp only [Machine.PArgHolds, GprHolds, Machine.getGpr] at hpb ⊢; rw [Reg64s.get64_set64_of_ne _ .r11 rx _ hx.symm]; exact hpb
  refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_argToBits _ .r10 hd2 hpb1)) ?_; rintro s2 ⟨rv10, hrv10, rfl⟩; exact hk rv11 rv10 hrv11 hrv10

private theorem opFunnel_z [Host] {E : Int64 → MachineData → Prop} (z32 : Bool)
    (w : Width) (hw : w = .W32 ∨ w = .W64)
    (isRight : Bool) {pa pb pc : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64}
    {c : List Instr} {clob : FlagMask} {va vb vc : BitVec w.bits} {s : MachineData}
    (hz : z32 = true → w = .W32 ∧
      match pc with
      | .gpr _ => True
      | .imm cb => cb.toNat % 32 ≠ 0 ∨ (if isRight then pb else pa) ≠ .gpr rd
      | .vec _ => False)
    (hc : opFunnelIns w isRight pa pb pc rd = some (c, clob)) (hrd : rd ∉ x64Scratch)
    (hargs : ∀ r ∈ pa.gprs ++ pb.gprs ++ pc.gprs, r ∉ x64Scratch)
    (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va)
    (hpb : x64Mach.PArgHolds s (.bits w.bits) pb vb)
    (hpc : x64Mach.PArgHolds s (.bits w.bits) pc vc) :
    _root_.Program.wp (emitClean c) (OpPostZ z32 w rd
      (if isRight then ((va ++ vb) >>> (vc.toNat % w.bits)).extractLsb' 0 w.bits
       else ((va ++ vb) <<< (vc.toNat % w.bits)).extractLsb' w.bits w.bits) clob s) E s := by
  have hd_h : x64Mach.PArgHolds s (.bits w.bits) (if isRight then pb else pa) (if isRight then vb else va) := by cases isRight <;> assumption
  have hs_h : x64Mach.PArgHolds s (.bits w.bits) (if isRight then pa else pb) (if isRight then va else vb) := by cases isRight <;> assumption
  have hs_sc : ∀ r ∈ (if isRight then pa else pb).gprs, r ∉ x64Scratch := fun r hr => by cases isRight <;> simp_all
  have tail_wp : ∀ {rest : List Directive} {ce : ShiftCountExpr} {restoreRcx : Bool} {s2 : MachineData}
      {rv11 rv10 : BitVec 64} (hrv11 : rv11.setWidth w.bits = if isRight then vb else va)
      (hrv10 : rv10.setWidth w.bits = if isRight then va else vb) (h11 : s2.regs.get64 .r11 = rv11) (h10 : s2.regs.get64 .r10 = rv10)
      (hm : s2.dmem = s.dmem) (hz : s2.zmms = s.zmms) (hce : ∀ [Labels] (p : Std.Rco Int64), ce.interpMasked s2 p w = vc.toNat % w.bits)
      (hrest : rest = (if restoreRcx then [movD .rcx rd] else []) ++ [movW w rd .r11])
      (hr_save : ∀ r, r ≠ rd → r ∉ x64Scratch → (if r = .rcx ∧ restoreRcx then s2.regs.get64 rd else s2.regs.get64 r) = s.regs.get64 r),
      _root_.Program.wp (insW w (if isRight then .shrd (.reg (regW w .r11)) (regW w .r10) ce else .shld (.reg (regW w .r11)) (regW w .r10) ce) :: rest)
        (OpPostZ z32 w rd (if isRight then ((va ++ vb) >>> (vc.toNat % w.bits)).extractLsb' 0 w.bits
          else ((va ++ vb) <<< (vc.toNat % w.bits)).extractLsb' w.bits w.bits) maskAll s) E s2 := by
    intro rest ce restoreRcx s2 rv11 rv10 hrv11 hrv10 h11 h10 hm hz hce hrest hsav
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_funnelW w hw isRight s2 ce (vc.toNat % w.bits)
      (Nat.mod_lt _ (width_bits_pos w)) hce)) ?_; rintro s3 ⟨rv11', st3, hrv11', rfl⟩; subst hrest
    have hres11 : rv11'.setWidth w.bits = if isRight then ((va ++ vb) >>> (vc.toNat % w.bits)).extractLsb' 0 w.bits
        else ((va ++ vb) <<< (vc.toNat % w.bits)).extractLsb' w.bits w.bits := by rw [hrv11', h11, h10, hrv11, hrv10]; cases isRight <;> rfl
    have hmv : _root_.Program.wp (if restoreRcx then [movD .rcx rd] else []) (fun s4 =>
        (s4.regs.get64 .r11).setWidth w.bits = (if isRight then ((va ++ vb) >>> (vc.toNat % w.bits)).extractLsb' 0 w.bits
          else ((va ++ vb) <<< (vc.toNat % w.bits)).extractLsb' w.bits w.bits) ∧
        (∀ r, r ≠ rd → r ∉ x64Scratch → s4.regs.get64 r = s.regs.get64 r) ∧ s4.dmem = s.dmem ∧ s4.zmms = s.zmms)
        E { s2 with regs := s2.regs.set64 .r11 rv11', status := st3 } := by
      cases restoreRcx
      · simp only [Bool.false_eq_true, ↓reduceIte]
        refine _root_.Program.wp_nil ⟨by rw [Reg64s.get64_set64_same, hres11], fun r hr hsc => ?_, hm, hz⟩
        rw [Reg64s.get64_set64_of_ne _ .r11 r _ (ne_of_not_mem_x64Scratch hsc).2.symm]; simpa using hsav r hr hsc
      · simp only [↓reduceIte]
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movD _ .rcx rd)) ?_; rintro s4 rfl
        refine ⟨by rw [Reg64s.get64_set64_of_ne _ .rcx .r11 _ (by decide), Reg64s.get64_set64_same, hres11], fun r hr hsc => ?_, hm, hz⟩
        have hne := ne_of_not_mem_x64Scratch hsc
        by_cases hrc : r = .rcx
        · subst hrc; rw [Reg64s.get64_set64_same, Reg64s.get64_set64_of_ne _ .r11 rd _ (ne_of_not_mem_x64Scratch hrd).2.symm]; simpa using hsav .rcx hr hsc
        · rw [Reg64s.get64_set64_of_ne _ .rcx r _ (Ne.symm hrc), Reg64s.get64_set64_of_ne _ .r11 r _ hne.2.symm]; simpa [hrc] using hsav r hr hsc
    refine Program.wp.append hmv ?_; rintro s4 ⟨h11_4, hsav4, hm4, hz4⟩
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movW w _ rd .r11)) ?_; rintro s5 rfl
    refine ⟨⟨(GprHolds.bits_iff w _ _).2
      (by rw [Reg64s.get64_set64_same, setWidth_64_setWidth, h11_4]), hm4,
      x64_frame_of_eq (fun r hr => ?_) hz4 (updFlags_maskAll _ _)⟩, fun _ hw32 => by
      subst hw32; rw [Reg64s.get64_set64_same, h11_4]⟩
    simp only [List.mem_cons, not_or] at hr; rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1)]
    exact hsav4 r hr.1 (by simp only [x64Scratch, List.mem_cons, List.mem_nil_iff, or_false]; exact fun h => h.elim hr.2.1 hr.2.2.1)
  cases pc with
  | vec _ => simp [opFunnelIns] at hc
  | imm cb =>
    rcases hpc with rfl; simp only [opFunnelIns] at hc
    by_cases hcnt : cb.toNat % w.bits == 0
    · simp only [hcnt, ↓reduceIte] at hc
      have hres : (if isRight then ((va ++ vb) >>> (cb.toNat % w.bits)).extractLsb' 0 w.bits
          else ((va ++ vb) <<< (cb.toNat % w.bits)).extractLsb' w.bits w.bits) = if isRight then vb else va := by
        rw [beq_iff_eq.1 hcnt]; rcases hw with rfl | rfl <;> cases isRight <;> first | exact extractLsb'_hi_append _ va vb | exact extractLsb'_lo_append _ va vb
      rw [hres]
      cases z32
      · cases isRight <;>
          exact Program.wp.mono (opCopyBits_spec w hc (by assumption))
            fun _ h => ⟨h, fun h0 => by cases h0⟩
      · obtain ⟨rfl, hne⟩ := hz rfl
        have hne' : (if isRight then pb else pa) ≠ .gpr rd :=
          hne.resolve_left (fun h => h (beq_iff_eq.1 hcnt))
        cases isRight <;> exact opCopyBits_zero32_spec hne' hc (by assumption)
    · simp only [hcnt, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind] at hc
      rcases Option.bind_eq_some_iff.mp hc with ⟨dDst, hd1, h1⟩; rcases Option.bind_eq_some_iff.mp h1 with ⟨dSrc, hd2, h2⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at h2; rcases h2 with ⟨rfl, rfl⟩
      simp only [emitClean_cons, emitClean_nil]
      refine wp_argPair11_10 w s hd1 hd2 hd_h hs_h hs_sc fun rv11 rv10 hrv11 hrv10 => ?_
      refine tail_wp (restoreRcx := false) hrv11 hrv10 (by rw [Reg64s.get64_set64_of_ne _ .r10 .r11 _ (by decide), Reg64s.get64_set64_same])
        (by rw [Reg64s.get64_set64_same]) rfl rfl (fun p => shiftMask_imm_eq w cb p s) rfl ?_
      intro r _ hsc; have hne := ne_of_not_mem_x64Scratch hsc
      simp [Reg64s.get64_set64_of_ne _ .r10 r _ hne.1.symm, Reg64s.get64_set64_of_ne _ .r11 r _ hne.2.symm]
  | gpr rc =>
    simp only [opFunnelIns, Option.bind_eq_bind] at hc
    rcases Option.bind_eq_some_iff.mp hc with ⟨dDst, hd1, h1⟩; rcases Option.bind_eq_some_iff.mp h1 with ⟨dSrc, hd2, h2⟩
    have hc_reg := (GprHolds.bits_iff w _ _).1 hpc
    have hrc_mod' : ∀ (s0 : MachineData), s0.regs.get64 .rcx = s.regs.get64 rc →
        ∀ [Labels] (p : Std.Rco Int64), ShiftCountExpr.cl.interpMasked s0 p w = vc.toNat % w.bits := by
      intro s0 hget _ p; have hrcx0 : s0.regs.rcx.toBitVec = s.regs.get64 rc := hget
      have hvc := congrArg BitVec.toNat hc_reg; simp only [BitVec.toNat_setWidth] at hvc
      have h5 : (31 : Nat) = 2 ^ 5 - 1 := rfl; have h6 : (63 : Nat) = 2 ^ 6 - 1 := rfl
      rcases hw with rfl | rfl <;>
        simp only [ShiftCountExpr.interpMasked, ShiftCountExpr.interp, hrcx0, BitVec.take,
          BitVec.extractLsb'_toNat, Nat.shiftRight_zero, Width.bits, h5, h6, Nat.and_two_pow_sub_one_eq_mod] at hvc ⊢
      · rw [Nat.mod_mod_of_dvd _ (by decide : 32 ∣ 2 ^ 8), ← Nat.mod_mod_of_dvd _ (by decide : 32 ∣ 2 ^ 32), hvc]
      · rw [Nat.mod_mod_of_dvd _ (by decide : 64 ∣ 2 ^ 8), ← Nat.mod_mod_of_dvd _ (by decide : 64 ∣ 2 ^ 64), hvc]
    have hrc_sc := ne_of_not_mem_x64Scratch (hargs rc (by simp [PArg.gprs])); have hrd_sc := ne_of_not_mem_x64Scratch hrd
    by_cases hrcx : rd == .rcx
    · have hrd_c : rd = .rcx := (beq_reg64_iff rd .rcx).1 hrcx; subst hrd_c
      simp only [hrcx, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h2; rcases h2 with ⟨rfl, rfl⟩
      simp only [List.cons_append, emitClean_cons]
      refine wp_argPair11_10 w s hd1 hd2 hd_h hs_h hs_sc fun rv11 rv10 hrv11 hrv10 => ?_
      have hbody : ∀ {mv : List Instr},
          _root_.Program.wp (emitClean mv) (fun s3 => s3.regs.get64 .rcx = s.regs.get64 rc ∧
            s3 = { s with regs := ((s.regs.set64 .r11 rv11).set64 .r10 rv10).set64 .rcx (s.regs.get64 rc) }) E
            { s with regs := (s.regs.set64 .r11 rv11).set64 .r10 rv10 } →
          _root_.Program.wp
            (emitClean (mv ++ [x64InsI w (if isRight then .shrd (.reg (regW w .r11))
              (regW w .r10) .cl else .shld (.reg (regW w .r11)) (regW w .r10) .cl),
              movWI w .rcx .r11]))
            (OpPostZ z32 w .rcx
              (if isRight then ((va ++ vb) >>> (vc.toNat % w.bits)).extractLsb' 0 w.bits
              else ((va ++ vb) <<< (vc.toNat % w.bits)).extractLsb' w.bits w.bits) maskAll s) E { s with regs := (s.regs.set64 .r11 rv11).set64 .r10 rv10 } := by
        intro mv hmv; simp only [emitClean_append, emitClean_cons, emitClean_nil]
        refine Program.wp.append hmv ?_; rintro s3 ⟨_, rfl⟩
        refine tail_wp (restoreRcx := false) hrv11 hrv10
          (by rw [Reg64s.get64_set64_of_ne _ .rcx .r11 _ (by decide), Reg64s.get64_set64_of_ne _ .r10 .r11 _ (by decide), Reg64s.get64_set64_same])
          (by rw [Reg64s.get64_set64_of_ne _ .rcx .r10 _ (by decide), Reg64s.get64_set64_same]) rfl rfl (fun p => hrc_mod' _ (by rw [Reg64s.get64_set64_same]) p) rfl ?_
        intro r hr hsc; have hne := ne_of_not_mem_x64Scratch hsc
        simp [Reg64s.get64_set64_of_ne _ .rcx r _ hr.symm, Reg64s.get64_set64_of_ne _ .r10 r _ hne.1.symm, Reg64s.get64_set64_of_ne _ .r11 r _ hne.2.symm]
      change _root_.Program.wp (emitClean (_ ++ _)) _ E _; refine hbody ?_
      by_cases hrc : rc == .rcx
      · have hrc_eq := (beq_reg64_iff rc .rcx).1 hrc; subst hrc_eq
        simp only [hrc, ↓reduceIte]
        exact _root_.Program.wp_nil ⟨by rw [Reg64s.get64_set64_of_ne _ .r10 .rcx _ (by decide), Reg64s.get64_set64_of_ne _ .r11 .rcx _ (by decide)], by congr 1⟩
      · simp only [hrc, Bool.false_eq_true, ↓reduceIte]
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movD _ .rcx rc)) ?_; rintro s3 rfl
        exact ⟨by rw [Reg64s.get64_set64_same, Reg64s.get64_set64_of_ne _ .r10 rc _ hrc_sc.1.symm, Reg64s.get64_set64_of_ne _ .r11 rc _ hrc_sc.2.symm],
          by rw [Reg64s.get64_set64_of_ne _ .r10 rc _ hrc_sc.1.symm, Reg64s.get64_set64_of_ne _ .r11 rc _ hrc_sc.2.symm]⟩
    · have hrd_ne_c : rd ≠ .rcx := fun h => hrcx ((beq_reg64_iff rd .rcx).2 h)
      by_cases hrcd : rc == rd
      · have hrc_eq : rc = rd := (beq_reg64_iff rc rd).1 hrcd; subst hrc_eq
        simp only [hrcx, Bool.false_eq_true, ↓reduceIte, hrcd, Option.some.injEq, Prod.mk.injEq] at h2; rcases h2 with ⟨rfl, rfl⟩
        simp only [emitClean_cons, emitClean_nil]
        refine wp_argPair11_10 w s hd1 hd2 hd_h hs_h hs_sc fun rv11 rv10 hrv11 hrv10 => ?_
        refine wp_xorSwap64 _ .rcx rc hrd_ne_c.symm fun st3 => ?_
        refine tail_wp (restoreRcx := true) hrv11 hrv10
          (by rw [Reg64s.get64_set64_of_ne _ rc .r11 _ hrd_sc.2, Reg64s.get64_set64_of_ne _ .rcx .r11 _ (by decide),
            Reg64s.get64_set64_of_ne _ .r10 .r11 _ (by decide), Reg64s.get64_set64_same])
          (by rw [Reg64s.get64_set64_of_ne _ rc .r10 _ hrd_sc.1, Reg64s.get64_set64_of_ne _ .rcx .r10 _ (by decide), Reg64s.get64_set64_same])
          rfl rfl (fun p => hrc_mod' _ (by rw [Reg64s.get64_set64_of_ne _ rc .rcx _ hrd_ne_c, Reg64s.get64_set64_same,
            Reg64s.get64_set64_of_ne _ .r10 rc _ hrd_sc.1.symm, Reg64s.get64_set64_of_ne _ .r11 rc _ hrd_sc.2.symm]) p) rfl ?_
        intro r hr hsc; have hne := ne_of_not_mem_x64Scratch hsc
        by_cases hrc : r = .rcx
        · subst hrc; simp [Reg64s.get64_set64_same, Reg64s.get64_set64_of_ne _ .r10 .rcx _ (by decide), Reg64s.get64_set64_of_ne _ .r11 .rcx _ (by decide)]
        · simp [hrc, Reg64s.get64_set64_of_ne _ rc r _ hr.symm, Reg64s.get64_set64_of_ne _ .rcx r _ (Ne.symm hrc),
            Reg64s.get64_set64_of_ne _ .r10 r _ hne.1.symm, Reg64s.get64_set64_of_ne _ .r11 r _ hne.2.symm]
      · simp only [hrcx, hrcd, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h2; rcases h2 with ⟨rfl, rfl⟩
        simp only [List.cons_append, emitClean_cons]
        have hrc_ne_rd : rc ≠ rd := fun h => hrcd ((beq_reg64_iff rc rd).2 h)
        refine wp_argPair11_10 w s hd1 hd2 hd_h hs_h hs_sc fun rv11 rv10 hrv11 hrv10 => ?_
        refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_movD _ rd .rcx)) ?_; rintro s3 rfl
        have hbody : ∀ {mv : List Instr},
            _root_.Program.wp (emitClean mv)
              (· = { s with regs := ((((s.regs.set64 .r11 rv11).set64 .r10 rv10).set64
                rd (s.regs.get64 .rcx)).set64 .rcx (s.regs.get64 rc)) }) E
              { s with regs := ((s.regs.set64 .r11 rv11).set64 .r10 rv10).set64 rd (s.regs.get64 .rcx) } →
            _root_.Program.wp
              (emitClean (mv ++ [x64InsI w (if isRight then .shrd (.reg (regW w .r11))
                (regW w .r10) .cl else .shld (.reg (regW w .r11)) (regW w .r10) .cl),
                movI .rcx rd, movWI w rd .r11]))
              (OpPostZ z32 w rd
                (if isRight then ((va ++ vb) >>> (vc.toNat % w.bits)).extractLsb' 0 w.bits
                else ((va ++ vb) <<< (vc.toNat % w.bits)).extractLsb' w.bits w.bits) maskAll s) E
              { s with regs := ((s.regs.set64 .r11 rv11).set64 .r10 rv10).set64 rd (s.regs.get64 .rcx) } := by
          intro mv hmv; simp only [emitClean_append, emitClean_cons, emitClean_nil]
          refine Program.wp.append hmv ?_; rintro s4 rfl
          refine tail_wp (restoreRcx := true) hrv11 hrv10
            (by rw [Reg64s.get64_set64_of_ne _ .rcx .r11 _ (by decide), Reg64s.get64_set64_of_ne _ rd .r11 _ hrd_sc.2,
              Reg64s.get64_set64_of_ne _ .r10 .r11 _ (by decide), Reg64s.get64_set64_same])
            (by rw [Reg64s.get64_set64_of_ne _ .rcx .r10 _ (by decide), Reg64s.get64_set64_of_ne _ rd .r10 _ hrd_sc.1, Reg64s.get64_set64_same])
            rfl rfl (fun p => hrc_mod' _ (by rw [Reg64s.get64_set64_same]) p) rfl ?_
          intro r hr hsc; have hne := ne_of_not_mem_x64Scratch hsc
          by_cases hrc0 : r = .rcx
          · subst hrc0; simp [Reg64s.get64_set64_of_ne _ .rcx rd _ hr, Reg64s.get64_set64_same]
          · simp [hrc0, Reg64s.get64_set64_of_ne _ .rcx r _ (Ne.symm hrc0), Reg64s.get64_set64_of_ne _ rd r _ hr.symm,
              Reg64s.get64_set64_of_ne _ .r10 r _ hne.1.symm, Reg64s.get64_set64_of_ne _ .r11 r _ hne.2.symm]
        dsimp only; change _root_.Program.wp (emitClean (_ ++ _)) _ E _; refine hbody ?_
        have hgc : ((s.regs.set64 .r11 rv11).set64 .r10 rv10).get64 .rcx = s.regs.get64 .rcx := by
          rw [Reg64s.get64_set64_of_ne _ .r10 .rcx _ (by decide), Reg64s.get64_set64_of_ne _ .r11 .rcx _ (by decide)]
        by_cases hrc : rc == .rcx
        · have hrc_eq := (beq_reg64_iff rc .rcx).1 hrc; subst hrc_eq
          simp only [hrc, ↓reduceIte]
          refine _root_.Program.wp_nil ?_; congr 1; refine reg64s_ext fun r => ?_; by_cases hr : r = .rcx
          · subst hr; rw [Reg64s.get64_set64_same, Reg64s.get64_set64_of_ne _ rd .rcx _ hrd_ne_c, hgc]
          · rw [Reg64s.get64_set64_of_ne _ .rcx r _ (Ne.symm hr)]
        · simp only [hrc, Bool.false_eq_true, ↓reduceIte]
          refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movD _ .rcx rc)) ?_; rintro s4 rfl
          rw [Reg64s.get64_set64_of_ne _ rd rc _ (Ne.symm hrc_ne_rd), Reg64s.get64_set64_of_ne _ .r10 rc _ hrc_sc.1.symm,
            Reg64s.get64_set64_of_ne _ .r11 rc _ hrc_sc.2.symm]

theorem opFunnel_spec [Host] {E : Int64 → MachineData → Prop} (w : Width) (hw : w = .W32 ∨ w = .W64)
    (isRight : Bool) {pa pb pc : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64}
    {c : List Instr} {clob : FlagMask} {va vb vc : BitVec w.bits} {s : MachineData}
    (hc : opFunnelIns w isRight pa pb pc rd = some (c, clob)) (hrd : rd ∉ x64Scratch)
    (hargs : ∀ r ∈ pa.gprs ++ pb.gprs ++ pc.gprs, r ∉ x64Scratch)
    (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va)
    (hpb : x64Mach.PArgHolds s (.bits w.bits) pb vb)
    (hpc : x64Mach.PArgHolds s (.bits w.bits) pc vc) :
    _root_.Program.wp (emitClean c) (OpPost1 (.bits w.bits) rd
      (if isRight then ((va ++ vb) >>> (vc.toNat % w.bits)).extractLsb' 0 w.bits
       else ((va ++ vb) <<< (vc.toNat % w.bits)).extractLsb' w.bits w.bits) clob s) E s :=
  Program.wp.mono (opFunnel_z false w hw isRight (fun h => by cases h) hc hrd hargs hpa hpb hpc)
    fun _ h => h.1

theorem opFunnel_zero32_spec [Host] {E : Int64 → MachineData → Prop} (isRight : Bool)
    {pa pb pc : PArg Reg64 RegMm CondCode (.bits 32)} {rd : Reg64}
    {c : List Instr} {clob : FlagMask} {va vb vc : BitVec 32} {s : MachineData}
    (hz : match pc with
      | .gpr _ => True
      | .imm cb => cb.toNat % 32 ≠ 0 ∨ (if isRight then pb else pa) ≠ .gpr rd
      | .vec _ => False)
    (hc : opFunnelIns .W32 isRight pa pb pc rd = some (c, clob)) (hrd : rd ∉ x64Scratch)
    (hargs : ∀ r ∈ pa.gprs ++ pb.gprs ++ pc.gprs, r ∉ x64Scratch)
    (hpa : x64Mach.PArgHolds s (.bits 32) pa va) (hpb : x64Mach.PArgHolds s (.bits 32) pb vb)
    (hpc : x64Mach.PArgHolds s (.bits 32) pc vc) :
    _root_.Program.wp (emitClean c) (OpPostZ true .W32 rd
      (if isRight then ((va ++ vb) >>> (vc.toNat % 32)).extractLsb' 0 32
       else ((va ++ vb) <<< (vc.toNat % 32)).extractLsb' 32 32) clob s) E s :=
  opFunnel_z true .W32 (.inl rfl) isRight (fun _ => ⟨rfl, by cases pc <;> exact hz⟩)
    hc hrd hargs hpa hpb hpc

/-! ## 5. `x64Gpr_op_noLab` -/

theorem x64Gpr_op_noLab {sig rs : List Ty} {code : OpCode sig rs}
    {pas : Tup (PArg Reg64 RegMm CondCode) sig} {dsts : Tup (PDst Reg64 RegMm CondCode) rs}
    {vh : VariantHint} {c : List Directive} {clob : FlagMask}
    (h : x64Gpr.op code pas dsts vh = some (c, clob)) : ∀ l, Kraken.Directive.label l ∉ c :=
  emitCleanPair_noLab h

end LeanQbe.T.Amd64