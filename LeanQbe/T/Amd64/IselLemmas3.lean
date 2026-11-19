module

public import LeanQbe.T.Amd64.IselLemmas2

/-!
# x64 Scalar `GprTarget` Proofs — Part 3 (`T8`)

Completes `opCmp`, `opSelect`, `opShift`, and `opFunnel` correctness, plus
`AllInstr` for `select`, `shift`, and `funnel` (`opDiv`/`opAddc`/`opSubb`/`opMulw`,
`x64Gpr_op_noLab`, `supportsScalarOp` 1-for-1, and `x64GprSpec` continue in `IselLemmas4`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Amd64

open LeanQbe.T

/-! ## 1. `opCmp_spec` (`cmp` with `.gpr` and `.flag` destinations) -/

private theorem wp_cmpDirect [Host] {E : Int64 → MachineData → Prop} (w : Width)
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {c : List Directive}
    {va vb : BitVec w.bits} {s : MachineData}
    (hc : cmpDirect w pa pb = some c)
    (hargs : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ x64Scratch)
    (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va)
    (hpb : x64Mach.PArgHolds s (.bits w.bits) pb vb) :
    _root_.Program.wp c (fun s' =>
      (∀ r, r ∉ x64Scratch → s'.regs.get64 r = s.regs.get64 r) ∧
      s'.dmem = s.dmem ∧ s'.zmms = s.zmms ∧ s'.status = subFlags va vb) E s := by
  cases pa <;> cases pb <;> simp only [cmpDirect] at hc <;> try contradiction
  · rename_i rx ry; simp only [Option.some.injEq] at hc; subst hc
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_cmp_reg w s rx ry)) ?_
    rintro s' rfl; exact ⟨fun _ _ => rfl, rfl, rfl, by rw [hpa.2, hpb.2]⟩
  · rename_i rx cy; rcases hpb with rfl; split at hc
    · simp only [Option.some.injEq] at hc; subst hc
      refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_cmp_imm w s rx cy)) ?_
      rintro s' rfl; exact ⟨fun _ _ => rfl, rfl, rfl, by rw [hpa.2]⟩
    · simp only [Option.some.injEq] at hc; subst hc
      have hrx := (ne_of_not_mem_x64Scratch (hargs rx (by simp [PArg.gprs]))).1
      refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s .r10 (cy.setWidth 64))) ?_
      rintro s1 rfl
      refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_cmp_reg w _ rx .r10)) ?_
      rintro s2 rfl
      refine ⟨fun r hr => Reg64s.get64_set64_of_ne _ .r10 r _ (ne_of_not_mem_x64Scratch hr).1.symm, rfl, rfl, ?_⟩
      rw [Reg64s.get64_set64_of_ne _ .r10 rx _ hrx.symm, hpa.2, Reg64s.get64_set64_same, setWidth_64_setWidth]
  · rename_i cx ry; rcases hpa with rfl; simp only [Option.some.injEq] at hc; subst hc
    have hry := (ne_of_not_mem_x64Scratch (hargs ry (by simp [PArg.gprs]))).1
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s .r10 (cx.setWidth 64))) ?_
    rintro s1 rfl
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_cmp_reg w _ .r10 ry)) ?_
    rintro s2 rfl
    refine ⟨fun r hr => Reg64s.get64_set64_of_ne _ .r10 r _ (ne_of_not_mem_x64Scratch hr).1.symm, rfl, rfl, ?_⟩
    rw [Reg64s.get64_set64_of_ne _ .r10 ry _ hry.symm, hpb.2, Reg64s.get64_set64_same, setWidth_64_setWidth]
  · rename_i cx cy; rcases hpa with rfl; rcases hpb with rfl; simp only [Option.some.injEq] at hc; subst hc
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s .r11 (cx.setWidth 64))) ?_
    rintro s1 rfl
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD _ .r10 (cy.setWidth 64))) ?_
    rintro s2 rfl
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_cmp_reg w _ .r11 .r10)) ?_
    rintro s3 rfl
    refine ⟨fun r hr => ?_, rfl, rfl, ?_⟩
    · have hne := ne_of_not_mem_x64Scratch hr
      rw [Reg64s.get64_set64_of_ne _ .r10 r _ hne.1.symm, Reg64s.get64_set64_of_ne _ .r11 r _ hne.2.symm]
    · rw [Reg64s.get64_set64_of_ne _ .r10 .r11 _ (by decide), Reg64s.get64_set64_same,
        Reg64s.get64_set64_same, setWidth_64_setWidth, setWidth_64_setWidth]

theorem opCmp_spec [Host] {E : Int64 → MachineData → Prop} (w : Width) (co : CmpOp)
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {pd : PDst Reg64 RegMm CondCode .bool}
    {c : List Directive} {clob : FlagMask} {va vb : BitVec w.bits} {s : MachineData}
    (hc : opCmp w co pa pb pd = some (c, clob))
    (hargs : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ x64Scratch)
    (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va)
    (hpb : x64Mach.PArgHolds s (.bits w.bits) pb vb) :
    _root_.Program.wp c (OpPostDst1 .bool pd (co.evalBits va vb) clob s) E s := by
  have hwn : w.bits = 8 ∨ w.bits = 16 ∨ w.bits = 32 ∨ w.bits = 64 := by
    cases w <;> simp [Width.bits]
  cases pd with
  | vec _ => simp [opCmp] at hc
  | gpr rd =>
    have useSetcc (pre : List Directive) (x y : BitVec w.bits) (cond : CondCode)
        (hcond : cond.interp (subFlags x y) = co.evalBits va vb)
        (hc_eq : c = pre ++ setccMove rd cond) (hcl_eq : clob = maskAll)
        (hpre : _root_.Program.wp pre (fun s1 =>
          (∀ r, r ∉ x64Scratch → s1.regs.get64 r = s.regs.get64 r) ∧
          s1.dmem = s.dmem ∧ s1.zmms = s.zmms ∧ s1.status = subFlags x y) E s) :
        _root_.Program.wp c (OpPostDst1 .bool (.gpr rd) (co.evalBits va vb) clob s) E s := by
      subst hc_eq; subst hcl_eq
      refine Program.wp.append hpre ?_
      rintro s1 ⟨hr1, hm1, hz1, hst1⟩
      refine Program.wp.mono (wp_setccMove s1 rd cond) ?_
      rintro s2 rfl
      refine ⟨?_, hm1, x64_frame_of_eq ?_ hz1 (updFlags_maskAll _ _)⟩
      · dsimp only [Machine.PDstHolds, GprHolds]
        rw [Reg64s.get64_set64_same, hst1, hcond]; cases co.evalBits va vb <;> rfl
      · intro r hr; simp only [tupDstGprs, List.cons_append, List.nil_append, List.mem_cons, not_or] at hr
        rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1),
          hr1 r (by simp only [x64Scratch, List.mem_cons, List.mem_nil_iff, or_false]; exact fun h => h.elim hr.2.1 hr.2.2.1)]
    cases pa with
    | imm cx =>
      cases pb with
      | imm cy =>
        simp only [opCmp, Option.some.injEq, Prod.mk.injEq] at hc
        rcases hc with ⟨rfl, rfl⟩; rcases hpa with rfl; rcases hpb with rfl
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_moviD s rd _)) ?_
        rintro s' rfl
        exact opPostDst_gpr_bool (by cases co.evalBits cx cy <;> rfl) (updFlags_of_status_eq rfl _)
      | gpr ry =>
        rcases hpa with rfl; simp only [opCmp] at hc
        split at hc
        · simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
          refine useSetcc _ vb cx (condOf (swapCmp co))
            (by rw [cond_subFlags hwn, swapCmp_evalBits]) rfl rfl ?_
          refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_cmp_imm w s ry cx)) ?_
          rintro s1 rfl; exact ⟨fun _ _ => rfl, rfl, rfl, by rw [hpb.2]⟩
        · simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
          refine useSetcc _ cx vb (condOf co) (cond_subFlags hwn _ _ _) rfl rfl ?_
          have hry := (ne_of_not_mem_x64Scratch (hargs ry (by simp [PArg.gprs]))).1
          refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s .r10 (cx.setWidth 64))) ?_
          rintro s1 rfl
          refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_cmp_reg w _ .r10 ry)) ?_
          rintro s2 rfl
          refine ⟨fun r hr => Reg64s.get64_set64_of_ne _ .r10 r _ (ne_of_not_mem_x64Scratch hr).1.symm, rfl, rfl, ?_⟩
          rw [Reg64s.get64_set64_of_ne _ .r10 ry _ hry.symm, hpb.2, Reg64s.get64_set64_same, setWidth_64_setWidth]
      | vec _ => simp [opCmp, cmpDirect] at hc
    | gpr rx =>
      cases pb with
      | vec _ => simp [opCmp, cmpDirect] at hc
      | gpr _ | imm _ =>
        simp only [opCmp, Option.bind_eq_bind] at hc
        rcases Option.bind_eq_some_iff.mp hc with ⟨seq, hseq, hm⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, rfl⟩
        exact useSetcc _ va vb (condOf co) (cond_subFlags hwn _ _ _) rfl rfl
          (wp_cmpDirect w hseq hargs hpa hpb)
    | vec _ => simp [opCmp, cmpDirect] at hc
  | flag cc =>
    have finish (pre : List Directive) (x y : BitVec w.bits)
        (hcc : cc.interp (subFlags x y) = co.evalBits va vb)
        (hc_eq : c = pre) (hcl_eq : clob = maskAll)
        (hpre : _root_.Program.wp pre (fun s1 =>
          (∀ r, r ∉ x64Scratch → s1.regs.get64 r = s.regs.get64 r) ∧
          s1.dmem = s.dmem ∧ s1.zmms = s.zmms ∧ s1.status = subFlags x y) E s) :
        _root_.Program.wp c (OpPostDst1 .bool (.flag cc) (co.evalBits va vb) clob s) E s := by
      subst hc_eq; subst hcl_eq
      refine Program.wp.mono hpre ?_
      rintro s1 ⟨hr1, hm1, hz1, hst1⟩
      refine ⟨?_, hm1, x64_frame_of_eq ?_ hz1 (updFlags_maskAll _ _)⟩
      · dsimp only [Machine.PDstHolds]; rw [hst1, hcc]
      · intro r hr; exact hr1 r (by simpa [tupDstGprs] using hr)
    cases pa with
    | imm cx =>
      cases pb with
      | gpr ry =>
        rcases hpa with rfl; simp only [opCmp] at hc
        split at hc
        · rename_i hcond
          have hcc := (beq_cond_iff cc _).1 ((Bool.and_eq_true ..).mp hcond).1
          simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
          refine finish _ vb cx (by rw [hcc, cond_subFlags hwn, swapCmp_evalBits]) rfl rfl ?_
          refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_cmp_imm w s ry cx)) ?_
          rintro s1 rfl; exact ⟨fun _ _ => rfl, rfl, rfl, by rw [hpb.2]⟩
        · split at hc
          · rename_i hcc; have hcc' := (beq_cond_iff cc _).1 hcc
            simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
            refine finish _ cx vb (by rw [hcc', cond_subFlags hwn]) rfl rfl ?_
            have hry := (ne_of_not_mem_x64Scratch (hargs ry (by simp [PArg.gprs]))).1
            refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s .r10 (cx.setWidth 64))) ?_
            rintro s1 rfl
            refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_cmp_reg w _ .r10 ry)) ?_
            rintro s2 rfl
            refine ⟨fun r hr => Reg64s.get64_set64_of_ne _ .r10 r _ (ne_of_not_mem_x64Scratch hr).1.symm, rfl, rfl, ?_⟩
            rw [Reg64s.get64_set64_of_ne _ .r10 ry _ hry.symm, hpb.2, Reg64s.get64_set64_same, setWidth_64_setWidth]
          · split at hc <;> try contradiction
            rename_i hcc; have hcc' := (beq_cond_iff cc _).1 hcc
            simp only [Option.some.injEq, Prod.mk.injEq] at hc; rcases hc with ⟨rfl, rfl⟩
            refine finish _ vb cx (by rw [hcc', cond_subFlags hwn, swapCmp_evalBits]) rfl rfl ?_
            have hry := (ne_of_not_mem_x64Scratch (hargs ry (by simp [PArg.gprs]))).1
            refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s .r10 (cx.setWidth 64))) ?_
            rintro s1 rfl
            refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_cmp_reg w _ ry .r10)) ?_
            rintro s2 rfl
            refine ⟨fun r hr => Reg64s.get64_set64_of_ne _ .r10 r _ (ne_of_not_mem_x64Scratch hr).1.symm, rfl, rfl, ?_⟩
            rw [Reg64s.get64_set64_of_ne _ .r10 ry _ hry.symm, hpb.2, Reg64s.get64_set64_same, setWidth_64_setWidth]
      | imm cy =>
        simp only [opCmp, Option.bind_eq_bind] at hc
        split at hc
        · rename_i hcc; have hcc' := (beq_cond_iff cc _).1 hcc
          rcases Option.bind_eq_some_iff.mp hc with ⟨seq, hseq, hm⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at hm; rcases hm with ⟨rfl, rfl⟩
          exact finish _ va vb (by rw [hcc', cond_subFlags hwn]) rfl rfl (wp_cmpDirect w hseq hargs hpa hpb)
        · split at hc <;> try contradiction
          rename_i hcc; have hcc' := (beq_cond_iff cc _).1 hcc
          rcases Option.bind_eq_some_iff.mp hc with ⟨seq, hseq, hm⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at hm; rcases hm with ⟨rfl, rfl⟩
          have hargs' : ∀ r ∈ (PArg.imm cy : PArg Reg64 RegMm CondCode (.bits w.bits)).gprs ++
              (PArg.imm cx : PArg Reg64 RegMm CondCode (.bits w.bits)).gprs, r ∉ x64Scratch :=
            fun r hr => by simp [PArg.gprs] at hr
          exact finish _ vb va (by rw [hcc', cond_subFlags hwn, swapCmp_evalBits]) rfl rfl
            (wp_cmpDirect w hseq hargs' hpb hpa)
      | vec _ => simp [opCmp, cmpDirect] at hc
    | gpr rx =>
      cases pb with
      | vec _ => simp [opCmp, cmpDirect] at hc
      | gpr _ | imm _ =>
        simp only [opCmp, Option.bind_eq_bind] at hc
        split at hc
        · rename_i hcc; have hcc' := (beq_cond_iff cc _).1 hcc
          rcases Option.bind_eq_some_iff.mp hc with ⟨seq, hseq, hm⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at hm; rcases hm with ⟨rfl, rfl⟩
          exact finish _ va vb (by rw [hcc', cond_subFlags hwn]) rfl rfl (wp_cmpDirect w hseq hargs hpa hpb)
        · split at hc <;> try contradiction
          rename_i hcc; have hcc' := (beq_cond_iff cc _).1 hcc
          rcases Option.bind_eq_some_iff.mp hc with ⟨seq, hseq, hm⟩
          simp only [Option.some.injEq, Prod.mk.injEq] at hm; rcases hm with ⟨rfl, rfl⟩
          have hargs' : ∀ r ∈ _ ++ (PArg.gpr rx : PArg Reg64 RegMm CondCode (.bits w.bits)).gprs, r ∉ x64Scratch :=
            fun r hr => hargs r (by simp [List.mem_append] at hr ⊢; exact hr.symm)
          exact finish _ vb va (by rw [hcc', cond_subFlags hwn, swapCmp_evalBits]) rfl rfl
            (wp_cmpDirect w hseq hargs' hpb hpa)
    | vec _ => simp [opCmp, cmpDirect] at hc

/-! ## 2. `AllInstr` Lemmas for `opSelect`, `opShift`, and `opFunnel` -/

theorem selectFlagSeq_allInstr {w : Width} {cc : CondCode}
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64} {c : List Directive}
    (h : selectFlagSeq w cc pa pb rd = some c) : AllInstr c := by
  cases pa <;> cases pb <;> simp only [selectFlagSeq] at h <;> try contradiction
  · split at h
    · split at h <;> simp only [Option.some.injEq] at h <;> subst h <;> simp
    · split at h
      · simp only [Option.some.injEq] at h; subst h; simp
      · split at h <;> simp only [Option.some.injEq] at h <;> subst h <;> simp
  · split at h <;> simp only [Option.some.injEq] at h <;> subst h <;> simp
  · split at h <;> simp only [Option.some.injEq] at h <;> subst h <;> simp
  · simp only [Option.some.injEq] at h; subst h; simp

theorem opSelect_allInstr {w : Width} {pc : PArg Reg64 RegMm CondCode .bool}
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64}
    {c : List Directive} {clob : FlagMask}
    (h : opSelect w pc pa pb rd = some (c, clob)) : AllInstr c := by
  cases pc with
  | imm b => exact opCopyBits_allInstr h
  | flag cc =>
    simp only [opSelect] at h
    rcases Option.map_eq_some_iff.mp h with ⟨seq, hseq, hm⟩
    cases hm; exact selectFlagSeq_allInstr hseq
  | gpr rc =>
    simp only [opSelect] at h
    rcases Option.map_eq_some_iff.mp h with ⟨seq, hseq, hm⟩
    cases hm; simp [selectFlagSeq_allInstr hseq]
  | vec _ => simp [opSelect] at h

theorem opShift_allInstr {w : Width} {sk : ShiftKind}
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64}
    {c : List Directive} {clob : FlagMask}
    (h : opShift w sk pa pb rd = some (c, clob)) : AllInstr c := by
  cases pb with
  | vec _ => simp [opShift] at h
  | imm cb =>
    simp only [opShift] at h; split at h
    · exact opCopyBits_allInstr h
    · cases pa with
      | vec _ => simp at h
      | gpr _ | imm _ => rcases h with ⟨rfl, -⟩; simp
  | gpr rb =>
    simp only [opShift, Option.bind_eq_bind] at h
    rcases Option.bind_eq_some_iff.mp h with ⟨d1, hd1, h'⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at h'
    rcases h' with ⟨rfl, -⟩
    obtain ⟨_, e1⟩ := isInstr_argToBits hd1
    simp [e1]

theorem opFunnel_allInstr {w : Width} {isRight : Bool}
    {pa pb pc : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64}
    {c : List Directive} {clob : FlagMask}
    (h : opFunnel w isRight pa pb pc rd = some (c, clob)) : AllInstr c := by
  cases pc with
  | vec _ => simp [opFunnel] at h
  | imm cb =>
    simp only [opFunnel] at h; split at h
    · exact opCopyBits_allInstr h
    · simp only [Option.bind_eq_bind] at h
      rcases Option.bind_eq_some_iff.mp h with ⟨d1, hd1, h1⟩
      rcases Option.bind_eq_some_iff.mp h1 with ⟨d2, hd2, h2⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at h2; rcases h2 with ⟨rfl, -⟩
      obtain ⟨_, e1⟩ := isInstr_argToBits hd1
      obtain ⟨_, e2⟩ := isInstr_argToBits hd2
      simp [e1, e2]
  | gpr rc =>
    simp only [opFunnel, Option.bind_eq_bind] at h
    rcases Option.bind_eq_some_iff.mp h with ⟨d1, hd1, h1⟩
    rcases Option.bind_eq_some_iff.mp h1 with ⟨d2, hd2, h2⟩
    obtain ⟨_, e1⟩ := isInstr_argToBits hd1
    obtain ⟨_, e2⟩ := isInstr_argToBits hd2
    split at h2
    · simp only [Option.some.injEq, Prod.mk.injEq] at h2; rcases h2 with ⟨rfl, -⟩; simp [e1, e2]
    · split at h2 <;> simp only [Option.some.injEq, Prod.mk.injEq] at h2 <;> rcases h2 with ⟨rfl, -⟩ <;> simp [e1, e2]

/-! ## 3. `opSelect_spec` (`cmovcc`, never branching) -/

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

private theorem wp_selectFlagSeq [Host] {E : Int64 → MachineData → Prop} (w : Width) (cc : CondCode)
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64} {c : List Directive}
    {va vb : BitVec w.bits} {s : MachineData}
    (hc : selectFlagSeq w cc pa pb rd = some c)
    (hrd : rd ∉ x64Scratch)
    (hargs : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ x64Scratch)
    (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va)
    (hpb : x64Mach.PArgHolds s (.bits w.bits) pb vb) :
    _root_.Program.wp c (fun s' =>
      ((s'.regs.get64 rd).setWidth w.bits = if cc.interp s.status then va else vb) ∧
      (∀ r, r ≠ rd → r ∉ x64Scratch → s'.regs.get64 r = s.regs.get64 r) ∧
      s'.dmem = s.dmem ∧ s'.zmms = s.zmms ∧ s'.status = s.status) E s := by
  let cw : Width := if w == .W64 then .W64 else .W32
  have hcw : cw = .W32 ∨ cw = .W64 := by cases w <;> simp [cw]
  have hwle : w.bits ≤ cw.bits := by cases w <;> simp [cw, Width.bits]
  have hrd10 := (ne_of_not_mem_x64Scratch hrd).1
  cases pa with
  | vec _ => cases pb <;> simp [selectFlagSeq] at hc
  | gpr ra =>
    cases pb with
    | vec _ => simp [selectFlagSeq] at hc
    | gpr rb =>
      simp only [selectFlagSeq] at hc
      by_cases hab : ra == rb
      · have heq := (beq_reg64_iff ra rb).1 hab; subst rb
        simp only [hab, ↓reduceIte] at hc
        by_cases har : ra == rd
        · have heq := (beq_reg64_iff ra rd).1 har; subst ra
          simp only [har, ↓reduceIte, Option.some.injEq] at hc; subst hc
          refine _root_.Program.wp_nil ⟨?_, fun _ _ _ => rfl, rfl, rfl, rfl⟩
          rw [hpa.2]
          have hv : va = vb := hpa.2.symm.trans hpb.2
          subst hv; cases cc.interp s.status <;> rfl
        · simp only [har, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hc; subst hc
          refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movW cw s rd ra)) ?_
          rintro s' rfl
          refine ⟨?_, fun r hr _ => Reg64s.get64_set64_of_ne _ rd r _ hr.symm, rfl, rfl, rfl⟩
          rw [Reg64s.get64_set64_same, BitVec.setWidth_setWidth_of_le _ (width_bits_le_64 w),
            BitVec.setWidth_setWidth_of_le _ hwle]
          have hv : va = vb := hpa.2.symm.trans hpb.2
          rw [hpa.2, hv]; cases cc.interp s.status <;> rfl
      · simp only [hab, Bool.false_eq_true, ↓reduceIte] at hc
        have hab_ne : ra ≠ rb := fun h => hab ((beq_reg64_iff ra rb).2 h)
        by_cases hrbd : rd == rb
        · have heq := (beq_reg64_iff rd rb).1 hrbd; subst rb
          simp only [hrbd, ↓reduceIte, Option.some.injEq] at hc; subst hc
          refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_cmovcc cw hcw cc s rd ra)) ?_
          rintro s' rfl
          refine ⟨?_, fun r hr _ => Reg64s.get64_set64_of_ne _ rd r _ hr.symm, rfl, rfl, rfl⟩
          rw [Reg64s.get64_set64_same, BitVec.setWidth_setWidth_of_le _ (width_bits_le_64 w)]
          cases cc.interp s.status <;> simp [BitVec.setWidth_setWidth_of_le _ hwle, hpa.2, hpb.2]
        · simp only [hrbd, Bool.false_eq_true, ↓reduceIte] at hc
          by_cases hrad : rd == ra
          · have heq := (beq_reg64_iff rd ra).1 hrad; subst ra
            simp only [hrad, ↓reduceIte, Option.some.injEq] at hc; subst hc
            refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_cmovcc cw hcw (x64NegCond cc) s rd rb)) ?_
            rintro s' rfl
            refine ⟨?_, fun r hr _ => Reg64s.get64_set64_of_ne _ rd r _ hr.symm, rfl, rfl, rfl⟩
            rw [Reg64s.get64_set64_same, BitVec.setWidth_setWidth_of_le _ (width_bits_le_64 w),
              x64NegCond_interp]
            cases cc.interp s.status <;> simp [BitVec.setWidth_setWidth_of_le _ hwle, hpa.2, hpb.2]
          · simp only [hrad, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hc; subst hc
            have hrad_ne : ra ≠ rd := fun h => hrad ((beq_reg64_iff rd ra).2 h.symm)
            refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_movW cw s rd rb)) ?_
            rintro s1 rfl
            refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_cmovcc cw hcw cc _ rd ra)) ?_
            rintro s2 rfl
            refine ⟨?_, fun r hr _ => ?_, rfl, rfl, rfl⟩
            · rw [Reg64s.get64_set64_same, BitVec.setWidth_setWidth_of_le _ (width_bits_le_64 w)]
              cases cc.interp s.status
              · simp [BitVec.setWidth_setWidth_of_le _ hwle,
                  BitVec.setWidth_setWidth_of_le _ (width_bits_le_64 cw),
                  Reg64s.get64_set64_same, hpb.2]
              · simp [BitVec.setWidth_setWidth_of_le _ hwle,
                  Reg64s.get64_set64_of_ne _ rd ra _ hrad_ne.symm, hpa.2]
            · rw [Reg64s.get64_set64_of_ne _ rd r _ hr.symm, Reg64s.get64_set64_of_ne _ rd r _ hr.symm]
    | imm cb =>
      rcases hpb with rfl; simp only [selectFlagSeq] at hc
      have ha10 := (ne_of_not_mem_x64Scratch (hargs ra (by simp [PArg.gprs]))).1
      by_cases hrad : rd == ra
      · have heq := (beq_reg64_iff rd ra).1 hrad; subst ra
        simp only [hrad, ↓reduceIte, Option.some.injEq] at hc; subst hc
        have hrd10' : rd ≠ .r10 := ha10
        refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s .r10 (cb.setWidth 64))) ?_
        rintro s1 rfl
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_cmovcc cw hcw (x64NegCond cc) _ rd .r10)) ?_
        rintro s2 rfl
        refine ⟨?_, fun r hr hsc => ?_, rfl, rfl, rfl⟩
        · rw [Reg64s.get64_set64_same, BitVec.setWidth_setWidth_of_le _ (width_bits_le_64 w),
            x64NegCond_interp]
          cases cc.interp s.status
          · simp [BitVec.setWidth_setWidth_of_le _ hwle,
              BitVec.setWidth_setWidth_of_le _ (width_bits_le_64 cw), Reg64s.get64_set64_same]
          · simp [BitVec.setWidth_setWidth_of_le _ hwle,
              Reg64s.get64_set64_of_ne _ .r10 rd _ hrd10'.symm, hpa.2]
        · rw [Reg64s.get64_set64_of_ne _ rd r _ hr.symm,
            Reg64s.get64_set64_of_ne _ .r10 r _ (ne_of_not_mem_x64Scratch hsc).1.symm]
      · simp only [hrad, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hc; subst hc
        have hrad_ne : ra ≠ rd := fun h => hrad ((beq_reg64_iff rd ra).2 h.symm)
        refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s rd (cb.setWidth 64))) ?_
        rintro s1 rfl
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_cmovcc cw hcw cc _ rd ra)) ?_
        rintro s2 rfl
        refine ⟨?_, fun r hr _ => ?_, rfl, rfl, rfl⟩
        · rw [Reg64s.get64_set64_same, BitVec.setWidth_setWidth_of_le _ (width_bits_le_64 w)]
          cases cc.interp s.status
          · simp [BitVec.setWidth_setWidth_of_le _ hwle,
              BitVec.setWidth_setWidth_of_le _ (width_bits_le_64 cw), Reg64s.get64_set64_same]
          · simp [BitVec.setWidth_setWidth_of_le _ hwle,
              Reg64s.get64_set64_of_ne _ rd ra _ hrad_ne.symm, hpa.2]
        · rw [Reg64s.get64_set64_of_ne _ rd r _ hr.symm, Reg64s.get64_set64_of_ne _ rd r _ hr.symm]
  | imm ca =>
    rcases hpa with rfl
    cases pb with
    | vec _ => simp [selectFlagSeq] at hc
    | gpr rb =>
      simp only [selectFlagSeq] at hc
      have hb10 := (ne_of_not_mem_x64Scratch (hargs rb (by simp [PArg.gprs]))).1
      by_cases hrbd : rd == rb
      · have heq := (beq_reg64_iff rd rb).1 hrbd; subst rb
        simp only [hrbd, ↓reduceIte, Option.some.injEq] at hc; subst hc
        have hrd10' : rd ≠ .r10 := hb10
        refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s .r10 (ca.setWidth 64))) ?_
        rintro s1 rfl
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_cmovcc cw hcw cc _ rd .r10)) ?_
        rintro s2 rfl
        refine ⟨?_, fun r hr hsc => ?_, rfl, rfl, rfl⟩
        · rw [Reg64s.get64_set64_same, BitVec.setWidth_setWidth_of_le _ (width_bits_le_64 w)]
          cases cc.interp s.status
          · simp [BitVec.setWidth_setWidth_of_le _ hwle,
              Reg64s.get64_set64_of_ne _ .r10 rd _ hrd10'.symm, hpb.2]
          · simp [BitVec.setWidth_setWidth_of_le _ hwle,
              BitVec.setWidth_setWidth_of_le _ (width_bits_le_64 cw), Reg64s.get64_set64_same]
        · rw [Reg64s.get64_set64_of_ne _ rd r _ hr.symm,
            Reg64s.get64_set64_of_ne _ .r10 r _ (ne_of_not_mem_x64Scratch hsc).1.symm]
      · simp only [hrbd, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hc; subst hc
        have hrbd_ne : rb ≠ rd := fun h => hrbd ((beq_reg64_iff rd rb).2 h.symm)
        refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s rd (ca.setWidth 64))) ?_
        rintro s1 rfl
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_cmovcc cw hcw (x64NegCond cc) _ rd rb)) ?_
        rintro s2 rfl
        refine ⟨?_, fun r hr _ => ?_, rfl, rfl, rfl⟩
        · rw [Reg64s.get64_set64_same, BitVec.setWidth_setWidth_of_le _ (width_bits_le_64 w),
            x64NegCond_interp]
          cases cc.interp s.status
          · simp [BitVec.setWidth_setWidth_of_le _ hwle,
              Reg64s.get64_set64_of_ne _ rd rb _ hrbd_ne.symm, hpb.2]
          · simp [BitVec.setWidth_setWidth_of_le _ hwle,
              BitVec.setWidth_setWidth_of_le _ (width_bits_le_64 cw), Reg64s.get64_set64_same]
        · rw [Reg64s.get64_set64_of_ne _ rd r _ hr.symm, Reg64s.get64_set64_of_ne _ rd r _ hr.symm]
    | imm cb =>
      rcases hpb with rfl; simp only [selectFlagSeq] at hc
      simp only [Option.some.injEq] at hc; subst hc
      refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD s rd (cb.setWidth 64))) ?_
      rintro s1 rfl
      refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_moviD _ .r10 (ca.setWidth 64))) ?_
      rintro s2 rfl
      refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_cmovcc cw hcw cc _ rd .r10)) ?_
      rintro s3 rfl
      refine ⟨?_, fun r hr hsc => ?_, rfl, rfl, rfl⟩
      · rw [Reg64s.get64_set64_same, BitVec.setWidth_setWidth_of_le _ (width_bits_le_64 w)]
        cases cc.interp s.status
        · simp [BitVec.setWidth_setWidth_of_le _ hwle,
            BitVec.setWidth_setWidth_of_le _ (width_bits_le_64 cw),
            Reg64s.get64_set64_of_ne _ .r10 rd _ hrd10.symm, Reg64s.get64_set64_same]
        · simp [BitVec.setWidth_setWidth_of_le _ hwle,
            BitVec.setWidth_setWidth_of_le _ (width_bits_le_64 cw), Reg64s.get64_set64_same]
      · rw [Reg64s.get64_set64_of_ne _ rd r _ hr.symm,
          Reg64s.get64_set64_of_ne _ .r10 r _ (ne_of_not_mem_x64Scratch hsc).1.symm,
          Reg64s.get64_set64_of_ne _ rd r _ hr.symm]

theorem opSelect_spec [Host] {E : Int64 → MachineData → Prop} (w : Width)
    {pc : PArg Reg64 RegMm CondCode .bool}
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64}
    {c : List Directive} {clob : FlagMask} {b : Bool} {va vb : BitVec w.bits} {s : MachineData}
    (hc : opSelect w pc pa pb rd = some (c, clob))
    (hrd : rd ∉ x64Scratch)
    (hargs : ∀ r ∈ pc.gprs ++ pa.gprs ++ pb.gprs, r ∉ x64Scratch)
    (hpc : x64Mach.PArgHolds s .bool pc b)
    (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va)
    (hpb : x64Mach.PArgHolds s (.bits w.bits) pb vb) :
    _root_.Program.wp c (OpPost1 (.bits w.bits) rd (if b then va else vb) clob s) E s := by
  have hab : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ x64Scratch := fun r hr => hargs r (by simp_all)
  cases pc with
  | vec _ => simp [opSelect] at hc
  | imm b0 =>
    rcases hpc with rfl; unfold opSelect at hc
    cases b0 <;> exact opCopyBits_spec w hc (by assumption)
  | flag cc =>
    simp only [opSelect] at hc
    rcases Option.map_eq_some_iff.mp hc with ⟨seq, hseq, hm⟩
    simp only [Prod.mk.injEq] at hm; rcases hm with ⟨rfl, rfl⟩
    have hcc : cc.interp s.status = b := hpc
    refine Program.wp.mono (wp_selectFlagSeq w cc hseq hrd hab hpa hpb) ?_
    rintro s' ⟨hrd', hfr, hm', hz', hst'⟩
    refine ⟨(GprHolds.bits_iff w _ _).2 (by rw [hrd', hcc]), hm',
      x64_frame_of_eq ?_ hz' (updFlags_of_status_eq hst' _)⟩
    intro r hr; simp only [List.mem_cons, not_or] at hr
    exact hfr r hr.1 (by simp only [x64Scratch, List.mem_cons, List.mem_nil_iff, or_false]; exact fun h => h.elim hr.2.1 hr.2.2.1)
  | gpr rc =>
    simp only [opSelect] at hc
    rcases Option.map_eq_some_iff.mp hc with ⟨seq, hseq, hm⟩
    simp only [Prod.mk.injEq] at hm; rcases hm with ⟨rfl, rfl⟩
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_testb_self s rc hpc)) ?_
    rintro s1 ⟨st1, rfl, hnz⟩
    have hpa1 : x64Mach.PArgHolds { s with status := st1 } (.bits w.bits) pa va := by
      cases pa <;> exact hpa
    have hpb1 : x64Mach.PArgHolds { s with status := st1 } (.bits w.bits) pb vb := by
      cases pb <;> exact hpb
    refine Program.wp.mono (wp_selectFlagSeq w .nz hseq hrd hab hpa1 hpb1) ?_
    rintro s2 ⟨hrd', hfr, hm', hz', _⟩
    refine ⟨(GprHolds.bits_iff w _ _).2 (by rw [hrd', hnz]), hm',
      x64_frame_of_eq ?_ hz' (updFlags_maskAll _ _)⟩
    intro r hr; simp only [List.mem_cons, not_or] at hr
    exact hfr r hr.1 (by simp only [x64Scratch, List.mem_cons, List.mem_nil_iff, or_false]; exact fun h => h.elim hr.2.1 hr.2.2.1)

/-! ## 4. `opShift_spec` (`shl`/`lshr`/`ashr`/`rotl`/`rotr` + 8/16-bit mask trap) -/

def ShiftKind.eval {n : Nat} : ShiftKind → BitVec n → Nat → BitVec n
  | .shl,  x, k => x <<< k
  | .lshr, x, k => x >>> k
  | .ashr, x, k => x.sshiftRight k
  | .rotl, x, k => x.rotateLeft k
  | .rotr, x, k => x.rotateRight k

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

theorem setRegW_eq_set64 (w : Width) (s : MachineData) (rd : Reg64) (v : w.type) (st : StatusFlags) :
    ∃ rv, rv.setWidth w.bits = v ∧
      ({ s with regs := s.regs.set (regW w rd) v, status := st } : MachineData) =
        { s with regs := s.regs.set64 rd rv, status := st } := by
  cases w <;> simp only [regW, Reg64s.set]
  · exact ⟨_, replaceLow_setWidth_le (by decide) _ _, rfl⟩
  · exact ⟨_, replaceLow_setWidth_le (by decide) _ _, rfl⟩
  · exact ⟨_, by simp [Width.bits], rfl⟩
  · exact ⟨_, rfl, rfl⟩

private theorem fallsTo_shiftW (w : Width) (sk : ShiftKind) (s : MachineData) (rd : Reg64)
    (ce : ShiftCountExpr) (k : Nat) (hk_lt : k < w.bits)
    (hk : ∀ [Labels] (p : Std.Rco Int64), ce.interpMasked s p w = k) :
    Directive.FallsTo (insW w (sk.toOp (.reg (regW w rd)) ce)) s (fun s' =>
      ∃ rv status, rv.setWidth w.bits = sk.eval ((s.regs.get64 rd).setWidth w.bits) k ∧
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
      { obtain ⟨rv, hrv, hs⟩ := setRegW_eq_set64 _ s rd _ s.status
        exact hcont _ ⟨rv, s.status, hrv.trans (ShiftKind.eval_zero _ _).symm, fun _ => ⟨rfl, rfl, rfl⟩, hs⟩ }
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
          obtain ⟨rv, hrv, hs⟩ := setRegW_eq_set64 _ s rd _ _
          exact hcont _ ⟨rv, _, hrv, fun h => by solve | cases h | exact ⟨rfl, rfl, rfl⟩, hs⟩
        · simp only [beq_false_of_ne hk1, Bool.false_eq_true, ↓reduceIte]; intro _
          try dsimp only [ShiftKind.eval, ShiftKind.isRot]
          obtain ⟨rv, hrv, hs⟩ := setRegW_eq_set64 _ s rd _ _
          exact hcont _ ⟨rv, _, hrv, fun h => by solve | cases h | exact ⟨rfl, rfl, rfl⟩, hs⟩ }

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

theorem opShift_spec [Host] {E : Int64 → MachineData → Prop} (w : Width) (sk : ShiftKind)
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64}
    {c : List Directive} {clob : FlagMask} {va vb : BitVec w.bits} {s : MachineData}
    (hc : opShift w sk pa pb rd = some (c, clob))
    (_hrd : rd ∉ x64Scratch)
    (hargs : ∀ r ∈ pa.gprs ++ pb.gprs, r ∉ x64Scratch)
    (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va)
    (hpb : x64Mach.PArgHolds s (.bits w.bits) pb vb) :
    _root_.Program.wp c (OpPost1 (.bits w.bits) rd (sk.eval va (vb.toNat % w.bits)) clob s) E s := by
  cases pb with
  | vec _ => simp [opShift] at hc
  | imm cb =>
    rcases hpb with rfl; simp only [opShift] at hc
    by_cases hcnt : cb.toNat % w.bits == 0
    · simp only [hcnt, ↓reduceIte] at hc; rw [beq_iff_eq.1 hcnt, sk.eval_zero]; exact opCopyBits_spec w hc hpa
    · simp only [hcnt, Bool.false_eq_true, ↓reduceIte] at hc
      have hsetup : ∃ seq, c = seq ++ [insW w (sk.toOp (.reg (regW w rd))
          (.imm8 (.int64 (Int64.ofNat (cb.toNat % w.bits)))))] ∧
          clob = (if sk.isRot then maskCF ||| maskOF else maskAll) ∧
          _root_.Program.wp seq (fun s1 => (s1.regs.get64 rd).setWidth w.bits = va ∧
            (∀ r, r ≠ rd → s1.regs.get64 r = s.regs.get64 r) ∧
            s1.dmem = s.dmem ∧ s1.zmms = s.zmms ∧ s1.status = s.status) E s := by
        cases pa with
        | vec _ => cases hc
        | gpr ra =>
          rcases hc with ⟨rfl, rfl⟩
          exact ⟨_, rfl, rfl, wp_optMovW w s rd ra (GprHolds.bits_iff w _ _ |>.1 hpa)⟩
        | imm ca =>
          rcases hpa with rfl
          rcases hc with ⟨rfl, rfl⟩
          refine ⟨_, rfl, rfl, Program.wp.mono (Directive.FallsTo.wp (fallsTo_moviD s rd (ca.setWidth 64))) ?_⟩
          rintro s1 rfl; exact ⟨by simp [setWidth_64_setWidth], fun r hr => Reg64s.get64_set64_of_ne _ rd r _ hr.symm, rfl, rfl, rfl⟩
      rcases hsetup with ⟨seq, rfl, rfl, hwp⟩
      refine Program.wp.append hwp ?_; rintro s1 ⟨hrd1, hfr1, hm1, hz1, hst1⟩
      refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_shiftW w sk s1 rd
        (.imm8 (.int64 (Int64.ofNat (cb.toNat % w.bits)))) (cb.toNat % w.bits)
        (Nat.mod_lt _ (width_bits_pos w)) (fun p => shiftMask_imm_eq w cb p s1))) ?_
      rintro s2 ⟨rv, st, hrv, hrot, rfl⟩
      refine ⟨(GprHolds.bits_iff w _ _).2 (by rw [Reg64s.get64_set64_same, hrv, hrd1]), hm1,
        x64_frame_of_eq (fun r hr => ?_) hz1 ?_⟩
      · simp only [List.mem_cons, not_or] at hr; rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1), hfr1 r hr.1]
      · by_cases hr : sk.isRot = true
        · simp only [hr, ↓reduceIte]; obtain ⟨h1, h2, h3⟩ := hrot hr
          exact updFlags_maskCF_OF (h1.trans (congrArg StatusFlags.pf hst1))
            (h2.trans (congrArg StatusFlags.zf hst1)) (h3.trans (congrArg StatusFlags.sf hst1))
        · simp only [hr, Bool.false_eq_true, ↓reduceIte]; exact updFlags_maskAll _ _
  | gpr rb =>
    simp only [opShift, Option.bind_eq_bind] at hc
    rcases Option.bind_eq_some_iff.mp hc with ⟨d1, hd1, hm⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at hm; rcases hm with ⟨rfl, rfl⟩
    have hvb : (s.regs.get64 rb).setWidth w.bits = vb := (GprHolds.bits_iff w _ _).1 hpb
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_argToBits s .r11 hd1 hpa)) ?_; rintro s1 ⟨rv11, hrv11, rfl⟩
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_movD _ .r10 .rcx)) ?_; rintro s2 rfl
    dsimp only; rw [Reg64s.get64_set64_of_ne _ .r11 .rcx _ (by decide)]
    have hrcx_step : _root_.Program.wp (if rb == .rcx then [] else [movW w .rcx rb])
        (fun s3 => ∃ rcxVal, rcxVal.setWidth w.bits = vb ∧
          s3 = { s with regs := ((s.regs.set64 .r11 rv11).set64 .r10 (s.regs.get64 .rcx)).set64 .rcx rcxVal }) E
        { s with regs := (s.regs.set64 .r11 rv11).set64 .r10 (s.regs.get64 .rcx) } := by
      by_cases hrc : rb == .rcx
      · have heq := (beq_reg64_iff rb .rcx).1 hrc; subst heq; simp only [hrc, ↓reduceIte]
        refine _root_.Program.wp_nil ⟨s.regs.get64 .rcx, hvb, ?_⟩
        congr 1
      · simp only [hrc, Bool.false_eq_true, ↓reduceIte]
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movW w _ .rcx rb)) ?_; rintro s3 rfl
        have hrb_ne := ne_of_not_mem_x64Scratch (hargs rb (by simp [PArg.gprs]))
        exact ⟨_, by rw [setWidth_64_setWidth, Reg64s.get64_set64_of_ne _ .r10 rb _ hrb_ne.1.symm,
          Reg64s.get64_set64_of_ne _ .r11 rb _ hrb_ne.2.symm, hvb], rfl⟩
    simp only [List.append_eq, List.nil_append, List.append_assoc]
    refine Program.wp.append hrcx_step ?_; rintro s3 ⟨rcxVal, hrcxVal, rfl⟩
    refine Program.wp.append (wp_shiftMaskRcx w s _ (Reg64s.get64_set64_same _ _ _) hrcxVal) ?_
    rintro s4 ⟨rcxM, stM, hcl, hstM, rfl⟩
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_shiftW w sk _ .r11 .cl (vb.toNat % w.bits)
      (Nat.mod_lt _ (width_bits_pos w)) hcl)) ?_; rintro s5 ⟨rv11', st5, hrv11', hrot5, rfl⟩
    refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_movD _ .rcx .r10)) ?_; rintro s6 rfl
    refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movW w _ rd .r11)) ?_; rintro s7 rfl
    have hva11 : ((((s.regs.set64 .r11 rv11).set64 .r10 (s.regs.get64 .rcx)).set64 .rcx rcxM).get64 .r11).setWidth w.bits = va := by
      rw [Reg64s.get64_set64_of_ne _ .rcx .r11 _ (by decide), Reg64s.get64_set64_of_ne _ .r10 .r11 _ (by decide),
        Reg64s.get64_set64_same, hrv11]
    refine ⟨(GprHolds.bits_iff w _ _).2 (by rw [Reg64s.get64_set64_same, setWidth_64_setWidth,
      Reg64s.get64_set64_of_ne _ .rcx .r11 _ (by decide), Reg64s.get64_set64_same, hrv11',
      Reg64s.set64_set64_same, hva11]), rfl,
      x64_frame_of_eq (fun r hr => ?_) rfl ?_⟩
    · simp only [List.mem_cons, not_or] at hr
      have hne10 : r ≠ .r10 := hr.2.1; have hne11 : r ≠ .r11 := hr.2.2.1
      rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1)]
      by_cases hrc : r = .rcx
      · subst hrc; simp only [Reg64s.get64_set64_same, Reg64s.get64_set64_of_ne _ .r11 .r10 _ (by decide),
          Reg64s.get64_set64_of_ne _ .rcx .r10 _ (by decide)]
      · simp only [Reg64s.get64_set64_of_ne _ .rcx r _ (Ne.symm hrc),
          Reg64s.get64_set64_of_ne _ .r10 r _ hne10.symm,
          Reg64s.get64_set64_of_ne _ .r11 r _ hne11.symm]
    · by_cases hw32 : w = .W8 ∨ w = .W16
      · rw [show (if w == .W8 || w == .W16 then maskAll else if sk.isRot then maskCF ||| maskOF else maskAll) = maskAll by
          rcases hw32 with rfl | rfl <;> rfl]
        exact updFlags_maskAll _ _
      · have hw32' : w = .W32 ∨ w = .W64 := by cases w <;> simp at hw32 ⊢
        simp only [show (w == .W8 || w == .W16) = false by rcases hw32' with rfl | rfl <;> rfl,
          Bool.false_eq_true, ↓reduceIte]
        by_cases hrot : sk.isRot = true
        · simp only [hrot, ↓reduceIte]; obtain ⟨p1, z1, s1⟩ := hrot5 hrot; obtain ⟨p0, z0, s0⟩ := hstM hw32'
          exact updFlags_maskCF_OF (p1.trans p0) (z1.trans z0) (s1.trans s0)
        · simp only [hrot, Bool.false_eq_true, ↓reduceIte]; exact updFlags_maskAll _ _

/-! ## 5. `opFunnel_spec` (`fshl`/`fshr` via `shld`/`shrd` on `.W32`/`.W64`) -/

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
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {va vb : BitVec w.bits} {d1 d2 : Directive}
    (hd1 : argToBits w .r11 pa = some d1) (hd2 : argToBits w .r10 pb = some d2)
    (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va) (hpb : x64Mach.PArgHolds s (.bits w.bits) pb vb)
    (hpb_sc : ∀ r ∈ pb.gprs, r ∉ x64Scratch) {rest : List Directive} {Q : MachineData → Prop}
    (hk : ∀ rv11 rv10, rv11.setWidth w.bits = va → rv10.setWidth w.bits = vb →
      _root_.Program.wp rest Q E { s with regs := (s.regs.set64 .r11 rv11).set64 .r10 rv10 }) :
    _root_.Program.wp (d1 :: d2 :: rest) Q E s := by
  refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_argToBits s .r11 hd1 hpa)) ?_; rintro s1 ⟨rv11, hrv11, rfl⟩
  have hpb1 : x64Mach.PArgHolds { s with regs := s.regs.set64 .r11 rv11 } (.bits w.bits) pb vb := by
    cases pb with | vec _ => simp [argToBits] at hd2 | imm _ => exact hpb | gpr rx =>
      have hx := (ne_of_not_mem_x64Scratch (hpb_sc rx (by simp [PArg.gprs]))).2
      dsimp only [Machine.PArgHolds, GprHolds, Machine.getGpr] at hpb ⊢; rw [Reg64s.get64_set64_of_ne _ .r11 rx _ hx.symm]; exact hpb
  refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_argToBits _ .r10 hd2 hpb1)) ?_; rintro s2 ⟨rv10, hrv10, rfl⟩; exact hk rv11 rv10 hrv11 hrv10

theorem opFunnel_spec [Host] {E : Int64 → MachineData → Prop} (w : Width) (hw : w = .W32 ∨ w = .W64)
    (isRight : Bool) {pa pb pc : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64}
    {c : List Directive} {clob : FlagMask} {va vb vc : BitVec w.bits} {s : MachineData}
    (hc : opFunnel w isRight pa pb pc rd = some (c, clob)) (hrd : rd ∉ x64Scratch)
    (hargs : ∀ r ∈ pa.gprs ++ pb.gprs ++ pc.gprs, r ∉ x64Scratch)
    (hpa : x64Mach.PArgHolds s (.bits w.bits) pa va) (hpb : x64Mach.PArgHolds s (.bits w.bits) pb vb)
    (hpc : x64Mach.PArgHolds s (.bits w.bits) pc vc) :
    _root_.Program.wp c (OpPost1 (.bits w.bits) rd (if isRight then ((va ++ vb) >>> (vc.toNat % w.bits)).extractLsb' 0 w.bits
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
        (OpPost1 (.bits w.bits) rd (if isRight then ((va ++ vb) >>> (vc.toNat % w.bits)).extractLsb' 0 w.bits
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
    refine ⟨(GprHolds.bits_iff w _ _).2 (by rw [Reg64s.get64_set64_same, setWidth_64_setWidth, h11_4]), hm4,
      x64_frame_of_eq (fun r hr => ?_) hz4 (updFlags_maskAll _ _)⟩
    simp only [List.mem_cons, not_or] at hr; rw [Reg64s.get64_set64_of_ne _ rd r _ (Ne.symm hr.1)]
    exact hsav4 r hr.1 (by simp only [x64Scratch, List.mem_cons, List.mem_nil_iff, or_false]; exact fun h => h.elim hr.2.1 hr.2.2.1)
  cases pc with
  | vec _ => simp [opFunnel] at hc
  | imm cb =>
    rcases hpc with rfl; simp only [opFunnel] at hc
    by_cases hcnt : cb.toNat % w.bits == 0
    · simp only [hcnt, ↓reduceIte] at hc
      have hres : (if isRight then ((va ++ vb) >>> (cb.toNat % w.bits)).extractLsb' 0 w.bits
          else ((va ++ vb) <<< (cb.toNat % w.bits)).extractLsb' w.bits w.bits) = if isRight then vb else va := by
        rw [beq_iff_eq.1 hcnt]; rcases hw with rfl | rfl <;> cases isRight <;> first | exact extractLsb'_hi_append _ va vb | exact extractLsb'_lo_append _ va vb
      rw [hres]; cases isRight <;> exact opCopyBits_spec w hc (by assumption)
    · simp only [hcnt, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind] at hc
      rcases Option.bind_eq_some_iff.mp hc with ⟨dDst, hd1, h1⟩; rcases Option.bind_eq_some_iff.mp h1 with ⟨dSrc, hd2, h2⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at h2; rcases h2 with ⟨rfl, rfl⟩
      refine wp_argPair11_10 w s hd1 hd2 hd_h hs_h hs_sc fun rv11 rv10 hrv11 hrv10 => ?_
      refine tail_wp (restoreRcx := false) hrv11 hrv10 (by rw [Reg64s.get64_set64_of_ne _ .r10 .r11 _ (by decide), Reg64s.get64_set64_same])
        (by rw [Reg64s.get64_set64_same]) rfl rfl (fun p => shiftMask_imm_eq w cb p s) rfl ?_
      intro r _ hsc; have hne := ne_of_not_mem_x64Scratch hsc
      simp [Reg64s.get64_set64_of_ne _ .r10 r _ hne.1.symm, Reg64s.get64_set64_of_ne _ .r11 r _ hne.2.symm]
  | gpr rc =>
    simp only [opFunnel, Option.bind_eq_bind] at hc
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
      refine wp_argPair11_10 w s hd1 hd2 hd_h hs_h hs_sc fun rv11 rv10 hrv11 hrv10 => ?_
      have hbody : ∀ {mv : List Directive},
          _root_.Program.wp mv (fun s3 => s3.regs.get64 .rcx = s.regs.get64 rc ∧
            s3 = { s with regs := ((s.regs.set64 .r11 rv11).set64 .r10 rv10).set64 .rcx (s.regs.get64 rc) }) E
            { s with regs := (s.regs.set64 .r11 rv11).set64 .r10 rv10 } →
          _root_.Program.wp (mv ++ [insW w (if isRight then .shrd (.reg (regW w .r11)) (regW w .r10) .cl
            else .shld (.reg (regW w .r11)) (regW w .r10) .cl), movW w .rcx .r11])
            (OpPost1 (.bits w.bits) .rcx (if isRight then ((va ++ vb) >>> (vc.toNat % w.bits)).extractLsb' 0 w.bits
              else ((va ++ vb) <<< (vc.toNat % w.bits)).extractLsb' w.bits w.bits) maskAll s) E { s with regs := (s.regs.set64 .r11 rv11).set64 .r10 rv10 } := by
        intro mv hmv; refine Program.wp.append hmv ?_; rintro s3 ⟨_, rfl⟩
        refine tail_wp (restoreRcx := false) hrv11 hrv10
          (by rw [Reg64s.get64_set64_of_ne _ .rcx .r11 _ (by decide), Reg64s.get64_set64_of_ne _ .r10 .r11 _ (by decide), Reg64s.get64_set64_same])
          (by rw [Reg64s.get64_set64_of_ne _ .rcx .r10 _ (by decide), Reg64s.get64_set64_same]) rfl rfl (fun p => hrc_mod' _ (by rw [Reg64s.get64_set64_same]) p) rfl ?_
        intro r hr hsc; have hne := ne_of_not_mem_x64Scratch hsc
        simp [Reg64s.get64_set64_of_ne _ .rcx r _ hr.symm, Reg64s.get64_set64_of_ne _ .r10 r _ hne.1.symm, Reg64s.get64_set64_of_ne _ .r11 r _ hne.2.symm]
      change _root_.Program.wp (_ ++ _) _ E _; refine hbody ?_
      by_cases hrc : rc == .rcx
      · have hrc_eq := (beq_reg64_iff rc .rcx).1 hrc; subst hrc_eq; simp only [hrc, ↓reduceIte]
        exact _root_.Program.wp_nil ⟨by rw [Reg64s.get64_set64_of_ne _ .r10 .rcx _ (by decide), Reg64s.get64_set64_of_ne _ .r11 .rcx _ (by decide)], by congr 1⟩
      · simp only [hrc, Bool.false_eq_true, ↓reduceIte]
        refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movD _ .rcx rc)) ?_; rintro s3 rfl
        exact ⟨by rw [Reg64s.get64_set64_same, Reg64s.get64_set64_of_ne _ .r10 rc _ hrc_sc.1.symm, Reg64s.get64_set64_of_ne _ .r11 rc _ hrc_sc.2.symm],
          by rw [Reg64s.get64_set64_of_ne _ .r10 rc _ hrc_sc.1.symm, Reg64s.get64_set64_of_ne _ .r11 rc _ hrc_sc.2.symm]⟩
    · have hrd_ne_c : rd ≠ .rcx := fun h => hrcx ((beq_reg64_iff rd .rcx).2 h)
      by_cases hrcd : rc == rd
      · have hrc_eq : rc = rd := (beq_reg64_iff rc rd).1 hrcd; subst hrc_eq
        simp only [hrcx, Bool.false_eq_true, ↓reduceIte, hrcd, Option.some.injEq, Prod.mk.injEq] at h2; rcases h2 with ⟨rfl, rfl⟩
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
        have hrc_ne_rd : rc ≠ rd := fun h => hrcd ((beq_reg64_iff rc rd).2 h)
        refine wp_argPair11_10 w s hd1 hd2 hd_h hs_h hs_sc fun rv11 rv10 hrv11 hrv10 => ?_
        refine Program.wp.cons (Directive.FallsTo.wp (fallsTo_movD _ rd .rcx)) ?_; rintro s3 rfl
        have hbody : ∀ {mv : List Directive},
            _root_.Program.wp mv (· = { s with regs := ((((s.regs.set64 .r11 rv11).set64 .r10 rv10).set64 rd (s.regs.get64 .rcx)).set64 .rcx (s.regs.get64 rc)) }) E
              { s with regs := ((s.regs.set64 .r11 rv11).set64 .r10 rv10).set64 rd (s.regs.get64 .rcx) } →
            _root_.Program.wp (mv ++ [insW w (if isRight then .shrd (.reg (regW w .r11)) (regW w .r10) .cl
              else .shld (.reg (regW w .r11)) (regW w .r10) .cl), movD .rcx rd, movW w rd .r11])
              (OpPost1 (.bits w.bits) rd (if isRight then ((va ++ vb) >>> (vc.toNat % w.bits)).extractLsb' 0 w.bits
                else ((va ++ vb) <<< (vc.toNat % w.bits)).extractLsb' w.bits w.bits) maskAll s) E
              { s with regs := ((s.regs.set64 .r11 rv11).set64 .r10 rv10).set64 rd (s.regs.get64 .rcx) } := by
          intro mv hmv; refine Program.wp.append hmv ?_; rintro s4 rfl
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
        dsimp only; change _root_.Program.wp (_ ++ _) _ E _; refine hbody ?_
        have hgc : ((s.regs.set64 .r11 rv11).set64 .r10 rv10).get64 .rcx = s.regs.get64 .rcx := by
          rw [Reg64s.get64_set64_of_ne _ .r10 .rcx _ (by decide), Reg64s.get64_set64_of_ne _ .r11 .rcx _ (by decide)]
        by_cases hrc : rc == .rcx
        · have hrc_eq := (beq_reg64_iff rc .rcx).1 hrc; subst hrc_eq; simp only [hrc, ↓reduceIte]
          refine _root_.Program.wp_nil ?_; congr 1; refine reg64s_ext fun r => ?_; by_cases hr : r = .rcx
          · subst hr; rw [Reg64s.get64_set64_same, Reg64s.get64_set64_of_ne _ rd .rcx _ hrd_ne_c, hgc]
          · rw [Reg64s.get64_set64_of_ne _ .rcx r _ (Ne.symm hr)]
        · simp only [hrc, Bool.false_eq_true, ↓reduceIte]
          refine Program.wp.mono (Directive.FallsTo.wp (fallsTo_movD _ .rcx rc)) ?_; rintro s4 rfl
          rw [Reg64s.get64_set64_of_ne _ rd rc _ (Ne.symm hrc_ne_rd), Reg64s.get64_set64_of_ne _ .r10 rc _ hrc_sc.1.symm,
            Reg64s.get64_set64_of_ne _ .r11 rc _ hrc_sc.2.symm]

/-! ## 6. Remaining `NoLab` Lemmas and `x64Gpr_op_noLab` -/

theorem opDiv_allInstr {w : Width} {isSigned isRem : Bool}
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64} {c : List Directive} {clob : FlagMask}
    (h : opDiv w isSigned isRem pa pb rd = some (c, clob)) : AllInstr c := by
  unfold opDiv at h; split at h; · contradiction
  simp only [Option.bind_eq_bind] at h
  rcases Option.bind_eq_some_iff.mp h with ⟨da, hda, h1⟩; rcases Option.bind_eq_some_iff.mp h1 with ⟨db, hdb, h2⟩
  have ea : ∃ i, da = .instr i := by cases pa with | vec _ => cases w <;> simp at hda | imm _ => simp only [Option.some.injEq] at hda; subst hda; simp | gpr _ => cases w <;> simp only [Option.some.injEq] at hda <;> subst hda <;> simp
  have eb : ∃ i, db = .instr i := by cases pb with | vec _ => cases w <;> simp at hdb | imm _ => simp only [Option.some.injEq] at hdb; subst hdb; simp | gpr _ => cases w <;> simp only [Option.some.injEq] at hdb <;> subst hdb <;> simp
  obtain ⟨_, ea⟩ := ea; obtain ⟨_, eb⟩ := eb
  cases w <;> cases isSigned <;> simp only [Option.some.injEq, Prod.mk.injEq] at h2 <;>
    rcases h2 with ⟨rfl, -⟩ <;> repeat' (first | (simp [ea, eb]; done) | split)

theorem opAddc_allInstr {w : Width} {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)}
    {pc : PArg Reg64 RegMm CondCode .bool} {dsum : PDst Reg64 RegMm CondCode (.bits w.bits)}
    {dc : PDst Reg64 RegMm CondCode .bool} {vh : VariantHint} {c : List Directive} {clob : FlagMask}
    (h : opAddc w pa pb pc dsum dc vh = some (c, clob)) : AllInstr c := by
  cases dsum with
  | vec _ => simp [opAddc] at h
  | gpr rd =>
    unfold opAddc at h; dsimp +zetaHave only at h
    cases dc with
    | vec _ =>
      dsimp only at h; cases vh <;> cases pc <;> (try cases ‹Bool›) <;> (try cases ‹CondCode›) <;>
        simp only [Option.bind_eq_bind, Option.bind_some, Option.bind_none] at h <;> (try cases h) <;>
        (rcases Option.bind_eq_some_iff.mp h with ⟨_, _, h2⟩; cases h2)
    | flag cc =>
      dsimp only at h; cases vh <;> cases pc <;> (try cases ‹Bool›) <;> (try cases ‹CondCode›) <;>
        simp only [Option.bind_eq_bind, Option.bind_some, Option.bind_none] at h <;> (try cases h) <;>
        (rcases Option.bind_eq_some_iff.mp h with ⟨cr, hcr, h2⟩
         first
         | (cases h2; done)
         | ((try (split at h2 <;> simp only [Option.bind_some, Option.bind_none] at h2))
            all_goals first
              | (cases h2; done)
              | (simp only [Option.some.injEq, Prod.mk.injEq] at h2; rcases h2 with ⟨rfl, -⟩
                 simp [allInstr_carryCore (fun _ _ => isInstr_insW ..) (fun _ _ => isInstr_insW ..) hcr])))
    | gpr rc =>
      dsimp only at h; split at h; · cases ‹_›
      cases vh <;> cases pc <;> (try cases ‹Bool›) <;> (try cases ‹CondCode›) <;>
        simp only [Option.bind_eq_bind, Option.bind_some, Option.bind_none] at h <;> (try cases h) <;>
        (rcases Option.bind_eq_some_iff.mp h with ⟨cr, hcr, h2⟩
         simp only [Option.some.injEq, Prod.mk.injEq] at h2; rcases h2 with ⟨rfl, -⟩
         simp [allInstr_carryCore (fun _ _ => isInstr_insW ..) (fun _ _ => isInstr_insW ..) hcr])

theorem opSubb_allInstr {w : Width} {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)}
    {pc : PArg Reg64 RegMm CondCode .bool} {ddiff : PDst Reg64 RegMm CondCode (.bits w.bits)}
    {db : PDst Reg64 RegMm CondCode .bool} {c : List Directive} {clob : FlagMask}
    (h : opSubb w pa pb pc ddiff db = some (c, clob)) : AllInstr c := by
  cases ddiff with
  | vec _ => simp [opSubb] at h
  | gpr rd =>
    unfold opSubb at h; dsimp +zetaHave only at h
    cases db with
    | vec _ =>
      dsimp only at h; cases pc <;> (try cases ‹Bool›) <;> (try cases ‹CondCode›) <;>
        simp only [Option.bind_eq_bind, Option.bind_some, Option.bind_none] at h <;> (try cases h) <;>
        (rcases Option.bind_eq_some_iff.mp h with ⟨_, _, h2⟩; cases h2)
    | flag cc =>
      dsimp only at h; cases cc <;> cases pc <;> (try cases ‹Bool›) <;> (try cases ‹CondCode›) <;>
        simp only [Option.bind_eq_bind, Option.bind_some, Option.bind_none] at h <;> (try cases h) <;>
        (rcases Option.bind_eq_some_iff.mp h with ⟨cr, hcr, h2⟩
         first
         | (cases h2; done)
         | (simp only [Option.some.injEq, Prod.mk.injEq] at h2; rcases h2 with ⟨rfl, -⟩
            simp [allInstr_carryCore (fun _ _ => isInstr_insW ..) (fun _ _ => isInstr_insW ..) hcr]))
    | gpr rb =>
      dsimp only at h; split at h; · cases ‹_›
      cases pc <;> (try cases ‹Bool›) <;> (try cases ‹CondCode›) <;>
        simp only [Option.bind_eq_bind, Option.bind_some, Option.bind_none] at h <;> (try cases h) <;>
        (rcases Option.bind_eq_some_iff.mp h with ⟨cr, hcr, h2⟩
         simp only [Option.some.injEq, Prod.mk.injEq] at h2; rcases h2 with ⟨rfl, -⟩
         simp [allInstr_carryCore (fun _ _ => isInstr_insW ..) (fun _ _ => isInstr_insW ..) hcr])

theorem opMulw_allInstr {w : Width} {isSigned : Bool} {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)}
    {dlo dhi : PDst Reg64 RegMm CondCode (.bits w.bits)} {vh : VariantHint} {c : List Directive} {clob : FlagMask}
    (h : opMulw w isSigned pa pb dlo dhi vh = some (c, clob)) : AllInstr c := by
  cases dlo <;> cases dhi <;> simp only [opMulw, reduceCtorEq] at h; rename_i rlo rhi
  split at h; · contradiction
  split at h
  · simp only [Option.bind_eq_bind] at h; rcases Option.bind_eq_some_iff.mp h with ⟨da, hda, h1⟩
    obtain ⟨_, ea⟩ := isInstr_argToBits hda
    cases pb with
    | vec _ => simp [argToBits] at h1
    | imm c0 => simp only [argToBits, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h1; rcases h1 with ⟨rfl, -⟩; simp [ea]
    | gpr r => cases r <;> simp only [argToBits, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h1 <;> rcases h1 with ⟨rfl, -⟩ <;> simp [ea]
  · simp only [Option.bind_eq_bind] at h
    rcases Option.bind_eq_some_iff.mp h with ⟨da, hda, h1⟩; rcases Option.bind_eq_some_iff.mp h1 with ⟨db, hdb, h2⟩
    obtain ⟨_, ea⟩ := isInstr_argToBits hda; obtain ⟨_, eb⟩ := isInstr_argToBits hdb
    simp only [Option.some.injEq, Prod.mk.injEq] at h2; rcases h2 with ⟨rfl, -⟩
    repeat' (first | (simp [ea, eb]; done) | split)

theorem x64Op_allInstr {sig rs : List Ty} {code : OpCode sig rs}
    {pas : Tup (PArg Reg64 RegMm CondCode) sig} {dsts : Tup (PDst Reg64 RegMm CondCode) rs}
    {vh : VariantHint} {c : List Directive} {clob : FlagMask}
    (h : x64Gpr.op code pas dsts vh = some (c, clob)) : AllInstr c := by
  change x64Op code pas dsts vh = some (c, clob) at h
  cases code with
  | copy t =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t <;> dsimp only [x64Op] at h <;> try exact absurd h (by intro h1; cases h1)
    · exact opCopyBool_allInstr h
    · (cases pd <;> try exact absurd h (by intro h1; cases h1)); exact withWidth_elim h fun _ _ hw => opCopyBits_allInstr hw
  | add t | sub t | mul t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t <;> try exact absurd h (by intro h1; cases h1)
    (cases pd <;> try exact absurd h (by intro h1; cases h1)); dsimp only [x64Op] at h
    exact withWidth_elim h fun _ _ hw => opBin_allInstr hw
  | and t | or t | xor t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t <;> dsimp only [x64Op] at h <;> try exact absurd h (by intro h1; cases h1)
    · exact opBoolBin_allInstr h
    · (cases pd <;> try exact absurd h (by intro h1; cases h1)); exact withWidth_elim h fun _ _ hw => opBin_allInstr hw
  | neg t =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t <;> try exact absurd h (by intro h1; cases h1)
    (cases pd <;> try exact absurd h (by intro h1; cases h1)); dsimp only [x64Op] at h
    exact withWidth_elim h fun _ _ hw => opNeg_allInstr hw
  | not t =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t <;> dsimp only [x64Op] at h <;> try exact absurd h (by intro h1; cases h1)
    · exact opBoolNot_allInstr h
    · (cases pd <;> try exact absurd h (by intro h1; cases h1)); exact withWidth_elim h fun _ _ hw => opNot_allInstr hw
  | shl t | lshr t | ashr t | rotl t | rotr t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t <;> try exact absurd h (by intro h1; cases h1)
    (cases pd <;> try exact absurd h (by intro h1; cases h1)); dsimp only [x64Op] at h
    exact withWidth_elim h fun _ _ hw => opShift_allInstr hw
  | fshl n | fshr n =>
    rcases pas with ⟨pa, pb, pc, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    (cases pd <;> try exact absurd h (by intro h1; cases h1)); dsimp only [x64Op] at h
    exact withWideWidth_elim h fun _ _ hw => opFunnel_allInstr hw
  | bswap t =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t <;> try exact absurd h (by intro h1; cases h1)
    (cases pd <;> try exact absurd h (by intro h1; cases h1)); dsimp only [x64Op] at h
    exact opBswap_allInstr h
  | cmp co t m hm =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t <;> try exact absurd h (by intro h1; cases h1)
    dsimp only [x64Op] at h; exact withWidth_elim h fun _ _ hw => opCmp_allInstr hw
  | select t =>
    rcases pas with ⟨pc, pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t <;> try exact absurd h (by intro h1; cases h1)
    (cases pd <;> try exact absurd h (by intro h1; cases h1)); dsimp only [x64Op] at h
    exact withWidth_elim h fun _ _ hw => opSelect_allInstr hw
  | zext m n => rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; (cases pd <;> try exact absurd h (by intro h1; cases h1)); dsimp only [x64Op] at h; exact opZext_allInstr h
  | sext m n => rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; (cases pd <;> try exact absurd h (by intro h1; cases h1)); dsimp only [x64Op] at h; exact opSext_allInstr h
  | trunc m n => rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; (cases pd <;> try exact absurd h (by intro h1; cases h1)); dsimp only [x64Op] at h; exact opTrunc_allInstr h
  | ofBool n => rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩; (cases pd <;> try exact absurd h (by intro h1; cases h1)); dsimp only [x64Op] at h; split at h <;> first | exact opOfBool_allInstr h | cases h
  | addc n => rcases pas with ⟨pa, pb, pc, ⟨⟩⟩; rcases dsts with ⟨dsum, dc, ⟨⟩⟩; dsimp only [x64Op] at h; exact withWideWidth_elim h fun _ _ hw => opAddc_allInstr hw
  | subb n => rcases pas with ⟨pa, pb, pc, ⟨⟩⟩; rcases dsts with ⟨ddiff, db, ⟨⟩⟩; dsimp only [x64Op] at h; exact withWideWidth_elim h fun _ _ hw => opSubb_allInstr hw
  | umulw n | smulw n => rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨dlo, dhi, ⟨⟩⟩; dsimp only [x64Op] at h; exact withWideWidth_elim h fun _ _ hw => opMulw_allInstr hw
  | udiv n | sdiv n | urem n | srem n =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    (cases pd <;> try exact absurd h (by intro h1; cases h1)); dsimp only [x64Op] at h; exact withWidth_elim h fun _ _ hw => opDiv_allInstr hw
  | bitcast t u _ =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t <;> cases u <;> try exact absurd h (by intro h1; cases h1)
    (cases pd <;> try exact absurd h (by intro h1; cases h1)); dsimp only [x64Op] at h
    split at h <;> first | exact withWidth_elim h fun _ _ hw => opCopyBits_allInstr hw | cases h
  | ternlog _ _ | clz _ | cls _ | rbit _ | ctz _ | popcnt _ | blend _ _ _ | udiv0 _ | sdiv0 _
  | mkpair _ _ | unpair _ _ | shufd _ _ | shufb _ | alignr _ _ | blendw _ _
  | sha256rnds2 | sha256msg1 | sha256msg2
  | fadd _ | fsub _ | fmul _ | fdiv _ | ffma _ | fsqrt _ | fneg _ | fabs _ | fcmp _ _ _ _
  | fptoui _ _ | fptosi _ _ | uitofp _ _ | sitofp _ _ | fcvt _ _ =>
    cases pas; cases dsts; exact absurd h (by intro h1; cases h1)

theorem x64Gpr_op_noLab {sig rs : List Ty} {code : OpCode sig rs}
    {pas : Tup (PArg Reg64 RegMm CondCode) sig} {dsts : Tup (PDst Reg64 RegMm CondCode) rs}
    {vh : VariantHint} {c : List Directive} {clob : FlagMask}
    (h : x64Gpr.op code pas dsts vh = some (c, clob)) : ∀ l, Kraken.Directive.label l ∉ c :=
  (x64Op_allInstr h).noLabel

end LeanQbe.T.Amd64