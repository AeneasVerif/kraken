module

public import LeanQbe.T.Arm64.Isel
public import LeanQbe.T.Arm64.IselLemmas31
import LeanQbe.T.Arm64.IselLemmas30
import Kraken.AArch64.Parser

/-!
# AArch64 Wave 6.2-B `CCMP`/`CCMN` & `CSNEG` Proofs + `ParserChecks` (`Arm64.IselCcmpLemmas`)

Weakest-precondition specifications and label-cleanliness theorems for `armCcmp` and
`armSelectNeg`, plus kernel `rfl` `ParserChecks` against `Kraken.AArch64.Parser`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Arm64

open LeanQbe.T

/-! ## 1. `armNzcvTrue` / `armNzcvFalse` and `armCcmp` specification -/

theorem armNzcvTrue_interp (c : ArmCond) :
    c.interp (StatusFlags.ofNat (armNzcvTrue c)) = true := by
  cases c <;> decide

theorem armNzcvFalse_interp (c : ArmCond) :
    c.interp (StatusFlags.ofNat (armNzcvFalse c)) = false := by
  cases c <;> decide

private theorem armCcmpDir_wp [Host] {n : Nat} (hn : n = 32 ∨ n = 64)
    (prevCond : ArmCond) (isOr : Bool) (co : CmpOp)
    (rx : XReg) (pb : PArg Reg Empty ArmCond (.bits n))
    {vx vb : BitVec n} {ins_ : Instr} {s : MachineData}
    (hrx : (s.regs.getXReg rx).toBitVec.setWidth n = vx)
    (hpb : armMach.PArgHolds s (.bits n) pb vb)
    (hi : (let w := armWidthOf n
           let ccExec := if isOr then armNegCond prevCond else prevCond
           let dstCond := armCmpCond co
           let nzcv := if isOr then armNzcvTrue dstCond else armNzcvFalse dstCond
           match pb with
           | .gpr (.reg rb) =>
             some (armIselInsI (.CCMP_reg (zr rx w) (zr rb w) nzcv ccExec.toKraken))
           | .imm cb => armCcmpImm5? w rx cb nzcv ccExec
           | _ => none) = some ins_) :
    _root_.Program.wp [Kraken.Directive.instr ins_]
      (fun s' =>
        (armCmpCond co).interp s'.status =
          (if isOr then prevCond.interp s.status || co.evalBits vx vb
           else prevCond.interp s.status && co.evalBits vx vb) ∧
        s'.dmem = s.dmem ∧
        armMach.Frame armCondReads s s' armScratch [] maskNZCV)
      (fun _ _ => False) s := by
  let dstCond := armCmpCond co
  let ccExec := if isOr then armNegCond prevCond else prevCond
  let nzcv := if isOr then armNzcvTrue dstCond else armNzcvFalse dstCond
  have hexec : ccExec.interp s.status =
      if isOr then !prevCond.interp s.status else prevCond.interp s.status := by
    cases isOr <;> simp [ccExec, armNegCond_interp]
  have hsubs_eval :
      dstCond.interp (StatusFlags.subs (vx - vb) vx vb) = co.evalBits vx vb :=
    armCmpCond_subs hn co vx vb
  have hfinish : ∀ {st : StatusFlags},
      st = (if ccExec.interp s.status then StatusFlags.subs (vx - vb) vx vb
            else StatusFlags.ofNat nzcv) →
      dstCond.interp st =
        (if isOr then prevCond.interp s.status || co.evalBits vx vb
         else prevCond.interp s.status && co.evalBits vx vb) := by
    intro st hst; subst hst; rw [hexec]
    cases isOr <;> cases hprev : prevCond.interp s.status <;>
      simp [dstCond, nzcv, armNzcvTrue_interp, armNzcvFalse_interp] <;>
      exact hsubs_eval
  have hrz : ∀ (w : RegWidth) (r : XReg) {vr : BitVec n}, (hwb : w.bits = n) →
      (s.regs.getXReg r).toBitVec.setWidth n = vr →
      (s.regs.getRegOrZr (.low (.reg r) w)).setWidth n = vr := by
    intro w r vr hwb hr
    cases w <;> cases hwb <;>
      (simp only [Reg64s.getRegOrZr, Reg64s.getRegOrZr64, RegOrZr.base, BitVec.take,
         RegWidth.bits, BitVec.setWidth_eq]
       rw [← hr]; apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi])
  rcases hn with rfl | rfl
  · have hw : armWidthOf 32 = .W32 := rfl
    have hrxw : s.regs.getRegOrZr (.low (.reg rx) .W32) = vx := by
      simpa [BitVec.setWidth_eq] using hrz .W32 rx rfl hrx
    rw [hw] at hi
    cases pb with
    | vec v => exact v.elim
    | gpr r => cases r with
      | SP => simp at hi
      | reg rb =>
        simp only [Option.some.injEq] at hi; subst hi
        have hrb : (s.regs.getXReg rb).toBitVec.setWidth 32 = vb := by
          simpa [Machine.PArgHolds, GprHolds, get_reg] using hpb.2
        have hrbw : s.regs.getRegOrZr (.low (.reg rb) .W32) = vb := by
          simpa [BitVec.setWidth_eq] using hrz .W32 rb rfl hrb
        refine armWp_mono (armDirFallsTo_wp (Q := fun s' => s' = { s with
            status := if ccExec.interp s.status then StatusFlags.subs (vx - vb) vx vb
                      else StatusFlags.ofNat nzcv })
          fun {_} p next jmp Q hk => by
            simp only [t_step_simp, hrxw, hrbw]; exact hk _ rfl)
          (fun s' hs' => by subst hs'; exact ⟨hfinish rfl, rfl, armFrame_nzcv fun _ _ => rfl⟩)
    | imm cb =>
      have hcb : cb = vb := hpb
      dsimp only [armCcmpImm5?] at hi
      by_cases hlt : Nat.blt cb.toNat 32 = true
      · simp only [hlt, ↓reduceIte, Option.some.injEq] at hi; subst hi
        refine armWp_mono (armDirFallsTo_wp (Q := fun s' => s' = { s with
            status := if ccExec.interp s.status then StatusFlags.subs (vx - vb) vx vb
                      else StatusFlags.ofNat nzcv })
          fun {_} p next jmp Q hk => by
            simp only [t_step_simp, RegWidth.bits, MemWidth.bits, hrxw,
              BitVec.ofNat_toNat, BitVec.setWidth_eq, hcb]; exact hk _ rfl)
          (fun s' hs' => by subst hs'; exact ⟨hfinish rfl, rfl, armFrame_nzcv fun _ _ => rfl⟩)
      · simp only [hlt, Bool.false_eq_true, ↓reduceIte] at hi
        by_cases hand : (cb != 0#32 && Nat.blt (-cb).toNat 32) = true
        · simp only [hand, ↓reduceIte, Option.some.injEq] at hi; subst hi
          simp only [Bool.and_eq_true, bne_iff_ne, Nat.blt_eq] at hand
          have hlt2 : (-cb).toNat < 16777216 := Nat.lt_trans hand.2 (by decide)
          have hncb0 : -cb ≠ 0#32 := fun h => hand.1 (by simpa using congrArg (- ·) h)
          have hadds : StatusFlags.adds (vx + (-vb)) vx (-vb) =
              StatusFlags.subs (vx - vb) vx vb := by
            rw [adds_eq_subs_neg (by decide : 32 ≤ 32) vx (-vb) (hcb ▸ hncb0) (hcb ▸ hlt2),
              BitVec.neg_neg]
          refine armWp_mono (armDirFallsTo_wp (Q := fun s' => s' = { s with
              status := if ccExec.interp s.status then StatusFlags.subs (vx - vb) vx vb
                        else StatusFlags.ofNat nzcv })
            fun {_} p next jmp Q hk => by
              simp only [t_step_simp, RegWidth.bits, MemWidth.bits, hrxw,
                BitVec.ofNat_toNat, BitVec.setWidth_eq, hcb, hadds]; exact hk _ rfl)
            (fun s' hs' => by subst hs'; exact ⟨hfinish rfl, rfl, armFrame_nzcv fun _ _ => rfl⟩)
        · simp only [hand, Bool.false_eq_true, ↓reduceIte] at hi; cases hi
  · have hw : armWidthOf 64 = .W64 := rfl
    have hrxw : s.regs.getRegOrZr (.low (.reg rx) .W64) = vx := by
      simpa [BitVec.setWidth_eq] using hrz .W64 rx rfl hrx
    rw [hw] at hi
    cases pb with
    | vec v => exact v.elim
    | gpr r => cases r with
      | SP => simp at hi
      | reg rb =>
        simp only [Option.some.injEq] at hi; subst hi
        have hrb : (s.regs.getXReg rb).toBitVec.setWidth 64 = vb := by
          simpa [Machine.PArgHolds, GprHolds, get_reg] using hpb.2
        have hrbw : s.regs.getRegOrZr (.low (.reg rb) .W64) = vb := by
          simpa [BitVec.setWidth_eq] using hrz .W64 rb rfl hrb
        refine armWp_mono (armDirFallsTo_wp (Q := fun s' => s' = { s with
            status := if ccExec.interp s.status then StatusFlags.subs (vx - vb) vx vb
                      else StatusFlags.ofNat nzcv })
          fun {_} p next jmp Q hk => by
            simp only [t_step_simp, hrxw, hrbw]; exact hk _ rfl)
          (fun s' hs' => by subst hs'; exact ⟨hfinish rfl, rfl, armFrame_nzcv fun _ _ => rfl⟩)
    | imm cb =>
      have hcb : cb = vb := hpb
      dsimp only [armCcmpImm5?] at hi
      by_cases hlt : Nat.blt cb.toNat 32 = true
      · simp only [hlt, ↓reduceIte, Option.some.injEq] at hi; subst hi
        refine armWp_mono (armDirFallsTo_wp (Q := fun s' => s' = { s with
            status := if ccExec.interp s.status then StatusFlags.subs (vx - vb) vx vb
                      else StatusFlags.ofNat nzcv })
          fun {_} p next jmp Q hk => by
            simp only [t_step_simp, RegWidth.bits, MemWidth.bits, hrxw,
              BitVec.ofNat_toNat, BitVec.setWidth_eq, hcb]; exact hk _ rfl)
          (fun s' hs' => by subst hs'; exact ⟨hfinish rfl, rfl, armFrame_nzcv fun _ _ => rfl⟩)
      · simp only [hlt, Bool.false_eq_true, ↓reduceIte] at hi
        by_cases hand : (cb != 0#64 && Nat.blt (-cb).toNat 32) = true
        · simp only [hand, ↓reduceIte, Option.some.injEq] at hi; subst hi
          simp only [Bool.and_eq_true, bne_iff_ne, Nat.blt_eq] at hand
          have hlt2 : (-cb).toNat < 16777216 := Nat.lt_trans hand.2 (by decide)
          have hncb0 : -cb ≠ 0#64 := fun h => hand.1 (by simpa using congrArg (- ·) h)
          have hadds : StatusFlags.adds (vx + (-vb)) vx (-vb) =
              StatusFlags.subs (vx - vb) vx vb := by
            rw [adds_eq_subs_neg (by decide : 32 ≤ 64) vx (-vb) (hcb ▸ hncb0) (hcb ▸ hlt2),
              BitVec.neg_neg]
          refine armWp_mono (armDirFallsTo_wp (Q := fun s' => s' = { s with
              status := if ccExec.interp s.status then StatusFlags.subs (vx - vb) vx vb
                        else StatusFlags.ofNat nzcv })
            fun {_} p next jmp Q hk => by
              simp only [t_step_simp, RegWidth.bits, MemWidth.bits, hrxw,
                BitVec.ofNat_toNat, BitVec.setWidth_eq, hcb, hadds]; exact hk _ rfl)
            (fun s' hs' => by subst hs'; exact ⟨hfinish rfl, rfl, armFrame_nzcv fun _ _ => rfl⟩)
        · simp only [hand, Bool.false_eq_true, ↓reduceIte] at hi; cases hi

theorem armCcmp_spec {h : Host} {k : Nat}
    {prevCond : ArmCond} {isOr : Bool} {co : CmpOp} {n : Nat}
    {pa pb : PArg Reg Empty ArmCond (.bits n)} {dstCond : ArmCond}
    {c : List Directive} {clob : FlagMask} {va vb : BitVec n} {s : MachineData}
    {post : MachineState → Prop}
    (hc_in : armCcmp prevCond isOr co n pa pb = some (dstCond, c, clob))
    (hpa : armMach.PArgHolds s (.bits n) pa va)
    (hpb : armMach.PArgHolds s (.bits n) pb vb) :
    armMach.FallsTo armCondReads h k c armScratch [] clob s
      (fun s' =>
        armMach.evalCond s' dstCond =
          (if isOr then armMach.evalCond s prevCond || co.evalBits va vb
           else armMach.evalCond s prevCond && co.evalBits va vb) ∧
        armMach.mem s' = armMach.mem s) post := by
  letI := h
  rw [armCcmp, Option.map_eq_some_iff] at hc_in
  rcases hc_in with ⟨⟨dst', ci, cl'⟩, hci, hprod⟩
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨rfl, rfl⟩
  dsimp only [armCcmpIns] at hci
  split at hci
  · cases hci
  · rename_i hn3264
    have hn : n = 32 ∨ n = 64 := by
      have h1 := not_not_eq_true hn3264
      simp only [Bool.or_eq_true, beq_iff_eq] at h1; exact h1
    cases pa with
    | vec v => exact v.elim
    | gpr r1 => cases r1 with
      | SP => cases pb <;> simp at hci
      | reg ra =>
        have hra : (s.regs.getXReg ra).toBitVec.setWidth n = va := by
          simpa [Machine.PArgHolds, GprHolds, get_reg] using hpa.2
        cases pb with
        | vec v => exact v.elim
        | gpr r2 => cases r2 with
          | SP => simp at hci
          | reg rb =>
            rcases Option.some.inj hci with ⟨rfl, rfl, rfl⟩
            simp only [emitClean_cons, emitClean_nil]
            exact armFallsTo_of_wp (armWp_mono
              (armCcmpDir_wp hn prevCond isOr co ra (.gpr (.reg rb)) hra hpb rfl)
              fun _ ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩)
        | imm cb =>
          simp only [Option.map_eq_some_iff] at hci
          rcases hci with ⟨ins_, hi, hprod'⟩
          rcases Prod.mk.inj hprod' with ⟨rfl, hprod2'⟩
          rcases Prod.mk.inj hprod2' with ⟨rfl, rfl⟩
          simp only [emitClean_cons, emitClean_nil]
          exact armFallsTo_of_wp (armWp_mono
            (armCcmpDir_wp hn prevCond isOr co ra (.imm cb) hra hpb hi)
            fun _ ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩)
    | imm ca =>
      cases pb with
      | vec v => exact v.elim
      | imm _ => simp at hci
      | gpr r2 => cases r2 with
        | SP => simp at hci
        | reg rb =>
          have hrb : (s.regs.getXReg rb).toBitVec.setWidth n = vb := by
            simpa [Machine.PArgHolds, GprHolds, get_reg] using hpb.2
          simp only [Option.map_eq_some_iff] at hci
          rcases hci with ⟨ins_, hi, hprod'⟩
          rcases Prod.mk.inj hprod' with ⟨rfl, hprod2'⟩
          rcases Prod.mk.inj hprod2' with ⟨rfl, rfl⟩
          simp only [emitClean_cons, emitClean_nil]
          have hwp := armCcmpDir_wp hn prevCond isOr co.swap rb (.imm ca) hrb hpa hi
          rw [CmpOp.swap_evalBits] at hwp
          exact armFallsTo_of_wp (armWp_mono hwp fun _ ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩)

theorem armCcmp_noLab {prevCond : ArmCond} {isOr : Bool} {co : CmpOp} {n : Nat}
    {pa pb : PArg Reg Empty ArmCond (.bits n)} {dstCond : ArmCond}
    {c : List Directive} {clob : FlagMask}
    (hc : armCcmp prevCond isOr co n pa pb = some (dstCond, c, clob)) (lab : Sym) :
    Kraken.Directive.label lab ∉ c := by
  rw [armCcmp, Option.map_eq_some_iff] at hc
  rcases hc with ⟨⟨_, ci, _⟩, _, hprod⟩
  rcases Prod.mk.inj hprod with ⟨_, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨rfl, _⟩
  exact emitClean_noLab ci lab

/-! ## 2. `armSelectNeg` specification -/

private theorem armSelectNeg_wp [Host] {n : Nat}
    (pc : PArg Reg Empty ArmCond .bool) (rx : Reg) (negFirst : Bool) (rd : Reg)
    {vc : Bool} {vx : BitVec n} {c : List Instr} {clob : FlagMask} {s : MachineData}
    (hc : armSelectNegIns n pc rx negFirst rd = some (c, clob))
    (hpc : armMach.PArgHolds s .bool pc vc)
    (hrx : GprHolds (armMach.getGpr s rx) (.bits n) vx) :
    let res : BitVec n :=
      if vc then (if negFirst then -vx else vx) else (if negFirst then vx else -vx)
    _root_.Program.wp (emitClean c) (fun s' =>
      GprHoldsZ (armMach.getGpr s' rd) n res ∧
      armMach.mem s' = armMach.mem s ∧
      armMach.Frame armCondReads s s' (rd :: armScratch) [] clob) (fun _ _ => False) s := by
  dsimp only [armSelectNegIns] at hc; split at hc
  · simp at hc
  · rename_i hn; replace hn := not_not_eq_true hn
    simp only [List.contains_eq_mem, decide_eq_true_eq] at hn
    have hn64 := mem_armWidths_le_64 hn
    have hnw := mem_armWidths_le_armWidth hn
    cases rx with
    | SP => simp at hc
    | reg x =>
      cases rd with
      | SP => simp at hc
      | reg d =>
        simp only [Bind.bind, Option.bind] at hc
        have hx : (s.regs.getXReg x).toBitVec.setWidth n = vx := by
          simpa [GprHolds, armMach, get_reg] using hrx.2
        have hxs : s.regs.getRegOrZr (.low (.reg x) (armWidthOf n)) =
            (s.regs.getXReg x).toBitVec.setWidth (armWidthOf n).bits := by
          cases armWidthOf n <;>
            (simp only [Reg64s.getRegOrZr, Reg64s.getRegOrZr64, RegOrZr.base, BitVec.take]
             apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi])
        have hxw : (s.regs.getRegOrZr (.low (.reg x) (armWidthOf n))).setWidth n = vx := by
          rw [hxs, BitVec.setWidth_setWidth_of_le _ hnw, hx]
        have hx32 : s.regs.getRegOrZr (.low (.reg x) .W32) =
            (s.regs.getXReg x).toBitVec.setWidth 32 := by
          simp only [Reg64s.getRegOrZr, Reg64s.getRegOrZr64, RegOrZr.base, BitVec.take]
          apply BitVec.eq_of_getLsbD_eq; intro i hi; simp [hi]
        cases pc with
        | vec v => exact v.elim
        | imm b =>
          simp only [Machine.PArgHolds] at hpc; subst hpc
          dsimp only at hc
          by_cases hneg : (if b then negFirst else !negFirst) = true
          · simp only [hneg, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hc
            rcases hc with ⟨rfl, rfl⟩
            simp only [emitClean_cons, emitClean_nil]
            have hres : (if b then (if negFirst then -vx else vx)
                else (if negFirst then vx else -vx)) = -vx := by
              cases b <;> cases negFirst <;> simp_all
            rw [hres]
            exact armWrDst_of_eq hn64 d (armSubNegDir_wp (armWidthOf n) d x s)
              (by rw [BitVec.setWidth_setWidth_of_le _ hn64, setWidth_neg_le hnw,
                BitVec.setWidth_setWidth_of_le _ hnw, hx])
              (fun hn32 => by
                subst hn32; rw [show armWidthOf 32 = .W32 from rfl, RegWidth.bits, hx])
          · simp only [hneg, Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
              Prod.mk.injEq] at hc
            rcases hc with ⟨rfl, rfl⟩
            simp only [emitClean_cons, emitClean_nil]
            have hres : (if b then (if negFirst then -vx else vx)
                else (if negFirst then vx else -vx)) = vx := by
              cases b <;> cases negFirst <;> simp_all
            rw [hres]
            exact armWrDst_of_eq hn64 d (armMovRegDir_wp (armWidthOf n) d x s)
              (by rw [BitVec.setWidth_setWidth_of_le _ hn64, BitVec.setWidth_setWidth_of_le _ hnw,
                hx])
              (fun hn32 => by
                subst hn32; rw [show armWidthOf 32 = .W32 from rfl, RegWidth.bits, hx])
        | flag cond =>
          dsimp only at hc
          simp only [Option.some.injEq, Prod.mk.injEq] at hc
          rcases hc with ⟨rfl, rfl⟩
          simp only [emitClean_cons, emitClean_nil]
          simp only [Machine.PArgHolds] at hpc
          have hcnd : (if negFirst then armNegCond cond else cond).interp s.status =
              if negFirst then !vc else vc := by
            cases negFirst <;> simp [armNegCond_interp, hpc]
          refine armWrDst_of_eq hn64 d
            (armCsnegDir_wp (armWidthOf n) d (.reg x) (.reg x)
              (if negFirst then armNegCond cond else cond) s) ?_ ?_
          · rw [BitVec.setWidth_setWidth_of_le _ hn64, hcnd]
            cases negFirst <;> cases vc <;>
              simp only [↓reduceIte, Bool.false_eq_true, Bool.not_true, Bool.not_false] <;>
              first | rw [hxw] | rw [setWidth_neg_le hnw, hxw]
          · intro hn32; subst hn32
            rw [show armWidthOf 32 = .W32 from rfl, hcnd, hx32]
            cases negFirst <;> cases vc <;>
              simp only [↓reduceIte, Bool.false_eq_true, Bool.not_true, Bool.not_false] <;>
              first | rw [hx] | rw [setWidth_neg_le (by decide : 32 ≤ 32), BitVec.setWidth_eq, hx]
        | gpr rc => cases rc with
          | SP => simp at hc
          | reg rc =>
            dsimp only at hc
            simp only [Option.some.injEq, Prod.mk.injEq] at hc
            rcases hc with ⟨rfl, rfl⟩
            have hrc : (s.regs.getXReg rc).toBitVec.setWidth 8 = BitVec.ofNat 8 vc.toNat := by
              simpa [Machine.PArgHolds, GprHolds, get_reg] using hpc
            let st1 := StatusFlags.from_result
              ((s.regs.getXReg rc).toBitVec.setWidth 32 &&& 1#32) { c := false, v := false }
            rw [emitClean_cons]
            refine armWp_cons (armDirFallsTo_wp (Q := fun s' => s' = { s with status := st1 })
              fun {_} p next jmp Q hk => by
                simp only [t_step_simp, Reg64s.setRegOrZr_xzr, Int64.toInt_one, RegWidth.bits,
                  MemWidth.bits]
                exact hk _ rfl) ?_
            rintro s₁ rfl
            simp only [emitClean_cons, emitClean_nil]
            have hne1 : ArmCond.ne.interp st1 = vc := ne_of_tstBit0 hrc
            have hcnd : (if negFirst then armNegCond .ne else .ne).interp st1 =
                if negFirst then !vc else vc := by
              cases negFirst <;> simp [armNegCond_interp, hne1]
            refine armWp_mono (armCsnegDir_wp (armWidthOf n) d (.reg x) (.reg x)
                (if negFirst then armNegCond .ne else .ne) { s with status := st1 }) ?_
            rintro s₂ rfl
            refine ⟨⟨⟨hn64, ?_⟩, ?_⟩, rfl, armFrame_nzcv fun r hr => ?_⟩
            · simp only [get_wr_same, BitVec.setWidth_setWidth_of_le _ hn64, hcnd]
              cases negFirst <;> cases vc <;>
                simp only [↓reduceIte, Bool.false_eq_true, Bool.not_true, Bool.not_false] <;>
                first | exact hxw | (rw [setWidth_neg_le hnw, hxw])
            · intro hn32; subst hn32
              rw [show armWidthOf 32 = .W32 from rfl, get_wr_same, hcnd, hx32]
              cases negFirst <;> cases vc <;>
                simp only [↓reduceIte, Bool.false_eq_true, Bool.not_true, Bool.not_false] <;>
                rw [hx]
            · have hne : r ≠ .reg d := fun e => hr (e ▸ List.mem_cons_self)
              exact get_wr_of_ne { s with status := st1 } d _ r hne

theorem armSelectNeg_spec {h : Host} {k : Nat}
    {n : Nat} {pc : PArg Reg Empty ArmCond .bool} {rx : Reg} {negFirst : Bool} {rd : Reg}
    {c : List Directive} {clob : FlagMask} {vc : Bool} {vx : BitVec n} {s : MachineData}
    {post : MachineState → Prop}
    (hc_in : armSelectNeg n pc rx negFirst rd = some (c, clob))
    (hpc : armMach.PArgHolds s .bool pc vc)
    (hrx : GprHolds (armMach.getGpr s rx) (.bits n) vx) :
    let res : BitVec n :=
      if vc then (if negFirst then -vx else vx) else (if negFirst then vx else -vx)
    armMach.FallsTo armCondReads h k c (rd :: armScratch) [] clob s
      (fun s' => GprHolds (armMach.getGpr s' rd) (.bits n) res ∧
        (n = 32 → true = true → armMach.getGpr s' rd = res.setWidth 64) ∧
        armMach.mem s' = armMach.mem s) post := by
  letI := h
  obtain ⟨ci, hc, rfl⟩ := emitCleanPair_eq_some.mp hc_in
  exact armFallsTo_of_wp (armWp_mono (armSelectNeg_wp pc rx negFirst rd hc hpc hrx)
    fun _ ⟨⟨hg, hz⟩, hdm, hfr⟩ => ⟨⟨hg, fun hn32 _ => hz hn32, hdm⟩, hfr⟩)

theorem armSelectNeg_noLab {n : Nat} {pc : PArg Reg Empty ArmCond .bool} {rx : Reg}
    {negFirst : Bool} {rd : Reg} {c : List Directive} {clob : FlagMask}
    (hc : armSelectNeg n pc rx negFirst rd = some (c, clob)) (lab : Sym) :
    Kraken.Directive.label lab ∉ c := emitCleanPair_noLab hc lab

/-! ## 3. Kernel `rfl` `ParserChecks` against `Kraken.AArch64.Parser` -/

section ParserChecks
open Kraken.AArch64.Parser

theorem parser_moves_branches_rfl :
    ⸨prog|
      adds xzr, xzr, xzr
      mov x0, x1
      add sp, x0, #0
      csinc x0, xzr, xzr, ne
      mov x16, sp
      tbnz w16, #0, L_tgt
      tbz w0, #0, L_tgt
      b L_tgt
      b.eq L_tgt
    ⸩ =
      armGpr.clearFlags ++ armGpr.mov (.reg .X0) (.reg .X1) ++ armGpr.mov .SP (.reg .X0) ++
        armGpr.setcc (.reg .X0) .eq ++ (armGpr.jnzGpr .SP "L_tgt").1 ++
        (armJnzGprInv (.reg .X0) true "L_tgt").1 ++
        armGpr.jmp "L_tgt" ++ armGpr.jcc .eq "L_tgt" := rfl

theorem parser_mem_sp_flag_rfl :
    ⸨prog|
      add x16, sp, #8
      ldr x0, [x16]
      csinc x17, xzr, xzr, ne
      add x16, sp, #16
      strb w17, [x16]
    ⸩ =
      (armGpr.load i64 (.reg .X0) (.baseDisp .SP 8)).elim [] Prod.fst ++
      (armGpr.store .bool (.flag .eq) (.baseDisp .SP 16)).elim [] Prod.fst := rfl

theorem parser_ops_rfl :
    ⸨prog|
      sdiv w0, w1, w2
      udiv w17, w1, w2
      msub w0, w17, w2, w1
      rev16 w0, w1
      rbit x0, x1
      clz x0, x0
      ands wzr, w3, #1
      csel x0, x1, x2, ne
      adcs x0, x1, x2
      csinc x4, xzr, xzr, cc
      sbcs w0, w1, w2
      smaddl x0, w1, w2, xzr
      ubfm x3, x0, #32, #63
      extr x0, x1, x2, #7
    ⸩ =
      (armGpr.op (.sdiv0 32) (.gpr (.reg .X1), .gpr (.reg .X2), ())
        (.gpr (.reg .X0), ()) .default).elim [] Prod.fst ++
      (armGpr.op (.urem 32) (.gpr (.reg .X1), .gpr (.reg .X2), ())
        (.gpr (.reg .X0), ()) .default).elim [] Prod.fst ++
      (armGpr.op (.bswap i16) (.gpr (.reg .X1), ())
        (.gpr (.reg .X0), ()) .default).elim [] Prod.fst ++
      (armGpr.op (.ctz 64) (.gpr (.reg .X1), ()) (.gpr (.reg .X0), ()) .default).elim [] Prod.fst ++
      (armGpr.op (.select i64) (.gpr (.reg .X3), .gpr (.reg .X1), .gpr (.reg .X2), ())
        (.gpr (.reg .X0), ()) .default).elim [] Prod.fst ++
      (armGpr.op (.addc 64) (.gpr (.reg .X1), .gpr (.reg .X2), .flag .cs, ())
        (.gpr (.reg .X0), .gpr (.reg .X4), ()) .default).elim [] Prod.fst ++
      (armGpr.op (.subb 32) (.gpr (.reg .X1), .gpr (.reg .X2), .flag .cc, ())
        (.gpr (.reg .X0), .flag .cc, ()) .default).elim [] Prod.fst ++
      (armGpr.op (.smulw 32) (.gpr (.reg .X1), .gpr (.reg .X2), ())
        (.gpr (.reg .X0), .gpr (.reg .X3), ()) .default).elim [] Prod.fst ++
      (armGpr.op (.fshr 64) (.gpr (.reg .X1), .gpr (.reg .X2), .imm 7#64, ())
        (.gpr (.reg .X0), ()) .default).elim [] Prod.fst := rfl

theorem parser_opt_c6_rfl :
    ⸨prog|
      movz x0, #42
      movn x0, #0x1234
      movz x0, #0x5678
      movk x0, #0x1234, lsl #32
      movn x0, #0x5678
      movk x0, #0xedc3, lsl #32
      add x0, x1, #0x123, lsl #12
      sub w0, w1, #5, lsl #12
      and w0, w1, #7
      ldr w0, [x1, x2, lsl #2]
      str x0, [x1, x2, lsl #3]
    ⸩ =
      armGpr.movi (.reg .X0) 42#64 ++
      armGpr.movi (.reg .X0) (~~~0x1234#64) ++
      armGpr.movi (.reg .X0) 0x1234_0000_5678#64 ++
      armGpr.movi (.reg .X0) (~~~0x123c_0000_5678#64) ++
      (armGpr.op (.add i64) (.gpr (.reg .X1), .imm 0x123000#64, ())
        (.gpr (.reg .X0), ()) .default).elim [] Prod.fst ++
      (armGpr.op (.sub i32) (.gpr (.reg .X1), .imm 0x5000#32, ())
        (.gpr (.reg .X0), ()) .default).elim [] Prod.fst ++
      (armGpr.op (.and i32) (.gpr (.reg .X1), .imm 7#32, ())
        (.gpr (.reg .X0), ()) .default).elim [] Prod.fst ++
      (armGpr.load i32 (.reg .X0)
        (.baseIdxDisp (.reg .X1) (.reg .X2) .s4 0)).elim [] Prod.fst ++
      (armGpr.store i64 (.gpr (.reg .X0))
        (.baseIdxDisp (.reg .X1) (.reg .X2) .s8 0)).elim [] Prod.fst := rfl

theorem parser_opt_a2_a3_rfl :
    ⸨prog|
      ands xzr, x1, #0x80000000
      ands wzr, w1, w2
      add x16, x1, x2, lsl #2
      ldr w0, [x16, #4]
      sub x16, x1, #4
      ldr w0, [x16, x2, lsl #2]
    ⸩ =
      (armGpr.testOp 64 true (.gpr (.reg .X1)) (.imm 0x80000000#64) (.flag .ne)).elim [] Prod.fst ++
      (armGpr.testOp 32 false (.gpr (.reg .X1)) (.gpr (.reg .X2)) (.flag .eq)).elim [] Prod.fst ++
      (armGpr.load i32 (.reg .X0)
        (.baseIdxDisp (.reg .X1) (.reg .X2) .s4 4)).elim [] Prod.fst ++
      (armGpr.load i32 (.reg .X0)
        (.baseIdxDisp (.reg .X1) (.reg .X2) .s4 (-4))).elim [] Prod.fst := rfl

theorem parser_opt_s2_rfl :
    ⸨prog|
      cbz w0, L_tgt
      cbnz x1, L_tgt
      ubfm w16, w2, #0, #7
      cbz w16, L_tgt
      tbz x2, #5, L_tgt
      tbnz w3, #31, L_tgt
    ⸩ =
      (armGpr.cmpZeroJcc .eq 32 (.reg .X0) "L_tgt").elim [] Prod.fst ++
      (armGpr.cmpZeroJcc .ne 64 (.reg .X1) "L_tgt").elim [] Prod.fst ++
      (armGpr.cmpZeroJcc .eq 8 (.reg .X2) "L_tgt").elim [] Prod.fst ++
      (armGpr.testJcc false 64 (.reg .X2) 32#64 "L_tgt").elim [] Prod.fst ++
      (armGpr.testJcc true 32 (.reg .X3) 0x80000000#32 "L_tgt").elim [] Prod.fst := rfl

theorem parser_opt_w3_rfl :
    ⸨prog|
      str wzr, [x0]
      strh wzr, [x1]
      strb wzr, [x2]
      str xzr, [x3]
      ldrsb x0, [x1]
      ldrsh x0, [x1]
      add x0, x1, x2, lsl #3
      add w0, w1, w2, lsl #2
      csel w0, w1, wzr, eq
      csinc w0, w1, wzr, ne
      csel x0, x1, xzr, eq
      csinc x0, x1, xzr, eq
      csinv x0, x1, xzr, eq
      ubfm w0, w1, #31, #31
      ands wzr, w1, #0xff
      orn w0, wzr, w1
    ⸩ =
      (armGpr.store i32 (.imm 0#32) (.baseDisp (.reg .X0) 0)).elim [] Prod.fst ++
      (armGpr.store i16 (.imm 0#16) (.baseDisp (.reg .X1) 0)).elim [] Prod.fst ++
      (armGpr.store .bool (.imm false) (.baseDisp (.reg .X2) 0)).elim [] Prod.fst ++
      (armGpr.store i64 (.imm 0#64) (.baseDisp (.reg .X3) 0)).elim [] Prod.fst ++
      (armGpr.loadSext 8 64 (.reg .X0) (.baseDisp (.reg .X1) 0)).elim [] Prod.fst ++
      (armGpr.loadSext 16 64 (.reg .X0) (.baseDisp (.reg .X1) 0)).elim [] Prod.fst ++
      (armGpr.leaArith 64 (some (.reg .X1)) (.reg .X2) .s8 0 (.reg .X0)).elim [] Prod.fst ++
      (armGpr.leaArith 32 (some (.reg .X1)) (.reg .X2) .s4 0 (.reg .X0)).elim [] Prod.fst ++
      (armGpr.op (.and .bool) (.gpr (.reg .X1), .flag .eq, ())
        (.gpr (.reg .X0), ()) .default).elim [] Prod.fst ++
      (armGpr.op (.or .bool) (.gpr (.reg .X1), .flag .eq, ())
        (.gpr (.reg .X0), ()) .default).elim [] Prod.fst ++
      (armGpr.op (.select i64) (.flag .eq, .gpr (.reg .X1), .imm 0#64, ())
        (.gpr (.reg .X0), ()) .default).elim [] Prod.fst ++
      (armGpr.op (.select i64) (.flag .eq, .gpr (.reg .X1), .imm 1#64, ())
        (.gpr (.reg .X0), ()) .default).elim [] Prod.fst ++
      (armGpr.op (.select i64) (.flag .eq, .gpr (.reg .X1), .imm (-1#64), ())
        (.gpr (.reg .X0), ()) .default).elim [] Prod.fst ++
      (armGpr.op (.cmp .slt i32) (.gpr (.reg .X1), .imm 0#32, ())
        (.gpr (.reg .X0), ()) .default).elim [] Prod.fst ++
      (armGpr.op (.cmp .eq i8) (.gpr (.reg .X1), .imm 0#8, ())
        (.flag .eq, ()) .default).elim [] Prod.fst ++
      (armGpr.op (.sub i32) (.imm (-1#32), .gpr (.reg .X1), ())
        (.gpr (.reg .X0), ()) .default).elim [] Prod.fst := rfl

theorem parser_opt_uxtw_rfl :
    ⸨prog|
      ldr w0, [x1, w2, uxtw #2]
      ldr x0, [x1, w2, uxtw #3]
      ldrh w0, [x1, w2, uxtw #1]
      ldrb w0, [x1, w2, uxtw #0]
      ldrsb x0, [x1, w2, uxtw #0]
      ldrsh x0, [x1, w2, uxtw #1]
      str w0, [x1, w2, uxtw #2]
      str x0, [x1, w2, uxtw #3]
      add x16, x1, w2, uxtw #2
      ldr w0, [x16, #4]
      sub x16, x1, #4
      ldr w0, [x16, w2, uxtw #2]
      add x0, x1, w2, uxtw #3
      add x0, x1, w2, uxtw #4
      add x16, x1, w2, uxtw #2
      add x0, x16, #8
      ubfiz x0, x1, #3, #32
    ⸩ =
      (armLoadZextIdx i32 (.reg .X0) (.reg .X1) (.reg .X2) .s4 0).elim [] Prod.fst ++
      (armLoadZextIdx i64 (.reg .X0) (.reg .X1) (.reg .X2) .s8 0).elim [] Prod.fst ++
      (armLoadZextIdx i16 (.reg .X0) (.reg .X1) (.reg .X2) .s2 0).elim [] Prod.fst ++
      (armLoadZextIdx i8 (.reg .X0) (.reg .X1) (.reg .X2) .s1 0).elim [] Prod.fst ++
      (armLoadSextZextIdx 8 64 (.reg .X0) (.reg .X1) (.reg .X2) .s1 0).elim [] Prod.fst ++
      (armLoadSextZextIdx 16 64 (.reg .X0) (.reg .X1) (.reg .X2) .s2 0).elim [] Prod.fst ++
      (armStoreZextIdx i32 (.gpr (.reg .X0)) (.reg .X1) (.reg .X2) .s4 0).elim [] Prod.fst ++
      (armStoreZextIdx i64 (.gpr (.reg .X0)) (.reg .X1) (.reg .X2) .s8 0).elim [] Prod.fst ++
      (armLoadZextIdx i32 (.reg .X0) (.reg .X1) (.reg .X2) .s4 4).elim [] Prod.fst ++
      (armLoadZextIdx i32 (.reg .X0) (.reg .X1) (.reg .X2) .s4 (-4)).elim [] Prod.fst ++
      (armLeaArithZext (some (.reg .X1)) (.reg .X2) 3 0 (.reg .X0)).elim [] Prod.fst ++
      (armLeaArithZext (some (.reg .X1)) (.reg .X2) 4 0 (.reg .X0)).elim [] Prod.fst ++
      (armLeaArithZext (some (.reg .X1)) (.reg .X2) 2 8 (.reg .X0)).elim [] Prod.fst ++
      (armLeaArithZext none (.reg .X1) 3 0 (.reg .X0)).elim [] Prod.fst := rfl

theorem parser_w5_isel_rfl :
    ⸨prog|
      ldrsw x0, [x1]
      add x16, x1, x2, lsl #2
      add x0, x16, #8
      ubfm w16, w2, #30, #29
      add w0, w16, #4
      add w0, w1, #12
    ⸩ =
      (armGpr.loadSext 32 64 (.reg .X0) (.baseDisp (.reg .X1) 0)).elim [] Prod.fst ++
      (armGpr.leaArith 64 (some (.reg .X1)) (.reg .X2) .s4 8 (.reg .X0)).elim [] Prod.fst ++
      (armGpr.leaArith 32 none (.reg .X2) .s4 4 (.reg .X0)).elim [] Prod.fst ++
      (armGpr.leaArith 32 none (.reg .X1) .s1 12 (.reg .X0)).elim [] Prod.fst := rfl

theorem parser_w62_ccmp_csneg_rfl :
    ⸨prog|
      ccmp w0, w1, #4, ne
      ccmp x0, #5, #4, eq
      ccmn w0, #1, #1, ge
      csneg w0, w1, w1, ne
      csneg x0, x1, x1, eq
      ands wzr, w2, #1
      csneg w0, w1, w1, ne
    ⸩ =
      (armCcmp .eq true .eq 32 (.gpr (.reg .X0)) (.gpr (.reg .X1))).elim [] (·.2.1) ++
      (armCcmp .eq false .ne 64 (.gpr (.reg .X0)) (.imm 5#64)).elim [] (·.2.1) ++
      (armCcmp .lt true .sle 32 (.gpr (.reg .X0)) (.imm (-1#32))).elim [] (·.2.1) ++
      (armSelectNeg 32 (.flag .ne) (.reg .X1) false (.reg .X0)).elim [] Prod.fst ++
      (armSelectNeg 64 (.flag .ne) (.reg .X1) true (.reg .X0)).elim [] Prod.fst ++
      (armSelectNeg 32 (.gpr (.reg .X2)) (.reg .X1) false (.reg .X0)).elim [] Prod.fst := rfl

end ParserChecks

end LeanQbe.T.Arm64
