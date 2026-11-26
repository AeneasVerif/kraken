module

public import LeanQbe.T.Vll.FactorX640
import LeanQbe.T.Amd64.TargLemmas
import Kraken.X64.Regs

/-!
# Cleanliness & Bounded-Length Proofs for `Amd64` Scalar/Vector Builders (`Vll.FactorX641`)

Auxiliary straight-line cleanliness (`cleanBound`) and Jcc-split lemmas supporting
`LeanQbe.T.Vll.FactorX64`, keeping every module under `2,500` LOC:
* `cleanBound_x64OpIns`, `cleanBound_x64StoreIns`, `cleanBound_x64LoadSextIns`,
  `cleanBound_x64TestOpIns`, `cleanBound_x64CmpMemIns`, `cleanBound_x64TestMemIns`,
  `cleanBound_x64AluMemIns`, `cleanBound_x64RmwMemIns`, `cleanBound_x64LeaArithIns`,
  `x64JnzMem_splitClean`.
* `cleanBound_x64VmovIns`, `cleanBound_x64VmoviWithIns`, `cleanBound_x64Vslot`,
  `cleanBound_x64Vmem`, `cleanBound_x64VopIns`.

Zero `Arm64` / `Kraken.AArch64` imports, zero `@[expose]` on proof lemmas/theorems.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Vll

open LeanQbe.T
open LeanQbe.T.Amd64

private theorem dst_reg {w : _root_.Width} (r : Reg w) : dstNoRip (.reg r) = true := rfl
private theorem rm_reg {w : _root_.Width} (r : Reg w) : rmNoRip (.reg r) = true := rfl
private theorem opnd_reg {w : _root_.Width} (r : Reg w) : opndNoRip (.reg r) = true := rfl
private theorem opnd_immBitsOp (w : _root_.Width) (c : BitVec w.bits) :
    opndNoRip (immBitsOp w c) = true := rfl

private theorem reg_ne_rip_b (r : Reg64) : (some (RegOrRip.reg r) != some RegOrRip.rip) = true := by
  cases r <;> rfl

private theorem cleanBound_nil : cleanBound 0 [] := ⟨rfl, Nat.le_refl 0⟩

private theorem cbMono {m n : Nat} {is : List _root_.Instr}
    (h : cleanBound m is) (hmn : m ≤ n) : cleanBound n is :=
  cleanBound_mono hmn h

private theorem cleanBound_single {i : _root_.Instr} (h : instrStraightClean i = true) :
    cleanBound 1 [i] :=
  ⟨by simp [h], Nat.le_refl 1⟩

private theorem cleanBound_if_empty {b : Bool} {is : List _root_.Instr} {n : Nat}
    (h : cleanBound n is) : cleanBound n (if b then [] else is) := by
  cases b
  · exact h
  · exact ⟨rfl, Nat.zero_le n⟩

private theorem cleanBound_if_nil {b : Bool} {is : List _root_.Instr} {n : Nat}
    (h : cleanBound n is) : cleanBound n (if b then is else []) := by
  cases b
  · exact ⟨rfl, Nat.zero_le n⟩
  · exact h

private theorem instr_setcc (rd : Reg64) (cc : CondCode) :
    instrStraightClean (x64InsI .W8 (.setcc cc (.reg (b8 rd)))) = true := rfl

private theorem cleanBound_setccOnlyIns (rd : Reg64) (cc : CondCode) :
    cleanBound 1 (setccOnlyIns rd cc) :=
  cleanBound_single (instr_setcc rd cc)

private theorem cleanBound_setccMoveIns (rd : Reg64) (cc : CondCode) :
    cleanBound 2 (setccMoveIns rd cc) :=
  cleanBound_cons (instr_setcc rd cc) (cleanBound_single rfl)

private theorem instr_argToBitsI {w : _root_.Width} {rd : Reg64}
    {pa : PArg Reg64 RegMm CondCode (.bits w.bits)} {i : _root_.Instr}
    (h : argToBitsI w rd pa = some i) : instrStraightClean i = true := by
  cases pa with
  | gpr _ => cases h; exact instr_movWI w rd _
  | imm _ => cases h; exact instr_moviI rd _
  | vec _ => cases h

private theorem instr_boolArgTo8I {rd : Reg64} {pa : PArg Reg64 RegMm CondCode .bool}
    {i : _root_.Instr} (h : boolArgTo8I rd pa = some i) : instrStraightClean i = true := by
  cases pa with
  | gpr _ | flag _ => cases h; rfl
  | imm _ => cases h; exact instr_moviI rd _
  | vec _ => cases h

private theorem cleanBound_opCopyBitsIns {w : _root_.Width}
    {pa : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64}
    {is : List _root_.Instr} {cl : FlagMask} (h : opCopyBitsIns w pa rd = some (is, cl)) :
    cleanBound 1 is := by
  cases pa with
  | gpr rs =>
    dsimp only [opCopyBitsIns] at h
    by_cases he : (rs == rd) = true <;> simp only [he, Bool.false_eq_true, ↓reduceIte] at h
    · cases h; exact cleanBound_mono (by omega) cleanBound_nil
    · cases h; exact cleanBound_single (instr_movWI w rd rs)
  | imm _ => cases h; exact cleanBound_single (instr_moviI rd _)
  | vec _ => cases h

private theorem cleanBound_opCopyBoolIns {pa : PArg Reg64 RegMm CondCode .bool}
    {pd : PDst Reg64 RegMm CondCode .bool} {is : List _root_.Instr} {cl : FlagMask}
    (h : opCopyBoolIns pa pd = some (is, cl)) : cleanBound 1 is := by
  cases pd with
  | vec _ | flag _ => cases h
  | gpr rd =>
    cases pa with
    | vec _ => cases h
    | imm _ => cases h; exact cleanBound_single (instr_moviI rd _)
    | flag cc => cases h; exact cleanBound_setccOnlyIns rd cc
    | gpr rs =>
      dsimp only [opCopyBoolIns] at h
      by_cases he : (rs == rd) = true <;> simp only [he, Bool.false_eq_true, ↓reduceIte] at h
      · cases h; exact cleanBound_mono (by omega) cleanBound_nil
      · cases h; exact cleanBound_single rfl

private theorem cleanBound_boolBinSelf {fn : Dst .W8 → Operand .W8 → Operation .W8}
    (hfn : ∀ d s, dstNoRip d = true → opndNoRip s = true → opStraightClean (fn d s) = true)
    {rd : Reg64} {pb : PArg Reg64 RegMm CondCode .bool}
    {is : List _root_.Instr} {cl : FlagMask}
    (h : boolBinSelfIns fn rd pb = some (is, cl)) : cleanBound 3 is := by
  cases pb with
  | gpr rs =>
    cases h
    exact cleanBound_mono (by omega)
      (cleanBound_single (by simp [instrStraightClean, hfn _ _ (dst_reg _) (opnd_reg _)]))
  | imm b =>
    cases h
    exact cleanBound_mono (by omega)
      (cleanBound_cons (instr_moviI .r10 _)
        (cleanBound_single (by simp [instrStraightClean, hfn _ _ (dst_reg _) (opnd_reg _)])))
  | flag cc =>
    cases h
    exact cleanBound_mono (by omega)
      (cleanBound_cons rfl
        (cleanBound_single (by simp [instrStraightClean, hfn _ _ (dst_reg _) (opnd_reg _)])))
  | vec _ => cases h

private theorem cleanBound_boolBinDst {fn : Dst .W8 → Operand .W8 → Operation .W8}
    (hfn : ∀ d s, dstNoRip d = true → opndNoRip s = true → opStraightClean (fn d s) = true)
    {rd : Reg64} {pa pb : PArg Reg64 RegMm CondCode .bool}
    {is : List _root_.Instr} {cl : FlagMask}
    (h : boolBinDstIns fn rd pa pb = some (is, cl)) : cleanBound 3 is := by
  dsimp only [boolBinDstIns, bind, Option.bind] at h
  cases h1 : boolArgTo8I rd pa with
  | none => simp [h1] at h
  | some d1 =>
    rw [h1] at h; dsimp only at h
    have hd1 := instr_boolArgTo8I h1
    cases pb with
    | vec _ => cases h
    | gpr rs =>
      cases h
      exact cleanBound_mono (by omega)
        (cleanBound_cons hd1
          (cleanBound_single (by simp [instrStraightClean, hfn _ _ (dst_reg _) (opnd_reg _)])))
    | imm b =>
      simp only [boolArgTo8I, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, _⟩
      exact cleanBound_cons hd1 (cleanBound_cons (instr_moviI .r10 _)
        (cleanBound_single (by simp [instrStraightClean, hfn _ _ (dst_reg _) (opnd_reg _)])))
    | flag cc =>
      simp only [boolArgTo8I, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, _⟩
      exact cleanBound_cons hd1 (cleanBound_cons (instr_setcc .r10 cc)
        (cleanBound_single (by simp [instrStraightClean, hfn _ _ (dst_reg _) (opnd_reg _)])))

private theorem cleanBound_opBoolBinIns {op : Bool → Bool → Bool}
    {fn : Dst .W8 → Operand .W8 → Operation .W8}
    (hfn : ∀ d s, dstNoRip d = true → opndNoRip s = true → opStraightClean (fn d s) = true)
    {pa pb : PArg Reg64 RegMm CondCode .bool} {pd : PDst Reg64 RegMm CondCode .bool}
    {is : List _root_.Instr} {cl : FlagMask}
    (h : opBoolBinIns op fn pa pb pd = some (is, cl)) : cleanBound 3 is := by
  cases pd with
  | vec _ | flag _ => cases h
  | gpr rd =>
    cases pa with
    | vec _ =>
      cases pb <;> dsimp only [opBoolBinIns] at h
      · split at h <;> simp [boolBinSelfIns, boolBinDstIns, bind, Option.bind, boolArgTo8I] at h
      · cases h
      · cases h
      · cases h
    | imm _ =>
      cases pb with
      | imm _ => cases h; exact cbMono (cleanBound_single (instr_moviI rd _)) (by omega)
      | gpr _ =>
        dsimp only [opBoolBinIns] at h; split at h
        · exact cleanBound_boolBinSelf hfn h
        · exact cleanBound_boolBinDst hfn h
      | vec _ | flag _ =>
        dsimp only [opBoolBinIns] at h; exact cleanBound_boolBinDst hfn h
    | flag _ =>
      cases pb with
      | gpr _ =>
        dsimp only [opBoolBinIns] at h; split at h
        · exact cleanBound_boolBinSelf hfn h
        · exact cleanBound_boolBinDst hfn h
      | vec _ | flag _ | imm _ =>
        dsimp only [opBoolBinIns] at h; exact cleanBound_boolBinDst hfn h
    | gpr _ =>
      dsimp only [opBoolBinIns] at h
      split at h
      · exact cleanBound_boolBinSelf hfn h
      · cases pb with
        | gpr _ =>
          dsimp only at h; split at h
          · exact cleanBound_boolBinSelf hfn h
          · exact cleanBound_boolBinDst hfn h
        | vec _ | flag _ | imm _ => exact cleanBound_boolBinDst hfn h

private theorem cleanBound_opBoolNotIns {pa : PArg Reg64 RegMm CondCode .bool}
    {pd : PDst Reg64 RegMm CondCode .bool} {is : List _root_.Instr} {cl : FlagMask}
    (h : opBoolNotIns pa pd = some (is, cl)) : cleanBound 2 is := by
  cases pd with
  | vec _ => cases h
  | flag ccDst =>
    cases pa with
    | flag ccSrc =>
      dsimp only [opBoolNotIns] at h
      by_cases he : (ccDst == x64NegCond ccSrc) = true <;>
        simp only [he, Bool.false_eq_true, ↓reduceIte] at h
      · cases h; exact cleanBound_mono (by omega) cleanBound_nil
      · cases h
    | _ => cases h
  | gpr rd =>
    cases pa with
    | vec _ => cases h
    | imm _ => cases h; exact cleanBound_mono (by omega) (cleanBound_single (instr_moviI rd _))
    | flag cc => cases h; exact cleanBound_mono (by omega) (cleanBound_setccOnlyIns rd _)
    | gpr rs =>
      dsimp only [opBoolNotIns] at h
      by_cases he : (rs == rd) = true <;> simp only [he, Bool.false_eq_true, ↓reduceIte] at h
      · cases h; exact cleanBound_mono (by omega) (cleanBound_single rfl)
      · cases h; exact cleanBound_cons rfl (cleanBound_single rfl)

private theorem cleanBound_opBinLeaImm {w : _root_.Width} {k : AluBinKind} {ra : Reg64}
    {cb : BitVec w.bits} {rd : Reg64} {is : List _root_.Instr} {cl : FlagMask}
    (h : opBinLeaImm? w k ra cb rd = some (is, cl)) : cleanBound 1 is := by
  unfold opBinLeaImm? at h
  by_cases h1 : ((w == .W32 || w == .W64) && ra != rd && (k == .add || k == .sub)) = true <;>
    simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
  · by_cases h2 : fitsImm32 (BitVec.signExtend 64 (if k == .add then cb else -cb)) = true <;>
      simp only [h2, Bool.false_eq_true, ↓reduceIte] at h
    · cases h
      exact cleanBound_single
        (by simp [instrStraightClean, opStraightClean, addrNoRip, constNoLab, reg_ne_rip_b])
    · cases h
  · cases h

private theorem cleanBound_opBinLeaReg {w : _root_.Width} {k : AluBinKind} {ra rb rd : Reg64}
    {is : List _root_.Instr} {cl : FlagMask}
    (h : opBinLeaReg? w k ra rb rd = some (is, cl)) : cleanBound 1 is := by
  unfold opBinLeaReg? at h
  by_cases h1 : (k == .add && (w == .W32 || w == .W64) && ra != rd && rb != rd) = true <;>
    simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
  · by_cases h2 : (rb != .rsp) = true <;> simp only [h2, Bool.false_eq_true, ↓reduceIte] at h
    · cases h
      exact cleanBound_single
        (by simp [instrStraightClean, opStraightClean, addrNoRip, constNoLab, reg_ne_rip_b])
    · by_cases h3 : (ra != .rsp) = true <;> simp only [h3, Bool.false_eq_true, ↓reduceIte] at h
      · cases h
        exact cleanBound_single
          (by simp [instrStraightClean, opStraightClean, addrNoRip, constNoLab, reg_ne_rip_b])
      · cases h
  · cases h

private theorem cleanBound_opBinIns {w : _root_.Width} {k : AluBinKind}
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64} {vh : VariantHint}
    {is : List _root_.Instr} {cl : FlagMask}
    (h : opBinIns w k pa pb rd vh = some (is, cl)) : cleanBound 4 is := by
  have hri : ∀ ra cb,
      (if w != .W64 || fitsImm32 (cb.setWidth 64) then
        ((if ra == rd then [] else [movWI w rd ra]) ++ [aluBinI w k rd (immBitsOp w cb)], maskAll)
       else
        ([moviI .r10 (cb.setWidth 64)] ++
          (if ra == rd then [] else [movWI w rd ra]) ++
          [aluBinI w k rd (.reg (regW w .r10))], maskAll)) = (is, cl) → cleanBound 4 is := by
    intro ra cb hpair
    have hp := cleanBound_if_empty (b := ra == rd) (cleanBound_single (instr_movWI w rd ra))
    by_cases hf : (w != .W64 || fitsImm32 (cb.setWidth 64)) = true <;>
      simp only [hf, Bool.false_eq_true, ↓reduceIte] at hpair
    · cases hpair
      exact cbMono
        (cleanBound_append hp (cleanBound_single (instr_aluBinI w k rd (opnd_immBitsOp w cb))))
        (by omega)
    · cases hpair
      exact cbMono (cleanBound_cons (instr_moviI .r10 _)
        (cleanBound_append hp (cleanBound_single (instr_aluBinI w k rd (opnd_reg _)))))
        (by omega)
  have fallback : opBinIns w k pa pb rd .default = some (is, cl) → cleanBound 4 is := by
    intro hfb
    dsimp only [opBinIns] at hfb
    cases pa with
    | vec _ => cases pb <;> cases hfb
    | imm ca =>
      cases pb with
      | vec _ => cases hfb
      | imm cb => cases hfb; exact cbMono (cleanBound_single (instr_moviI rd _)) (by omega)
      | gpr rb =>
        dsimp only at hfb
        by_cases hneg : (k == .sub && ca == 0) = true <;>
          simp only [hneg, Bool.false_eq_true, ↓reduceIte] at hfb
        · cases hfb
          exact cbMono (cleanBound_append
            (cleanBound_if_empty (b := rb == rd) (cleanBound_single (instr_movWI w rd rb)))
            (cleanBound_single (by simp [instrStraightClean, opStraightClean, dst_reg]))) (by omega)
        · by_cases hcm : k.isComm = true <;>
            simp only [hcm, Bool.false_eq_true, ↓reduceIte] at hfb
          · cases ho : opBinLeaImm? w k rb ca rd with
            | none => simp only [ho, Option.getD_none, Option.some.injEq] at hfb
                      exact hri rb ca hfb
            | some res => simp only [ho, Option.getD_some, Option.some.injEq] at hfb
                          subst hfb; exact cbMono (cleanBound_opBinLeaImm ho) (by omega)
          · cases hfb
            exact cbMono (cleanBound_cons (instr_moviI .r11 _)
              (cleanBound_cons (instr_aluBinI w .sub .r11 (opnd_reg _))
                (cleanBound_single (instr_movWI w rd .r11)))) (by omega)
    | gpr ra =>
      cases pb with
      | vec _ => cases hfb
      | imm cb =>
        cases ho : opBinLeaImm? w k ra cb rd with
        | none => simp only [ho, Option.getD_none, Option.some.injEq] at hfb
                  exact hri ra cb hfb
        | some res => simp only [ho, Option.getD_some, Option.some.injEq] at hfb
                      subst hfb; exact cbMono (cleanBound_opBinLeaImm ho) (by omega)
      | gpr rb =>
        dsimp only at hfb
        by_cases h1 : (ra == rd) = true <;> simp only [h1, Bool.false_eq_true, ↓reduceIte] at hfb
        · cases hfb; exact cbMono
            (cleanBound_single (instr_aluBinI w k rd (opnd_reg _))) (by omega)
        · by_cases h2 : (k.isComm && rb == rd) = true <;>
            simp only [h2, Bool.false_eq_true, ↓reduceIte] at hfb
          · cases hfb; exact cbMono
              (cleanBound_single (instr_aluBinI w k rd (opnd_reg _))) (by omega)
          · by_cases h3 : (k == .sub && rb == rd) = true <;>
              simp only [h3, Bool.false_eq_true, ↓reduceIte] at hfb
            · cases hfb
              exact cbMono
                (cleanBound_cons (by simp [instrStraightClean, opStraightClean, dst_reg])
                  (cleanBound_single (instr_aluBinI w .add rd (opnd_reg _)))) (by omega)
            · cases ho : opBinLeaReg? w k ra rb rd with
              | some res => rw [ho] at hfb; cases hfb
                            exact cbMono (cleanBound_opBinLeaReg ho) (by omega)
              | none =>
                rw [ho] at hfb; dsimp only at hfb
                by_cases h4 : (rb != rd) = true <;>
                  simp only [h4, Bool.false_eq_true, ↓reduceIte] at hfb
                · cases hfb; exact cbMono (cleanBound_cons (instr_movWI w rd ra)
                    (cleanBound_single (instr_aluBinI w k rd (opnd_reg _)))) (by omega)
                · cases hfb
                  exact cbMono (cleanBound_cons (instr_movWI w .r11 ra)
                    (cleanBound_cons (instr_aluBinI w k .r11 (opnd_reg _))
                      (cleanBound_single (instr_movWI w rd .r11)))) (by omega)
  have hleaDisp : ∀ (rb : Reg64) (off : Int64), cleanBound 4
      [x64InsI w (.lea (regW w rd) (atDisp rb off))] := fun rb off =>
    cbMono (cleanBound_single
      (by simp [instrStraightClean, opStraightClean, addrNoRip, constNoLab, reg_ne_rip_b]))
      (by omega)
  have hincDec : ∀ (isDec : Bool) (r : Reg64), cleanBound 4
      ((if r == rd then [] else [movWI w rd r]) ++
        [x64InsI w (if isDec then .dec (.reg (regW w rd))
          else .inc (.reg (regW w rd)))]) := fun isDec r =>
    cbMono (cleanBound_append
      (cleanBound_if_empty (b := r == rd) (cleanBound_single (instr_movWI w rd r)))
      (cleanBound_single (by cases isDec <;> simp [instrStraightClean, opStraightClean, dst_reg])))
      (by omega)
  cases vh with
  | default | adcx | adox | mulxFast => exact fallback h
  | disp off =>
    dsimp only [opBinIns] at h
    by_cases hd0 : ((w == .W32 || w == .W64) && fitsImm32 off.toBitVec) = true
    · simp only [hd0, ↓reduceIte] at h
      cases k with
      | and | or | xor | mul => exact fallback h
      | add =>
        cases pa with
        | vec _ => exact fallback h
        | gpr rb =>
          cases pb with
          | gpr _ | vec _ => exact fallback h
          | imm cb =>
            dsimp only at h
            by_cases hdc : (off.toBitVec.setWidth w.bits == cb) = true
            · simp only [hdc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, _⟩; exact hleaDisp rb off
            · simp only [hdc, Bool.false_eq_true, ↓reduceIte] at h; exact fallback h
        | imm ca =>
          cases pb with
          | imm _ | vec _ => exact fallback h
          | gpr rb =>
            dsimp only at h
            by_cases hdc : (off.toBitVec.setWidth w.bits == ca) = true
            · simp only [hdc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, _⟩; exact hleaDisp rb off
            · simp only [hdc, Bool.false_eq_true, ↓reduceIte] at h; exact fallback h
      | sub =>
        cases pa with
        | imm _ | vec _ => exact fallback h
        | gpr rb =>
          cases pb with
          | gpr _ | vec _ => exact fallback h
          | imm cb =>
            dsimp only at h
            by_cases hdc : ((-off.toBitVec).setWidth w.bits == cb) = true
            · simp only [hdc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, _⟩; exact hleaDisp rb off
            · simp only [hdc, Bool.false_eq_true, ↓reduceIte] at h; exact fallback h
    · simp only [hd0, Bool.false_eq_true, ↓reduceIte] at h; exact fallback h
  | decInc =>
    dsimp only [opBinIns] at h
    cases k with
    | and | or | xor | mul => exact fallback h
    | sub =>
      cases pa with
      | imm _ | vec _ => exact fallback h
      | gpr ra =>
        cases pb with
        | gpr _ | vec _ => exact fallback h
        | imm cb =>
          dsimp only at h
          by_cases h1 : (cb == 1#w.bits) = true
          · simp only [h1, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, _⟩; exact hincDec true ra
          · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
            by_cases h2 : (cb == -1#w.bits) = true
            · simp only [h2, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, _⟩; exact hincDec false ra
            · simp only [h2, Bool.false_eq_true, ↓reduceIte] at h; exact fallback h
    | add =>
      cases pa with
      | vec _ => exact fallback h
      | gpr ra =>
        cases pb with
        | gpr _ | vec _ => exact fallback h
        | imm cb =>
          dsimp only at h
          by_cases h1 : (cb == 1#w.bits) = true
          · simp only [h1, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, _⟩; exact hincDec false ra
          · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
            by_cases h2 : (cb == -1#w.bits) = true
            · simp only [h2, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, _⟩; exact hincDec true ra
            · simp only [h2, Bool.false_eq_true, ↓reduceIte] at h; exact fallback h
      | imm ca =>
        cases pb with
        | imm _ | vec _ => exact fallback h
        | gpr rb =>
          dsimp only at h
          by_cases h1 : (ca == 1#w.bits) = true
          · simp only [h1, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, _⟩; exact hincDec false rb
          · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h; exact fallback h

private theorem cleanBound_opShiftIns {w : _root_.Width} {sk : ShiftKind}
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64}
    {is : List _root_.Instr} {cl : FlagMask}
    (h : opShiftIns w sk pa pb rd = some (is, cl)) : cleanBound 12 is := by
  have hsk : ∀ {w' : _root_.Width} (d : Dst w') c, dstNoRip d = true → scNoLab c = true →
      opStraightClean (sk.toOp d c) = true := fun d c hd hc => by
    cases sk <;> simp [ShiftKind.toOp, opStraightClean, hd, hc]
  dsimp only [opShiftIns] at h
  cases pb with
  | vec _ => cases h
  | imm cb =>
    dsimp only at h
    by_cases h0 : (cb.toNat % w.bits == 0) = true <;>
      simp only [h0, Bool.false_eq_true, ↓reduceIte] at h
    · exact cbMono (cleanBound_opCopyBitsIns h) (by omega)
    · by_cases hr : ((w == .W32 || w == .W64) && sk.isRot) = true <;>
        simp only [hr, Bool.false_eq_true, ↓reduceIte] at h
      · cases pa with
        | vec _ => cases h
        | imm _ => cases h; exact cbMono (cleanBound_single (instr_moviI rd _)) (by omega)
        | gpr _ =>
          cases h
          exact cbMono
            (cleanBound_single (by simp [instrStraightClean, opStraightClean, rm_reg, constNoLab]))
            (by omega)
      · have hfb : cleanBound 2 is → cleanBound 12 is := fun hb => cbMono hb (by omega)
        have hfb' : (do
            let setup ← match pa with
              | .gpr ra => some (if ra == rd then [] else [movWI w rd ra])
              | .imm ca => some [moviI rd (ca.setWidth 64)]
              | .vec _ => none
            some (setup ++
              [x64InsI w (sk.toOp (.reg (regW w rd))
                (.imm8 (.int64 (Int64.ofNat (cb.toNat % w.bits)))))],
              if sk.isRot then maskCF ||| maskOF else maskAll)) = some (is, cl) →
            cleanBound 2 is := by
          intro h1
          cases pa with
          | vec _ => cases h1
          | gpr ra =>
            cases h1
            exact cleanBound_append
              (cleanBound_if_empty (cleanBound_single (instr_movWI w rd ra)))
              (cleanBound_single (by
                cases sk <;> simp [ShiftKind.toOp, instrStraightClean, opStraightClean,
                  dst_reg, scNoLab, constNoLab]))
          | imm ca =>
            cases h1
            exact cleanBound_cons (instr_moviI rd _)
              (cleanBound_single (by
                cases sk <;> simp [ShiftKind.toOp, instrStraightClean, opStraightClean,
                  dst_reg, scNoLab, constNoLab]))
        by_cases hsh : ((w == .W32 || w == .W64) && sk == .shl) = true <;>
          simp only [hsh, Bool.false_eq_true, ↓reduceIte] at h
        · cases pa with
          | vec _ | imm _ => exact hfb (hfb' h)
          | gpr ra =>
            dsimp only at h
            cases hsc : AddrScale.ofShift? (cb.toNat % w.bits) with
            | none => simp only [hsc] at h; exact hfb (hfb' h)
            | some sc =>
              simp only [hsc] at h
              by_cases hnr : (ra != rd && ra != .rsp) = true <;>
                simp only [hnr, Bool.false_eq_true, ↓reduceIte] at h
              · cases h
                exact cbMono (cleanBound_single (by
                  simp [instrStraightClean, opStraightClean, addrNoRip, constNoLab,
                    show (none != some RegOrRip.rip) = true from rfl])) (by omega)
              · exact hfb (hfb' h)
        · exact hfb (hfb' h)
  | gpr rb =>
    dsimp only at h
    split at h
    · cases hbm : sk.toBmi2Op? (w := w) with
      | none => rw [hbm] at h; cases pa <;> cases h
      | some bmiOp =>
        rw [hbm] at h
        have hc2 : ∀ s, opStraightClean (bmiOp (regW w rd) (.reg (regW w s)) (regW w rb)) =
            true := fun s => by cases sk <;> cases hbm <;> exact @rm_reg w (regW w s)
        cases pa with
        | vec _ => cases h
        | gpr ra =>
          cases h
          exact cbMono (cleanBound_single (by simp [instrStraightClean, hc2])) (by omega)
        | imm ca =>
          cases h
          exact cbMono (cleanBound_cons (instr_moviI .r11 _)
            (cleanBound_single (by simp [instrStraightClean, hc2]))) (by omega)
    · cases hd1 : argToBitsI w .r11 pa with
      | none => simp [hd1] at h
      | some d1 =>
        simp only [hd1] at h
        cases h
        have hsm : (shiftMaskRcxIns w).all instrStraightClean = true ∧
            (shiftMaskRcxIns w).length ≤ 1 := by
          cases w <;> exact ⟨by
            dsimp only [shiftMaskRcxIns]
            simp [instrStraightClean, opStraightClean, dst_reg, opndNoRip, constNoLab],
            by decide⟩
        have hmv : (if rb == .rcx then ([] : List _root_.Instr) else [movWI w .rcx rb]).all
            instrStraightClean = true ∧
            (if rb == .rcx then ([] : List _root_.Instr) else [movWI w .rcx rb]).length ≤ 1 := by
          split
          · exact ⟨rfl, Nat.zero_le _⟩
          · exact ⟨by simp [instr_movWI], Nat.le_refl _⟩
        refine ⟨?_, ?_⟩
        · simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
          refine ⟨⟨⟨⟨instr_argToBitsI hd1, rfl⟩, hmv.1⟩, hsm.1⟩, ?_, rfl, instr_movWI w rd .r11⟩
          simp only [instrStraightClean, hsk (.reg _) .cl (dst_reg _) rfl]
        · have := hmv.2; have := hsm.2
          simp only [List.length_append, List.length_cons, List.length_nil]; omega

private theorem cleanBound_opBitcntIns {w : _root_.Width} {bk : BitcntKind}
    {pa : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64}
    {is : List _root_.Instr} {cl : FlagMask}
    (h : opBitcntIns w bk pa rd = some (is, cl)) : cleanBound 8 is := by
  cases pa with
  | vec _ => cases h
  | imm _ => cases h; exact cbMono (cleanBound_single (instr_moviI rd _)) (by omega)
  | gpr ra =>
    cases h
    have him : ∀ c : BitVec 32, opndNoRip (immBitsOp .W32 c) = true := fun _ => rfl
    cases w <;> cases bk <;> (
      simp only [cleanBound, List.all_cons, List.all_nil, Bool.and_true, List.length_cons,
        List.length_nil]
      refine ⟨?_, by decide⟩
      simp [instrStraightClean, opStraightClean, dst_reg, rm_reg, opnd_reg,
        him, constNoLab, scNoLab])

private theorem cleanBound_opDivTail (w : _root_.Width) (isRem : Bool) (rd : Reg64)
    (da db : _root_.Instr) (core : List _root_.Instr)
    (hda : instrStraightClean da = true) (hdb : instrStraightClean db = true)
    (hcore : cleanBound 4 core) :
    cleanBound 16
      (let res : Reg64 := if isRem then .rdx else .rax
       let mvRes := fun dst src : Reg64 =>
         if dst == src then [] else [if w == .W64 then movI dst src else movlI dst src]
       if rd == .rax then [da, db, movI .rax .r10, movI .r10 .rdx] ++ core ++
           mvRes .rax res ++ [movI .rdx .r10]
       else if rd == .rdx then [da, db, movI .rdx .rax, movI .rax .r10, movI .r10 .rdx] ++
           core ++ mvRes .rdx res ++ [movI .rax .r10]
       else [da, db, movI rd .rax, movI .rax .r10, movI .r10 .rdx] ++ core ++
           [movI .r11 res, movI .rdx .r10, movI .rax rd,
            if w == .W64 then movI rd .r11 else movlI rd .r11]) := by
  have hmv : ∀ x y, cleanBound 1 (if x == y then ([] : List _root_.Instr)
      else [if w == .W64 then movI x y else movlI x y]) := fun x y => by
    split
    · exact cbMono cleanBound_nil (by omega)
    · cases w <;> exact cleanBound_single rfl
  have hlast : instrStraightClean (if w == .W64 then movI rd .r11 else movlI rd .r11) = true := by
    cases w <;> rfl
  have hmov : ∀ a b, instrStraightClean (movI a b) = true := fun _ _ => rfl
  dsimp only
  by_cases hr1 : (rd == .rax) = true
  · simp only [hr1, ↓reduceIte]
    exact cbMono (cleanBound_append (cleanBound_append (cleanBound_append
      (cleanBound_cons hda (cleanBound_cons hdb (cleanBound_cons (hmov _ _)
        (cleanBound_single (hmov _ _))))) hcore) (hmv .rax _))
      (cleanBound_single (hmov _ _))) (by omega)
  · by_cases hr2 : (rd == .rdx) = true
    · simp only [hr1, hr2, Bool.false_eq_true, ↓reduceIte]
      exact cbMono (cleanBound_append (cleanBound_append (cleanBound_append
        (cleanBound_cons hda (cleanBound_cons hdb (cleanBound_cons (hmov _ _)
          (cleanBound_cons (hmov _ _) (cleanBound_single (hmov _ _)))))) hcore)
        (hmv .rdx _)) (cleanBound_single (hmov _ _))) (by omega)
    · simp only [hr1, hr2, Bool.false_eq_true, ↓reduceIte]
      exact cbMono (cleanBound_append (cleanBound_append
        (cleanBound_cons hda (cleanBound_cons hdb (cleanBound_cons (hmov _ _)
          (cleanBound_cons (hmov _ _) (cleanBound_single (hmov _ _)))))) hcore)
        (cleanBound_cons (hmov _ _) (cleanBound_cons (hmov _ _)
          (cleanBound_cons (hmov _ _) (cleanBound_single hlast))))) (by omega)

private theorem cleanBound_opDivIns {w : _root_.Width} {isSigned isRem : Bool}
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64}
    {is : List _root_.Instr} {cl : FlagMask}
    (h : opDivIns w isSigned isRem pa pb rd = some (is, cl)) : cleanBound 16 is := by
  have hcore : ∀ (w' : _root_.Width), cleanBound 4 (match w' with
      | .W64 =>
        if isSigned then
          [movI .rdx .rax, x64InsI .W64 (.sar (.reg (q .rdx)) (.imm8 (.int64 63))),
           x64InsI .W64 (.idiv (.reg (q .r11)))]
        else
          [x64InsI .W32 (.xor (.reg (d .rdx)) (.reg (d .rdx))),
           x64InsI .W64 (.div (.reg (q .r11)))]
      | _ =>
        if isSigned then
          [movlI .rdx .rax, x64InsI .W32 (.sar (.reg (d .rdx)) (.imm8 (.int64 31))),
           x64InsI .W32 (.idiv (.reg (d .r11)))]
        else
          [x64InsI .W32 (.xor (.reg (d .rdx)) (.reg (d .rdx))),
           x64InsI .W32 (.div (.reg (d .r11)))]) := fun w' => by
    cases w' <;> cases isSigned <;> (
      refine ⟨by simp [instrStraightClean, opStraightClean, dst_reg, rm_reg, opnd_reg,
        scNoLab, constNoLab], by simp⟩)
  have hgpr : ∀ (w' : _root_.Width) (t r : Reg64), instrStraightClean (match w' with
      | .W8 => x64InsI .W32 (if isSigned then .movsx (.reg (d t)) (.reg (b8 r))
                             else .movzx (.reg (d t)) (.reg (b8 r)))
      | .W16 => x64InsI .W32 (if isSigned then .movsx (.reg (d t)) (.reg (h16 r))
                              else .movzx (.reg (d t)) (.reg (h16 r)))
      | .W32 => movlI t r | .W64 => movI t r) = true := fun w' t r => by
    cases w' <;> cases isSigned <;>
      simp [instrStraightClean, opStraightClean, dst_reg, rm_reg, opnd_reg]
  dsimp only [opDivIns] at h
  split at h
  · cases h
  · have hc := hcore w
    have hg10 := hgpr w .r10
    have hg11 := hgpr w .r11
    dsimp only [bind, Option.bind] at h
    cases pa with
    | vec _ => cases h
    | imm ca =>
      cases pb with
      | vec _ => cases h
      | imm cb =>
        cases w <;>
        { dsimp only at hc h; cases h
          exact cleanBound_opDivTail _ _ rd _ _ _ (instr_moviI .r10 _)
            (instr_moviI .r11 _) hc }
      | gpr rb =>
        cases w <;>
        { dsimp only at hc hg11 h; cases h
          exact cleanBound_opDivTail _ _ rd _ _ _ (instr_moviI .r10 _)
            (hg11 rb) hc }
    | gpr ra =>
      cases w <;> cases pb with
      | vec _ => cases h
      | imm cb =>
        dsimp only at hc hg10 h; cases h
        exact cleanBound_opDivTail _ _ rd _ _ _ (hg10 ra) (instr_moviI .r11 _) hc
      | gpr rb =>
        dsimp only at hc hg10 hg11 h; cases h
        exact cleanBound_opDivTail _ _ rd _ _ _ (hg10 ra) (hg11 rb) hc

private theorem cleanBound_cmpDirectIns {w : _root_.Width}
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {is : List _root_.Instr}
    (h : cmpDirectIns w pa pb = some is) : cleanBound 3 is := by
  have hri : ∀ rx cy, cleanBound 2 (cmpRegImmIns w rx cy) := fun rx cy => by
    unfold cmpRegImmIns
    by_cases h0 : (cy == 0#w.bits) = true <;>
      simp only [h0, Bool.false_eq_true, ↓reduceIte]
    · exact cbMono
        (cleanBound_single (by simp [instrStraightClean, opStraightClean, rm_reg, opnd_reg]))
        (by omega)
    · by_cases hf : (w != .W64 || fitsImm32 (cy.setWidth 64)) = true <;>
        simp only [hf, Bool.false_eq_true, ↓reduceIte]
      · exact cbMono (cleanBound_single
          (by simp [instrStraightClean, opStraightClean, rm_reg, opnd_immBitsOp])) (by omega)
      · exact cleanBound_cons (instr_moviI .r10 _)
          (cleanBound_single (by simp [instrStraightClean, opStraightClean, rm_reg, opnd_reg]))
  cases pa with
  | vec _ => cases h
  | gpr rx =>
    cases pb with
    | vec _ => cases h
    | gpr _ =>
      cases h
      exact cbMono
        (cleanBound_single (by simp [instrStraightClean, opStraightClean, rm_reg, opnd_reg]))
        (by omega)
    | imm cy => cases h; exact cbMono (hri rx cy) (by omega)
  | imm _ =>
    cases pb with
    | vec _ => cases h
    | gpr _ =>
      cases h
      exact cbMono (cleanBound_cons (instr_moviI .r10 _)
        (cleanBound_single (by simp [instrStraightClean, opStraightClean, rm_reg, opnd_reg])))
        (by omega)
    | imm _ =>
      cases h
      exact cleanBound_cons (instr_moviI .r11 _) (cleanBound_cons (instr_moviI .r10 _)
        (cleanBound_single (by simp [instrStraightClean, opStraightClean, rm_reg, opnd_reg])))

private theorem cleanBound_opCmpIns {w : _root_.Width} {co : CmpOp}
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {pd : PDst Reg64 RegMm CondCode .bool}
    {is : List _root_.Instr} {cl : FlagMask}
    (h : opCmpIns w co pa pb pd = some (is, cl)) : cleanBound 4 is := by
  have hri : ∀ rx cy, cleanBound 2 (cmpRegImmIns w rx cy) := fun rx cy => by
    unfold cmpRegImmIns
    by_cases h0 : (cy == 0#w.bits) = true <;> simp only [h0, Bool.false_eq_true, ↓reduceIte]
    · exact cbMono
        (cleanBound_single (by simp [instrStraightClean, opStraightClean, rm_reg, opnd_reg]))
        (by omega)
    · by_cases hf : (w != .W64 || fitsImm32 (cy.setWidth 64)) = true <;>
        simp only [hf, Bool.false_eq_true, ↓reduceIte]
      · exact cbMono (cleanBound_single
          (by simp [instrStraightClean, opStraightClean, rm_reg, opnd_immBitsOp])) (by omega)
      · exact cleanBound_cons (instr_moviI .r10 _)
          (cleanBound_single (by simp [instrStraightClean, opStraightClean, rm_reg, opnd_reg]))
  cases pd with
  | vec _ => cases h
  | gpr rd =>
    cases pa with
    | vec _ => cases h
    | gpr ra =>
      dsimp only [opCmpIns, bind, Option.bind] at h
      cases hc : cmpDirectIns w (.gpr ra) pb with
      | none => simp [hc] at h
      | some c =>
        simp only [hc, Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, _⟩
        exact cleanBound_append (cleanBound_cmpDirectIns hc) (cleanBound_setccOnlyIns rd _)
    | imm cx =>
      cases pb with
      | vec _ => cases h
      | imm _ => cases h; exact cbMono (cleanBound_single (instr_moviI rd _)) (by omega)
      | gpr ry =>
        dsimp only [opCmpIns] at h
        split at h
        · cases h; exact cbMono
            (cleanBound_append (hri ry cx) (cleanBound_setccOnlyIns rd _)) (by omega)
        · cases h; exact cbMono (cleanBound_cons (instr_moviI .r10 _)
            (cleanBound_cons (by simp [instrStraightClean, opStraightClean, rm_reg, opnd_reg])
              (cleanBound_setccOnlyIns rd _))) (by omega)
  | flag cc =>
    cases pa with
    | vec _ =>
      cases pb <;> dsimp only [opCmpIns, cmpDirectIns, bind, Option.bind] at h <;>
        (by_cases h1 : (cc == condOf co) = true <;> by_cases h2 : (cc == condOf co.swap) = true <;>
          simp [h1, h2] at h)
    | gpr rx =>
      cases pb with
      | vec _ =>
        dsimp only [opCmpIns, cmpDirectIns, bind, Option.bind] at h
        by_cases h1 : (cc == condOf co) = true <;> by_cases h2 : (cc == condOf co.swap) = true <;>
          simp [h1, h2] at h
      | gpr ry =>
        dsimp only [opCmpIns, cmpDirectIns, bind, Option.bind] at h
        split at h
        · cases h; exact cbMono (cleanBound_cmpDirectIns (w := w) (pa := .gpr rx)
            (pb := .gpr ry) rfl) (by omega)
        · split at h
          · cases h; exact cbMono (cleanBound_cmpDirectIns (w := w) (pa := .gpr ry)
              (pb := .gpr rx) rfl) (by omega)
          · cases h
      | imm cy =>
        dsimp only [opCmpIns, bind, Option.bind] at h
        split at h
        · cases hc : cmpDirectIns w (.gpr rx) (.imm cy) with
          | none => cases hc
          | some _ =>
            simp only [hc, Option.some.injEq, Prod.mk.injEq] at h; cases h.1
            exact cbMono (cleanBound_cmpDirectIns hc) (by omega)
        · split at h
          · cases hc : cmpDirectIns w (.imm cy) (.gpr rx) with
            | none => cases hc
            | some _ =>
              simp only [hc, Option.some.injEq, Prod.mk.injEq] at h; cases h.1
              exact cbMono (cleanBound_cmpDirectIns hc) (by omega)
          · cases h
    | imm cx =>
      cases pb with
      | vec _ =>
        dsimp only [opCmpIns, cmpDirectIns, bind, Option.bind] at h
        split at h
        · cases h
        · split at h <;> cases h
      | gpr ry =>
        dsimp only [opCmpIns, bind, Option.bind] at h
        split at h
        · cases h; exact cbMono (hri ry cx) (by omega)
        · split at h
          · cases h; exact cbMono (cleanBound_cons (instr_moviI .r10 _)
              (cleanBound_single (by simp [instrStraightClean, opStraightClean, rm_reg,
                opnd_reg]))) (by omega)
          · split at h
            · cases h; exact cbMono (cleanBound_cons (instr_moviI .r10 _)
                (cleanBound_single (by simp [instrStraightClean, opStraightClean, rm_reg,
                  opnd_reg]))) (by omega)
            · cases h
      | imm cy =>
        dsimp only [opCmpIns, bind, Option.bind] at h
        split at h
        · cases hc : cmpDirectIns w (.imm cx) (.imm cy) with
          | none => cases hc
          | some _ =>
            simp only [hc, Option.some.injEq, Prod.mk.injEq] at h; cases h.1
            exact cbMono (cleanBound_cmpDirectIns hc) (by omega)
        · split at h
          · cases hc : cmpDirectIns w (.imm cy) (.imm cx) with
            | none => cases hc
            | some _ =>
              simp only [hc, Option.some.injEq, Prod.mk.injEq] at h; cases h.1
              exact cbMono (cleanBound_cmpDirectIns hc) (by omega)
          · cases h

private theorem cleanBound_opSelectIns {w : _root_.Width} {pc : PArg Reg64 RegMm CondCode .bool}
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64}
    {is : List _root_.Instr} {cl : FlagMask}
    (h : opSelectIns w pc pa pb rd = some (is, cl)) : cleanBound 4 is := by
  have hsel : ∀ cc is', selectFlagSeqIns w cc pa pb rd = some is' → cleanBound 3 is' := by
    intro cc is' hs
    have hcmov : ∀ cnd r, instrStraightClean (x64InsI (if w == .W64 then .W64 else .W32)
        (.cmovcc cnd (regW (if w == .W64 then .W64 else .W32) rd)
          (.reg (regW (if w == .W64 then .W64 else .W32) r)))) = true :=
      fun _ _ => by simp [instrStraightClean, opStraightClean, rm_reg]
    have hmw : ∀ r, instrStraightClean (movWI (if w == .W64 then .W64 else .W32) rd r) = true :=
      fun r => instr_movWI _ rd r
    cases pa with
    | vec _ => cases pb <;> cases hs
    | gpr ra =>
      cases pb with
      | vec _ => cases hs
      | gpr rb =>
        dsimp only [selectFlagSeqIns] at hs
        split at hs
        · split at hs
          · cases hs; exact cbMono cleanBound_nil (by omega)
          · cases hs; exact cbMono (cleanBound_single (hmw ra)) (by omega)
        · split at hs
          · cases hs; exact cbMono (cleanBound_single (hcmov _ _)) (by omega)
          · split at hs
            · cases hs; exact cbMono (cleanBound_single (hcmov _ _)) (by omega)
            · cases hs; exact cbMono
                (cleanBound_cons (hmw rb) (cleanBound_single (hcmov _ _))) (by omega)
      | imm cb =>
        dsimp only [selectFlagSeqIns] at hs
        split at hs
        · cases hs; exact cbMono
            (cleanBound_cons (instr_moviI .r10 _) (cleanBound_single (hcmov _ _))) (by omega)
        · cases hs; exact cbMono
            (cleanBound_cons (instr_moviI rd _) (cleanBound_single (hcmov _ _))) (by omega)
    | imm ca =>
      cases pb with
      | vec _ => cases hs
      | gpr rb =>
        dsimp only [selectFlagSeqIns] at hs
        split at hs
        · cases hs; exact cbMono
            (cleanBound_cons (instr_moviI .r10 _) (cleanBound_single (hcmov _ _))) (by omega)
        · cases hs; exact cbMono
            (cleanBound_cons (instr_moviI rd _) (cleanBound_single (hcmov _ _))) (by omega)
      | imm cb =>
        cases hs; exact cleanBound_cons (instr_moviI rd _)
          (cleanBound_cons (instr_moviI .r10 _) (cleanBound_single (hcmov _ _)))
  cases pc with
  | vec _ => cases h
  | imm _ => exact cbMono (cleanBound_opCopyBitsIns h) (by omega)
  | flag cc =>
    dsimp only [opSelectIns] at h
    rcases Option.map_eq_some_iff.mp h with ⟨is', his, hp⟩; cases hp
    exact cbMono (hsel cc is his) (by omega)
  | gpr rc =>
    dsimp only [opSelectIns] at h
    rcases Option.map_eq_some_iff.mp h with ⟨is', his, hp⟩; cases hp
    exact cleanBound_cons (by simp [instrStraightClean, opStraightClean, rm_reg, opnd_reg])
      (hsel .nz is' his)

private theorem cleanBound_carryCore {w : _root_.Width} {isComm supportsImm : Bool}
    {mkReg : Reg64 → Reg64 → _root_.Instr} {mkImm : Reg64 → BitVec w.bits → _root_.Instr}
    (hmr : ∀ a b, instrStraightClean (mkReg a b) = true)
    (hmi : ∀ a c, instrStraightClean (mkImm a c) = true)
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64} {is : List _root_.Instr}
    (h : carryCoreIns w isComm mkReg mkImm supportsImm pa pb rd = some is) : cleanBound 4 is := by
  have hri : ∀ rx c, cleanBound 3
      (let pre := if rx == rd then [] else [movWI w rd rx]
       if supportsImm && (w != .W64 || fitsImm32 (c.setWidth 64)) then pre ++ [mkImm rd c]
       else [moviI .r10 (c.setWidth 64)] ++ pre ++ [mkReg rd .r10]) := fun rx c => by
    have hp := cleanBound_if_empty (b := rx == rd) (cleanBound_single (instr_movWI w rd rx))
    by_cases hf : (supportsImm && (w != .W64 || fitsImm32 (c.setWidth 64))) = true <;>
      simp only [hf, Bool.false_eq_true, ↓reduceIte]
    · exact cbMono (cleanBound_append hp (cleanBound_single (hmi rd c))) (by omega)
    · exact cleanBound_cons (instr_moviI .r10 _)
        (cleanBound_append hp (cleanBound_single (hmr rd .r10)))
  cases pa with
  | vec _ => cases pb <;> cases h
  | gpr ra =>
    cases pb with
    | vec _ => cases h
    | imm _ => cases h; exact cbMono (hri _ _) (by omega)
    | gpr rb =>
      dsimp +zetaHave only [carryCoreIns] at h
      split at h
      · cases h; exact cbMono (cleanBound_single (hmr rd rb)) (by omega)
      · split at h
        · cases h; exact cbMono (cleanBound_single (hmr rd ra)) (by omega)
        · split at h
          · cases h; exact cbMono
              (cleanBound_cons (instr_movWI w rd ra) (cleanBound_single (hmr rd rb))) (by omega)
          · cases h; exact cbMono (cleanBound_cons (instr_movWI w .r11 ra)
              (cleanBound_cons (hmr .r11 rb) (cleanBound_single (instr_movWI w rd .r11))))
              (by omega)
  | imm _ =>
    cases pb with
    | vec _ => cases h
    | gpr _ =>
      dsimp +zetaHave only [carryCoreIns] at h
      split at h
      · cases h; exact cbMono (hri _ _) (by omega)
      · cases h; exact cbMono (cleanBound_cons (instr_moviI .r11 _)
          (cleanBound_cons (hmr .r11 _) (cleanBound_single (instr_movWI w rd .r11))))
          (by omega)
    | imm _ => cases h; exact cleanBound_cons (instr_moviI rd _) (hri rd _)

private theorem cleanBound_carrySetup {pc : PArg Reg64 RegMm CondCode .bool}
    {su : List _root_.Instr}
    (h : (match pc with
      | .flag .c => some ([] : List _root_.Instr)
      | .flag cc => some [x64InsI .W8 (.setcc cc (.reg (b8 .r10))),
                          x64InsI .W8 (.neg (.reg (b8 .r10)))]
      | .gpr rc => some [x64InsI .W8 (.mov (.reg (b8 .r10)) (.reg (b8 rc))),
                         x64InsI .W8 (.neg (.reg (b8 .r10)))]
      | .imm false => some [x64InsI .W32 (.xor (.reg (d .r10)) (.reg (d .r10)))]
      | .imm true => some [moviI .r10 1, x64InsI .W8 (.neg (.reg (b8 .r10)))]
      | .vec _ => none) = some su) : cleanBound 2 su := by
  cases pc with
  | vec _ => cases h
  | imm b =>
    cases b <;> cases h
    · exact cbMono
        (cleanBound_single (by simp [instrStraightClean, opStraightClean, dst_reg, opnd_reg]))
        (by omega)
    · exact cleanBound_cons (instr_moviI .r10 _)
        (cleanBound_single (by simp [instrStraightClean, opStraightClean, dst_reg]))
  | gpr _ =>
    cases h
    exact cleanBound_cons (by simp [instrStraightClean, opStraightClean, dst_reg, opnd_reg])
      (cleanBound_single (by simp [instrStraightClean, opStraightClean, dst_reg]))
  | flag cc =>
    cases cc with
    | c => cases h; exact cbMono cleanBound_nil (by omega)
    | _ =>
      cases h
      exact cleanBound_cons (instr_setcc _ _)
        (cleanBound_single (by simp [instrStraightClean, opStraightClean, dst_reg]))

private theorem cleanBound_carryTail {w : _root_.Width}
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64}
    {dc : PDst Reg64 RegMm CondCode .bool} {is : List _root_.Instr} {cl : FlagMask}
    {mkReg : Reg64 → Reg64 → _root_.Instr} {mkImm : Reg64 → BitVec w.bits → _root_.Instr}
    (hmr : ∀ a b, instrStraightClean (mkReg a b) = true)
    (hmi : ∀ a c, instrStraightClean (mkImm a c) = true)
    (supportsImm : Bool) (fc : CondCode) (cl' : FlagMask) {su : List _root_.Instr}
    (htail : (carryCoreIns w true mkReg mkImm supportsImm pa pb rd >>= fun core =>
      (match dc with
        | .flag cc => if cc == fc then some ([] : List _root_.Instr) else none
        | .gpr rc => some (setccMoveIns rc fc)
        | .vec _ => none) >>= fun tail =>
      some (su ++ core ++ tail, cl')) = some (is, cl))
    (hsu : cleanBound 2 su) : cleanBound 12 is := by
  rcases Option.bind_eq_some_iff.mp htail with ⟨cr, hcr, htail⟩
  rcases Option.bind_eq_some_iff.mp htail with ⟨tail, htl, htail⟩
  cases htail
  have hcr_b := cleanBound_carryCore hmr hmi hcr
  cases dc with
  | vec _ => cases htl
  | gpr rc =>
    cases htl
    exact cbMono (cleanBound_append (cleanBound_append hsu hcr_b)
      (cleanBound_setccMoveIns rc fc)) (by omega)
  | flag cc =>
    dsimp only at htl
    split at htl
    · cases htl; rw [List.append_nil]
      exact cbMono (cleanBound_append hsu hcr_b) (by omega)
    · cases htl

private theorem cleanBound_opAddcIns {w : _root_.Width}
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {pc : PArg Reg64 RegMm CondCode .bool}
    {dsum : PDst Reg64 RegMm CondCode (.bits w.bits)} {dc : PDst Reg64 RegMm CondCode .bool}
    {vh : VariantHint} {is : List _root_.Instr} {cl : FlagMask}
    (h : opAddcIns w pa pb pc dsum dc vh = some (is, cl)) : cleanBound 12 is := by
  dsimp only [opAddcIns] at h
  cases dsum with
  | vec _ => cases h
  | gpr rd =>
    have hdis : ∀ ok (rhs : Option (List _root_.Instr × FlagMask)),
        (if !ok then none else rhs) = some (is, cl) → rhs = some (is, cl) := fun ok rhs hif => by
      cases ok <;> cases hif <;> rfl
    replace h := hdis _ _ h
    have hmr : ∀ a b, instrStraightClean (x64InsI w (.adc (.reg (regW w a))
        (.reg (regW w b)))) = true := fun _ _ => by
      simp [instrStraightClean, opStraightClean, dst_reg, opnd_reg]
    have hmi : ∀ a c, instrStraightClean (x64InsI w (.adc (.reg (regW w a))
        (immBitsOp w c))) = true := fun _ _ => by
      simp [instrStraightClean, opStraightClean, dst_reg, opnd_immBitsOp]
    cases pc with
    | vec _ => cases vh <;> { dsimp only [bind, Option.bind] at h; cases h }
    | gpr _ =>
      cases vh <;>
      { exact cleanBound_carryTail hmr hmi true .c maskAll
          (by dsimp only [bind, Option.bind] at h ⊢; exact h)
          (cleanBound_cons (by simp [instrStraightClean, opStraightClean, dst_reg, opnd_reg])
            (cleanBound_single rfl)) }
    | imm b =>
      cases b
      · cases vh <;>
        { exact cleanBound_carryTail hmr hmi true .c maskAll
            (by dsimp only [bind, Option.bind] at h ⊢; exact h)
            (cbMono (cleanBound_single
              (by simp [instrStraightClean, opStraightClean, dst_reg, opnd_reg])) (by omega)) }
      · cases vh <;>
        { exact cleanBound_carryTail hmr hmi true .c maskAll
            (by dsimp only [bind, Option.bind] at h ⊢; exact h)
            (cleanBound_cons (instr_moviI .r10 _) (cleanBound_single rfl)) }
    | flag cc =>
      cases cc
      case c =>
        cases vh
        case adcx =>
          exact cleanBound_carryTail
            (mkReg := fun dst src => x64InsI w (.adcx (regW w dst) (.reg (regW w src))))
            (mkImm := fun dst _ => x64InsI w (.adcx (regW w dst) (.reg (regW w dst))))
            (fun a b => by cases w <;> simp [instrStraightClean, opStraightClean, rm_reg])
            (fun a _ => by cases w <;> simp [instrStraightClean, opStraightClean, rm_reg])
            false .c maskCF h (cbMono cleanBound_nil (by omega))
        all_goals
        { exact cleanBound_carryTail hmr hmi true .c maskAll
            (by dsimp only [bind, Option.bind] at h ⊢; exact h)
            (cbMono cleanBound_nil (by omega)) }
      case o =>
        cases vh
        case adox =>
          exact cleanBound_carryTail
            (mkReg := fun dst src => x64InsI w (.adox (regW w dst) (.reg (regW w src))))
            (mkImm := fun dst _ => x64InsI w (.adox (regW w dst) (.reg (regW w dst))))
            (fun a b => by cases w <;> simp [instrStraightClean, opStraightClean, rm_reg])
            (fun a _ => by cases w <;> simp [instrStraightClean, opStraightClean, rm_reg])
            false .o maskOF h (cbMono cleanBound_nil (by omega))
        all_goals
        { exact cleanBound_carryTail hmr hmi true .c maskAll
            (by dsimp only [bind, Option.bind] at h ⊢; exact h)
            (cleanBound_cons (instr_setcc _ _) (cleanBound_single rfl)) }
      all_goals
      { cases vh <;>
        { exact cleanBound_carryTail hmr hmi true .c maskAll
            (by dsimp only [bind, Option.bind] at h ⊢; exact h)
            (cleanBound_cons (instr_setcc _ _) (cleanBound_single rfl)) } }

private theorem cleanBound_opSubbIns {w : _root_.Width}
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {pc : PArg Reg64 RegMm CondCode .bool}
    {ddiff : PDst Reg64 RegMm CondCode (.bits w.bits)} {db : PDst Reg64 RegMm CondCode .bool}
    {is : List _root_.Instr} {cl : FlagMask}
    (h : opSubbIns w pa pb pc ddiff db = some (is, cl)) : cleanBound 12 is := by
  dsimp only [opSubbIns] at h
  cases ddiff with
  | vec _ => cases h
  | gpr rd =>
    have hdis : ∀ ok (rhs : Option (List _root_.Instr × FlagMask)),
        (if !ok then none else rhs) = some (is, cl) → rhs = some (is, cl) := fun ok rhs hif => by
      cases ok <;> cases hif <;> rfl
    replace h := hdis _ _ h
    have hsu : ∀ {su}, (match pc with
        | .flag .c => some ([] : List _root_.Instr)
        | .flag cc => some [x64InsI .W8 (.setcc cc (.reg (b8 .r10))),
                            x64InsI .W8 (.neg (.reg (b8 .r10)))]
        | .gpr rc => some [x64InsI .W8 (.mov (.reg (b8 .r10)) (.reg (b8 rc))),
                           x64InsI .W8 (.neg (.reg (b8 .r10)))]
        | .imm false => some [x64InsI .W32 (.xor (.reg (d .r10)) (.reg (d .r10)))]
        | .imm true => some [moviI .r10 1, x64InsI .W8 (.neg (.reg (b8 .r10)))]
        | .vec _ => none) = some su → cleanBound 2 su := fun hs => cleanBound_carrySetup hs
    dsimp only [bind, Option.bind] at h
    have hrun : ∀ {su}, (match pc with
        | .flag .c => some ([] : List _root_.Instr)
        | .flag cc => some [x64InsI .W8 (.setcc cc (.reg (b8 .r10))),
                            x64InsI .W8 (.neg (.reg (b8 .r10)))]
        | .gpr rc => some [x64InsI .W8 (.mov (.reg (b8 .r10)) (.reg (b8 rc))),
                           x64InsI .W8 (.neg (.reg (b8 .r10)))]
        | .imm false => some [x64InsI .W32 (.xor (.reg (d .r10)) (.reg (d .r10)))]
        | .imm true => some [moviI .r10 1, x64InsI .W8 (.neg (.reg (b8 .r10)))]
        | .vec _ => none) = some su →
        (do
          let core ← carryCoreIns w false
            (fun dst src => x64InsI w (.sbb (.reg (regW w dst)) (.reg (regW w src))))
            (fun dst imm =>
              x64InsI w (.sbb (.reg (regW w dst)) (immBitsOp w imm))) true pa pb rd
          let tail ← match db with
            | .flag .c => some ([] : List _root_.Instr) | .flag _ => none
            | .gpr rb => some (setccMoveIns rb .c) | .vec _ => none
          some (su ++ core ++ tail, maskAll)) = some (is, cl) → cleanBound 12 is :=
      fun {su} hs hq => by
      dsimp only [bind, Option.bind] at hq
      cases hcr : carryCoreIns w false _ _ true pa pb rd with
      | none => rw [hcr] at hq; cases hq
      | some cr =>
        rw [hcr] at hq; dsimp only at hq
        have hcr_b := cleanBound_carryCore
          (fun _ _ => by simp [instrStraightClean, opStraightClean, dst_reg, opnd_reg])
          (fun _ _ => by simp [instrStraightClean, opStraightClean, dst_reg, opnd_immBitsOp])
          hcr
        have hsu' := hsu hs
        cases db with
        | vec _ => cases hq
        | gpr rb =>
          cases hq; exact cbMono (cleanBound_append (cleanBound_append hsu' hcr_b)
            (cleanBound_setccMoveIns rb .c)) (by omega)
        | flag cc =>
          cases cc <;> cases hq; rw [List.append_nil]
          exact cbMono (cleanBound_append hsu' hcr_b) (by omega)
    cases pc with
    | vec _ => cases h
    | gpr _ => exact hrun rfl h
    | imm b => cases b <;> exact hrun rfl h
    | flag cc => cases cc <;> exact hrun rfl h

private theorem cleanBound_opMulwIns {w : _root_.Width} {isSigned : Bool}
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)}
    {dlo dhi : PDst Reg64 RegMm CondCode (.bits w.bits)} {vh : VariantHint}
    {is : List _root_.Instr} {cl : FlagMask}
    (h : opMulwIns w isSigned pa pb dlo dhi vh = some (is, cl)) : cleanBound 16 is := by
  dsimp +zetaHave only [opMulwIns] at h
  cases dlo with
  | vec _ => cases h
  | gpr rlo =>
    cases dhi with
    | vec _ => cases h
    | gpr rhi =>
      dsimp +zetaHave only at h
      split at h
      · cases h
      · split at h
        · dsimp only [bind, Option.bind] at h
          have hmv : ∀ (b : Bool) (dst src : Reg64),
              (if b then ([] : List _root_.Instr) else [movI dst src]).all instrStraightClean =
                true ∧
              (if b then ([] : List _root_.Instr) else [movI dst src]).length ≤ 1 := by
            intro b _ _; split
            · exact ⟨rfl, Nat.zero_le _⟩
            · exact ⟨rfl, Nat.le_refl _⟩
          have hmx : instrStraightClean (x64InsI w
              (.mulx (regW w rhi) (regW w rlo) (.reg (regW w .r11)))) = true := by
            simp [instrStraightClean, opStraightClean, rm_reg]
          cases ha : argToBitsI w .r11 pa with
          | none => simp [ha] at h
          | some da =>
            rw [ha] at h; dsimp only at h
            split at h
            · cases h
              exact ⟨by simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_true,
                  instr_argToBitsI ha, (hmv (rlo == .rdx || rhi == .rdx) .r10 .rdx).1,
                  (hmv (rlo == .rdx || rhi == .rdx) .rdx .r10).1, hmx],
                by have := (hmv (rlo == .rdx || rhi == .rdx) .r10 .rdx).2
                   have := (hmv (rlo == .rdx || rhi == .rdx) .rdx .r10).2
                   simp only [List.length_append, List.length_cons, List.length_nil]; omega⟩
            · cases hb : argToBitsI w .rdx pb with
              | none => simp [hb] at h
              | some db =>
                simp only [hb, Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, _⟩
                exact ⟨by simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_true,
                    instr_argToBitsI ha, instr_argToBitsI hb,
                    (hmv (rlo == .rdx || rhi == .rdx) .r10 .rdx).1,
                    (hmv (rlo == .rdx || rhi == .rdx) .rdx .r10).1, hmx],
                  by have := (hmv (rlo == .rdx || rhi == .rdx) .r10 .rdx).2
                     have := (hmv (rlo == .rdx || rhi == .rdx) .rdx .r10).2
                     simp only [List.length_append, List.length_cons, List.length_nil]; omega⟩
        · dsimp only [bind, Option.bind] at h
          cases ha : argToBitsI w .r10 pa with
          | none => simp [ha] at h
          | some da =>
            rw [ha] at h
            cases hb : argToBitsI w .r11 pb with
            | none => simp [hb] at h
            | some db =>
              simp only [hb, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, _⟩
              have hda := instr_argToBitsI ha; have hdb := instr_argToBitsI hb
              have hmd : instrStraightClean (x64InsI w (if isSigned then
                  .imul1 (.reg (regW w .r11)) else .mul (.reg (regW w .r11)))) = true := by
                cases isSigned <;> simp [instrStraightClean, opStraightClean, rm_reg]
              have hmi : ∀ x y, instrStraightClean (movI x y) = true := fun _ _ => rfl
              have hseq : ∀ l, (l.all instrStraightClean = true) → l.length ≤ 16 →
                  cleanBound 16 l := fun _ ha' hl' => ⟨ha', hl'⟩
              cases c1 : (rlo == .rax && rhi == .rdx)
              · cases c2 : (rlo == .rdx && rhi == .rax)
                · cases c3 : (rlo == .rax)
                  · cases c4 : (rhi == .rdx)
                    · cases c5 : (rlo == .rdx)
                      · cases c6 : (rhi == .rax)
                        · exact hseq _ (by
                            simp only [List.all_cons, List.all_nil, Bool.and_true,
                              Bool.false_eq_true, ↓reduceIte, hda, hdb, hmd, hmi]) (by simp)
                        · exact hseq _ (by
                            simp only [List.all_cons, List.all_nil, Bool.and_true,
                              Bool.false_eq_true, ↓reduceIte, hda, hdb, hmd, hmi]) (by simp)
                      · exact hseq _ (by
                          simp only [List.all_cons, List.all_nil, Bool.and_true,
                            Bool.false_eq_true, ↓reduceIte, hda, hdb, hmd, hmi]) (by simp)
                    · exact hseq _ (by
                        simp only [List.all_cons, List.all_nil, Bool.and_true,
                          Bool.false_eq_true, ↓reduceIte, hda, hdb, hmd, hmi]) (by simp)
                  · exact hseq _ (by
                      simp only [List.all_cons, List.all_nil, Bool.and_true,
                        Bool.false_eq_true, ↓reduceIte, hda, hdb, hmd, hmi]) (by simp)
                · exact hseq _ (by
                    simp only [List.all_cons, List.all_nil, Bool.and_true,
                      Bool.false_eq_true, ↓reduceIte, hda, hdb, hmd, hmi]) (by simp)
              · exact hseq _ (by
                  simp only [List.all_cons, List.all_nil, Bool.and_true, ↓reduceIte, hda, hdb,
                    hmd, hmi]) (by simp)

private theorem cleanBound_opFunnelIns {w : _root_.Width} {isRight : Bool}
    {pa pb pc : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64}
    {is : List _root_.Instr} {cl : FlagMask}
    (h : opFunnelIns w isRight pa pb pc rd = some (is, cl)) : cleanBound 12 is := by
  dsimp only [opFunnelIns] at h
  have hmk : ∀ cnt, scNoLab cnt = true →
      instrStraightClean (x64InsI w (if isRight then .shrd (.reg (regW w .r11)) (regW w .r10) cnt
        else .shld (.reg (regW w .r11)) (regW w .r10) cnt)) = true := fun cnt hc => by
    cases isRight <;> simp [instrStraightClean, opStraightClean, dst_reg, hc]
  cases pc with
  | vec _ => cases h
  | imm c =>
    dsimp only at h
    split at h
    · exact cbMono (cleanBound_opCopyBitsIns h) (by omega)
    · dsimp only [bind, Option.bind] at h
      cases h1 : argToBitsI w .r11 (if isRight then pb else pa) with
      | none => simp [h1] at h
      | some dDst =>
        rw [h1] at h; dsimp only at h
        cases h2 : argToBitsI w .r10 (if isRight then pa else pb) with
        | none => simp [h2] at h
        | some dSrc =>
          simp only [h2, Option.some.injEq, Prod.mk.injEq] at h; rcases h with ⟨rfl, _⟩
          exact cbMono (cleanBound_cons (instr_argToBitsI h1)
            (cleanBound_cons (instr_argToBitsI h2)
              (cleanBound_cons (hmk _ rfl) (cleanBound_single (instr_movWI w rd .r11)))))
            (by omega)
  | gpr rc =>
    dsimp only [bind, Option.bind] at h
    cases h1 : argToBitsI w .r11 (if isRight then pb else pa) with
    | none => simp [h1] at h
    | some dDst =>
      rw [h1] at h; dsimp only at h
      cases h2 : argToBitsI w .r10 (if isRight then pa else pb) with
      | none => simp [h2] at h
      | some dSrc =>
        rw [h2] at h; dsimp only at h
        have hd1 := instr_argToBitsI h1; have hd2 := instr_argToBitsI h2; have hsh := hmk .cl rfl
        have hmv := cleanBound_if_empty (b := rc == .rcx)
          (cleanBound_single (i := movI .rcx rc) rfl)
        split at h
        · cases h; exact cbMono (cleanBound_cons hd1 (cleanBound_cons hd2
            (cleanBound_append hmv (cleanBound_cons hsh
              (cleanBound_single (instr_movWI w .rcx _)))))) (by omega)
        · split at h
          · cases h; exact cbMono (cleanBound_cons hd1 (cleanBound_cons hd2
              (cleanBound_cons (by simp [instrStraightClean, opStraightClean, dst_reg, opnd_reg])
                (cleanBound_cons (by simp [instrStraightClean, opStraightClean, dst_reg, opnd_reg])
                  (cleanBound_cons (by simp [instrStraightClean, opStraightClean, dst_reg,
                      opnd_reg])
                    (cleanBound_cons hsh (cleanBound_cons rfl
                      (cleanBound_single (instr_movWI w rd .r11))))))))) (by omega)
          · cases h; exact cbMono (cleanBound_cons hd1 (cleanBound_cons hd2
              (cleanBound_cons rfl (cleanBound_append hmv (cleanBound_cons hsh (cleanBound_cons rfl
                (cleanBound_single (instr_movWI w rd .r11)))))))) (by omega)

private theorem withWidth_clean {F : Nat → Type} {n : Nat} {x : F n}
    {k : (w : _root_.Width) → F w.bits → Option (List _root_.Instr × FlagMask)} {b : Nat}
    (hk : ∀ w y is cl, k w y = some (is, cl) → cleanBound b is)
    {is : List _root_.Instr} {cl : FlagMask}
    (h : Amd64.withWidth n x k = some (is, cl)) : cleanBound b is := by
  have hm : x64BitWidths.contains n = true := by
    unfold Amd64.withWidth at h; split at h <;> first | contradiction | rfl
  simp only [x64BitWidths, List.contains_cons, List.contains_nil, Bool.or_false,
    Bool.or_eq_true, beq_iff_eq] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact hk .W8 x _ _ h
  · exact hk .W16 x _ _ h
  · exact hk .W32 x _ _ h
  · exact hk .W64 x _ _ h

private theorem withWideWidth_clean {F : Nat → Type} {n : Nat} {x : F n}
    {k : (w : _root_.Width) → F w.bits → Option (List _root_.Instr × FlagMask)} {b : Nat}
    (hk : ∀ w y is cl, k w y = some (is, cl) → cleanBound b is)
    {is : List _root_.Instr} {cl : FlagMask}
    (h : Amd64.withWideWidth n x k = some (is, cl)) : cleanBound b is := by
  have hm : x64WideWidths.contains n = true := by
    unfold Amd64.withWideWidth at h; split at h <;> first | contradiction | rfl
  simp only [x64WideWidths, List.contains_cons, List.contains_nil, Bool.or_false,
    Bool.or_eq_true, beq_iff_eq] at hm
  rcases hm with rfl | rfl
  · exact hk .W32 x _ _ h
  · exact hk .W64 x _ _ h

private theorem cleanBound_opZextIns {m n : Nat}
    {pa : PArg Reg64 RegMm CondCode (.bits m)} {rd : Reg64}
    {is : List _root_.Instr} {cl : FlagMask}
    (h : opZextIns m n pa rd = some (is, cl)) : cleanBound 32 is := by
  unfold opZextIns at h
  split at h
  · cases h
  · split at h
    · cases h; exact cbMono (cleanBound_single (instr_moviI rd _)) (by omega)
    · split at h
      · cases h; exact cbMono (cleanBound_single rfl) (by omega)
      · cases h; exact cbMono (cleanBound_single rfl) (by omega)
      · cases h; exact cbMono (cleanBound_single rfl) (by omega)
      · cases h
    · cases h

private theorem cleanBound_opSextIns {m n : Nat}
    {pa : PArg Reg64 RegMm CondCode (.bits m)} {rd : Reg64}
    {is : List _root_.Instr} {cl : FlagMask}
    (h : opSextIns m n pa rd = some (is, cl)) : cleanBound 32 is := by
  unfold opSextIns at h
  split at h
  · cases h
  · split at h
    · cases h; exact cbMono (cleanBound_single (instr_moviI rd _)) (by omega)
    · split at h
      · cases h; exact cbMono (cleanBound_single rfl) (by omega)
      · cases h; exact cbMono (cleanBound_single rfl) (by omega)
      · cases h; exact cbMono (cleanBound_single rfl) (by omega)
      · cases h; exact cbMono (cleanBound_single rfl) (by omega)
      · cases h; exact cbMono (cleanBound_single rfl) (by omega)
      · cases h
    · cases h

private theorem cleanBound_opTruncIns {m n : Nat}
    {pa : PArg Reg64 RegMm CondCode (.bits m)} {rd : Reg64}
    {is : List _root_.Instr} {cl : FlagMask}
    (h : opTruncIns m n pa rd = some (is, cl)) : cleanBound 32 is := by
  unfold opTruncIns at h
  split at h
  · cases h
  · dsimp +zetaHave only at h
    split at h
    all_goals first
      | cases h
      | (cases pa with
        | vec _ => cases h
        | imm _ => cases h; exact cbMono (cleanBound_single (instr_moviI rd _)) (by omega)
        | gpr _ =>
          dsimp only at h; split at h
          · cases h; exact cbMono cleanBound_nil (by omega)
          · cases h; exact cbMono (cleanBound_single (instr_movWI _ rd _)) (by omega))

private theorem cleanBound_opBswapIns {n : Nat}
    {pa : PArg Reg64 RegMm CondCode (.bits n)} {rd : Reg64}
    {is : List _root_.Instr} {cl : FlagMask}
    (h : opBswapIns n pa rd = some (is, cl)) : cleanBound 32 is := by
  have hsub : ∀ {w : _root_.Width} r (i : _root_.Instr),
      instrStraightClean i = true →
      cleanBound 32 ((if r == rd then [] else [movWI w rd r]) ++ [i]) := fun {w} r i hi =>
    cbMono
      (cleanBound_append (cleanBound_if_empty (cleanBound_single (instr_movWI w rd r)))
        (cleanBound_single hi)) (by omega)
  unfold opBswapIns at h
  split at h
  · cases h; exact cbMono (cleanBound_single (instr_moviI rd _)) (by omega)
  · cases h
    exact hsub _ _ (by simp [instrStraightClean, opStraightClean, dst_reg, scNoLab, constNoLab])
  · cases h; exact cbMono (cleanBound_single (instr_moviI rd _)) (by omega)
  · cases h; exact hsub (w := .W32) _ _ rfl
  · cases h; exact cbMono (cleanBound_single (instr_moviI rd _)) (by omega)
  · cases h; exact hsub (w := .W64) _ _ rfl
  · cases h

theorem cleanBound_x64OpIns {sig rs : List Ty} (code : OpCode sig rs)
    (pas : Tup (PArg Reg64 RegMm CondCode) sig)
    (dsts : Tup (PDst Reg64 RegMm CondCode) rs) (vh : VariantHint)
    {is : List _root_.Instr} {cl : FlagMask}
    (h : x64OpIns code pas dsts vh = some (is, cl)) : cleanBound 32 is := by
  cases code
  case copy t =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t with
    | float _ | pair _ _ => cases h
    | bool => exact cbMono (cleanBound_opCopyBoolIns h) (by omega)
    | bits _ =>
      cases pd with
      | vec _ => cases h
      | gpr _ =>
        dsimp only [x64OpIns] at h
        exact withWidth_clean (b := 32)
          (fun _ _ _ _ hw => cbMono (cleanBound_opCopyBitsIns hw) (by omega)) h
  case add t | sub t | mul t | and t | or t | xor t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t with
    | float _ | pair _ _ => cases h
    | bool =>
      dsimp only [x64OpIns] at h
      first
      | cases h
      | exact cbMono (cleanBound_opBoolBinIns (fun _ _ hd hs => by
          simp [opStraightClean, hd, hs]) h) (by omega)
    | bits _ =>
      cases pd with
      | vec _ => cases h
      | gpr _ =>
        dsimp only [x64OpIns] at h
        exact withWidth_clean (b := 32)
          (fun _ _ _ _ hw => cbMono (cleanBound_opBinIns hw) (by omega)) h
  case neg t | not t =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t with
    | float _ | pair _ _ => cases h
    | bool =>
      dsimp only [x64OpIns] at h
      first
      | cases h
      | exact cbMono (cleanBound_opBoolNotIns h) (by omega)
    | bits _ =>
      cases pd with
      | vec _ => cases h
      | gpr rd =>
        dsimp only [x64OpIns] at h
        exact withWidth_clean (b := 32) (fun w pa' _ _ hw => by
          cases pa' with
          | vec _ => cases hw
          | imm _ =>
            cases hw; exact cbMono (cleanBound_single (instr_moviI rd _)) (by omega)
          | gpr rs =>
            cases hw; exact cbMono (cleanBound_append
              (cleanBound_if_empty (b := rs == rd) (cleanBound_single (instr_movWI w rd rs)))
              (cleanBound_single (by simp [instrStraightClean, opStraightClean, dst_reg])))
              (by omega)) h
  case shl t | lshr t | ashr t | rotl t | rotr t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t <;> try cases h
    cases pd with
    | vec _ => cases h
    | gpr _ =>
      dsimp only [x64OpIns] at h
      exact withWidth_clean (b := 32)
        (fun _ _ _ _ hw => cbMono (cleanBound_opShiftIns hw) (by omega)) h
  case fshl n | fshr n =>
    rcases pas with ⟨pa, pb, pc, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd with
    | vec _ => cases h
    | gpr _ =>
      dsimp only [x64OpIns] at h
      exact withWideWidth_clean (b := 32)
        (fun _ _ _ _ hw => cbMono (cleanBound_opFunnelIns hw) (by omega)) h
  case bswap t =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t <;> try cases h
    cases pd with
    | vec _ => cases h
    | gpr _ => exact cleanBound_opBswapIns h
  case clz _ | cls _ | ctz _ | popcnt _ =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd with
    | vec _ => cases h
    | gpr _ =>
      dsimp only [x64OpIns] at h
      exact withWidth_clean (b := 32)
        (fun _ _ _ _ hw => cbMono (cleanBound_opBitcntIns hw) (by omega)) h
  case cmp _ t _ _ =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t <;> try cases h
    dsimp only [x64OpIns] at h
    exact withWidth_clean (b := 32)
      (fun _ _ _ _ hw => cbMono (cleanBound_opCmpIns hw) (by omega)) h
  case select t =>
    rcases pas with ⟨pc, pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t <;> try cases h
    cases pd with
    | vec _ => cases h
    | gpr _ =>
      dsimp only [x64OpIns] at h
      exact withWidth_clean (b := 32)
        (fun _ _ _ _ hw => cbMono (cleanBound_opSelectIns hw) (by omega)) h
  case zext m n =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd with | vec _ => cases h | gpr _ => exact cleanBound_opZextIns h
  case sext m n =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd with | vec _ => cases h | gpr _ => exact cleanBound_opSextIns h
  case trunc m n =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd with | vec _ => cases h | gpr _ => exact cleanBound_opTruncIns h
  case ofBool n =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd with
    | vec _ => cases h
    | gpr rd =>
      dsimp only [x64OpIns] at h
      split at h
      · cases pa with
        | vec _ => cases h
        | gpr _ => cases h; exact cbMono (cleanBound_single rfl) (by omega)
        | imm _ => cases h; exact cbMono (cleanBound_single (instr_moviI rd _)) (by omega)
        | flag cc => cases h; exact cbMono (cleanBound_setccMoveIns rd cc) (by omega)
      · cases h
  case addc n =>
    rcases pas with ⟨pa, pb, pc, ⟨⟩⟩; rcases dsts with ⟨dsum, dc, ⟨⟩⟩
    dsimp only [x64OpIns] at h
    exact withWideWidth_clean (b := 32)
      (fun _ _ _ _ hw => cbMono (cleanBound_opAddcIns hw) (by omega)) h
  case subb n =>
    rcases pas with ⟨pa, pb, pc, ⟨⟩⟩; rcases dsts with ⟨ddiff, db, ⟨⟩⟩
    dsimp only [x64OpIns] at h
    exact withWideWidth_clean (b := 32)
      (fun _ _ _ _ hw => cbMono (cleanBound_opSubbIns hw) (by omega)) h
  case umulw n | smulw n =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨dlo, dhi, ⟨⟩⟩
    dsimp only [x64OpIns] at h
    exact withWideWidth_clean (b := 32)
      (fun _ _ _ _ hw => cbMono (cleanBound_opMulwIns hw) (by omega)) h
  case udiv n | sdiv n | urem n | srem n =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd with
    | vec _ => cases h
    | gpr _ =>
      dsimp only [x64OpIns] at h
      exact withWidth_clean (b := 32)
        (fun _ _ _ _ hw => cbMono (cleanBound_opDivIns hw) (by omega)) h
  case bitcast t u _ =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t <;> cases u <;> try cases h
    cases pd with
    | vec _ => cases h
    | gpr _ =>
      rename_i m _
      dsimp only [x64OpIns] at h
      split at h
      · exact withWidth_clean (b := 32)
          (fun _ _ _ _ hw => cbMono (cleanBound_opCopyBitsIns hw) (by omega)) h
      · cases h
  all_goals cases h

theorem cleanBound_x64StoreIns {t : Ty} {pa : PArg Reg64 RegMm CondCode t}
    {a : AddrArg Reg64} {is : List _root_.Instr} {cl : FlagMask}
    (h : x64StoreIns t pa a = some (is, cl)) : cleanBound 8 is := by
  have ⟨hpre, ha⟩ := clean_addrToExprIns a
  cases t with
  | float _ | pair _ _ => cases h
  | bool =>
    dsimp only [x64StoreIns] at h
    split at h
    · cases h
    · cases pa with
      | vec _ => cases h
      | gpr _ | imm _ =>
        cases h; exact cbMono (cleanBound_append hpre
          (cleanBound_single (by simp [instrStraightClean, opStraightClean, dstNoRip, ha,
            opndNoRip, rm_reg, constNoLab]))) (by omega)
      | flag _ =>
        cases h; exact cbMono (cleanBound_cons rfl (cleanBound_append hpre
          (cleanBound_single (by simp [instrStraightClean, opStraightClean, dstNoRip, ha,
            opnd_reg])))) (by omega)
  | bits n =>
    dsimp only [x64StoreIns] at h
    split at h
    · cases h
    · exact withWidth_clean (b := 8) (fun w pa' _ _ hw => by
        cases pa' with
        | vec _ => cases hw
        | gpr _ => cases hw; exact cbMono (cleanBound_append hpre
            (cleanBound_single (by simp [instrStraightClean, opStraightClean, dstNoRip, ha,
              opnd_reg]))) (by omega)
        | imm cb =>
          dsimp only at hw
          split at hw
          · cases hw; exact cbMono (cleanBound_append hpre
              (cleanBound_single (by simp [instrStraightClean, opStraightClean, dstNoRip, ha,
                opnd_immBitsOp]))) (by omega)
          · cases hw; exact cbMono (cleanBound_append hpre
              (cleanBound_cons (instr_moviI .r11 _) (cleanBound_single (by
                simp [instrStraightClean, opStraightClean, dstNoRip, ha, opnd_reg])))) (by omega))
        h

theorem cleanBound_x64LoadSextIns {m n : Nat} {rd : Reg64} {a : AddrArg Reg64}
    {is : List _root_.Instr} {cl : FlagMask}
    (h : x64LoadSextIns m n rd a = some (is, cl)) : cleanBound 4 is := by
  have ⟨hpre, ha⟩ := clean_addrToExprIns a
  unfold x64LoadSextIns at h
  split at h
  · cases h
  · split at h
    · cases h; exact cbMono (cleanBound_append hpre
        (cleanBound_single (by simp [instrStraightClean, opStraightClean, dst_reg, rmNoRip, ha])))
        (by omega)
    · cases h; exact cbMono (cleanBound_append hpre
        (cleanBound_single (by simp [instrStraightClean, opStraightClean, dst_reg, rmNoRip, ha])))
        (by omega)
    · cases h; exact cbMono (cleanBound_append hpre
        (cleanBound_single (by simp [instrStraightClean, opStraightClean, dst_reg, rmNoRip, ha])))
        (by omega)
    · cases h

theorem cleanBound_x64TestOpIns {n : Nat} {neg : Bool}
    {pa pb : PArg Reg64 RegMm CondCode (.bits n)} {pd : PDst Reg64 RegMm CondCode .bool}
    {is : List _root_.Instr} {cl : FlagMask}
    (h : x64TestOpIns n neg pa pb pd = some (is, cl)) : cleanBound 8 is := by
  refine withWidth_clean (b := 8) (fun w p _ _ hp => ?_) h
  rcases p with ⟨pa', pb'⟩
  have htd : ∀ is', testDirectIns w pa' pb' = some is' → cleanBound 3 is' := fun is' ht => by
    have hri : ∀ rx (cy : BitVec w.bits), cleanBound 3 (if w != .W64 || fitsImm32 (cy.setWidth 64)
        then [x64InsI w (.test (.reg (regW w rx)) (immBitsOp w cy))]
        else [moviI .r10 (cy.setWidth 64),
          x64InsI w (.test (.reg (regW w rx)) (.reg (regW w .r10)))]) := fun rx cy => by
      split
      · exact cbMono (cleanBound_single
          (by simp [instrStraightClean, opStraightClean, rm_reg, opnd_immBitsOp])) (by omega)
      · exact cbMono (cleanBound_cons (instr_moviI .r10 _)
          (cleanBound_single (by simp [instrStraightClean, opStraightClean, rm_reg, opnd_reg])))
          (by omega)
    cases pa' <;> cases pb' <;> try cases ht
    · exact cbMono
        (cleanBound_single (by simp [instrStraightClean, opStraightClean, rm_reg, opnd_reg]))
        (by omega)
    · exact hri _ _
    · exact hri _ _
    · exact cleanBound_cons (instr_moviI .r11 _) (cleanBound_cons (instr_moviI .r10 _)
        (cleanBound_single (by simp [instrStraightClean, opStraightClean, rm_reg, opnd_reg])))
  dsimp only [bind, Option.bind] at hp
  cases pd with
  | vec _ => cases hp
  | gpr rd =>
    cases pa' with
    | vec _ => cases pb' <;> cases hp
    | gpr rx =>
      cases pb' with
      | vec _ => cases hp
      | gpr ry =>
        cases hp; exact cbMono
          (cleanBound_append (htd _ rfl) (cleanBound_setccOnlyIns rd _)) (by omega)
      | imm cy =>
        cases ht : testDirectIns w (.gpr rx) (.imm cy) with
        | none => simp [ht] at hp
        | some t =>
          simp only [ht] at hp; cases hp
          exact cbMono (cleanBound_append (htd t ht) (cleanBound_setccOnlyIns rd _)) (by omega)
    | imm cx =>
      cases pb' with
      | vec _ => cases hp
      | gpr ry =>
        cases ht : testDirectIns w (.imm cx) (.gpr ry) with
        | none => simp [ht] at hp
        | some t =>
          simp only [ht] at hp; cases hp
          exact cbMono (cleanBound_append (htd t ht) (cleanBound_setccOnlyIns rd _)) (by omega)
      | imm cy =>
        cases hp; exact cbMono (cleanBound_single (instr_moviI rd _)) (by omega)
  | flag cc =>
    cases ht : testDirectIns w pa' pb' with
    | none =>
      rw [ht] at hp
      dsimp only [bind, Option.bind] at hp
      by_cases hcc : (cc == (if neg then .nz else .z)) = true
      · simp only [hcc, ↓reduceIte] at hp; cases hp
      · simp only [hcc, Bool.false_eq_true, ↓reduceIte] at hp; cases hp
    | some t =>
      rw [ht] at hp
      dsimp only [bind, Option.bind] at hp
      by_cases hcc : (cc == (if neg then .nz else .z)) = true
      · simp only [hcc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hp
        have hcb := htd t ht
        cases hp.1; exact cbMono hcb (by omega)
      · simp only [hcc, Bool.false_eq_true, ↓reduceIte] at hp; cases hp

theorem cleanBound_x64CmpMemIns {co : CmpOp} {n : Nat} {a : AddrArg Reg64}
    {pb : PArg Reg64 RegMm CondCode (.bits n)} {pd : PDst Reg64 RegMm CondCode .bool}
    {is : List _root_.Instr} {cl : FlagMask}
    (h : x64CmpMemIns co n a pb pd = some (is, cl)) : cleanBound 8 is := by
  have ⟨hpre, ha⟩ := clean_addrToExprIns a
  dsimp only [x64CmpMemIns] at h
  split at h
  · cases h
  · refine withWidth_clean (b := 8) (fun w pb' _ _ hp => ?_) h
    have hcm : ∀ sw is', cmpMemCoreIns w (addrToExprIns a).2.1 sw pb' = some is' →
        cleanBound 2 is' := fun sw is' hc => by
      cases pb' with
      | vec _ => cases hc
      | gpr _ =>
        cases sw <;> cases hc <;> exact cbMono
          (cleanBound_single (by simp [instrStraightClean, opStraightClean, rmNoRip, opndNoRip,
            ha])) (by omega)
      | imm cy =>
        dsimp only [cmpMemCoreIns] at hc
        cases sw <;> simp only [Bool.false_eq_true, ↓reduceIte] at hc
        · split at hc
          · cases hc; exact cbMono (cleanBound_single
              (by simp [instrStraightClean, opStraightClean, rmNoRip, ha, opnd_immBitsOp]))
              (by omega)
          · cases hc; exact cleanBound_cons (instr_moviI .r11 _) (cleanBound_single
              (by simp [instrStraightClean, opStraightClean, rmNoRip, ha, opnd_reg]))
        · cases hc; exact cleanBound_cons (instr_moviI .r11 _) (cleanBound_single
            (by simp [instrStraightClean, opStraightClean, opndNoRip, rmNoRip, ha]))
    dsimp only [bind, Option.bind] at hp
    cases pd with
    | vec _ => cases hp
    | gpr rd =>
      cases hc : cmpMemCoreIns w (addrToExprIns a).2.1 false pb' with
      | none => simp [hc] at hp
      | some cr =>
        simp only [hc] at hp; cases hp
        exact cbMono
          (cleanBound_append (cleanBound_append hpre (hcm false cr hc))
            (cleanBound_setccOnlyIns rd _)) (by omega)
    | flag cc =>
      dsimp only at hp
      split at hp
      · cases hc : cmpMemCoreIns w (addrToExprIns a).2.1 false pb' with
        | none => simp [hc] at hp
        | some cr =>
          simp only [hc] at hp; cases hp
          exact cbMono (cleanBound_append hpre (hcm false cr hc)) (by omega)
      · split at hp
        · cases hc : cmpMemCoreIns w (addrToExprIns a).2.1 true pb' with
          | none => simp [hc] at hp
          | some cr =>
            simp only [hc] at hp; cases hp
            exact cbMono (cleanBound_append hpre (hcm true cr hc)) (by omega)
        · cases hp

theorem cleanBound_x64TestMemIns {n : Nat} {neg : Bool} {a : AddrArg Reg64}
    {pb : PArg Reg64 RegMm CondCode (.bits n)} {pd : PDst Reg64 RegMm CondCode .bool}
    {is : List _root_.Instr} {cl : FlagMask}
    (h : x64TestMemIns n neg a pb pd = some (is, cl)) : cleanBound 8 is := by
  have ⟨hpre, ha⟩ := clean_addrToExprIns a
  dsimp only [x64TestMemIns] at h
  split at h
  · cases h
  · refine withWidth_clean (b := 8) (fun w pb' _ _ hp => ?_) h
    have hcr : ∀ cr, (match pb' with
        | .gpr ry => some [x64InsI w (.test (.mem (addrToExprIns a).2.1) (.reg (regW w ry)))]
        | .imm cy =>
          if w != .W64 || fitsImm32 (cy.setWidth 64) then
            some [x64InsI w (.test (.mem (addrToExprIns a).2.1) (immBitsOp w cy))]
          else
            some [moviI .r11 (cy.setWidth 64),
                  x64InsI w (.test (.mem (addrToExprIns a).2.1) (.reg (regW w .r11)))]
        | .vec _ => none) = some cr → cleanBound 2 cr := fun cr hc => by
      cases pb' with
      | vec _ => cases hc
      | gpr _ => cases hc; exact cbMono (cleanBound_single
          (by simp [instrStraightClean, opStraightClean, rmNoRip, ha, opnd_reg])) (by omega)
      | imm cy =>
        dsimp only at hc
        split at hc
        · cases hc; exact cbMono (cleanBound_single
            (by simp [instrStraightClean, opStraightClean, rmNoRip, ha, opnd_immBitsOp]))
            (by omega)
        · cases hc; exact cleanBound_cons (instr_moviI .r11 _) (cleanBound_single
            (by simp [instrStraightClean, opStraightClean, rmNoRip, ha, opnd_reg]))
    cases pd with
    | vec _ => cases hp
    | gpr rd =>
      cases pb' with
      | vec _ => cases hp
      | gpr ry =>
        cases hp; exact cbMono (cleanBound_append (cleanBound_append hpre (cleanBound_single
          (by simp [instrStraightClean, opStraightClean, rmNoRip, ha, opnd_reg])))
          (cleanBound_setccOnlyIns rd _)) (by omega)
      | imm cy =>
        dsimp only at hp; split at hp
        · cases hp; exact cbMono (cleanBound_append (cleanBound_append hpre (cleanBound_single
            (by simp [instrStraightClean, opStraightClean, rmNoRip, ha, opnd_immBitsOp])))
            (cleanBound_setccOnlyIns rd _)) (by omega)
        · cases hp; exact cbMono (cleanBound_append (cleanBound_append hpre (cleanBound_cons
            (instr_moviI .r11 _) (cleanBound_single
              (by simp [instrStraightClean, opStraightClean, rmNoRip, ha, opnd_reg]))))
            (cleanBound_setccOnlyIns rd _)) (by omega)
    | flag cc =>
      by_cases hcc : (cc == (if neg then .nz else .z)) = true
      · simp only [hcc, ↓reduceIte] at hp
        cases pb' with
        | vec _ => cases hp
        | gpr ry =>
          cases hp; exact cbMono (cleanBound_append hpre (cleanBound_single
            (by simp [instrStraightClean, opStraightClean, rmNoRip, ha, opnd_reg]))) (by omega)
        | imm cy =>
          dsimp only at hp; split at hp
          · cases hp; exact cbMono (cleanBound_append hpre (cleanBound_single
              (by simp [instrStraightClean, opStraightClean, rmNoRip, ha, opnd_immBitsOp])))
              (by omega)
          · cases hp; exact cbMono (cleanBound_append hpre (cleanBound_cons
              (instr_moviI .r11 _) (cleanBound_single
                (by simp [instrStraightClean, opStraightClean, rmNoRip, ha, opnd_reg]))))
              (by omega)
      · simp only [hcc, Bool.false_eq_true, ↓reduceIte] at hp; cases hp

theorem cleanBound_x64AluMemIns {n : Nat}
    {code : OpCode [.bits n, .bits n] [.bits n]} {memRhs : Bool} {a : AddrArg Reg64}
    {pb : PArg Reg64 RegMm CondCode (.bits n)} {rd : Reg64}
    {is : List _root_.Instr} {cl : FlagMask}
    (h : x64AluMemIns n code memRhs a pb rd = some (is, cl)) : cleanBound 8 is := by
  have ⟨hpre, ha⟩ := clean_addrToExprIns a
  dsimp only [x64AluMemIns] at h
  split at h
  · cases h
  · cases hk : x64AluMemKind? code with
    | none => rw [hk] at h; cases h
    | some k =>
      rw [hk] at h; dsimp only at h
      split at h
      · cases h
      · refine withWidth_clean (b := 8) (fun w pb' _ _ hp => ?_) h
        have halu := instr_aluBinI w k rd (show opndNoRip
          (.regOrMem (.mem (addrToExprIns a).2.1)) = true from by simp [opndNoRip, rmNoRip, ha])
        cases pb' with
        | vec _ => cases hp
        | gpr rs =>
          dsimp only at hp
          split at hp
          · cases hp; exact cbMono (cleanBound_append hpre (cleanBound_single halu)) (by omega)
          · split at hp
            · cases hp
            · cases hp; exact cbMono (cleanBound_cons (instr_movWI w rd rs)
                (cleanBound_append hpre (cleanBound_single halu))) (by omega)
        | imm _ =>
          dsimp only at hp
          split at hp
          · cases hp
          · cases hp; exact cbMono (cleanBound_cons (instr_moviI rd _)
              (cleanBound_append hpre (cleanBound_single halu))) (by omega)

theorem cleanBound_x64RmwMemIns {n : Nat}
    {code : OpCode [.bits n, .bits n] [.bits n]} {a : AddrArg Reg64}
    {pb : PArg Reg64 RegMm CondCode (.bits n)} {is : List _root_.Instr} {cl : FlagMask}
    (h : x64RmwMemIns n code a pb = some (is, cl)) : cleanBound 8 is := by
  have ⟨hpre, ha⟩ := clean_addrToExprIns a
  have hrmw : ∀ w k s, opndNoRip s = true →
      instrStraightClean (rmwMemI w k (addrToExprIns a).2.1 s) = true := fun w k s hs => by
    cases k <;> simp [rmwMemI, instrStraightClean, opStraightClean, dstNoRip, ha, hs]
  dsimp only [x64RmwMemIns] at h
  split at h
  · cases h
  · cases hk : x64RmwKind? code with
    | none => rw [hk] at h; cases h
    | some k =>
      rw [hk] at h
      refine withWidth_clean (b := 8) (fun w pb' _ _ hp => ?_) h
      cases pb' with
      | vec _ => cases hp
      | gpr _ =>
        cases hp
        exact cbMono
          (cleanBound_append hpre (cleanBound_single (hrmw w k _ (opnd_reg _)))) (by omega)
      | imm cy =>
        dsimp only at hp
        split at hp
        · cases hp; exact cbMono (cleanBound_append hpre
            (cleanBound_single (by simp [instrStraightClean, opStraightClean, dstNoRip, ha])))
            (by omega)
        · split at hp
          · cases hp; exact cbMono (cleanBound_append hpre
              (cleanBound_single (by simp [instrStraightClean, opStraightClean, dstNoRip, ha])))
              (by omega)
          · split at hp
            · cases hp; exact cbMono (cleanBound_append hpre
                (cleanBound_single (hrmw w k _ (opnd_immBitsOp w cy)))) (by omega)
            · cases hp; exact cbMono (cleanBound_append hpre
                (cleanBound_cons (instr_moviI .r11 _)
                  (cleanBound_single (hrmw w k _ (opnd_reg _))))) (by omega)

theorem cleanBound_x64LeaArithIns {w : Nat} {base? : Option Reg64} {idx : Reg64}
    {sc : AddrScale} {disp : Int64} {rd : Reg64} {is : List _root_.Instr} {cl : FlagMask}
    (h : x64LeaArithIns w base? idx sc disp rd = some (is, cl)) : cleanBound 4 is := by
  dsimp only [x64LeaArithIns] at h
  split at h
  · cases h
  · have hsib : ∀ (wd : _root_.Width) b i s d', instrStraightClean
        (x64InsI wd (.lea (regW wd rd) (atSIB b i s d'))) = true := fun _ b _ _ _ => by
      simp [instrStraightClean, opStraightClean, addrNoRip, constNoLab, reg_ne_rip_b]
    have hidx : ∀ (wd : _root_.Width) i s d', instrStraightClean
        (x64InsI wd (.lea (regW wd rd) (atIdx i s d'))) = true := fun _ _ _ _ => by
      simp [instrStraightClean, opStraightClean, addrNoRip, constNoLab,
        show (none != some RegOrRip.rip) = true from rfl]
    split at h
    · cases base? with
      | none =>
        dsimp only at h; split at h
        · cases h; exact cbMono (cleanBound_single (hidx .W32 _ _ _)) (by omega)
        · cases h
      | some rb =>
        dsimp only at h; split at h
        · cases h; exact cbMono (cleanBound_single (hsib .W32 _ _ _ _)) (by omega)
        · split at h
          · cases h; exact cbMono (cleanBound_single (hsib .W32 _ _ _ _)) (by omega)
          · cases h
    · cases base? with
      | none =>
        dsimp only at h; split at h
        · cases h; exact cbMono (cleanBound_single (hidx .W64 _ _ _)) (by omega)
        · cases h
      | some rb =>
        dsimp only at h; split at h
        · cases h; exact cbMono (cleanBound_single (hsib .W64 _ _ _ _)) (by omega)
        · split at h
          · cases h; exact cbMono (cleanBound_single (hsib .W64 _ _ _ _)) (by omega)
          · cases h
    · cases h

theorem x64JnzMem_splitClean {a : AddrArg Reg64} {inv : Bool} {l : Sym}
    {ds : List _root_.Directive} {cl : FlagMask} (h : x64JnzMem a inv l = some (ds, cl)) :
    ∃ ds_pre, ds = ds_pre ++ [ins (.jcc (if inv then .z else .nz) l)] ∧
      (∀ d ∈ ds_pre, dirStraightClean d = true) ∧ ds_pre.length < 2 ^ 60 := by
  have ⟨hpre, ha⟩ := clean_addrToExprIns a
  dsimp only [x64JnzMem] at h
  obtain ⟨is, hi, rfl⟩ := emitCleanPair_eq_some.mp h
  dsimp only [x64JnzMemIns] at hi
  split at hi
  · cases hi
  · cases hi
    let pre := (addrToExprIns a).1
    let cmpI := x64InsI .W8 (.cmp (.mem (addrToExprIns a).2.1) (immBitsOp .W8 0#8))
    have hc : (pre ++ [cmpI]).all instrStraightClean = true := by
      simp [pre, cmpI, hpre.1, instrStraightClean, opStraightClean, rmNoRip, ha, opnd_immBitsOp]
    refine ⟨emitClean (pre ++ [cmpI]), ?_, dirStraightClean_emitClean hc, ?_⟩
    · simp only [emitClean, pre, cmpI, List.append_assoc, List.map_append]; rfl
    · simp only [emitClean, List.length_map, List.length_append, List.length_singleton, pre]
      have := hpre.2; omega

private theorem instr_x64MoviI (rd : Reg64) (c : BitVec 64) :
    instrStraightClean (x64MoviI rd c) = true := by
  simp [instrStraightClean, opStraightClean, dst_reg, opndNoRip, constNoLab]

private theorem cleanBound_x64SlotAddrIns (i : Nat) :
    cleanBound 2 (x64SlotAddrIns i).1 ∧ addrNoRip (x64SlotAddrIns i).2 = true := by
  dsimp only [x64SlotAddrIns]
  split
  · exact ⟨cbMono cleanBound_nil (by omega), by
      simp [addrNoRip, constNoLab,
        show (some (RegOrRip.reg .rsp) != some RegOrRip.rip) = true from rfl]⟩
  · exact ⟨cbMono (cleanBound_single (instr_x64MoviI .r10 _)) (by omega), by
      simp [addrNoRip, constNoLab,
        show (some (RegOrRip.reg .rsp) != some RegOrRip.rip) = true from rfl]⟩

private theorem cleanBound_x64AddrPrepIns (a : AddrArg Reg64) :
    cleanBound 2 (x64AddrPrepIns a).1 ∧ addrNoRip (x64AddrPrepIns a).2 = true := by
  cases a with
  | imm _ =>
    exact ⟨cbMono (cleanBound_single (instr_x64MoviI .r10 _)) (by omega), by
      simp [x64AddrPrepIns, atReg, addrNoRip, constNoLab,
        show (some (RegOrRip.reg .r10) != some RegOrRip.rip) = true from rfl]⟩
  | baseDisp rb disp =>
    dsimp only [x64AddrPrepIns]
    split
    · exact ⟨cbMono cleanBound_nil (by omega), by simp [addrNoRip, constNoLab, reg_ne_rip_b]⟩
    · exact ⟨cleanBound_cons (instr_x64MoviI .r10 _) (cleanBound_single (by
          simp [instrStraightClean, opStraightClean, addrNoRip, constNoLab, reg_ne_rip_b])),
        by simp [addrNoRip, constNoLab,
             show (some (RegOrRip.reg .r10) != some RegOrRip.rip) = true from rfl]⟩
  | baseIdxDisp rb _ _ disp =>
    dsimp only [x64AddrPrepIns]
    split
    · exact ⟨cbMono cleanBound_nil (by omega), by simp [addrNoRip, constNoLab, reg_ne_rip_b]⟩
    · exact ⟨cleanBound_cons (instr_x64MoviI .r10 _) (cleanBound_single (by
          simp [instrStraightClean, opStraightClean, addrNoRip, constNoLab, reg_ne_rip_b])),
        by simp [addrNoRip, constNoLab,
             show (some (RegOrRip.reg .r10) != some RegOrRip.rip) = true from rfl]⟩

theorem cleanBound_x64VmovIns (w : SlotWidth) (vd vs : RegMm) :
    cleanBound 1 (x64VmovIns w vd vs) :=
  cleanBound_single (by simp [instrStraightClean, avxStraightClean, avxDstNoRip, avxRmNoRip])

theorem cleanBound_x64VmoviWithIns {tmp : RegMm} {w : SlotWidth} {vd : RegMm}
    {c : BitVec 512} {is : List _root_.Instr} (h : x64VmoviWithIns tmp w vd c = some is) :
    cleanBound 8 is := by
  have h128 : ∀ t r, instrStraightClean (x64Avx128I (.vmovIn .W64 (.xmm t) (.reg (q r)))) =
      true := fun _ _ => by simp [instrStraightClean, avxStraightClean, rm_reg]
  have hp0 : ∀ c', instrStraightClean (x64AvxI w (.vpternlogd (.avx (x64AvxRegOf w vd))
      (.avx (x64AvxRegOf w vd)) (.avx (x64AvxRegOf w vd)) (.int64 c'))) = true := fun _ => by
    simp [instrStraightClean, avxStraightClean, avxDstNoRip, avxRmNoRip, constNoLab]
  cases w with
  | w64 =>
    cases h
    exact cbMono
      (cleanBound_cons (instr_x64MoviI .r10 _) (cleanBound_single (h128 vd .r10))) (by omega)
  | w128 =>
    cases h
    exact cbMono (cleanBound_cons (instr_x64MoviI .r10 _)
      (cleanBound_cons (h128 vd .r10) (cleanBound_cons (by
          simp [instrStraightClean, avxStraightClean, avxDstNoRip, avxRmNoRip, constNoLab])
        (cleanBound_cons (instr_x64MoviI .r10 _) (cleanBound_cons (h128 tmp .r10)
          (cleanBound_single (by
            simp [instrStraightClean, avxStraightClean, avxDstNoRip, avxRmNoRip, constNoLab])))))))
      (by omega)
  | w256 | w512 =>
    dsimp only [x64VmoviWithIns] at h
    split at h
    · cases h; exact cbMono (cleanBound_single (hp0 0x00)) (by omega)
    · split at h
      · cases h; exact cbMono (cleanBound_single (hp0 0xFF)) (by omega)
      · cases h

private theorem instr_x64VmemI (isLoad : Bool) (w : SlotWidth) (v : RegMm) {addr : AddrExpr}
    (ha : addrNoRip addr = true) : instrStraightClean (x64VmemI isLoad w v addr) = true := by
  cases w <;> cases isLoad <;>
    simp [x64VmemI, instrStraightClean, avxStraightClean, rmNoRip, dstNoRip, avxRmNoRip,
      avxDstNoRip, ha]

theorem cleanBound_x64Vslot (isLoad : Bool) (w : SlotWidth) (i : Nat) (v : RegMm) :
    cleanBound 3 (if isLoad then x64VslotLdIns w v i else x64VslotStIns w i v) := by
  have ⟨hpre, ha⟩ := cleanBound_x64SlotAddrIns i
  cases isLoad <;>
    exact cleanBound_append hpre (cleanBound_single (instr_x64VmemI _ w v ha))

theorem cleanBound_x64Vmem (isLoad : Bool) {t : Ty} {v : RegMm} {a : AddrArg Reg64}
    {is : List _root_.Instr} {cl : FlagMask}
    (h : (if isLoad then x64VloadIns t v a else x64VstoreIns t v a) = some (is, cl)) :
    cleanBound 3 is := by
  have ⟨hpre, ha⟩ := cleanBound_x64AddrPrepIns a
  cases isLoad <;>
    (dsimp only [x64VloadIns, x64VstoreIns] at h
     cases hv : x64AddrValid a <;>
       simp only [hv, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte] at h
     · cases h
     · rcases Option.map_eq_some_iff.mp h with ⟨w, _, hp⟩; cases hp
       exact cleanBound_append hpre (cleanBound_single (instr_x64VmemI _ w v ha)))

theorem cleanBound_x64VopIns {sig rs : List Ty} (code : OpCode sig rs)
    (pas : Tup (PArg Reg64 RegMm CondCode) sig)
    (dsts : Tup (PDst Reg64 RegMm CondCode) rs)
    {is : List _root_.Instr} {cl : FlagMask}
    (h : x64VopIns code pas dsts = some (is, cl)) : cleanBound 32 is := by
  have hun : ∀ w t vd pa emit is',
      (∀ d s, instrStraightClean (emit d s) = true) →
      x64EmitUnaryIns w t vd pa emit = some is' → cleanBound 10 is' := by
    intro w t vd pa emit is' he hu
    cases pa with
    | vec va => cases hu; exact cbMono (cleanBound_single (he vd va)) (by omega)
    | imm ca =>
      rcases Option.map_eq_some_iff.mp hu with ⟨p, hp, rfl⟩
      exact cbMono
        (cleanBound_append (cleanBound_x64VmoviWithIns hp) (cleanBound_single (he vd vd)))
        (by omega)
    | gpr _ | flag _ => cases hu
  have hbip : ∀ w t vd pa pb emit is',
      (∀ d s, instrStraightClean (emit d s) = true) →
      x64EmitBinInPlaceIns w t vd pa pb emit = some is' → cleanBound 20 is' := by
    intro w t vd pa pb emit is' he hb
    have hvm := fun a b => cleanBound_x64VmovIns w a b
    cases pa with
    | gpr _ | flag _ => cases hb
    | vec va =>
      cases pb with
      | gpr _ | flag _ => cases hb
      | vec vb =>
        dsimp only [x64EmitBinInPlaceIns] at hb
        split at hb
        · cases hb; exact cbMono (cleanBound_single (he vd vb)) (by omega)
        · split at hb
          · cases hb; exact cbMono
              (cleanBound_append (cleanBound_append (hvm .mm15 vb) (hvm vd va))
                (cleanBound_single (he vd .mm15))) (by omega)
          · cases hb; exact cbMono
              (cleanBound_append (hvm vd va) (cleanBound_single (he vd vb))) (by omega)
      | imm cb =>
        rcases Option.map_eq_some_iff.mp hb with ⟨p, hp, rfl⟩
        exact cbMono
          (cleanBound_append (cleanBound_append (cleanBound_x64VmoviWithIns hp)
            (cleanBound_if_empty (b := va == vd) (hvm vd va))) (cleanBound_single (he vd .mm15)))
          (by omega)
    | imm ca =>
      cases pb with
      | gpr _ | flag _ => cases hb
      | vec vb =>
        rcases Option.map_eq_some_iff.mp hb with ⟨p, hp, rfl⟩
        have hp_b := cleanBound_x64VmoviWithIns hp
        split
        · exact cbMono (cleanBound_append (cleanBound_append (hvm .mm15 vb) hp_b)
            (cleanBound_single (he vd .mm15))) (by omega)
        · exact cbMono (cleanBound_append hp_b (cleanBound_single (he vd vb))) (by omega)
      | imm cb =>
        dsimp only [x64EmitBinInPlaceIns, bind, Option.bind] at hb
        cases h1 : x64VmoviIns w vd _ with
        | none => rw [h1] at hb; cases hb
        | some p1 =>
          rw [h1] at hb
          cases h2 : x64VmoviIns w .mm15 _ with
          | none => rw [h2] at hb; cases hb
          | some p2 =>
            simp only [h2, Option.some.injEq] at hb; subst hb
            exact cbMono
              (cleanBound_append (cleanBound_append (cleanBound_x64VmoviWithIns h1)
                (cleanBound_x64VmoviWithIns h2)) (cleanBound_single (he vd .mm15))) (by omega)
  have htern : ∀ w dst s2 s3 imm,
      cleanBound 1 [x64TernlogI w dst s2 s3 imm] := fun w dst s2 s3 imm =>
    cleanBound_single (by simp [instrStraightClean, avxStraightClean, avxDstNoRip, avxRmNoRip,
      constNoLab])
  have ht1 : ∀ w vd rx f0 f1 is',
      x64EmitTernlog1VecIns w vd rx f0 f1 = some is' → cleanBound 24 is' := by
    intro w vd rx f0 f1 is' h1
    dsimp only [x64EmitTernlog1VecIns, bind, Option.bind] at h1
    cases hk : x64VmoviIns w .mm15 (f1 ^^^ f0) with
    | none => rw [hk] at h1; cases h1
    | some pk =>
      rw [hk] at h1
      cases hf : x64VmoviIns w .mm15 f0 with
      | none => rw [hf] at h1; cases h1
      | some pf =>
        simp only [hf, Option.some.injEq] at h1; subst h1
        exact cbMono
          (cleanBound_append (cleanBound_append (cleanBound_append (cleanBound_append
            (cleanBound_if_empty (b := rx == vd) (cleanBound_x64VmovIns w vd rx))
            (cleanBound_x64VmoviWithIns hk)) (htern w vd .mm15 .mm15 0xC0))
            (cleanBound_x64VmoviWithIns hf)) (htern w vd .mm15 .mm15 0x3C)) (by omega)
  have hwide : ∀ t (dsts' : Tup (PDst Reg64 RegMm CondCode) [t])
      (f : SlotWidth → RegMm → Option (List _root_.Instr)),
      (∀ w vd is', f w vd = some is' → cleanBound 30 is') →
      (match x64VecSlotWidth t, dsts' with
      | some w, (.vec vd, ()) => if w == .w64 then none else (f w vd).map (·, maskNone)
      | _, _ => none) = some (is, cl) → cleanBound 32 is := by
    intro t dsts' f hf hw
    rcases dsts' with ⟨pd, ⟨⟩⟩
    cases hsw : x64VecSlotWidth t with
    | none => rw [hsw] at hw; cases hw
    | some w =>
      rw [hsw] at hw
      cases pd with
      | gpr _ | flag _ => cases hw
      | vec vd =>
        dsimp only at hw
        split at hw
        · cases hw
        · rcases Option.map_eq_some_iff.mp hw with ⟨is', his, hp⟩; cases hp
          exact cbMono (hf w vd is his) (by omega)
  cases code
  case copy t =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    dsimp only [x64VopIns] at h
    cases hsw : x64VecSlotWidth t with
    | none => rw [hsw] at h; cases h
    | some w =>
      rw [hsw] at h
      cases pd with
      | gpr _ | flag _ => cases h
      | vec vd =>
        cases pa with
        | gpr _ | flag _ => cases h
        | vec _ => cases h; exact cbMono (cleanBound_x64VmovIns _ _ _) (by omega)
        | imm _ =>
          rcases Option.map_eq_some_iff.mp h with ⟨is', hi, hp⟩; cases hp
          exact cbMono (cleanBound_x64VmoviWithIns hi) (by omega)
  case add t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; dsimp only [x64VopIns] at h
    split at h
    · cases h
    · refine hwide t dsts _ (fun w vd is' hp => ?_) h
      have hpa : ∀ s1 s2, instrStraightClean (x64AvxI w (.vpaddd (.avx (x64AvxRegOf w vd))
          (.avx (x64AvxRegOf w s1)) (.avx (x64AvxRegOf w s2)))) = true := fun _ _ => by
        simp [instrStraightClean, avxStraightClean, avxDstNoRip, avxRmNoRip]
      cases pa with
      | gpr _ | flag _ => cases pb <;> cases hp
      | vec va =>
        cases pb with
        | gpr _ | flag _ => cases hp
        | vec vb => cases hp; exact cbMono (cleanBound_single (hpa va vb)) (by omega)
        | imm _ =>
          rcases Option.map_eq_some_iff.mp hp with ⟨p, hmv, rfl⟩
          exact cbMono
            (cleanBound_append (cleanBound_x64VmoviWithIns hmv) (cleanBound_single (hpa va .mm15)))
            (by omega)
      | imm ca =>
        cases pb with
        | gpr _ | flag _ => cases hp
        | vec vb =>
          rcases Option.map_eq_some_iff.mp hp with ⟨p, hmv, rfl⟩
          exact cbMono
            (cleanBound_append (cleanBound_x64VmoviWithIns hmv) (cleanBound_single (hpa .mm15 vb)))
            (by omega)
        | imm cb =>
          dsimp only [x64EmitVpadddIns, bind, Option.bind] at hp
          cases h1 : x64VmoviIns w vd _ with
          | none => rw [h1] at hp; cases hp
          | some p1 =>
            rw [h1] at hp
            cases h2 : x64VmoviIns w .mm15 _ with
            | none => rw [h2] at hp; cases hp
            | some p2 =>
              simp only [h2, Option.some.injEq] at hp; subst hp
              exact cbMono (cleanBound_append
                (cleanBound_append (cleanBound_x64VmoviWithIns (tmp := .mm14) h1)
                  (cleanBound_x64VmoviWithIns (tmp := .mm14) h2))
                (cleanBound_single (hpa vd .mm15))) (by omega)
  case and t | or t | xor t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    dsimp only [x64VopIns, x64WideTernlogBinIns] at h
    cases hsw : x64VecSlotWidth t with
    | none => rw [hsw] at h; cases h
    | some w =>
      rw [hsw] at h
      cases pd with
      | gpr _ | flag _ => cases h
      | vec vd =>
        dsimp only at h
        split at h
        · cases h
        · rcases Option.map_eq_some_iff.mp h with ⟨is', his, hp⟩; cases hp
          exact cbMono (hbip w t vd pa pb _ is (fun d s => by
            simp [instrStraightClean, avxStraightClean, avxDstNoRip, avxRmNoRip, constNoLab])
            his) (by omega)
  case not t =>
    rcases pas with ⟨pa, ⟨⟩⟩; dsimp only [x64VopIns] at h
    exact hwide t dsts _ (fun w vd is' hp => cbMono
      (hun w t vd pa _ is' (fun d s => by
        simp [instrStraightClean, avxStraightClean, avxDstNoRip, avxRmNoRip, constNoLab]) hp)
      (by omega)) h
  case ternlog t imm =>
    rcases pas with ⟨pa, pb, pc, ⟨⟩⟩; dsimp only [x64VopIns] at h
    refine hwide t dsts _ (fun w vd is' hp => ?_) h
    have hvm := fun a b => cleanBound_x64VmovIns w a b
    have hstg : ∀ va vb pimm, cleanBound 8 pimm → cleanBound 12 (if va == vd then
        pimm ++ [x64TernlogI w vd vb .mm14 imm]
      else if vb != vd then pimm ++ x64VmovIns w vd va ++ [x64TernlogI w vd vb .mm14 imm]
      else pimm ++ x64VmovIns w .mm15 vd ++ x64VmovIns w vd va ++
        [x64TernlogI w vd .mm15 .mm14 imm]) := fun va vb pimm hpi => by
      split
      · exact cbMono (cleanBound_append hpi (htern w vd vb .mm14 imm)) (by omega)
      · split
        · exact cbMono
            (cleanBound_append (cleanBound_append hpi (hvm vd va)) (htern w vd vb .mm14 imm))
            (by omega)
        · exact cbMono (cleanBound_append (cleanBound_append
            (cleanBound_append hpi (hvm .mm15 vd)) (hvm vd va)) (htern w vd .mm15 .mm14 imm))
            (by omega)
    cases pa with
    | gpr _ | flag _ => cases pb <;> cases pc <;> cases hp
    | vec va =>
      cases pb with
      | gpr _ | flag _ => cases pc <;> cases hp
      | vec vb =>
        cases pc with
        | gpr _ | flag _ => cases hp
        | vec vc =>
          dsimp only [x64EmitTernlogIns] at hp
          split at hp
          · cases hp; exact cbMono (htern w vd vb vc imm) (by omega)
          · split at hp
            · cases hp; exact cbMono
                (cleanBound_append (hvm vd va) (htern w vd vb vc imm)) (by omega)
            · cases hp; exact cbMono (cleanBound_append
                (cleanBound_append (hvm .mm15 vd) (hvm vd va))
                (htern w vd (if vb == vd then .mm15 else vb) (if vc == vd then .mm15 else vc) imm))
                (by omega)
        | imm cc =>
          rcases Option.map_eq_some_iff.mp hp with ⟨p, hmv, rfl⟩
          exact cbMono (hstg va vb p (cleanBound_x64VmoviWithIns hmv)) (by omega)
      | imm cb =>
        cases pc with
        | gpr _ | flag _ => cases hp
        | vec vc =>
          rcases Option.map_eq_some_iff.mp hp with ⟨p, hmv, rfl⟩
          have hp_b := cleanBound_x64VmoviWithIns hmv
          split
          · exact cbMono (cleanBound_append hp_b (htern w vd .mm14 vc imm)) (by omega)
          · split
            · exact cbMono (cleanBound_append (cleanBound_append hp_b
                (hvm vd va)) (htern w vd .mm14 vc imm)) (by omega)
            · exact cbMono (cleanBound_append (cleanBound_append
                (cleanBound_append hp_b (hvm .mm15 vd)) (hvm vd va))
                (htern w vd .mm14 .mm15 imm)) (by omega)
        | imm _ => exact cbMono (ht1 _ _ _ _ _ _ hp) (by omega)
    | imm ca =>
      cases pb with
      | gpr _ | flag _ => cases pc <;> cases hp
      | vec vb =>
        cases pc with
        | gpr _ | flag _ => cases hp
        | imm _ => exact cbMono (ht1 _ _ _ _ _ _ hp) (by omega)
        | vec vc =>
          rcases Option.map_eq_some_iff.mp hp with ⟨p, hmv, rfl⟩
          have hp_b := cleanBound_x64VmoviWithIns hmv
          split
          · exact cbMono (cleanBound_append hp_b (htern w vd vb vc imm)) (by omega)
          · exact cbMono (cleanBound_append
              (cleanBound_append (hvm .mm15 vd) hp_b)
              (htern w vd (if vb == vd then .mm15 else vb) (if vc == vd then .mm15 else vc) imm))
              (by omega)
      | imm cb =>
        cases pc with
        | gpr _ | flag _ => cases hp
        | vec vc => exact cbMono (ht1 _ _ _ _ _ _ hp) (by omega)
        | imm cc => exact cbMono (cleanBound_x64VmoviWithIns hp) (by omega)
  case rotr t | lshr t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    dsimp only [x64VopIns, x64UniformShiftI32Ins] at h
    split at h
    · cases h
    · cases hw : x64VecSlotWidth t with
      | none => rw [hw] at h; cases h
      | some w =>
        rw [hw] at h; cases pb <;> cases pd <;> try cases h
        rename_i cb vd
        dsimp only at h
        split at h
        · cases h
        · dsimp only [Option.bind] at h
          cases hc : x64UniformI32Splat? t cb with
          | none => simp [hc] at h
          | some cnt =>
            rw [hc] at h; dsimp only at h
            rcases Option.map_eq_some_iff.mp h with ⟨is', his, hp⟩; cases hp
            exact cbMono (hun _ _ _ pa _ is (fun d s => by
              simp [instrStraightClean, avxStraightClean, avxDstNoRip, avxRmNoRip, constNoLab])
              his) (by omega)
  case shufd t _ =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    dsimp only [x64VopIns] at h
    split at h
    · cases h
    · cases pd <;> try cases h
      rcases Option.map_eq_some_iff.mp h with ⟨is', his, hp⟩; cases hp
      exact cbMono (hun _ t _ pa _ is (fun d s => by
        simp [instrStraightClean, avxStraightClean, avxDstNoRip, avxRmNoRip, constNoLab]) his)
        (by omega)
  case shufb t | alignr t _ | blendw t _ | fadd t | fsub t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    have hbin128 : ∀ (ok : Bool) emit,
        (∀ d s, instrStraightClean (emit d s) = true) →
        x64BinInPlace128Ins ok (pa, pb, ()) (pd, ()) emit = some (is, cl) →
        cleanBound 32 is := fun ok emit he hbp => by
      dsimp only [x64BinInPlace128Ins] at hbp
      split at hbp
      · cases hbp
      · cases pd <;> try cases hbp
        rcases Option.map_eq_some_iff.mp hbp with ⟨is', his, hp⟩; cases hp
        exact cbMono (hbip .w128 t _ pa pb emit is he his) (by omega)
    all_goals
      exact hbin128 _ _ (fun d s => by
        simp [instrStraightClean, avxStraightClean, avxDstNoRip, avxRmNoRip, constNoLab]) h
  case mkpair a b =>
    have hl32 : ∀ rd' arg is', x64LoadI32ToGprIns rd' arg = some is' → cleanBound 1 is' := by
      intro rd' arg is' hl
      cases arg <;> cases hl
      · exact cleanBound_single rfl
      · exact cleanBound_single (instr_x64MoviI _ _)
    have hl64 : ∀ {t' : Ty} (ht' : t'.size = 64) vd' arg is',
        x64LoadSubVec64Ins ht' vd' arg = some is' → cleanBound 2 is' := by
      intro t' ht' vd' arg is' hl
      cases arg <;> cases hl
      · exact cbMono (cleanBound_single rfl) (by omega)
      · exact cleanBound_cons (instr_x64MoviI .r10 _)
          (cleanBound_single (by simp [instrStraightClean, avxStraightClean, rm_reg]))
    dsimp only [x64VopIns, x64EmitMkpairIns] at h
    split at h
    · rcases Option.bind_eq_some_iff.mp h with ⟨la, h1, h⟩
      rcases Option.bind_eq_some_iff.mp h with ⟨lb, h2, h⟩
      cases h
      exact cbMono (cleanBound_append (cleanBound_append (hl32 _ _ _ h1) (hl32 _ _ _ h2))
        (cleanBound_cons (by simp [instrStraightClean, opStraightClean, dst_reg, scNoLab,
            constNoLab])
          (cleanBound_cons (by simp [instrStraightClean, opStraightClean, dst_reg, opnd_reg])
            (cleanBound_single (by simp [instrStraightClean, avxStraightClean, rm_reg])))))
        (by omega)
    · split at h
      · rcases Option.bind_eq_some_iff.mp h with ⟨la, h1, h⟩
        rcases Option.bind_eq_some_iff.mp h with ⟨lb, h2, h⟩
        cases h
        exact cbMono (cleanBound_append (cleanBound_append (hl64 _ _ _ _ h1) (hl64 _ _ _ _ h2))
          (cleanBound_cons (by simp [instrStraightClean, avxStraightClean, avxDstNoRip,
              avxRmNoRip, constNoLab]) (htern .w128 _ .mm14 .mm14 0xFE))) (by omega)
      · cases h
    · cases h
  case unpair a b =>
    dsimp only [x64VopIns, x64EmitUnpairIns] at h
    split at h
    · split at h
      · cases h
      · rcases Option.map_eq_some_iff.mp h with ⟨lp, hp, h⟩; cases h
        have hlp : cleanBound 2 lp := by
          split at hp
          · cases hp; exact cbMono (cleanBound_single
              (by simp [instrStraightClean, avxStraightClean, dst_reg])) (by omega)
          · cases hp; exact cbMono (cleanBound_single (instr_x64MoviI .r10 _)) (by omega)
          · cases hp
        exact cbMono (cleanBound_append hlp (cleanBound_cons rfl (cleanBound_cons
          (by simp [instrStraightClean, opStraightClean, dst_reg, scNoLab, constNoLab])
          (cleanBound_single rfl)))) (by omega)
    · split at h
      · cases h
      · split at h
        · split at h
          · cases h; exact cbMono (cleanBound_cons
              (by simp [instrStraightClean, avxStraightClean, avxDstNoRip, avxRmNoRip,
                constNoLab]) (cleanBound_cons rfl (cleanBound_single rfl))) (by omega)
          · cases h; exact cbMono (cleanBound_append
              (cleanBound_cons (instr_x64MoviI .r10 _)
                (cleanBound_single (by simp [instrStraightClean, avxStraightClean, rm_reg])))
              (cleanBound_cons (instr_x64MoviI .r10 _)
                (cleanBound_single (by simp [instrStraightClean, avxStraightClean, rm_reg]))))
              (by omega)
          · cases h
        · cases h
    · cases h
  all_goals cases h

end LeanQbe.T.Vll
