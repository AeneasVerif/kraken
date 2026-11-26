module

public import LeanQbe.T.Amd64.VllFactorX640
public import LeanQbe.T.Amd64.VllFactorX641
import LeanQbe.T.Amd64.VllFactorX64Zero
import LeanQbe.T.Amd64.TargLemmas
import LeanQbe.T.AbiLemmas
import LeanQbe.T.TargetLemmas
import Kraken.X64.Regs

/-!
# BedrockMach SysV x86-64 Policy, Target, and Soundness (`Amd64.VllFactorX642`)

Constructs and verifies the `BedrockMach` L1 SysV x86-64 lowering policy and target:
end-to-end semantic correspondence with `x64Target`:
* `vllX64PolicySpec : VllPolicySpec x64Arch vllX64NativeHooks`, `vllX64Policy`, `vllX64Target`,
  and `vllX64LabelClean`.
  `compileFn`, `compile`, and `compileModule` equality under `asmX64List`.
  (`vllX64_execBody_to_x64`), and bidirectional `vllX64Target.FnSpec ↔ x64Target.FnSpec` bridges.

Zero `Arm64` / `Kraken.AArch64` imports, zero `@[expose]` on proof theorems/lemmas.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64

open LeanQbe.T
open LeanQbe.T.Vll

/-! ## 1. Compare Flags (`x64Arch_cmpFlags_spec`) and Native Lifting Bridges -/

private theorem subFlags_cf_eq {n : Nat} (x y : BitVec n) :
    ((x - y).unsigned != x.unsigned - y.unsigned) = x.ult y := by
  simp only [BitVec.unsigned, BitVec.ult]
  have hx := x.isLt; have hy := y.isLt
  have hsub : (x - y).toNat = (2 ^ n - y.toNat + x.toNat) % 2 ^ n := BitVec.toNat_sub x y
  by_cases hlt : x.toNat < y.toNat
  · have hmod : (2 ^ n - y.toNat + x.toNat) % 2 ^ n = 2 ^ n + x.toNat - y.toNat := by
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [hsub, hmod, decide_eq_true hlt]; simp only [bne_iff_ne, ne_eq]; omega
  · have hmod : (2 ^ n - y.toNat + x.toNat) % 2 ^ n = x.toNat - y.toNat := by
      have : 2 ^ n - y.toNat + x.toNat = 2 ^ n + (x.toNat - y.toNat) := by omega
      rw [this, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    rw [hsub, hmod, decide_eq_false hlt, bne_eq_false_iff_eq]; omega

private theorem subFlags_zf_eq {n : Nat} (x y : BitVec n) (af : Bool) :
    ((StatusFlags.from_result (x - y)
      { cf := (x - y).unsigned != x.unsigned - y.unsigned, af := af,
        of := (x - y).signed != x.signed - y.signed }).zf) = decide (x = y) := by
  simp only [StatusFlags.from_result, BitVec.zero]
  by_cases heq : x = y
  · subst heq; simp [BitVec.sub_self]
  · have hne : x - y ≠ 0#n := fun h => by
      have he : x = y := by rw [← BitVec.sub_add_cancel x y, h, BitVec.zero_add]
      exact heq he
    simp [heq, hne]

private theorem two_pow_coe_w (w : Vll.Width) :
    ((2 ^ w.bits : Nat) : Int) = 2 * ((2 ^ (w.bits - 1) : Nat) : Int) ∧
      ((2 ^ (w.bits - 1) : Nat) : Int) = (2 : Int) ^ (w.bits - 1) := by
  cases w <;> exact ⟨rfl, rfl⟩

private theorem int_add_emod_self_w (d m : Int) : (d + m) % m = d % m := by
  rw [Int.add_emod, Int.emod_self, Int.add_zero, Int.emod_emod]

private theorem bmod_two_pow_w (m : Nat) (H : Int) (hm : (m : Int) = 2 * H) (hpos : 0 < H)
    (d : Int) (hd1 : -(2 * H) < d) (hd2 : d < 2 * H) :
    (decide (d.bmod m < 0) != (d.bmod m != d)) = decide (d < 0) := by
  have hpow2 : ((m : Int) + 1) / 2 = H := by omega
  have hbmod : d.bmod m = if d < -H then d + 2 * H else if H ≤ d then d - 2 * H else d := by
    rw [Int.bmod_def, hpow2, hm]
    by_cases hlt : d < -H
    · have hmod : d % (2 * H) = d + 2 * H := by
        rw [← int_add_emod_self_w d (2 * H)]; exact Int.emod_eq_of_lt (by omega) (by omega)
      simp only [hlt, ↓reduceIte, hmod]; split
      · rfl
      · exact absurd ‹_› (by omega)
    · by_cases hge : H ≤ d
      · have hmod : d % (2 * H) = d := Int.emod_eq_of_lt (by omega) (by omega)
        simp only [hlt, hge, ↓reduceIte, hmod]; split
        · exact absurd ‹_› (by omega)
        · rfl
      · by_cases h0 : 0 ≤ d
        · have hmod : d % (2 * H) = d := Int.emod_eq_of_lt h0 (by omega)
          simp only [hlt, hge, ↓reduceIte, hmod]; split
          · rfl
          · exact absurd ‹_› (by omega)
        · have hmod : d % (2 * H) = d + 2 * H := by
            rw [← int_add_emod_self_w d (2 * H)]; exact Int.emod_eq_of_lt (by omega) (by omega)
          simp only [hlt, hge, ↓reduceIte, hmod]; split
          · exact absurd ‹_› (by omega)
          · omega
  rw [hbmod]
  by_cases hlt : d < -H
  · have hne : d + 2 * H ≠ d := by omega
    simp only [hlt, ↓reduceIte, show ¬ (d + 2 * H < 0) by omega, decide_false, Bool.false_bne]
    simpa [show d < 0 by omega] using hne
  · by_cases hge : H ≤ d
    · have hne : d - 2 * H ≠ d := by omega
      simp only [hlt, hge, ↓reduceIte, show d - 2 * H < 0 by omega, decide_true, Bool.true_bne]
      simpa [show ¬ d < 0 by omega] using hne
    · simp only [hlt, hge, ↓reduceIte, bne_self_eq_false, Bool.bne_false]

/-- Proof of `cmpFlags_spec` for `x64CmpFlags` across all 10 `CmpOp` comparisons. -/
theorem x64Arch_cmpFlags_spec :
    ∀ co cc (w : Vll.Width) (a b : BitVec w.bits) f,
      vllX64NativeHooks.condOfCmp? co = some cc →
      x64Arch.evalCond (x64Arch.cmpFlags w a b f) cc = co.evalBits a b := by
  intro co cc w a b f hco
  simp only [vllX64NativeHooks, Function.comp_apply, Option.some.injEq] at hco; subst hco
  show (condOf co).interp (x64CmpFlags w a b f) = co.evalBits a b
  have hcf : (x64CmpFlags w a b f).cf = a.ult b := subFlags_cf_eq a b
  have hzf : (x64CmpFlags w a b f).zf = decide (a = b) := by
    simpa [x64CmpFlags] using subFlags_zf_eq a b _
  have hl : ((x64CmpFlags w a b f).sf != (x64CmpFlags w a b f).of) = a.slt b := by
    simp only [x64CmpFlags, StatusFlags.from_result, BitVec.signed, BitVec.slt]
    rw [BitVec.msb_eq_toInt, BitVec.toInt_sub]
    obtain ⟨hpow, hcoe⟩ := two_pow_coe_w w
    have hpos : (0 : Int) < ((2 ^ (w.bits - 1) : Nat) : Int) := by
      exact_mod_cast Nat.pow_pos (a := 2) (n := w.bits - 1) (by decide)
    have ha := @BitVec.le_toInt w.bits a; have ha2 := @BitVec.toInt_lt w.bits a
    have hb := @BitVec.le_toInt w.bits b; have hb2 := @BitVec.toInt_lt w.bits b
    rw [← hcoe] at ha ha2 hb hb2
    have heq := bmod_two_pow_w (2 ^ w.bits) ((2 ^ (w.bits - 1) : Nat) : Int) hpow hpos
      (a.toInt - b.toInt) (by omega) (by omega)
    by_cases hlt : a.toInt < b.toInt
    · simpa [hlt, show a.toInt - b.toInt < 0 by omega] using heq
    · simpa [hlt, show ¬ a.toInt - b.toInt < 0 by omega] using heq
  have hbeq : ((x64CmpFlags w a b f).sf == (x64CmpFlags w a b f).of) =
      !((x64CmpFlags w a b f).sf != (x64CmpFlags w a b f).of) := by
    cases (x64CmpFlags w a b f).sf <;> cases (x64CmpFlags w a b f).of <;> rfl
  have hne : (!decide (a = b)) = decide (a ≠ b) := by by_cases h : a = b <;> simp [h]
  have hule : (a.ult b || decide (a = b)) = a.ule b := by
    simp only [BitVec.ult, BitVec.ule]
    by_cases hlt : a.toNat < b.toNat <;> by_cases hle : a.toNat ≤ b.toNat <;> by_cases heq : a = b
    all_goals first | (simp [hlt, hle, heq]; done) | (subst heq; omega) |
      (exact absurd (BitVec.eq_of_toNat_eq (by omega)) heq) | omega
  have hugt : (!a.ult b && !decide (a = b)) = b.ult a := by
    simp only [BitVec.ult]
    by_cases h1 : a.toNat < b.toNat <;> by_cases h2 : b.toNat < a.toNat <;> by_cases heq : a = b
    all_goals first | (simp [h1, h2, heq]; done) | (subst heq; omega) |
      (exact absurd (BitVec.eq_of_toNat_eq (by omega)) heq) | omega
  have huge : (!a.ult b) = b.ule a := by
    simp only [BitVec.ult, BitVec.ule]
    by_cases h1 : a.toNat < b.toNat <;> by_cases h2 : b.toNat ≤ a.toNat <;>
      first | (simp [h1, h2]; done) | omega
  have hsle : (a.slt b || decide (a = b)) = a.sle b := by
    simp only [BitVec.slt, BitVec.sle]
    by_cases h1 : a.toInt < b.toInt <;> by_cases h2 : a.toInt ≤ b.toInt <;> by_cases heq : a = b
    all_goals first | (simp [h1, h2, heq]; done) | (subst heq; omega) |
      (exact absurd (BitVec.eq_of_toInt_eq (by omega)) heq) | omega
  have hsgt : (!decide (a = b) && !a.slt b) = b.slt a := by
    simp only [BitVec.slt]
    by_cases h1 : a.toInt < b.toInt <;> by_cases h2 : b.toInt < a.toInt <;> by_cases heq : a = b
    all_goals first | (simp [h1, h2, heq]; done) | (subst heq; omega) |
      (exact absurd (BitVec.eq_of_toInt_eq (by omega)) heq) | omega
  have hsge : (!a.slt b) = b.sle a := by
    simp only [BitVec.slt, BitVec.sle]
    by_cases h1 : a.toInt < b.toInt <;> by_cases h2 : b.toInt ≤ a.toInt <;>
      first | (simp [h1, h2]; done) | omega
  cases co <;> simp only [condOf, CondCode.interp, CmpOp.evalBits, hcf, hzf, hbeq, hl]
  · exact hne
  · exact hule
  · exact hugt
  · exact huge
  · exact hsle
  · exact hsgt
  · exact hsge

private theorem clearFlags_x64 : ∀ (f : StatusFlags) (cc : CondCode),
    FlagMask.disjoint (x64Arch.condReads cc) FlagMask.all = true →
    x64Arch.evalCond x64Arch.clearFlagsVal cc = x64Arch.evalCond f cc :=
  clearFlags_frame_of_nonzero (A := x64Arch) fun (cc : CondCode) => by cases cc <;> decide

private theorem krakenSim_gpr_eq {sv' : MachSt x64Arch} {sk' : MachineData}
    (h : KrakenSim (machToKraken sv') sk') (r : Reg64) : sv'.gpr r = sk'.regs.get64 r :=
  (regsOfFn_get64 sv'.gpr r).symm.trans (h.1 r)

private theorem krakenSim_vreg_eq {sv' : MachSt x64Arch} {sk' : MachineData}
    (h : KrakenSim (machToKraken sv') sk') (vr : RegMm) : sv'.vreg vr = sk'.zmms.get512 vr :=
  (zmmsOfFn_get512 sv'.vreg vr).symm.trans (h.2.1 vr)

private theorem krakenSim_mem_eq {sv' : MachSt x64Arch} {sk' : MachineData}
    (h : KrakenSim (machToKraken sv') sk') : sv'.mem = sk'.dmem := h.2.2.1

private theorem krakenSim_evalCond_eq {sv' : MachSt x64Arch} {sk' : MachineData}
    (h : KrakenSim (machToKraken sv') sk') (cc : CondCode) :
    (vllMach x64Arch).evalCond sv' cc = x64Mach.evalCond sk' cc := by
  have hcf : sv'.flags.cf = sk'.status.cf := h.2.2.2.1
  have hpf : sv'.flags.pf = sk'.status.pf := h.2.2.2.2.1
  have hzf : sv'.flags.zf = sk'.status.zf := h.2.2.2.2.2.1
  have hsf : sv'.flags.sf = sk'.status.sf := h.2.2.2.2.2.2.1
  have hof : sv'.flags.of = sk'.status.of := h.2.2.2.2.2.2.2
  change CondCode.interp cc sv'.flags = CondCode.interp cc sk'.status
  cases cc <;> dsimp only [CondCode.interp] <;>
    first | rw [hzf, hsf, hof] | rw [hcf, hzf] | rw [hsf, hof] |
      rw [hcf] | rw [hpf] | rw [hzf] | rw [hsf] | rw [hof]

private theorem reg64_eq_of_beq {x y : Reg64} (h : (x == y) = true) : x = y := by
  cases x <;> cases y <;> first | rfl | cases h

private theorem condCode_eq_of_beq {x y : CondCode} (h : (x == y) = true) : x = y := by
  cases x <;> cases y <;> first | rfl | cases h

private theorem parg_trel2 {s : MachSt x64Arch} {t1 t2 : Ty}
    {pa : PArg Reg64 RegMm CondCode t1} {pb : PArg Reg64 RegMm CondCode t2}
    {va : Val t1} {vb : Val t2}
    (h : TRel (as := [t1, t2]) ((vllMach x64Arch).PArgHolds s) (pa, pb, ()) (va, vb, ())) :
    (vllMach x64Arch).PArgHolds s t1 pa va ∧ (vllMach x64Arch).PArgHolds s t2 pb vb := by
  cases h with | cons h1 h2 => cases h2 with | cons h3 _ => exact ⟨h1, h3⟩

private theorem machToKraken_gpr_eq (s : MachSt x64Arch) :
    x64Mach.getGpr (machToKraken s) = s.gpr :=
  funext (regsOfFn_get64 s.gpr)

private theorem machToKraken_mem_eq (s : MachSt x64Arch) :
    x64Mach.mem (machToKraken s) = s.mem := rfl

private theorem pArgHolds_to_x64Mach {sv : MachSt x64Arch} {t : Ty}
    {pa : PArg Reg64 RegMm CondCode t} {v : Val t}
    (h : (vllMach x64Arch).PArgHolds sv t pa v) : x64Mach.PArgHolds (machToKraken sv) t pa v := by
  dsimp only [Machine.PArgHolds, vllMach, x64Mach, machToKraken] at h ⊢
  cases pa with
  | gpr r => simpa [regsOfFn_get64] using h
  | vec vr => simpa [zmmsOfFn_get512] using h
  | flag _ | imm _ => exact h

private theorem tRel_pArgHolds_to_x64Mach {sv : MachSt x64Arch} :
    ∀ {ts : List Ty} {pas : Tup (PArg Reg64 RegMm CondCode) ts} {vs : Tup Val ts},
      TRel ((vllMach x64Arch).PArgHolds sv) pas vs →
      TRel (x64Mach.PArgHolds (machToKraken sv)) pas vs
  | [], (), (), .nil => .nil
  | _ :: _, (_, _), (_, _), .cons h1 h2 =>
    .cons (pArgHolds_to_x64Mach h1) (tRel_pArgHolds_to_x64Mach h2)

private theorem pDstHolds_of_x64Mach {sv' : MachSt x64Arch} {sk' : MachineData}
    (hsim : KrakenSim (machToKraken sv') sk') {t : Ty}
    {pd : PDst Reg64 RegMm CondCode t} {v : Val t}
    (h : x64Mach.PDstHolds sk' t pd v) : (vllMach x64Arch).PDstHolds sv' t pd v := by
  dsimp only [Machine.PDstHolds, vllMach, x64Mach] at h ⊢
  cases pd with
  | gpr r => simpa [krakenSim_gpr_eq hsim r] using h
  | vec vr => simpa [krakenSim_vreg_eq hsim vr] using h
  | flag cc => exact (krakenSim_evalCond_eq hsim cc).trans h

private theorem tRel_pDstHolds_of_x64Mach {sv' : MachSt x64Arch} {sk' : MachineData}
    (hsim : KrakenSim (machToKraken sv') sk') :
    ∀ {ts : List Ty} {dsts : Tup (PDst Reg64 RegMm CondCode) ts} {vs : Tup Val ts},
      TRel (x64Mach.PDstHolds sk') dsts vs → TRel ((vllMach x64Arch).PDstHolds sv') dsts vs
  | [], (), (), .nil => .nil
  | _ :: _, (_, _), (_, _), .cons h1 h2 =>
    .cons (pDstHolds_of_x64Mach hsim h1) (tRel_pDstHolds_of_x64Mach hsim h2)

private theorem flagCmpOk_of_x64Mach {sv' : MachSt x64Arch} {sk' : MachineData}
    (hsim : KrakenSim (machToKraken sv') sk') {w : Nat} {a b : BitVec w} {eqNe : Bool}
    (h : FlagCmpOk x64Mach x64Gpr sk' a b eqNe) :
    FlagCmpOk (vllMach x64Arch) (vllGprIsaOfHooks x64Arch vllX64NativeHooks) sv' a b eqNe :=
  fun co cc hco hcc => (krakenSim_evalCond_eq hsim cc).trans (h co cc hco hcc)

private theorem x64Native_fallsTo_of_clean {vh : VllHost x64Arch} {k : Nat}
    {ds : List _root_.Directive} {gClob : List Reg64} {vClob : List RegMm} {fClob : FlagMask}
    {sv : MachSt x64Arch} {Q : MachSt x64Arch → Prop} {Qk : MachineData → Prop}
    {post : Config x64Arch → Prop}
    (hclean : ∀ d ∈ ds, dirStraightClean d = true) (hlen : ds.length < 2 ^ 61)
    (hx : ∀ (kh : Host),
      x64Mach.FallsTo x64CondReads kh 0 ds gClob vClob fClob (machToKraken sv) Qk
        (fun st => st.pc = @Host.addrOf kh ds.length ∧ Qk st.data ∧
          x64Mach.Frame x64CondReads (machToKraken sv) st.data gClob vClob fClob))
    (hQ : ∀ sv' sk', KrakenSim (machToKraken sv') sk' → Qk sk' → Q sv') :
    (vllMach x64Arch).FallsTo x64CondReads vh k (ds.map .native) gClob vClob fClob sv Q post :=
  x64Mach_fallsTo_to_vll hclean hlen hx hQ

private theorem gprHolds_to_bits {v : BitVec 64} {w : Vll.Width} {x : BitVec w.bits}
    (h : GprHolds v (.bits w.bits) x) : v.setWidth w.bits = x := h.2

private theorem writeSubX64_w32 (old : BitVec 64) (v : BitVec 32) :
    writeSubX64 .w32 old v = v.setWidth 64 := rfl

private theorem vllX64WidthOfBits_eq {n : Nat} {w : Vll.Width}
    (hw : vllX64WidthOfBits? n = some w) : n = w.bits := by
  unfold vllX64WidthOfBits? at hw; split at hw <;> cases hw <;> rfl

private theorem nativePair_some_iff {x : Option (List _root_.Directive × FlagMask)}
    {c : List (Instr x64Arch)} {clob : FlagMask}
    (h : x64NativePair x = some (c, clob)) :
    ∃ ds, x = some (ds, clob) ∧ c = ds.map (Instr.native (A := x64Arch)) := by
  cases x with
  | none => cases h
  | some p => cases h; exact ⟨p.1, rfl, rfl⟩

/-! ## 2. Verified `vllX64PolicySpec`, `vllX64Policy`, `vllX64Target`, & `vllX64LabelClean` -/

private theorem vllX64VecTarget :
    VecTarget (vllMach x64Arch) vllX64Vec x64Arch.condReads x64Arch.abi.sp
      x64Arch.abi.scratch x64Arch.abi.spOk where
  vecScratch_disj := x64_vecSpec.vecScratch_disj
  vecArgRegs_nodup := x64_vecSpec.vecArgRegs_nodup
  vecRetRegs_nodup := x64_vecSpec.vecRetRegs_nodup
  abiVec_slot := x64_vecSpec.abiVec_slot
  vmov_spec {h k w vd vs s post} := by
    have hcl := clean_small_of_cleanBound (cleanBound_x64VmovIns w vd vs) (by decide)
    refine x64Native_fallsTo_of_clean hcl.1 hcl.2
      (fun kh => x64_vecSpec.vmov_spec (s := machToKraken s)) fun sv' sk' hsim hq => ?_
    dsimp only [vllMach, x64Mach, machToKraken] at hq ⊢
    exact ⟨by simpa [krakenSim_vreg_eq hsim vd, zmmsOfFn_get512] using hq.1,
      (krakenSim_mem_eq hsim).trans hq.2⟩
  vmovi_spec {h k w vd c code s post} hmv hnd := by
    rcases Option.map_eq_some_iff.mp hmv with ⟨ds, hds, rfl⟩
    obtain ⟨is, his, rfl⟩ := emitCleanOpt_eq_some.mp hds
    have hcl := clean_small_of_cleanBound (cleanBound_x64VmoviWithIns his) (by decide)
    refine x64Native_fallsTo_of_clean hcl.1 hcl.2
      (fun kh => x64_vecSpec.vmovi_spec hds hnd) fun sv' sk' hsim hq => ?_
    dsimp only [vllMach, x64Mach] at hq ⊢
    exact ⟨by simpa [krakenSim_vreg_eq hsim vd] using hq.1,
      (krakenSim_mem_eq hsim).trans hq.2⟩
  vslotSt_spec {h k w i vr s G post} hvr _ hm := by
    have hcl := clean_small_of_cleanBound (cleanBound_x64Vslot false w i vr) (by decide)
    have hmk : x64Mach.mem (machToKraken s) =⋆
        region (x64Mach.getGpr (machToKraken s) x64Frame.sp + BitVec.ofNat 64 (8 * i))
          (8 * w.slots) ⋆ G := by
      dsimp only [vllMach, x64Mach, x64Frame, machToKraken, x64Arch] at hm ⊢
      simpa [regsOfFn_get64] using hm
    refine x64Native_fallsTo_of_clean hcl.1 hcl.2
      (fun kh => x64_vecSpec.vslotSt_spec (s := machToKraken s) hvr trivial hmk) ?_
    intro sv' sk' hsim hq
    dsimp only [vllMach, x64Mach, x64Frame, machToKraken, x64Arch] at hq ⊢
    simpa [krakenSim_mem_eq hsim, regsOfFn_get64, zmmsOfFn_get512] using hq
  vslotLd_spec {h k w i vd bv s G post} hvd _ hm := by
    have hcl := clean_small_of_cleanBound (cleanBound_x64Vslot true w i vd) (by decide)
    have hmk : x64Mach.mem (machToKraken s) =⋆
        array64 (x64Mach.getGpr (machToKraken s) x64Frame.sp + BitVec.ofNat 64 (8 * i))
          (unpackSlotWords w bv) ⋆ G := by
      dsimp only [vllMach, x64Mach, x64Frame, machToKraken, x64Arch] at hm ⊢
      simpa [regsOfFn_get64] using hm
    refine x64Native_fallsTo_of_clean hcl.1 hcl.2
      (fun kh => x64_vecSpec.vslotLd_spec (s := machToKraken s) hvd trivial hmk) ?_
    intro sv' sk' hsim hq
    dsimp only [vllMach, x64Mach] at hq ⊢
    exact ⟨by simpa [krakenSim_vreg_eq hsim vd] using hq.1,
      (krakenSim_mem_eq hsim).trans hq.2⟩
  vop_spec {h k sig rs code pas dsts vh c clob vs P s post} hv ha hva hd hvd hrel hwp := by
    rcases Option.map_eq_some_iff.mp hv with ⟨⟨ds, cl'⟩, h0, heq⟩; cases heq
    obtain ⟨is, his, hds⟩ := emitCleanPair_eq_some.mp h0
    have hcl := clean_small_of_cleanBound (cleanBound_x64VopIns code pas dsts his) (by decide)
    rw [hds] at h0 ⊢
    refine x64Native_fallsTo_of_clean hcl.1 hcl.2
      (fun kh => x64_vecSpec.vop_spec h0 ha hva hd hvd (tRel_pArgHolds_to_x64Mach hrel) hwp) ?_
    rintro sv' sk' hsim ⟨⟨rvs, hp, htr⟩, hm⟩
    exact ⟨⟨rvs, hp, tRel_pDstHolds_of_x64Mach hsim htr⟩,
      (krakenSim_mem_eq hsim).trans hm⟩
  vload_spec {h k t vd a c clob val s post} hv hvd ha hlv := by
    rcases Option.map_eq_some_iff.mp hv with ⟨⟨ds, cl'⟩, h0, heq⟩; cases heq
    obtain ⟨is, his, hds⟩ := emitCleanPair_eq_some.mp h0
    have hcl := clean_small_of_cleanBound (cleanBound_x64Vmem true his) (by decide)
    have hlv_k : loadVal (x64Mach.mem (machToKraken s)) t
        (a.eval (x64Mach.getGpr (machToKraken s))) = some val := by
      rw [machToKraken_gpr_eq s, machToKraken_mem_eq s]; exact hlv
    rw [hds] at h0 ⊢
    refine x64Native_fallsTo_of_clean hcl.1 hcl.2
      (fun kh => x64_vecSpec.vload_spec h0 hvd ha hlv_k) ?_
    intro sv' sk' hsim hq
    dsimp only [vllMach, x64Mach] at hq ⊢
    exact ⟨by simpa [krakenSim_vreg_eq hsim vd] using hq.1,
      (krakenSim_mem_eq hsim).trans hq.2⟩
  vstore_spec {h k t vs a c clob val s post} hv ha hvs hvh hok := by
    rcases Option.map_eq_some_iff.mp hv with ⟨⟨ds, cl'⟩, h0, heq⟩; cases heq
    obtain ⟨is, his, hds⟩ := emitCleanPair_eq_some.mp h0
    have hcl := clean_small_of_cleanBound (cleanBound_x64Vmem false his) (by decide)
    have hvh_k : VecHolds (x64Mach.getVec (machToKraken s) vs) t val := by
      dsimp only [vllMach, x64Mach, machToKraken] at hvh ⊢
      simpa [zmmsOfFn_get512] using hvh
    have hok_k : storeOk (x64Mach.mem (machToKraken s)) t
        (a.eval (x64Mach.getGpr (machToKraken s))) := by
      rw [machToKraken_gpr_eq s, machToKraken_mem_eq s]; exact hok
    rw [hds] at h0 ⊢
    refine x64Native_fallsTo_of_clean hcl.1 hcl.2
      (fun kh => x64_vecSpec.vstore_spec h0 ha hvs hvh_k hok_k) ?_
    intro sv' sk' hsim hq
    simpa only [vllMach, x64Mach, machToKraken, regsOfFn_get64] using
      (krakenSim_mem_eq hsim).trans hq

private theorem opHook_native_fb {h : VllHost x64Arch} {k : Nat} {sig rs : List Ty}
    {code : OpCode sig rs} {pas : Tup (PArg Reg64 RegMm CondCode) sig}
    {dsts : Tup (PDst Reg64 RegMm CondCode) rs} {vh : VariantHint}
    {c : List (Instr x64Arch)} {clob : FlagMask} {vs : Tup Val sig}
    {P : Tup Val rs → Prop} {s : MachSt x64Arch} {post : Config x64Arch → Prop}
    (hfb : x64NativePair (x64Op code pas dsts vh) = some (c, clob))
    (ha : ∀ r ∈ tupArgGprs pas, r ∉ x64Arch.abi.scratch)
    (hd : ∀ r ∈ tupDstGprs dsts, r ∉ x64Arch.abi.scratch)
    (hrel : TRel ((vllMach x64Arch).PArgHolds s) pas vs) (hwp : code.wp vs P) :
    (vllMach x64Arch).FallsTo x64Arch.condReads h k c
      (tupDstGprs dsts ++ x64Arch.abi.scratch) [] clob s
      (fun s' => (∃ rvs, P rvs ∧ TRel ((vllMach x64Arch).PDstHolds s') dsts rvs) ∧
        s'.mem = s.mem) post := by
  obtain ⟨ds, h0, rfl⟩ := nativePair_some_iff hfb
  obtain ⟨ci, hci, hds⟩ := emitCleanPair_eq_some.mp h0
  have hcl := clean_small_of_cleanBound (cleanBound_x64OpIns code pas dsts vh hci) (by decide)
  rw [hds] at h0 ⊢
  refine x64Native_fallsTo_of_clean hcl.1 hcl.2
    (fun kh => x64_gprSpec.op_spec h0 ha hd (tRel_pArgHolds_to_x64Mach hrel) hwp) ?_
  rintro sv' sk' hsim ⟨⟨rvs, hp, htr⟩, hm⟩
  exact ⟨⟨rvs, hp, tRel_pDstHolds_of_x64Mach hsim htr⟩, (krakenSim_mem_eq hsim).trans hm⟩

private theorem opHook_alu_core {h : VllHost x64Arch} {k : Nat} {op : CoreAlu}
    {w : Vll.Width} {rd ra : Reg64} {pb : PArg Reg64 RegMm CondCode (.bits w.bits)}
    {sb : Src x64Arch} {va vb : BitVec w.bits} {P : Tup Val [.bits w.bits] → Prop}
    {s : MachSt x64Arch} {post : Config x64Arch → Prop}
    (hsb : match pb with
      | .gpr rb => sb = .reg rb
      | .imm cb => sb = .imm (cb.setWidth 64)
      | .vec _ => False)
    (hclob : x64Arch.aluClob op true = maskAll)
    (ha : (vllMach x64Arch).PArgHolds s (.bits w.bits) (.gpr ra) va)
    (hb : (vllMach x64Arch).PArgHolds s (.bits w.bits) pb vb)
    (hP : P (op.eval w va vb, ())) :
    (vllMach x64Arch).FallsTo x64Arch.condReads h k [.alu op w rd ra sb true]
      (rd :: x64Arch.abi.scratch) [] maskAll s
      (fun s' => (∃ rvs, P rvs ∧
          TRel ((vllMach x64Arch).PDstHolds s') (as := [.bits w.bits]) (.gpr rd, ()) rvs) ∧
        s'.mem = s.mem) post := by
  have heval : sb.evalW w s.gpr = vb := by
    cases pb with
    | vec _ => exact False.elim hsb
    | gpr rb => subst hsb; exact gprHolds_to_bits hb
    | imm cb =>
      subst hsb; have hcb : cb = vb := hb; subst hcb
      dsimp only [Src.evalW, Src.eval]
      rw [BitVec.setWidth_setWidth_of_le _ w.bits_le_64, BitVec.setWidth_eq]
  have hva : (s.gpr ra).setWidth w.bits = va := gprHolds_to_bits ha
  refine Machine.FallsTo.conseq (Machine.FallsTo.weaken
    (vllMach_alu_spec x64Arch_wf (op := op) (w := w) (rd := rd) (lhs := ra) (rhs := sb)
      (sf := true))
    (fun _ hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self)
    (fun _ h0 => nomatch h0) (by rw [hclob]; exact flagMask_sub_refl _)) ?_
  intro s' ⟨_, hg, _, hm⟩ _
  rw [hva, heval] at hg
  exact ⟨⟨(op.eval w va vb, ()), hP, .cons hg .nil⟩, hm⟩

private theorem vllX64OpHook_spec {h : VllHost x64Arch} {k : Nat} {sig rs : List Ty}
    {code : OpCode sig rs} {pas : Tup (PArg Reg64 RegMm CondCode) sig}
    {dsts : Tup (PDst Reg64 RegMm CondCode) rs} {vh : VariantHint}
    {c : List (Instr x64Arch)} {clob : FlagMask} {vs : Tup Val sig}
    {P : Tup Val rs → Prop} {s : MachSt x64Arch} {post : Config x64Arch → Prop}
    (hop : vllX64OpHook code pas dsts vh = some (c, clob))
    (ha : ∀ r ∈ tupArgGprs pas, r ∉ x64Arch.abi.scratch)
    (hd : ∀ r ∈ tupDstGprs dsts, r ∉ x64Arch.abi.scratch)
    (hrel : TRel ((vllMach x64Arch).PArgHolds s) pas vs) (hwp : code.wp vs P) :
    (vllMach x64Arch).FallsTo x64Arch.condReads h k c
      (tupDstGprs dsts ++ x64Arch.abi.scratch) [] clob s
      (fun s' => (∃ rvs, P rvs ∧ TRel ((vllMach x64Arch).PDstHolds s') dsts rvs) ∧
        s'.mem = s.mem) post := by
  have aluBin : ∀ (w : Vll.Width) (op : CoreAlu) (rd ra : Reg64)
      (pb : PArg Reg64 RegMm CondCode (.bits w.bits)) (va vb : BitVec w.bits)
      {P' : Tup Val [.bits w.bits] → Prop}
      (hsb : match pb with
        | .gpr rb => c = [.alu op w rd ra (.reg rb) true] ∧ clob = maskAll
        | .imm cb => c = [.alu op w rd ra (.imm (cb.setWidth 64)) true] ∧ clob = maskAll
        | .vec _ => False)
      (hclob : x64Arch.aluClob op true = maskAll)
      (hva : (vllMach x64Arch).PArgHolds s (.bits w.bits) (.gpr ra) va)
      (hvb : (vllMach x64Arch).PArgHolds s (.bits w.bits) pb vb)
      (hP : P' (op.eval w va vb, ())),
      (vllMach x64Arch).FallsTo x64Arch.condReads h k c
        (rd :: x64Arch.abi.scratch) [] clob s
        (fun s' => (∃ rvs, P' rvs ∧
            TRel ((vllMach x64Arch).PDstHolds s') (as := [.bits w.bits]) (.gpr rd, ()) rvs) ∧
          s'.mem = s.mem) post := by
    intro w op rd ra pb va vb P' hsb hclob hva hvb hP
    cases pb with
    | vec _ => exact False.elim hsb
    | gpr rb =>
      rcases hsb with ⟨rfl, rfl⟩
      exact opHook_alu_core rfl hclob hva hvb hP
    | imm cb =>
      rcases hsb with ⟨rfl, rfl⟩
      exact opHook_alu_core rfl hclob hva hvb hP
  cases code with
  | copy t =>
    cases t with
    | bool =>
      rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
      cases pd <;> try exact opHook_native_fb hop ha hd hrel hwp
      cases pa <;> try exact opHook_native_fb hop ha hd hrel hwp
      all_goals cases hop
    | bits n =>
      rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
      cases pd <;> try exact opHook_native_fb hop ha hd hrel hwp
      dsimp only [vllX64OpHook] at hop; split at hop
      · cases pa <;> dsimp only at hop
        · split at hop <;> first | cases hop | exact opHook_native_fb hop ha hd hrel hwp
        · exact opHook_native_fb hop ha hd hrel hwp
        · cases hop
      · exact opHook_native_fb hop ha hd hrel hwp
    | _ => exact opHook_native_fb hop ha hd hrel hwp
  | bitcast t u hb =>
    cases t <;> cases u <;> try exact opHook_native_fb hop ha hd hrel hwp
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd <;> try exact opHook_native_fb hop ha hd hrel hwp
    dsimp only [vllX64OpHook] at hop; split at hop
    · cases pa <;> dsimp only at hop
      · split at hop <;> first | cases hop | exact opHook_native_fb hop ha hd hrel hwp
      · exact opHook_native_fb hop ha hd hrel hwp
      · cases hop
    · exact opHook_native_fb hop ha hd hrel hwp
  | trunc m n =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd <;> try exact opHook_native_fb hop ha hd hrel hwp
    dsimp only [vllX64OpHook] at hop; split at hop
    · cases pa <;> dsimp only at hop
      · split at hop <;> first | cases hop | exact opHook_native_fb hop ha hd hrel hwp
      · exact opHook_native_fb hop ha hd hrel hwp
      · cases hop
    · exact opHook_native_fb hop ha hd hrel hwp
  | mul t =>
    cases t <;> try exact opHook_native_fb hop ha hd hrel hwp
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd <;> try exact opHook_native_fb hop ha hd hrel hwp
    dsimp only [vllX64OpHook] at hop; split at hop
    · cases pa <;> cases pb <;> dsimp only at hop
      any_goals exact opHook_native_fb hop ha hd hrel hwp
      all_goals (split at hop <;> first | cases hop | exact opHook_native_fb hop ha hd hrel hwp)
    · exact opHook_native_fb hop ha hd hrel hwp
  | cmp co t m hm =>
    cases t <;> try exact opHook_native_fb hop ha hd hrel hwp
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    subst hm
    dsimp only [vllX64OpHook] at hop; split at hop
    · cases pa <;> cases pb <;> cases pd <;> dsimp only at hop <;> first
        | cases hop
        | exact opHook_native_fb hop ha hd hrel hwp
        | (split at hop <;> first | cases hop | exact opHook_native_fb hop ha hd hrel hwp)
    · exact opHook_native_fb hop ha hd hrel hwp
  | add t =>
    cases t <;> try exact opHook_native_fb hop ha hd hrel hwp
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd with
    | vec _ => exact opHook_native_fb hop ha hd hrel hwp
    | gpr rd =>
      rcases vs with ⟨va, vb, ⟨⟩⟩
      obtain ⟨ha1, hb1⟩ := parg_trel2 hrel
      dsimp only [OpCode.wp, Ty.hasFloat, lift2] at hwp
      dsimp only [vllX64OpHook] at hop
      cases hw : vllX64WidthOfBits? _ with
      | none =>
        rw [hw] at hop; dsimp only at hop; exact opHook_native_fb hop ha hd hrel hwp
      | some w =>
        cases vh with
        | default =>
          cases pa with
          | gpr ra =>
            rw [hw] at hop; dsimp only at hop
            by_cases hrr : (ra == rd) = true
            · simp only [hrr, ↓reduceIte] at hop
              obtain rfl := vllX64WidthOfBits_eq hw
              have hreq : ra = rd := reg64_eq_of_beq hrr
              cases pb with
              | vec _ => exact opHook_native_fb hop ha hd hrel hwp
              | gpr rb =>
                cases hop; exact aluBin w .add rd rd (.gpr rb) va vb ⟨rfl, rfl⟩ rfl
                  (hreq ▸ ha1) hb1 hwp
              | imm cb =>
                cases hop; exact aluBin w .add rd rd (.imm cb) va vb ⟨rfl, rfl⟩ rfl
                  (hreq ▸ ha1) hb1 hwp
            · simp only [hrr, Bool.false_eq_true, ↓reduceIte] at hop
              exact opHook_native_fb hop ha hd hrel hwp
          | _ =>
            rw [hw] at hop; dsimp only at hop; exact opHook_native_fb hop ha hd hrel hwp
        | _ =>
          rw [hw] at hop; dsimp only at hop; exact opHook_native_fb hop ha hd hrel hwp
  | sub t =>
    cases t <;> try exact opHook_native_fb hop ha hd hrel hwp
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd with
    | vec _ => exact opHook_native_fb hop ha hd hrel hwp
    | gpr rd =>
      rcases vs with ⟨va, vb, ⟨⟩⟩
      obtain ⟨ha1, hb1⟩ := parg_trel2 hrel
      dsimp only [OpCode.wp, Ty.hasFloat, lift2] at hwp
      dsimp only [vllX64OpHook] at hop
      cases hw : vllX64WidthOfBits? _ with
      | none =>
        rw [hw] at hop; dsimp only at hop; exact opHook_native_fb hop ha hd hrel hwp
      | some w =>
        cases vh with
        | default =>
          cases pa with
          | gpr ra =>
            rw [hw] at hop; dsimp only at hop
            by_cases hrr : (ra == rd) = true
            · simp only [hrr, ↓reduceIte] at hop
              obtain rfl := vllX64WidthOfBits_eq hw
              have hreq : ra = rd := reg64_eq_of_beq hrr
              cases pb with
              | vec _ => exact opHook_native_fb hop ha hd hrel hwp
              | gpr rb =>
                cases hop; exact aluBin w .sub rd rd (.gpr rb) va vb ⟨rfl, rfl⟩ rfl
                  (hreq ▸ ha1) hb1 hwp
              | imm cb =>
                cases hop; exact aluBin w .sub rd rd (.imm cb) va vb ⟨rfl, rfl⟩ rfl
                  (hreq ▸ ha1) hb1 hwp
            · simp only [hrr, Bool.false_eq_true, ↓reduceIte] at hop
              exact opHook_native_fb hop ha hd hrel hwp
          | _ =>
            rw [hw] at hop; dsimp only at hop; exact opHook_native_fb hop ha hd hrel hwp
        | _ =>
          rw [hw] at hop; dsimp only at hop; exact opHook_native_fb hop ha hd hrel hwp
  | and t =>
    cases t <;> try exact opHook_native_fb hop ha hd hrel hwp
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd with
    | vec _ => exact opHook_native_fb hop ha hd hrel hwp
    | gpr rd =>
      rcases vs with ⟨va, vb, ⟨⟩⟩
      obtain ⟨ha1, hb1⟩ := parg_trel2 hrel
      dsimp only [OpCode.wp, Ty.hasFloat, lift2] at hwp
      dsimp only [vllX64OpHook] at hop
      cases hw : vllX64WidthOfBits? _ with
      | none =>
        rw [hw] at hop; dsimp only at hop; exact opHook_native_fb hop ha hd hrel hwp
      | some w =>
        cases vh with
        | default =>
          cases pa with
          | gpr ra =>
            rw [hw] at hop; dsimp only at hop
            split at hop
            · obtain rfl := vllX64WidthOfBits_eq hw
              cases pb with
              | vec _ => exact opHook_native_fb hop ha hd hrel hwp
              | gpr rb =>
                cases hop; exact aluBin w .and rd ra (.gpr rb) va vb ⟨rfl, rfl⟩ rfl ha1 hb1 hwp
              | imm cb =>
                cases hop; exact aluBin w .and rd ra (.imm cb) va vb ⟨rfl, rfl⟩ rfl ha1 hb1 hwp
            · exact opHook_native_fb hop ha hd hrel hwp
          | _ =>
            rw [hw] at hop; dsimp only at hop; exact opHook_native_fb hop ha hd hrel hwp
        | _ =>
          rw [hw] at hop; dsimp only at hop; exact opHook_native_fb hop ha hd hrel hwp
  | or t =>
    cases t <;> try exact opHook_native_fb hop ha hd hrel hwp
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd with
    | vec _ => exact opHook_native_fb hop ha hd hrel hwp
    | gpr rd =>
      rcases vs with ⟨va, vb, ⟨⟩⟩
      obtain ⟨ha1, hb1⟩ := parg_trel2 hrel
      dsimp only [OpCode.wp, Ty.hasFloat, lift2] at hwp
      dsimp only [vllX64OpHook] at hop
      cases hw : vllX64WidthOfBits? _ with
      | none =>
        rw [hw] at hop; dsimp only at hop; exact opHook_native_fb hop ha hd hrel hwp
      | some w =>
        cases vh with
        | default =>
          cases pa with
          | gpr ra =>
            rw [hw] at hop; dsimp only at hop
            split at hop
            · obtain rfl := vllX64WidthOfBits_eq hw
              cases pb with
              | vec _ => exact opHook_native_fb hop ha hd hrel hwp
              | gpr rb =>
                cases hop; exact aluBin w .or rd ra (.gpr rb) va vb ⟨rfl, rfl⟩ rfl ha1 hb1 hwp
              | imm cb =>
                cases hop; exact aluBin w .or rd ra (.imm cb) va vb ⟨rfl, rfl⟩ rfl ha1 hb1 hwp
            · exact opHook_native_fb hop ha hd hrel hwp
          | _ =>
            rw [hw] at hop; dsimp only at hop; exact opHook_native_fb hop ha hd hrel hwp
        | _ =>
          rw [hw] at hop; dsimp only at hop; exact opHook_native_fb hop ha hd hrel hwp
  | xor t =>
    cases t <;> try exact opHook_native_fb hop ha hd hrel hwp
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd with
    | vec _ => exact opHook_native_fb hop ha hd hrel hwp
    | gpr rd =>
      rcases vs with ⟨va, vb, ⟨⟩⟩
      obtain ⟨ha1, hb1⟩ := parg_trel2 hrel
      dsimp only [OpCode.wp, Ty.hasFloat, lift2] at hwp
      dsimp only [vllX64OpHook] at hop
      cases hw : vllX64WidthOfBits? _ with
      | none =>
        rw [hw] at hop; dsimp only at hop; exact opHook_native_fb hop ha hd hrel hwp
      | some w =>
        cases vh with
        | default =>
          cases pa with
          | gpr ra =>
            rw [hw] at hop; dsimp only at hop
            split at hop
            · obtain rfl := vllX64WidthOfBits_eq hw
              cases pb with
              | vec _ => exact opHook_native_fb hop ha hd hrel hwp
              | gpr rb =>
                cases hop; exact aluBin w .xor rd ra (.gpr rb) va vb ⟨rfl, rfl⟩ rfl ha1 hb1 hwp
              | imm cb =>
                cases hop; exact aluBin w .xor rd ra (.imm cb) va vb ⟨rfl, rfl⟩ rfl ha1 hb1 hwp
            · exact opHook_native_fb hop ha hd hrel hwp
          | _ =>
            rw [hw] at hop; dsimp only at hop; exact opHook_native_fb hop ha hd hrel hwp
        | _ =>
          rw [hw] at hop; dsimp only at hop; exact opHook_native_fb hop ha hd hrel hwp
  | _ => exact opHook_native_fb hop ha hd hrel hwp

private theorem x64ZeroUpper32Op_trunc_m64 {m : Nat}
    {pa : PArg Reg64 RegMm CondCode (.bits m)} {rd : Reg64}
    (hz : x64ZeroUpper32Op (.trunc m 32) (pa, ()) (.gpr rd, ()) = true) :
    (∀ v, pa ≠ .vec v) ∧ m = 64 := by
  change (m == 64 && _) = true at hz
  have hm64 : m = 64 := beq_iff_eq.mp (Bool.and_eq_true_iff.mp hz).1
  subst hm64
  cases pa with
  | vec _ => cases hz
  | gpr _ | imm _ => exact ⟨(fun _ e => by cases e), rfl⟩

private theorem x64ZeroUpper32Op_zext_m {m : Nat}
    {pa : PArg Reg64 RegMm CondCode (.bits m)} {rd : Reg64}
    (hz : x64ZeroUpper32Op (.zext m 32) (pa, ()) (.gpr rd, ()) = true) :
    m = 8 ∨ m = 16 := by
  dsimp only [x64ZeroUpper32Op] at hz
  simp only [Bool.or_eq_true, beq_iff_eq] at hz; exact hz

private theorem x64ZeroUpper32Op_sext_m {m : Nat}
    {pa : PArg Reg64 RegMm CondCode (.bits m)} {rd : Reg64}
    (hz : x64ZeroUpper32Op (.sext m 32) (pa, ()) (.gpr rd, ()) = true) :
    m = 8 ∨ m = 16 := by
  dsimp only [x64ZeroUpper32Op] at hz
  simp only [Bool.or_eq_true, beq_iff_eq] at hz; exact hz

private theorem vllX64OpHook_ofBool32_ne_none (pa : PArg Reg64 RegMm CondCode .bool)
    (rd : Reg64) (vh : VariantHint) (ha : ∀ v, pa ≠ .vec v) :
    vllX64OpHook (.ofBool 32) (pa, ()) (.gpr rd, ()) vh ≠ none := by
  intro h
  dsimp only [vllX64OpHook, x64NativePair, x64Op, emitCleanPair, x64OpIns] at h
  have h1 := Option.map_eq_none_iff.mp (Option.map_eq_none_iff.mp h)
  cases pa with
  | vec v => exact ha v rfl
  | gpr _ | imm _ | flag _ => cases h1

private theorem vllX64OpHook_zext32_ne_none {m : Nat} (hm : m = 8 ∨ m = 16)
    (pa : PArg Reg64 RegMm CondCode (.bits m)) (rd : Reg64) (vh : VariantHint)
    (ha : ∀ v, pa ≠ .vec v) :
    vllX64OpHook (.zext m 32) (pa, ()) (.gpr rd, ()) vh ≠ none := by
  intro h
  rcases hm with rfl | rfl
  · dsimp only [vllX64OpHook, x64NativePair, x64Op, emitCleanPair, x64OpIns] at h
    have h1 := Option.map_eq_none_iff.mp (Option.map_eq_none_iff.mp h)
    cases pa with | vec v => exact ha v rfl | gpr _ | imm _ => cases h1
  · dsimp only [vllX64OpHook, x64NativePair, x64Op, emitCleanPair, x64OpIns] at h
    have h1 := Option.map_eq_none_iff.mp (Option.map_eq_none_iff.mp h)
    cases pa with | vec v => exact ha v rfl | gpr _ | imm _ => cases h1

private theorem vllX64OpHook_sext32_ne_none {m : Nat} (hm : m = 8 ∨ m = 16)
    (pa : PArg Reg64 RegMm CondCode (.bits m)) (rd : Reg64) (vh : VariantHint)
    (ha : ∀ v, pa ≠ .vec v) :
    vllX64OpHook (.sext m 32) (pa, ()) (.gpr rd, ()) vh ≠ none := by
  intro h
  rcases hm with rfl | rfl
  · dsimp only [vllX64OpHook, x64NativePair, x64Op, emitCleanPair, x64OpIns] at h
    have h1 := Option.map_eq_none_iff.mp (Option.map_eq_none_iff.mp h)
    cases pa with | vec v => exact ha v rfl | gpr _ | imm _ => cases h1
  · dsimp only [vllX64OpHook, x64NativePair, x64Op, emitCleanPair, x64OpIns] at h
    have h1 := Option.map_eq_none_iff.mp (Option.map_eq_none_iff.mp h)
    cases pa with | vec v => exact ha v rfl | gpr _ | imm _ => cases h1

private theorem vllX64StoreHook_eq_native {t : Ty} {pa : PArg Reg64 RegMm CondCode t}
    {a : AddrArg Reg64} {c : List (Instr x64Arch)} {clob : FlagMask}
    (h : vllX64StoreHook t pa a = some (c, clob)) :
    x64NativePair (x64Store t pa a) = some (c, clob) := by
  cases t <;> cases pa <;> dsimp only [vllX64StoreHook] at h <;>
    split at h <;> first | cases h | exact h

private theorem op_zero32_native_fb {h : VllHost x64Arch} {k : Nat} {sig : List Ty}
    {code : OpCode sig [.bits 32]} {pas : Tup (PArg Reg64 RegMm CondCode) sig}
    {rd : Reg64} {vh : VariantHint} {c : List (Instr x64Arch)} {clob : FlagMask}
    {vs : Tup Val sig} {P : Tup Val [.bits 32] → Prop} {s : MachSt x64Arch}
    {post : Config x64Arch → Prop}
    (hz : x64ZeroUpper32Op code pas (.gpr rd, ()) = true)
    (hfb : x64NativePair (x64Op code pas (.gpr rd, ()) vh) = some (c, clob))
    (ha : ∀ r ∈ tupArgGprs pas, r ∉ x64Arch.abi.scratch) (hrd : rd ∉ x64Arch.abi.scratch)
    (hrel : TRel ((vllMach x64Arch).PArgHolds s) pas vs) (hwp : code.wp vs P) :
    (vllMach x64Arch).FallsTo x64Arch.condReads h k c (rd :: x64Arch.abi.scratch) [] clob s
      (fun s' => (∃ rv : BitVec 32, P (rv, ()) ∧ s'.gpr rd = rv.setWidth 64) ∧
        s'.mem = s.mem) post := by
  obtain ⟨ds, h0, rfl⟩ := nativePair_some_iff hfb
  obtain ⟨ci, hci, hds⟩ := emitCleanPair_eq_some.mp h0
  have hcl := clean_small_of_cleanBound (cleanBound_x64OpIns code pas (.gpr rd, ()) vh hci)
    (by decide)
  rw [hds] at h0 ⊢
  refine x64Native_fallsTo_of_clean hcl.1 hcl.2
    (fun kh => x64_gprSpec.op_zero32 hz h0 rfl ha hrd (tRel_pArgHolds_to_x64Mach hrel) hwp) ?_
  rintro sv' sk' hsim ⟨⟨rv, hp, hg⟩, hm⟩
  exact ⟨⟨rv, hp, (krakenSim_gpr_eq hsim rd).trans hg⟩, (krakenSim_mem_eq hsim).trans hm⟩

private theorem op_zero32_alu32 {h : VllHost x64Arch} {k : Nat} {op : CoreAlu}
    {rd ra : Reg64} {pb : PArg Reg64 RegMm CondCode (.bits 32)}
    {sb : Src x64Arch} {va vb : BitVec 32} {P : Tup Val [.bits 32] → Prop}
    {s : MachSt x64Arch} {post : Config x64Arch → Prop}
    (hsb : match pb with
      | .gpr rb => sb = .reg rb
      | .imm cb => sb.evalW .w32 s.gpr = cb
      | .vec _ => False)
    {sf : Bool} {clob : FlagMask} (hmSub : x64Arch.aluClob op sf &&& ~~~clob = 0#8)
    (ha : (vllMach x64Arch).PArgHolds s (.bits 32) (.gpr ra) va)
    (hb : (vllMach x64Arch).PArgHolds s (.bits 32) pb vb)
    (hP : P (op.eval .w32 va vb, ())) :
    (vllMach x64Arch).FallsTo x64Arch.condReads h k [.alu op .w32 rd ra sb sf]
      (rd :: x64Arch.abi.scratch) [] clob s
      (fun s' => (∃ rv : BitVec 32, P (rv, ()) ∧ s'.gpr rd = rv.setWidth 64) ∧
        s'.mem = s.mem) post := by
  have heval : sb.evalW .w32 s.gpr = vb := by
    cases pb with
    | vec _ => exact False.elim hsb
    | gpr rb =>
      subst hsb; dsimp only [vllMach, Machine.PArgHolds] at hb
      exact gprHolds_to_bits hb
    | imm cb =>
      have hcb : cb = vb := hb; subst hcb; exact hsb
  have hva : (s.gpr ra).setWidth 32 = va :=
    gprHolds_to_bits (w := .w32) (by dsimp only [vllMach, Machine.PArgHolds] at ha; exact ha)
  refine Machine.FallsTo.conseq (Machine.FallsTo.weaken
    (vllMach_alu_spec x64Arch_wf (op := op) (w := .w32) (rd := rd) (lhs := ra) (rhs := sb)
      (sf := sf))
    (fun _ hr => by simp only [List.mem_singleton] at hr; subst hr; exact List.mem_cons_self)
    (fun _ h0 => nomatch h0) hmSub) ?_
  intro s' ⟨hg, _, _, hm⟩ _
  dsimp only [vllMach, x64Arch] at hg
  rw [hva, heval, writeSubX64_w32] at hg
  exact ⟨⟨op.eval .w32 va vb, hP, hg⟩, hm⟩

private theorem vllX64Op_zero32 {h : VllHost x64Arch} {k : Nat} {sig : List Ty}
    {code : OpCode sig [.bits 32]} {pas : Tup (PArg Reg64 RegMm CondCode) sig}
    {dsts : Tup (PDst Reg64 RegMm CondCode) [.bits 32]} {rd : Reg64} {vh : VariantHint}
    {c : List (Instr x64Arch)} {clob : FlagMask} {vs : Tup Val sig}
    {P : Tup Val [.bits 32] → Prop} {s : MachSt x64Arch} {post : Config x64Arch → Prop}
    (hz : vllX64NativeHooks.zeroUpper32Op code pas dsts = true)
    (hop : (vllGprIsaOfHooks x64Arch vllX64NativeHooks).op code pas dsts vh = some (c, clob))
    (hdst : dsts = (.gpr rd, ()))
    (ha : ∀ r ∈ tupArgGprs pas, r ∉ x64Arch.abi.scratch) (hrd : rd ∉ x64Arch.abi.scratch)
    (hrel : TRel ((vllMach x64Arch).PArgHolds s) pas vs) (hwp : code.wp vs P) :
    (vllMach x64Arch).FallsTo x64Arch.condReads h k c (rd :: x64Arch.abi.scratch) [] clob s
      (fun s' => (∃ rv : BitVec 32, P (rv, ()) ∧ s'.gpr rd = rv.setWidth 64) ∧
        s'.mem = s.mem) post := by
  subst hdst
  dsimp only [vllGprIsaOfHooks] at hop
  dsimp only [vllX64NativeHooks] at hz hop
  cases hhk : vllX64OpHook code pas (.gpr rd, ()) vh with
  | some res =>
    rw [hhk] at hop; cases hop
    have core32 : ∀ (op : CoreAlu) (ra : Reg64) (pb : PArg Reg64 RegMm CondCode (.bits 32))
        (va vb : BitVec 32) (hclob : x64Arch.aluClob op true = maskAll),
        (match pb with
          | .gpr rb => c = [.alu op .w32 rd ra (.reg rb) true] ∧ clob = maskAll
          | .imm cb => c = [.alu op .w32 rd ra (.imm (cb.setWidth 64)) true] ∧ clob = maskAll
          | .vec _ => False) →
        (vllMach x64Arch).PArgHolds s (.bits 32) (.gpr ra) va →
        (vllMach x64Arch).PArgHolds s (.bits 32) pb vb →
        P (op.eval .w32 va vb, ()) →
        (vllMach x64Arch).FallsTo x64Arch.condReads h k c (rd :: x64Arch.abi.scratch) [] clob s
          (fun s' => (∃ rv : BitVec 32, P (rv, ()) ∧ s'.gpr rd = rv.setWidth 64) ∧
            s'.mem = s.mem) post := by
      intro op ra pb va vb hclob hc hva hvb hP
      cases pb with
      | vec _ => exact False.elim hc
      | gpr rb =>
        rcases hc with ⟨rfl, rfl⟩
        exact op_zero32_alu32 rfl (by rw [hclob]; exact flagMask_sub_refl _) hva hvb hP
      | imm cb =>
        rcases hc with ⟨rfl, rfl⟩
        exact op_zero32_alu32
          (by dsimp only [Src.evalW, Src.eval]
              rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq])
          (by rw [hclob]; exact flagMask_sub_refl _) hva hvb hP
    cases code with
    | copy _ =>
      rcases pas with ⟨pa, ⟨⟩⟩; dsimp only [vllX64OpHook] at hhk
      split at hhk
      · cases pa <;> dsimp only at hhk
        · split at hhk <;> first | cases hhk | exact op_zero32_native_fb hz hhk ha hrd hrel hwp
        · exact op_zero32_native_fb hz hhk ha hrd hrel hwp
        · cases hhk
      · exact op_zero32_native_fb hz hhk ha hrd hrel hwp
    | bitcast t _ _ =>
      cases t <;> try exact op_zero32_native_fb hz hhk ha hrd hrel hwp
      rcases pas with ⟨pa, ⟨⟩⟩; dsimp only [vllX64OpHook] at hhk
      split at hhk
      · cases pa <;> dsimp only at hhk
        · split at hhk <;> first | cases hhk | exact op_zero32_native_fb hz hhk ha hrd hrel hwp
        · exact op_zero32_native_fb hz hhk ha hrd hrel hwp
        · cases hhk
      · exact op_zero32_native_fb hz hhk ha hrd hrel hwp
    | trunc _ _ =>
      rcases pas with ⟨pa, ⟨⟩⟩; dsimp only [vllX64OpHook] at hhk
      split at hhk
      · cases pa <;> dsimp only at hhk
        · split at hhk <;> first | cases hhk | exact op_zero32_native_fb hz hhk ha hrd hrel hwp
        · exact op_zero32_native_fb hz hhk ha hrd hrel hwp
        · cases hhk
      · exact op_zero32_native_fb hz hhk ha hrd hrel hwp
    | mul _ =>
      rcases pas with ⟨pa, pb, ⟨⟩⟩; dsimp only [vllX64OpHook] at hhk
      split at hhk
      · cases pa <;> cases pb <;> dsimp only at hhk <;> first
          | exact op_zero32_native_fb hz hhk ha hrd hrel hwp
          | (split at hhk <;> first
              | cases hhk | exact op_zero32_native_fb hz hhk ha hrd hrel hwp)
      · exact op_zero32_native_fb hz hhk ha hrd hrel hwp
    | add _ =>
      rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
      obtain ⟨ha1, hb1⟩ := parg_trel2 hrel
      dsimp only [OpCode.wp, Ty.hasFloat, lift2] at hwp
      dsimp only [vllX64OpHook, vllX64WidthOfBits?] at hhk
      cases vh with
      | default =>
        cases pa with
        | gpr ra =>
          by_cases hrr : (ra == rd) = true
          · simp only [hrr, ↓reduceIte] at hhk
            have hreq : ra = rd := reg64_eq_of_beq hrr
            cases pb with
            | vec _ => exact op_zero32_native_fb hz hhk ha hrd hrel hwp
            | gpr rb =>
              cases hhk; exact core32 .add rd (.gpr rb) va vb rfl ⟨rfl, rfl⟩ (hreq ▸ ha1) hb1 hwp
            | imm cb =>
              cases hhk; exact core32 .add rd (.imm cb) va vb rfl ⟨rfl, rfl⟩ (hreq ▸ ha1) hb1 hwp
          · simp only [hrr, Bool.false_eq_true, ↓reduceIte] at hhk
            exact op_zero32_native_fb hz hhk ha hrd hrel hwp
        | _ => exact op_zero32_native_fb hz hhk ha hrd hrel hwp
      | _ => exact op_zero32_native_fb hz hhk ha hrd hrel hwp
    | sub _ =>
      rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
      obtain ⟨ha1, hb1⟩ := parg_trel2 hrel
      dsimp only [OpCode.wp, Ty.hasFloat, lift2] at hwp
      dsimp only [vllX64OpHook, vllX64WidthOfBits?] at hhk
      cases vh with
      | default =>
        cases pa with
        | gpr ra =>
          by_cases hrr : (ra == rd) = true
          · simp only [hrr, ↓reduceIte] at hhk
            have hreq : ra = rd := reg64_eq_of_beq hrr
            cases pb with
            | vec _ => exact op_zero32_native_fb hz hhk ha hrd hrel hwp
            | gpr rb =>
              cases hhk; exact core32 .sub rd (.gpr rb) va vb rfl ⟨rfl, rfl⟩ (hreq ▸ ha1) hb1 hwp
            | imm cb =>
              cases hhk; exact core32 .sub rd (.imm cb) va vb rfl ⟨rfl, rfl⟩ (hreq ▸ ha1) hb1 hwp
          · simp only [hrr, Bool.false_eq_true, ↓reduceIte] at hhk
            exact op_zero32_native_fb hz hhk ha hrd hrel hwp
        | _ => exact op_zero32_native_fb hz hhk ha hrd hrel hwp
      | _ => exact op_zero32_native_fb hz hhk ha hrd hrel hwp
    | and _ =>
      rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
      obtain ⟨ha1, hb1⟩ := parg_trel2 hrel
      dsimp only [OpCode.wp, Ty.hasFloat, lift2] at hwp
      dsimp only [vllX64OpHook] at hhk
      cases vh with
      | default =>
        cases pa with
        | gpr ra =>
          rw [show vllX64WidthOfBits? 32 = some .w32 from rfl] at hhk
          dsimp only at hhk
          simp only [beq_self_eq_true, Bool.or_true, Bool.true_or, ↓reduceIte] at hhk
          cases pb with
          | vec _ => exact op_zero32_native_fb hz hhk ha hrd hrel hwp
          | gpr rb => cases hhk; exact core32 .and ra (.gpr rb) va vb rfl ⟨rfl, rfl⟩ ha1 hb1 hwp
          | imm cb => cases hhk; exact core32 .and ra (.imm cb) va vb rfl ⟨rfl, rfl⟩ ha1 hb1 hwp
        | _ => exact op_zero32_native_fb hz hhk ha hrd hrel hwp
      | _ => exact op_zero32_native_fb hz hhk ha hrd hrel hwp
    | or _ =>
      rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
      obtain ⟨ha1, hb1⟩ := parg_trel2 hrel
      dsimp only [OpCode.wp, Ty.hasFloat, lift2] at hwp
      dsimp only [vllX64OpHook] at hhk
      cases vh with
      | default =>
        cases pa with
        | gpr ra =>
          rw [show vllX64WidthOfBits? 32 = some .w32 from rfl] at hhk
          dsimp only at hhk
          simp only [beq_self_eq_true, Bool.or_true, Bool.true_or, ↓reduceIte] at hhk
          cases pb with
          | vec _ => exact op_zero32_native_fb hz hhk ha hrd hrel hwp
          | gpr rb => cases hhk; exact core32 .or ra (.gpr rb) va vb rfl ⟨rfl, rfl⟩ ha1 hb1 hwp
          | imm cb => cases hhk; exact core32 .or ra (.imm cb) va vb rfl ⟨rfl, rfl⟩ ha1 hb1 hwp
        | _ => exact op_zero32_native_fb hz hhk ha hrd hrel hwp
      | _ => exact op_zero32_native_fb hz hhk ha hrd hrel hwp
    | xor _ =>
      rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
      obtain ⟨ha1, hb1⟩ := parg_trel2 hrel
      dsimp only [OpCode.wp, Ty.hasFloat, lift2] at hwp
      dsimp only [vllX64OpHook] at hhk
      cases vh with
      | default =>
        cases pa with
        | gpr ra =>
          rw [show vllX64WidthOfBits? 32 = some .w32 from rfl] at hhk
          dsimp only at hhk
          simp only [beq_self_eq_true, Bool.or_true, Bool.true_or, ↓reduceIte] at hhk
          cases pb with
          | vec _ => exact op_zero32_native_fb hz hhk ha hrd hrel hwp
          | gpr rb => cases hhk; exact core32 .xor ra (.gpr rb) va vb rfl ⟨rfl, rfl⟩ ha1 hb1 hwp
          | imm cb => cases hhk; exact core32 .xor ra (.imm cb) va vb rfl ⟨rfl, rfl⟩ ha1 hb1 hwp
        | _ => exact op_zero32_native_fb hz hhk ha hrd hrel hwp
      | _ => exact op_zero32_native_fb hz hhk ha hrd hrel hwp
    | cmp _ _ _ _ => cases hz
    | _ => exact op_zero32_native_fb hz hhk ha hrd hrel hwp
  | none =>
    rw [hhk] at hop; dsimp only at hop
    have coreCopy32 : ∀ {pa : PArg Reg64 RegMm CondCode (.bits 32)} {va : BitVec 32},
        vllCoreCopyW x64Arch .w32 pa rd = some (c, clob) →
        (vllMach x64Arch).PArgHolds s (.bits 32) pa va → P (va, ()) →
        (vllMach x64Arch).FallsTo x64Arch.condReads h k c (rd :: x64Arch.abi.scratch) [] clob s
          (fun s' => (∃ rv : BitVec 32, P (rv, ()) ∧ s'.gpr rd = rv.setWidth 64) ∧
            s'.mem = s.mem) post := by
      intro pa va hcp hva hP
      cases pa with
      | vec _ => cases hcp
      | gpr rs =>
        cases hcp
        refine Machine.FallsTo.conseq (fallsTo_weaken_rd (vllMach_movW_spec x64Arch_wf
          (w := .w32) (rd := rd) (rs := rs))) ?_
        intro s' ⟨hg, _, hm⟩ _
        dsimp only [vllMach, Machine.PArgHolds] at hva
        dsimp only [vllMach, x64Arch] at hg
        rw [gprHolds_to_bits (w := .w32) hva, writeSubX64_w32] at hg
        exact ⟨⟨va, hP, hg⟩, hm⟩
      | imm cv =>
        cases hcp; have hcv : cv = va := hva; subst hcv
        refine Machine.FallsTo.conseq (fallsTo_weaken_rd (vllMach_movi_spec
          (A := x64Arch) (rd := rd) (imm := cv.setWidth 64))) ?_
        intro s' ⟨hg, hm⟩ _
        exact ⟨⟨cv, hP, hg⟩, hm⟩
    have coreBin32 : ∀ (op : CoreAlu)
        {pa pb : PArg Reg64 RegMm CondCode (.bits 32)} {va vb : BitVec 32},
        vllCoreAlu x64Arch op .w32 pa pb rd = some (c, clob) →
        (∀ r ∈ pb.gprs, r ∉ x64Arch.abi.scratch) →
        (vllMach x64Arch).PArgHolds s (.bits 32) pa va →
        (vllMach x64Arch).PArgHolds s (.bits 32) pb vb →
        P (op.eval .w32 va vb, ()) →
        (vllMach x64Arch).FallsTo x64Arch.condReads h k c (rd :: x64Arch.abi.scratch) [] clob s
          (fun s' => (∃ rv : BitVec 32, P (rv, ()) ∧ s'.gpr rd = rv.setWidth 64) ∧
            s'.mem = s.mem) post := by
      intro op pa pb va vb halu hpb_ns hva hvb hP
      dsimp only [vllCoreAlu] at halu
      have hs0_mem : (.r10 : Reg64) ∈ x64Arch.abi.scratch := List.mem_cons_self
      cases pb with
      | vec _ => cases pa <;> cases halu
      | gpr rb =>
        cases pa with
        | vec _ => cases halu
        | gpr ra =>
          cases halu
          exact op_zero32_alu32 rfl (by cases op <;> rfl) hva hvb hP
        | imm ca =>
          cases halu
          have hrb_ne : rb ≠ .r10 := fun e => hpb_ns rb List.mem_cons_self (e ▸ hs0_mem)
          refine Machine.FallsTo.weaken (Machine.FallsTo.comp (v₂ := ([] : List RegMm))
            (vllMach_movi_spec (A := x64Arch) (rd := .r10) (imm := ca.setWidth 64))
            fun s1 ⟨hg1, hm1⟩ hfr1 => by
              have hva1 : (vllMach x64Arch).PArgHolds s1 (.bits 32) (.gpr .r10) va := by
                have hca : ca = va := hva; subst hca
                dsimp only [vllMach] at hg1
                exact ⟨by decide, by
                  change (s1.gpr .r10).setWidth 32 = ca
                  rw [hg1, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]⟩
              have hvb1 : (vllMach x64Arch).PArgHolds s1 (.bits 32) (.gpr rb) vb := by
                have hrb_eq : s1.gpr rb = s.gpr rb := hfr1.1 rb (fun hm => by
                  simp only [List.mem_singleton] at hm; exact hrb_ne hm)
                dsimp only [vllMach, Machine.PArgHolds] at hvb ⊢
                rwa [hrb_eq]
              exact Machine.FallsTo.conseq (op_zero32_alu32 (op := op) (rd := rd) (ra := .r10)
                (pb := .gpr rb) (sb := .reg rb) (sf := false) (clob := x64Arch.aluClob op false)
                rfl (flagMask_sub_refl _) hva1 hvb1 hP)
                (fun s2 ⟨hres, hm2⟩ _ => ⟨hres, hm2.trans hm1⟩))
            (fun r hr => by
              rw [List.cons_append, List.nil_append, List.mem_cons] at hr
              rcases hr with rfl | hr'
              · exact List.mem_cons_of_mem _ hs0_mem
              · exact hr')
            (fun _ h0 => nomatch h0)
            (by
              rw [show FlagMask.none ||| x64Arch.aluClob op false = x64Arch.aluClob op false from
                BitVec.zero_or]
              exact flagMask_sub_refl _)
      | imm cb =>
        cases pa with
        | vec _ => cases halu
        | gpr ra =>
          cases halu
          exact op_zero32_alu32
            (by dsimp only [Src.evalW, Src.eval]
                rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq])
            (by cases op <;> rfl) hva hvb hP
        | imm ca =>
          cases halu
          refine Machine.FallsTo.weaken (Machine.FallsTo.comp (v₂ := ([] : List RegMm))
            (vllMach_movi_spec (A := x64Arch) (rd := .r10) (imm := ca.setWidth 64))
            fun s1 ⟨hg1, hm1⟩ _ => by
              have hva1 : (vllMach x64Arch).PArgHolds s1 (.bits 32) (.gpr .r10) va := by
                have hca : ca = va := hva; subst hca
                dsimp only [vllMach] at hg1
                exact ⟨by decide, by
                  change (s1.gpr .r10).setWidth 32 = ca
                  rw [hg1, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]⟩
              exact Machine.FallsTo.conseq (op_zero32_alu32 (op := op) (rd := rd) (ra := .r10)
                (pb := .imm cb) (sb := .imm (cb.setWidth 64)) (sf := false)
                (clob := x64Arch.aluClob op false)
                (by dsimp only [Src.evalW, Src.eval]
                    rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq])
                (flagMask_sub_refl _) hva1 hvb hP)
                (fun s2 ⟨hres, hm2⟩ _ => ⟨hres, hm2.trans hm1⟩))
            (fun r hr => by
              rw [List.cons_append, List.nil_append, List.mem_cons] at hr
              rcases hr with rfl | hr'
              · exact List.mem_cons_of_mem _ hs0_mem
              · exact hr')
            (fun _ h0 => nomatch h0)
            (by
              rw [show FlagMask.none ||| x64Arch.aluClob op false = x64Arch.aluClob op false from
                BitVec.zero_or]
              exact flagMask_sub_refl _)
    cases code with
    | copy _ =>
      rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
      cases hrel with | cons ha1 _ =>
      dsimp only [OpCode.wp] at hwp
      have hcp : vllCoreCopyW x64Arch .w32 pa rd = some (c, clob) := hop
      exact coreCopy32 hcp ha1 hwp
    | bitcast t _ hb =>
      cases t with
      | bool => cases hb
      | pair _ _ => cases hz
      | float _ => cases hz
      | bits m =>
        have hm : m = 32 := by simpa [Ty.size] using hb
        subst hm
        rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
        cases hrel with | cons ha1 _ =>
        dsimp only [OpCode.wp] at hwp
        have hcp : vllCoreCopyW x64Arch .w32 pa rd = some (c, clob) := hop
        exact coreCopy32 hcp ha1 hwp
    | trunc m _ =>
      rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
      cases hrel with | cons ha1 _ =>
      dsimp only [OpCode.wp] at hwp
      obtain ⟨hpa, hm⟩ := x64ZeroUpper32Op_trunc_m64 hz
      subst hm
      cases pa with
      | vec v => exact absurd rfl (hpa v)
      | gpr rs =>
        have htr : vllCoreTruncW x64Arch 64 .w32 (.gpr rs) rd = some (c, clob) := hop
        cases htr
        refine Machine.FallsTo.conseq (fallsTo_weaken_rd (vllMach_movW_spec x64Arch_wf
          (w := .w32) (rd := rd) (rs := rs))) ?_
        intro s' ⟨hg, _, hm⟩ _
        dsimp only [vllMach, Machine.PArgHolds] at ha1
        dsimp only [vllMach, x64Arch] at hg
        have ha64 : s.gpr rs = va := by simpa [GprHolds, BitVec.setWidth_eq] using ha1
        rw [ha64, writeSubX64_w32] at hg
        exact ⟨⟨va.setWidth 32, hwp.2, hg⟩, hm⟩
      | imm cv =>
        have htr : vllCoreTruncW x64Arch 64 .w32 (.imm cv) rd = some (c, clob) := hop
        cases htr; have hcv : cv = va := ha1; subst hcv
        refine Machine.FallsTo.conseq (fallsTo_weaken_rd (vllMach_movi_spec
          (A := x64Arch) (rd := rd) (imm := (cv.setWidth 32).setWidth 64))) ?_
        intro s' ⟨hg, hm⟩ _
        exact ⟨⟨cv.setWidth 32, hwp.2, hg⟩, hm⟩
    | add _ | sub _ | mul _ | and _ | or _ | xor _ | shl _ | lshr _ | ashr _ =>
      rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
      cases hrel with | cons ha1 hrel2 => cases hrel2 with | cons hb1 _ =>
      have hpb_ns : ∀ r ∈ pb.gprs, r ∉ x64Arch.abi.scratch := fun r hr =>
        ha r (List.mem_append_right _ (List.mem_append_left _ hr))
      dsimp only [OpCode.wp, Ty.hasFloat, lift2] at hwp
      exact coreBin32 _ hop hpb_ns ha1 hb1 hwp
    | neg _ =>
      rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
      cases hrel with | cons ha1 _ =>
      dsimp only [OpCode.wp, Ty.hasFloat, lift1] at hwp
      have hneg : vllCoreNegW x64Arch .w32 pa rd = some (c, clob) := hop
      have halu_eq : vllCoreAlu x64Arch .sub .w32 (.imm 0#32) pa rd =
          vllCoreNegW x64Arch .w32 pa rd := by
        cases pa <;> rfl
      exact coreBin32 .sub (halu_eq.trans hneg)
        (fun r hr => ha r (List.mem_append_left _ hr)) rfl ha1
        (by simpa [CoreAlu.eval, BitVec.zero_sub] using hwp)
    | not _ =>
      rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
      cases hrel with | cons ha1 _ =>
      dsimp only [OpCode.wp, lift1] at hwp
      have hnot : vllCoreNotW x64Arch .w32 pa rd = some (c, clob) := hop
      have hs0_mem : (.r10 : Reg64) ∈ x64Arch.abi.scratch := List.mem_cons_self
      have hnot_eval : va ^^^ (4294967295#32 : BitVec 32) = ~~~va :=
        BitVec.xor_allOnes (x := va)
      cases pa with
      | vec _ => cases hnot
      | gpr ra =>
        cases hnot
        exact op_zero32_alu32 (op := .xor) (rd := rd) (ra := ra)
          (pb := .imm ((~~~(0#64) : BitVec 64).setWidth 32))
          (sb := .imm (~~~0#64)) rfl rfl ha1 rfl
          (by simpa [CoreAlu.eval, hnot_eval] using hwp)
      | imm ca =>
        cases hnot
        refine Machine.FallsTo.weaken (Machine.FallsTo.comp (v₂ := ([] : List RegMm))
          (vllMach_movi_spec (A := x64Arch) (rd := .r10) (imm := ca.setWidth 64))
          fun s1 ⟨hg1, hm1⟩ _ => by
            have ha1' : (vllMach x64Arch).PArgHolds s1 (.bits 32) (.gpr .r10) va := by
              have hca : ca = va := ha1; subst hca
              dsimp only [vllMach] at hg1
              exact ⟨by decide, by
                change (s1.gpr .r10).setWidth 32 = ca
                rw [hg1, BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_eq]⟩
            exact Machine.FallsTo.conseq (op_zero32_alu32 (op := .xor) (rd := rd) (ra := .r10)
              (pb := .imm ((~~~(0#64) : BitVec 64).setWidth 32)) (sb := .imm (~~~0#64))
              (sf := false) (clob := x64Arch.aluClob .xor false)
              rfl (flagMask_sub_refl _) ha1' rfl (by simpa [CoreAlu.eval, hnot_eval] using hwp))
              (fun s2 ⟨hres, hm2⟩ _ => ⟨hres, hm2.trans hm1⟩))
          (fun r hr => by
            rw [List.cons_append, List.nil_append, List.mem_cons] at hr
            rcases hr with rfl | hr'
            · exact List.mem_cons_of_mem _ hs0_mem
            · exact hr')
          (fun _ h0 => nomatch h0)
          (by
            rw [show FlagMask.none ||| x64Arch.aluClob .xor false = x64Arch.aluClob .xor false from
              BitVec.zero_or]
            exact flagMask_sub_refl _)
    | ofBool _ =>
      rcases pas with ⟨pa, ⟨⟩⟩
      cases pa with
      | vec _ => cases hop
      | gpr _ | imm _ | flag _ =>
        exact absurd hhk (vllX64OpHook_ofBool32_ne_none _ rd vh fun _ e => by cases e)
    | zext m _ =>
      rcases pas with ⟨pa, ⟨⟩⟩
      have hm := x64ZeroUpper32Op_zext_m hz
      cases pa with
      | vec _ => rcases hm with rfl | rfl <;> cases hop
      | gpr _ | imm _ =>
        exact absurd hhk (vllX64OpHook_zext32_ne_none hm _ rd vh fun _ e => by cases e)
    | sext m _ =>
      rcases pas with ⟨pa, ⟨⟩⟩
      have hm := x64ZeroUpper32Op_sext_m hz
      cases pa with
      | vec _ => rcases hm with rfl | rfl <;> cases hop
      | gpr _ | imm _ =>
        exact absurd hhk (vllX64OpHook_sext32_ne_none hm _ rd vh fun _ e => by cases e)
    | cmp _ _ _ _ => cases hz
    | _ => cases hop

private theorem statusFlags_from_result_zero_sub (w : Vll.Width) (rv : BitVec w.bits)
    (f : StatusFlags) (cc : CondCode) :
    cc.interp (StatusFlags.from_result rv { cf := false, af := false, of := false }) =
      cc.interp (x64CmpFlags w rv 0#w.bits f) := by
  have h0u : (0#w.bits).unsigned = 0 := rfl
  have h0s : (0#w.bits).signed = 0 := by cases w <;> rfl
  simp only [x64CmpFlags, BitVec.sub_zero, h0u, h0s, Int.sub_zero, bne_self_eq_false]
  cases cc <;> rfl

private theorem opBinIns_ne_none {w : _root_.Width} {k : AluBinKind}
    {pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)} {rd : Reg64} {vh : VariantHint}
    (ha : ∀ v, pa ≠ .vec v) (hb : ∀ v, pb ≠ .vec v) :
    opBinIns w k pa pb rd vh ≠ none := by
  intro h
  dsimp only [opBinIns] at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases pa with
      | vec v => exact ha v rfl
      | imm _ =>
        cases pb with
        | vec v => exact hb v rfl
        | imm _ => cases h
        | gpr _ => repeat (first | cases h | split at h)
      | gpr _ =>
        cases pb with
        | vec v => exact hb v rfl
        | imm _ => cases h
        | gpr _ => repeat (first | cases h | split at h)

private theorem boolArgTo8I_ne_none (rd : Reg64) {pa : PArg Reg64 RegMm CondCode .bool}
    (h : ∀ v, pa ≠ .vec v) : (boolArgTo8I rd pa).isSome = true := by
  cases pa with
  | vec v => exact False.elim (h v rfl)
  | gpr _ | imm _ | flag _ => rfl

private theorem opBoolBinIns_ne_none {op : Bool → Bool → Bool}
    {insFn : Dst .W8 → Operand .W8 → Operation .W8}
    {pa pb : PArg Reg64 RegMm CondCode .bool} {rd : Reg64}
    (ha : ∀ v, pa ≠ .vec v) (hb : ∀ v, pb ≠ .vec v) :
    opBoolBinIns op insFn pa pb (.gpr rd) ≠ none := by
  intro h
  have hdst : ∀ f s, (∀ v, f ≠ .vec v) → (∀ v, s ≠ .vec v) →
      boolBinDstIns insFn rd f s = none → False := by
    intro f s hf hs hbn
    obtain ⟨d1, hd1⟩ := Option.isSome_iff_exists.mp (boolArgTo8I_ne_none rd hf)
    obtain ⟨d2, hd2⟩ := Option.isSome_iff_exists.mp (boolArgTo8I_ne_none .r10 hs)
    simp only [boolBinDstIns, hd1] at hbn
    cases s with
    | vec v => exact hs v rfl
    | gpr _ => cases hbn
    | imm _ | flag _ => simp only [hd2] at hbn; cases hbn
  have hself : ∀ o, (∀ v, o ≠ .vec v) → boolBinSelfIns insFn rd o = none → False := by
    intro o ho hbs
    obtain ⟨d2, hd2⟩ := Option.isSome_iff_exists.mp (boolArgTo8I_ne_none .r10 ho)
    dsimp only [boolBinSelfIns] at hbs
    cases o with
    | vec v => exact ho v rfl
    | gpr _ => cases hbs
    | imm _ | flag _ => simp only [hd2] at hbs; cases hbs
  dsimp only [opBoolBinIns] at h
  cases pa with
  | vec v => exact ha v rfl
  | imm _ =>
    cases pb with
    | vec v => exact hb v rfl
    | imm _ => cases h
    | gpr _ =>
      dsimp only at h; split at h
      · exact hself _ ha h
      · exact hdst _ _ ha hb h
    | flag _ => exact hdst _ _ ha hb h
  | flag _ =>
    cases pb with
    | vec v => exact hb v rfl
    | imm _ | flag _ => exact hdst _ _ ha hb h
    | gpr _ =>
      dsimp only at h; split at h
      · exact hself _ ha h
      · exact hdst _ _ ha hb h
  | gpr _ =>
    dsimp only at h; split at h
    · exact hself _ hb h
    · cases pb with
      | vec v => exact hb v rfl
      | imm _ | flag _ => exact hdst _ _ hb ha h
      | gpr _ =>
        dsimp only at h; split at h
        · exact hself _ ha h
        · exact hdst _ _ ha hb h

private theorem x64BitWidths_eq_false_of_none {w : Nat} (h : vllX64WidthOfBits? w = none) :
    x64Arch.abi.bitWidths.contains w = false := by
  by_cases hbw : x64Arch.abi.bitWidths.contains w = true
  · exfalso
    have hm : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by
      simpa [x64Arch, x64Frame, x64BitWidths] using hbw
    rcases hm with rfl | rfl | rfl | rfl <;> cases h
  · cases h0 : x64Arch.abi.bitWidths.contains w <;> simp_all

private abbrev CmpPairF (m : Nat) : Type :=
  PArg Reg64 RegMm CondCode (.bits m) × PArg Reg64 RegMm CondCode (.bits m)

private theorem opCmpIns_imm_gpr_ne_none (co : CmpOp) (xw : Vll.Width)
    (cx : BitVec xw.bits) (ry : Reg64) (pd : PDst Reg64 RegMm CondCode .bool)
    (b : Bool) (vh : VariantHint)
    (hfl : x64CmpFlagsOut co xw.bits (.imm cx) (.gpr ry) pd = some b) :
    vllX64OpHook (.cmp co (.bits xw.bits) .bool rfl) (.imm cx, .gpr ry, ()) (pd, ()) vh ≠
      none := by
  intro hhk
  have hbw : x64BitWidths.contains xw.bits = true := by cases xw <;> rfl
  simp only [x64CmpFlagsOut, hbw, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hfl
  have hop : (Amd64.withWidth (F := CmpPairF) xw.bits (.imm cx, .gpr ry) fun w (pa', pb') =>
      opCmpIns w co pa' pb' pd) = none := by
    dsimp only [vllX64OpHook, x64NativePair, x64Op, emitCleanPair, x64OpIns] at hhk
    simp only [hbw, ↓reduceIte] at hhk
    exact Option.map_eq_none_iff.mp (Option.map_eq_none_iff.mp hhk)
  cases pd with
  | vec _ => cases hfl
  | gpr _ =>
    cases xw <;> simp only [Amd64.withWidth, opCmpIns] at hop <;> split at hop <;> cases hop
  | flag cf =>
    cases xw <;> simp only [Amd64.withWidth, opCmpIns] at hop <;>
      (try rw [show (_root_.Width.W8 != _root_.Width.W64) = true from rfl] at hop) <;>
      (try rw [show (_root_.Width.W16 != _root_.Width.W64) = true from rfl] at hop) <;>
      (try rw [show (_root_.Width.W32 != _root_.Width.W64) = true from rfl] at hop) <;>
      (try rw [show (_root_.Width.W64 != _root_.Width.W64) = false from rfl] at hop) <;>
      (try rw [show Vll.Width.w8.bits = 8 from rfl] at hfl) <;>
      (try rw [show Vll.Width.w16.bits = 16 from rfl] at hfl) <;>
      (try rw [show Vll.Width.w32.bits = 32 from rfl] at hfl) <;>
      (try rw [show Vll.Width.w64.bits = 64 from rfl] at hfl) <;>
      by_cases h1 : (cf == condOf co.swap) = true <;>
      by_cases h2 : (cf == condOf co) = true <;>
      by_cases hf : fitsImm32 (cx.setWidth 64) = true <;>
      simp_all

private theorem vllX64OpHook_cmp_gpr_flag_eq (co : CmpOp) (xw : Vll.Width)
    (rx : Reg64) (pb : PArg Reg64 RegMm CondCode (.bits xw.bits)) (cf : CondCode)
    (b : Bool) (vh : VariantHint)
    (hfl : x64CmpFlagsOut co xw.bits (.gpr rx) pb (.flag cf) = some b)
    (hhk : vllX64OpHook (.cmp co (.bits xw.bits) .bool rfl) (.gpr rx, pb, ()) (.flag cf, ()) vh =
      none) :
    cf = condOf co := by
  have hbw : x64BitWidths.contains xw.bits = true := by cases xw <;> rfl
  simp only [x64CmpFlagsOut, hbw, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hfl
  by_cases hcf : (cf == condOf co) = true
  · exact condCode_eq_of_beq hcf
  · exfalso
    cases pb with
    | vec _ => cases hfl
    | gpr ry =>
      have hop : (Amd64.withWidth (F := CmpPairF) xw.bits (.gpr rx, .gpr ry) fun w (pa', pb') =>
          opCmpIns w co pa' pb' (.flag cf)) = none := by
        dsimp only [vllX64OpHook, x64NativePair, x64Op, emitCleanPair, x64OpIns] at hhk
        simp only [hbw, ↓reduceIte, hcf, Bool.false_eq_true] at hhk
        exact Option.map_eq_none_iff.mp (Option.map_eq_none_iff.mp hhk)
      cases xw <;> simp only [Amd64.withWidth, opCmpIns, cmpDirectIns] at hop <;>
        simp only [hcf, Bool.false_eq_true, ↓reduceIte] at hfl hop <;>
        split at hfl <;> simp_all
    | imm cy =>
      have hop : (Amd64.withWidth (F := CmpPairF) xw.bits (.gpr rx, .imm cy) fun w (pa', pb') =>
          opCmpIns w co pa' pb' (.flag cf)) = none := by
        dsimp only [vllX64OpHook, x64NativePair, x64Op, emitCleanPair, x64OpIns] at hhk
        simp only [hbw, ↓reduceIte, hcf, Bool.false_eq_true] at hhk
        exact Option.map_eq_none_iff.mp (Option.map_eq_none_iff.mp hhk)
      cases xw <;> simp only [Amd64.withWidth, opCmpIns, cmpDirectIns] at hop <;>
        simp only [hcf, Bool.false_eq_true, ↓reduceIte] at hfl hop <;>
        split at hfl <;> simp_all

private theorem width_ne_bits_of_none {w : Nat} (h : vllX64WidthOfBits? w = none) :
    ¬(w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) := by
  rintro (rfl | rfl | rfl | rfl) <;> cases h

private theorem vllX64OpHook_binAlu_ne_none (k : AluBinKind) (hk : k ≠ .mul) (w : _root_.Width)
    (pa pb : PArg Reg64 RegMm CondCode (.bits w.bits)) (rd : Reg64) (vh : VariantHint)
    (ha : ∀ v, pa ≠ .vec v) (hb : ∀ v, pb ≠ .vec v) :
    vllX64OpHook
      (match k with
        | .add => .add (.bits w.bits) | .sub => .sub (.bits w.bits)
        | .and => .and (.bits w.bits) | .or => .or (.bits w.bits)
        | .xor => .xor (.bits w.bits) | .mul => .mul (.bits w.bits))
      (pa, pb, ()) (.gpr rd, ()) vh ≠ none := by
  intro h
  have hfb : x64NativePair (x64Op
      (match k with
        | .add => .add (.bits w.bits) | .sub => .sub (.bits w.bits)
        | .and => .and (.bits w.bits) | .or => .or (.bits w.bits)
        | .xor => .xor (.bits w.bits) | .mul => .mul (.bits w.bits))
      (pa, pb, ()) (.gpr rd, ()) vh) ≠ none := by
    intro hn
    cases k with
    | mul => exact hk rfl
    | add | sub | and | or | xor =>
      dsimp only at hn
      cases w <;>
        exact opBinIns_ne_none ha hb (Option.map_eq_none_iff.mp (Option.map_eq_none_iff.mp
          (by dsimp only [x64NativePair, x64Op, emitCleanPair, x64OpIns, Amd64.withWidth] at hn
              exact hn)))
  cases k with
  | mul => exact hk rfl
  | add | sub | and | or | xor =>
    dsimp only [vllX64OpHook] at h
    split at h
    · split at h
      · cases pb with
        | vec v => exact hb v rfl
        | gpr _ | imm _ => cases h
      · exact hfb h
    · exact hfb h

private theorem aluZero_none_absurd {w : Nat} (k : AluBinKind) (hk : k ≠ .mul)
    {pa pb : PArg Reg64 RegMm CondCode (.bits w)} {rd : Reg64} {vh : VariantHint}
    {c : List (Instr x64Arch)} {clob : FlagMask}
    (hhk : vllX64OpHook (match k with
      | .add => .add (.bits w) | .sub => .sub (.bits w) | .and => .and (.bits w)
      | .or => .or (.bits w) | .xor => .xor (.bits w) | .mul => .mul (.bits w))
      (pa, pb, ()) (.gpr rd, ()) vh = none)
    (hop : vllCoreOp x64Arch (some ∘ condOf) (match k with
      | .add => .add (.bits w) | .sub => .sub (.bits w) | .and => .and (.bits w)
      | .or => .or (.bits w) | .xor => .xor (.bits w) | .mul => .mul (.bits w))
      (pa, pb, ()) (.gpr rd, ()) vh = some (c, clob)) : False := by
  cases k with
  | mul => exact hk rfl
  | add | sub | and | or | xor =>
    dsimp only [vllCoreOp, vllCoreBinTy, vllCoreBoolOrBits, vllCoreBinBits] at hop
    cases hbw : x64Arch.abi.bitWidths.contains w
    · simp only [hbw, Bool.false_eq_true, ↓reduceIte] at hop; cases hop
    · simp only [hbw, ↓reduceIte] at hop
      have hcases : (∃ hw : w = _root_.Width.W8.bits, True) ∨
          (∃ hw : w = _root_.Width.W16.bits, True) ∨
          (∃ hw : w = _root_.Width.W32.bits, True) ∨
          (∃ hw : w = _root_.Width.W64.bits, True) :=
        match w, hbw with
        | 8, _ => Or.inl ⟨rfl, trivial⟩
        | 16, _ => Or.inr (Or.inl ⟨rfl, trivial⟩)
        | 32, _ => Or.inr (Or.inr (Or.inl ⟨rfl, trivial⟩))
        | 64, _ => Or.inr (Or.inr (Or.inr ⟨rfl, trivial⟩))
      rcases hcases with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;>
        cases pa with
        | vec _ => cases hop
        | gpr _ | imm _ =>
          cases pb with
          | vec _ => cases hop
          | gpr _ | imm _ =>
            exact absurd hhk (vllX64OpHook_binAlu_ne_none _ hk _ _ _ rd vh
              (fun _ e => by cases e) (fun _ e => by cases e))

theorem vllX64PolicySpec : VllPolicySpec x64Arch vllX64NativeHooks where
  clearFlags_frame := clearFlags_x64
  cmpFlags_spec := x64Arch_cmpFlags_spec
  opHook_spec := fun hhk ha hd hrel hwp => vllX64OpHook_spec hhk ha hd hrel hwp
  storeHook_spec {h k t pa a c clob v s post} hhk hns hh hok := by
    obtain ⟨ds, h0, rfl⟩ := nativePair_some_iff (vllX64StoreHook_eq_native hhk)
    obtain ⟨ci, hci, hds⟩ := emitCleanPair_eq_some.mp h0
    have hcl := clean_small_of_cleanBound (cleanBound_x64StoreIns hci) (by decide)
    have hok_k : storeOk (x64Mach.mem (machToKraken s)) t
        (a.eval (x64Mach.getGpr (machToKraken s))) := by
      rw [machToKraken_gpr_eq s, machToKraken_mem_eq s]; exact hok
    rw [hds] at h0 ⊢
    refine x64Native_fallsTo_of_clean hcl.1 hcl.2
      (fun kh => x64_gprSpec.store_spec h0 hns (pArgHolds_to_x64Mach hh) hok_k) ?_
    intro sv' sk' hsim hq
    simpa only [vllMach, x64Mach, machToKraken, regsOfFn_get64] using
      (krakenSim_mem_eq hsim).trans hq
  load_zero32 := fun _ {_ _ _ _ _ _ s post v} hld _ _ hval =>
    vllCoreLoad_zx_zero32 x64Arch x64Arch_wf hld hval
  load_zext := fun _ {_ _ _ _ _ _ _ v s post} hld _ _ hval =>
    vllCoreLoad_zx_zext x64Arch x64Arch_wf hld hval
  op_zero32 := fun hz hop hdst ha hrd hrel hwp => vllX64Op_zero32 hz hop hdst ha hrd hrel hwp
  testOp_spec {h k w neg pa pb pd c clob va vb s post} hto ha hd hva hvb := by
    obtain ⟨ds, h0, rfl⟩ := nativePair_some_iff hto
    obtain ⟨ci, hci, hds⟩ := emitCleanPair_eq_some.mp h0
    have hcl := clean_small_of_cleanBound (cleanBound_x64TestOpIns hci) (by decide)
    rw [hds] at h0 ⊢
    refine x64Native_fallsTo_of_clean hcl.1 hcl.2 (fun kh => x64_gprSpec.testOp_spec h0 ha hd
      (pArgHolds_to_x64Mach hva) (pArgHolds_to_x64Mach hvb)) ?_
    intro sv' sk' hsim ⟨hpd, hm⟩
    exact ⟨pDstHolds_of_x64Mach hsim hpd, (krakenSim_mem_eq hsim).trans hm⟩
  cmpMem_spec {h k co w a pb pd c clob va vb s post} hcm ha hd hlv hvb := by
    obtain ⟨ds, h0, rfl⟩ := nativePair_some_iff hcm
    obtain ⟨ci, hci, hds⟩ := emitCleanPair_eq_some.mp h0
    have hcl := clean_small_of_cleanBound (cleanBound_x64CmpMemIns hci) (by decide)
    have hlv_k : loadVal (x64Mach.mem (machToKraken s)) (.bits w)
        (a.eval (x64Mach.getGpr (machToKraken s))) = some va := by
      rw [machToKraken_gpr_eq s, machToKraken_mem_eq s]; exact hlv
    rw [hds] at h0 ⊢
    refine x64Native_fallsTo_of_clean hcl.1 hcl.2 (fun kh => x64_gprSpec.cmpMem_spec h0 ha hd
      hlv_k (pArgHolds_to_x64Mach hvb)) ?_
    intro sv' sk' hsim ⟨hpd, hm⟩
    exact ⟨pDstHolds_of_x64Mach hsim hpd, (krakenSim_mem_eq hsim).trans hm⟩
  testMem_spec {h k w neg a pb pd c clob va vb s post} htm ha hd hlv hvb := by
    obtain ⟨ds, h0, rfl⟩ := nativePair_some_iff htm
    obtain ⟨ci, hci, hds⟩ := emitCleanPair_eq_some.mp h0
    have hcl := clean_small_of_cleanBound (cleanBound_x64TestMemIns hci) (by decide)
    have hlv_k : loadVal (x64Mach.mem (machToKraken s)) (.bits w)
        (a.eval (x64Mach.getGpr (machToKraken s))) = some va := by
      rw [machToKraken_gpr_eq s, machToKraken_mem_eq s]; exact hlv
    rw [hds] at h0 ⊢
    refine x64Native_fallsTo_of_clean hcl.1 hcl.2 (fun kh => x64_gprSpec.testMem_spec h0 ha hd
      hlv_k (pArgHolds_to_x64Mach hvb)) ?_
    intro sv' sk' hsim ⟨hpd, hm⟩
    exact ⟨pDstHolds_of_x64Mach hsim hpd, (krakenSim_mem_eq hsim).trans hm⟩
  loadSext_spec {h k m n rd a c clob v s post} hls _ _ hlv := by
    dsimp only [vllX64NativeHooks, vllX64LoadSext] at hls
    split at hls
    · cases hls
    · have go : ∀ (w : Vll.Width) (hw : m = w.bits),
          [.load w .sx rd a] = c → clob = FlagMask.none →
          (vllMach x64Arch).FallsTo x64Arch.condReads h k c (rd :: x64Arch.abi.scratch) [] clob s
            (fun s' => s'.gpr rd = v.signExtend 64 ∧ s'.mem = s.mem) post := by
        intro w hw hc hcl; subst hc hcl hw
        refine Machine.FallsTo.conseq (fallsTo_weaken_rd
          (vllMach_load_spec x64Arch_wf (ext := .sx) (rd := rd) hlv)) ?_
        intro s' ⟨hg, _, hm⟩ _
        exact ⟨hg, hm⟩
      split at hls
      · cases hls; exact go .w8 rfl rfl rfl
      · cases hls; exact go .w16 rfl rfl rfl
      · cases hls; exact go .w32 rfl rfl rfl
      · cases hls
  aluMem_spec {h k w memRhs code a pb rd c clob va vb P s post} ham ha hrd hlv hvb hwp := by
    obtain ⟨ds, h0, rfl⟩ := nativePair_some_iff ham
    obtain ⟨ci, hci, hds⟩ := emitCleanPair_eq_some.mp h0
    have hcl := clean_small_of_cleanBound (cleanBound_x64AluMemIns hci) (by decide)
    have hlv_k : loadVal (x64Mach.mem (machToKraken s)) (.bits w)
        (a.eval (x64Mach.getGpr (machToKraken s))) = some va := by
      rw [machToKraken_gpr_eq s, machToKraken_mem_eq s]; exact hlv
    rw [hds] at h0 ⊢
    refine x64Native_fallsTo_of_clean hcl.1 hcl.2 (fun kh => x64_gprSpec.aluMem_spec h0 ha hrd
      hlv_k (pArgHolds_to_x64Mach hvb) hwp) ?_
    rintro sv' sk' hsim ⟨⟨rv, hp, hg⟩, hm⟩
    exact ⟨⟨rv, hp, by simpa [krakenSim_gpr_eq hsim rd] using hg⟩,
      (krakenSim_mem_eq hsim).trans hm⟩
  aluMem_zero32 := fun _ {h k memRhs code a pb rd c clob va vb P s post}
      ham ha hrd hlv hvb hwp => by
    obtain ⟨ds, h0, rfl⟩ := nativePair_some_iff ham
    obtain ⟨ci, hci, hds⟩ := emitCleanPair_eq_some.mp h0
    have hcl := clean_small_of_cleanBound (cleanBound_x64AluMemIns hci) (by decide)
    have hlv_k : loadVal (x64Mach.mem (machToKraken s)) (.bits 32)
        (a.eval (x64Mach.getGpr (machToKraken s))) = some va := by
      rw [machToKraken_gpr_eq s, machToKraken_mem_eq s]; exact hlv
    rw [hds] at h0 ⊢
    refine x64Native_fallsTo_of_clean hcl.1 hcl.2 (fun kh => x64_gprSpec.aluMem_zero32 rfl h0 ha
      hrd hlv_k (pArgHolds_to_x64Mach hvb) hwp) ?_
    rintro sv' sk' hsim ⟨⟨rv, hp, hg⟩, hm⟩
    exact ⟨⟨rv, hp, (krakenSim_gpr_eq hsim rd).trans hg⟩, (krakenSim_mem_eq hsim).trans hm⟩
  jnzMem_spec {h k j a inv l c clob v8 b s post} hjz hc hl ha hlv hv8 hcont := by
    obtain ⟨ds, h0, rfl⟩ := nativePair_some_iff hjz
    obtain ⟨ds_pre, hds, hclean, hlen⟩ := x64JnzMem_splitClean h0
    rw [hds] at hc h0 hcont
    have hlen' : ((ds_pre ++ [ins (.jcc (if inv then .z else .nz) l)]).map
        (Instr.native (A := x64Arch))).length =
        (ds_pre ++ [ins (.jcc (if inv then .z else .nz) l)]).length := by
      simp
    rw [hlen'] at hcont
    refine x64Mach_splitJcc_to_vll (cond := if inv then !b else b) hclean hlen hc hl
      (fun kh hinf_k j_k hlab_k hcont_k => ?_) hcont
    have hlv_k : loadVal (x64Mach.mem (machToKraken s)) (.bits 8)
        (a.eval (x64Mach.getGpr (machToKraken s))) = some v8 := by
      rw [machToKraken_gpr_eq s, machToKraken_mem_eq s]; exact hlv
    exact x64_gprSpec.jnzMem_spec h0 hinf_k hlab_k ha hlv_k hv8 fun s' hfr hm => by
      have hh := hcont_k s' hfr hm
      simpa [hds] using hh
  rmwMem_spec {h k w code a pb c clob va vb P s post} hrm ha hlv hok hvb hwp := by
    obtain ⟨ds, h0, rfl⟩ := nativePair_some_iff hrm
    obtain ⟨ci, hci, hds⟩ := emitCleanPair_eq_some.mp h0
    have hcl := clean_small_of_cleanBound (cleanBound_x64RmwMemIns hci) (by decide)
    have hlv_k : loadVal (x64Mach.mem (machToKraken s)) (.bits w)
        (a.eval (x64Mach.getGpr (machToKraken s))) = some va := by
      rw [machToKraken_gpr_eq s, machToKraken_mem_eq s]; exact hlv
    have hok_k : storeOk (x64Mach.mem (machToKraken s)) (.bits w)
        (a.eval (x64Mach.getGpr (machToKraken s))) := by
      rw [machToKraken_gpr_eq s, machToKraken_mem_eq s]; exact hok
    rw [hds] at h0 ⊢
    refine x64Native_fallsTo_of_clean hcl.1 hcl.2 (fun kh => x64_gprSpec.rmwMem_spec h0 ha
      hlv_k hok_k (pArgHolds_to_x64Mach hvb) hwp) ?_
    rintro sv' sk' hsim ⟨rv, hp, hm⟩
    exact ⟨rv, hp, by
      simpa only [vllMach, x64Mach, machToKraken, regsOfFn_get64] using
        (krakenSim_mem_eq hsim).trans hm⟩
  leaArith_spec {h k w base? idx sc disp rd c clob vb vi s post} hlea hb hidx hrd hvb hvi := by
    obtain ⟨ds, h0, rfl⟩ := nativePair_some_iff hlea
    obtain ⟨ci, hci, hds⟩ := emitCleanPair_eq_some.mp h0
    have hcl := clean_small_of_cleanBound (cleanBound_x64LeaArithIns hci) (by decide)
    have hvb_k : ∀ r, base? = some r → GprHolds (x64Mach.getGpr (machToKraken s) r) (.bits w) vb :=
      fun r hr => by
        dsimp only [vllMach, x64Mach, machToKraken] at hvb ⊢
        simpa [regsOfFn_get64] using hvb r hr
    have hvi_k : GprHolds (x64Mach.getGpr (machToKraken s) idx) (.bits w) vi := by
      dsimp only [vllMach, x64Mach, machToKraken] at hvi ⊢
      simpa [regsOfFn_get64] using hvi
    rw [hds] at h0 ⊢
    refine x64Native_fallsTo_of_clean hcl.1 hcl.2
      (fun kh => x64_gprSpec.leaArith_spec h0 hb hidx hrd hvb_k hvi_k) ?_
    intro sv' sk' hsim ⟨hg, hm⟩
    dsimp only [vllMach] at ⊢
    exact ⟨by simpa [krakenSim_gpr_eq hsim rd] using hg, (krakenSim_mem_eq hsim).trans hm⟩
  leaArith_zero32 := fun _ {h k base? idx sc disp rd c clob vb vi s post}
      hlea hb hidx hrd hvb hvi => by
    obtain ⟨ds, h0, rfl⟩ := nativePair_some_iff hlea
    obtain ⟨ci, hci, hds⟩ := emitCleanPair_eq_some.mp h0
    have hcl := clean_small_of_cleanBound (cleanBound_x64LeaArithIns hci) (by decide)
    have hvb_k : ∀ r, base? = some r →
        GprHolds (x64Mach.getGpr (machToKraken s) r) (.bits 32) vb :=
      fun r hr => by
        dsimp only [vllMach, x64Mach, machToKraken] at hvb ⊢
        simpa [regsOfFn_get64] using hvb r hr
    have hvi_k : GprHolds (x64Mach.getGpr (machToKraken s) idx) (.bits 32) vi := by
      dsimp only [vllMach, x64Mach, machToKraken] at hvi ⊢
      simpa [regsOfFn_get64] using hvi
    rw [hds] at h0 ⊢
    refine x64Native_fallsTo_of_clean hcl.1 hcl.2
      (fun kh => x64_gprSpec.leaArith_zero32 rfl h0 hb hidx hrd hvb_k hvi_k) ?_
    intro sv' sk' hsim ⟨hg, hm⟩
    dsimp only [vllMach] at ⊢
    exact ⟨(krakenSim_gpr_eq hsim rd).trans hg, (krakenSim_mem_eq hsim).trans hm⟩
  jnzGprInv_spec {fn h k j r inv l b s post} hfn hc hl hr hb hcont := by
    cases hfn
    cases inv with
    | false =>
      exact vllMach_jnzGpr_spec x64Arch_wf hc hl hb hcont
    | true =>
      let ds_pre : List _root_.Directive := [ins8 (.test (.reg (b8 r)) (.reg (b8 r)))]
      have hvll : (vllX64JnzGprInv r true l).1 =
          (ds_pre ++ [ins (.jcc .z l)]).map (Instr.native (A := x64Arch)) := rfl
      have hds : (x64JnzGpr r true l).1 = ds_pre ++ [ins (.jcc .z l)] := rfl
      have hclean : ∀ d ∈ ds_pre, dirStraightClean d = true := fun d hd => by
        simp only [ds_pre, List.mem_singleton] at hd; subst hd; rfl
      have hlen : ds_pre.length < 2 ^ 60 := by dsimp only [ds_pre]; simp
      rw [hvll] at hc hcont
      rw [show (vllX64JnzGprInv r true l).2 = maskAll from rfl] at hcont
      have hlen' : ((ds_pre ++ [ins (.jcc .z l)]).map (Instr.native (A := x64Arch))).length =
          (ds_pre ++ [ins (.jcc .z l)]).length := by simp
      rw [hlen'] at hcont
      refine x64Mach_splitJcc_to_vll (cond := !b) hclean hlen hc hl
        (fun kh hinf_k j_k hlab_k hcont_k => ?_) hcont
      have hb_k : GprHolds (x64Mach.getGpr (machToKraken s) r) .bool b := by
        dsimp only [vllMach, x64Mach, machToKraken] at hb ⊢
        simpa [regsOfFn_get64] using hb
      rw [← hds] at hinf_k
      refine x64_gprSpec.jnzGprInv_spec (rfl : x64Gpr.jnzGprInv? = some x64JnzGpr)
        hinf_k hlab_k hr hb_k ?_
      intro s' hfr' hm'
      simpa [hds] using hcont_k s' hfr' hm'
  op_boolFlag_spec {h k sig code pas pd cc vh c clob vs P s post} hfl hop ha hd hrel hwp := by
    have nativeBool : x64NativePair (x64Op code pas (pd, ()) vh) = some (c, clob) →
        (vllMach x64Arch).FallsTo x64Arch.condReads h k c
          (pd.gprs ++ x64Arch.abi.scratch) [] clob s
          (fun s' => (∃ b : Bool, P (b, ()) ∧ (vllMach x64Arch).PDstHolds s' .bool pd b ∧
              (vllMach x64Arch).evalCond s' cc = b) ∧ s'.mem = s.mem) post := by
      intro hfb
      obtain ⟨ds, h0, rfl⟩ := nativePair_some_iff hfb
      obtain ⟨ci, hci, hds⟩ := emitCleanPair_eq_some.mp h0
      have hcl := clean_small_of_cleanBound (cleanBound_x64OpIns code pas (pd, ()) vh hci)
        (by decide)
      rw [hds] at h0 ⊢
      refine x64Native_fallsTo_of_clean hcl.1 hcl.2 (fun kh =>
        x64_gprSpec.op_boolFlag_spec hfl h0 ha hd (tRel_pArgHolds_to_x64Mach hrel) hwp) ?_
      rintro sv' sk' hsim ⟨⟨b, hp, hpd, hev⟩, hm⟩
      exact ⟨⟨b, hp, pDstHolds_of_x64Mach hsim hpd, (krakenSim_evalCond_eq hsim cc).trans hev⟩,
        (krakenSim_mem_eq hsim).trans hm⟩
    dsimp only [vllGprIsaOfHooks, vllX64NativeHooks] at hfl hop
    cases hhk : vllX64OpHook code pas (pd, ()) vh with
    | some res =>
      rw [hhk] at hop; cases hop
      cases pd with
      | vec _ | flag _ => simp [x64BoolFlagOut] at hfl
      | gpr rd =>
        cases code with
        | copy _ =>
          rcases pas with ⟨pa, ⟨⟩⟩; dsimp only [vllX64OpHook] at hhk
          cases pa <;> first | cases hhk | exact nativeBool hhk
        | not _ =>
          rcases pas with ⟨pa, ⟨⟩⟩; dsimp only [vllX64OpHook] at hhk
          exact nativeBool hhk
        | and _ | or _ | xor _ =>
          rcases pas with ⟨pa, pb, ⟨⟩⟩; dsimp only [vllX64OpHook] at hhk
          exact nativeBool hhk
        | _ => simp [x64BoolFlagOut] at hfl
    | none =>
      rw [hhk] at hop; dsimp only at hop
      cases pd with
      | vec _ | flag _ => simp [x64BoolFlagOut] at hfl
      | gpr rd =>
        cases code with
        | copy _ =>
          rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
          cases hrel with | cons ha1 _ =>
          cases pa with
          | gpr _ | vec _ | imm _ => simp [x64BoolFlagOut] at hfl hhk
          | flag cf =>
            simp only [x64BoolFlagOut, Option.some.injEq] at hfl; subst hfl
            cases hop
            dsimp only [OpCode.wp] at hwp
            have hcf : (vllMach x64Arch).evalCond s cf = va := ha1
            refine Machine.FallsTo.conseq (fallsTo_weaken_rd
              (vllMach_setcc_spec x64Arch_wf (rd := rd) (c := cf))) ?_
            intro s' ⟨hg, hm⟩ hfr
            have hfl_eq : (vllMach x64Arch).evalCond s' cf = (vllMach x64Arch).evalCond s cf :=
              hfr.2.2 cf (by simp [FlagMask.disjoint, FlagMask.none])
            rw [hcf] at hg
            exact ⟨⟨va, hwp, hg, hfl_eq.trans hcf⟩, hm⟩
        | not _ =>
          rcases pas with ⟨pa, ⟨⟩⟩
          cases pa with
          | gpr _ | flag _ =>
            dsimp only [vllX64OpHook, x64NativePair, x64Op, emitCleanPair, x64OpIns,
              opBoolNotIns] at hhk
            first | cases hhk | (split at hhk <;> cases hhk)
          | imm _ | vec _ => simp [x64BoolFlagOut] at hfl
        | and _ | or _ | xor _ =>
          rcases pas with ⟨pa, pb, ⟨⟩⟩
          cases pa <;> cases pb <;> first
            | (cases hfl; done)
            | (dsimp only [vllX64OpHook, x64NativePair, x64Op, emitCleanPair, x64OpIns] at hhk;
               exact absurd (Option.map_eq_none_iff.mp (Option.map_eq_none_iff.mp hhk))
                 (opBoolBinIns_ne_none (fun _ e => by cases e) (fun _ e => by cases e)))
        | _ => simp [x64BoolFlagOut] at hfl
  op_cmpFlags_spec {h k co w pa pb pd lhsFirst vh c clob va vb s post}
      hfl hop ha hd hva hvb := by
    dsimp only [vllGprIsaOfHooks, vllX64NativeHooks] at hfl hop
    cases hhk : vllX64OpHook (.cmp co (.bits w) .bool rfl) (pa, pb, ()) (pd, ()) vh with
    | some res =>
      rw [hhk] at hop; cases hop
      have hfb : x64NativePair (x64Op (.cmp co (.bits w) .bool rfl)
          (pa, pb, ()) (pd, ()) vh) = some (c, clob) := by
        dsimp only [vllX64OpHook] at hhk
        split at hhk
        · cases pa <;> cases pb <;> cases pd <;> dsimp only at hhk <;> first
            | cases hhk
            | exact hhk
            | (split at hhk <;> first | cases hhk | exact hhk)
        · exact hhk
      obtain ⟨ds, h0, rfl⟩ := nativePair_some_iff hfb
      obtain ⟨ci, hci, hds⟩ := emitCleanPair_eq_some.mp h0
      have hcl := clean_small_of_cleanBound (cleanBound_x64OpIns _ _ _ vh hci) (by decide)
      rw [hds] at h0 ⊢
      refine x64Native_fallsTo_of_clean hcl.1 hcl.2 (fun kh => x64_gprSpec.op_cmpFlags_spec
        hfl h0 ha hd (pArgHolds_to_x64Mach hva) (pArgHolds_to_x64Mach hvb)) ?_
      intro sv' sk' hsim ⟨hpd, hcmp, hm⟩
      exact ⟨pDstHolds_of_x64Mach hsim hpd, flagCmpOk_of_x64Mach hsim hcmp,
        (krakenSim_mem_eq hsim).trans hm⟩
    | none =>
      rw [hhk] at hop; dsimp only at hop
      have hbw : x64BitWidths.contains w = true := by
        cases hb : x64BitWidths.contains w
        · dsimp only [x64CmpFlagsOut] at hfl; rw [hb] at hfl; cases hfl
        · rfl
      obtain ⟨xw, hxw, hcore⟩ : ∃ (xw : Vll.Width) (hxw : w = xw.bits),
          vllCoreCmpW x64Arch (some ∘ condOf) co xw (hxw ▸ pa) (hxw ▸ pb) pd = some (c, clob) := by
        dsimp only [vllCoreOp, vllCoreCmp] at hop
        have hbw' : x64Arch.abi.bitWidths.contains w = true := hbw
        simp only [hbw', ↓reduceIte] at hop
        exact match w, hbw', pa, pb, hop with
          | 8, _, _, _, h0 => ⟨.w8, rfl, h0⟩ | 16, _, _, _, h0 => ⟨.w16, rfl, h0⟩
          | 32, _, _, _, h0 => ⟨.w32, rfl, h0⟩ | 64, _, _, _, h0 => ⟨.w64, rfl, h0⟩
      subst hxw
      have hbw' : x64BitWidths.contains xw.bits = true := by cases xw <;> rfl
      have hfl0 : x64CmpFlagsOut co xw.bits pa pb pd = some lhsFirst := hfl
      simp only [x64CmpFlagsOut, hbw', Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hfl
      cases pa with
      | vec _ => cases pd <;> cases hfl
      | imm cx =>
        cases pb with
        | vec _ => cases pd <;> cases hfl
        | imm cy =>
          cases pd with
          | vec _ | gpr _ => cases hfl
          | flag cf =>
            exfalso
            have hhop : (Amd64.withWidth (F := CmpPairF) xw.bits (.imm cx, .imm cy)
                fun w (pa', pb') => opCmpIns w co pa' pb' (.flag cf)) = none := by
              dsimp only [vllX64OpHook, x64NativePair, x64Op, emitCleanPair, x64OpIns] at hhk
              simp only [hbw', ↓reduceIte] at hhk
              exact Option.map_eq_none_iff.mp (Option.map_eq_none_iff.mp hhk)
            simp only [x64CmpFlagsOut, hbw', Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hfl0
            cases xw <;> simp only [Amd64.withWidth, opCmpIns, cmpDirectIns] at hhop <;>
              by_cases h1 : (cf == condOf co) = true <;>
              by_cases h2 : (cf == condOf co.swap) = true <;> simp_all
        | gpr ry =>
          cases pd with
          | vec _ => cases hfl
          | gpr rd =>
            exact absurd hhk (opCmpIns_imm_gpr_ne_none co xw cx ry (.gpr rd) lhsFirst vh hfl0)
          | flag cf =>
            exact absurd hhk (opCmpIns_imm_gpr_ne_none co xw cx ry (.flag cf) lhsFirst vh hfl0)
      | gpr rx =>
        have hlhs : lhsFirst = true := by
          have hbeq : (condOf co == condOf co) = true := by cases co <;> rfl
          cases pb with
          | vec _ => cases pd <;> cases hfl
          | gpr ry =>
            cases pd with
            | vec _ => cases hfl
            | gpr _ => simp only [Option.some.injEq] at hfl; exact hfl.symm
            | flag cf =>
              have hcf : cf = condOf co :=
                vllX64OpHook_cmp_gpr_flag_eq co xw rx (.gpr ry) cf lhsFirst vh hfl0 hhk
              subst hcf
              dsimp only [x64CmpFlagsOut] at hfl0
              rw [hbw', Bool.not_true, hbeq] at hfl0
              simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hfl0
              exact hfl0.symm
          | imm cy =>
            cases pd with
            | vec _ => cases hfl
            | gpr _ => simp only [Option.some.injEq] at hfl; exact hfl.symm
            | flag cf =>
              have hcf : cf = condOf co :=
                vllX64OpHook_cmp_gpr_flag_eq co xw rx (.imm cy) cf lhsFirst vh hfl0 hhk
              subst hcf
              dsimp only [x64CmpFlagsOut] at hfl0
              rw [hbw', Bool.not_true, hbeq] at hfl0
              simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hfl0
              exact hfl0.symm
        subst hlhs
        have hev_b : ∃ sb, vllSrcOfPArg xw pb = some sb ∧
            ∀ s0 : MachSt x64Arch, sb.evalW xw s0.gpr =
              match pb with
              | .gpr ry => (s0.gpr ry).setWidth xw.bits | .imm cb => cb | _ => 0 := by
          cases pb with
          | vec _ => cases hcore
          | gpr ry => exact ⟨.reg ry, rfl, fun _ => rfl⟩
          | imm cb =>
            refine ⟨.imm (cb.setWidth 64), rfl, fun _ => ?_⟩
            dsimp only [Src.evalW, Src.eval]
            rw [BitVec.setWidth_setWidth_of_le _ xw.bits_le_64, BitVec.setWidth_eq]
        obtain ⟨sb, hsb, hsb_eval⟩ := hev_b
        dsimp only [vllMach, Machine.PArgHolds] at hva hvb
        have ha_eq : (s.gpr rx).setWidth xw.bits = va := gprHolds_to_bits hva
        have hb_eq : sb.evalW xw s.gpr = vb := by
          rw [hsb_eval s]; cases pb with
          | vec _ => cases hsb
          | gpr _ => exact gprHolds_to_bits hvb
          | imm _ => exact hvb
        cases pd with
        | vec _ => cases hfl
        | flag cf =>
          have hcf_res : cf = condOf co ∧ c = [.cmp xw rx sb] ∧ clob = maskAll := by
            dsimp only [vllCoreCmpW, vllRegOfPArg, Function.comp_apply] at hcore
            rw [hsb] at hcore
            split at hcore
            · next c1 ra sb' h1 h2 =>
              injection h1 with h1'; cases h1'
              injection h2 with h2'; subst h2'
              split at hcore
              · next hcf =>
                simp only [Option.some.injEq, Prod.mk.injEq, List.nil_append] at hcore
                exact ⟨by simp only [beq_iff_eq] at hcf; exact hcf, hcore.1.symm, hcore.2.symm⟩
              · cases hcore
            · next _ _ hne => exact (hne [] rx sb rfl rfl).elim
          rcases hcf_res with ⟨rfl, rfl, rfl⟩
          refine Machine.FallsTo.conseq (Machine.FallsTo.weaken
            (vllMach_cmp_spec x64Arch_wf (w := xw) (lhs := rx) (rhs := sb))
            (fun _ hr => nomatch hr) (fun _ hr => nomatch hr) (flagMask_sub_refl _)) ?_
          intro s' ⟨hflg, hm⟩ _
          have hcc : ∀ c0 cc0, (some ∘ condOf) c0 = some cc0 →
              cc0.interp s'.flags = c0.evalBits va vb := fun c0 cc0 hcc0 => by
            rw [hflg, ha_eq, hb_eq]; exact x64Arch_cmpFlags_spec c0 cc0 xw va vb s.flags hcc0
          exact ⟨hcc co (condOf co) rfl, fun c0 cc0 _ hcc0 => hcc c0 cc0 hcc0, hm⟩
        | gpr rd =>
          dsimp only [vllCoreCmpW, vllRegOfPArg, Function.comp_apply] at hcore
          rw [hsb] at hcore
          simp only [Option.some.injEq, Prod.mk.injEq] at hcore; rcases hcore with ⟨rfl, rfl⟩
          change (vllMach x64Arch).FallsTo x64Arch.condReads h k
            ([Instr.cmp xw rx sb] ++ [Instr.setcc rd (condOf co)])
            ((PDst.gpr rd).gprs ++ x64Arch.abi.scratch) [] maskAll s _ post
          have hcmp_s1 : (vllMach x64Arch).FallsTo x64Arch.condReads h k [Instr.cmp xw rx sb]
              [] [] x64Arch.cmpClob s
              (fun s1 => s1.flags = x64Arch.cmpFlags xw va vb s.flags ∧ s1.mem = s.mem) post :=
            Machine.FallsTo.conseq (vllMach_cmp_spec x64Arch_wf (w := xw) (lhs := rx) (rhs := sb))
              fun s1 ⟨hflg1, hm1⟩ _ => ⟨by rw [← ha_eq, ← hb_eq]; exact hflg1, hm1⟩
          have hcomp : (vllMach x64Arch).FallsTo x64Arch.condReads h k
              ([Instr.cmp xw rx sb] ++ [Instr.setcc rd (condOf co)])
              ([] ++ [rd]) [] (x64Arch.cmpClob ||| FlagMask.none) s
              (fun s2 => (vllMach x64Arch).PDstHolds s2 .bool (.gpr rd) (co.evalBits va vb) ∧
                (∀ c0,
                  (vllMach x64Arch).evalCond s2 c0 = c0.interp (x64CmpFlags xw va vb s.flags)) ∧
                s2.mem = s.mem) post :=
            Machine.FallsTo.comp hcmp_s1 fun s1 ⟨hflg1, hm1⟩ _ =>
              Machine.FallsTo.conseq
                (vllMach_setcc_spec x64Arch_wf (rd := rd) (c := condOf co) (s := s1))
                fun s2 ⟨hpd, hm2⟩ hfr2 => by
                  have hcf2 : ∀ c0, (vllMach x64Arch).evalCond s2 c0 =
                      c0.interp (x64CmpFlags xw va vb s.flags) := fun c0 => by
                    rw [hfr2.2.2 c0 (by simp [FlagMask.disjoint, FlagMask.none])]
                    change c0.interp s1.flags = _
                    rw [hflg1]
                  have hev1 : (vllMach x64Arch).evalCond s1 (condOf co) = co.evalBits va vb := by
                    change (condOf co).interp s1.flags = _
                    rw [hflg1]
                    exact x64Arch_cmpFlags_spec co (condOf co) xw va vb s.flags rfl
                  rw [hev1] at hpd
                  exact ⟨hpd, hcf2, hm2.trans hm1⟩
          have hweaken : (vllMach x64Arch).FallsTo x64Arch.condReads h k
              ([Instr.cmp xw rx sb] ++ [Instr.setcc rd (condOf co)])
              ((PDst.gpr rd : PDst Reg64 RegMm CondCode .bool).gprs ++ x64Arch.abi.scratch) []
              maskAll s
              (fun s2 => (vllMach x64Arch).PDstHolds s2 .bool (.gpr rd) (co.evalBits va vb) ∧
                (∀ c0,
                  (vllMach x64Arch).evalCond s2 c0 = c0.interp (x64CmpFlags xw va vb s.flags)) ∧
                s2.mem = s.mem) post :=
            Machine.FallsTo.weaken hcomp
              (fun r hr => by
                simp only [List.nil_append, List.mem_singleton] at hr
                subst hr; simp [PDst.gprs])
              (fun _ hr => nomatch hr)
              (by simp [FlagMask.none])
          refine Machine.FallsTo.conseq hweaken ?_
          intro s2 ⟨hpd, hcf2, hm2⟩ _
          refine ⟨hpd, fun c0 cc0 _ hcc0 => ?_, hm2⟩
          rw [hcf2 cc0]
          exact x64Arch_cmpFlags_spec c0 cc0 xw va vb s.flags hcc0
  op_aluZero_spec {h k sig w code pas pd eqNe vh c clob vs P s post}
      hfl hcl hop ha hd hrel hwp := by
    have nativeAz : x64NativePair (x64Op code pas (pd, ()) vh) = some (c, clob) →
        (vllMach x64Arch).FallsTo x64Arch.condReads h k c
          (pd.gprs ++ x64Arch.abi.scratch) [] clob s
          (fun s' => (∃ rv : BitVec w, P (rv, ()) ∧ (vllMach x64Arch).PDstHolds s' (.bits w) pd rv ∧
              (∀ rd, w = 32 → pd = .gpr rd →
                vllX64NativeHooks.zeroUpper32Op code pas (.gpr rd, ()) = true →
                s'.gpr rd = rv.setWidth 64) ∧
              FlagCmpOk (vllMach x64Arch) (vllGprIsaOfHooks x64Arch vllX64NativeHooks)
                s' rv 0#w eqNe) ∧
            s'.mem = s.mem) post := by
      intro hfb
      obtain ⟨ds, h0, rfl⟩ := nativePair_some_iff hfb
      obtain ⟨ci, hci, hds⟩ := emitCleanPair_eq_some.mp h0
      have hcl_b := clean_small_of_cleanBound (cleanBound_x64OpIns code pas (pd, ()) vh hci)
        (by decide)
      rw [hds] at h0 ⊢
      refine x64Native_fallsTo_of_clean hcl_b.1 hcl_b.2 (fun kh => x64_gprSpec.op_aluZero_spec
        hfl hcl h0 ha hd (tRel_pArgHolds_to_x64Mach hrel) hwp) ?_
      rintro sv' sk' hsim ⟨⟨rv, hp, hpd, hz32, hfc⟩, hm⟩
      exact ⟨⟨rv, hp, pDstHolds_of_x64Mach hsim hpd, fun rd' hw32 hpr hzx =>
        (krakenSim_gpr_eq hsim rd').trans (hz32 rd' hw32 hpr hzx),
        flagCmpOk_of_x64Mach hsim hfc⟩, (krakenSim_mem_eq hsim).trans hm⟩
    have aluZeroCore : ∀ (op : CoreAlu) (xw : Vll.Width) (hn : w = xw.bits)
        (ra rd : Reg64) (pb : PArg Reg64 RegMm CondCode (.bits xw.bits))
        (sb : Src x64Arch) (va vb : BitVec xw.bits),
        (match pb with
          | .gpr rb => sb = .reg rb
          | .imm cb => sb = .imm (cb.setWidth 64)
          | .vec _ => False) →
        pd = .gpr rd →
        c = [.alu op xw rd ra sb true] →
        clob = maskAll →
        ((op = .add ∨ op = .sub) ∧ eqNe = true ∨
         (op = .and ∨ op = .or ∨ op = .xor) ∧ eqNe = false) →
        (vllMach x64Arch).PArgHolds s (.bits xw.bits) (.gpr ra) va →
        (vllMach x64Arch).PArgHolds s (.bits xw.bits) pb vb →
        P (hn ▸ op.eval xw va vb, ()) →
        (vllMach x64Arch).FallsTo x64Arch.condReads h k c
          (pd.gprs ++ x64Arch.abi.scratch) [] clob s
          (fun s' => (∃ rv : BitVec w, P (rv, ()) ∧
              (vllMach x64Arch).PDstHolds s' (.bits w) pd rv ∧
              (∀ rd', w = 32 → pd = .gpr rd' →
                vllX64NativeHooks.zeroUpper32Op code pas (.gpr rd', ()) = true →
                s'.gpr rd' = rv.setWidth 64) ∧
              FlagCmpOk (vllMach x64Arch) (vllGprIsaOfHooks x64Arch vllX64NativeHooks) s'
                rv 0#w eqNe) ∧ s'.mem = s.mem) post := by
      intro op xw hn ra rd pb sb va vb hsb hpd hc hclm hkind hva hvb hP
      subst hn hpd hc hclm
      dsimp only [vllMach, Machine.PArgHolds] at hva hvb
      have heval : sb.evalW xw s.gpr = vb := by
        cases pb with
        | vec _ => exact False.elim hsb
        | gpr rb => subst hsb; exact gprHolds_to_bits hvb
        | imm cb =>
          subst hsb; have hcb : cb = vb := hvb; subst hcb
          dsimp only [Src.evalW, Src.eval]
          rw [BitVec.setWidth_setWidth_of_le _ xw.bits_le_64, BitVec.setWidth_eq]
      have hva' : (s.gpr ra).setWidth xw.bits = va := gprHolds_to_bits hva
      have hcl_op : x64Arch.aluClob op true = maskAll := by
        rcases hkind with ⟨rfl | rfl, _⟩ | ⟨rfl | rfl | rfl, _⟩ <;> rfl
      refine Machine.FallsTo.conseq (Machine.FallsTo.weaken
        (vllMach_alu_spec x64Arch_wf (op := op) (w := xw) (rd := rd) (lhs := ra) (rhs := sb)
          (sf := true))
        (fun _ hr => by simp only [List.mem_singleton] at hr; subst hr; simp [PDst.gprs])
        (fun _ hr => nomatch hr) (by rw [hcl_op]; exact flagMask_sub_refl _)) ?_
      intro s' ⟨hg_sub, hg, hflg, hm⟩ _
      dsimp only [vllMach, x64Arch] at hg_sub hg hflg
      rw [hva', heval] at hg_sub hg hflg
      refine ⟨⟨op.eval xw va vb, hP, hg, fun rd' hw32 heq _ => ?_, ?_⟩, hm⟩
      · cases heq; cases xw <;> simp [Vll.Width.bits] at hw32
        simpa [writeSubX64_w32] using hg_sub
      · intro co cc hco_ok hcc
        simp only [vllGprIsaOfHooks, vllX64NativeHooks, Function.comp_apply, Option.some.injEq]
          at hcc
        subst hcc
        dsimp only [FlagCmpOk, Machine.evalCond, vllMach, x64Arch] at *
        rw [hflg]
        rcases hkind with ⟨rfl | rfl, rfl⟩ | ⟨rfl | rfl | rfl, rfl⟩
        · dsimp only [CoreAlu.eval, condOf, CondCode.interp, CmpOp.evalBits]
          rw [show x64AluFlags .add xw true va vb s.flags =
            StatusFlags.from_result (va + vb) {
              cf := (va + vb).unsigned != va.unsigned + vb.unsigned
              af := ((va + vb).take 4).unsigned != (va.take 4).unsigned + (vb.take 4).unsigned
              of := (va + vb).signed != va.signed + vb.signed } from rfl]
          simp only [StatusFlags.from_result, BitVec.zero]
          simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at hco_ok
          rcases hco_ok with rfl | rfl
          · by_cases he : va + vb = 0#xw.bits <;> simp [he]
          · by_cases he : va + vb = 0#xw.bits <;> simp [he]
        · simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at hco_ok
          dsimp only [CoreAlu.eval, condOf, CondCode.interp, CmpOp.evalBits]
          rw [show x64AluFlags .sub xw true va vb s.flags = x64CmpFlags xw va vb s.flags from rfl,
            x64CmpFlags, subFlags_zf_eq]
          rcases hco_ok with rfl | rfl
          · by_cases he : va = vb
            · subst he; simp [BitVec.sub_self]
            · have hne : va - vb ≠ 0#xw.bits := fun h => he (by
                rw [← BitVec.sub_add_cancel va vb, h, BitVec.zero_add])
              simp [he, hne]
          · by_cases he : va = vb
            · subst he; simp [BitVec.sub_self]
            · have hne : va - vb ≠ 0#xw.bits := fun h => he (by
                rw [← BitVec.sub_add_cancel va vb, h, BitVec.zero_add])
              simp [he, hne]
        · rw [show x64AluFlags .and xw true va vb s.flags =
            StatusFlags.from_result (va &&& vb) { cf := false, af := false, of := false } from rfl]
          rw [statusFlags_from_result_zero_sub xw (va &&& vb) s.flags (condOf co)]
          exact x64Arch_cmpFlags_spec co (condOf co) xw (va &&& vb) 0#xw.bits s.flags rfl
        · rw [show x64AluFlags .or xw true va vb s.flags =
            StatusFlags.from_result (va ||| vb) { cf := false, af := false, of := false } from rfl]
          rw [statusFlags_from_result_zero_sub xw (va ||| vb) s.flags (condOf co)]
          exact x64Arch_cmpFlags_spec co (condOf co) xw (va ||| vb) 0#xw.bits s.flags rfl
        · rw [show x64AluFlags .xor xw true va vb s.flags =
            StatusFlags.from_result (va ^^^ vb) { cf := false, af := false, of := false } from rfl]
          rw [statusFlags_from_result_zero_sub xw (va ^^^ vb) s.flags (condOf co)]
          exact x64Arch_cmpFlags_spec co (condOf co) xw (va ^^^ vb) 0#xw.bits s.flags rfl
    dsimp only [vllGprIsaOfHooks, vllX64NativeHooks] at hfl hop
    cases pd with
    | vec _ => simp [x64AluZeroOut] at hfl
    | gpr rd =>
      cases hhk : vllX64OpHook code pas (.gpr rd, ()) vh with
      | none =>
        rw [hhk] at hop; dsimp only at hop
        cases code with
        | neg _ =>
          rcases pas with ⟨pa, ⟨⟩⟩
          dsimp only [vllCoreOp, vllCoreNeg] at hop
          cases hbw : x64Arch.abi.bitWidths.contains w
          · simp only [hbw, Bool.false_eq_true, ↓reduceIte] at hop; cases hop
          · simp only [hbw, ↓reduceIte] at hop
            obtain ⟨xw, rfl, hcore⟩ : ∃ (xw : Vll.Width) (hw : w = xw.bits),
                vllCoreNegW x64Arch xw (hw ▸ pa) rd = some (c, clob) :=
              match w, hbw, pa, hop with
              | 8, _, _, h0 => ⟨.w8, rfl, h0⟩ | 16, _, _, h0 => ⟨.w16, rfl, h0⟩
              | 32, _, _, h0 => ⟨.w32, rfl, h0⟩ | 64, _, _, h0 => ⟨.w64, rfl, h0⟩
            cases pa with
            | vec _ => cases xw <;> cases hcore
            | gpr _ | imm _ =>
              dsimp only [vllX64OpHook, x64NativePair, x64Op, emitCleanPair, x64OpIns] at hhk
              cases xw <;> cases hhk
        | add _ =>
          rcases pas with ⟨pa, pb, ⟨⟩⟩
          exact absurd hop (fun hp => aluZero_none_absurd .add (by decide) hhk hp)
        | sub _ =>
          rcases pas with ⟨pa, pb, ⟨⟩⟩
          exact absurd hop (fun hp => aluZero_none_absurd .sub (by decide) hhk hp)
        | and _ =>
          rcases pas with ⟨pa, pb, ⟨⟩⟩
          exact absurd hop (fun hp => aluZero_none_absurd .and (by decide) hhk hp)
        | or _ =>
          rcases pas with ⟨pa, pb, ⟨⟩⟩
          exact absurd hop (fun hp => aluZero_none_absurd .or (by decide) hhk hp)
        | xor _ =>
          rcases pas with ⟨pa, pb, ⟨⟩⟩
          exact absurd hop (fun hp => aluZero_none_absurd .xor (by decide) hhk hp)
        | _ => simp [x64AluZeroOut] at hfl
      | some res =>
        rw [hhk] at hop; cases hop
        cases code with
        | neg _ => exact nativeAz hhk
        | add _ =>
          rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
          obtain ⟨ha1, hb1⟩ := parg_trel2 hrel
          simp only [x64AluZeroOut, Option.some.injEq] at hfl; subst hfl
          dsimp only [OpCode.wp, Ty.hasFloat, lift2] at hwp
          dsimp only [vllX64OpHook] at hhk
          cases hw : vllX64WidthOfBits? w with
          | none =>
            rw [hw] at hhk; dsimp only at hhk; exact nativeAz hhk
          | some xw =>
            cases vh with
            | default =>
              cases pa with
              | gpr ra =>
                rw [hw] at hhk; dsimp only at hhk
                by_cases hrr : (ra == rd) = true
                · simp only [hrr, ↓reduceIte] at hhk
                  obtain rfl := vllX64WidthOfBits_eq hw
                  have hreq : ra = rd := reg64_eq_of_beq hrr
                  cases pb with
                  | vec _ => exact nativeAz hhk
                  | gpr rb =>
                    cases hhk
                    exact aluZeroCore .add xw rfl rd rd (.gpr rb) (.reg rb) va vb rfl rfl rfl rfl
                      (Or.inl ⟨Or.inl rfl, rfl⟩) (hreq ▸ ha1) hb1 hwp
                  | imm cb =>
                    cases hhk
                    exact aluZeroCore .add xw rfl rd rd (.imm cb) (.imm (cb.setWidth 64)) va vb
                      rfl rfl rfl rfl (Or.inl ⟨Or.inl rfl, rfl⟩) (hreq ▸ ha1) hb1 hwp
                · simp only [hrr, Bool.false_eq_true, ↓reduceIte] at hhk; exact nativeAz hhk
              | _ =>
                rw [hw] at hhk; dsimp only at hhk; exact nativeAz hhk
            | _ =>
              rw [hw] at hhk; dsimp only at hhk; exact nativeAz hhk
        | sub _ =>
          rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
          obtain ⟨ha1, hb1⟩ := parg_trel2 hrel
          simp only [x64AluZeroOut, Option.some.injEq] at hfl; subst hfl
          dsimp only [OpCode.wp, Ty.hasFloat, lift2] at hwp
          dsimp only [vllX64OpHook] at hhk
          cases hw : vllX64WidthOfBits? w with
          | none =>
            rw [hw] at hhk; dsimp only at hhk; exact nativeAz hhk
          | some xw =>
            cases vh with
            | default =>
              cases pa with
              | gpr ra =>
                rw [hw] at hhk; dsimp only at hhk
                by_cases hrr : (ra == rd) = true
                · simp only [hrr, ↓reduceIte] at hhk
                  obtain rfl := vllX64WidthOfBits_eq hw
                  have hreq : ra = rd := reg64_eq_of_beq hrr
                  cases pb with
                  | vec _ => exact nativeAz hhk
                  | gpr rb =>
                    cases hhk
                    exact aluZeroCore .sub xw rfl rd rd (.gpr rb) (.reg rb) va vb rfl rfl rfl rfl
                      (Or.inl ⟨Or.inr rfl, rfl⟩) (hreq ▸ ha1) hb1 hwp
                  | imm cb =>
                    cases hhk
                    exact aluZeroCore .sub xw rfl rd rd (.imm cb) (.imm (cb.setWidth 64)) va vb
                      rfl rfl rfl rfl (Or.inl ⟨Or.inr rfl, rfl⟩) (hreq ▸ ha1) hb1 hwp
                · simp only [hrr, Bool.false_eq_true, ↓reduceIte] at hhk; exact nativeAz hhk
              | _ =>
                rw [hw] at hhk; dsimp only at hhk; exact nativeAz hhk
            | _ =>
              rw [hw] at hhk; dsimp only at hhk; exact nativeAz hhk
        | and _ =>
          rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
          obtain ⟨ha1, hb1⟩ := parg_trel2 hrel
          simp only [x64AluZeroOut, Option.some.injEq] at hfl; subst hfl
          dsimp only [OpCode.wp, Ty.hasFloat, lift2] at hwp
          dsimp only [vllX64OpHook] at hhk
          cases hw : vllX64WidthOfBits? w with
          | none =>
            rw [hw] at hhk; dsimp only at hhk; exact nativeAz hhk
          | some xw =>
            cases vh with
            | default =>
              cases pa with
              | gpr ra =>
                rw [hw] at hhk; dsimp only at hhk
                split at hhk
                · obtain rfl := vllX64WidthOfBits_eq hw
                  cases pb with
                  | vec _ => exact nativeAz hhk
                  | gpr rb =>
                    cases hhk
                    exact aluZeroCore .and xw rfl ra rd (.gpr rb) (.reg rb) va vb rfl rfl rfl rfl
                      (Or.inr ⟨Or.inl rfl, rfl⟩) ha1 hb1 hwp
                  | imm cb =>
                    cases hhk
                    exact aluZeroCore .and xw rfl ra rd (.imm cb) (.imm (cb.setWidth 64)) va vb
                      rfl rfl rfl rfl (Or.inr ⟨Or.inl rfl, rfl⟩) ha1 hb1 hwp
                · exact nativeAz hhk
              | _ =>
                rw [hw] at hhk; dsimp only at hhk; exact nativeAz hhk
            | _ =>
              rw [hw] at hhk; dsimp only at hhk; exact nativeAz hhk
        | or _ =>
          rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
          obtain ⟨ha1, hb1⟩ := parg_trel2 hrel
          simp only [x64AluZeroOut, Option.some.injEq] at hfl; subst hfl
          dsimp only [OpCode.wp, Ty.hasFloat, lift2] at hwp
          dsimp only [vllX64OpHook] at hhk
          cases hw : vllX64WidthOfBits? w with
          | none =>
            rw [hw] at hhk; dsimp only at hhk; exact nativeAz hhk
          | some xw =>
            cases vh with
            | default =>
              cases pa with
              | gpr ra =>
                rw [hw] at hhk; dsimp only at hhk
                split at hhk
                · obtain rfl := vllX64WidthOfBits_eq hw
                  cases pb with
                  | vec _ => exact nativeAz hhk
                  | gpr rb =>
                    cases hhk
                    exact aluZeroCore .or xw rfl ra rd (.gpr rb) (.reg rb) va vb rfl rfl rfl rfl
                      (Or.inr ⟨Or.inr (Or.inl rfl), rfl⟩) ha1 hb1 hwp
                  | imm cb =>
                    cases hhk
                    exact aluZeroCore .or xw rfl ra rd (.imm cb) (.imm (cb.setWidth 64)) va vb
                      rfl rfl rfl rfl (Or.inr ⟨Or.inr (Or.inl rfl), rfl⟩) ha1 hb1 hwp
                · exact nativeAz hhk
              | _ =>
                rw [hw] at hhk; dsimp only at hhk; exact nativeAz hhk
            | _ =>
              rw [hw] at hhk; dsimp only at hhk; exact nativeAz hhk
        | xor _ =>
          rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
          obtain ⟨ha1, hb1⟩ := parg_trel2 hrel
          simp only [x64AluZeroOut, Option.some.injEq] at hfl; subst hfl
          dsimp only [OpCode.wp, Ty.hasFloat, lift2] at hwp
          dsimp only [vllX64OpHook] at hhk
          cases hw : vllX64WidthOfBits? w with
          | none =>
            rw [hw] at hhk; dsimp only at hhk; exact nativeAz hhk
          | some xw =>
            cases vh with
            | default =>
              cases pa with
              | gpr ra =>
                rw [hw] at hhk; dsimp only at hhk
                split at hhk
                · obtain rfl := vllX64WidthOfBits_eq hw
                  cases pb with
                  | vec _ => exact nativeAz hhk
                  | gpr rb =>
                    cases hhk
                    exact aluZeroCore .xor xw rfl ra rd (.gpr rb) (.reg rb) va vb rfl rfl rfl rfl
                      (Or.inr ⟨Or.inr (Or.inr rfl), rfl⟩) ha1 hb1 hwp
                  | imm cb =>
                    cases hhk
                    exact aluZeroCore .xor xw rfl ra rd (.imm cb) (.imm (cb.setWidth 64)) va vb
                      rfl rfl rfl rfl (Or.inr ⟨Or.inr (Or.inr rfl), rfl⟩) ha1 hb1 hwp
                · exact nativeAz hhk
              | _ =>
                rw [hw] at hhk; dsimp only at hhk; exact nativeAz hhk
            | _ =>
              rw [hw] at hhk; dsimp only at hhk; exact nativeAz hhk
        | _ => simp [x64AluZeroOut] at hfl
  testOp_boolFlag_spec := fun _ {_ _ _ _ _ _ _ _ _ _ _ _ s post} hcl hcc hto ha hd hva hvb => by
    obtain ⟨ds, h0, rfl⟩ := nativePair_some_iff hto
    obtain ⟨ci, hci, hds⟩ := emitCleanPair_eq_some.mp h0
    have hcl_b := clean_small_of_cleanBound (cleanBound_x64TestOpIns hci) (by decide)
    rw [hds] at h0 ⊢
    refine x64Native_fallsTo_of_clean hcl_b.1 hcl_b.2 (fun kh => x64_gprSpec.testOp_boolFlag_spec
      rfl hcl hcc h0 ha hd (pArgHolds_to_x64Mach hva) (pArgHolds_to_x64Mach hvb)) ?_
    intro sv' sk' hsim ⟨hpd, hev, hm⟩
    exact ⟨pDstHolds_of_x64Mach hsim hpd, (krakenSim_evalCond_eq hsim _).trans hev,
      (krakenSim_mem_eq hsim).trans hm⟩
  testMem_boolFlag_spec := fun _ {_ _ _ _ a _ _ _ _ va _ _ s post} hcl hcc htm ha hd hlv hvb => by
    obtain ⟨ds, h0, rfl⟩ := nativePair_some_iff htm
    obtain ⟨ci, hci, hds⟩ := emitCleanPair_eq_some.mp h0
    have hcl_b := clean_small_of_cleanBound (cleanBound_x64TestMemIns hci) (by decide)
    have hlv_k : loadVal (x64Mach.mem (machToKraken s)) _
        (a.eval (x64Mach.getGpr (machToKraken s))) = some va := by
      rw [machToKraken_gpr_eq s, machToKraken_mem_eq s]; exact hlv
    rw [hds] at h0 ⊢
    refine x64Native_fallsTo_of_clean hcl_b.1 hcl_b.2 (fun kh => x64_gprSpec.testMem_boolFlag_spec
      rfl hcl hcc h0 ha hd hlv_k (pArgHolds_to_x64Mach hvb)) ?_
    intro sv' sk' hsim ⟨hpd, hev, hm⟩
    exact ⟨pDstHolds_of_x64Mach hsim hpd, (krakenSim_evalCond_eq hsim _).trans hev,
      (krakenSim_mem_eq hsim).trans hm⟩
  cmpMem_flags_spec {h k co w a pb pd lhsFirst c clob va vb s post} hfl hcm ha hd hlv hvb := by
    obtain ⟨ds, h0, rfl⟩ := nativePair_some_iff hcm
    obtain ⟨ci, hci, hds⟩ := emitCleanPair_eq_some.mp h0
    have hcl_b := clean_small_of_cleanBound (cleanBound_x64CmpMemIns hci) (by decide)
    have hlv_k : loadVal (x64Mach.mem (machToKraken s)) (.bits w)
        (a.eval (x64Mach.getGpr (machToKraken s))) = some va := by
      rw [machToKraken_gpr_eq s, machToKraken_mem_eq s]; exact hlv
    rw [hds] at h0 ⊢
    refine x64Native_fallsTo_of_clean hcl_b.1 hcl_b.2 (fun kh => x64_gprSpec.cmpMem_flags_spec
      hfl h0 ha hd hlv_k (pArgHolds_to_x64Mach hvb)) ?_
    intro sv' sk' hsim ⟨hpd, hcmp, hm⟩
    exact ⟨pDstHolds_of_x64Mach hsim hpd, flagCmpOk_of_x64Mach hsim hcmp,
      (krakenSim_mem_eq hsim).trans hm⟩
  moviDeadFlags?_spec := fun hfn => by cases hfn; exact vllX64_moviDeadFlags_spec
  vecSpec := vllX64VecTarget

/-- Verified hybrid lowering policy for SysV x86-64 on `BedrockMach` L1 (`x64Arch`). -/
@[expose] def vllX64Policy : VllPolicy x64Arch where
  hooks := vllX64NativeHooks
  spec := vllX64PolicySpec

/-- `BedrockMach` L1 x86-64 `Isa` instance. -/
abbrev vllX64Isa : Isa := vllIsa x64Arch vllX64Policy

/-- `BedrockMach` L1 x86-64 `LegalTarget` (`= x64LegalTarget`). -/
abbrev vllX64LegalTarget : LegalTarget := vllLegalTarget x64Arch vllX64Policy

/-- Verified `BedrockMach` L1 x86-64 `Target`. -/
@[expose] def vllX64Target : Target := vllTarget x64Arch x64Arch_wf vllX64Policy

/-- Structural `Rega.LabelClean` proof for `vllX64Target.toIsa`. -/
theorem vllX64LabelClean : Rega.LabelClean vllX64Isa :=
  vllLabelClean x64Arch vllX64Policy vllX64Hooks_noLab


end LeanQbe.T.Amd64
