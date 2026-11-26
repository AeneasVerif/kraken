module

public import LeanQbe.T.Vll.RegaInst
public import LeanQbe.T.Arm64.VllArm64
public import LeanQbe.T.Arm64.VllAsmArm64
public import LeanQbe.T.Arm64.Targ
public import LeanQbe.T.Arm64.VllFactorArm64Save
import LeanQbe.T.Arm64.VllFactorArm640
import LeanQbe.T.Arm64.VllFactorArm64CoreLemmas
import LeanQbe.T.Arm64.VllFactorArm64FlagLemmas
import LeanQbe.T.RegaLemmas
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.TargetLemmas
import LeanQbe.T.AbiLemmas

/-!
# `BedrockMach` L1 AArch64 Hooks, Verified Policy, & Targets (`Arm64.VllFactorArm641`)

Instantiates `VllNativeHooks arm64Arch`, `VllPolicySpec arm64Arch`, `vllArmPolicy`,
`vllArmTarget`, and `vllArmStrictTarget` over `BedrockMach` L1 (`Instr arm64Arch`), plus
label-freedom (`vllArmHooksNoLab`, `vllArmLabelClean`, `vllArmStrictLabelClean`).

Factored out of `Arm64.VllFactorArm64` to keep every module well under `2,500` LOC with zero public
`*Lemmas*` imports and zero `Amd64`/`Kraken.X64` imports.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open LeanQbe.T
open LeanQbe.T.Vll
open Std Std.ExtHashMap

/-! ## 1. AArch64 `VllNativeHooks` (Maximally Core `Instr arm64Arch`, Minimal `.native`) -/

/-- Store hook: delegates GP-register stores on valid addresses to core `vllCoreStore` (`.store`),
falling back to `.native` `armStore` only for `.SP`/`.imm`/`.flag` operands. -/
@[expose] def vllArmStoreHook (t : Ty) (pa : PArg Arm64.Reg Empty ArmCond t)
    (a : AddrArg Arm64.Reg) : Option (List (Instr arm64Arch) × FlagMask) :=
  match t, pa with
  | .bool, .gpr (.reg _) | .bits 8, .gpr (.reg _) | .bits 16, .gpr (.reg _)
  | .bits 32, .gpr (.reg _) | .bits 64, .gpr (.reg _) => none
  | _, _ => wrapArmNative (armStore t pa a)

/-- Scalar `opHook` lowering hot scalar operations into first-class core `Instr arm64Arch`
(either directly or by returning `none` to delegate to `vllCoreOp`), using `.native` `armOp`
only for Arm64-specific or fused idioms (`CSEL`, `SDIV`/`MSUB`, `REV`/`CLZ`, `ORR_s W64`,
negated-imm `CMN`, sub-word 8/16-bit ALU/cmp, bool `CSEL`/`CSINC`). -/
@[expose] def vllArmOpHook {sig rs : List Ty} (code : OpCode sig rs)
    (pas : Tup (PArg Arm64.Reg Empty ArmCond) sig)
    (dsts : Tup (PDst Arm64.Reg Empty ArmCond) rs) (vh : VariantHint) :
    Option (List (Instr arm64Arch) × FlagMask) :=
  let fb := wrapArmNative (armOp code pas dsts vh)
  match code with
  | .copy t =>
    match t, dsts, pas with
    | .bool, (.gpr (.reg d), ()), (.gpr (.reg r), ()) =>
      some ([.mov .w32 (.reg d) (.reg r)], maskNone)
    | .bool, (.gpr (.reg _), ()), (.imm _, ())
    | .bool, (.gpr (.reg _), ()), (.flag _, ()) => none
    | .bits n, (.gpr (.reg d), ()), (.gpr (.reg r), ()) =>
      if n == 8 || n == 16 || n == 32 then some ([.mov .w32 (.reg d) (.reg r)], maskNone) else fb
    | .bits n, (.gpr (.reg _), ()), (.imm _, ()) =>
      if [8, 16, 32, 64].contains n then none else fb
    | _, _, _ => fb
  | .bitcast t u _ =>
    match t, u, dsts, pas with
    | .bits m, .bits n, (.gpr (.reg d), ()), (.gpr (.reg r), ()) =>
      if [8, 16, 32, 64].contains m && [8, 16, 32, 64].contains n &&
          (m == 8 || m == 16 || m == 32) then
        some ([.mov .w32 (.reg d) (.reg r)], maskNone)
      else fb
    | .bits m, .bits n, (.gpr (.reg _), ()), (.imm _, ()) =>
      if [8, 16, 32, 64].contains m && [8, 16, 32, 64].contains n then none else fb
    | _, _, _, _ => fb
  | .zext m n =>
    match dsts, pas with
    | (.gpr (.reg _), ()), (.imm _, ()) =>
      if [8, 16, 32, 64].contains m && [8, 16, 32, 64].contains n && Nat.ble m n then none else fb
    | (.gpr (.reg d), ()), (.gpr (.reg r), ()) =>
      if [8, 16, 32, 64].contains m && [8, 16, 32, 64].contains n && Nat.ble m n then
        if m == 8 then some ([.mov .w8 (.reg d) (.reg r)], maskNone)
        else if m == 16 then some ([.mov .w16 (.reg d) (.reg r)], maskNone)
        else if m == 32 then some ([.mov .w32 (.reg d) (.reg r)], maskNone)
        else fb
      else fb
    | _, _ => fb
  | .trunc m n =>
    match dsts, pas with
    | (.gpr (.reg _), ()), (.imm _, ()) =>
      if [8, 16, 32, 64].contains m && [8, 16, 32, 64].contains n && Nat.ble n m then none else fb
    | (.gpr (.reg d), ()), (.gpr (.reg r), ()) =>
      if [8, 16, 32, 64].contains m && [8, 16, 32, 64].contains n && Nat.ble n m &&
          (n == 8 || n == 16 || n == 32) then
        some ([.mov .w32 (.reg d) (.reg r)], maskNone)
      else fb
    | _, _ => fb
  | .ofBool n =>
    match dsts, pas with
    | (.gpr (.reg _), ()), (.imm _, ()) =>
      if [8, 16, 32, 64].contains n then none else fb
    | (.gpr (.reg d), ()), (.flag c, ()) =>
      if [8, 16, 32, 64].contains n then some ([.setcc (.reg d) c], maskNone) else fb
    | (.gpr (.reg d), ()), (.gpr (.reg r), ()) =>
      if [8, 16, 32, 64].contains n then some ([.mov .w8 (.reg d) (.reg r)], maskNone) else fb
    | _, _ => fb
  | .not t =>
    match t, dsts, pas with
    | .bool, (.gpr (.reg d), ()), (.imm b, ()) =>
      some ([.movi (.reg d) (BitVec.ofNat 64 (!b).toNat)], maskNone)
    | .bool, (.gpr (.reg d), ()), (.flag c, ()) =>
      some ([.setcc (.reg d) (armNegCond c)], maskNone)
    | .bool, (.gpr (.reg d), ()), (.gpr (.reg r), ()) =>
      some ([.alu .xor .w32 (.reg d) (.reg r) (.imm 1#64) false], maskNone)
    | .bits n, (.gpr (.reg d), ()), (.imm c, ()) =>
      if [8, 16, 32, 64].contains n then some ([.movi (.reg d) ((~~~c).setWidth 64)], maskNone)
      else fb
    | _, _, _ => fb
  | .neg t =>
    match t, dsts, pas with
    | .bits n, (.gpr (.reg d), ()), (.imm c, ()) =>
      if [8, 16, 32, 64].contains n then some ([.movi (.reg d) ((-c).setWidth 64)], maskNone)
      else fb
    | _, _, _ => fb
  | .add t =>
    match t, dsts, pas with
    | .bits n, (.gpr (.reg _), ()), (.gpr (.reg _), .gpr (.reg _), ()) =>
      if n == 32 || n == 64 then none else fb
    | .bits n, (.gpr (.reg d), ()), (.gpr (.reg ra), .imm cb, ()) =>
      if n == 32 || n == 64 then
        if (armImm12? cb).isSome || (armImm12? (-cb)).isNone then none
        else some ([.alu .sub (if n == 64 then .w64 else .w32) (.reg d) (.reg ra)
          (.imm ((-cb).setWidth 64)) false], maskNone)
      else fb
    | _, _, _ => fb
  | .sub t =>
    match t, dsts, pas with
    | .bits n, (.gpr (.reg _), ()), (.gpr (.reg _), .gpr (.reg _), ()) =>
      if n == 32 || n == 64 then none else fb
    | .bits n, (.gpr (.reg d), ()), (.gpr (.reg ra), .imm cb, ()) =>
      if n == 32 || n == 64 then
        if (armImm12? cb).isSome || (armImm12? (-cb)).isNone then none
        else some ([.alu .add (if n == 64 then .w64 else .w32) (.reg d) (.reg ra)
          (.imm ((-cb).setWidth 64)) false], maskNone)
      else fb
    | _, _, _ => fb
  | .mul t =>
    match t, dsts, pas with
    | .bits n, (.gpr (.reg _), ()), (.gpr (.reg _), .gpr (.reg _), ()) =>
      if n == 32 || n == 64 then none else fb
    | _, _, _ => fb
  | .and t | .or t | .xor t =>
    match t, dsts, pas with
    | .bits n, (.gpr (.reg _), ()), (.gpr (.reg _), .gpr (.reg _), ())
    | .bits n, (.gpr (.reg _), ()), (.gpr (.reg _), .imm _, ()) =>
      if n == 32 || n == 64 then none else fb
    | _, _, _ => fb
  | .shl t | .lshr t | .ashr t =>
    match t, dsts, pas with
    | .bits n, (.gpr (.reg _), ()), (.gpr (.reg _), .gpr (.reg _), ())
    | .bits n, (.gpr (.reg _), ()), (.gpr (.reg _), .imm _, ())
    | .bits n, (.gpr (.reg _), ()), (.imm _, .gpr (.reg _), ()) =>
      if n == 32 || n == 64 then none else fb
    | _, _, _ => fb
  | .cmp o t m hm =>
    match t, m, hm, pas, dsts with
    | .bits n, .bool, rfl, (.gpr (.reg ra), .gpr (.reg rb), ()), (dst, ()) =>
      if n == 32 || n == 64 then
        vllArmCmpCore o (if n == 64 then .w64 else .w32) ra (.reg (.reg rb)) dst
      else fb
    | .bits n, .bool, rfl, (.gpr (.reg ra), .imm cb, ()), (dst, ()) =>
      if (n == 32 || n == 64) && (cb != 0#n || (armZeroCmpIns? o n ra dst).isNone) &&
          ((armImm12? cb).isSome || cb == 0#n || (armImm12? (-cb)).isNone) then
        vllArmCmpCore o (if n == 64 then .w64 else .w32) ra (.imm (cb.setWidth 64)) dst
      else fb
    | _, _, _, _, _ => fb
  | _ => fb

/-- Complete AArch64 `VllNativeHooks` configuration achieving 1:1 directive parity with `armIsa`. -/
@[expose] def vllArmNativeHooks : VllNativeHooks arm64Arch where
  regName r := toString (repr r)
  vregName v := v.elim
  loadExt := .zx
  condOfCmp? := some ∘ armCmpCond
  cmpFlags := [.eq, .ne, .lt, .ge, .le, .gt, .ls, .hi]
  jnzGpr? := some fun r l => let (ds, cl) := armJnzGpr r l; (ds.map .native, cl)
  jnzGprInv? := some fun r inv l => let (ds, cl) := armJnzGprInv r inv l; (ds.map .native, cl)
  boolFlagOut? := armBoolFlagOut
  cmpFlagsOut? := armCmpFlagsOut
  hasTestFlags := true
  opHook := vllArmOpHook
  loadHook _ _ _ := none
  storeHook := vllArmStoreHook
  supportsScalarOpOverride? := some armSupportsScalarOp
  zeroUpper32Load := true
  zeroExtLoad := true
  zeroUpper32Op := armZeroUpper32Op
  elideZext32 := true
  testOp w neg pa pb pd := wrapArmNative (armTestOp w neg pa pb pd)
  loadSext := vllArmLoadSext
  cmpZeroJcc co w r l := wrapArmNative (armCmpZeroJcc co w r l)
  testJcc neg w r mask l := wrapArmNative (armTestJcc neg w r mask l)
  leaArith w base? idx sc disp rd := wrapArmNative (armLeaArith w base? idx sc disp rd)
  zeroUpper32LeaArith := true
  loadZextIdx t rd base idx sc disp := wrapArmNative (armLoadZextIdx t rd base idx sc disp)
  loadSextZextIdx m n rd base idx sc disp :=
    wrapArmNative (armLoadSextZextIdx m n rd base idx sc disp)
  storeZextIdx t pa base idx sc disp := wrapArmNative (armStoreZextIdx t pa base idx sc disp)
  leaArithZext base? idx sh disp rd := wrapArmNative (armLeaArithZext base? idx sh disp rd)
  saveRegs? := some vllArmSaveRegs
  restoreRegs? := some vllArmRestoreRegs
  supportsAddrDisp := armSupportsAddrDisp
  supportsAddrIdx := armSupportsAddrIdx
  supportsTestFuse := true
  supportsAddrZextIdx := armSupportsAddrIdx
  vec := vllEmptyVecIsa arm64Arch Empty.elim
  legalTarget? := some armLegalTarget

/-! ## 2. Verified Policy (`vllArmPolicySpec`), `vllArmTarget`, `vllArmStrictTarget` -/

private theorem armCondReads_ne_zero (c : ArmCond) : arm64Arch.condReads c ≠ 0#8 := by
  cases c <;> decide

private theorem armCmpCond_subs {n : Nat} (hn : n = 32 ∨ n = 64) (o : CmpOp) (x y : BitVec n) :
    (armCmpCond o).interp (StatusFlags.subs (x - y) x y) = o.evalBits x y := by
  simp only [armCmpCond, ArmCond.interp, ArmCond.toKraken, CondCode.interp,
    StatusFlags.subs, StatusFlags.from_result, CmpOp.evalBits, BitVec.ult, BitVec.ule,
    BitVec.slt, BitVec.sle]
  rcases hn with rfl | rfl <;> cases o <;> grind [BitVec.unsigned, BitVec.signed]

private theorem vllPArg_to_arm {s : MachSt arm64Arch} {t : Ty}
    {pa : PArg Arm64.Reg Empty ArmCond t} {v : Val t}
    (h : (vllMach arm64Arch).PArgHolds s t pa v) :
    armMach.PArgHolds (vllToMachData s) t pa v := by
  cases pa with
  | gpr r => simpa [Machine.PArgHolds, armMach, vllMach, get_vllToMachData] using h
  | vec vr => exact vr.elim
  | flag c => exact h
  | imm c => exact h

private theorem vllTRel_PArg_to_arm {s : MachSt arm64Arch} :
    ∀ {sig : List Ty} {pas : Tup (PArg Arm64.Reg Empty ArmCond) sig} {vs : Tup Val sig},
      TRel ((vllMach arm64Arch).PArgHolds s) pas vs →
      TRel (armMach.PArgHolds (vllToMachData s)) pas vs
  | [], (), (), .nil => .nil
  | _ :: _, (_, _), (_, _), .cons h rest => .cons (vllPArg_to_arm h) (vllTRel_PArg_to_arm rest)

private theorem armPDst_to_vll {sm : MachineData} {t : Ty}
    {pd : PDst Arm64.Reg Empty ArmCond t} {v : Val t}
    (h : armMach.PDstHolds sm t pd v) :
    (vllMach arm64Arch).PDstHolds (machDataToVll sm) t pd v := by
  cases pd with
  | gpr r => exact h
  | vec vr => exact vr.elim
  | flag c => exact h

private theorem armTRel_PDst_to_vll {sm : MachineData} :
    ∀ {rs : List Ty} {dsts : Tup (PDst Arm64.Reg Empty ArmCond) rs} {rvs : Tup Val rs},
      TRel (armMach.PDstHolds sm) dsts rvs →
      TRel ((vllMach arm64Arch).PDstHolds (machDataToVll sm)) dsts rvs
  | [], (), (), .nil => .nil
  | _ :: _, (_, _), (_, _), .cons h rest => .cons (armPDst_to_vll h) (armTRel_PDst_to_vll rest)

private theorem wrapArmNative_eq_some {res : Option (List _root_.Directive × FlagMask)}
    {c : List (Instr arm64Arch)} {cl : FlagMask}
    (h : wrapArmNative res = some (c, cl)) :
    ∃ ds, res = some (ds, cl) ∧ c = ds.map (Instr.native (A := arm64Arch)) := by
  cases res with
  | none => cases h
  | some p =>
    rcases p with ⟨ds, cl'⟩
    simp only [wrapArmNative, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨ds, rfl, rfl⟩

private theorem wrap1_arm {h : VllHost arm64Arch} {k : Nat} {c : List (Instr arm64Arch)}
    {clob : FlagMask} {s : MachSt arm64Arch} {post : Config arm64Arch → Prop} {t : Ty}
    {rd : Arm64.Reg} {v : Val t} {P : Tup Val [t] → Prop} (hP : P (v, ()))
    (ft : (vllMach arm64Arch).FallsTo arm64Arch.condReads h k c (rd :: armScratch) [] clob s
      (fun s' => GprHolds (s'.gpr rd) t v ∧ s'.mem = s.mem) post) :
    (vllMach arm64Arch).FallsTo arm64Arch.condReads h k c
      (@tupDstGprs Arm64.Reg Empty ArmCond [t] (.gpr rd, ()) ++ armScratch) [] clob s
      (fun s' => (∃ rvs, P rvs ∧
        TRel ((vllMach arm64Arch).PDstHolds s') (as := [t]) (.gpr rd, ()) rvs) ∧
        s'.mem = s.mem) post :=
  Machine.FallsTo.conseq ft fun _ ⟨hg, hm⟩ _ => ⟨⟨(_, ()), hP, .cons hg .nil⟩, hm⟩

private theorem setWidth_setWidth_self64 {n : Nat} (hn : n ≤ 64) (v : BitVec n) :
    (v.setWidth 64).setWidth n = v := by
  rw [BitVec.setWidth_setWidth_of_le _ hn, BitVec.setWidth_eq]

private theorem vllMach_setcc_exact {h : VllHost arm64Arch} {k : Nat} {rd : Arm64.Reg}
    {c : ArmCond} {s : MachSt arm64Arch} {post : Config arm64Arch → Prop} :
    (vllMach arm64Arch).FallsTo arm64Arch.condReads h k [.setcc rd c] [rd] [] maskNone s
      (fun s' => s'.gpr rd = (BitVec.ofNat 8 (arm64Arch.evalCond s.flags c).toNat).setWidth 64 ∧
        s'.mem = s.mem) post := by
  intro hc cont
  refine vllMach_run_of_bodyWp hc
    (fun _ hi _ => by simp only [List.mem_singleton] at hi; subst hi; intro e; cases e)
    (fun _ hi _ => by simp only [List.mem_singleton] at hi; subst hi; intro e; cases e)
    (K := fun s' => s' = s.setGprW .w8 rd (BitVec.ofNat 8 (arm64Arch.evalCond s.flags c).toNat))
    (instrWp_setcc (A := arm64Arch) (symAddr := h.labelAddr) (rd := rd) (c := c) rfl)
    fun s' hs' => by
      subst hs'
      have hg : (s.setGprW .w8 rd
          (BitVec.ofNat 8 (arm64Arch.evalCond s.flags c).toNat)).gpr rd =
          (BitVec.ofNat 8 (arm64Arch.evalCond s.flags c).toNat).setWidth 64 :=
        MachSt.gpr_setGprW_same s .w8 rd _
      refine cont _ ⟨hg, rfl⟩ ⟨fun r hr => ?_, fun v _ => v.elim, fun _ _ => rfl⟩
      simp only [List.mem_singleton] at hr
      exact MachSt.gpr_setGprW_ne s .w8 _ hr

private theorem vllArmCmpCore_spec {h : VllHost arm64Arch} {k : Nat} {o : CmpOp} {w : Width}
    (hw : w = .w32 ∨ w = .w64) {ra : XReg} {rhs : Src arm64Arch}
    {dst : PDst Arm64.Reg Empty ArmCond .bool} {c : List (Instr arm64Arch)} {clob : FlagMask}
    {va vb : BitVec w.bits} {s : MachSt arm64Arch} {post : Config arm64Arch → Prop}
    (hcmp : vllArmCmpCore o w ra rhs dst = some (c, clob))
    (ha : (s.gpr (.reg ra)).setWidth w.bits = va)
    (hb : rhs.evalW w s.gpr = vb) :
    (vllMach arm64Arch).FallsTo arm64Arch.condReads h k c
      (@tupDstGprs Arm64.Reg Empty ArmCond [.bool] (dst, ()) ++ armScratch) [] clob s
      (fun s' => (∃ rvs : Tup Val [.bool], rvs = (o.evalBits va vb, ()) ∧
        TRel ((vllMach arm64Arch).PDstHolds s') (as := [.bool]) (dst, ()) rvs) ∧
        s'.mem = s.mem) post := by
  have hbits : w.bits = 32 ∨ w.bits = 64 := by rcases hw with rfl | rfl <;> simp
  cases dst with
  | vec v => exact v.elim
  | flag cf =>
    dsimp only [vllArmCmpCore] at hcmp
    cases heq : (cf == armCmpCond o) <;> simp only [heq, Bool.false_eq_true, ↓reduceIte] at hcmp
    · cases hcmp
    · cases hcmp
      have hcf : cf = armCmpCond o := beq_iff_eq.mp heq; subst hcf
      refine Machine.FallsTo.conseq (Machine.FallsTo.weaken
        (vllMach_cmp_spec arm64Arch_wf (w := w) (lhs := .reg ra) (rhs := rhs))
        (fun _ hr => False.elim (List.not_mem_nil hr))
        (fun _ hr => False.elim (List.not_mem_nil hr)) (flagMask_sub_refl _)) ?_
      intro s' ⟨hf, hm⟩ _
      refine ⟨⟨(_, ()), rfl, .cons ?_ .nil⟩, hm⟩
      show (armCmpCond o).interp s'.flags = o.evalBits va vb
      rw [hf]; dsimp only [arm64Arch, arm64CmpFlags]; rw [ha, hb]
      exact armCmpCond_subs hbits o va vb
  | gpr r => cases r with | SP => cases hcmp | reg d =>
    cases hcmp
    have h1 : (vllMach arm64Arch).FallsTo arm64Arch.condReads h k
        ([.cmp w (.reg ra) rhs] ++ [.setcc (.reg d) (armCmpCond o)])
        ([] ++ [.reg d]) ([] ++ []) (maskNZCV ||| maskNone) s
        (fun s' => GprHolds (s'.gpr (.reg d)) .bool (o.evalBits va vb) ∧ s'.mem = s.mem) post :=
      Machine.FallsTo.comp
        (vllMach_cmp_spec arm64Arch_wf (w := w) (lhs := .reg ra) (rhs := rhs))
        fun s1 ⟨hf1, hm1⟩ _ => Machine.FallsTo.conseq
          (vllMach_setcc_spec arm64Arch_wf (rd := .reg d) (c := armCmpCond o))
          fun s2 ⟨hg2, hm2⟩ _ => by
            have hev : (vllMach arm64Arch).evalCond s1 (armCmpCond o) = o.evalBits va vb := by
              show (armCmpCond o).interp s1.flags = o.evalBits va vb
              rw [hf1]; dsimp only [arm64Arch, arm64CmpFlags]; rw [ha, hb]
              exact armCmpCond_subs hbits o va vb
            rw [hev] at hg2; exact ⟨hg2, hm2.trans hm1⟩
    refine wrap1_arm rfl (Machine.FallsTo.weaken h1 ?_
      (fun _ hr => False.elim (List.not_mem_nil hr)) ?_)
    · intro r hr; simp only [List.nil_append, List.mem_singleton] at hr; subst hr
      exact List.mem_cons_self
    · decide

private theorem vllArmOpHook_fallback {h : VllHost arm64Arch} {k : Nat} {sig rs : List Ty}
    {code : OpCode sig rs} {pas : Tup (PArg Arm64.Reg Empty ArmCond) sig}
    {dsts : Tup (PDst Arm64.Reg Empty ArmCond) rs} {vh : VariantHint}
    {c : List (Instr arm64Arch)} {clob : FlagMask} {vs : Tup Val sig} {P : Tup Val rs → Prop}
    {s : MachSt arm64Arch} {post : Config arm64Arch → Prop}
    (hfb : wrapArmNative (armOp code pas dsts vh) = some (c, clob))
    (ha : ∀ r ∈ tupArgGprs pas, r ∉ armScratch) (hd : ∀ r ∈ tupDstGprs dsts, r ∉ armScratch)
    (hrel : TRel ((vllMach arm64Arch).PArgHolds s) pas vs) (hwp : code.wp vs P) :
    (vllMach arm64Arch).FallsTo arm64Arch.condReads h k c (tupDstGprs dsts ++ armScratch) [] clob s
      (fun s' => (∃ rvs, P rvs ∧ TRel ((vllMach arm64Arch).PDstHolds s') dsts rvs) ∧
        s'.mem = s.mem) post := by
  obtain ⟨ds, hds, rfl⟩ := wrapArmNative_eq_some hfb
  obtain ⟨hp, hlen⟩ := armOp_pure_len hds
  refine armFallsTo_to_vllNative hp hlen fun host postH =>
    Machine.FallsTo.conseq
      (arm_gprSpec.op_spec hds ha hd (vllTRel_PArg_to_arm hrel) hwp) ?_
  intro sm' ⟨⟨rvs, hPr, hdst⟩, hm⟩ _
  exact ⟨⟨rvs, hPr, armTRel_PDst_to_vll hdst⟩, hm⟩

private theorem vllArmOpHook_spec {h : VllHost arm64Arch} {k : Nat} {sig rs : List Ty}
    {code : OpCode sig rs} {pas : Tup (PArg Arm64.Reg Empty ArmCond) sig}
    {dsts : Tup (PDst Arm64.Reg Empty ArmCond) rs} {vh : VariantHint}
    {c : List (Instr arm64Arch)} {clob : FlagMask} {vs : Tup Val sig} {P : Tup Val rs → Prop}
    {s : MachSt arm64Arch} {post : Config arm64Arch → Prop}
    (hhk : vllArmOpHook code pas dsts vh = some (c, clob))
    (ha : ∀ r ∈ tupArgGprs pas, r ∉ armScratch) (hd : ∀ r ∈ tupDstGprs dsts, r ∉ armScratch)
    (hrel : TRel ((vllMach arm64Arch).PArgHolds s) pas vs) (hwp : code.wp vs P) :
    (vllMach arm64Arch).FallsTo arm64Arch.condReads h k c (tupDstGprs dsts ++ armScratch) [] clob s
      (fun s' => (∃ rvs, P rvs ∧ TRel ((vllMach arm64Arch).PDstHolds s') dsts rvs) ∧
        s'.mem = s.mem) post := by
  have mov32_bits : ∀ {n : Nat} (hn : n = 8 ∨ n = 16 ∨ n = 32) {r d : XReg} {v : BitVec n},
      (s.gpr (.reg r)).setWidth n = v →
      (vllMach arm64Arch).FallsTo arm64Arch.condReads h k
        [.mov .w32 (.reg d) (.reg r)] (.reg d :: armScratch) [] maskNone s
        (fun s' => GprHolds (s'.gpr (.reg d)) (.bits n) v ∧ s'.mem = s.mem) post := by
    intro n hn r d v hv
    refine Machine.FallsTo.conseq (fallsTo_weaken_rd
      (vllMach_movW_spec arm64Arch_wf (w := .w32) (rd := .reg d) (rs := .reg r))) ?_
    intro s' ⟨hg, _, hm⟩ _
    have hle32 : n ≤ 32 := by rcases hn with rfl | rfl | rfl <;> decide
    have hle64 : n ≤ 64 := by omega
    refine ⟨⟨hle64, ?_⟩, hm⟩
    rw [hg]; dsimp only [arm64Arch, writeSubZeroExtend]
    rw [BitVec.setWidth_setWidth_of_le _ hle64, BitVec.setWidth_setWidth_of_le _ hle32, hv]
  cases code with
  | copy t =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    rcases vs with ⟨va, ⟨⟩⟩; rcases hrel with _ | ⟨hpa, hnil⟩; cases hnil
    cases t with
    | bool =>
      cases pd with
      | vec v => exact v.elim
      | flag _ =>
        dsimp only [vllArmOpHook] at hhk
        exact vllArmOpHook_fallback hhk ha hd (.cons hpa .nil) hwp
      | gpr rd => cases rd with
        | SP =>
          dsimp only [vllArmOpHook] at hhk
          exact vllArmOpHook_fallback hhk ha hd (.cons hpa .nil) hwp
        | reg d => cases pa with
          | vec v => exact v.elim
          | imm _ | flag _ => cases hhk
          | gpr r => cases r with
            | SP =>
              dsimp only [vllArmOpHook] at hhk
              exact vllArmOpHook_fallback hhk ha hd (.cons hpa .nil) hwp
            | reg rx =>
              cases hhk
              refine wrap1_arm hwp (Machine.FallsTo.conseq (fallsTo_weaken_rd
                (vllMach_movW_spec arm64Arch_wf (w := .w32) (rd := .reg d) (rs := .reg rx))) ?_)
              intro s' ⟨hg, _, hm⟩ _
              have h8 : (s.gpr (.reg rx)).setWidth 8 = BitVec.ofNat 8 va.toNat := hpa
              refine ⟨?_, hm⟩
              show (s'.gpr (.reg d)).setWidth 8 = BitVec.ofNat 8 va.toNat
              rw [hg]; dsimp only [arm64Arch, writeSubZeroExtend]
              rw [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
                BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32), h8]
    | bits n =>
      cases pd with
      | vec v => exact v.elim
      | gpr rd => cases rd with
        | SP =>
          dsimp only [vllArmOpHook] at hhk
          exact vllArmOpHook_fallback hhk ha hd (.cons hpa .nil) hwp
        | reg d => cases pa with
          | vec v => exact v.elim
          | imm _ =>
            dsimp only [vllArmOpHook] at hhk
            cases hc : [8, 16, 32, 64].contains n <;>
              simp only [hc, Bool.false_eq_true, ↓reduceIte] at hhk
            · exact vllArmOpHook_fallback hhk ha hd (.cons hpa .nil) hwp
            · cases hhk
          | gpr r => cases r with
            | SP =>
              dsimp only [vllArmOpHook] at hhk
              exact vllArmOpHook_fallback hhk ha hd (.cons hpa .nil) hwp
            | reg rx =>
              dsimp only [vllArmOpHook] at hhk
              cases hw : (n == 8 || n == 16 || n == 32) <;>
                simp only [hw, Bool.false_eq_true, ↓reduceIte] at hhk
              · exact vllArmOpHook_fallback hhk ha hd (.cons hpa .nil) hwp
              · cases hhk
                have hn : n = 8 ∨ n = 16 ∨ n = 32 := by
                  simp only [Bool.or_eq_true, beq_iff_eq] at hw; omega
                exact wrap1_arm hwp (mov32_bits hn hpa.2)
    | float _ | pair _ _ =>
      dsimp only [vllArmOpHook] at hhk
      exact vllArmOpHook_fallback hhk ha hd (.cons hpa .nil) hwp
  | bitcast t u hsz =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    rcases vs with ⟨va, ⟨⟩⟩; rcases hrel with _ | ⟨hpa, hnil⟩; cases hnil
    cases t with
    | bool | float _ | pair _ _ =>
      dsimp only [vllArmOpHook] at hhk
      exact vllArmOpHook_fallback hhk ha hd (.cons hpa .nil) hwp
    | bits m => cases u with
      | bool | float _ | pair _ _ =>
        dsimp only [vllArmOpHook] at hhk
        exact vllArmOpHook_fallback hhk ha hd (.cons hpa .nil) hwp
      | bits n =>
        have hmn : m = n := hsz; subst hmn
        cases pd with
        | vec v => exact v.elim
        | gpr rd => cases rd with
          | SP =>
            dsimp only [vllArmOpHook] at hhk
            exact vllArmOpHook_fallback hhk ha hd (.cons hpa .nil) hwp
          | reg d => cases pa with
            | vec v => exact v.elim
            | imm _ =>
              dsimp only [vllArmOpHook] at hhk
              cases hc : ([8, 16, 32, 64].contains m && [8, 16, 32, 64].contains m) <;>
                simp only [hc, Bool.false_eq_true, ↓reduceIte] at hhk
              · exact vllArmOpHook_fallback hhk ha hd (.cons hpa .nil) hwp
              · cases hhk
            | gpr r => cases r with
              | SP =>
                dsimp only [vllArmOpHook] at hhk
                exact vllArmOpHook_fallback hhk ha hd (.cons hpa .nil) hwp
              | reg rx =>
                dsimp only [vllArmOpHook] at hhk
                cases hw : ([8, 16, 32, 64].contains m && [8, 16, 32, 64].contains m &&
                    (m == 8 || m == 16 || m == 32)) <;>
                  simp only [hw, Bool.false_eq_true, ↓reduceIte] at hhk
                · exact vllArmOpHook_fallback hhk ha hd (.cons hpa .nil) hwp
                · cases hhk
                  have hm : m = 8 ∨ m = 16 ∨ m = 32 := by
                    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hw; omega
                  have hP : P (va, ()) := by
                    simpa [OpCode.wp, ofBits, toBits] using hwp
                  exact wrap1_arm hP (mov32_bits hm hpa.2)
  | zext m n =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    rcases vs with ⟨va, ⟨⟩⟩; rcases hrel with _ | ⟨hpa, hnil⟩; cases hnil
    cases pd with
    | vec v => exact v.elim
    | gpr rd => cases rd with
      | SP =>
        dsimp only [vllArmOpHook] at hhk
        exact vllArmOpHook_fallback hhk ha hd (.cons hpa .nil) hwp
      | reg d => cases pa with
        | vec v => exact v.elim
        | imm _ =>
          dsimp only [vllArmOpHook] at hhk
          cases hc : ([8, 16, 32, 64].contains m && [8, 16, 32, 64].contains n && Nat.ble m n) <;>
            simp only [hc, Bool.false_eq_true, ↓reduceIte] at hhk
          · exact vllArmOpHook_fallback hhk ha hd (.cons hpa .nil) hwp
          · cases hhk
        | gpr r => cases r with
          | SP =>
            dsimp only [vllArmOpHook] at hhk
            exact vllArmOpHook_fallback hhk ha hd (.cons hpa .nil) hwp
          | reg rx =>
            dsimp only [vllArmOpHook] at hhk
            cases hc : ([8, 16, 32, 64].contains m && [8, 16, 32, 64].contains n && Nat.ble m n) <;>
              simp only [hc, Bool.false_eq_true, ↓reduceIte] at hhk
            · exact vllArmOpHook_fallback hhk ha hd (.cons hpa .nil) hwp
            · have hn64 : n ≤ 64 := by
                simp only [Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq,
                  List.mem_cons, List.not_mem_nil, or_false] at hc
                rcases hc.1.2 with rfl | rfl | rfl | rfl <;> decide
              have hrx : (s.gpr (.reg rx)).setWidth m = va := hpa.2
              have hP : P (va.setWidth n, ()) := hwp.2
              cases h8 : (m == 8) <;> simp only [h8, Bool.false_eq_true, ↓reduceIte] at hhk
              · cases h16 : (m == 16) <;> simp only [h16, Bool.false_eq_true, ↓reduceIte] at hhk
                · cases h32 : (m == 32) <;> simp only [h32, Bool.false_eq_true, ↓reduceIte] at hhk
                  · exact vllArmOpHook_fallback hhk ha hd (.cons hpa .nil) hwp
                  · have hm : m = 32 := beq_iff_eq.mp h32; subst hm; cases hhk
                    refine wrap1_arm hP (Machine.FallsTo.conseq (fallsTo_weaken_rd
                      (vllMach_movW_spec arm64Arch_wf (w := .w32) (rd := .reg d) (rs := .reg rx)))
                      fun s' ⟨hg, _, hm'⟩ _ => ⟨⟨hn64, ?_⟩, hm'⟩)
                    rw [hg]; dsimp only [arm64Arch, writeSubZeroExtend, Width.bits]
                    rw [hrx, BitVec.setWidth_setWidth_of_le _ hn64]
                · have hm : m = 16 := beq_iff_eq.mp h16; subst hm; cases hhk
                  refine wrap1_arm hP (Machine.FallsTo.conseq (fallsTo_weaken_rd
                    (vllMach_movW_spec arm64Arch_wf (w := .w16) (rd := .reg d) (rs := .reg rx)))
                    fun s' ⟨hg, _, hm'⟩ _ => ⟨⟨hn64, ?_⟩, hm'⟩)
                  rw [hg]; dsimp only [arm64Arch, writeSubZeroExtend, Width.bits]
                  rw [hrx, BitVec.setWidth_setWidth_of_le _ hn64]
              · have hm : m = 8 := beq_iff_eq.mp h8; subst hm; cases hhk
                refine wrap1_arm hP (Machine.FallsTo.conseq (fallsTo_weaken_rd
                  (vllMach_movW_spec arm64Arch_wf (w := .w8) (rd := .reg d) (rs := .reg rx)))
                  fun s' ⟨hg, _, hm'⟩ _ => ⟨⟨hn64, ?_⟩, hm'⟩)
                rw [hg]; dsimp only [arm64Arch, writeSubZeroExtend, Width.bits]
                rw [hrx, BitVec.setWidth_setWidth_of_le _ hn64]
  | trunc m n =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    rcases vs with ⟨va, ⟨⟩⟩; rcases hrel with _ | ⟨hpa, hnil⟩; cases hnil
    cases pd with
    | vec v => exact v.elim
    | gpr rd => cases rd with
      | SP =>
        dsimp only [vllArmOpHook] at hhk
        exact vllArmOpHook_fallback hhk ha hd (.cons hpa .nil) hwp
      | reg d => cases pa with
        | vec v => exact v.elim
        | imm _ =>
          dsimp only [vllArmOpHook] at hhk
          cases hc : ([8, 16, 32, 64].contains m && [8, 16, 32, 64].contains n && Nat.ble n m) <;>
            simp only [hc, Bool.false_eq_true, ↓reduceIte] at hhk
          · exact vllArmOpHook_fallback hhk ha hd (.cons hpa .nil) hwp
          · cases hhk
        | gpr r => cases r with
          | SP =>
            dsimp only [vllArmOpHook] at hhk
            exact vllArmOpHook_fallback hhk ha hd (.cons hpa .nil) hwp
          | reg rx =>
            dsimp only [vllArmOpHook] at hhk
            cases hc : ([8, 16, 32, 64].contains m && [8, 16, 32, 64].contains n &&
                Nat.ble n m && (n == 8 || n == 16 || n == 32)) <;>
              simp only [hc, Bool.false_eq_true, ↓reduceIte] at hhk
            · exact vllArmOpHook_fallback hhk ha hd (.cons hpa .nil) hwp
            · cases hhk
              have hnm : n ≤ m := by
                simp only [Bool.and_eq_true, Nat.ble_eq] at hc; exact hc.1.2
              have hn : n = 8 ∨ n = 16 ∨ n = 32 := by
                simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc; omega
              have hrx : (s.gpr (.reg rx)).setWidth m = va := hpa.2
              have htr : (s.gpr (.reg rx)).setWidth n = va.setWidth n := by
                rw [← hrx, BitVec.setWidth_setWidth_of_le _ hnm]
              have hP : P (va.setWidth n, ()) := hwp.2
              exact wrap1_arm hP (mov32_bits hn htr)
  | ofBool n =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    rcases vs with ⟨va, ⟨⟩⟩; rcases hrel with _ | ⟨hpa, hnil⟩; cases hnil
    cases pd with
    | vec v => exact v.elim
    | gpr rd => cases rd with
      | SP =>
        dsimp only [vllArmOpHook] at hhk
        exact vllArmOpHook_fallback hhk ha hd (.cons hpa .nil) hwp
      | reg d => cases pa with
        | vec v => exact v.elim
        | imm _ =>
          dsimp only [vllArmOpHook] at hhk
          cases hc : [8, 16, 32, 64].contains n <;>
            simp only [hc, Bool.false_eq_true, ↓reduceIte] at hhk
          · exact vllArmOpHook_fallback hhk ha hd (.cons hpa .nil) hwp
          · cases hhk
        | flag cf =>
          dsimp only [vllArmOpHook] at hhk
          cases hc : [8, 16, 32, 64].contains n <;>
            simp only [hc, Bool.false_eq_true, ↓reduceIte] at hhk
          · exact vllArmOpHook_fallback hhk ha hd (.cons hpa .nil) hwp
          · cases hhk
            have hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64 := by
              simp only [List.contains_eq_mem, decide_eq_true_eq, List.mem_cons,
                List.not_mem_nil, or_false] at hc; exact hc
            have hEq : arm64Arch.evalCond s.flags cf = va := hpa
            have hP : P (BitVec.ofNat n va.toNat, ()) := hwp
            refine wrap1_arm hP (Machine.FallsTo.conseq (fallsTo_weaken_rd
              (vllMach_setcc_exact (rd := .reg d) (c := cf))) ?_)
            intro s' ⟨hg, hm⟩ _
            have hg' : s'.gpr (.reg d) = (BitVec.ofNat 8 va.toNat).setWidth 64 := by
              rw [hg, hEq]
            rcases hn with rfl | rfl | rfl | rfl <;>
              exact ⟨⟨by decide, by rw [hg']; cases va <;> rfl⟩, hm⟩
        | gpr r => cases r with
          | SP =>
            dsimp only [vllArmOpHook] at hhk
            exact vllArmOpHook_fallback hhk ha hd (.cons hpa .nil) hwp
          | reg rx =>
            dsimp only [vllArmOpHook] at hhk
            cases hc : [8, 16, 32, 64].contains n <;>
              simp only [hc, Bool.false_eq_true, ↓reduceIte] at hhk
            · exact vllArmOpHook_fallback hhk ha hd (.cons hpa .nil) hwp
            · cases hhk
              have hn : n = 8 ∨ n = 16 ∨ n = 32 ∨ n = 64 := by
                simp only [List.contains_eq_mem, decide_eq_true_eq, List.mem_cons,
                  List.not_mem_nil, or_false] at hc; exact hc
              have hP : P (BitVec.ofNat n va.toNat, ()) := hwp
              refine wrap1_arm hP (Machine.FallsTo.conseq (fallsTo_weaken_rd
                (vllMach_movW_spec arm64Arch_wf (w := .w8) (rd := .reg d) (rs := .reg rx))) ?_)
              intro s' ⟨hg, _, hm⟩ _
              have h8 : (s.gpr (.reg rx)).setWidth 8 = BitVec.ofNat 8 va.toNat := hpa
              have hg' : s'.gpr (.reg d) = (BitVec.ofNat 8 va.toNat).setWidth 64 := by
                rw [hg]; dsimp only [arm64Arch, writeSubZeroExtend]; rw [h8]
              rcases hn with rfl | rfl | rfl | rfl <;>
                exact ⟨⟨by decide, by rw [hg']; cases va <;> rfl⟩, hm⟩
  | not t =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    rcases vs with ⟨va, ⟨⟩⟩; rcases hrel with _ | ⟨hpa, hnil⟩; cases hnil
    cases t with
    | bool =>
      cases pd with
      | vec v => exact v.elim
      | flag _ =>
        dsimp only [vllArmOpHook] at hhk
        exact vllArmOpHook_fallback hhk ha hd (.cons hpa .nil) hwp
      | gpr rd => cases rd with
        | SP =>
          dsimp only [vllArmOpHook] at hhk
          exact vllArmOpHook_fallback hhk ha hd (.cons hpa .nil) hwp
        | reg d => cases pa with
          | vec v => exact v.elim
          | imm b =>
            cases hhk; have hb : b = va := hpa; subst hb
            have hP : P (!b, ()) := hwp
            refine wrap1_arm hP (Machine.FallsTo.conseq (fallsTo_weaken_rd
              (vllMach_movi_spec (A := arm64Arch) (rd := .reg d)
                (imm := BitVec.ofNat 64 (!b).toNat))) ?_)
            intro s' ⟨hg, hm⟩ _
            have hg' : s'.gpr (.reg d) = BitVec.ofNat 64 (!b).toNat := hg
            exact ⟨by show (s'.gpr (.reg d)).setWidth 8 = _; rw [hg']; cases b <;> rfl, hm⟩
          | flag cf =>
            cases hhk
            have hP : P (!va, ()) := hwp
            refine wrap1_arm hP (Machine.FallsTo.conseq (fallsTo_weaken_rd
              (vllMach_setcc_spec arm64Arch_wf (rd := .reg d) (c := armNegCond cf))) ?_)
            intro s' ⟨hg, hm⟩ _
            have hev : (vllMach arm64Arch).evalCond s (armNegCond cf) = !va := by
              rw [show (vllMach arm64Arch).evalCond s (armNegCond cf) =
                !(vllMach arm64Arch).evalCond s cf from armNegCond_interp cf s.flags, hpa]
            rw [hev] at hg; exact ⟨hg, hm⟩
          | gpr r => cases r with
            | SP =>
              dsimp only [vllArmOpHook] at hhk
              exact vllArmOpHook_fallback hhk ha hd (.cons hpa .nil) hwp
            | reg rx =>
              cases hhk
              have hP : P (!va, ()) := hwp
              refine wrap1_arm hP (Machine.FallsTo.conseq (fallsTo_weaken_rd
                (vllMach_alu_spec arm64Arch_wf (op := .xor) (w := .w32) (rd := .reg d)
                  (lhs := .reg rx) (rhs := .imm 1#64) (sf := false))) ?_)
              intro s' ⟨hg, _, _, hm⟩ _
              have h8 : (s.gpr (.reg rx)).setWidth 8 = BitVec.ofNat 8 va.toNat := hpa
              refine ⟨?_, hm⟩
              show (s'.gpr (.reg d)).setWidth 8 = BitVec.ofNat 8 (!va).toNat
              rw [hg]; dsimp only [arm64Arch, writeSubZeroExtend, CoreAlu.eval, Src.evalW, Src.eval]
              rw [BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
                BitVec.setWidth_xor, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32), h8]
              cases va <;> rfl
    | bits n =>
      cases pd with
      | vec v => exact v.elim
      | gpr rd => cases rd with
        | SP =>
          dsimp only [vllArmOpHook] at hhk
          exact vllArmOpHook_fallback hhk ha hd (.cons hpa .nil) hwp
        | reg d => cases pa with
          | vec v => exact v.elim
          | gpr _ =>
            dsimp only [vllArmOpHook] at hhk
            exact vllArmOpHook_fallback hhk ha hd (.cons hpa .nil) hwp
          | imm cv =>
            dsimp only [vllArmOpHook] at hhk
            cases hc : [8, 16, 32, 64].contains n <;>
              simp only [hc, Bool.false_eq_true, ↓reduceIte] at hhk
            · exact vllArmOpHook_fallback hhk ha hd (.cons hpa .nil) hwp
            · cases hhk; have hEq : cv = va := hpa; subst hEq
              have hn64 : n ≤ 64 := by
                simp only [List.contains_eq_mem, decide_eq_true_eq, List.mem_cons,
                  List.not_mem_nil, or_false] at hc
                rcases hc with rfl | rfl | rfl | rfl <;> decide
              have hP : P (~~~cv, ()) := hwp
              refine wrap1_arm hP (Machine.FallsTo.conseq (fallsTo_weaken_rd
                (vllMach_movi_spec (A := arm64Arch) (rd := .reg d)
                  (imm := (~~~cv).setWidth 64))) ?_)
              intro s' ⟨hg, hm⟩ _
              have hg' : s'.gpr (.reg d) = (~~~cv).setWidth 64 := hg
              exact ⟨⟨hn64, by rw [hg']; exact setWidth_setWidth_self64 hn64 _⟩, hm⟩
    | float _ | pair _ _ =>
      dsimp only [vllArmOpHook] at hhk
      exact vllArmOpHook_fallback hhk ha hd (.cons hpa .nil) hwp
  | neg t =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    rcases vs with ⟨va, ⟨⟩⟩; rcases hrel with _ | ⟨hpa, hnil⟩; cases hnil
    cases t with
    | bool | float _ | pair _ _ =>
      dsimp only [vllArmOpHook] at hhk
      exact vllArmOpHook_fallback hhk ha hd (.cons hpa .nil) hwp
    | bits n =>
      cases pd with
      | vec v => exact v.elim
      | gpr rd => cases rd with
        | SP =>
          dsimp only [vllArmOpHook] at hhk
          exact vllArmOpHook_fallback hhk ha hd (.cons hpa .nil) hwp
        | reg d => cases pa with
          | vec v => exact v.elim
          | gpr _ =>
            dsimp only [vllArmOpHook] at hhk
            exact vllArmOpHook_fallback hhk ha hd (.cons hpa .nil) hwp
          | imm cv =>
            dsimp only [vllArmOpHook] at hhk
            cases hc : [8, 16, 32, 64].contains n <;>
              simp only [hc, Bool.false_eq_true, ↓reduceIte] at hhk
            · exact vllArmOpHook_fallback hhk ha hd (.cons hpa .nil) hwp
            · cases hhk; have hEq : cv = va := hpa; subst hEq
              have hn64 : n ≤ 64 := by
                simp only [List.contains_eq_mem, decide_eq_true_eq, List.mem_cons,
                  List.not_mem_nil, or_false] at hc
                rcases hc with rfl | rfl | rfl | rfl <;> decide
              have hP : P (-cv, ()) := hwp
              refine wrap1_arm hP (Machine.FallsTo.conseq (fallsTo_weaken_rd
                (vllMach_movi_spec (A := arm64Arch) (rd := .reg d)
                  (imm := (-cv).setWidth 64))) ?_)
              intro s' ⟨hg, hm⟩ _
              have hg' : s'.gpr (.reg d) = (-cv).setWidth 64 := hg
              exact ⟨⟨hn64, by rw [hg']; exact setWidth_setWidth_self64 hn64 _⟩, hm⟩
  | add t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    rcases vs with ⟨va, vb, ⟨⟩⟩
    rcases hrel with _ | ⟨hpa, hrel2⟩; rcases hrel2 with _ | ⟨hpb, hnil⟩; cases hnil
    cases t with
    | bool | float _ | pair _ _ =>
      dsimp only [vllArmOpHook] at hhk
      exact vllArmOpHook_fallback hhk ha hd (.cons hpa (.cons hpb .nil)) hwp
    | bits n => cases pd with
      | vec v => exact v.elim
      | gpr rd => cases rd with
        | SP =>
          dsimp only [vllArmOpHook] at hhk
          exact vllArmOpHook_fallback hhk ha hd (.cons hpa (.cons hpb .nil)) hwp
        | reg d => cases pa with
          | vec v => exact v.elim
          | imm _ =>
            dsimp only [vllArmOpHook] at hhk
            exact vllArmOpHook_fallback hhk ha hd (.cons hpa (.cons hpb .nil)) hwp
          | gpr r1 => cases r1 with
            | SP =>
              dsimp only [vllArmOpHook] at hhk
              exact vllArmOpHook_fallback hhk ha hd (.cons hpa (.cons hpb .nil)) hwp
            | reg ra => cases pb with
              | vec v => exact v.elim
              | gpr r2 => cases r2 with
                | SP =>
                  dsimp only [vllArmOpHook] at hhk
                  exact vllArmOpHook_fallback hhk ha hd (.cons hpa (.cons hpb .nil)) hwp
                | reg _ =>
                  dsimp only [vllArmOpHook] at hhk
                  cases hw : (n == 32 || n == 64) <;>
                    simp only [hw, Bool.false_eq_true, ↓reduceIte] at hhk
                  · exact vllArmOpHook_fallback hhk ha hd (.cons hpa (.cons hpb .nil)) hwp
                  · cases hhk
              | imm cb =>
                dsimp only [vllArmOpHook] at hhk
                cases hw : (n == 32 || n == 64) <;>
                  simp only [hw, Bool.false_eq_true, ↓reduceIte] at hhk
                · exact vllArmOpHook_fallback hhk ha hd (.cons hpa (.cons hpb .nil)) hwp
                · cases hi : ((armImm12? cb).isSome || (armImm12? (-cb)).isNone) <;>
                    simp only [hi, Bool.false_eq_true, ↓reduceIte] at hhk
                  · cases hhk; have hEq : cb = vb := hpb; subst hEq
                    have hn : n = 32 ∨ n = 64 := by
                      simp only [Bool.or_eq_true, beq_iff_eq] at hw; exact hw
                    have hP : P (va + cb, ()) := hwp
                    rcases hn with rfl | rfl
                    · have hra : (s.gpr (.reg ra)).setWidth 32 = va := hpa.2
                      refine wrap1_arm hP (Machine.FallsTo.conseq (fallsTo_weaken_rd
                        (vllMach_alu_spec arm64Arch_wf (op := .sub) (w := .w32) (rd := .reg d)
                          (lhs := .reg ra) (rhs := .imm ((-cb).setWidth 64)) (sf := false))) ?_)
                      intro s' ⟨_, hg, _, hm⟩ _
                      dsimp only [CoreAlu.eval, Src.evalW, Src.eval, Width.bits, Width.toTy] at hg
                      rw [hra, setWidth_setWidth_self64 (by decide), BitVec.sub_neg] at hg
                      exact ⟨hg, hm⟩
                    · have hra : (s.gpr (.reg ra)).setWidth 64 = va := hpa.2
                      refine wrap1_arm hP (Machine.FallsTo.conseq (fallsTo_weaken_rd
                        (vllMach_alu_spec arm64Arch_wf (op := .sub) (w := .w64) (rd := .reg d)
                          (lhs := .reg ra) (rhs := .imm ((-cb).setWidth 64)) (sf := false))) ?_)
                      intro s' ⟨_, hg, _, hm⟩ _
                      dsimp only [CoreAlu.eval, Src.evalW, Src.eval, Width.bits, Width.toTy] at hg
                      rw [hra, setWidth_setWidth_self64 (by decide), BitVec.sub_neg] at hg
                      exact ⟨hg, hm⟩
                  · cases hhk
  | sub t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    rcases vs with ⟨va, vb, ⟨⟩⟩
    rcases hrel with _ | ⟨hpa, hrel2⟩; rcases hrel2 with _ | ⟨hpb, hnil⟩; cases hnil
    cases t with
    | bool | float _ | pair _ _ =>
      dsimp only [vllArmOpHook] at hhk
      exact vllArmOpHook_fallback hhk ha hd (.cons hpa (.cons hpb .nil)) hwp
    | bits n => cases pd with
      | vec v => exact v.elim
      | gpr rd => cases rd with
        | SP =>
          dsimp only [vllArmOpHook] at hhk
          exact vllArmOpHook_fallback hhk ha hd (.cons hpa (.cons hpb .nil)) hwp
        | reg d => cases pa with
          | vec v => exact v.elim
          | imm _ =>
            dsimp only [vllArmOpHook] at hhk
            exact vllArmOpHook_fallback hhk ha hd (.cons hpa (.cons hpb .nil)) hwp
          | gpr r1 => cases r1 with
            | SP =>
              dsimp only [vllArmOpHook] at hhk
              exact vllArmOpHook_fallback hhk ha hd (.cons hpa (.cons hpb .nil)) hwp
            | reg ra => cases pb with
              | vec v => exact v.elim
              | gpr r2 => cases r2 with
                | SP =>
                  dsimp only [vllArmOpHook] at hhk
                  exact vllArmOpHook_fallback hhk ha hd (.cons hpa (.cons hpb .nil)) hwp
                | reg _ =>
                  dsimp only [vllArmOpHook] at hhk
                  cases hw : (n == 32 || n == 64) <;>
                    simp only [hw, Bool.false_eq_true, ↓reduceIte] at hhk
                  · exact vllArmOpHook_fallback hhk ha hd (.cons hpa (.cons hpb .nil)) hwp
                  · cases hhk
              | imm cb =>
                dsimp only [vllArmOpHook] at hhk
                cases hw : (n == 32 || n == 64) <;>
                  simp only [hw, Bool.false_eq_true, ↓reduceIte] at hhk
                · exact vllArmOpHook_fallback hhk ha hd (.cons hpa (.cons hpb .nil)) hwp
                · cases hi : ((armImm12? cb).isSome || (armImm12? (-cb)).isNone) <;>
                    simp only [hi, Bool.false_eq_true, ↓reduceIte] at hhk
                  · cases hhk; have hEq : cb = vb := hpb; subst hEq
                    have hn : n = 32 ∨ n = 64 := by
                      simp only [Bool.or_eq_true, beq_iff_eq] at hw; exact hw
                    have hP : P (va - cb, ()) := hwp
                    rcases hn with rfl | rfl
                    · have hra : (s.gpr (.reg ra)).setWidth 32 = va := hpa.2
                      refine wrap1_arm hP (Machine.FallsTo.conseq (fallsTo_weaken_rd
                        (vllMach_alu_spec arm64Arch_wf (op := .add) (w := .w32) (rd := .reg d)
                          (lhs := .reg ra) (rhs := .imm ((-cb).setWidth 64)) (sf := false))) ?_)
                      intro s' ⟨_, hg, _, hm⟩ _
                      dsimp only [CoreAlu.eval, Src.evalW, Src.eval, Width.bits, Width.toTy] at hg
                      rw [hra, setWidth_setWidth_self64 (by decide), ← BitVec.sub_eq_add_neg] at hg
                      exact ⟨hg, hm⟩
                    · have hra : (s.gpr (.reg ra)).setWidth 64 = va := hpa.2
                      refine wrap1_arm hP (Machine.FallsTo.conseq (fallsTo_weaken_rd
                        (vllMach_alu_spec arm64Arch_wf (op := .add) (w := .w64) (rd := .reg d)
                          (lhs := .reg ra) (rhs := .imm ((-cb).setWidth 64)) (sf := false))) ?_)
                      intro s' ⟨_, hg, _, hm⟩ _
                      dsimp only [CoreAlu.eval, Src.evalW, Src.eval, Width.bits, Width.toTy] at hg
                      rw [hra, setWidth_setWidth_self64 (by decide), ← BitVec.sub_eq_add_neg] at hg
                      exact ⟨hg, hm⟩
                  · cases hhk
  | mul _ | and _ | or _ | xor _ | shl _ | lshr _ | ashr _ =>
    dsimp only [vllArmOpHook] at hhk
    split at hhk <;> first
      | exact vllArmOpHook_fallback hhk ha hd hrel hwp
      | (split at hhk <;> first | cases hhk | exact vllArmOpHook_fallback hhk ha hd hrel hwp)
  | cmp o t m hm =>
    subst hm; rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨dst, ⟨⟩⟩
    rcases vs with ⟨va, vb, ⟨⟩⟩
    rcases hrel with _ | ⟨hpa, hrel2⟩; rcases hrel2 with _ | ⟨hpb, hnil⟩; cases hnil
    cases t with
    | bool | float _ | pair _ _ =>
      dsimp only [vllArmOpHook] at hhk
      exact vllArmOpHook_fallback hhk ha hd (.cons hpa (.cons hpb .nil)) hwp
    | bits n => cases pa with
      | vec v => exact v.elim
      | imm _ =>
        dsimp only [vllArmOpHook] at hhk
        exact vllArmOpHook_fallback hhk ha hd (.cons hpa (.cons hpb .nil)) hwp
      | gpr r1 => cases r1 with
        | SP =>
          dsimp only [vllArmOpHook] at hhk
          exact vllArmOpHook_fallback hhk ha hd (.cons hpa (.cons hpb .nil)) hwp
        | reg ra => cases pb with
          | vec v => exact v.elim
          | gpr r2 => cases r2 with
            | SP =>
              dsimp only [vllArmOpHook] at hhk
              exact vllArmOpHook_fallback hhk ha hd (.cons hpa (.cons hpb .nil)) hwp
            | reg rb =>
              dsimp only [vllArmOpHook] at hhk
              cases hw : (n == 32 || n == 64) <;>
                simp only [hw, Bool.false_eq_true, ↓reduceIte] at hhk
              · exact vllArmOpHook_fallback hhk ha hd (.cons hpa (.cons hpb .nil)) hwp
              · have hn : n = 32 ∨ n = 64 := by
                  simp only [Bool.or_eq_true, beq_iff_eq] at hw; exact hw
                rcases hn with rfl | rfl
                · refine Machine.FallsTo.conseq
                    (vllArmCmpCore_spec (w := .w32) (Or.inl rfl) hhk hpa.2 hpb.2) ?_
                  rintro s' ⟨⟨rvs, rfl, hdt⟩, hm'⟩ _; exact ⟨⟨_, hwp, hdt⟩, hm'⟩
                · refine Machine.FallsTo.conseq
                    (vllArmCmpCore_spec (w := .w64) (Or.inr rfl) hhk hpa.2 hpb.2) ?_
                  rintro s' ⟨⟨rvs, rfl, hdt⟩, hm'⟩ _; exact ⟨⟨_, hwp, hdt⟩, hm'⟩
          | imm cb =>
            dsimp only [vllArmOpHook] at hhk
            cases hcond : ((n == 32 || n == 64) &&
                (cb != 0#n || (armZeroCmpIns? o n ra dst).isNone) &&
                ((armImm12? cb).isSome || cb == 0#n || (armImm12? (-cb)).isNone)) <;>
              simp only [hcond, Bool.false_eq_true, ↓reduceIte] at hhk
            · exact vllArmOpHook_fallback hhk ha hd (.cons hpa (.cons hpb .nil)) hwp
            · have hn : n = 32 ∨ n = 64 := by
                simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hcond; exact hcond.1.1
              have hEq : cb = vb := hpb; subst hEq
              rcases hn with rfl | rfl
              · refine Machine.FallsTo.conseq
                  (vllArmCmpCore_spec (w := .w32) (Or.inl rfl) hhk hpa.2
                    (setWidth_setWidth_self64 (by decide) cb)) ?_
                rintro s' ⟨⟨rvs, rfl, hdt⟩, hm'⟩ _; exact ⟨⟨_, hwp, hdt⟩, hm'⟩
              · refine Machine.FallsTo.conseq
                  (vllArmCmpCore_spec (w := .w64) (Or.inr rfl) hhk hpa.2
                    (setWidth_setWidth_self64 (by decide) cb)) ?_
                rintro s' ⟨⟨rvs, rfl, hdt⟩, hm'⟩ _; exact ⟨⟨_, hwp, hdt⟩, hm'⟩
  | _ => dsimp only [vllArmOpHook] at hhk; exact vllArmOpHook_fallback hhk ha hd hrel hwp

private theorem vllArmOp_zero32_aux {h : VllHost arm64Arch} {k : Nat} {sig : List Ty}
    {code : OpCode sig [.bits 32]} {pas : Tup (PArg Arm64.Reg Empty ArmCond) sig}
    {dsts : Tup (PDst Arm64.Reg Empty ArmCond) [.bits 32]} {rd : Arm64.Reg} {vh : VariantHint}
    {c : List (Instr arm64Arch)} {clob : FlagMask} {vs : Tup Val sig}
    {P : Tup Val [.bits 32] → Prop} {s : MachSt arm64Arch} {post : Config arm64Arch → Prop}
    (hz : armZeroUpper32Op code pas dsts = true)
    (hop : (vllGprIsaOfHooks arm64Arch vllArmNativeHooks).op code pas dsts vh = some (c, clob))
    (hdst : dsts = (.gpr rd, ()))
    (ha : ∀ r ∈ tupArgGprs pas, r ∉ armScratch) (hrd : rd ∉ armScratch)
    (hrel : TRel ((vllMach arm64Arch).PArgHolds s) pas vs) (hwp : code.wp vs P) :
    (vllMach arm64Arch).FallsTo arm64Arch.condReads h k c (rd :: armScratch) [] clob s
      (fun s' => (∃ rv : BitVec 32, P (rv, ()) ∧ s'.gpr rd = rv.setWidth 64) ∧
        s'.mem = s.mem) post := by
  subst hdst
  cases rd with
  | SP => simp [armZeroUpper32Op] at hz
  | reg d =>
    have hfb : wrapArmNative (armOp code pas (.gpr (.reg d), ()) vh) = some (c, clob) →
        (vllMach arm64Arch).FallsTo arm64Arch.condReads h k c (.reg d :: armScratch) [] clob s
          (fun s' => (∃ rv : BitVec 32, P (rv, ()) ∧ s'.gpr (.reg d) = rv.setWidth 64) ∧
            s'.mem = s.mem) post := by
      intro hf
      obtain ⟨ds, hds, rfl⟩ := wrapArmNative_eq_some hf
      obtain ⟨hp, hlen⟩ := armOp_pure_len hds
      exact armFallsTo_to_vllNative hp hlen fun host postH =>
        arm_gprSpec.op_zero32 hz hds rfl ha hrd (vllTRel_PArg_to_arm hrel) hwp
    dsimp only [vllGprIsaOfHooks, vllArmNativeHooks] at hop
    cases hhk : vllArmOpHook code pas (.gpr (.reg d), ()) vh with
    | none => rw [hhk] at hop; exact vllCoreOp_zero32 hop ha hrel hwp
    | some res =>
      rw [hhk] at hop; cases hop
      cases code with
      | copy _ =>
        rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
        rcases hrel with _ | ⟨hpa, hnil⟩; cases hnil
        cases pa with
        | vec v => exact v.elim
        | imm _ => cases hhk
        | gpr r => cases r with
          | SP => dsimp only [vllArmOpHook] at hhk; exact hfb hhk
          | reg rx =>
            cases hhk
            have hrx : (s.gpr (.reg rx)).setWidth 32 = va := hpa.2
            refine Machine.FallsTo.conseq (fallsTo_weaken_rd
              (vllMach_movW_spec arm64Arch_wf (w := .w32) (rd := .reg d) (rs := .reg rx))) ?_
            intro s' ⟨hg, _, hm⟩ _; dsimp only [Width.bits] at hg; rw [hrx] at hg
            exact ⟨⟨va, hwp, hg⟩, hm⟩
      | bitcast t u hsz =>
        rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
        rcases hrel with _ | ⟨hpa, hnil⟩; cases hnil
        cases t with
        | bool | float _ | pair _ _ => dsimp only [vllArmOpHook] at hhk; exact hfb hhk
        | bits m =>
          have hm32 : m = 32 := hsz; subst hm32
          cases pa with
          | vec v => exact v.elim
          | imm _ => cases hhk
          | gpr r => cases r with
            | SP => dsimp only [vllArmOpHook] at hhk; exact hfb hhk
            | reg rx =>
              cases hhk
              have hrx : (s.gpr (.reg rx)).setWidth 32 = va := hpa.2
              refine Machine.FallsTo.conseq (fallsTo_weaken_rd
                (vllMach_movW_spec arm64Arch_wf (w := .w32) (rd := .reg d) (rs := .reg rx))) ?_
              intro s' ⟨hg, _, hm⟩ _; dsimp only [Width.bits] at hg; rw [hrx] at hg
              exact ⟨⟨va, by simpa [OpCode.wp, ofBits, toBits] using hwp, hg⟩, hm⟩
      | zext m _ =>
        rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
        rcases hrel with _ | ⟨hpa, hnil⟩; cases hnil
        cases pa with
        | vec v => exact v.elim
        | imm _ =>
          dsimp only [vllArmOpHook] at hhk
          cases hc : ([8, 16, 32, 64].contains m && [8, 16, 32, 64].contains 32 && Nat.ble m 32) <;>
            simp only [hc, Bool.false_eq_true, ↓reduceIte] at hhk
          · exact hfb hhk
          · cases hhk
        | gpr r => cases r with
          | SP => dsimp only [vllArmOpHook] at hhk; exact hfb hhk
          | reg rx =>
            dsimp only [vllArmOpHook] at hhk
            cases hc : ([8, 16, 32, 64].contains m && [8, 16, 32, 64].contains 32 &&
                Nat.ble m 32) <;> simp only [hc, Bool.false_eq_true, ↓reduceIte] at hhk
            · exact hfb hhk
            · have hrx : (s.gpr (.reg rx)).setWidth m = va := hpa.2
              have hP : P (va.setWidth 32, ()) := hwp.2
              cases h8 : (m == 8) <;> simp only [h8, Bool.false_eq_true, ↓reduceIte] at hhk
              · cases h16 : (m == 16) <;> simp only [h16, Bool.false_eq_true, ↓reduceIte] at hhk
                · cases h32 : (m == 32) <;> simp only [h32, Bool.false_eq_true, ↓reduceIte] at hhk
                  · exact hfb hhk
                  · have hm : m = 32 := beq_iff_eq.mp h32; subst hm; cases hhk
                    refine Machine.FallsTo.conseq (fallsTo_weaken_rd
                      (vllMach_movW_spec arm64Arch_wf (w := .w32) (rd := .reg d) (rs := .reg rx)))
                      fun s' ⟨hg, _, hm'⟩ _ => by
                        dsimp only [arm64Arch, writeSubZeroExtend, Width.bits] at hg; rw [hrx] at hg
                        exact ⟨⟨va.setWidth 32, hP, by simpa using hg⟩, hm'⟩
                · have hm : m = 16 := beq_iff_eq.mp h16; subst hm; cases hhk
                  refine Machine.FallsTo.conseq (fallsTo_weaken_rd
                    (vllMach_movW_spec arm64Arch_wf (w := .w16) (rd := .reg d) (rs := .reg rx)))
                    fun s' ⟨hg, _, hm'⟩ _ => by
                      dsimp only [Width.bits] at hg; rw [hrx] at hg
                      refine ⟨⟨va.setWidth 32, hP, ?_⟩, hm'⟩
                      rw [hg]; dsimp only [arm64Arch, writeSubZeroExtend]
                      apply BitVec.eq_of_getLsbD_eq; intro j
                      by_cases hj : j < 64
                      · by_cases h16' : j < 16
                        · simp [h16']
                        · have h0 : va.getLsbD j = false :=
                            Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le va.isLt
                              (Nat.pow_le_pow_right (by decide) (by omega)))
                          simp [h0]
                      · simp [hj]
              · have hm : m = 8 := beq_iff_eq.mp h8; subst hm; cases hhk
                refine Machine.FallsTo.conseq (fallsTo_weaken_rd
                  (vllMach_movW_spec arm64Arch_wf (w := .w8) (rd := .reg d) (rs := .reg rx)))
                  fun s' ⟨hg, _, hm'⟩ _ => by
                    dsimp only [Width.bits] at hg; rw [hrx] at hg
                    refine ⟨⟨va.setWidth 32, hP, ?_⟩, hm'⟩
                    rw [hg]; dsimp only [arm64Arch, writeSubZeroExtend]
                    apply BitVec.eq_of_getLsbD_eq; intro j
                    by_cases hj : j < 64
                    · by_cases h8' : j < 8
                      · simp [h8']
                      · have h0 : va.getLsbD j = false :=
                          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le va.isLt
                            (Nat.pow_le_pow_right (by decide) (by omega)))
                        simp [h0]
                    · simp [hj]
      | trunc m _ =>
        rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
        rcases hrel with _ | ⟨hpa, hnil⟩; cases hnil
        cases pa with
        | vec v => exact v.elim
        | imm _ =>
          dsimp only [vllArmOpHook] at hhk
          cases hc : ([8, 16, 32, 64].contains m && [8, 16, 32, 64].contains 32 && Nat.ble 32 m) <;>
            simp only [hc, Bool.false_eq_true, ↓reduceIte] at hhk
          · exact hfb hhk
          · cases hhk
        | gpr r => cases r with
          | SP => dsimp only [vllArmOpHook] at hhk; exact hfb hhk
          | reg rx =>
            dsimp only [vllArmOpHook] at hhk
            cases hc : ([8, 16, 32, 64].contains m && [8, 16, 32, 64].contains 32 &&
                Nat.ble 32 m && (32 == 8 || 32 == 16 || 32 == 32)) <;>
              simp only [hc, Bool.false_eq_true, ↓reduceIte] at hhk
            · exact hfb hhk
            · cases hhk
              have h32m : 32 ≤ m := by simp only [Bool.and_eq_true, Nat.ble_eq] at hc; exact hc.1.2
              have hrx : (s.gpr (.reg rx)).setWidth m = va := hpa.2
              have hP : P (va.setWidth 32, ()) := hwp.2
              refine Machine.FallsTo.conseq (fallsTo_weaken_rd
                (vllMach_movW_spec arm64Arch_wf (w := .w32) (rd := .reg d) (rs := .reg rx))) ?_
              intro s' ⟨hg, _, hm'⟩ _
              dsimp only [Width.bits] at hg
              rw [show (s.gpr (.reg rx)).setWidth 32 = va.setWidth 32 by
                rw [← hrx, BitVec.setWidth_setWidth_of_le _ h32m]] at hg
              exact ⟨⟨va.setWidth 32, hP, hg⟩, hm'⟩
      | ofBool _ =>
        rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
        rcases hrel with _ | ⟨hpa, hnil⟩; cases hnil
        cases pa with
        | vec v => exact v.elim
        | imm _ => cases hhk
        | flag cf =>
          cases hhk
          have hEq : arm64Arch.evalCond s.flags cf = va := hpa
          refine Machine.FallsTo.conseq (fallsTo_weaken_rd
            (vllMach_setcc_exact (rd := .reg d) (c := cf))) ?_
          intro s' ⟨hg, hm⟩ _
          have hg' : s'.gpr (.reg d) = (BitVec.ofNat 32 va.toNat).setWidth 64 := by
            rw [hg, hEq]; cases va <;> rfl
          exact ⟨⟨BitVec.ofNat 32 va.toNat, hwp, hg'⟩, hm⟩
        | gpr r => cases r with
          | SP => dsimp only [vllArmOpHook] at hhk; exact hfb hhk
          | reg rx =>
            cases hhk
            refine Machine.FallsTo.conseq (fallsTo_weaken_rd
              (vllMach_movW_spec arm64Arch_wf (w := .w8) (rd := .reg d) (rs := .reg rx))) ?_
            intro s' ⟨hg, _, hm⟩ _
            have h8 : (s.gpr (.reg rx)).setWidth 8 = BitVec.ofNat 8 va.toNat := hpa
            have hg' : s'.gpr (.reg d) = (BitVec.ofNat 32 va.toNat).setWidth 64 := by
              rw [hg]; dsimp only [arm64Arch, writeSubZeroExtend]; rw [h8]; cases va <;> rfl
            exact ⟨⟨BitVec.ofNat 32 va.toNat, hwp, hg'⟩, hm⟩
      | neg _ =>
        rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
        rcases hrel with _ | ⟨hpa, hnil⟩; cases hnil
        cases pa with
        | vec v => exact v.elim
        | gpr _ => dsimp only [vllArmOpHook] at hhk; exact hfb hhk
        | imm cv =>
          cases hhk; have hEq : cv = va := hpa; subst hEq
          refine Machine.FallsTo.conseq (fallsTo_weaken_rd
            (vllMach_movi_spec (A := arm64Arch) (rd := .reg d) (imm := (-cv).setWidth 64))) ?_
          intro s' ⟨hg, hm⟩ _; exact ⟨⟨-cv, hwp, hg⟩, hm⟩
      | not _ =>
        rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
        rcases hrel with _ | ⟨hpa, hnil⟩; cases hnil
        cases pa with
        | vec v => exact v.elim
        | gpr _ => dsimp only [vllArmOpHook] at hhk; exact hfb hhk
        | imm cv =>
          cases hhk; have hEq : cv = va := hpa; subst hEq
          refine Machine.FallsTo.conseq (fallsTo_weaken_rd
            (vllMach_movi_spec (A := arm64Arch) (rd := .reg d) (imm := (~~~cv).setWidth 64))) ?_
          intro s' ⟨hg, hm⟩ _; exact ⟨⟨~~~cv, hwp, hg⟩, hm⟩
      | add _ =>
        rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
        rcases hrel with _ | ⟨hpa, hrel2⟩; rcases hrel2 with _ | ⟨hpb, hnil⟩; cases hnil
        cases pa with
        | vec v => exact v.elim
        | imm _ => dsimp only [vllArmOpHook] at hhk; exact hfb hhk
        | gpr r1 => cases r1 with
          | SP => dsimp only [vllArmOpHook] at hhk; exact hfb hhk
          | reg ra => cases pb with
            | vec v => exact v.elim
            | gpr r2 => cases r2 with
              | SP => dsimp only [vllArmOpHook] at hhk; exact hfb hhk
              | reg _ => cases hhk
            | imm cb =>
              dsimp only [vllArmOpHook] at hhk
              cases hi : ((armImm12? cb).isSome || (armImm12? (-cb)).isNone) <;>
                simp only [hi, Bool.false_eq_true, ↓reduceIte] at hhk
              · cases hhk; have hEq : cb = vb := hpb; subst hEq
                have hra : (s.gpr (.reg ra)).setWidth 32 = va := hpa.2
                refine Machine.FallsTo.conseq (fallsTo_weaken_rd
                  (vllMach_alu_spec arm64Arch_wf (op := .sub) (w := .w32) (rd := .reg d)
                    (lhs := .reg ra) (rhs := .imm ((-cb).setWidth 64)) (sf := false))) ?_
                intro s' ⟨hg, _, _, hm⟩ _
                dsimp only [CoreAlu.eval, Src.evalW, Src.eval, Width.bits] at hg
                rw [hra, setWidth_setWidth_self64 (by decide), BitVec.sub_neg] at hg
                exact ⟨⟨va + cb, hwp, hg⟩, hm⟩
              · cases hhk
      | sub _ =>
        rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases vs with ⟨va, vb, ⟨⟩⟩
        rcases hrel with _ | ⟨hpa, hrel2⟩; rcases hrel2 with _ | ⟨hpb, hnil⟩; cases hnil
        cases pa with
        | vec v => exact v.elim
        | imm _ => dsimp only [vllArmOpHook] at hhk; exact hfb hhk
        | gpr r1 => cases r1 with
          | SP => dsimp only [vllArmOpHook] at hhk; exact hfb hhk
          | reg ra => cases pb with
            | vec v => exact v.elim
            | gpr r2 => cases r2 with
              | SP => dsimp only [vllArmOpHook] at hhk; exact hfb hhk
              | reg _ => cases hhk
            | imm cb =>
              dsimp only [vllArmOpHook] at hhk
              cases hi : ((armImm12? cb).isSome || (armImm12? (-cb)).isNone) <;>
                simp only [hi, Bool.false_eq_true, ↓reduceIte] at hhk
              · cases hhk; have hEq : cb = vb := hpb; subst hEq
                have hra : (s.gpr (.reg ra)).setWidth 32 = va := hpa.2
                refine Machine.FallsTo.conseq (fallsTo_weaken_rd
                  (vllMach_alu_spec arm64Arch_wf (op := .add) (w := .w32) (rd := .reg d)
                    (lhs := .reg ra) (rhs := .imm ((-cb).setWidth 64)) (sf := false))) ?_
                intro s' ⟨hg, _, _, hm⟩ _
                dsimp only [CoreAlu.eval, Src.evalW, Src.eval, Width.bits] at hg
                rw [hra, setWidth_setWidth_self64 (by decide), ← BitVec.sub_eq_add_neg] at hg
                exact ⟨⟨va - cb, hwp, hg⟩, hm⟩
              · cases hhk
      | mul _ | and _ | or _ | xor _ | shl _ | lshr _ | ashr _ =>
        dsimp only [vllArmOpHook] at hhk
        split at hhk <;> first
          | cases hhk
          | exact hfb hhk
          | (split at hhk <;> first | cases hhk | exact hfb hhk)
      | cmp _ t _ hm => cases t <;> cases hm
      | _ => dsimp only [vllArmOpHook] at hhk; exact hfb hhk

private theorem sep_swap12 (A B C : Mem 64 → Prop) : (A ⋆ (B ⋆ C)) = (B ⋆ (A ⋆ C)) := by
  rw [← sep_assoc, sep_comm A B, sep_assoc]

private theorem sep_rot3 (A B C D : Mem 64 → Prop) :
    (A ⋆ (B ⋆ (C ⋆ D))) = (B ⋆ (C ⋆ (A ⋆ D))) := by
  rw [sep_swap12 A B, sep_swap12 A C]

private theorem sep_rot3_inv (A B C D : Mem 64 → Prop) :
    (A ⋆ (B ⋆ (C ⋆ D))) = (C ⋆ (A ⋆ (B ⋆ D))) := by
  rw [sep_swap12 B C, sep_swap12 A C]

private theorem vllArmSaveRegs_spec :
    ∀ (rs : List Arm64.Reg) (i : Nat) {h : VllHost arm64Arch} {k : Nat}
      {s : MachSt arm64Arch} {G : Mem 64 → Prop} {post : Config arm64Arch → Prop},
      8 * i + 8 * rs.length ≤ 2 ^ 64 →
      (∀ r ∈ rs, r ∉ armScratch) → arm64Arch.abi.spOk (s.gpr .SP) →
      (s.mem =⋆ region (s.gpr .SP + BitVec.ofNat 64 (8 * i)) (8 * rs.length) ⋆ G) →
      (vllMach arm64Arch).FallsTo arm64Arch.condReads h k (vllArmSaveRegs i rs)
        armScratch [] maskNone s
        (fun s' => s'.mem =⋆
          array64 (s.gpr .SP + BitVec.ofNat 64 (8 * i)) (rs.map s.gpr) ⋆ G) post
  | [], i, h, k, s, G, post, _, _, _, hm => by
    simp only [vllArmSaveRegs, List.length_nil, Nat.mul_zero, List.map_nil, array64_nil] at hm ⊢
    exact Machine.FallsTo.nil (by simpa [region_zero] using hm)
  | [r], i, h, k, s, G, post, _, _, _, hm => by
    simp only [vllArmSaveRegs, List.length_singleton, Nat.mul_one, List.map_cons, List.map_nil,
      array64_cons, array64_nil] at hm ⊢
    exact Machine.FallsTo.conseq (vllMach_slotSt_spec hm) fun s' hs' _ => by
      simpa [sep_emp] using hs'
  | r1 :: r2 :: rs, i, h, k, s, G, post, hbd, hns, hsp, hm => by
    have hsp_ns : XRegOrSp.SP ∉ armScratch := by simp [armScratch]
    have hadd1 : s.gpr .SP + BitVec.ofNat 64 (8 * i) + 8 =
        s.gpr .SP + BitVec.ofNat 64 (8 * (i + 1)) := by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega
    have hadd2 : s.gpr .SP + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 16 =
        s.gpr .SP + BitVec.ofNat 64 (8 * (i + 2)) := by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega
    have h88 : s.gpr .SP + BitVec.ofNat 64 (8 * i) + 8 + 8 =
        s.gpr .SP + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 16 := by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
    have hstep1 : ∀ (x : Arm64.Reg) (rest : List Arm64.Reg),
        x :: rest = r1 :: r2 :: rs →
        (vllMach arm64Arch).FallsTo arm64Arch.condReads h k
          ([.slotSt i x] ++ vllArmSaveRegs (i + 1) rest) armScratch [] maskNone s
          (fun s' => s'.mem =⋆
            array64 (s.gpr .SP + BitVec.ofNat 64 (8 * i)) ((x :: rest).map s.gpr) ⋆ G) post := by
      intro x rest hEq; cases hEq
      have hlen : 8 * (r1 :: r2 :: rs).length = 8 + 8 * (r2 :: rs).length := by simp; omega
      have hbd1 : 8 + 8 * (r2 :: rs).length ≤ 2 ^ 64 := by
        simp only [List.length_cons] at hbd ⊢; omega
      rw [hlen, region_split hbd1, sep_assoc] at hm
      have hcomp := Machine.FallsTo.comp (vllMach_slotSt_spec (rs := r1) hm) fun s1 hm1 hfr1 => by
        have hsp1 : s1.gpr .SP = s.gpr .SP := hfr1.1 .SP hsp_ns
        have hrest : ∀ r ∈ r2 :: rs, s1.gpr r = s.gpr r := fun r hr =>
          hfr1.1 r (hns r (List.mem_cons_of_mem _ hr))
        have hm1' : (s1.mem =⋆ region (s1.gpr .SP + BitVec.ofNat 64 (8 * (i + 1)))
            (8 * (r2 :: rs).length) ⋆
            (cell64 (s.gpr .SP + BitVec.ofNat 64 (8 * i)) (s.gpr r1) ⋆ G)) := by
          rw [hsp1, ← hadd1]
          dsimp only [arm64Arch, arm64Abi] at hm1
          exact sep_cast hm1 (sep_swap12 _ _ _)
        have hih := vllArmSaveRegs_spec (r2 :: rs) (i + 1) (h := h)
          (k := k + 1) (s := s1) (post := post)
          (by simp at hbd ⊢; omega) (fun r hr => hns r (List.mem_cons_of_mem _ hr))
          (by rwa [hsp1]) hm1'
        exact Machine.FallsTo.conseq hih (Q₂ := fun (s' : MachSt arm64Arch) => s'.mem =⋆
            array64 (s.gpr .SP + BitVec.ofNat 64 (8 * i)) ((r1 :: r2 :: rs).map s.gpr) ⋆ G)
          fun s2 hm2 _ => by
          rw [hsp1, ← hadd1, List.map_congr_left hrest] at hm2
          rw [List.map_cons, array64_cons, sep_assoc]
          exact sep_cast hm2 (sep_swap12 _ _ _)
      exact Machine.FallsTo.weaken hcomp
        (fun r hr => by rcases List.mem_append.mp hr with h1 | h1 <;> exact h1)
        (fun _ h => nomatch h) (by decide)
    cases r1 with
    | SP => exact hstep1 .SP (r2 :: rs) rfl
    | reg x1 => cases r2 with
      | SP => exact hstep1 (.reg x1) (.SP :: rs) rfl
      | reg x2 =>
        dsimp only [vllArmSaveRegs]
        cases hfit : armFitsPairOff (8 * i) <;>
          simp only [Bool.false_eq_true, ↓reduceIte]
        · have hlen : 8 * (XRegOrSp.reg x1 :: XRegOrSp.reg x2 :: rs).length =
              8 + (8 + 8 * rs.length) := by simp; omega
          have hbd1 : 8 + (8 + 8 * rs.length) ≤ 2 ^ 64 := by simp at hbd; omega
          have hbd2 : 8 + 8 * rs.length ≤ 2 ^ 64 := by omega
          rw [hlen, region_split hbd1, region_split hbd2, sep_assoc, sep_assoc] at hm
          have hst12 : (vllMach arm64Arch).FallsTo arm64Arch.condReads h k
              ([.slotSt i (.reg x1)] ++ ([.slotSt (i + 1) (.reg x2)] ++ vllArmSaveRegs (i + 2) rs))
              armScratch [] maskNone s
              (fun s' => s'.mem =⋆
                array64 (s.gpr .SP + BitVec.ofNat 64 (8 * i))
                  ((XRegOrSp.reg x1 :: XRegOrSp.reg x2 :: rs).map s.gpr) ⋆ G) post := by
            have hcomp1 :=
              Machine.FallsTo.comp (vllMach_slotSt_spec (rs := XRegOrSp.reg x1) hm)
              fun s1 hm1 hfr1 => by
              have hsp1 : s1.gpr .SP = s.gpr .SP := hfr1.1 .SP hsp_ns
              have hx2 : s1.gpr (.reg x2) = s.gpr (.reg x2) :=
                hfr1.1 (.reg x2) (hns _ (List.mem_cons_of_mem _ List.mem_cons_self))
              have hm1' : (s1.mem =⋆ region (s1.gpr .SP + BitVec.ofNat 64 (8 * (i + 1))) 8 ⋆
                  (region (s.gpr .SP + BitVec.ofNat 64 (8 * (i + 2))) (8 * rs.length) ⋆
                    (cell64 (s.gpr .SP + BitVec.ofNat 64 (8 * i)) (s.gpr (.reg x1)) ⋆ G))) := by
                rw [hsp1, ← hadd1, ← hadd2, ← h88]
                dsimp only [arm64Arch, arm64Abi] at hm1
                exact sep_cast hm1 (sep_rot3 _ _ _ _)
              have hcomp2 :=
                Machine.FallsTo.comp (vllMach_slotSt_spec (rs := XRegOrSp.reg x2) hm1')
                fun s2 hm2 hfr2 => by
                have hsp2 : s2.gpr .SP = s.gpr .SP := (hfr2.1 .SP hsp_ns).trans hsp1
                have hrest : ∀ r ∈ rs, s2.gpr r = s.gpr r := fun r hr =>
                  (hfr2.1 r (hns r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)))).trans
                    (hfr1.1 r (hns r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr))))
                have hm2' : (s2.mem =⋆ region (s2.gpr .SP + BitVec.ofNat 64 (8 * (i + 2)))
                    (8 * rs.length) ⋆
                    (cell64 (s.gpr .SP + BitVec.ofNat 64 (8 * i)) (s.gpr (.reg x1)) ⋆
                    (cell64 (s.gpr .SP + BitVec.ofNat 64 (8 * (i + 1))) (s.gpr (.reg x2)) ⋆
                    G))) := by
                  rw [hsp2]; dsimp only [arm64Arch, arm64Abi] at hm2; rw [hsp1, hx2] at hm2
                  exact sep_cast hm2 (sep_rot3 _ _ _ _)
                have hih := vllArmSaveRegs_spec rs (i + 2) (h := h)
                  (k := k + 1 + 1) (s := s2) (post := post) (by simp at hbd ⊢; omega)
                  (fun r hr => hns r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)))
                  (by rwa [hsp2]) hm2'
                exact Machine.FallsTo.conseq hih (Q₂ := fun (s' : MachSt arm64Arch) => s'.mem =⋆
                    array64 (s.gpr .SP + BitVec.ofNat 64 (8 * i))
                      ((XRegOrSp.reg x1 :: XRegOrSp.reg x2 :: rs).map s.gpr) ⋆ G)
                  fun s3 hm3 _ => by
                  rw [hsp2, ← hadd2, List.map_congr_left hrest] at hm3
                  rw [← hadd1, ← h88] at hm3
                  simp only [List.map_cons, array64_cons, sep_assoc]
                  exact sep_cast hm3 (sep_rot3 _ _ _ _)
              exact Machine.FallsTo.weaken (g₂ := armScratch) (v₂ := []) (f₂ := maskNone) hcomp2
                (fun r hr => by rcases List.mem_append.mp hr with h1 | h1 <;> exact h1)
                (fun _ h => nomatch h) (by decide)
            exact Machine.FallsTo.weaken hcomp1
              (fun r hr => by rcases List.mem_append.mp hr with h1 | h1 <;> exact h1)
              (fun _ h => nomatch h) (by decide)
          simpa only [List.cons_append, List.nil_append] using hst12
        · have hlen : 8 * (XRegOrSp.reg x1 :: XRegOrSp.reg x2 :: rs).length =
              16 + 8 * rs.length := by simp; omega
          have hbd1 : 16 + 8 * rs.length ≤ 2 ^ 64 := by simp at hbd; omega
          rw [hlen, region_split hbd1, sep_assoc] at hm
          let stpD : _root_.Directive :=
            .instr (armInsI (.STP (zr x1 .W64) (zr x2 .W64) (atOff .SP (8 * i))))
          have hstpEq : armSaveRegs i [.reg x1, .reg x2] = [stpD] := by
            simp [armSaveRegs, armSaveRegsIns, armStpSpXRegIns, hfit, emitClean, stpD]
          have hstpPure : [stpD].all (dirPure none) = true := by
            simp [stpD, dirPure, opPure, addrExprPure, constPure]
          have hstp : (vllMach arm64Arch).FallsTo arm64Arch.condReads h k [Instr.native stpD]
              armScratch [] maskNone s
              (fun s' => s'.mem =⋆
                array64 (s.gpr .SP + BitVec.ofNat 64 (8 * i)) [s.gpr (.reg x1), s.gpr (.reg x2)] ⋆
                (region (s.gpr .SP + BitVec.ofNat 64 (8 * (i + 2))) (8 * rs.length) ⋆ G))
              post := by
            have hstp' := armFallsTo_to_vllNative (ds := [stpD]) hstpPure (by simp)
              (vh := h) (k := k) (gClob := armScratch) (fClob := maskNone) (s := s)
              (Q := fun s' => s'.mem =⋆
                array64 (s.gpr .SP + BitVec.ofNat 64 (8 * i)) [s.gpr (.reg x1), s.gpr (.reg x2)] ⋆
                  (region (s.gpr .SP + BitVec.ofNat 64 (8 * (i + 2))) (8 * rs.length) ⋆ G))
              (post := post) fun host postH => by
                rw [← hstpEq]
                have hmPair : ((vllToMachData s).dmem =⋆
                    region (Arm64.get (vllToMachData s) .SP + BitVec.ofNat 64 (8 * i))
                      (8 * ([XRegOrSp.reg x1, XRegOrSp.reg x2]).length) ⋆
                    (region (s.gpr .SP + BitVec.ofNat 64 (8 * (i + 2))) (8 * rs.length) ⋆ G)) := by
                  rw [get_vllToMachData, ← hadd2]; exact hm
                have hfr := arm_frameSpec.saveRegs_spec (h := host) (k := 0) (i := i)
                  (rs := [.reg x1, .reg x2]) rfl (by simp at hbd ⊢; omega)
                  (fun r hr => by
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
                    rcases hr with rfl | rfl
                    · exact hns _ List.mem_cons_self
                    · exact hns _ (List.mem_cons_of_mem _ List.mem_cons_self))
                  (by
                    dsimp only [armFramePreds, armMach, armFrame]
                    rw [get_vllToMachData]; exact hsp)
                  hmPair (post := postH)
                exact Machine.FallsTo.conseq hfr fun sm' hsm' _ => by
                  simpa [get_vllToMachData, machDataToVll] using hsm'
            exact hstp'
          have hcomp := Machine.FallsTo.comp hstp fun s1 hm1 hfr1 => by
            have hsp1 : s1.gpr .SP = s.gpr .SP := hfr1.1 .SP hsp_ns
            have hrest : ∀ r ∈ rs, s1.gpr r = s.gpr r := fun r hr =>
              hfr1.1 r (hns r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)))
            have hm1' : (s1.mem =⋆ region (s1.gpr .SP + BitVec.ofNat 64 (8 * (i + 2)))
                (8 * rs.length) ⋆
                (array64 (s.gpr .SP + BitVec.ofNat 64 (8 * i))
                  [s.gpr (.reg x1), s.gpr (.reg x2)] ⋆ G)) := by
              rw [hsp1]; exact sep_cast hm1 (sep_swap12 _ _ _)
            have hih := vllArmSaveRegs_spec rs (i + 2) (h := h)
              (k := k + 1) (s := s1) (post := post)
              (by simp at hbd ⊢; omega)
              (fun r hr => hns r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)))
              (by rwa [hsp1]) hm1'
            exact Machine.FallsTo.conseq hih (Q₂ := fun (s' : MachSt arm64Arch) => s'.mem =⋆
                array64 (s.gpr .SP + BitVec.ofNat 64 (8 * i))
                  ((XRegOrSp.reg x1 :: XRegOrSp.reg x2 :: rs).map s.gpr) ⋆ G)
              fun s2 hm2 _ => by
              rw [hsp1, ← hadd2, List.map_congr_left hrest, ← h88] at hm2
              simp only [List.map_cons, array64_cons, array64_nil, sep_emp, sep_assoc] at hm2 ⊢
              exact sep_cast hm2 (sep_rot3 _ _ _ _)
          exact Machine.FallsTo.weaken hcomp
            (fun r hr => by rcases List.mem_append.mp hr with h1 | h1 <;> exact h1)
            (fun _ h => nomatch h) (by decide)

private theorem vllArmRestoreRegs_spec :
    ∀ (rs : List Arm64.Reg) (i : Nat) {h : VllHost arm64Arch} {k : Nat}
      {s₀ s : MachSt arm64Arch} {G : Mem 64 → Prop} {post : Config arm64Arch → Prop},
      rs.Nodup → (∀ r ∈ rs, r ∈ arm64Arch.abi.calleeSaved) →
      arm64Arch.abi.spOk (s.gpr .SP) →
      (s.mem =⋆ array64 (s.gpr .SP + BitVec.ofNat 64 (8 * i)) (rs.map s₀.gpr) ⋆ G) →
      (vllMach arm64Arch).FallsTo arm64Arch.condReads h k (vllArmRestoreRegs i rs)
        (rs ++ armScratch) [] maskNone s
        (fun s' => (∀ r ∈ rs, s'.gpr r = s₀.gpr r) ∧ s'.mem = s.mem) post
  | [], i, h, k, s₀, s, G, post, _, _, _, _ =>
    Machine.FallsTo.nil ⟨(fun _ hr => nomatch hr), rfl⟩
  | [r], i, h, k, s₀, s, G, post, _, _, _, hm => by
    simp only [vllArmRestoreRegs, List.map_cons, List.map_nil, array64_cons, array64_nil,
      sep_emp] at hm ⊢
    exact Machine.FallsTo.conseq (vllMach_slotLd_spec hm) fun s' ⟨hr, hm'⟩ _ =>
      ⟨fun r' hr' => by simp only [List.mem_singleton] at hr'; subst hr'; exact hr, hm'⟩
  | r1 :: r2 :: rs, i, h, k, s₀, s, G, post, hnd, hcs, hsp, hm => by
    have hsp_cs : ∀ r ∈ r1 :: r2 :: rs, r ≠ .SP := fun r hr hEq => by
      have hc := hcs r hr; subst hEq; simp [arm64Arch, arm64Abi, armFrame] at hc
    have hsp_ns : XRegOrSp.SP ∉ armScratch := by simp [armScratch]
    have hadd1 : s.gpr .SP + BitVec.ofNat 64 (8 * i) + 8 =
        s.gpr .SP + BitVec.ofNat 64 (8 * (i + 1)) := by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega
    have hadd2 : s.gpr .SP + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 16 =
        s.gpr .SP + BitVec.ofNat 64 (8 * (i + 2)) := by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega
    have h88 : s.gpr .SP + BitVec.ofNat 64 (8 * i) + 8 + 8 =
        s.gpr .SP + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 16 := by
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
    have hnd1 := List.nodup_cons.mp hnd
    have hnd2 := List.nodup_cons.mp hnd1.2
    have hcs_ns : ∀ r, r ∈ arm64Arch.abi.calleeSaved → r ∉ armScratch := fun r hr hs =>
      (arm64Arch_wf.scratch_disj r hs).2.1 hr
    cases r1 with
    | SP => exact absurd rfl (hsp_cs .SP List.mem_cons_self)
    | reg x1 => cases r2 with
      | SP => exact absurd rfl (hsp_cs .SP (List.mem_cons_of_mem _ List.mem_cons_self))
      | reg x2 =>
        dsimp only [vllArmRestoreRegs]
        cases hfit : armFitsPairOff (8 * i) <;>
          simp only [Bool.false_eq_true, ↓reduceIte]
        · simp only [List.map_cons, array64_cons, sep_assoc] at hm
          have hld12 : (vllMach arm64Arch).FallsTo arm64Arch.condReads h k
              ([.slotLd (.reg x1) i] ++ ([.slotLd (.reg x2) (i + 1)] ++
                vllArmRestoreRegs (i + 2) rs))
              ((XRegOrSp.reg x1 :: XRegOrSp.reg x2 :: rs) ++ armScratch) [] maskNone s
              (fun s' => (∀ r ∈ XRegOrSp.reg x1 :: XRegOrSp.reg x2 :: rs,
                s'.gpr r = s₀.gpr r) ∧ s'.mem = s.mem) post := by
            have hcomp1 :=
              Machine.FallsTo.comp (vllMach_slotLd_spec (rd := XRegOrSp.reg x1) hm)
              fun s1 ⟨hg1, hm1⟩ hfr1 => by
              have hsp1 : s1.gpr .SP = s.gpr .SP := hfr1.1 .SP (by
                simp [arm64Arch, arm64Abi, armScratch])
              have hm1' : (s1.mem =⋆ cell64 (s1.gpr .SP + BitVec.ofNat 64 (8 * (i + 1)))
                  (s₀.gpr (.reg x2)) ⋆
                  (array64 (s.gpr .SP + BitVec.ofNat 64 (8 * (i + 2))) (rs.map s₀.gpr) ⋆
                    (cell64 (s.gpr .SP + BitVec.ofNat 64 (8 * i)) (s₀.gpr (.reg x1)) ⋆ G))) := by
                rw [hm1, hsp1, ← hadd1, ← hadd2, ← h88]
                exact sep_cast hm (sep_rot3 _ _ _ _)
              have hcomp2 :=
                Machine.FallsTo.comp (vllMach_slotLd_spec (rd := XRegOrSp.reg x2) hm1')
                fun s2 ⟨hg2, hm2⟩ hfr2 => by
                have hsp2 : s2.gpr .SP = s.gpr .SP := (hfr2.1 .SP (by
                  simp [arm64Arch, arm64Abi, armScratch])).trans hsp1
                have hm2' : (s2.mem =⋆ array64 (s2.gpr .SP + BitVec.ofNat 64 (8 * (i + 2)))
                    (rs.map s₀.gpr) ⋆
                    (cell64 (s.gpr .SP + BitVec.ofNat 64 (8 * i)) (s₀.gpr (.reg x1)) ⋆
                    (cell64 (s.gpr .SP + BitVec.ofNat 64 (8 * (i + 1))) (s₀.gpr (.reg x2)) ⋆
                    G))) := by
                  rw [hm2, hm1, hsp2, ← hadd2, ← hadd1, ← h88]
                  exact sep_cast hm (sep_rot3_inv _ _ _ _)
                have hih := vllArmRestoreRegs_spec rs (i + 2) (h := h)
                  (k := k + 1 + 1) (s₀ := s₀) (s := s2) (post := post) hnd2.2
                  (fun r hr => hcs r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)))
                  (by rwa [hsp2]) hm2'
                exact Machine.FallsTo.conseq hih
                  (Q₂ := fun (s' : MachSt arm64Arch) =>
                    (∀ r ∈ XRegOrSp.reg x1 :: XRegOrSp.reg x2 :: rs,
                      s'.gpr r = s₀.gpr r) ∧ s'.mem = s.mem)
                  fun s3 ⟨h3, hm3⟩ hfr3 => by
                  refine ⟨fun r hr => ?_, hm3.trans (hm2.trans hm1)⟩
                  rcases List.mem_cons.mp hr with rfl | hr'
                  · have hne1 : XRegOrSp.reg x1 ∉ rs ++ armScratch := by
                      intro hm'; rcases List.mem_append.mp hm' with h1 | h2
                      · exact hnd1.1 (List.mem_cons_of_mem _ h1)
                      · exact hcs_ns _ (hcs _ List.mem_cons_self) h2
                    have hne2 : XRegOrSp.reg x1 ∉ XRegOrSp.reg x2 :: armScratch := by
                      intro hm'
                      rcases List.mem_cons.mp hm' with h1 | h2
                      · exact hnd1.1 (h1 ▸ List.mem_cons_self)
                      · exact hcs_ns _ (hcs _ List.mem_cons_self) h2
                    exact (hfr3.1 _ hne1).trans ((hfr2.1 _ hne2).trans hg1)
                  · rcases List.mem_cons.mp hr' with rfl | hr''
                    · have hne1 : XRegOrSp.reg x2 ∉ rs ++ armScratch := by
                        intro hm'; rcases List.mem_append.mp hm' with h1 | h2
                        · exact hnd2.1 h1
                        · exact hcs_ns _ (hcs _ (List.mem_cons_of_mem _ List.mem_cons_self)) h2
                      exact (hfr3.1 _ hne1).trans hg2
                    · exact h3 r hr''
              exact Machine.FallsTo.weaken
                (g₂ := (XRegOrSp.reg x2 :: rs) ++ armScratch) (v₂ := []) (f₂ := maskNone) hcomp2
                (fun r hr => by
                  rcases List.mem_append.mp hr with h1 | h2
                  · rcases List.mem_cons.mp h1 with rfl | hs
                    · exact List.mem_append_left _ List.mem_cons_self
                    · exact List.mem_append_right _ hs
                  · rcases List.mem_append.mp h2 with hr' | hs
                    · exact List.mem_append_left _ (List.mem_cons_of_mem _ hr')
                    · exact List.mem_append_right _ hs)
                (fun _ h => nomatch h) (by decide)
            exact Machine.FallsTo.weaken hcomp1
              (fun r hr => by
                rcases List.mem_append.mp hr with h1 | h2
                · rcases List.mem_cons.mp h1 with rfl | hs
                  · exact List.mem_append_left _ List.mem_cons_self
                  · exact List.mem_append_right _ hs
                · rcases List.mem_append.mp h2 with hr' | hs
                  · exact List.mem_append_left _ (List.mem_cons_of_mem _ hr')
                  · exact List.mem_append_right _ hs)
              (fun _ h => nomatch h) (by decide)
          simpa only [List.cons_append, List.nil_append] using hld12
        · let ldpD : _root_.Directive :=
            .instr (armInsI (.LDP (zr x1 .W64) (zr x2 .W64) (atOff .SP (8 * i))))
          have hldpEq : armRestoreRegs i [.reg x1, .reg x2] = [ldpD] := by
            simp [armRestoreRegs, armRestoreRegsIns, armLdpSpXRegIns, hfit, emitClean, ldpD]
          have hldpPure : [ldpD].all (dirPure none) = true := by
            simp [ldpD, dirPure, opPure, addrExprPure, constPure]
          have hldp : (vllMach arm64Arch).FallsTo arm64Arch.condReads h k [Instr.native ldpD]
              ([.reg x1, .reg x2] ++ armScratch) [] maskNone s
              (fun s' => (∀ r ∈ [XRegOrSp.reg x1, .reg x2], s'.gpr r = s₀.gpr r) ∧
                s'.mem = s.mem) post := by
            have hldp' := armFallsTo_to_vllNative (ds := [ldpD]) hldpPure (by simp)
              (vh := h) (k := k) (gClob := [.reg x1, .reg x2] ++ armScratch) (fClob := maskNone)
              (s := s) (Q := fun s' => (∀ r ∈ [XRegOrSp.reg x1, .reg x2], s'.gpr r = s₀.gpr r) ∧
                s'.mem = s.mem) (post := post) fun host postH => by
                rw [← hldpEq]
                have hmPair : ((vllToMachData s).dmem =⋆
                    array64 (Arm64.get (vllToMachData s) .SP + BitVec.ofNat 64 (8 * i))
                      ([XRegOrSp.reg x1, .reg x2].map (Arm64.get (vllToMachData s₀))) ⋆
                    (array64 (s.gpr .SP + BitVec.ofNat 64 (8 * (i + 2))) (rs.map s₀.gpr) ⋆ G)) := by
                  simp only [List.map_cons, List.map_nil, array64_cons, array64_nil, sep_emp,
                    get_vllToMachData, sep_assoc] at hm ⊢
                  rw [← hadd2, ← h88]; exact hm
                have hndPair : ([XRegOrSp.reg x1, .reg x2]).Nodup :=
                  List.nodup_cons.mpr ⟨fun hm' => by
                    simp only [List.mem_singleton] at hm'
                    exact hnd1.1 (hm' ▸ List.mem_cons_self),
                    List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩⟩
                have hfr := arm_frameSpec.restoreRegs_spec (h := host) (k := 0) (i := i)
                  (rs := [.reg x1, .reg x2]) (s₀ := vllToMachData s₀) rfl hndPair
                  (fun r hr => by
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
                    rcases hr with rfl | rfl
                    · exact hcs _ List.mem_cons_self
                    · exact hcs _ (List.mem_cons_of_mem _ List.mem_cons_self))
                  (by
                    dsimp only [armFramePreds, armMach, armFrame]
                    rw [get_vllToMachData]; exact hsp)
                  hmPair (post := postH)
                exact Machine.FallsTo.conseq hfr fun sm' ⟨hg, hm'⟩ _ =>
                  ⟨fun r hr => by simpa [get_vllToMachData, machDataToVll] using hg r hr, hm'⟩
            exact hldp'
          have hcomp := Machine.FallsTo.comp hldp fun s1 ⟨hg1, hm1⟩ hfr1 => by
            have hsp1 : s1.gpr .SP = s.gpr .SP := hfr1.1 .SP (by simp [armScratch])
            have hm1' : (s1.mem =⋆ array64 (s1.gpr .SP + BitVec.ofNat 64 (8 * (i + 2)))
                (rs.map s₀.gpr) ⋆
                (cell64 (s.gpr .SP + BitVec.ofNat 64 (8 * i)) (s₀.gpr (.reg x1)) ⋆
                 (cell64 (s.gpr .SP + BitVec.ofNat 64 (8 * (i + 1))) (s₀.gpr (.reg x2)) ⋆
                  G))) := by
              rw [hm1, hsp1, ← hadd2, ← hadd1, ← h88]
              simp only [List.map_cons, array64_cons, sep_assoc] at hm
              exact sep_cast hm (sep_rot3_inv _ _ _ _)
            have hih := vllArmRestoreRegs_spec rs (i + 2) (h := h)
              (k := k + 1) (s₀ := s₀) (s := s1) (post := post) hnd2.2
              (fun r hr => hcs r (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hr)))
              (by rwa [hsp1]) hm1'
            exact Machine.FallsTo.conseq hih
              (Q₂ := fun (s' : MachSt arm64Arch) => (∀ r ∈ XRegOrSp.reg x1 :: XRegOrSp.reg x2 :: rs,
                s'.gpr r = s₀.gpr r) ∧ s'.mem = s.mem)
              fun s2 ⟨h2, hm2⟩ hfr2 => by
              refine ⟨fun r hr => ?_, hm2.trans hm1⟩
              rcases List.mem_cons.mp hr with rfl | hr'
              · have hne : XRegOrSp.reg x1 ∉ rs ++ armScratch := by
                  intro hm'; rcases List.mem_append.mp hm' with h1 | h2
                  · exact hnd1.1 (List.mem_cons_of_mem _ h1)
                  · exact hcs_ns _ (hcs _ List.mem_cons_self) h2
                exact (hfr2.1 _ hne).trans (hg1 _ List.mem_cons_self)
              · rcases List.mem_cons.mp hr' with rfl | hr''
                · have hne : XRegOrSp.reg x2 ∉ rs ++ armScratch := by
                    intro hm'; rcases List.mem_append.mp hm' with h1 | h2
                    · exact hnd2.1 h1
                    · exact hcs_ns _ (hcs _ (List.mem_cons_of_mem _ List.mem_cons_self)) h2
                  exact (hfr2.1 _ hne).trans (hg1 _ (List.mem_cons_of_mem _ List.mem_cons_self))
                · exact h2 r hr''
          exact Machine.FallsTo.weaken hcomp
            (fun r hr => by
              simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
              rcases hr with ((rfl | rfl) | hs) | (hr | hs) <;> simp [*])
            (fun _ h => nomatch h) (by decide)

private theorem gprHolds_vllToMach {s : MachSt arm64Arch} {r : Arm64.Reg} {t : Ty} {v : Val t}
    (h : GprHolds (s.gpr r) t v) : GprHolds (Arm64.get (vllToMachData s) r) t v := by
  rw [get_vllToMachData (s := s) r]; exact h

/-- Complete soundness proof `VllPolicySpec arm64Arch vllArmNativeHooks`. -/
theorem vllArmPolicySpec : VllPolicySpec arm64Arch vllArmNativeHooks where
  clearFlags_frame := clearFlags_frame_of_nonzero armCondReads_ne_zero
  cmpFlags_spec := fun {_ _ _ _ _ _} h => vllArm_cmpFlags_spec h
  jnzGpr_override_spec := by
    intro fn h k j r l b s post hfn hc hl hr hb hcont
    cases hfn
    obtain ⟨hp, hlen⟩ := armJnzGpr_pure_len r l
    refine armBranchRun_to_vllNative hp hlen hc hl ?_ (by simpa only [List.length_map] using hcont)
    intro host jt postH hinfH hlabH hcontH
    exact arm_gprSpec.jnzGpr_spec (b := b) hinfH hlabH hr (gprHolds_vllToMach hb)
      (fun sm' hfr hm => by simpa only [Nat.zero_add] using hcontH sm' hfr hm)
  jnzGprInv_spec := vllArm_jnzGprInv_spec
  opHook_spec := vllArmOpHook_spec
  storeHook_spec := by
    intro h k t pa a c clob v s post hhk hns hh hok
    have hfb : wrapArmNative (armStore t pa a) = some (c, clob) := by
      dsimp only [vllArmNativeHooks, vllArmStoreHook] at hhk
      split at hhk <;> first | cases hhk | exact hhk
    obtain ⟨ds, hds, rfl⟩ := wrapArmNative_eq_some hfb
    obtain ⟨hp, hlen⟩ := armStore_pure_len hds
    have hg : Arm64.get (vllToMachData s) = s.gpr := funext (get_vllToMachData (s := s))
    refine armFallsTo_to_vllNative hp hlen fun host postH =>
      Machine.FallsTo.conseq
        (arm_gprSpec.store_spec hds hns (vllPArg_to_arm hh) (by
          show storeOk (vllToMachData s).dmem t (a.eval (Arm64.get (vllToMachData s)))
          rw [hg]; exact hok))
        fun sm' hm' _ => by
          show sm'.dmem = storeMem s.mem t (a.eval s.gpr) v
          rw [← hg]; exact hm'
  load_zero32 := fun _ h k rd a c clob s post v hld hrd ha hval =>
    vllCoreLoad_zx_zero32 arm64Arch arm64Arch_wf hld hval
  load_zext := fun _ h k t rd a c clob v s post hld hrd ha hval =>
    vllCoreLoad_zx_zext arm64Arch arm64Arch_wf hld hval
  op_zero32 := vllArmOp_zero32_aux
  testOp_spec := by
    intro h k w neg pa pb pd c clob va vb s post hhk hab hd hpa hpb
    obtain ⟨ds, hds, rfl⟩ := wrapArmNative_eq_some hhk
    obtain ⟨hp, hlen⟩ := armTestOp_pure_len hds
    refine armFallsTo_to_vllNative hp hlen fun host postH =>
      Machine.FallsTo.conseq
        (arm_gprSpec.testOp_spec hds hab hd (vllPArg_to_arm hpa) (vllPArg_to_arm hpb))
        fun sm' ⟨hd', hm'⟩ _ => ⟨armPDst_to_vll hd', hm'⟩
  loadSext_spec := by
    intro h k m n rd a c clob v s post hhk hrd ha hval
    dsimp only [vllArmNativeHooks, vllArmLoadSext] at hhk
    cases hok : (!(m == 8 || m == 16) || !Nat.blt m n || !Nat.ble n 64) <;>
      simp only [hok, Bool.false_eq_true, ↓reduceIte] at hhk
    · have hm : m = 8 ∨ m = 16 := by
        simp only [Bool.or_eq_false_iff, Bool.not_eq_false', Bool.or_eq_true, beq_iff_eq] at hok
        exact hok.1.1
      rcases hm with rfl | rfl
      · cases hv : armAddrValid 1 a <;> simp only [hv, Bool.false_eq_true, ↓reduceIte] at hhk
        · cases hhk
        · cases hhk
          refine Machine.FallsTo.conseq (fallsTo_weaken_rd
            (vllMach_load_spec arm64Arch_wf (w := .w8) (ext := .sx) (rd := rd) (addr := a) hval))
            fun s' ⟨hg, _, hm⟩ _ => ⟨hg, hm⟩
      · cases hv : armAddrValid 2 a <;> simp only [hv, Bool.false_eq_true, ↓reduceIte] at hhk
        · cases hhk
        · cases hhk
          refine Machine.FallsTo.conseq (fallsTo_weaken_rd
            (vllMach_load_spec arm64Arch_wf (w := .w16) (ext := .sx) (rd := rd) (addr := a) hval))
            fun s' ⟨hg, _, hm⟩ _ => ⟨hg, hm⟩
    · cases hhk
  cmpZeroJcc_spec := by
    intro h k j co w r l c clob v s post hhk hc hl hr hv hcont
    obtain ⟨ds, hds, rfl⟩ := wrapArmNative_eq_some hhk
    obtain ⟨hp, hlen⟩ := armCmpZeroJcc_pure_len hds
    refine armBranchRun_to_vllNative hp hlen hc hl ?_ (by simpa only [List.length_map] using hcont)
    intro host jt postH hinfH hlabH hcontH
    exact arm_gprSpec.cmpZeroJcc_spec (v := v) hds hinfH hlabH hr (gprHolds_vllToMach hv)
      (fun sm' hfr hm => by simpa only [Nat.zero_add] using hcontH sm' hfr hm)
  testJcc_spec := by
    intro h k j neg w r mask l c clob v s post hhk hc hl hr hv hcont
    obtain ⟨ds, hds, rfl⟩ := wrapArmNative_eq_some hhk
    obtain ⟨hp, hlen⟩ := armTestJcc_pure_len hds
    refine armBranchRun_to_vllNative hp hlen hc hl ?_ (by simpa only [List.length_map] using hcont)
    intro host jt postH hinfH hlabH hcontH
    exact arm_gprSpec.testJcc_spec (v := v) hds hinfH hlabH hr (gprHolds_vllToMach hv)
      (fun sm' hfr hm => by simpa only [Nat.zero_add] using hcontH sm' hfr hm)
  leaArith_spec := by
    intro h k w base? idx sc disp rd c clob vb vi s post hhk hb hi hrd hvb hvi
    obtain ⟨ds, hds, rfl⟩ := wrapArmNative_eq_some hhk
    obtain ⟨hp, hlen⟩ := armLeaArith_pure_len hds
    exact armFallsTo_to_vllNative hp hlen fun host postH =>
      arm_gprSpec.leaArith_spec hds hb hi hrd
        (fun r hr => gprHolds_vllToMach (hvb r hr)) (gprHolds_vllToMach hvi)
  leaArith_zero32 := by
    intro _ h k base? idx sc disp rd c clob vb vi s post hhk hb hi hrd hvb hvi
    obtain ⟨ds, hds, rfl⟩ := wrapArmNative_eq_some hhk
    obtain ⟨hp, hlen⟩ := armLeaArith_pure_len hds
    exact armFallsTo_to_vllNative hp hlen fun host postH =>
      arm_gprSpec.leaArith_zero32 rfl hds hb hi hrd
        (fun r hr => gprHolds_vllToMach (hvb r hr)) (gprHolds_vllToMach hvi)
  loadZextIdx_spec := by
    intro h k t rd base idx sc disp c clob v vb vi s post hhk hrd hb hi hvb hvi hval
    obtain ⟨ds, hds, rfl⟩ := wrapArmNative_eq_some hhk
    obtain ⟨hp, hlen⟩ := armLoadZextIdx_pure_len hds
    exact armFallsTo_to_vllNative hp hlen fun host postH =>
      arm_gprSpec.loadZextIdx_spec hds hrd hb hi
        (gprHolds_vllToMach hvb) (gprHolds_vllToMach hvi) hval
  loadZextIdx_zero32 := by
    intro _ h k rd base idx sc disp c clob v vb vi s post hhk hrd hb hi hvb hvi hval
    obtain ⟨ds, hds, rfl⟩ := wrapArmNative_eq_some hhk
    obtain ⟨hp, hlen⟩ := armLoadZextIdx_pure_len hds
    exact armFallsTo_to_vllNative hp hlen fun host postH =>
      arm_gprSpec.loadZextIdx_zero32 rfl hds hrd hb hi
        (gprHolds_vllToMach hvb) (gprHolds_vllToMach hvi) hval
  loadZextIdx_zext := by
    intro _ h k t rd base idx sc disp c clob v vb vi s post hhk hrd hb hi hvb hvi hval
    obtain ⟨ds, hds, rfl⟩ := wrapArmNative_eq_some hhk
    obtain ⟨hp, hlen⟩ := armLoadZextIdx_pure_len hds
    exact armFallsTo_to_vllNative hp hlen fun host postH =>
      arm_gprSpec.loadZextIdx_zext rfl hds hrd hb hi
        (gprHolds_vllToMach hvb) (gprHolds_vllToMach hvi) hval
  loadSextZextIdx_spec := by
    intro h k m n rd base idx sc disp c clob v vb vi s post hhk hrd hb hi hvb hvi hval
    obtain ⟨ds, hds, rfl⟩ := wrapArmNative_eq_some hhk
    obtain ⟨hp, hlen⟩ := armLoadSextZextIdx_pure_len hds
    exact armFallsTo_to_vllNative hp hlen fun host postH =>
      arm_gprSpec.loadSextZextIdx_spec hds hrd hb hi
        (gprHolds_vllToMach hvb) (gprHolds_vllToMach hvi) hval
  storeZextIdx_spec := by
    intro h k t pa base idx sc disp c clob v vb vi s post hhk hpa hb hi hhh hvb hvi hok
    obtain ⟨ds, hds, rfl⟩ := wrapArmNative_eq_some hhk
    obtain ⟨hp, hlen⟩ := armStoreZextIdx_pure_len hds
    exact armFallsTo_to_vllNative hp hlen fun host postH =>
      arm_gprSpec.storeZextIdx_spec hds hpa hb hi (vllPArg_to_arm hhh)
        (gprHolds_vllToMach hvb) (gprHolds_vllToMach hvi) hok
  leaArithZext_spec := by
    intro h k base? idx shift disp rd c clob vb vi s post hhk hb hi hrd hvb hvi
    obtain ⟨ds, hds, rfl⟩ := wrapArmNative_eq_some hhk
    obtain ⟨hp, hlen⟩ := armLeaArithZext_pure_len hds
    exact armFallsTo_to_vllNative hp hlen fun host postH =>
      arm_gprSpec.leaArithZext_spec hds hb hi hrd
        (fun r hr => gprHolds_vllToMach (hvb r hr)) (gprHolds_vllToMach hvi)
  saveRegs_spec := by
    intro fn h k i rs s G post hfn hbd hns hsp hm
    cases hfn; exact vllArmSaveRegs_spec rs i hbd hns hsp hm
  restoreRegs_spec := by
    intro fn h k i rs s₀ s G post hfn hnd hcs hsp hm
    cases hfn; exact vllArmRestoreRegs_spec rs i hnd hcs hsp hm
  op_boolFlag_spec := by
    intro h k sig code pas pd cnd vh c clob vs P s post hfl hop _ _ hvs hwp
    dsimp only [vllGprIsaOfHooks, vllArmNativeHooks] at hfl hop
    cases pd with
    | vec v => exact v.elim
    | flag _ => cases hfl
    | gpr r => cases r with
      | SP => cases hfl
      | reg d =>
        cases code with
        | copy =>
          rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
          rcases hvs with _ | ⟨hpa, hnil⟩; cases hnil
          cases pa with
          | vec v => exact v.elim
          | gpr _ | imm _ => cases hfl
          | flag cf =>
            cases hfl
            dsimp only [vllArmOpHook, vllCoreOp, vllCoreCopy] at hop
            rcases Option.some.inj hop with ⟨rfl, rfl⟩
            exact vllArm_setcc_boolFlag_spec hpa hwp
        | not =>
          rcases pas with ⟨pa, ⟨⟩⟩; rcases vs with ⟨va, ⟨⟩⟩
          rcases hvs with _ | ⟨hpa, hnil⟩; cases hnil
          cases pa with
          | vec v => exact v.elim
          | gpr _ | imm _ => cases hfl
          | flag cf =>
            cases hfl
            dsimp only [vllArmOpHook] at hop
            rcases Option.some.inj hop with ⟨rfl, rfl⟩
            dsimp only [OpCode.wp, lift1] at hwp
            have hpa' : cf.interp s.flags = va := hpa
            exact vllArm_setcc_boolFlag_spec (by rw [armNegCond_interp, hpa']) hwp
        | _ => cases hfl
  op_cmpFlags_spec := by
    intro h k co w pa pb pd lhsFirst vh c clob va vb s post hfl hop ha hd hpa hpb
    dsimp only [vllGprIsaOfHooks, vllArmNativeHooks] at hfl hop ⊢
    have hfb_ne : wrapArmNative (armOp (.cmp co (.bits w) .bool rfl)
        (pa, pb, ()) (pd, ()) vh) ≠ none := by
      intro h0; have hs := armCmpOp_isSome_of_flagsOut (vh := vh) hfl
      cases harm : armOp (.cmp co (.bits w) .bool rfl) (pa, pb, ()) (pd, ()) vh <;>
        simp [wrapArmNative, harm] at h0 hs
    have hCoreLf : ∀ {ra : XReg} {x : PArg Arm64.Reg Empty ArmCond (.bits w)},
        armCmpFlagsOut co w (.gpr (.reg ra)) x pd = some lhsFirst → lhsFirst = true := by
      intro ra x hfx
      dsimp only [armCmpFlagsOut] at hfx
      split at hfx; · cases hfx
      split at hfx; · cases hfx
      simp only [Option.bind_eq_some_iff] at hfx
      rcases hfx with ⟨lf', hlf', hok⟩
      have hl : lf' = lhsFirst := by
        cases pd with
        | vec v => exact v.elim
        | gpr r => cases r with | SP => cases hok | reg _ => exact Option.some.inj hok
        | flag cf =>
          cases heq : (cf == armCmpCond (if lf' then co else co.swap)) <;>
            simp only [heq, Bool.false_eq_true, ↓reduceIte] at hok <;>
            first | exact Option.some.inj hok | cases hok
      subst hl
      cases x with
      | vec v => exact v.elim
      | imm cb => dsimp only at hlf'; split at hlf' <;> cases hlf'; rfl
      | gpr r2 => cases r2 with | SP => cases hlf' | reg _ => exact (Option.some.inj hlf').symm
    cases hhk : vllArmOpHook (.cmp co (.bits w) .bool rfl) (pa, pb, ()) (pd, ()) vh with
    | none =>
      exfalso; dsimp only [vllArmOpHook] at hhk
      cases pa with
      | vec v => exact v.elim
      | imm ca => exact hfb_ne hhk
      | gpr r1 => cases r1 with
        | SP => exact hfb_ne hhk
        | reg ra => cases pb with
          | vec v => exact v.elim
          | gpr r2 => cases r2 with
            | SP => exact hfb_ne hhk
            | reg rb =>
              dsimp only at hhk
              by_cases hn : (w == 32 || w == 64) = true <;>
                simp only [hn, Bool.false_eq_true, ↓reduceIte] at hhk
              · dsimp only [vllArmCmpCore] at hhk
                cases pd with
                | vec v => exact v.elim
                | gpr r => cases r with | SP => simp [armCmpFlagsOut] at hfl | reg _ => cases hhk
                | flag cf =>
                  dsimp only [armCmpFlagsOut] at hfl
                  split at hfl; · cases hfl
                  split at hfl; · cases hfl
                  simp only [Option.bind_eq_some_iff] at hfl
                  rcases hfl with ⟨lf', hlf', hok⟩
                  cases hlf'
                  simp only [↓reduceIte] at hok
                  split at hok
                  · rename_i hcf; simp only [hcf, ↓reduceIte] at hhk; cases hhk
                  · cases hok
              · exact hfb_ne hhk
          | imm cb =>
            dsimp only at hhk
            by_cases hcond : ((w == 32 || w == 64) &&
                (cb != 0#w || (armZeroCmpIns? co w ra pd).isNone) &&
                ((armImm12? cb).isSome || cb == 0#w || (armImm12? (-cb)).isNone)) = true <;>
              simp only [hcond, Bool.false_eq_true, ↓reduceIte] at hhk
            · dsimp only [vllArmCmpCore] at hhk
              cases pd with
              | vec v => exact v.elim
              | gpr r => cases r with | SP => simp [armCmpFlagsOut] at hfl | reg _ => cases hhk
              | flag cf =>
                dsimp only [armCmpFlagsOut] at hfl
                split at hfl; · cases hfl
                split at hfl; · cases hfl
                simp only [Option.bind_eq_some_iff] at hfl
                rcases hfl with ⟨lf', hlf', hok⟩
                split at hlf'
                · cases hlf'
                · cases hlf'
                  simp only [↓reduceIte] at hok
                  split at hok
                  · rename_i hcf; simp only [hcf, ↓reduceIte] at hhk; cases hhk
                  · cases hok
            · exact hfb_ne hhk
    | some res =>
      rw [hhk] at hop; cases hop
      dsimp only [vllArmOpHook] at hhk
      cases pa with
      | vec v => exact v.elim
      | imm ca => exact vllArm_cmpNative_flags_spec rfl hfl hhk ha hd hpa hpb
      | gpr r1 => cases r1 with
        | SP => exact vllArm_cmpNative_flags_spec rfl hfl hhk ha hd hpa hpb
        | reg ra => cases pb with
          | vec v => exact v.elim
          | gpr r2 => cases r2 with
            | SP => exact vllArm_cmpNative_flags_spec rfl hfl hhk ha hd hpa hpb
            | reg rb =>
              dsimp only at hhk
              by_cases hn : (w == 32 || w == 64) = true
              · simp only [hn, ↓reduceIte] at hhk
                have hn' : w = 32 ∨ w = 64 := by
                  simp only [Bool.or_eq_true, beq_iff_eq] at hn; exact hn
                obtain rfl : lhsFirst = true := hCoreLf hfl
                rcases hn' with rfl | rfl
                · exact vllArm_cmpCore_flags_spec rfl hhk hpa.2 hpb.2
                · exact vllArm_cmpCore_flags_spec rfl hhk hpa.2 hpb.2
              · simp only [hn, Bool.false_eq_true, ↓reduceIte] at hhk
                exact vllArm_cmpNative_flags_spec rfl hfl hhk ha hd hpa hpb
          | imm cb =>
            dsimp only at hhk
            by_cases hcond : ((w == 32 || w == 64) &&
                (cb != 0#w || (armZeroCmpIns? co w ra pd).isNone) &&
                ((armImm12? cb).isSome || cb == 0#w || (armImm12? (-cb)).isNone)) = true
            · simp only [hcond, ↓reduceIte] at hhk
              have hn' : w = 32 ∨ w = 64 := by
                simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hcond; exact hcond.1.1
              obtain rfl : lhsFirst = true := hCoreLf hfl
              have hcb : cb = vb := hpb
              rcases hn' with rfl | rfl
              · exact vllArm_cmpCore_flags_spec rfl hhk hpa.2
                  (by dsimp only [Src.evalW, Src.eval, Width.bits]; rw [hcb]
                      exact (BitVec.setWidth_setWidth_of_le vb (by decide)).trans
                        (BitVec.setWidth_eq vb))
              · exact vllArm_cmpCore_flags_spec rfl hhk hpa.2
                  (by dsimp only [Src.evalW, Src.eval, Width.bits]; rw [hcb]
                      exact (BitVec.setWidth_setWidth_of_le vb (by decide)).trans
                        (BitVec.setWidth_eq vb))
            · simp only [hcond, Bool.false_eq_true, ↓reduceIte] at hhk
              exact vllArm_cmpNative_flags_spec rfl hfl hhk ha hd hpa hpb
  testOp_boolFlag_spec := fun _ {_ _ _ _ _ _ _ _ _ _ _ _ _ _} hcl hcc hto ha hd hpa hpb =>
    vllArm_testOp_boolFlag_spec hcl hcc hto ha hd hpa hpb
  testMem_boolFlag_spec := by
    intros; simp only [vllArmNativeHooks] at *; contradiction
  vecSpec := vllEmptyVecTarget arm64Arch Empty.elim

/-- Verified AArch64 `VllPolicy arm64Arch`. -/
@[expose] def vllArmPolicy : VllPolicy arm64Arch :=
  ⟨vllArmNativeHooks, vllArmPolicySpec⟩

/-- Verified `BedrockMach` L1 AArch64 `Target` (`vllTarget arm64Arch arm64Arch_wf vllArmPolicy`). -/
@[expose] def vllArmTarget : Target :=
  vllTarget arm64Arch arm64Arch_wf vllArmPolicy

/-- Strict domain-matched `GprIsa` restricting `op`/`load`/`store` to the exact domain accepted by
`armGpr`, guaranteeing unconditional 1:1 `asmArm64List` parity with `armTarget` across all inputs.
-/
@[expose] def vllArmStrictGpr : GprIsa Arm64.Reg Empty ArmCond (Instr arm64Arch) :=
  let base := vllGprIsaOfHooks arm64Arch vllArmNativeHooks
  { base with
    op := fun code pas dsts vh =>
      if (armGpr.op code pas dsts vh).isSome then base.op code pas dsts vh else none
    load := fun t rd a =>
      if (armGpr.load t rd a).isSome then base.load t rd a else none
    store := fun t pa a =>
      if (armGpr.store t pa a).isSome then base.store t pa a else none }

/-- Strict domain-matched `Isa` over `Instr arm64Arch`. -/
@[expose, reducible] def vllArmStrictIsa : Isa where
  Reg := Arm64.Reg
  VReg := Empty
  Cond := ArmCond
  Directive := Instr arm64Arch
  gpr := vllArmStrictGpr
  vec := vllEmptyVecIsa arm64Arch Empty.elim
  frame := vllFrameIsaOfHooks arm64Arch vllArmNativeHooks
  supportsAddrDisp := armSupportsAddrDisp
  supportsAddrIdx := armSupportsAddrIdx
  supportsTestFuse := true
  supportsAddrZextIdx := armSupportsAddrIdx

/-- Verified `GprTarget` instance for `vllArmStrictGpr`. -/
theorem vllArmStrictGprTarget :
    GprTarget (vllMach arm64Arch) vllArmStrictGpr armScratch := by
  have base := vllArmTarget.gprSpec
  refine
    { negCond_reads := base.negCond_reads, negCond_eval := base.negCond_eval
      clearFlags_spec := base.clearFlags_spec
      mov_spec := base.mov_spec, movi_spec := base.movi_spec
      setcc_spec := base.setcc_spec, jmp_spec := base.jmp_spec, jcc_spec := base.jcc_spec
      jnzGpr_spec := base.jnzGpr_spec, jnzGprInv_spec := base.jnzGprInv_spec
      op_spec := fun hop => by
        dsimp only [vllArmStrictGpr] at hop
        split at hop <;> first | exact base.op_spec hop | cases hop
      load_spec := fun hld => by
        dsimp only [vllArmStrictGpr] at hld
        split at hld <;> first | exact base.load_spec hld | cases hld
      store_spec := fun hst => by
        dsimp only [vllArmStrictGpr] at hst
        split at hst <;> first | exact base.store_spec hst | cases hst
      load_zero32 := fun hz {_ _ _ _ _ _ _ _ _} hld => by
        dsimp only [vllArmStrictGpr] at hld
        split at hld <;> first | exact base.load_zero32 hz hld | cases hld
      load_zext := fun hz {_ _ _ _ _ _ _ _ _ _} hld => by
        dsimp only [vllArmStrictGpr] at hld
        split at hld <;> first | exact base.load_zext hz hld | cases hld
      op_zero32 := fun hz hop => by
        dsimp only [vllArmStrictGpr] at hop
        split at hop <;> first | exact base.op_zero32 hz hop | cases hop
      op_boolFlag_spec := fun hfl hop => by
        dsimp only [vllArmStrictGpr] at hop
        split at hop <;> first | exact base.op_boolFlag_spec hfl hop | cases hop
      op_cmpFlags_spec := fun hfl hop => by
        dsimp only [vllArmStrictGpr] at hop
        split at hop <;> first | exact base.op_cmpFlags_spec hfl hop | cases hop
      testOp_spec := base.testOp_spec, testOp_boolFlag_spec := base.testOp_boolFlag_spec
      testMem_boolFlag_spec := base.testMem_boolFlag_spec
      loadSext_spec := base.loadSext_spec, cmpZeroJcc_spec := base.cmpZeroJcc_spec
      testJcc_spec := base.testJcc_spec, leaArith_spec := base.leaArith_spec
      leaArith_zero32 := base.leaArith_zero32, loadZextIdx_spec := base.loadZextIdx_spec
      loadZextIdx_zero32 := base.loadZextIdx_zero32, loadZextIdx_zext := base.loadZextIdx_zext
      loadSextZextIdx_spec := base.loadSextZextIdx_spec, storeZextIdx_spec := base.storeZextIdx_spec
      leaArithZext_spec := base.leaArithZext_spec }

/-- Verified strict domain-matched `Target` over `BedrockMach` L1 (`Instr arm64Arch`). -/
@[expose, reducible] def vllArmStrictTarget : Target where
  toIsa := vllArmStrictIsa
  mach := vllMach arm64Arch
  gprSpec := vllArmStrictGprTarget
  frameSpec := vllArmTarget.frameSpec
  vecSpec := vllArmTarget.vecSpec

private theorem vllArmCmpCore_noLab {o : CmpOp} {w : Width} {ra : XReg} {rhs : Src arm64Arch}
    {dst : PDst Arm64.Reg Empty ArmCond .bool} {c : List (Instr arm64Arch)} {cl : FlagMask}
    (h : vllArmCmpCore o w ra rhs dst = some (c, cl)) : NoVllLab c := by
  cases dst with
  | vec v => exact v.elim
  | flag _ =>
    dsimp only [vllArmCmpCore] at h; split at h
    · cases h; exact noVllLab_one (fun _ e => by cases e)
    · cases h
  | gpr r => cases r with | SP => cases h | reg _ =>
    cases h; exact noVllLab_two (fun _ e => by cases e) (fun _ e => by cases e)

private theorem vllArmOpHook_noLab {sig rs : List Ty} {code : OpCode sig rs}
    {pas : Tup (PArg Arm64.Reg Empty ArmCond) sig}
    {dsts : Tup (PDst Arm64.Reg Empty ArmCond) rs} {vh : VariantHint}
    {c : List (Instr arm64Arch)} {cl : FlagMask}
    (h : vllArmOpHook code pas dsts vh = some (c, cl)) : NoVllLab c := by
  have h1 : ∀ {i : Instr arm64Arch} {f : FlagMask},
      some ([i], f) = some (c, cl) → (∀ l, i ≠ .label l) → NoVllLab c := fun e hne => by
    cases e; exact noVllLab_one hne
  cases code with
  | copy _ | bitcast _ _ _ | zext _ _ | trunc _ _ | ofBool _ | not _ | neg _
  | add _ | sub _ | mul _ | and _ | or _ | xor _ | shl _ | lshr _ | ashr _ | cmp _ _ _ _ =>
    dsimp only [vllArmOpHook] at h
    split at h <;> first
      | exact h1 h (fun _ e => by cases e)
      | exact wrapArmNative_noLab h
      | exact vllArmCmpCore_noLab h
      | cases h
      | (split at h <;> first
          | exact h1 h (fun _ e => by cases e)
          | exact wrapArmNative_noLab h
          | exact vllArmCmpCore_noLab h
          | cases h
          | (split at h <;> first
              | exact h1 h (fun _ e => by cases e)
              | exact wrapArmNative_noLab h
              | cases h
              | (split at h <;> first
                  | exact h1 h (fun _ e => by cases e)
                  | (split at h <;> first
                      | exact h1 h (fun _ e => by cases e)
                      | exact wrapArmNative_noLab h))))
  | _ => dsimp only [vllArmOpHook] at h; exact wrapArmNative_noLab h

/-- Structural label-freedom for `vllArmNativeHooks`. -/
theorem vllArmHooksNoLab : VllHooksNoLab arm64Arch vllArmNativeHooks where
  jnzGpr := fun h => by cases h; exact insPure_map_native_noLab
  jnzGprInv := fun h => by cases h; exact insPure_map_native_noLab
  opHook := fun h => vllArmOpHook_noLab h
  storeHook := fun {t pa a c cl} h => by
    dsimp only [vllArmNativeHooks, vllArmStoreHook] at h
    split at h <;> first | cases h | exact wrapArmNative_noLab h
  testOp := fun h => wrapArmNative_noLab h
  loadSext := fun {m n rd a c cl} h => by
    dsimp only [vllArmNativeHooks, vllArmLoadSext] at h
    split at h
    · cases h
    · split at h <;> first
        | cases h
        | (split at h <;> first | (cases h; exact noVllLab_one (fun _ e => by cases e)) | cases h)
  cmpZeroJcc := fun h => wrapArmNative_noLab h
  testJcc := fun h => wrapArmNative_noLab h
  leaArith := fun h => wrapArmNative_noLab h
  loadZextIdx := fun h => wrapArmNative_noLab h
  loadSextZextIdx := fun h => wrapArmNative_noLab h
  storeZextIdx := fun h => wrapArmNative_noLab h
  leaArithZext := fun h => wrapArmNative_noLab h
  saveRegs := fun h => by cases h; exact vllArmSaveRegs_noLab _ _
  restoreRegs := fun h => by cases h; exact vllArmRestoreRegs_noLab _ _
  vmov := fun _ v _ => v.elim
  vmovi := fun _ v _ _ _ => v.elim
  vslotSt := fun _ _ v => v.elim
  vslotLd := fun _ v _ => v.elim
  vop := fun _ _ _ _ _ _ h => nomatch h
  vload := fun _ v _ _ _ _ => v.elim
  vstore := fun _ v _ _ _ _ => v.elim

theorem vllArmLabelClean : Rega.LabelClean vllArmTarget.toIsa :=
  vllLabelClean arm64Arch vllArmPolicy vllArmHooksNoLab

theorem vllArmStrictLabelClean : Rega.LabelClean vllArmStrictTarget.toIsa := by
  have b := vllArmLabelClean
  exact
    { b with
      op := fun code pas dsts vh c cl h => by
        dsimp only [vllArmStrictTarget, vllArmStrictIsa, vllArmStrictGpr] at h
        split at h <;> first | exact b.op code pas dsts vh c cl h | cases h
      load := fun t r a c cl h => by
        dsimp only [vllArmStrictTarget, vllArmStrictIsa, vllArmStrictGpr] at h
        split at h <;> first | exact b.load t r a c cl h | cases h
      store := fun t pa a c cl h => by
        dsimp only [vllArmStrictTarget, vllArmStrictIsa, vllArmStrictGpr] at h
        split at h <;> first | exact b.store t pa a c cl h | cases h }

end LeanQbe.T.Arm64
