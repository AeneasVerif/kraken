module

public import LeanQbe.T.Amd64.Isel
public import LeanQbe.T.Amd64.Frame
public import LeanQbe.T.Legal
public import LeanQbe.T.MainLemmas
import LeanQbe.T.RegaLemmas
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.Amd64.IselLemmas5
import LeanQbe.T.Amd64.FrameLemmas
import all Kraken.Mem
import all Kraken.Separation

/-!
# Scalar-Only SysV x64 `Target` Firewall (`x64ScalarTarget`)

Assembles a strictly scalar, AVX/SIMD-free SysV x64 target (`x64ScalarIsa`, `x64ScalarTarget`,
`x64ScalarLegalTarget`, `x64ScalarLayout`, `x64ScalarLabelClean`, `x64ScalarInit`) reusing the
verified scalar `Amd64/Isel`, `Amd64/Frame`, `Amd64/IselLemmas1..5`, and `Amd64/FrameLemmas`
with `VecIsa.empty` / `VecTarget.empty` and **zero `IselVec` / `IselVecLemmas*` imports**.

Uses `public section` (no blanket `@[expose]`) with private-import firewall theorems
(`x64Scalar_gprSpec`, `x64Scalar_frameSpec`) so downstream bootstrap modules remain
incrementality-clean and free of SIMD/proof-term leakage.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Amd64

open Std Std.ExtHashMap
open LeanQbe.T

/-! ## 1. Empty-`VReg` Adapter (`x64ScalarGpr`, `x64ScalarMach`, `x64ScalarIsa`) -/

/-- Lift a scalar `PArg` (`VReg := Empty`) into `PArg Reg64 RegMm CondCode`. -/
@[expose] def liftScalarPArg {t : Ty} :
    PArg Reg64 Empty CondCode t → PArg Reg64 RegMm CondCode t
  | .gpr r => .gpr r
  | .vec v => v.elim
  | .flag cc => .flag cc
  | .imm k => .imm k

/-- Lift a tuple of scalar `PArg`s (`VReg := Empty`) into `Tup (PArg Reg64 RegMm CondCode)`. -/
@[expose] def liftScalarPArgs :
    {ts : List Ty} → Tup (PArg Reg64 Empty CondCode) ts → Tup (PArg Reg64 RegMm CondCode) ts
  | [], () => ()
  | _ :: _, (a, as) => (liftScalarPArg a, liftScalarPArgs as)

/-- Lift a scalar `PDst` (`VReg := Empty`) into `PDst Reg64 RegMm CondCode`. -/
@[expose] def liftScalarPDst {t : Ty} :
    PDst Reg64 Empty CondCode t → PDst Reg64 RegMm CondCode t
  | .gpr r => .gpr r
  | .vec v => v.elim
  | .flag cc => .flag cc

/-- Lift a tuple of scalar `PDst`s (`VReg := Empty`) into `Tup (PDst Reg64 RegMm CondCode)`. -/
@[expose] def liftScalarPDsts :
    {ts : List Ty} → Tup (PDst Reg64 Empty CondCode) ts → Tup (PDst Reg64 RegMm CondCode) ts
  | [], () => ()
  | _ :: _, (d, ds) => (liftScalarPDst d, liftScalarPDsts ds)

/-- Scalar-only `GprIsa` wrapping `x64Gpr` with `VReg := Empty`. -/
@[expose] def x64ScalarGpr : GprIsa Reg64 Empty CondCode Directive where
  condReads := x64Gpr.condReads
  negCond := x64Gpr.negCond
  zeroFlags := x64Gpr.zeroFlags
  clearFlags := x64Gpr.clearFlags
  mov := x64Gpr.mov
  movi := x64Gpr.movi
  setcc := x64Gpr.setcc
  jmp := x64Gpr.jmp
  jcc := x64Gpr.jcc
  jnzGpr := x64Gpr.jnzGpr
  op code pas dsts vh := x64Gpr.op code (liftScalarPArgs pas) (liftScalarPDsts dsts) vh
  load := x64Gpr.load
  store t pa a := x64Gpr.store t (liftScalarPArg pa) a
  supportsScalarOp := x64Gpr.supportsScalarOp
  cmpFlags := x64Gpr.cmpFlags

/-- Scalar-only `Machine` matching `x64Mach` with `VReg := Empty`. -/
@[expose, reducible] def x64ScalarMach : Machine Reg64 Empty CondCode Directive where
  MData := MachineData
  Addr := Int64
  State := MachineState
  Host := Host
  getGpr s r := s.regs.get64 r
  getVec _ vr := vr.elim
  evalCond s cc := cc.interp s.status
  mem s := s.dmem
  mkState s a := ⟨s, a⟩
  pc st := st.pc
  data st := st.data
  pc_mk _ _ := rfl
  data_mk _ _ := rfl
  mk_eta _ := rfl
  prog h := @Host.prog h
  addrOf h k := @Host.addrOf h k
  labelAddr := hostLabel
  step := hostStep

/-- True iff scalar `x64Load`/`x64Store` encodes `[base + disp]` in one displacement operand. -/
@[expose] def x64ScalarSupportsAddrDisp (t : Ty) (d : BitVec 64) : Bool :=
  let okTy := match t with
    | .bool => true
    | .bits n => x64BitWidths.contains n
    | .pair _ _ => false
    | .float _ => false
  okTy && fitsImm32 d

/-- Scalar-only SysV x64 `Isa` (`VReg := Empty`, `vec := VecIsa.empty`). -/
@[expose, reducible] def x64ScalarIsa : Isa where
  Reg := Reg64
  VReg := Empty
  Cond := CondCode
  Directive := Directive
  gpr := x64ScalarGpr
  vec := VecIsa.empty Reg64 CondCode Directive
  frame := x64Frame
  supportsAddrDisp := x64ScalarSupportsAddrDisp

/-- Scalar-only SysV x64 `LegalTarget` (`[8, 16, 32, 64]` scalar bits, no vectors or floats). -/
@[expose] def x64ScalarLegalTarget : LegalTarget where
  oracle := .none
  allowPackBridge := false
  bitWidths := [8, 16, 32, 64]
  floatFmts := []
  vecIntOpSupported _ _ _ := false
  vecFloatOpSupported _ _ := false

theorem x64ScalarLegalTarget_valid : x64ScalarLegalTarget.valid = true := by
  decide

/-! ## 2. Private-Import Firewall Theorems (`x64Scalar_gprSpec`, `x64Scalar_frameSpec`) -/

private theorem frame_scalar_of_x64 {s s' : MachineData} {gClob : List Reg64}
    {fClob : FlagMask} (h : x64Mach.Frame x64CondReads s s' gClob [] fClob) :
    x64ScalarMach.Frame x64CondReads s s' gClob [] fClob :=
  ⟨h.1, fun v _ => v.elim, h.2.2⟩

private theorem fallsTo_scalar_of_x64 {h : Host} {k : Nat} {c : List Directive}
    {gClob : List Reg64} {fClob : FlagMask} {s : MachineData}
    {Q : MachineData → Prop} {post : MachineState → Prop}
    (hft : x64Mach.FallsTo x64CondReads h k c gClob [] fClob s Q post) :
    x64ScalarMach.FallsTo x64CondReads h k c gClob [] fClob s Q post :=
  fun hc hk => hft hc fun s' hq hfr => hk s' hq (frame_scalar_of_x64 hfr)

private theorem liftScalarPArg_gprs {t : Ty} (pa : PArg Reg64 Empty CondCode t) :
    (liftScalarPArg pa).gprs = pa.gprs := by
  cases pa with
  | vec v => exact v.elim
  | gpr _ | flag _ | imm _ => rfl

private theorem liftScalarPArgs_gprs :
    {ts : List Ty} → (pas : Tup (PArg Reg64 Empty CondCode) ts) →
      tupArgGprs (liftScalarPArgs pas) = tupArgGprs pas
  | [], () => rfl
  | _ :: _, (a, as) => by
    simp only [liftScalarPArgs, tupArgGprs_cons, liftScalarPArg_gprs, liftScalarPArgs_gprs as]

private theorem liftScalarPDst_gprs {t : Ty} (pd : PDst Reg64 Empty CondCode t) :
    (liftScalarPDst pd).gprs = pd.gprs := by
  cases pd with
  | vec v => exact v.elim
  | gpr _ | flag _ => rfl

private theorem liftScalarPDsts_gprs :
    {ts : List Ty} → (dsts : Tup (PDst Reg64 Empty CondCode) ts) →
      tupDstGprs (liftScalarPDsts dsts) = tupDstGprs dsts
  | [], () => rfl
  | _ :: _, (d, ds) => by
    simp only [liftScalarPDsts, tupDstGprs_cons, liftScalarPDst_gprs, liftScalarPDsts_gprs ds]

private theorem pargHolds_liftScalar {s : MachineData} {t : Ty}
    {pa : PArg Reg64 Empty CondCode t} {v : Val t} :
    x64ScalarMach.PArgHolds s t pa v ↔ x64Mach.PArgHolds s t (liftScalarPArg pa) v := by
  cases pa with
  | vec vr => exact vr.elim
  | gpr _ | flag _ | imm _ => exact Iff.rfl

private theorem pdstHolds_liftScalar {s : MachineData} {t : Ty}
    {pd : PDst Reg64 Empty CondCode t} {v : Val t} :
    x64ScalarMach.PDstHolds s t pd v ↔ x64Mach.PDstHolds s t (liftScalarPDst pd) v := by
  cases pd with
  | vec vr => exact vr.elim
  | gpr _ | flag _ => exact Iff.rfl

private theorem trel_liftScalarPArg {s : MachineData} :
    {ts : List Ty} → {pas : Tup (PArg Reg64 Empty CondCode) ts} → {vs : Tup Val ts} →
      TRel (x64ScalarMach.PArgHolds s) pas vs →
      TRel (x64Mach.PArgHolds s) (liftScalarPArgs pas) vs
  | [], (), (), .nil => .nil
  | _ :: _, (_, _), (_, _), .cons h1 h2 =>
    .cons (pargHolds_liftScalar.mp h1) (trel_liftScalarPArg h2)

private theorem trel_liftScalarPDst {s : MachineData} :
    {ts : List Ty} → {dsts : Tup (PDst Reg64 Empty CondCode) ts} → {vs : Tup Val ts} →
      TRel (x64Mach.PDstHolds s) (liftScalarPDsts dsts) vs →
      TRel (x64ScalarMach.PDstHolds s) dsts vs
  | [], (), (), .nil => .nil
  | _ :: _, (_, _), (_, _), .cons h1 h2 =>
    .cons (pdstHolds_liftScalar.mpr h1) (trel_liftScalarPDst h2)

/-- Private-import firewall theorem exporting `GprTarget` for `x64ScalarGpr` over
`x64ScalarMach` without leaking `Amd64.IselLemmas1..5`. -/
theorem x64Scalar_gprSpec : GprTarget x64ScalarMach x64ScalarGpr x64Scratch where
  negCond_reads := x64GprSpec.negCond_reads
  negCond_eval := x64GprSpec.negCond_eval
  clearFlags_spec := fallsTo_scalar_of_x64 x64GprSpec.clearFlags_spec
  mov_spec := fallsTo_scalar_of_x64 x64GprSpec.mov_spec
  movi_spec := fallsTo_scalar_of_x64 x64GprSpec.movi_spec
  setcc_spec hr := fallsTo_scalar_of_x64 (x64GprSpec.setcc_spec hr)
  jmp_spec hc ha hk :=
    x64GprSpec.jmp_spec hc ha fun s' hfr hm => hk s' (frame_scalar_of_x64 hfr) hm
  jcc_spec hc ha hk :=
    x64GprSpec.jcc_spec hc ha fun s' hfr hm => hk s' (frame_scalar_of_x64 hfr) hm
  jnzGpr_spec hc ha hr hb hk :=
    x64GprSpec.jnzGpr_spec hc ha hr hb fun s' hfr hm => hk s' (frame_scalar_of_x64 hfr) hm
  op_spec := @fun h k sig rs code pas dsts vh c clob vs P s post
      hop hargs hdst hvs hwp => by
    have hargs' : ∀ r ∈ tupArgGprs (liftScalarPArgs pas), r ∉ x64Scratch := by
      rw [liftScalarPArgs_gprs]; exact hargs
    have hdst' : ∀ r ∈ tupDstGprs (liftScalarPDsts dsts), r ∉ x64Scratch := by
      rw [liftScalarPDsts_gprs]; exact hdst
    have hft := x64GprSpec.op_spec (h := h) (k := k) (post := post)
      hop hargs' hdst' (trel_liftScalarPArg hvs) hwp
    rw [liftScalarPDsts_gprs] at hft
    refine fallsTo_scalar_of_x64 (Machine.FallsTo.conseq hft fun s' h _ => ?_)
    obtain ⟨⟨rvs, hp, hpd⟩, hm⟩ := h
    exact ⟨⟨rvs, hp, trel_liftScalarPDst hpd⟩, hm⟩
  load_spec hld hrd ha hv := fallsTo_scalar_of_x64 (x64GprSpec.load_spec hld hrd ha hv)
  store_spec := @fun h k t pa a c clob v s post hst hargs hva hok =>
    fallsTo_scalar_of_x64 (x64GprSpec.store_spec hst
      (by rw [liftScalarPArg_gprs]; exact hargs) (pargHolds_liftScalar.mp hva) hok)

/-- Frame predicates for `x64ScalarMach`, reusing `x64FramePreds` verbatim. -/
@[expose, reducible] def x64ScalarFramePreds : FramePreds x64ScalarMach where
  RetAddr := x64FramePreds.RetAddr
  raReg := x64FramePreds.raReg
  spEntry := x64FramePreds.spEntry
  spOk := x64FramePreds.spOk
  Saved := x64FramePreds.Saved

/-- Private-import firewall theorem exporting `FrameSpec` over `x64ScalarFramePreds` without
leaking `Amd64.FrameLemmas`. -/
theorem x64Scalar_frameSpec :
    FrameSpec x64ScalarMach x64Frame x64CondReads x64ScalarFramePreds where
  sp_disj := x64FrameSpec.spec.sp_disj
  scratch_disj := x64FrameSpec.spec.scratch_disj
  cs_disj := x64FrameSpec.spec.cs_disj
  ra_disj := x64FrameSpec.spec.ra_disj
  argRegs_nodup := x64FrameSpec.spec.argRegs_nodup
  retRegs_nodup := x64FrameSpec.spec.retRegs_nodup
  retAddr_region := x64FrameSpec.spec.retAddr_region
  raReg_of_raRegs := x64FrameSpec.spec.raReg_of_raRegs
  slots_le_frameSize := x64FrameSpec.spec.slots_le_frameSize
  spOk_frame := x64FrameSpec.spec.spOk_frame
  spEntry_call := x64FrameSpec.spec.spEntry_call
  labelAddr_eq := x64FrameSpec.spec.labelAddr_eq
  label_spec := x64FrameSpec.spec.label_spec
  prologue_spec h1 h2 h3 h4 := fallsTo_scalar_of_x64 (x64FrameSpec.spec.prologue_spec h1 h2 h3 h4)
  epilogue_spec h1 h2 h3 := fallsTo_scalar_of_x64 (x64FrameSpec.spec.epilogue_spec h1 h2 h3)
  slotSt_spec h1 h2 h3 := fallsTo_scalar_of_x64 (x64FrameSpec.spec.slotSt_spec h1 h2 h3)
  slotLd_spec h1 h2 h3 := fallsTo_scalar_of_x64 (x64FrameSpec.spec.slotLd_spec h1 h2 h3)
  canonAbi_spec h1 h2 h3 := fallsTo_scalar_of_x64 (x64FrameSpec.spec.canonAbi_spec h1 h2 h3)
  call_spec hc hmem hk :=
    x64FrameSpec.spec.call_spec hc hmem fun s' hsp hfr hra hm' =>
      hk s' hsp (frame_scalar_of_x64 hfr) hra hm'
  exitJmp_spec hc hk :=
    x64FrameSpec.spec.exitJmp_spec hc fun s' hfr hm' =>
      hk s' (frame_scalar_of_x64 hfr) hm'
  ret_spec hc hra hmem hk :=
    x64FrameSpec.spec.ret_spec hc hra hmem fun s' hkg _ hsp hm' =>
      hk s' hkg (fun v _ => v.elim) hsp hm'
  leafZeroFrame_ok := x64FrameSpec.spec.leafZeroFrame_ok

/-- `FrameTarget` for `x64ScalarMach` from `x64ScalarFramePreds` and `x64Scalar_frameSpec`. -/
@[expose] def x64ScalarFrameTarget : FrameTarget x64ScalarMach x64Frame x64CondReads where
  toFramePreds := x64ScalarFramePreds
  spec := x64Scalar_frameSpec

/-! ## 3. Target Assembly (`x64ScalarTarget`), `LabelClean`, & `TargetLayout` -/

/-- Verified scalar-only SysV x64 `Target` (`VReg := Empty`, `VecIsa.empty` / `VecTarget.empty`,
zero `IselVec` / `IselVecLemmas*` imports). -/
@[expose, reducible] def x64ScalarTarget : Target where
  toIsa := x64ScalarIsa
  mach := x64ScalarMach
  gprSpec := x64Scalar_gprSpec
  frameSpec := x64ScalarFrameTarget
  vecSpec := VecTarget.empty x64ScalarMach x64CondReads x64Frame.sp x64Scratch
    x64ScalarFrameTarget.spOk

theorem x64ScalarTarget_toIsa : x64ScalarTarget.toIsa = x64ScalarIsa :=
  rfl

/-- No scalar x64 instruction-selection or frame snippet emits a `.label` directive. -/
theorem x64ScalarLabelClean : Rega.LabelClean x64ScalarTarget.toIsa where
  label_inj _ _ h := Kraken.Directive.label.inj h
  mov := x64Gpr_mov_noLab
  movi := x64Gpr_movi_noLab
  setcc := x64Gpr_setcc_noLab
  jmp := x64Gpr_jmp_noLab
  jcc := x64Gpr_jcc_noLab
  jnzGpr := x64Gpr_jnzGpr_noLab
  op _ _ _ _ _ _ h l := x64Gpr_op_noLab h l
  load _ _ _ _ _ h l := x64Gpr_load_noLab h l
  store _ _ _ _ _ h l := x64Gpr_store_noLab h l
  clearFlags := x64Gpr_clearFlags_noLab
  vmov _ d := d.elim
  vmovi _ d := d.elim
  vslotSt _ _ s := s.elim
  vslotLd _ d := d.elim
  vop _ _ _ _ _ _ h := nomatch h
  vload _ d := d.elim
  vstore _ s := s.elim
  prologue := x64Prologue_noLab
  epilogue := x64Epilogue_noLab
  slotSt := x64SlotSt_noLab
  slotLd := x64SlotLd_noLab
  canonAbi := x64CanonAbi_noLab
  call := x64Call_noLab
  exitJmp := x64ExitJmp_noLab
  ret := x64Ret_noLab

/-- Uniform scalar x64 layout: 4 bytes per instruction, 0 bytes per label, base `0x1000`. -/
@[expose, instance_reducible] def x64ScalarUniformLayout : Layout where
  start := 0x1000
  instrSize _ := 4
  instrSize_pos _ := by decide

/-- Size per x64 directive under `x64ScalarUniformLayout`. -/
@[expose, reducible] def x64ScalarDirSize : Directive → Nat
  | .instr _ => 4
  | .label _ => 0
  | .byteArray arr => arr.size
  | .word bytes _ => bytes

/-- Kernel-reducible check that laying out `p` under `x64ScalarUniformLayout` fits in `2 ^ 64`. -/
@[expose] def x64ScalarProgSmall (p : List Directive) : Bool :=
  decide ((p.map x64ScalarDirSize).sum < 2 ^ 64)

private theorem size_map_x64ScalarUniformLayout :
    ∀ (xs : List Directive) (k : Nat),
      ((xs.mapIdx fun i d =>
          ({ directive := d, size := x64ScalarUniformLayout.size d (k + i) } :
            Kraken.Sized Directive)).map (·.size)) =
        xs.map x64ScalarDirSize
  | [], _ => rfl
  | d :: xs, k => by
    rw [List.mapIdx_cons, List.map_cons, List.map_cons]
    have hd : x64ScalarUniformLayout.size d (k + 0) = x64ScalarDirSize d := by cases d <;> rfl
    have hrest :
        (xs.mapIdx fun i d' =>
          ({ directive := d', size := x64ScalarUniformLayout.size d' (k + (i + 1)) } :
            Kraken.Sized Directive)) =
        xs.mapIdx fun i d' =>
          ({ directive := d', size := x64ScalarUniformLayout.size d' ((k + 1) + i) } :
            Kraken.Sized Directive) := by
      congr 1; funext i d'; rw [show k + (i + 1) = (k + 1) + i from by omega]
    rw [hd, hrest, size_map_x64ScalarUniformLayout xs (k + 1)]

theorem x64ScalarUniformLayout_small (p : List Directive) (h : x64ScalarProgSmall p = true) :
    (x64ScalarUniformLayout.apply p).sizeBefore p.length < 2 ^ 64 := by
  have hs :
      (x64ScalarUniformLayout.apply p).sizeBefore p.length = (p.map x64ScalarDirSize).sum := by
    simp only [Kraken.Executable.sizeBefore, Kraken.Layout.apply]
    rw [List.take_of_length_le (by simp)]
    simpa using congrArg List.sum (size_map_x64ScalarUniformLayout p 0)
  rw [hs]
  exact of_decide_eq_true h

/-- Extract label name if `d` is a `.label` directive. -/
@[expose] def x64ScalarLabelOf? : Directive → Option String
  | .label l => some l
  | _ => none

/-- Concrete scalar x64 host layout (`Host.ofLayout` with `x64ScalarUniformLayout`). -/
@[expose] def x64ScalarLayout : TargetLayout x64ScalarTarget where
  labelsNodup := labelsNodupBy x64ScalarLabelOf?
  progSmall := x64ScalarProgSmall
  layoutOf prog h := .ofLayout prog x64ScalarUniformLayout (x64ScalarUniformLayout_small prog h)
  prog_layoutOf _ _ := rfl
  labelsUnique_layoutOf {prog} h hnd :=
    letI : Host := .ofLayout prog x64ScalarUniformLayout (x64ScalarUniformLayout_small prog h)
    Host.labelsUnique_of_nodup (labelsNodupBy_nodup x64ScalarLabelOf? hnd)

/-! ## 4. Concrete Initial Machine State (`x64ScalarInit : TargetInit x64ScalarTarget 2048 8192`) -/

/-- `n`-byte zero stack below `rsp = 0x0ff8`, return address `ra` at `0x0ff8`, and payload `bs`
at `0x1000`. -/
@[expose] def x64ScalarInitMem (n : Nat) (ra : Int64) (bs : List UInt8) : Mem 64 :=
  ((stackZeros n ++ Int.toBytes 8 ra.toBitVec.toInt) ++ bs).At (0x0ff8#64 - BitVec.ofNat 64 n)

theorem x64ScalarInitMem_entry (n : Nat) (ra : Int64) (bs : List UInt8)
    (hn : n ≤ 2048) (hbs : bs.length ≤ 8192) :
    x64ScalarInitMem n ra bs =⋆
      Eq (bs.At 0x1000#64) ⋆ x64ScalarTarget.Entry 0x0ff8#64 ra n ⋆ Std.ExtHashMap.emp := by
  let raBytes : List UInt8 := Int.toBytes 8 ra.toBitVec.toInt
  have hra : raBytes.length = 8 := Int.toBytes_length 8 _
  have hzs : (stackZeros n).length = n := stackZeros_length n
  have hsp : (0x0ff8#64 - BitVec.ofNat 64 n) + BitVec.ofNat 64 n = 0x0ff8#64 :=
    BitVec.sub_add_cancel _ _
  have h1000 : (0x0ff8#64 : BitVec 64) + BitVec.ofNat 64 8 = 0x1000#64 := by decide
  have hlen1 : (stackZeros n).length + (raBytes ++ bs).length ≤ 2 ^ 64 := by
    rw [hzs, List.length_append, hra]
    exact Nat.le_trans (Nat.add_le_add hn (Nat.add_le_add_left hbs 8)) (by decide)
  have hlen2 : raBytes.length + bs.length ≤ 2 ^ 64 := by
    rw [hra]
    exact Nat.le_trans (Nat.add_le_add_left hbs 8) (by decide)
  have h1 : Eq ((stackZeros n ++ (raBytes ++ bs)).At (0x0ff8#64 - BitVec.ofNat 64 n)) =
      (Eq ((stackZeros n).At (0x0ff8#64 - BitVec.ofNat 64 n)) ⋆
        Eq ((raBytes ++ bs).At 0x0ff8#64)) := by
    have e := Mem.At_append_sep (stackZeros n) (raBytes ++ bs) (0x0ff8#64 - BitVec.ofNat 64 n) hlen1
    rwa [hzs, hsp] at e
  have h2 : Eq ((raBytes ++ bs).At 0x0ff8#64) =
      (Eq (raBytes.At 0x0ff8#64) ⋆ Eq (bs.At 0x1000#64)) := by
    have e := Mem.At_append_sep raBytes bs 0x0ff8#64 hlen2
    rwa [hra, h1000] at e
  have hmem : (Eq (bs.At 0x1000#64) ⋆
      (Eq ((stackZeros n).At (0x0ff8#64 - BitVec.ofNat 64 n)) ⋆ Eq (raBytes.At 0x0ff8#64)) ⋆
      Std.ExtHashMap.emp) (x64ScalarInitMem n ra bs) := by
    rw [Std.ExtHashMap.sep_emp]
    refine sep_cast (show Eq (x64ScalarInitMem n ra bs) (x64ScalarInitMem n ra bs) from rfl) ?_
    change Eq ((stackZeros n ++ raBytes ++ bs).At (0x0ff8#64 - BitVec.ofNat 64 n)) = _
    rw [List.append_assoc, h1, h2]
    ac_rfl
  have hsub : ∀ m, (Eq ((stackZeros n).At (0x0ff8#64 - BitVec.ofNat 64 n)) ⋆
      Eq (raBytes.At 0x0ff8#64)) m → x64ScalarTarget.Entry 0x0ff8#64 ra n m := by
    intro m ⟨f1, f2, hu, hd, hf1, hf2⟩
    exact ⟨f1, f2, hu, hd, ⟨stackZeros n, hzs, hf1.symm⟩, hf2⟩
  exact sep_mono_mid hsub hmem

/-- Encode typed ABI scalar argument value into a 64-bit register word. -/
@[expose] def valToScalarGpr : (t : Ty) → Val t → BitVec 64
  | .bool, b => BitVec.ofNat 64 b.toNat
  | .bits _, v => v.setWidth 64
  | _, _ => 0

/-- Populate SysV x64 GPR argument registers with `rsp = 0x0ff8`. -/
@[expose] def setX64ScalarAbiRegs :
    {ts : List Ty} → Tup (AbiReg Reg64 Empty) ts → Tup Val ts → Reg64s
  | [], _, _ => { rsp := 0x0ff8 }
  | t :: _, (loc, locs), (v, vs) =>
    let p := setX64ScalarAbiRegs locs vs
    match loc with
    | .gpr r => p.set64 r (valToScalarGpr t v)
    | .vec vr => vr.elim

private theorem x64ScalarAssignSig_cons {t : Ty} {ts : List Ty} {loc : AbiReg Reg64 Empty t}
    {locs : Tup (AbiReg Reg64 Empty) ts} {gs : List Reg64} {vs : List Empty}
    (h : x64ScalarTarget.toIsa.assignSig (t :: ts) gs vs = some (loc, locs)) :
    match loc with
    | .gpr r => ∃ gs', gs = r :: gs' ∧
        x64ScalarTarget.toIsa.assignSig ts gs' vs = some locs ∧
        (t = .bool ∨ ∃ n, t = .bits n ∧ n ≤ 64)
    | .vec vr => vr.elim := by
  cases t with
  | bool =>
    cases gs with
    | nil => simp [Isa.assignSig] at h
    | cons r0 gs' =>
      simp only [Isa.assignSig, Option.map_eq_some_iff] at h
      obtain ⟨locs', h', hloc⟩ := h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hloc
      exact ⟨gs', rfl, h', Or.inl rfl⟩
  | bits n =>
    cases gs with
    | nil => simp [Isa.assignSig] at h
    | cons r0 gs' =>
      simp only [Isa.assignSig] at h
      cases hbw : [8, 16, 32, 64].contains n
      · simp only [hbw, Bool.false_eq_true, ↓reduceIte] at h; cases h
      · simp only [hbw, ↓reduceIte, Option.map_eq_some_iff] at h
        obtain ⟨locs', h', hloc⟩ := h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hloc
        have hle : n ≤ 64 := by
          simp only [List.contains_eq_mem, List.mem_cons,
            List.not_mem_nil, or_false, decide_eq_true_eq] at hbw
          rcases hbw with rfl | rfl | rfl | rfl <;> decide
        exact ⟨gs', rfl, h', Or.inr ⟨n, rfl, hle⟩⟩
  | float _ => simp [Isa.assignSig] at h
  | pair _ _ => cases vs with | nil => simp [Isa.assignSig] at h | cons v _ => exact v.elim

private theorem setX64ScalarAbiRegs_get_rsp :
    ∀ {ts : List Ty} {locs : Tup (AbiReg Reg64 Empty) ts} {args : Tup Val ts}
      {gs : List Reg64} {vs : List Empty},
      .rsp ∉ gs → x64ScalarTarget.toIsa.assignSig ts gs vs = some locs →
      (setX64ScalarAbiRegs locs args).get64 .rsp = 0x0ff8#64
  | [], (), (), _, _, _, _ => rfl
  | t :: ts, (loc, locs), (v, vs), gs, vs', hrsp, h => by
    have hc := x64ScalarAssignSig_cons h
    cases loc with
    | gpr r =>
      obtain ⟨gs', rfl, h', _⟩ := hc
      have hne : r ≠ .rsp := fun e => hrsp (e ▸ List.mem_cons_self)
      simp only [setX64ScalarAbiRegs]
      rw [Reg64s.get64_set64_of_ne _ _ _ _ hne]
      exact setX64ScalarAbiRegs_get_rsp (fun hm => hrsp (List.mem_cons_of_mem _ hm)) h'
    | vec vr => exact vr.elim

private theorem x64ScalarAbi_frame {g g' : Reg64s} :
    ∀ {ts : List Ty} {locs : Tup (AbiReg Reg64 Empty) ts} {args : Tup Val ts}
      {gs : List Reg64} {vs : List Empty},
      (∀ r ∈ gs, g'.get64 r = g.get64 r) →
      x64ScalarTarget.toIsa.assignSig ts gs vs = some locs →
      TRel (fun t loc val => match loc with
        | .gpr r => AbiGprHolds (g.get64 r) t val
        | .vec vr => vr.elim) locs args →
      TRel (fun t loc val => match loc with
        | .gpr r => AbiGprHolds (g'.get64 r) t val
        | .vec vr => vr.elim) locs args
  | [], (), (), _, _, _, _, _ => .nil
  | _ :: _, (loc, _), (_, _), _, _, hg, h, hrel => by
    cases hrel with
    | cons h1 h2 =>
      have hc := x64ScalarAssignSig_cons h
      cases loc with
      | gpr r =>
        obtain ⟨_, rfl, h', _⟩ := hc
        exact .cons (by simpa [hg r List.mem_cons_self] using h1)
          (x64ScalarAbi_frame (fun x hm => hg x (List.mem_cons_of_mem _ hm)) h' h2)
      | vec vr => exact vr.elim

private theorem setX64ScalarAbiRegs_holds :
    ∀ {ts : List Ty} {locs : Tup (AbiReg Reg64 Empty) ts} {args : Tup Val ts}
      {gs : List Reg64} {vs : List Empty},
      gs.Nodup → x64ScalarTarget.toIsa.assignSig ts gs vs = some locs →
      TRel (fun t loc val => match loc with
        | .gpr r => AbiGprHolds ((setX64ScalarAbiRegs locs args).get64 r) t val
        | .vec vr => vr.elim) locs args
  | [], (), (), _, _, _, _ => .nil
  | t :: ts, (loc, locs), (v, vs), gs, vs', hgs, h => by
    have hc := x64ScalarAssignSig_cons h
    cases loc with
    | gpr r =>
      obtain ⟨gs', rfl, h', hty⟩ := hc
      obtain ⟨hnmem, hgs'⟩ := List.nodup_cons.mp hgs
      have hhead :
          AbiGprHolds
            ((setX64ScalarAbiRegs (ts := t :: ts) (AbiReg.gpr r, locs) (v, vs)).get64 r) t v := by
        rcases hty with rfl | ⟨n, rfl, hn⟩
        · simp [setX64ScalarAbiRegs, valToScalarGpr, AbiGprHolds]
        · simp [setX64ScalarAbiRegs, valToScalarGpr, AbiGprHolds, hn]
      refine .cons hhead (x64ScalarAbi_frame ?_ h' (setX64ScalarAbiRegs_holds hgs' h'))
      intro x hx
      simp only [setX64ScalarAbiRegs]
      exact Reg64s.get64_set64_of_ne _ _ _ _ (fun e => hnmem (e ▸ hx))
    | vec vr => exact vr.elim

/-- Concrete initial `MachineData` for `x64ScalarTarget` (`sp0 = 0x0ff8`, `ra0 = 0x1234`,
payload `bs` at `0x1000#64`, scalar SysV ABI argument registers populated). -/
@[expose] def x64ScalarInitState (n : Nat) (bs : List UInt8) {as : List Ty}
    (args : Tup Val as) : MachineData :=
  let regs :=
    match x64ScalarTarget.toIsa.assignArgs as with
    | some locs => setX64ScalarAbiRegs locs args
    | none => { rsp := 0x0ff8 }
  { regs := regs, zmms := {}, dmem := x64ScalarInitMem n 0x1234 bs }

private theorem trel_x64Scalar_imp {P Q : ∀ t, AbiReg Reg64 Empty t → Val t → Prop}
    (h : ∀ t a v, P t a v → Q t a v) :
    ∀ {ts : List Ty} {xs : Tup (AbiReg Reg64 Empty) ts} {ys : Tup Val ts},
      TRel P xs ys → TRel Q xs ys
  | [], _, _, .nil => .nil
  | _ :: _, _, _, .cons hx hxs => .cons (h _ _ _ hx) (trel_x64Scalar_imp h hxs)

/-- Closed concrete execution harness for `x64ScalarTarget` (`sp0 = 0x0ff8#64`, `ra0 = 0x1234`). -/
@[expose] def x64ScalarInit : TargetInit x64ScalarTarget 2048 8192 where
  sp0 := 0x0ff8#64
  ra0 := 0x1234
  ret0 := .rax
  arg0 := .rdi
  initState := x64ScalarInitState
  get_sp := fun n bs {as} args => by
    simp only [x64ScalarTarget, x64ScalarMach, x64ScalarInitState]
    cases h : x64ScalarTarget.toIsa.assignArgs as with
    | none => rfl
    | some locs =>
      exact setX64ScalarAbiRegs_get_rsp (by simp) h
  argsIn := fun n bs {as} args his => by
    obtain ⟨locs, hlocs⟩ := Option.isSome_iff_exists.mp his
    refine ⟨locs, hlocs, ?_⟩
    simp only [x64ScalarInitState, hlocs]
    exact trel_x64Scalar_imp
      (fun t loc v h => by cases loc with | gpr _ => exact h | vec v => exact v.elim)
      (setX64ScalarAbiRegs_holds (by simp) hlocs)
  raReg _ _ := by intros; trivial
  spEntry := by dsimp only [x64ScalarTarget, x64ScalarFrameTarget, x64ScalarFramePreds,
    x64FramePreds]; decide
  mem_entry n bs {_} _ hn hbs := x64ScalarInitMem_entry n 0x1234 bs hn hbs
  retsIn_singleton v s h := by
    obtain ⟨locs, hlocs, hrel⟩ := h
    change some (AbiReg.gpr .rax, ()) = some locs at hlocs
    injection hlocs with hlocs; subst hlocs
    cases hrel with
    | cons h1 _ => exact h1.2.trans (by simp)
  argsIn_singleton v s h := by
    obtain ⟨locs, hlocs, hrel⟩ := h
    change some (AbiReg.gpr .rdi, ()) = some locs at hlocs
    injection hlocs with hlocs; subst hlocs
    cases hrel with
    | cons h1 _ => exact h1.2.trans (by simp)

/-! ## 5. Scalar Capability Kernel Checks -/

/-- Kernel checks verifying `x64ScalarLegalTarget` and `x64ScalarTarget.toIsa` accept scalar ops
and reject float and vector ops. -/
theorem x64ScalarSupportsOp_checks :
    x64ScalarLegalTarget.valid = true ∧
    x64ScalarLegalTarget.keepsPacked (Ty.vec 2 i32) = false ∧
    x64ScalarLegalTarget.supportsTy (.float .s) = false ∧
    x64ScalarLegalTarget.supportsTy (.float .d) = false ∧
    x64ScalarTarget.toIsa.vec.supportsVecOp (.add (Ty.vec 2 i32)) (.var (), .var (), ()) =
      false ∧
    x64ScalarTarget.toIsa.supportsOp (.add i64) (.var (), .var (), ()) = true ∧
    x64ScalarTarget.toIsa.supportsOp (.umulw 64) (.var (), .var (), ()) = true ∧
    x64ScalarTarget.toIsa.supportsOp (.udiv 64) (.var (), .var (), ()) = true ∧
    x64ScalarTarget.toIsa.supportsOp (.sdiv 64) (.var (), .var (), ()) = true ∧
    x64ScalarTarget.toIsa.supportsOp (.fadd (.float .s)) (.var (), .var (), ()) = false := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end LeanQbe.T.Amd64
