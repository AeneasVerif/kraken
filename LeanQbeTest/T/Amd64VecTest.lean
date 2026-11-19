module

public import LeanQbe.T.Amd64.IselVecLemmas3
public import LeanQbe.T.Examples.ChaCha
import Kraken.X64.Parser

/-!
# SysV x64 SIMD Vector Target Tests (`T10`)

Standalone downstream test suite verifying `x64Vec` and `x64VecSpec`:
1. Kernel `rfl` checks of `x64Vec` bank metadata, `isAbiVec`, `vecSlotWidth`, `supportsVecOp`
   (including negative checks rejecting SHA-NI and non-uniform shifts), and `Parser` snippets.
2. Concrete `Host.ofLayout` ChaCha quarter-round + `shufd $0x39` execution on `v4i32` rows
   (including RFC 8439 §2.1.1 vector verification).
3. Concrete `Host.ofLayout` `addps`/`subps` execution on `v4f32` including IEEE-754 binary32
   arithmetic and explicit NaN propagation.
4. Concrete `Host.ofLayout` `mkpair`/`unpair` bridge round-trips (`i32 × i32 ↔ v2i32 ↔ v4i32`
   and `v2f32 × v2f32 ↔ v4f32`).
5. Concrete `Host.ofLayout` unaligned stack-slot (`vslotSt`/`vslotLd` at misaligned `%rsp` and
   large `≥ 2^31` slot index) and unaligned memory (`vstore`/`vload` with large `disp`) round-trips.
6. Standard-axiom audit `[propext, Classical.choice, Quot.sound]` on `x64VecSpec`, all `NoLab`
   theorems, and test runs.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.Amd64VecTest

open LeanQbe.T
open LeanQbe.T.Amd64
open LeanQbe.T.Examples.ChaCha
open Kraken.X64.Parser
open Std Std.ExtHashMap

abbrev v2i32 : Ty := Ty.vec 1 i32
abbrev v2f32 : Ty := Ty.vec 1 (.float .s)
abbrev v8f32 : Ty := Ty.vec 3 (.float .s)
abbrev v16i32 : Ty := Ty.vec 4 i32
abbrev v16f32 : Ty := Ty.vec 4 (.float .s)

/-! ## 1. Kernel `rfl` metadata, `supportsVecOp`, and `Parser` checks -/

theorem x64Vec_metadata_rfl :
    x64Vec.vecScratch = [.mm14, .mm15] ∧
    x64Vec.vecAllocatable = [.mm0, .mm1, .mm2, .mm3, .mm4, .mm5, .mm6, .mm7,
      .mm8, .mm9, .mm10, .mm11, .mm12, .mm13] ∧
    x64Vec.vecArgRegs = [.mm0, .mm1, .mm2, .mm3, .mm4, .mm5, .mm6, .mm7] ∧
    x64Vec.vecRetRegs = [.mm0, .mm1] ∧
    x64Vec.isAbiVec v4i32 = true ∧
    x64Vec.isAbiVec v4f32 = true ∧
    x64Vec.isAbiVec v2i32 = false ∧
    x64Vec.isAbiVec v2f32 = false ∧
    x64Vec.isAbiVec v8i32 = false ∧
    x64Vec.isAbiVec v16i32 = false ∧
    x64Vec.vecSlotWidth v2i32 = some .w64 ∧
    x64Vec.vecSlotWidth v2f32 = some .w64 ∧
    x64Vec.vecSlotWidth v4i32 = some .w128 ∧
    x64Vec.vecSlotWidth v4f32 = some .w128 ∧
    x64Vec.vecSlotWidth v8i32 = some .w256 ∧
    x64Vec.vecSlotWidth v16f32 = some .w512 ∧
    x64Vec.vecSlotWidth i64 = none ∧
    x64Vec.vecSlotWidth (.float .d) = none ∧
    x64Vec.vecSlotWidth .bool = none := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem x64Vec_supportsVecOp_rfl :
    x64Vec.supportsVecOp (.copy v4i32) (.var (), ()) = true ∧
    x64Vec.supportsVecOp (.copy v8f32) (.var (), ()) = true ∧
    x64Vec.supportsVecOp (.add v8i32) (.var (), .var (), ()) = true ∧
    x64Vec.supportsVecOp (.and v16i32) (.var (), .var (), ()) = true ∧
    x64Vec.supportsVecOp (.or v8f32) (.var (), .var (), ()) = true ∧
    x64Vec.supportsVecOp (.xor v4i32) (.var (), .var (), ()) = true ∧
    x64Vec.supportsVecOp (.not v4i32) (.var (), ()) = true ∧
    x64Vec.supportsVecOp (.ternlog v4i32 0xca#8) (.var (), .var (), .var (), ()) = true ∧
    x64Vec.supportsVecOp (.rotr v4i32) (.var (), .imm ((16#32, 16#32), (16#32, 16#32)), ()) = true ∧
    x64Vec.supportsVecOp (.lshr v4i32) (.var (), .imm ((35#32, 3#32), (3#32, 67#32)), ()) = true ∧
    x64Vec.supportsVecOp (.shufd v4i32 0x39#8) (.var (), ()) = true ∧
    x64Vec.supportsVecOp (.shufb v4i32) (.var (), .var (), ()) = true ∧
    x64Vec.supportsVecOp (OpCode.alignr v4i32 4#8) (.var (), .var (), ()) = true ∧
    x64Vec.supportsVecOp (.blendw v4i32 0xf0#8) (.var (), .var (), ()) = true ∧
    x64Vec.supportsVecOp (.fadd v4f32) (.var (), .var (), ()) = true ∧
    x64Vec.supportsVecOp (.fsub v4f32) (.var (), .var (), ()) = true ∧
    x64Vec.supportsVecOp (.mkpair i32 i32) (.var (), .var (), ()) = true ∧
    x64Vec.supportsVecOp (.mkpair v2i32 v2i32) (.var (), .var (), ()) = true ∧
    x64Vec.supportsVecOp (.mkpair v2f32 v2f32) (.var (), .var (), ()) = true ∧
    x64Vec.supportsVecOp (.unpair i32 i32) (.var (), ()) = true ∧
    x64Vec.supportsVecOp (.unpair v2f32 v2f32) (.var (), ()) = true ∧
    -- Rejected ops: SHA-NI (G10), non-uniform splats, non-imm shifts, sub-128 arith, wide float
    x64Vec.supportsVecOp .sha256rnds2 (.var (), .var (), .var (), ()) = false ∧
    x64Vec.supportsVecOp .sha256msg1 (.var (), .var (), ()) = false ∧
    x64Vec.supportsVecOp .sha256msg2 (.var (), .var (), ()) = false ∧
    x64Vec.supportsVecOp (.rotr v4i32) (.var (), .imm ((16#32, 12#32), (16#32, 16#32)), ()) = false ∧
    x64Vec.supportsVecOp (.rotr v4i32) (.var (), .var (), ()) = false ∧
    x64Vec.supportsVecOp (.add v2i32) (.var (), .var (), ()) = false ∧
    x64Vec.supportsVecOp (.copy v2f32) (.var (), ()) = false ∧
    x64Vec.supportsVecOp (.fadd v8f32) (.var (), .var (), ()) = false ∧
    x64Vec.supportsVecOp (.add v4f32) (.var (), .var (), ()) = false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem x64Vec_evex_sse_parser_rfl :
    ⸨prog| vmovdqu32 %zmm1, %zmm0; vpaddd %zmm2, %zmm1, %zmm0 ⸩ =
      x64Vec.vmov .w512 .mm0 .mm1 ++
        (x64Vec.vop (.add v16i32) (.vec .mm1, .vec .mm2, ()) (.vec .mm0, ()) .default).get!.1 ∧
    ⸨prog| vpsrld $5, %ymm1, %ymm0 ⸩ =
      (x64Vec.vop (.lshr v8i32) (.vec .mm1, .imm (splatV 3 37#32), ()) (.vec .mm0, ()) .default).get!.1 ∧
    ⸨prog| movabs $2147483648, %r10; leaq (%rbx, %r10, 1), %r10; vmovdqu32 %xmm0, (%r10) ⸩ =
      (x64Vec.vstore v4i32 .mm0 (.baseDisp .rbx 2147483648)).get!.1 := by
  exact ⟨rfl, rfl, rfl⟩

/-! ## Shared `Host.ofLayout` test layout & stepping glue -/

@[instance_reducible] def testLayout : Layout where
  start := 0x10000
  instrSize _ := 4
  instrSize_pos _ := by decide

theorem step_vop1 {h : Host} {k : Nat} {sig : List Ty} {t : Ty}
    (code : OpCode sig [t]) (pas : Tup (PArg Reg64 RegMm CondCode) sig) (vd : RegMm)
    {c : List Directive} {clob : FlagMask} {vs : Tup Val sig} {res : Val t} {s : MachineData}
    {post : MachineState → Prop}
    (hc : x64Vec.vop code pas (.vec vd, ()) .default = some (c, clob))
    (hpaG : ∀ r ∈ tupArgGprs pas, r ∉ x64Scratch)
    (hpaV : ∀ vr ∈ tupArgVecs pas, vr ∉ x64VecScratch)
    (hdV : vd ∉ x64VecScratch)
    (hhold : TRel (x64Mach.PArgHolds s) pas vs)
    (hwp : code.wp vs fun rvs => rvs = (res, ()))
    (hinf : c.IsInfixAt (x64Mach.prog h) k)
    (hk : ∀ s', VecHolds (x64Mach.getVec s' vd) t res →
      x64Mach.Frame x64CondReads s s' x64Scratch (vd :: x64VecScratch) clob →
      x64Mach.mem s' = x64Mach.mem s →
      x64Mach.Run h (k + c.length) s' post) :
    x64Mach.Run h k s post := by
  refine x64VecSpec.vop_spec hc hpaG hpaV (by simp [tupDstGprs])
    (fun vr hvr => by simp only [tupDstVecs, List.mem_singleton] at hvr; subst hvr; exact hdV)
    hhold hwp hinf ?_
  rintro s' ⟨⟨⟨rv, ⟨⟩⟩, heq, htr⟩, hmem⟩ hfr
  obtain rfl : rv = res := (Prod.mk.inj heq).1
  rcases htr with _ | ⟨hvd, _⟩
  exact hk s' hvd hfr hmem

/-! ## 2. ChaCha quarter-round + `shufd $0x39` concrete `Host.ofLayout` run (`v4i32`) -/

def chachaOps : List (List Directive) :=
  [ (x64Vec.vop (.add v4i32) (.vec .mm0, .vec .mm1, ()) (.vec .mm0, ()) .default).get!.1
  , (x64Vec.vop (.xor v4i32) (.vec .mm3, .vec .mm0, ()) (.vec .mm3, ()) .default).get!.1
  , (x64Vec.vop (.rotr v4i32) (.vec .mm3, .imm (splatV 2 16#32), ()) (.vec .mm3, ()) .default).get!.1
  , (x64Vec.vop (.add v4i32) (.vec .mm2, .vec .mm3, ()) (.vec .mm2, ()) .default).get!.1
  , (x64Vec.vop (.xor v4i32) (.vec .mm1, .vec .mm2, ()) (.vec .mm1, ()) .default).get!.1
  , (x64Vec.vop (.rotr v4i32) (.vec .mm1, .imm (splatV 2 20#32), ()) (.vec .mm1, ()) .default).get!.1
  , (x64Vec.vop (.add v4i32) (.vec .mm0, .vec .mm1, ()) (.vec .mm0, ()) .default).get!.1
  , (x64Vec.vop (.xor v4i32) (.vec .mm3, .vec .mm0, ()) (.vec .mm3, ()) .default).get!.1
  , (x64Vec.vop (.rotr v4i32) (.vec .mm3, .imm (splatV 2 24#32), ()) (.vec .mm3, ()) .default).get!.1
  , (x64Vec.vop (.add v4i32) (.vec .mm2, .vec .mm3, ()) (.vec .mm2, ()) .default).get!.1
  , (x64Vec.vop (.xor v4i32) (.vec .mm1, .vec .mm2, ()) (.vec .mm1, ()) .default).get!.1
  , (x64Vec.vop (.rotr v4i32) (.vec .mm1, .imm (splatV 2 25#32), ()) (.vec .mm1, ()) .default).get!.1
  , (x64Vec.vop (.shufd v4i32 0x39#8) (.vec .mm1, ()) (.vec .mm1, ()) .default).get!.1
  ]

def chachaQrProg : List Directive := chachaOps.flatten

theorem chachaQrProg_small :
    (Kraken.Layout.apply testLayout chachaQrProg).sizeBefore chachaQrProg.length < 2 ^ 64 := by
  simp only [Kraken.Layout.apply, Kraken.Executable.sizeBefore, Kraken.Layout.size, chachaQrProg, chachaOps]
  decide

@[instance_reducible] def chachaHost : Host :=
  Host.ofLayout chachaQrProg testLayout chachaQrProg_small

def rowRotr (r : Row) (n : Nat) : Row :=
  lift2 (fun x y => x.rotateRight (y.toNat % 32)) (fun _ y => y) v4i32 r (splatV 2 (BitVec.ofNat 32 n))

def rowAddV (a b : Row) : Row := lift2 (· + ·) (fun x _ => x) v4i32 a b
def rowXorV (a b : Row) : Row := lift2 (· ^^^ ·) (fun x _ => x) v4i32 a b

def chachaQrModel (a b c d : Row) : Row × Row × Row × Row :=
  let a1 := rowAddV a b
  let d1 := rowXorV d a1
  let d2 := rowRotr d1 16
  let c1 := rowAddV c d2
  let b1 := rowXorV b c1
  let b2 := rowRotr b1 20
  let a2 := rowAddV a1 b2
  let d3 := rowXorV d2 a2
  let d4 := rowRotr d3 24
  let c2 := rowAddV c1 d4
  let b3 := rowXorV b2 c2
  let b4 := rowRotr b3 25
  let b4s := ofBits v4i32 ((toBits v4i32 b4).shuffleDwords 0x39#8)
  (a2, b4s, c2, d4)

theorem chachaQrProg_run {a b c d : Row} {s : MachineData}
    (ha : VecHolds (x64Mach.getVec s .mm0) v4i32 a)
    (hb : VecHolds (x64Mach.getVec s .mm1) v4i32 b)
    (hc : VecHolds (x64Mach.getVec s .mm2) v4i32 c)
    (hd : VecHolds (x64Mach.getVec s .mm3) v4i32 d) :
    x64Mach.Run chachaHost 0 s fun st =>
      let (a', b', c', d') := chachaQrModel a b c d
      VecHolds (x64Mach.getVec st.data .mm0) v4i32 a' ∧
      VecHolds (x64Mach.getVec st.data .mm1) v4i32 b' ∧
      VecHolds (x64Mach.getVec st.data .mm2) v4i32 c' ∧
      VecHolds (x64Mach.getVec st.data .mm3) v4i32 d' ∧
      st.data.dmem = s.dmem := by
  have hprog : chachaQrProg.IsInfixAt (x64Mach.prog chachaHost) 0 :=
    ⟨[], by rw [List.drop_zero, List.append_nil]; rfl⟩
  letI := chachaHost
  have hlist : chachaQrProg =
      chachaOps[0] ++ chachaOps[1] ++ chachaOps[2] ++ chachaOps[3] ++ chachaOps[4] ++
      chachaOps[5] ++ chachaOps[6] ++ chachaOps[7] ++ chachaOps[8] ++ chachaOps[9] ++
      chachaOps[10] ++ chachaOps[11] ++ chachaOps[12] := by decide
  rw [hlist] at hprog
  obtain ⟨h0, hs12⟩ := hprog.append; obtain ⟨h0, hs11⟩ := h0.append
  obtain ⟨h0, hs10⟩ := h0.append; obtain ⟨h0, hs9⟩ := h0.append
  obtain ⟨h0, hs8⟩ := h0.append; obtain ⟨h0, hs7⟩ := h0.append
  obtain ⟨h0, hs6⟩ := h0.append; obtain ⟨h0, hs5⟩ := h0.append
  obtain ⟨h0, hs4⟩ := h0.append; obtain ⟨h0, hs3⟩ := h0.append
  obtain ⟨h0, hs2⟩ := h0.append; obtain ⟨hs0, hs1⟩ := h0.append
  refine step_vop1 (.add v4i32) (.vec .mm0, .vec .mm1, ()) .mm0 (clob := maskNone) rfl
    (by simp [tupArgGprs]) (by simp [tupArgVecs, x64VecScratch]) (by simp [x64VecScratch])
    (TRel.cons ha (TRel.cons hb .nil)) rfl hs0 ?_
  intro s1 ha1 hfr1 hm1
  have hb1 := hb; rw [← hfr1.2.1 .mm1 (by simp [x64VecScratch])] at hb1
  have hc1 := hc; rw [← hfr1.2.1 .mm2 (by simp [x64VecScratch])] at hc1
  have hd1 := hd; rw [← hfr1.2.1 .mm3 (by simp [x64VecScratch])] at hd1
  refine step_vop1 (.xor v4i32) (.vec .mm3, .vec .mm0, ()) .mm3 (clob := maskNone) rfl
    (by simp [tupArgGprs]) (by simp [tupArgVecs, x64VecScratch]) (by simp [x64VecScratch])
    (TRel.cons hd1 (TRel.cons ha1 .nil)) rfl hs1 ?_
  intro s2 hd2 hfr2 hm2
  have ha2 := ha1; rw [← hfr2.2.1 .mm0 (by simp [x64VecScratch])] at ha2
  have hb2 := hb1; rw [← hfr2.2.1 .mm1 (by simp [x64VecScratch])] at hb2
  have hc2 := hc1; rw [← hfr2.2.1 .mm2 (by simp [x64VecScratch])] at hc2
  refine step_vop1 (.rotr v4i32) (.vec .mm3, .imm (splatV 2 16#32), ()) .mm3 (clob := maskNone) rfl
    (by simp [tupArgGprs]) (by simp [tupArgVecs, x64VecScratch]) (by simp [x64VecScratch])
    (TRel.cons hd2 (TRel.cons rfl .nil)) rfl hs2 ?_
  intro s3 hd3 hfr3 hm3
  have ha3 := ha2; rw [← hfr3.2.1 .mm0 (by simp [x64VecScratch])] at ha3
  have hb3 := hb2; rw [← hfr3.2.1 .mm1 (by simp [x64VecScratch])] at hb3
  have hc3 := hc2; rw [← hfr3.2.1 .mm2 (by simp [x64VecScratch])] at hc3
  refine step_vop1 (.add v4i32) (.vec .mm2, .vec .mm3, ()) .mm2 (clob := maskNone) rfl
    (by simp [tupArgGprs]) (by simp [tupArgVecs, x64VecScratch]) (by simp [x64VecScratch])
    (TRel.cons hc3 (TRel.cons hd3 .nil)) rfl hs3 ?_
  intro s4 hc4 hfr4 hm4
  have ha4 := ha3; rw [← hfr4.2.1 .mm0 (by simp [x64VecScratch])] at ha4
  have hb4 := hb3; rw [← hfr4.2.1 .mm1 (by simp [x64VecScratch])] at hb4
  have hd4 := hd3; rw [← hfr4.2.1 .mm3 (by simp [x64VecScratch])] at hd4
  refine step_vop1 (.xor v4i32) (.vec .mm1, .vec .mm2, ()) .mm1 (clob := maskNone) rfl
    (by simp [tupArgGprs]) (by simp [tupArgVecs, x64VecScratch]) (by simp [x64VecScratch])
    (TRel.cons hb4 (TRel.cons hc4 .nil)) rfl hs4 ?_
  intro s5 hb5 hfr5 hm5
  have ha5 := ha4; rw [← hfr5.2.1 .mm0 (by simp [x64VecScratch])] at ha5
  have hc5 := hc4; rw [← hfr5.2.1 .mm2 (by simp [x64VecScratch])] at hc5
  have hd5 := hd4; rw [← hfr5.2.1 .mm3 (by simp [x64VecScratch])] at hd5
  refine step_vop1 (.rotr v4i32) (.vec .mm1, .imm (splatV 2 20#32), ()) .mm1 (clob := maskNone) rfl
    (by simp [tupArgGprs]) (by simp [tupArgVecs, x64VecScratch]) (by simp [x64VecScratch])
    (TRel.cons hb5 (TRel.cons rfl .nil)) rfl hs5 ?_
  intro s6 hb6 hfr6 hm6
  have ha6 := ha5; rw [← hfr6.2.1 .mm0 (by simp [x64VecScratch])] at ha6
  have hc6 := hc5; rw [← hfr6.2.1 .mm2 (by simp [x64VecScratch])] at hc6
  have hd6 := hd5; rw [← hfr6.2.1 .mm3 (by simp [x64VecScratch])] at hd6
  refine step_vop1 (.add v4i32) (.vec .mm0, .vec .mm1, ()) .mm0 (clob := maskNone) rfl
    (by simp [tupArgGprs]) (by simp [tupArgVecs, x64VecScratch]) (by simp [x64VecScratch])
    (TRel.cons ha6 (TRel.cons hb6 .nil)) rfl hs6 ?_
  intro s7 ha7 hfr7 hm7
  have hb7 := hb6; rw [← hfr7.2.1 .mm1 (by simp [x64VecScratch])] at hb7
  have hc7 := hc6; rw [← hfr7.2.1 .mm2 (by simp [x64VecScratch])] at hc7
  have hd7 := hd6; rw [← hfr7.2.1 .mm3 (by simp [x64VecScratch])] at hd7
  refine step_vop1 (.xor v4i32) (.vec .mm3, .vec .mm0, ()) .mm3 (clob := maskNone) rfl
    (by simp [tupArgGprs]) (by simp [tupArgVecs, x64VecScratch]) (by simp [x64VecScratch])
    (TRel.cons hd7 (TRel.cons ha7 .nil)) rfl hs7 ?_
  intro s8 hd8 hfr8 hm8
  have ha8 := ha7; rw [← hfr8.2.1 .mm0 (by simp [x64VecScratch])] at ha8
  have hb8 := hb7; rw [← hfr8.2.1 .mm1 (by simp [x64VecScratch])] at hb8
  have hc8 := hc7; rw [← hfr8.2.1 .mm2 (by simp [x64VecScratch])] at hc8
  refine step_vop1 (.rotr v4i32) (.vec .mm3, .imm (splatV 2 24#32), ()) .mm3 (clob := maskNone) rfl
    (by simp [tupArgGprs]) (by simp [tupArgVecs, x64VecScratch]) (by simp [x64VecScratch])
    (TRel.cons hd8 (TRel.cons rfl .nil)) rfl hs8 ?_
  intro s9 hd9 hfr9 hm9
  have ha9 := ha8; rw [← hfr9.2.1 .mm0 (by simp [x64VecScratch])] at ha9
  have hb9 := hb8; rw [← hfr9.2.1 .mm1 (by simp [x64VecScratch])] at hb9
  have hc9 := hc8; rw [← hfr9.2.1 .mm2 (by simp [x64VecScratch])] at hc9
  refine step_vop1 (.add v4i32) (.vec .mm2, .vec .mm3, ()) .mm2 (clob := maskNone) rfl
    (by simp [tupArgGprs]) (by simp [tupArgVecs, x64VecScratch]) (by simp [x64VecScratch])
    (TRel.cons hc9 (TRel.cons hd9 .nil)) rfl hs9 ?_
  intro s10 hc10 hfr10 hm10
  have ha10 := ha9; rw [← hfr10.2.1 .mm0 (by simp [x64VecScratch])] at ha10
  have hb10 := hb9; rw [← hfr10.2.1 .mm1 (by simp [x64VecScratch])] at hb10
  have hd10 := hd9; rw [← hfr10.2.1 .mm3 (by simp [x64VecScratch])] at hd10
  refine step_vop1 (.xor v4i32) (.vec .mm1, .vec .mm2, ()) .mm1 (clob := maskNone) rfl
    (by simp [tupArgGprs]) (by simp [tupArgVecs, x64VecScratch]) (by simp [x64VecScratch])
    (TRel.cons hb10 (TRel.cons hc10 .nil)) rfl hs10 ?_
  intro s11 hb11 hfr11 hm11
  have ha11 := ha10; rw [← hfr11.2.1 .mm0 (by simp [x64VecScratch])] at ha11
  have hc11 := hc10; rw [← hfr11.2.1 .mm2 (by simp [x64VecScratch])] at hc11
  have hd11 := hd10; rw [← hfr11.2.1 .mm3 (by simp [x64VecScratch])] at hd11
  refine step_vop1 (.rotr v4i32) (.vec .mm1, .imm (splatV 2 25#32), ()) .mm1 (clob := maskNone) rfl
    (by simp [tupArgGprs]) (by simp [tupArgVecs, x64VecScratch]) (by simp [x64VecScratch])
    (TRel.cons hb11 (TRel.cons rfl .nil)) rfl hs11 ?_
  intro s12 hb12 hfr12 hm12
  have ha12 := ha11; rw [← hfr12.2.1 .mm0 (by simp [x64VecScratch])] at ha12
  have hc12 := hc11; rw [← hfr12.2.1 .mm2 (by simp [x64VecScratch])] at hc12
  have hd12 := hd11; rw [← hfr12.2.1 .mm3 (by simp [x64VecScratch])] at hd12
  refine step_vop1 (.shufd v4i32 0x39#8) (.vec .mm1, ()) .mm1 (clob := maskNone) rfl
    (by simp [tupArgGprs]) (by simp [tupArgVecs, x64VecScratch]) (by simp [x64VecScratch])
    (TRel.cons hb12 .nil) ⟨by decide, by decide, rfl⟩ hs12 ?_
  intro s13 hb13 hfr13 hm13
  have ha13 := ha12; rw [← hfr13.2.1 .mm0 (by simp [x64VecScratch])] at ha13
  have hc13 := hc12; rw [← hfr13.2.1 .mm2 (by simp [x64VecScratch])] at hc13
  have hd13 := hd12; rw [← hfr13.2.1 .mm3 (by simp [x64VecScratch])] at hd13
  refine Eventually.done _ ⟨ha13, hb13, hc13, hd13, ?_⟩
  exact hm13.trans (hm12.trans (hm11.trans (hm10.trans (hm9.trans (hm8.trans (hm7.trans
    (hm6.trans (hm5.trans (hm4.trans (hm3.trans (hm2.trans hm1)))))))))))

theorem chachaQrModel_rfc8439_lane0_shufd :
    let initA := mkRow 0x11111111#32 0x10#32 0x20#32 0x30#32
    let initB := mkRow 0x01020304#32 0x11#32 0x21#32 0x31#32
    let initC := mkRow 0x9b8d6f43#32 0x12#32 0x22#32 0x32#32
    let initD := mkRow 0x01234567#32 0x13#32 0x23#32 0x33#32
    let (a', b'shuf, c', d') := chachaQrModel initA initB initC initD
    -- Lane 0 of (a', c', d') and lane 3 of shufd $0x39 b' match RFC 8439 §2.1.1 directly:
    (a'.1.1, b'shuf.2.2, c'.1.1, d'.1.1) = quarterRound 0x11111111#32 0x01020304#32 0x9b8d6f43#32 0x01234567#32 ∧
    -- `shufd $0x39` shifts `b` lanes left (downward by 1 dword) cleanly:
    b'shuf.1.1 = (quarterRound 0x10#32 0x11#32 0x12#32 0x13#32).2.1 ∧
    b'shuf.1.2 = (quarterRound 0x20#32 0x21#32 0x22#32 0x23#32).2.1 ∧
    b'shuf.2.1 = (quarterRound 0x30#32 0x31#32 0x32#32 0x33#32).2.1 := by
  decide

/-! ## 3. `addps`/`subps` on `v4f32` including NaN propagation (`Host.ofLayout`) -/

def floatVecProg : List Directive :=
  (x64Vec.vop (.fadd v4f32) (.vec .mm0, .vec .mm1, ()) (.vec .mm0, ()) .default).get!.1 ++
  (x64Vec.vop (.fsub v4f32) (.vec .mm0, .vec .mm2, ()) (.vec .mm0, ()) .default).get!.1

theorem floatVecProg_small :
    (Kraken.Layout.apply testLayout floatVecProg).sizeBefore floatVecProg.length < 2 ^ 64 := by
  simp only [Kraken.Layout.apply, Kraken.Executable.sizeBefore, Kraken.Layout.size, floatVecProg]
  decide

@[instance_reducible] def floatHost : Host :=
  Host.ofLayout floatVecProg testLayout floatVecProg_small

private theorem unpackFloat_notANumber {x : BitVec 32} (hx : isFloatNaN .s x = true) :
    unpackFloat .s x = .notANumber := by
  dsimp only [isFloatNaN] at hx
  cases hu : unpackFloat .s x with
  | notANumber => rfl
  | infinity _ | zero _ | finite _ _ _ _ => simp [hu, Float.Model.UnpackedFloat.isNaN] at hx

private theorem floatResultWp_of_eval {x y expect : BitVec 32}
    (hna : (Float.Model.UnpackedFloat.add .binary32 (unpackFloat .s x) (unpackFloat .s y)).isNaN = false)
    (hpk : packFloat .s (Float.Model.UnpackedFloat.add .binary32 (unpackFloat .s x) (unpackFloat .s y)) = expect) :
    floatResultWp .s (Float.Model.UnpackedFloat.add .binary32 (unpackFloat .s x) (unpackFloat .s y))
      (fun r => r = expect) := by
  unfold floatResultWp; simp [hna, hpk]

private theorem floatResultWp_sub_of_eval {x y expect : BitVec 32}
    (hna : (Float.Model.UnpackedFloat.sub .binary32 (unpackFloat .s x) (unpackFloat .s y)).isNaN = false)
    (hpk : packFloat .s (Float.Model.UnpackedFloat.sub .binary32 (unpackFloat .s x) (unpackFloat .s y)) = expect) :
    floatResultWp .s (Float.Model.UnpackedFloat.sub .binary32 (unpackFloat .s x) (unpackFloat .s y))
      (fun r => r = expect) := by
  unfold floatResultWp; simp [hna, hpk]

theorem floatVecProg_nan_run {n0 n1 : BitVec 32}
    (hn0 : isFloatNaN .s n0 = true) (hn1 : isFloatNaN .s n1 = true) {s : MachineData}
    (h0 : VecHolds (x64Mach.getVec s .mm0) v4f32 ((0x3f800000#32, n0), (0x40200000#32, 0x40400000#32)))
    (h1 : VecHolds (x64Mach.getVec s .mm1) v4f32 ((0x40000000#32, 0x3f800000#32), (0x3fc00000#32, n1)))
    (h2 : VecHolds (x64Mach.getVec s .mm2) v4f32 ((0x3f000000#32, 0x3f800000#32), (0x3f000000#32, 0x3f800000#32))) :
    x64Mach.Run floatHost 0 s fun st =>
      ∃ res : Val v4f32, VecHolds (x64Mach.getVec st.data .mm0) v4f32 res ∧
        res.1.1 = 0x40200000#32 ∧ isFloatNaN .s res.1.2 = true ∧
        res.2.1 = 0x40600000#32 ∧ isFloatNaN .s res.2.2 = true := by
  have hprog : floatVecProg.IsInfixAt (x64Mach.prog floatHost) 0 :=
    ⟨[], by rw [List.drop_zero, List.append_nil]; rfl⟩
  letI := floatHost
  obtain ⟨haddInf, hsubInf⟩ := hprog.append
  have hf_add0 : floatResultWp .s (Float.Model.UnpackedFloat.add .binary32
      (unpackFloat .s 0x3f800000#32) (unpackFloat .s 0x40000000#32)) (fun r => r = 0x40400000#32) :=
    floatResultWp_of_eval (by decide) (by decide)
  have hf_add2 : floatResultWp .s (Float.Model.UnpackedFloat.add .binary32
      (unpackFloat .s 0x40200000#32) (unpackFloat .s 0x3fc00000#32)) (fun r => r = 0x40800000#32) :=
    floatResultWp_of_eval (by decide) (by decide)
  have hf_sub0 : floatResultWp .s (Float.Model.UnpackedFloat.sub .binary32
      (unpackFloat .s 0x40400000#32) (unpackFloat .s 0x3f000000#32)) (fun r => r = 0x40200000#32) :=
    floatResultWp_sub_of_eval (by decide) (by decide)
  have hf_sub2 : floatResultWp .s (Float.Model.UnpackedFloat.sub .binary32
      (unpackFloat .s 0x40800000#32) (unpackFloat .s 0x3f000000#32)) (fun r => r = 0x40600000#32) :=
    floatResultWp_sub_of_eval (by decide) (by decide)
  have hwp_add : (OpCode.fadd v4f32).wp
      (((0x3f800000#32, n0), (0x40200000#32, 0x40400000#32)),
       ((0x40000000#32, 0x3f800000#32), (0x3fc00000#32, n1)), ())
      (fun rvs => rvs.1.1.1 = 0x40400000#32 ∧ isFloatNaN .s rvs.1.1.2 = true ∧
        rvs.1.2.1 = 0x40800000#32 ∧ isFloatNaN .s rvs.1.2.2 = true) := by
    simp only [OpCode.wp, Ty.isFloatTree, liftFloatRel2, Fmt.format, Bool.and_true, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte]
    refine floatResultWp_mono .s _ (fun r0 hr0 => ?_) hf_add0
    rw [unpackFloat_notANumber hn0]
    refine fun r1 hr1 => floatResultWp_mono .s _ (fun r2 hr2 => ?_) hf_add2
    rw [unpackFloat_notANumber hn1]
    exact fun r3 hr3 => ⟨hr0, hr1, hr2, hr3⟩
  refine x64VecSpec.vop_spec (code := .fadd v4f32) (pas := (.vec .mm0, .vec .mm1, ()))
    (dsts := (.vec .mm0, ())) (vh := .default) (clob := maskNone) rfl
    (by simp [tupArgGprs]) (by simp [tupArgVecs, x64VecScratch]) (by simp [tupDstGprs])
    (by simp [tupDstVecs, x64VecScratch]) (TRel.cons h0 (TRel.cons h1 .nil)) hwp_add haddInf ?_
  rintro s1 ⟨⟨⟨mid, ⟨⟩⟩, ⟨hm0, hm1n, hm2, hm3n⟩, htr1⟩, _⟩ hfr1
  rcases htr1 with _ | ⟨hmid, _⟩
  rcases mid with ⟨⟨m0, m1⟩, ⟨m2, m3⟩⟩
  dsimp only at hm0 hm1n hm2 hm3n
  subst hm0 hm2
  have h2_s1 : VecHolds (x64Mach.getVec s1 .mm2) v4f32 ((0x3f000000#32, 0x3f800000#32), (0x3f000000#32, 0x3f800000#32)) := by
    rw [hfr1.2.1 .mm2 (by simp [tupDstVecs, x64VecScratch])]; exact h2
  have hwp_sub : (OpCode.fsub v4f32).wp
      (((0x40400000#32, m1), (0x40800000#32, m3)),
       ((0x3f000000#32, 0x3f800000#32), (0x3f000000#32, 0x3f800000#32)), ())
      (fun rvs => rvs.1.1.1 = 0x40200000#32 ∧ isFloatNaN .s rvs.1.1.2 = true ∧
        rvs.1.2.1 = 0x40600000#32 ∧ isFloatNaN .s rvs.1.2.2 = true) := by
    simp only [OpCode.wp, Ty.isFloatTree, liftFloatRel2, Fmt.format, Bool.and_true, Bool.not_true,
      Bool.false_eq_true, ↓reduceIte]
    refine floatResultWp_mono .s _ (fun r0 hr0 => ?_) hf_sub0
    rw [unpackFloat_notANumber hm1n]
    refine fun r1 hr1 => floatResultWp_mono .s _ (fun r2 hr2 => ?_) hf_sub2
    rw [unpackFloat_notANumber hm3n]
    exact fun r3 hr3 => ⟨hr0, hr1, hr2, hr3⟩
  refine x64VecSpec.vop_spec (code := .fsub v4f32) (pas := (.vec .mm0, .vec .mm2, ()))
    (dsts := (.vec .mm0, ())) (vh := .default) (clob := maskNone) rfl
    (by simp [tupArgGprs]) (by simp [tupArgVecs, x64VecScratch]) (by simp [tupDstGprs])
    (by simp [tupDstVecs, x64VecScratch]) (TRel.cons hmid (TRel.cons h2_s1 .nil)) hwp_sub hsubInf ?_
  rintro s' ⟨⟨⟨res, ⟨⟩⟩, hprops, htr'⟩, _⟩ _
  rcases htr' with _ | ⟨hres, _⟩
  exact Eventually.done _ ⟨res, hres, hprops⟩

/-! ## 4. `mkpair`/`unpair` pack-unpack bridges (`Host.ofLayout`) -/

def bridgeProg : List Directive :=
  (x64Vec.vop (.mkpair i32 i32) (.gpr .rdi, .gpr .rsi, ()) (.vec .mm0, ()) .default).get!.1 ++
  (x64Vec.vop (.mkpair v2i32 v2i32) (.vec .mm0, .vec .mm1, ()) (.vec .mm2, ()) .default).get!.1 ++
  (x64Vec.vop (.unpair v2i32 v2i32) (.vec .mm2, ()) (.vec .mm3, .vec .mm4, ()) .default).get!.1 ++
  (x64Vec.vop (.unpair i32 i32) (.vec .mm4, ()) (.gpr .rax, .gpr .rdx, ()) .default).get!.1 ++
  (x64Vec.vop (.mkpair v2f32 v2f32) (.vec .mm5, .vec .mm6, ()) (.vec .mm7, ()) .default).get!.1 ++
  (x64Vec.vop (.unpair v2f32 v2f32) (.vec .mm7, ()) (.vec .mm8, .vec .mm9, ()) .default).get!.1

theorem bridgeProg_small :
    (Kraken.Layout.apply testLayout bridgeProg).sizeBefore bridgeProg.length < 2 ^ 64 := by
  simp only [Kraken.Layout.apply, Kraken.Executable.sizeBefore, Kraken.Layout.size, bridgeProg]
  decide

@[instance_reducible] def bridgeHost : Host :=
  Host.ofLayout bridgeProg testLayout bridgeProg_small

theorem bridgeProg_run {a0 a1 : Val i32} {hi : Val v2i32} {f0 f1 : Val v2f32} {s : MachineData}
    (hrdi : GprHolds (x64Mach.getGpr s .rdi) i32 a0)
    (hrsi : GprHolds (x64Mach.getGpr s .rsi) i32 a1)
    (hmm1 : VecHolds (x64Mach.getVec s .mm1) v2i32 hi)
    (hmm5 : VecHolds (x64Mach.getVec s .mm5) v2f32 f0)
    (hmm6 : VecHolds (x64Mach.getVec s .mm6) v2f32 f1) :
    x64Mach.Run bridgeHost 0 s fun st =>
      VecHolds (x64Mach.getVec st.data .mm3) v2i32 (a0, a1) ∧
      GprHolds (x64Mach.getGpr st.data .rax) i32 hi.1 ∧
      GprHolds (x64Mach.getGpr st.data .rdx) i32 hi.2 ∧
      VecHolds (x64Mach.getVec st.data .mm8) v2f32 f0 ∧
      VecHolds (x64Mach.getVec st.data .mm9) v2f32 f1 := by
  have hprog : bridgeProg.IsInfixAt (x64Mach.prog bridgeHost) 0 :=
    ⟨[], by rw [List.drop_zero, List.append_nil]; rfl⟩
  letI := bridgeHost
  obtain ⟨h0, hc5⟩ := hprog.append; obtain ⟨h0, hc4⟩ := h0.append
  obtain ⟨h0, hc3⟩ := h0.append; obtain ⟨h0, hc2⟩ := h0.append
  obtain ⟨hc0, hc1⟩ := h0.append
  refine x64VecSpec.vop_spec (code := .mkpair i32 i32) (pas := (.gpr .rdi, .gpr .rsi, ()))
    (dsts := (.vec .mm0, ())) (vh := .default) (clob := maskAll) rfl
    (by simp [tupArgGprs, x64Scratch]) (by simp [tupArgVecs]) (by simp [tupDstGprs])
    (by simp [tupDstVecs, x64VecScratch]) (TRel.cons hrdi (TRel.cons hrsi .nil)) rfl hc0 ?_
  rintro s1 ⟨⟨⟨r1, ⟨⟩⟩, heq1, htr1⟩, _⟩ hfr1
  obtain rfl : r1 = (a0, a1) := (Prod.mk.inj heq1).1.symm
  rcases htr1 with _ | ⟨hmm0_1, _⟩
  have hmm1_1 : VecHolds (x64Mach.getVec s1 .mm1) v2i32 hi := by
    rw [hfr1.2.1 .mm1 (by simp [tupDstVecs, x64VecScratch])]; exact hmm1
  have hmm5_1 : VecHolds (x64Mach.getVec s1 .mm5) v2f32 f0 := by
    rw [hfr1.2.1 .mm5 (by simp [tupDstVecs, x64VecScratch])]; exact hmm5
  have hmm6_1 : VecHolds (x64Mach.getVec s1 .mm6) v2f32 f1 := by
    rw [hfr1.2.1 .mm6 (by simp [tupDstVecs, x64VecScratch])]; exact hmm6
  refine x64VecSpec.vop_spec (code := .mkpair v2i32 v2i32) (pas := (.vec .mm0, .vec .mm1, ()))
    (dsts := (.vec .mm2, ())) (vh := .default) (clob := maskNone) rfl
    (by simp [tupArgGprs]) (by simp [tupArgVecs, x64VecScratch]) (by simp [tupDstGprs])
    (by simp [tupDstVecs, x64VecScratch]) (TRel.cons hmm0_1 (TRel.cons hmm1_1 .nil)) rfl hc1 ?_
  rintro s2 ⟨⟨⟨r2, ⟨⟩⟩, heq2, htr2⟩, _⟩ hfr2
  obtain rfl : r2 = ((a0, a1), hi) := (Prod.mk.inj heq2).1.symm
  rcases htr2 with _ | ⟨hmm2_2, _⟩
  have hmm5_2 : VecHolds (x64Mach.getVec s2 .mm5) v2f32 f0 := by
    rw [hfr2.2.1 .mm5 (by simp [tupDstVecs, x64VecScratch])]; exact hmm5_1
  have hmm6_2 : VecHolds (x64Mach.getVec s2 .mm6) v2f32 f1 := by
    rw [hfr2.2.1 .mm6 (by simp [tupDstVecs, x64VecScratch])]; exact hmm6_1
  refine x64VecSpec.vop_spec (code := .unpair v2i32 v2i32) (pas := (.vec .mm2, ()))
    (dsts := (.vec .mm3, .vec .mm4, ())) (vh := .default) (clob := maskNone) rfl
    (by simp [tupArgGprs]) (by simp [tupArgVecs, x64VecScratch]) (by simp [tupDstGprs])
    (by simp [tupDstVecs, x64VecScratch]) (TRel.cons hmm2_2 .nil) rfl hc2 ?_
  rintro s3 ⟨⟨⟨ra3, rb3, ⟨⟩⟩, heq3, htr3⟩, _⟩ hfr3
  have heq3' := Prod.mk.inj heq3
  have hr3a : ra3 = (a0, a1) := heq3'.1.symm
  have hr3b : rb3 = hi := (Prod.mk.inj heq3'.2).1.symm
  rcases htr3 with _ | ⟨hmm3_3, _ | ⟨hmm4_3, _⟩⟩
  rw [hr3a] at hmm3_3; rw [hr3b] at hmm4_3
  change x64Mach.PArgHolds s3 (i32.pair i32) (.vec .mm4) hi at hmm4_3
  have hmm5_3 : VecHolds (x64Mach.getVec s3 .mm5) v2f32 f0 := by
    rw [hfr3.2.1 .mm5 (by simp [tupDstVecs, x64VecScratch])]; exact hmm5_2
  have hmm6_3 : VecHolds (x64Mach.getVec s3 .mm6) v2f32 f1 := by
    rw [hfr3.2.1 .mm6 (by simp [tupDstVecs, x64VecScratch])]; exact hmm6_2
  refine x64VecSpec.vop_spec (code := .unpair i32 i32) (pas := (.vec .mm4, ()))
    (dsts := (.gpr .rax, .gpr .rdx, ())) (vh := .default) (clob := maskAll) rfl
    (by simp [tupArgGprs]) (by simp [tupArgVecs, x64VecScratch]) (by simp [tupDstGprs, x64Scratch])
    (by simp [tupDstVecs]) (TRel.cons hmm4_3 .nil) rfl hc3 ?_
  rintro s4 ⟨⟨⟨ra4, rb4, ⟨⟩⟩, heq4, htr4⟩, _⟩ hfr4
  have heq4' := Prod.mk.inj heq4
  have hr4a : ra4 = hi.1 := heq4'.1.symm
  have hr4b : rb4 = hi.2 := (Prod.mk.inj heq4'.2).1.symm
  rcases htr4 with _ | ⟨hrax4, _ | ⟨hrdx4, _⟩⟩
  rw [hr4a] at hrax4; rw [hr4b] at hrdx4
  have hmm3_4 : VecHolds (x64Mach.getVec s4 .mm3) v2i32 (a0, a1) := by
    rw [hfr4.2.1 .mm3 (by simp [tupDstVecs, x64VecScratch])]; exact hmm3_3
  have hmm5_4 : VecHolds (x64Mach.getVec s4 .mm5) v2f32 f0 := by
    rw [hfr4.2.1 .mm5 (by simp [tupDstVecs, x64VecScratch])]; exact hmm5_3
  have hmm6_4 : VecHolds (x64Mach.getVec s4 .mm6) v2f32 f1 := by
    rw [hfr4.2.1 .mm6 (by simp [tupDstVecs, x64VecScratch])]; exact hmm6_3
  refine x64VecSpec.vop_spec (code := .mkpair v2f32 v2f32) (pas := (.vec .mm5, .vec .mm6, ()))
    (dsts := (.vec .mm7, ())) (vh := .default) (clob := maskNone) rfl
    (by simp [tupArgGprs]) (by simp [tupArgVecs, x64VecScratch]) (by simp [tupDstGprs])
    (by simp [tupDstVecs, x64VecScratch]) (TRel.cons hmm5_4 (TRel.cons hmm6_4 .nil)) rfl hc4 ?_
  rintro s5 ⟨⟨⟨r5, ⟨⟩⟩, heq5, htr5⟩, _⟩ hfr5
  obtain rfl : r5 = (f0, f1) := (Prod.mk.inj heq5).1.symm
  rcases htr5 with _ | ⟨hmm7_5, _⟩
  change x64Mach.PArgHolds s5 (v2f32.pair v2f32) (.vec .mm7) (f0, f1) at hmm7_5
  have hmm3_5 : VecHolds (x64Mach.getVec s5 .mm3) v2i32 (a0, a1) := by
    rw [hfr5.2.1 .mm3 (by simp [tupDstVecs, x64VecScratch])]; exact hmm3_4
  have hrax5 : GprHolds (x64Mach.getGpr s5 .rax) i32 hi.1 := by
    rw [hfr5.1 .rax (by simp [tupDstGprs, x64Scratch])]; exact hrax4
  have hrdx5 : GprHolds (x64Mach.getGpr s5 .rdx) i32 hi.2 := by
    rw [hfr5.1 .rdx (by simp [tupDstGprs, x64Scratch])]; exact hrdx4
  refine x64VecSpec.vop_spec (code := .unpair v2f32 v2f32) (pas := (.vec .mm7, ()))
    (dsts := (.vec .mm8, .vec .mm9, ())) (vh := .default) (clob := maskNone) rfl
    (by simp [tupArgGprs]) (by simp [tupArgVecs, x64VecScratch]) (by simp [tupDstGprs])
    (by simp [tupDstVecs, x64VecScratch]) (TRel.cons hmm7_5 .nil) rfl hc5 ?_
  rintro s6 ⟨⟨⟨ra6, rb6, ⟨⟩⟩, heq6, htr6⟩, _⟩ hfr6
  have heq6' := Prod.mk.inj heq6
  have hr6a : ra6 = f0 := heq6'.1.symm
  have hr6b : rb6 = f1 := (Prod.mk.inj heq6'.2).1.symm
  rcases htr6 with _ | ⟨hmm8_6, _ | ⟨hmm9_6, _⟩⟩
  rw [hr6a] at hmm8_6; rw [hr6b] at hmm9_6
  exact Eventually.done _
    ⟨by rw [hfr6.2.1 .mm3 (by simp [tupDstVecs, x64VecScratch])]; exact hmm3_5,
     by rw [hfr6.1 .rax (by simp [tupDstGprs, x64Scratch])]; exact hrax5,
     by rw [hfr6.1 .rdx (by simp [tupDstGprs, x64Scratch])]; exact hrdx5,
     hmm8_6, hmm9_6⟩

/-! ## 5. Unaligned stack-slot & memory round-trips (`Host.ofLayout`) -/

def unalignedProg : List Directive :=
  x64Vec.vslotSt .w64 0 .mm0 ++ x64Vec.vslotLd .w64 .mm1 0 ++
  x64Vec.vslotSt .w128 1 .mm2 ++ x64Vec.vslotLd .w128 .mm3 1 ++
  x64Vec.vslotSt .w512 (2 ^ 29) .mm4 ++ x64Vec.vslotLd .w512 .mm5 (2 ^ 29) ++
  (x64Vec.vstore v4i32 .mm6 (.baseDisp .rbx 2147483648)).get!.1 ++
  (x64Vec.vload v4i32 .mm7 (.baseDisp .rbx 2147483648)).get!.1

theorem unalignedProg_small :
    (Kraken.Layout.apply testLayout unalignedProg).sizeBefore unalignedProg.length < 2 ^ 64 := by
  simp only [Kraken.Layout.apply, Kraken.Executable.sizeBefore, Kraken.Layout.size, unalignedProg]
  decide

@[instance_reducible] def unalignedHost : Host :=
  Host.ofLayout unalignedProg testLayout unalignedProg_small

theorem unalignedProg_run {v64 : Val v2i32} {v128 : Val v4i32} {v512 : Val v16i32}
    {memInit memVal : Val v4i32} {s : MachineData} {R : Mem 64 → Prop}
    (hspUnalign : (x64Mach.getGpr s x64Frame.sp) &&& 0xF#64 = 1#64)
    (haddrUnalign : (x64Mach.getGpr s .rbx + 2147483648#64) &&& 0xF#64 = 3#64)
    (hm0 : VecHolds (x64Mach.getVec s .mm0) v2i32 v64)
    (hm2 : VecHolds (x64Mach.getVec s .mm2) v4i32 v128)
    (hm4 : VecHolds (x64Mach.getVec s .mm4) v16i32 v512)
    (hm6 : VecHolds (x64Mach.getVec s .mm6) v4i32 memVal)
    (hmem : s.dmem =⋆
      region (x64Mach.getGpr s x64Frame.sp) 8 ⋆
      region (x64Mach.getGpr s x64Frame.sp + 8#64) 16 ⋆
      region (x64Mach.getGpr s x64Frame.sp + BitVec.ofNat 64 (8 * 2 ^ 29)) 64 ⋆
      cell (x64Mach.getGpr s .rbx + 2147483648#64) memInit ⋆ R) :
    x64Mach.Run unalignedHost 0 s fun st =>
      VecHolds (x64Mach.getVec st.data .mm1) v2i32 v64 ∧
      VecHolds (x64Mach.getVec st.data .mm3) v4i32 v128 ∧
      VecHolds (x64Mach.getVec st.data .mm5) v16i32 v512 ∧
      VecHolds (x64Mach.getVec st.data .mm7) v4i32 memVal ∧
      (x64Mach.getGpr s x64Frame.sp) &&& 0xF#64 = 1#64 ∧
      (x64Mach.getGpr s .rbx + 2147483648#64) &&& 0xF#64 = 3#64 := by
  have hprog : unalignedProg.IsInfixAt (x64Mach.prog unalignedHost) 0 :=
    ⟨[], by rw [List.drop_zero, List.append_nil]; rfl⟩
  letI := unalignedHost
  obtain ⟨h0, hc7⟩ := hprog.append; obtain ⟨h0, hc6⟩ := h0.append
  obtain ⟨h0, hc5⟩ := h0.append; obtain ⟨h0, hc4⟩ := h0.append
  obtain ⟨h0, hc3⟩ := h0.append; obtain ⟨h0, hc2⟩ := h0.append
  obtain ⟨hc0, hc1⟩ := h0.append
  -- Step 0–1: vslotSt .w64 0 .mm0 ; vslotLd .w64 .mm1 0 at unaligned %rsp
  have hmem0 : s.dmem =⋆
      region (x64Mach.getGpr s x64Frame.sp + BitVec.ofNat 64 (8 * 0)) (8 * SlotWidth.w64.slots) ⋆
      (region (x64Mach.getGpr s x64Frame.sp + 8#64) 16 ⋆
        region (x64Mach.getGpr s x64Frame.sp + BitVec.ofNat 64 (8 * 2 ^ 29)) 64 ⋆
        cell (x64Mach.getGpr s .rbx + 2147483648#64) memInit ⋆ R) := by
    rw [show BitVec.ofNat 64 (8 * 0) = 0#64 from rfl, BitVec.add_zero,
      show 8 * SlotWidth.w64.slots = 8 from rfl]
    exact sep_cast hmem (by ac_rfl)
  refine x64VecSpec.vslotSt_spec (by simp [x64VecScratch]) trivial hmem0 hc0 ?_
  intro s1 hmem1 hfr1
  have hsp1 : x64Mach.getGpr s1 x64Frame.sp = x64Mach.getGpr s x64Frame.sp :=
    hfr1.1 x64Frame.sp (by simp [x64Scratch])
  have hmem1' : s1.dmem =⋆
      array64 (x64Mach.getGpr s1 x64Frame.sp + BitVec.ofNat 64 (8 * 0))
        (unpackSlotWords .w64 (x64Mach.getVec s .mm0)) ⋆
      (region (x64Mach.getGpr s x64Frame.sp + 8#64) 16 ⋆
        region (x64Mach.getGpr s x64Frame.sp + BitVec.ofNat 64 (8 * 2 ^ 29)) 64 ⋆
        cell (x64Mach.getGpr s .rbx + 2147483648#64) memInit ⋆ R) := by
    rw [hsp1]; exact hmem1
  refine x64VecSpec.vslotLd_spec (by simp [x64VecScratch]) trivial hmem1' hc1 ?_
  rintro s2 ⟨hld1, hdmem2⟩ hfr2
  have hm1_2 : VecHolds (x64Mach.getVec s2 .mm1) v2i32 v64 :=
    VecHolds.of_setWidth_eq (by decide) hld1 hm0
  have hsp2 : x64Mach.getGpr s2 x64Frame.sp = x64Mach.getGpr s x64Frame.sp := by
    rw [hfr2.1 x64Frame.sp (by simp [x64Scratch]), hsp1]
  have hm2_2 : VecHolds (x64Mach.getVec s2 .mm2) v4i32 v128 := by
    rw [hfr2.2.1 .mm2 (by simp [x64VecScratch]), hfr1.2.1 .mm2 (by simp [x64VecScratch])]; exact hm2
  -- Step 2–3: vslotSt .w128 1 .mm2 ; vslotLd .w128 .mm3 1 at unaligned %rsp + 8
  have hmem2 : s2.dmem =⋆
      region (x64Mach.getGpr s2 x64Frame.sp + BitVec.ofNat 64 (8 * 1)) (8 * SlotWidth.w128.slots) ⋆
      (array64 (x64Mach.getGpr s x64Frame.sp) (unpackSlotWords .w64 (x64Mach.getVec s .mm0)) ⋆
        region (x64Mach.getGpr s x64Frame.sp + BitVec.ofNat 64 (8 * 2 ^ 29)) 64 ⋆
        cell (x64Mach.getGpr s .rbx + 2147483648#64) memInit ⋆ R) := by
    change s2.dmem = s1.dmem at hdmem2
    rw [hdmem2]
    rw [hsp1, show BitVec.ofNat 64 (8 * 0) = 0#64 from rfl, BitVec.add_zero] at hmem1'
    rw [hsp2, show BitVec.ofNat 64 (8 * 1) = 8#64 from rfl]
    exact sep_cast hmem1' (by ac_rfl)
  refine x64VecSpec.vslotSt_spec (by simp [x64VecScratch]) trivial hmem2 hc2 ?_
  intro s3 hmem3 hfr3
  have hsp3 : x64Mach.getGpr s3 x64Frame.sp = x64Mach.getGpr s x64Frame.sp := by
    rw [hfr3.1 x64Frame.sp (by simp [x64Scratch]), hsp2]
  have hm1_3 : VecHolds (x64Mach.getVec s3 .mm1) v2i32 v64 := by
    rw [hfr3.2.1 .mm1 (by simp [x64VecScratch])]; exact hm1_2
  have hmem3' : s3.dmem =⋆
      array64 (x64Mach.getGpr s3 x64Frame.sp + BitVec.ofNat 64 (8 * 1))
        (unpackSlotWords .w128 (x64Mach.getVec s2 .mm2)) ⋆
      (array64 (x64Mach.getGpr s x64Frame.sp) (unpackSlotWords .w64 (x64Mach.getVec s .mm0)) ⋆
        region (x64Mach.getGpr s x64Frame.sp + BitVec.ofNat 64 (8 * 2 ^ 29)) 64 ⋆
        cell (x64Mach.getGpr s .rbx + 2147483648#64) memInit ⋆ R) := by
    change (array64 (x64Mach.getGpr s2 x64Frame.sp + BitVec.ofNat 64 (8 * 1))
        (unpackSlotWords .w128 (x64Mach.getVec s2 .mm2)) ⋆
      (array64 (x64Mach.getGpr s x64Frame.sp) (unpackSlotWords .w64 (x64Mach.getVec s .mm0)) ⋆
        region (x64Mach.getGpr s x64Frame.sp + BitVec.ofNat 64 (8 * 2 ^ 29)) 64 ⋆
        cell (x64Mach.getGpr s .rbx + 2147483648#64) memInit ⋆ R)) s3.dmem at hmem3
    rw [hsp2] at hmem3; rw [hsp3]; exact hmem3
  refine x64VecSpec.vslotLd_spec (by simp [x64VecScratch]) trivial hmem3' hc3 ?_
  rintro s4 ⟨hld3, hdmem4⟩ hfr4
  have hm3_4 : VecHolds (x64Mach.getVec s4 .mm3) v4i32 v128 :=
    VecHolds.of_setWidth_eq (by decide) hld3 hm2_2
  have hsp4 : x64Mach.getGpr s4 x64Frame.sp = x64Mach.getGpr s x64Frame.sp := by
    rw [hfr4.1 x64Frame.sp (by simp [x64Scratch]), hsp3]
  have hm1_4 : VecHolds (x64Mach.getVec s4 .mm1) v2i32 v64 := by
    rw [hfr4.2.1 .mm1 (by simp [x64VecScratch])]; exact hm1_3
  have hm4_4 : VecHolds (x64Mach.getVec s4 .mm4) v16i32 v512 := by
    rw [hfr4.2.1 .mm4 (by simp [x64VecScratch]), hfr3.2.1 .mm4 (by simp [x64VecScratch]),
      hfr2.2.1 .mm4 (by simp [x64VecScratch]), hfr1.2.1 .mm4 (by simp [x64VecScratch])]; exact hm4
  -- Step 4–5: vslotSt .w512 (2 ^ 29) .mm4 ; vslotLd .w512 .mm5 (2 ^ 29)
  have hmem4 : s4.dmem =⋆
      region (x64Mach.getGpr s4 x64Frame.sp + BitVec.ofNat 64 (8 * 2 ^ 29)) (8 * SlotWidth.w512.slots) ⋆
      (array64 (x64Mach.getGpr s x64Frame.sp + 8#64) (unpackSlotWords .w128 (x64Mach.getVec s2 .mm2)) ⋆
        array64 (x64Mach.getGpr s x64Frame.sp) (unpackSlotWords .w64 (x64Mach.getVec s .mm0)) ⋆
        cell (x64Mach.getGpr s .rbx + 2147483648#64) memInit ⋆ R) := by
    change s4.dmem = s3.dmem at hdmem4
    rw [hdmem4]
    rw [hsp3, show BitVec.ofNat 64 (8 * 1) = 8#64 from rfl] at hmem3'
    rw [hsp4]
    exact sep_cast hmem3' (by ac_rfl)
  refine x64VecSpec.vslotSt_spec (by simp [x64VecScratch]) trivial hmem4 hc4 ?_
  intro s5 hmem5 hfr5
  have hsp5 : x64Mach.getGpr s5 x64Frame.sp = x64Mach.getGpr s x64Frame.sp := by
    rw [hfr5.1 x64Frame.sp (by simp [x64Scratch]), hsp4]
  have hmem5' : s5.dmem =⋆
      array64 (x64Mach.getGpr s5 x64Frame.sp + BitVec.ofNat 64 (8 * 2 ^ 29))
        (unpackSlotWords .w512 (x64Mach.getVec s4 .mm4)) ⋆
      (array64 (x64Mach.getGpr s x64Frame.sp + 8#64) (unpackSlotWords .w128 (x64Mach.getVec s2 .mm2)) ⋆
        array64 (x64Mach.getGpr s x64Frame.sp) (unpackSlotWords .w64 (x64Mach.getVec s .mm0)) ⋆
        cell (x64Mach.getGpr s .rbx + 2147483648#64) memInit ⋆ R) := by
    change (array64 (x64Mach.getGpr s4 x64Frame.sp + BitVec.ofNat 64 (8 * 2 ^ 29))
        (unpackSlotWords .w512 (x64Mach.getVec s4 .mm4)) ⋆
      (array64 (x64Mach.getGpr s x64Frame.sp + 8#64) (unpackSlotWords .w128 (x64Mach.getVec s2 .mm2)) ⋆
        array64 (x64Mach.getGpr s x64Frame.sp) (unpackSlotWords .w64 (x64Mach.getVec s .mm0)) ⋆
        cell (x64Mach.getGpr s .rbx + 2147483648#64) memInit ⋆ R)) s5.dmem at hmem5
    rw [hsp4] at hmem5; rw [hsp5]; exact hmem5
  refine x64VecSpec.vslotLd_spec (by simp [x64VecScratch]) trivial hmem5' hc5 ?_
  rintro s6 ⟨hld5, hdmem6⟩ hfr6
  have hm5_6 : VecHolds (x64Mach.getVec s6 .mm5) v16i32 v512 :=
    VecHolds.of_setWidth_eq (by decide) hld5 hm4_4
  have hm1_6 : VecHolds (x64Mach.getVec s6 .mm1) v2i32 v64 := by
    rw [hfr6.2.1 .mm1 (by simp [x64VecScratch]), hfr5.2.1 .mm1 (by simp [x64VecScratch])]; exact hm1_4
  have hm3_6 : VecHolds (x64Mach.getVec s6 .mm3) v4i32 v128 := by
    rw [hfr6.2.1 .mm3 (by simp [x64VecScratch]), hfr5.2.1 .mm3 (by simp [x64VecScratch])]; exact hm3_4
  have hm6_6 : VecHolds (x64Mach.getVec s6 .mm6) v4i32 memVal := by
    rw [hfr6.2.1 .mm6 (by simp [x64VecScratch]), hfr5.2.1 .mm6 (by simp [x64VecScratch]),
      hfr4.2.1 .mm6 (by simp [x64VecScratch]), hfr3.2.1 .mm6 (by simp [x64VecScratch]),
      hfr2.2.1 .mm6 (by simp [x64VecScratch]), hfr1.2.1 .mm6 (by simp [x64VecScratch])]; exact hm6
  have hrbx6 : x64Mach.getGpr s6 .rbx = x64Mach.getGpr s .rbx := by
    rw [hfr6.1 .rbx (by simp [x64Scratch]), hfr5.1 .rbx (by simp [x64Scratch]),
      hfr4.1 .rbx (by simp [x64Scratch]), hfr3.1 .rbx (by simp [x64Scratch]),
      hfr2.1 .rbx (by simp [x64Scratch]), hfr1.1 .rbx (by simp [x64Scratch])]
  -- Step 6–7: unaligned vstore/vload at `[rbx + 2147483648]`
  have hmem6 : (cell (x64Mach.getGpr s6 .rbx + 2147483648#64) memInit ⋆
      (array64 (x64Mach.getGpr s x64Frame.sp + BitVec.ofNat 64 (8 * 2 ^ 29))
        (unpackSlotWords .w512 (x64Mach.getVec s4 .mm4)) ⋆
        array64 (x64Mach.getGpr s x64Frame.sp + 8#64) (unpackSlotWords .w128 (x64Mach.getVec s2 .mm2)) ⋆
        array64 (x64Mach.getGpr s x64Frame.sp) (unpackSlotWords .w64 (x64Mach.getVec s .mm0)) ⋆ R)) s6.dmem := by
    change s6.dmem = s5.dmem at hdmem6
    rw [hdmem6, hrbx6]
    rw [hsp5] at hmem5'
    exact sep_cast hmem5' (by ac_rfl)
  obtain ⟨hsok, hstored⟩ := store_cell (t := v4i32) memVal (by decide) hmem6
  have ha_eval6 : AddrArg.eval (x64Mach.getGpr s6) (.baseDisp .rbx 2147483648) =
      x64Mach.getGpr s6 .rbx + 2147483648#64 := rfl
  rw [← ha_eval6] at hsok
  refine x64VecSpec.vstore_spec (clob := maskNone) rfl (by simp [AddrArg.regs, x64Scratch])
    (by simp [x64VecScratch]) hm6_6 hsok hc6 ?_
  intro s7 hmem7 hfr7
  have hrbx7 : x64Mach.getGpr s7 .rbx = x64Mach.getGpr s6 .rbx := hfr7.1 .rbx (by simp [x64Scratch])
  have hmem7' : (cell (AddrArg.eval (x64Mach.getGpr s7) (.baseDisp .rbx 2147483648)) memVal ⋆
      (array64 (x64Mach.getGpr s x64Frame.sp + BitVec.ofNat 64 (8 * 2 ^ 29))
        (unpackSlotWords .w512 (x64Mach.getVec s4 .mm4)) ⋆
        array64 (x64Mach.getGpr s x64Frame.sp + 8#64) (unpackSlotWords .w128 (x64Mach.getVec s2 .mm2)) ⋆
        array64 (x64Mach.getGpr s x64Frame.sp) (unpackSlotWords .w64 (x64Mach.getVec s .mm0)) ⋆ R)) s7.dmem := by
    change s7.dmem = _ at hmem7
    rw [hmem7, ha_eval6, show AddrArg.eval (x64Mach.getGpr s7) (.baseDisp .rbx 2147483648) =
      x64Mach.getGpr s6 .rbx + 2147483648#64 by rw [AddrArg.eval, hrbx7]; rfl]
    exact hstored
  refine x64VecSpec.vload_spec (clob := maskNone) rfl (by simp [x64VecScratch])
    (by simp [AddrArg.regs, x64Scratch]) (loadVal_cell (by decide) hmem7') hc7 ?_
  rintro s8 ⟨hm7_8, _⟩ hfr8
  exact Eventually.done _
    ⟨by rw [hfr8.2.1 .mm1 (by simp [x64VecScratch]), hfr7.2.1 .mm1 (by simp [x64VecScratch])]; exact hm1_6,
     by rw [hfr8.2.1 .mm3 (by simp [x64VecScratch]), hfr7.2.1 .mm3 (by simp [x64VecScratch])]; exact hm3_6,
     by rw [hfr8.2.1 .mm5 (by simp [x64VecScratch]), hfr7.2.1 .mm5 (by simp [x64VecScratch])]; exact hm5_6,
     hm7_8, hspUnalign, haddrUnalign⟩

/-! ## 6. Standard-axiom audit -/

#print axioms LeanQbe.T.Amd64.x64VecSpec
#print axioms LeanQbe.T.Amd64.x64Vmov_noLab
#print axioms LeanQbe.T.Amd64.x64Vmovi_noLab
#print axioms LeanQbe.T.Amd64.x64VslotSt_noLab
#print axioms LeanQbe.T.Amd64.x64VslotLd_noLab
#print axioms LeanQbe.T.Amd64.x64Vload_noLab
#print axioms LeanQbe.T.Amd64.x64Vstore_noLab
#print axioms LeanQbe.T.Amd64.x64Vop_noLab
#print axioms chachaQrProg_run
#print axioms floatVecProg_nan_run
#print axioms bridgeProg_run
#print axioms unalignedProg_run

end LeanQbeTest.T.Amd64VecTest