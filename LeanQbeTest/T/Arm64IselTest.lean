module

public import LeanQbe.T.Arm64.IselLemmas4
public import LeanQbe.T.Arm64.Targ
public import LeanQbe.T.Arm64.Frame
public import LeanQbe.T.OpsLemmas
public import LeanQbe.T.Main
public import LeanQbe.T.Examples.Bignum
import Kraken.AArch64.Parser
meta import LeanQbe.T.Arm64.Isel
meta import LeanQbe.T.Arm64.Frame
meta import LeanQbe.T.Main
meta import LeanQbe.T.Examples.Bignum
meta import LeanQbe.T.Legal

/-!
# AArch64 Scalar GprIsa + GprTarget Test & Witness Suite (`T9`)

Standalone downstream module verifying:
1. Kernel `rfl` checks for `armGpr.supportsScalarOp` across `[8, 16, 32, 64]`, `.bool`, `bswap`,
   bit-counts, `popcnt = false`, funnel shifts, carry/borrow chains, `umulw`/`smulw`, `udiv0`/`sdiv0`,
   and `VariantHint` lowering behavior.
2. Concrete `Host.ofLayout` execution witnesses via `armGprSpec` covering:
   - `udiv0` / `sdiv0` on `/ 0` and `INT_MIN / -1`
   - `clz` / `cls` / `rbit` / `ctz`
   - multi-word `addc` (`.cs` carry chain) and `subb` (`.cc` borrow chain) + `clearFlags`
   - `umulw` / `smulw` (including destination aliasing), `fshl` / `fshr` (`.imm`, `.gpr`, and shift-by-0),
     and branchless `select` (`CSEL`)
   - sub-word `8`/`16` shifts, `cmp`, and `sdiv` with non-zero upper garbage bits
   - `.SP` corner cases (`movi`, `mov`, `setcc`, `store` `.bool .flag` & `load` at unaligned `SP % 16 ≠ 0`,
     and `jnzGpr .SP`) plus `jnzGpr` `.bool false` with arbitrary upper garbage bits `8..63`
3. Complete standard-axiom audit (`[propext, Classical.choice, Quot.sound]` only) for `armGprSpec`,
   all 10 `NoLab` theorems, and every witness theorem.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbeTest.T.Arm64IselTest

open LeanQbe.T
open LeanQbe.T.Arm64
open Kraken.AArch64.Parser

/-! ## 1. Kernel `rfl` `supportsScalarOp` and `VariantHint` checks -/

theorem armGpr_supports_rfl
    (u1_8 : Tup (Arg (fun _ => Unit)) [i8])
    (u1_16 : Tup (Arg (fun _ => Unit)) [i16])
    (u1_32 : Tup (Arg (fun _ => Unit)) [i32])
    (u1_64 : Tup (Arg (fun _ => Unit)) [i64])
    (u2_8 : Tup (Arg (fun _ => Unit)) [i8, i8])
    (u2_16 : Tup (Arg (fun _ => Unit)) [i16, i16])
    (u2_32 : Tup (Arg (fun _ => Unit)) [i32, i32])
    (u2_64 : Tup (Arg (fun _ => Unit)) [i64, i64])
    (ub2 : Tup (Arg (fun _ => Unit)) [.bool, .bool])
    (ub1 : Tup (Arg (fun _ => Unit)) [.bool])
    (uc3_32 : Tup (Arg (fun _ => Unit)) [i32, i32, .bool])
    (uc3_64 : Tup (Arg (fun _ => Unit)) [i64, i64, .bool])
    (uf3_32 : Tup (Arg (fun _ => Unit)) [i32, i32, i32])
    (uf3_64 : Tup (Arg (fun _ => Unit)) [i64, i64, i64])
    (us_64 : Tup (Arg (fun _ => Unit)) [.bool, i64, i64]) :
    armGpr.supportsScalarOp (.copy i8) u1_8 = true ∧
    armGpr.supportsScalarOp (.add i16) u2_16 = true ∧
    armGpr.supportsScalarOp (.udiv0 32) u2_32 = true ∧
    armGpr.supportsScalarOp (.sdiv0 64) u2_64 = true ∧
    armGpr.supportsScalarOp (.select i8) (.imm false, .imm 1#8, .imm 2#8, ()) = true ∧
    armGpr.supportsScalarOp (.select i64) us_64 = true ∧
    armGpr.supportsScalarOp (.cmp .slt i16) u2_16 = true ∧
    armGpr.supportsScalarOp (.ofBool 8) ub1 = true ∧
    armGpr.supportsScalarOp (.bitcast i32 (.bits 32) rfl) u1_32 = true ∧
    armGpr.supportsScalarOp (.xor .bool) ub2 = true ∧
    armGpr.supportsScalarOp (.not .bool) ub1 = true ∧
    armGpr.supportsScalarOp (.bswap i8) u1_8 = false ∧
    armGpr.supportsScalarOp (.bswap i16) u1_16 = true ∧
    armGpr.supportsScalarOp (.bswap i32) u1_32 = true ∧
    armGpr.supportsScalarOp (.bswap i64) u1_64 = true ∧
    armGpr.supportsScalarOp (.clz 16) u1_16 = false ∧
    armGpr.supportsScalarOp (.clz 32) u1_32 = true ∧
    armGpr.supportsScalarOp (.cls 64) u1_64 = true ∧
    armGpr.supportsScalarOp (.rbit 32) u1_32 = true ∧
    armGpr.supportsScalarOp (.ctz 64) u1_64 = true ∧
    armGpr.supportsScalarOp (.popcnt 32) u1_32 = false ∧
    armGpr.supportsScalarOp (.popcnt 64) u1_64 = false ∧
    armGpr.supportsScalarOp (.fshl 16) (.imm 0#16, .imm 0#16, .imm 0#16, ()) = false ∧
    armGpr.supportsScalarOp (.fshl 32) uf3_32 = true ∧
    armGpr.supportsScalarOp (.fshr 64) uf3_64 = true ∧
    armGpr.supportsScalarOp (.addc 32) uc3_32 = true ∧
    armGpr.supportsScalarOp (.subb 64) uc3_64 = true ∧
    armGpr.supportsScalarOp (.umulw 32) u2_32 = true ∧
    armGpr.supportsScalarOp (.smulw 64) u2_64 = true ∧
    armGpr.supportsScalarOp (.shl i8) u2_8 = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem armGpr_variantHint_rfl :
    armGpr.op (.add i64) (.gpr (.reg .X1), .gpr (.reg .X2), ()) (.gpr (.reg .X0), ()) .decInc =
      armGpr.op (.add i64) (.gpr (.reg .X1), .gpr (.reg .X2), ()) (.gpr (.reg .X0), ()) .default ∧
    armGpr.op (.sub i64) (.gpr (.reg .X1), .gpr (.reg .X2), ()) (.gpr (.reg .X0), ()) (.disp 16) =
      armGpr.op (.sub i64) (.gpr (.reg .X1), .gpr (.reg .X2), ()) (.gpr (.reg .X0), ()) .default ∧
    armGpr.op (.addc 64) (.gpr (.reg .X1), .gpr (.reg .X2), .flag .cs, ()) (.gpr (.reg .X0), .flag .cs, ()) .adcx = none ∧
    armGpr.op (.addc 64) (.gpr (.reg .X1), .gpr (.reg .X2), .flag .cs, ()) (.gpr (.reg .X0), .flag .cs, ()) (.disp 8) = none ∧
    armGpr.op (.subb 64) (.gpr (.reg .X1), .gpr (.reg .X2), .flag .cc, ()) (.gpr (.reg .X0), .flag .cc, ()) .decInc = none ∧
    (armGpr.op (.addc 64) (.gpr (.reg .X1), .gpr (.reg .X2), .flag .cs, ()) (.gpr (.reg .X0), .flag .cs, ()) .default).isSome = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## 2. Concrete `Host.ofLayout` setup & small combinators -/

@[instance_reducible] def iselLayout : Layout where
  start := 0x40000
  instrSize _ := 4
  instrSize_pos _ := by decide

private theorem armMach_run_end {h : Host} {s : MachineData} {k : Nat} {post : MachineState → Prop}
    (hp : post (armMach.mkState s (armMach.addrOf h k))) :
    armMach.Run h k s post :=
  Eventually.done _ hp

private theorem tdst1 {R : ∀ t, PDst Reg Empty ArmCond t → Val t → Prop} {t : Ty}
    {pd : PDst Reg Empty ArmCond t} {v : Val t} (h : TRel R (as := [t]) (pd, ()) (v, ())) :
    R t pd v := by
  cases h with | cons hx _ => exact hx

private theorem tdst2 {R : ∀ t, PDst Reg Empty ArmCond t → Val t → Prop} {t₁ t₂ : Ty}
    {pd₁ : PDst Reg Empty ArmCond t₁} {pd₂ : PDst Reg Empty ArmCond t₂}
    {v₁ : Val t₁} {v₂ : Val t₂}
    (h : TRel R (as := [t₁, t₂]) (pd₁, pd₂, ()) (v₁, v₂, ())) :
    R t₁ pd₁ v₁ ∧ R t₂ pd₂ v₂ := by
  cases h with | cons hx h2 => cases h2 with | cons hy _ => exact ⟨hx, hy⟩

/-! ## 3. Concrete `udiv0` / `sdiv0` (`/ 0` and `INT_MIN / -1`) witness -/

def div0Op0 : List Directive :=
  (armGpr.op (.udiv0 32) (.gpr (.reg .X1), .gpr (.reg .X2), ()) (.gpr (.reg .X0), ()) .default).elim [] Prod.fst
def div0Op1 : List Directive :=
  (armGpr.op (.sdiv0 32) (.gpr (.reg .X1), .gpr (.reg .X2), ()) (.gpr (.reg .X3), ()) .default).elim [] Prod.fst
def div0Op2 : List Directive :=
  (armGpr.op (.sdiv0 32) (.gpr (.reg .X1), .gpr (.reg .X4), ()) (.gpr (.reg .X5), ()) .default).elim [] Prod.fst

def div0Prog : List Directive := div0Op0 ++ div0Op1 ++ div0Op2

theorem div0Prog_small : (Kraken.Layout.apply iselLayout div0Prog).sizeBefore div0Prog.length < 2 ^ 64 := by
  have : (Kraken.Layout.apply iselLayout div0Prog).sizeBefore div0Prog.length = 12 := by
    simp only [Kraken.Layout.apply, Kraken.Executable.sizeBefore, Kraken.Layout.size]
    decide
  omega

@[instance_reducible] def div0Host : Host := Host.ofLayout div0Prog iselLayout div0Prog_small

theorem div0_witness {s : MachineData}
    (hx1 : GprHolds (armMach.getGpr s (.reg .X1)) i32 0x80000000#32)
    (hx2 : GprHolds (armMach.getGpr s (.reg .X2)) i32 0#32)
    (hx4 : GprHolds (armMach.getGpr s (.reg .X4)) i32 0xFFFFFFFF#32) :
    armMach.Run div0Host 0 s fun st =>
      st.pc = armMach.addrOf div0Host div0Prog.length ∧
      GprHolds (armMach.getGpr st.data (.reg .X0)) i32 0#32 ∧
      GprHolds (armMach.getGpr st.data (.reg .X3)) i32 0#32 ∧
      GprHolds (armMach.getGpr st.data (.reg .X5)) i32 0x80000000#32 := by
  have hi : div0Prog.IsInfixAt (armMach.prog div0Host) 0 := ⟨[], rfl⟩
  obtain ⟨h01, h2⟩ := hi.append
  obtain ⟨h0, h1⟩ := h01.append
  simp only [List.length_append, ← Nat.add_assoc] at h1 h2
  refine armGprSpec.op_spec (code := .udiv0 32) (pas := (.gpr (.reg .X1), .gpr (.reg .X2), ()))
    (dsts := (.gpr (.reg .X0), ())) (vh := .default) (vs := (0x80000000#32, 0#32, ()))
    (P := (· = (0#32, ()))) rfl (by simp [tupArgGprs, armScratch]) (by simp [tupDstGprs, armScratch])
    (.cons hx1 (.cons hx2 .nil)) rfl h0 ?_
  rintro s1 ⟨⟨_, rfl, hd0⟩, _⟩ hfr0
  have hgx0 := tdst1 hd0
  have hx1_1 : GprHolds (armMach.getGpr s1 (.reg .X1)) i32 0x80000000#32 := by
    rw [hfr0.1 _ (by simp [tupDstGprs, armScratch])]; exact hx1
  have hx2_1 : GprHolds (armMach.getGpr s1 (.reg .X2)) i32 0#32 := by
    rw [hfr0.1 _ (by simp [tupDstGprs, armScratch])]; exact hx2
  have hx4_1 : GprHolds (armMach.getGpr s1 (.reg .X4)) i32 0xFFFFFFFF#32 := by
    rw [hfr0.1 _ (by simp [tupDstGprs, armScratch])]; exact hx4
  refine armGprSpec.op_spec (code := .sdiv0 32) (pas := (.gpr (.reg .X1), .gpr (.reg .X2), ()))
    (dsts := (.gpr (.reg .X3), ())) (vh := .default) (vs := (0x80000000#32, 0#32, ()))
    (P := (· = (0#32, ()))) rfl (by simp [tupArgGprs, armScratch]) (by simp [tupDstGprs, armScratch])
    (.cons hx1_1 (.cons hx2_1 .nil)) rfl h1 ?_
  rintro s2 ⟨⟨_, rfl, hd1⟩, _⟩ hfr1
  have hgx3 := tdst1 hd1
  have hgx0_2 : GprHolds (armMach.getGpr s2 (.reg .X0)) i32 0#32 := by
    rw [hfr1.1 _ (by simp [tupDstGprs, armScratch])]; exact hgx0
  have hx1_2 : GprHolds (armMach.getGpr s2 (.reg .X1)) i32 0x80000000#32 := by
    rw [hfr1.1 _ (by simp [tupDstGprs, armScratch])]; exact hx1_1
  have hx4_2 : GprHolds (armMach.getGpr s2 (.reg .X4)) i32 0xFFFFFFFF#32 := by
    rw [hfr1.1 _ (by simp [tupDstGprs, armScratch])]; exact hx4_1
  refine armGprSpec.op_spec (code := .sdiv0 32) (pas := (.gpr (.reg .X1), .gpr (.reg .X4), ()))
    (dsts := (.gpr (.reg .X5), ())) (vh := .default) (vs := (0x80000000#32, 0xFFFFFFFF#32, ()))
    (P := (· = (0x80000000#32, ()))) rfl (by simp [tupArgGprs, armScratch]) (by simp [tupDstGprs, armScratch])
    (.cons hx1_2 (.cons hx4_2 .nil)) rfl h2 ?_
  rintro s3 ⟨⟨_, rfl, hd2⟩, _⟩ hfr2
  have hgx5 := tdst1 hd2
  refine armMach_run_end ⟨rfl, ?_, ?_, hgx5⟩
  · rw [hfr2.1 _ (by simp [tupDstGprs, armScratch])]; exact hgx0_2
  · rw [hfr2.1 _ (by simp [tupDstGprs, armScratch])]; exact hgx3

/-! ## 4. Concrete `clz` / `cls` / `rbit` / `ctz` witness -/

def bitOp0 : List Directive :=
  (armGpr.op (.clz 64) (.imm 0x0001000000000000#64, ()) (.gpr (.reg .X0), ()) .default).elim [] Prod.fst
def bitOp1 : List Directive :=
  (armGpr.op (.cls 32) (.imm 0xE0000001#32, ()) (.gpr (.reg .X1), ()) .default).elim [] Prod.fst
def bitOp2 : List Directive :=
  (armGpr.op (.rbit 32) (.imm 0x00000003#32, ()) (.gpr (.reg .X2), ()) .default).elim [] Prod.fst
def bitOp3 : List Directive :=
  (armGpr.op (.ctz 32) (.imm 0x00001000#32, ()) (.gpr (.reg .X3), ()) .default).elim [] Prod.fst

def bitProg : List Directive := bitOp0 ++ bitOp1 ++ bitOp2 ++ bitOp3

theorem bitProg_small : (Kraken.Layout.apply iselLayout bitProg).sizeBefore bitProg.length < 2 ^ 64 := by
  simp only [Kraken.Layout.apply, Kraken.Executable.sizeBefore, Kraken.Layout.size]
  decide

@[instance_reducible] def bitHost : Host := Host.ofLayout bitProg iselLayout bitProg_small

theorem bitCount_witness (s : MachineData) :
    armMach.Run bitHost 0 s fun st =>
      st.pc = armMach.addrOf bitHost bitProg.length ∧
      GprHolds (armMach.getGpr st.data (.reg .X0)) i64 15#64 ∧
      GprHolds (armMach.getGpr st.data (.reg .X1)) i32 2#32 ∧
      GprHolds (armMach.getGpr st.data (.reg .X2)) i32 0xC0000000#32 ∧
      GprHolds (armMach.getGpr st.data (.reg .X3)) i32 12#32 := by
  have hi : bitProg.IsInfixAt (armMach.prog bitHost) 0 := ⟨[], rfl⟩
  obtain ⟨h012, h3⟩ := hi.append
  obtain ⟨h01, h2⟩ := h012.append
  obtain ⟨h0, h1⟩ := h01.append
  simp only [List.length_append, ← Nat.add_assoc] at h1 h2 h3
  refine armGprSpec.op_spec (code := .clz 64) (pas := (.imm 0x0001000000000000#64, ()))
    (dsts := (.gpr (.reg .X0), ())) (vh := .default) (vs := (0x0001000000000000#64, ()))
    (P := (· = (15#64, ()))) rfl (by simp [tupArgGprs]) (by simp [tupDstGprs, armScratch])
    (.cons rfl .nil) (by dsimp [OpCode.wp]) h0 ?_
  rintro s1 ⟨⟨_, rfl, hd0⟩, _⟩ _
  have hx0 := tdst1 hd0
  refine armGprSpec.op_spec (code := .cls 32) (pas := (.imm 0xE0000001#32, ()))
    (dsts := (.gpr (.reg .X1), ())) (vh := .default) (vs := (0xE0000001#32, ()))
    (P := (· = (2#32, ()))) rfl (by simp [tupArgGprs]) (by simp [tupDstGprs, armScratch])
    (.cons rfl .nil) (by dsimp [OpCode.wp]; decide) h1 ?_
  rintro s2 ⟨⟨_, rfl, hd1⟩, _⟩ hfr1
  have hx1 := tdst1 hd1
  have hx0_2 : GprHolds (armMach.getGpr s2 (.reg .X0)) i64 15#64 := by
    rw [hfr1.1 _ (by simp [tupDstGprs, armScratch])]; exact hx0
  refine armGprSpec.op_spec (code := .rbit 32) (pas := (.imm 0x00000003#32, ()))
    (dsts := (.gpr (.reg .X2), ())) (vh := .default) (vs := (0x00000003#32, ()))
    (P := (· = (0xC0000000#32, ()))) rfl (by simp [tupArgGprs]) (by simp [tupDstGprs, armScratch])
    (.cons rfl .nil) (by dsimp [OpCode.wp]; decide) h2 ?_
  rintro s3 ⟨⟨_, rfl, hd2⟩, _⟩ hfr2
  have hx2 := tdst1 hd2
  have hx0_3 : GprHolds (armMach.getGpr s3 (.reg .X0)) i64 15#64 := by
    rw [hfr2.1 _ (by simp [tupDstGprs, armScratch])]; exact hx0_2
  have hx1_3 : GprHolds (armMach.getGpr s3 (.reg .X1)) i32 2#32 := by
    rw [hfr2.1 _ (by simp [tupDstGprs, armScratch])]; exact hx1
  have hrev : (0x00001000#32).reverse = 0x00080000#32 := by decide
  have hclz : (0x00080000#32).clz = 12#32 := by decide
  refine armGprSpec.op_spec (code := .ctz 32) (pas := (.imm 0x00001000#32, ()))
    (dsts := (.gpr (.reg .X3), ())) (vh := .default) (vs := (0x00001000#32, ()))
    (P := (· = (12#32, ()))) rfl (by simp [tupArgGprs]) (by simp [tupDstGprs, armScratch])
    (.cons rfl .nil) (by dsimp [OpCode.wp]; rw [hrev, hclz]) h3 ?_
  rintro s4 ⟨⟨_, rfl, hd3⟩, _⟩ hfr3
  have hx3 := tdst1 hd3
  refine armMach_run_end ⟨rfl, ?_, ?_, ?_, hx3⟩
  · rw [hfr3.1 _ (by simp [tupDstGprs, armScratch])]; exact hx0_3
  · rw [hfr3.1 _ (by simp [tupDstGprs, armScratch])]; exact hx1_3
  · rw [hfr3.1 _ (by simp [tupDstGprs, armScratch])]; exact hx2

/-! ## 5. Concrete `addc` (`.cs` chain), `subb` (`.cc` borrow chain), and `clearFlags` witness -/

def carryCf : List Directive := armGpr.clearFlags
def addcLo : List Directive :=
  (armGpr.op (.addc 64) (.gpr (.reg .X0), .gpr (.reg .X1), .imm false, ()) (.gpr (.reg .X4), .flag .cs, ()) .default).elim [] Prod.fst
def addcHi : List Directive :=
  (armGpr.op (.addc 64) (.gpr (.reg .X2), .gpr (.reg .X3), .flag .cs, ()) (.gpr (.reg .X5), .gpr (.reg .X6), ()) .default).elim [] Prod.fst
def subbLo : List Directive :=
  (armGpr.op (.subb 64) (.gpr (.reg .X1), .gpr (.reg .X0), .imm false, ()) (.gpr (.reg .X7), .flag .cc, ()) .default).elim [] Prod.fst
def subbHi : List Directive :=
  (armGpr.op (.subb 64) (.gpr (.reg .X2), .gpr (.reg .X2), .flag .cc, ()) (.gpr (.reg .X8), .gpr (.reg .X9), ()) .default).elim [] Prod.fst

def carryProg : List Directive := carryCf ++ addcLo ++ addcHi ++ subbLo ++ subbHi

theorem carryProg_small : (Kraken.Layout.apply iselLayout carryProg).sizeBefore carryProg.length < 2 ^ 64 := by
  have : (Kraken.Layout.apply iselLayout carryProg).sizeBefore carryProg.length = 28 := by
    simp only [Kraken.Layout.apply, Kraken.Executable.sizeBefore, Kraken.Layout.size]
    decide
  omega

@[instance_reducible] def carryHost : Host := Host.ofLayout carryProg iselLayout carryProg_small

theorem carry_borrow_chain_witness {s : MachineData}
    (hx0 : GprHolds (armMach.getGpr s (.reg .X0)) i64 0xFFFFFFFFFFFFFFFF#64)
    (hx1 : GprHolds (armMach.getGpr s (.reg .X1)) i64 2#64)
    (hx2 : GprHolds (armMach.getGpr s (.reg .X2)) i64 10#64)
    (hx3 : GprHolds (armMach.getGpr s (.reg .X3)) i64 20#64) :
    armMach.Run carryHost 0 s fun st =>
      st.pc = armMach.addrOf carryHost carryProg.length ∧
      GprHolds (armMach.getGpr st.data (.reg .X4)) i64 1#64 ∧
      GprHolds (armMach.getGpr st.data (.reg .X5)) i64 31#64 ∧
      GprHolds (armMach.getGpr st.data (.reg .X6)) .bool false ∧
      GprHolds (armMach.getGpr st.data (.reg .X7)) i64 3#64 ∧
      GprHolds (armMach.getGpr st.data (.reg .X8)) i64 0xFFFFFFFFFFFFFFFF#64 ∧
      GprHolds (armMach.getGpr st.data (.reg .X9)) .bool true := by
  have hi : carryProg.IsInfixAt (armMach.prog carryHost) 0 := ⟨[], rfl⟩
  obtain ⟨h0123, h4⟩ := hi.append
  obtain ⟨h012, h3⟩ := h0123.append
  obtain ⟨h01, h2⟩ := h012.append
  obtain ⟨h0, h1⟩ := h01.append
  simp only [List.length_append, ← Nat.add_assoc] at h1 h2 h3 h4
  refine armGprSpec.clearFlags_spec (s := s) h0 ?_
  rintro s0 ⟨_, _⟩ hfrCf
  have hx0_0 : GprHolds (armMach.getGpr s0 (.reg .X0)) i64 0xFFFFFFFFFFFFFFFF#64 := by rw [hfrCf.1 _ (by simp [armScratch])]; exact hx0
  have hx1_0 : GprHolds (armMach.getGpr s0 (.reg .X1)) i64 2#64 := by rw [hfrCf.1 _ (by simp [armScratch])]; exact hx1
  have hx2_0 : GprHolds (armMach.getGpr s0 (.reg .X2)) i64 10#64 := by rw [hfrCf.1 _ (by simp [armScratch])]; exact hx2
  have hx3_0 : GprHolds (armMach.getGpr s0 (.reg .X3)) i64 20#64 := by rw [hfrCf.1 _ (by simp [armScratch])]; exact hx3
  refine armGprSpec.op_spec (code := .addc 64)
    (pas := (.gpr (.reg .X0), .gpr (.reg .X1), .imm false, ()))
    (dsts := (.gpr (.reg .X4), .flag .cs, ())) (vh := .default)
    (vs := (0xFFFFFFFFFFFFFFFF#64, 2#64, false, ())) (P := (· = (1#64, true, ())))
    rfl (by simp [tupArgGprs, armScratch]) (by simp [tupDstGprs, armScratch])
    (.cons hx0_0 (.cons hx1_0 (.cons rfl .nil))) (by dsimp [OpCode.wp]; decide) h1 ?_
  rintro s1 ⟨⟨_, rfl, hd1⟩, _⟩ hfr1
  have ⟨hx4, hcs⟩ := tdst2 hd1
  have hx0_1 : GprHolds (armMach.getGpr s1 (.reg .X0)) i64 0xFFFFFFFFFFFFFFFF#64 := by
    rw [hfr1.1 _ (by simp [tupDstGprs, armScratch])]; exact hx0_0
  have hx1_1 : GprHolds (armMach.getGpr s1 (.reg .X1)) i64 2#64 := by
    rw [hfr1.1 _ (by simp [tupDstGprs, armScratch])]; exact hx1_0
  have hx2_1 : GprHolds (armMach.getGpr s1 (.reg .X2)) i64 10#64 := by
    rw [hfr1.1 _ (by simp [tupDstGprs, armScratch])]; exact hx2_0
  have hx3_1 : GprHolds (armMach.getGpr s1 (.reg .X3)) i64 20#64 := by
    rw [hfr1.1 _ (by simp [tupDstGprs, armScratch])]; exact hx3_0
  refine armGprSpec.op_spec (code := .addc 64)
    (pas := (.gpr (.reg .X2), .gpr (.reg .X3), .flag .cs, ()))
    (dsts := (.gpr (.reg .X5), .gpr (.reg .X6), ())) (vh := .default)
    (vs := (10#64, 20#64, true, ())) (P := (· = (31#64, false, ())))
    rfl (by simp [tupArgGprs, armScratch]) (by simp [tupDstGprs, armScratch])
    (.cons hx2_1 (.cons hx3_1 (.cons hcs .nil))) (by dsimp [OpCode.wp]; decide) h2 ?_
  rintro s2 ⟨⟨_, rfl, hd2⟩, _⟩ hfr2
  have ⟨hx5, hx6⟩ := tdst2 hd2
  have hx0_2 : GprHolds (armMach.getGpr s2 (.reg .X0)) i64 0xFFFFFFFFFFFFFFFF#64 := by
    rw [hfr2.1 _ (by simp [tupDstGprs, armScratch])]; exact hx0_1
  have hx1_2 : GprHolds (armMach.getGpr s2 (.reg .X1)) i64 2#64 := by
    rw [hfr2.1 _ (by simp [tupDstGprs, armScratch])]; exact hx1_1
  have hx2_2 : GprHolds (armMach.getGpr s2 (.reg .X2)) i64 10#64 := by
    rw [hfr2.1 _ (by simp [tupDstGprs, armScratch])]; exact hx2_1
  have hx4_2 : GprHolds (armMach.getGpr s2 (.reg .X4)) i64 1#64 := by
    rw [hfr2.1 _ (by simp [tupDstGprs, armScratch])]; exact hx4
  refine armGprSpec.op_spec (code := .subb 64)
    (pas := (.gpr (.reg .X1), .gpr (.reg .X0), .imm false, ()))
    (dsts := (.gpr (.reg .X7), .flag .cc, ())) (vh := .default)
    (vs := (2#64, 0xFFFFFFFFFFFFFFFF#64, false, ())) (P := (· = (3#64, true, ())))
    rfl (by simp [tupArgGprs, armScratch]) (by simp [tupDstGprs, armScratch])
    (.cons hx1_2 (.cons hx0_2 (.cons rfl .nil))) (by dsimp [OpCode.wp]; decide) h3 ?_
  rintro s3 ⟨⟨_, rfl, hd3⟩, _⟩ hfr3
  have ⟨hx7, hcc⟩ := tdst2 hd3
  have hx2_3 : GprHolds (armMach.getGpr s3 (.reg .X2)) i64 10#64 := by
    rw [hfr3.1 _ (by simp [tupDstGprs, armScratch])]; exact hx2_2
  have hx4_3 : GprHolds (armMach.getGpr s3 (.reg .X4)) i64 1#64 := by
    rw [hfr3.1 _ (by simp [tupDstGprs, armScratch])]; exact hx4_2
  have hx5_3 : GprHolds (armMach.getGpr s3 (.reg .X5)) i64 31#64 := by
    rw [hfr3.1 _ (by simp [tupDstGprs, armScratch])]; exact hx5
  have hx6_3 : GprHolds (armMach.getGpr s3 (.reg .X6)) .bool false := by
    rw [hfr3.1 _ (by simp [tupDstGprs, armScratch])]; exact hx6
  refine armGprSpec.op_spec (code := .subb 64)
    (pas := (.gpr (.reg .X2), .gpr (.reg .X2), .flag .cc, ()))
    (dsts := (.gpr (.reg .X8), .gpr (.reg .X9), ())) (vh := .default)
    (vs := (10#64, 10#64, true, ())) (P := (· = (0xFFFFFFFFFFFFFFFF#64, true, ())))
    rfl (by simp [tupArgGprs, armScratch]) (by simp [tupDstGprs, armScratch])
    (.cons hx2_3 (.cons hx2_3 (.cons hcc .nil))) (by dsimp [OpCode.wp]; decide) h4 ?_
  rintro s4 ⟨⟨_, rfl, hd4⟩, _⟩ hfr4
  have ⟨hx8, hx9⟩ := tdst2 hd4
  refine armMach_run_end ⟨rfl, ?_, ?_, ?_, ?_, hx8, hx9⟩
  · rw [hfr4.1 _ (by simp [tupDstGprs, armScratch])]; exact hx4_3
  · rw [hfr4.1 _ (by simp [tupDstGprs, armScratch])]; exact hx5_3
  · rw [hfr4.1 _ (by simp [tupDstGprs, armScratch])]; exact hx6_3
  · rw [hfr4.1 _ (by simp [tupDstGprs, armScratch])]; exact hx7

/-! ## 6. Concrete `umulw` / `smulw`, `fshl` / `fshr`, and `select` (`CSEL`) witness -/

def wfOp0 : List Directive :=
  (armGpr.op (.umulw 64) (.gpr (.reg .X0), .gpr (.reg .X1), ()) (.gpr (.reg .X0), .gpr (.reg .X2), ()) .default).elim [] Prod.fst
def wfOp1 : List Directive :=
  (armGpr.op (.smulw 32) (.gpr (.reg .X3), .gpr (.reg .X4), ()) (.gpr (.reg .X5), .gpr (.reg .X6), ()) .default).elim [] Prod.fst
def wfOp2 : List Directive :=
  (armGpr.op (.fshl 32) (.imm 0x12345678#32, .imm 0x9ABCDEF0#32, .imm 0#32, ()) (.gpr (.reg .X7), ()) .default).elim [] Prod.fst
def wfOp3 : List Directive :=
  (armGpr.op (.fshl 64) (.gpr (.reg .X1), .gpr (.reg .X2), .gpr (.reg .X8), ()) (.gpr (.reg .X9), ()) .default).elim [] Prod.fst
def wfOp4 : List Directive :=
  (armGpr.op (.fshr 32) (.imm 0x00000002#32, .imm 0x00000010#32, .imm 4#32, ()) (.gpr (.reg .X10), ()) .default).elim [] Prod.fst
def wfOp5 : List Directive :=
  (armGpr.op (.select i64) (.gpr (.reg .X8), .gpr (.reg .X1), .gpr (.reg .X2), ()) (.gpr (.reg .X11), ()) .default).elim [] Prod.fst

def mulFunnelSelProg : List Directive := wfOp0 ++ wfOp1 ++ wfOp2 ++ wfOp3 ++ wfOp4 ++ wfOp5

theorem mulFunnelSel_small :
    (Kraken.Layout.apply iselLayout mulFunnelSelProg).sizeBefore mulFunnelSelProg.length < 2 ^ 64 := by
  simp only [Kraken.Layout.apply, Kraken.Executable.sizeBefore, Kraken.Layout.size]
  decide

@[instance_reducible] def mulFunnelSelHost : Host :=
  Host.ofLayout mulFunnelSelProg iselLayout mulFunnelSel_small

theorem mul_funnel_select_witness {s : MachineData}
    (hx0 : GprHolds (armMach.getGpr s (.reg .X0)) i64 0x100000000#64)
    (hx1 : GprHolds (armMach.getGpr s (.reg .X1)) i64 0x100000002#64)
    (hx3 : GprHolds (armMach.getGpr s (.reg .X3)) i32 0xFFFFFFFE#32)
    (hx4 : GprHolds (armMach.getGpr s (.reg .X4)) i32 0x7FFFFFFF#32)
    (hx8 : GprHolds (armMach.getGpr s (.reg .X8)) i64 0#64) :
    armMach.Run mulFunnelSelHost 0 s fun st =>
      st.pc = armMach.addrOf mulFunnelSelHost mulFunnelSelProg.length ∧
      GprHolds (armMach.getGpr st.data (.reg .X0)) i64 0x200000000#64 ∧
      GprHolds (armMach.getGpr st.data (.reg .X2)) i64 1#64 ∧
      GprHolds (armMach.getGpr st.data (.reg .X5)) i32 2#32 ∧
      GprHolds (armMach.getGpr st.data (.reg .X6)) i32 0xFFFFFFFF#32 ∧
      GprHolds (armMach.getGpr st.data (.reg .X7)) i32 0x12345678#32 ∧
      GprHolds (armMach.getGpr st.data (.reg .X9)) i64 0x100000002#64 ∧
      GprHolds (armMach.getGpr st.data (.reg .X10)) i32 0x20000001#32 ∧
      GprHolds (armMach.getGpr st.data (.reg .X11)) i64 1#64 := by
  have hi : mulFunnelSelProg.IsInfixAt (armMach.prog mulFunnelSelHost) 0 := ⟨[], rfl⟩
  obtain ⟨h01234, h5⟩ := hi.append
  obtain ⟨h0123, h4⟩ := h01234.append
  obtain ⟨h012, h3⟩ := h0123.append
  obtain ⟨h01, h2⟩ := h012.append
  obtain ⟨h0, h1⟩ := h01.append
  simp only [List.length_append, ← Nat.add_assoc] at h1 h2 h3 h4 h5
  refine armGprSpec.op_spec (code := .umulw 64) (pas := (.gpr (.reg .X0), .gpr (.reg .X1), ()))
    (dsts := (.gpr (.reg .X0), .gpr (.reg .X2), ())) (vh := .default)
    (vs := (0x100000000#64, 0x100000002#64, ())) (P := (· = (0x200000000#64, 1#64, ())))
    rfl (by simp [tupArgGprs, armScratch]) (by simp [tupDstGprs, armScratch])
    (.cons hx0 (.cons hx1 .nil)) rfl h0 ?_
  rintro s1 ⟨⟨_, rfl, hd0⟩, _⟩ hfr0
  have ⟨rx0, rx2⟩ := tdst2 hd0
  have hx1_1 : GprHolds (armMach.getGpr s1 (.reg .X1)) i64 0x100000002#64 := by
    rw [hfr0.1 _ (by simp [tupDstGprs, armScratch])]; exact hx1
  have hx3_1 : GprHolds (armMach.getGpr s1 (.reg .X3)) i32 0xFFFFFFFE#32 := by
    rw [hfr0.1 _ (by simp [tupDstGprs, armScratch])]; exact hx3
  have hx4_1 : GprHolds (armMach.getGpr s1 (.reg .X4)) i32 0x7FFFFFFF#32 := by
    rw [hfr0.1 _ (by simp [tupDstGprs, armScratch])]; exact hx4
  have hx8_1 : GprHolds (armMach.getGpr s1 (.reg .X8)) i64 0#64 := by
    rw [hfr0.1 _ (by simp [tupDstGprs, armScratch])]; exact hx8
  refine armGprSpec.op_spec (code := .smulw 32) (pas := (.gpr (.reg .X3), .gpr (.reg .X4), ()))
    (dsts := (.gpr (.reg .X5), .gpr (.reg .X6), ())) (vh := .default)
    (vs := (0xFFFFFFFE#32, 0x7FFFFFFF#32, ())) (P := (· = (2#32, 0xFFFFFFFF#32, ())))
    rfl (by simp [tupArgGprs, armScratch]) (by simp [tupDstGprs, armScratch])
    (.cons hx3_1 (.cons hx4_1 .nil)) rfl h1 ?_
  rintro s2 ⟨⟨_, rfl, hd1⟩, _⟩ hfr1
  have ⟨rx5, rx6⟩ := tdst2 hd1
  have rx0_2 : GprHolds (armMach.getGpr s2 (.reg .X0)) i64 0x200000000#64 := by
    rw [hfr1.1 _ (by simp [tupDstGprs, armScratch])]; exact rx0
  have hx1_2 : GprHolds (armMach.getGpr s2 (.reg .X1)) i64 0x100000002#64 := by
    rw [hfr1.1 _ (by simp [tupDstGprs, armScratch])]; exact hx1_1
  have rx2_2 : GprHolds (armMach.getGpr s2 (.reg .X2)) i64 1#64 := by
    rw [hfr1.1 _ (by simp [tupDstGprs, armScratch])]; exact rx2
  have hx8_2 : GprHolds (armMach.getGpr s2 (.reg .X8)) i64 0#64 := by
    rw [hfr1.1 _ (by simp [tupDstGprs, armScratch])]; exact hx8_1
  refine armGprSpec.op_spec (code := .fshl 32)
    (pas := (.imm 0x12345678#32, .imm 0x9ABCDEF0#32, .imm 0#32, ()))
    (dsts := (.gpr (.reg .X7), ())) (vh := .default)
    (vs := (0x12345678#32, 0x9ABCDEF0#32, 0#32, ())) (P := (· = (0x12345678#32, ())))
    rfl (by simp [tupArgGprs]) (by simp [tupDstGprs, armScratch])
    (.cons rfl (.cons rfl (.cons rfl .nil))) rfl h2 ?_
  rintro s3 ⟨⟨_, rfl, hd2⟩, _⟩ hfr2
  have rx7 := tdst1 hd2
  have rx0_3 : GprHolds (armMach.getGpr s3 (.reg .X0)) i64 0x200000000#64 := by
    rw [hfr2.1 _ (by simp [tupDstGprs, armScratch])]; exact rx0_2
  have hx1_3 : GprHolds (armMach.getGpr s3 (.reg .X1)) i64 0x100000002#64 := by
    rw [hfr2.1 _ (by simp [tupDstGprs, armScratch])]; exact hx1_2
  have rx2_3 : GprHolds (armMach.getGpr s3 (.reg .X2)) i64 1#64 := by
    rw [hfr2.1 _ (by simp [tupDstGprs, armScratch])]; exact rx2_2
  have rx5_3 : GprHolds (armMach.getGpr s3 (.reg .X5)) i32 2#32 := by
    rw [hfr2.1 _ (by simp [tupDstGprs, armScratch])]; exact rx5
  have rx6_3 : GprHolds (armMach.getGpr s3 (.reg .X6)) i32 0xFFFFFFFF#32 := by
    rw [hfr2.1 _ (by simp [tupDstGprs, armScratch])]; exact rx6
  have hx8_3 : GprHolds (armMach.getGpr s3 (.reg .X8)) i64 0#64 := by
    rw [hfr2.1 _ (by simp [tupDstGprs, armScratch])]; exact hx8_2
  refine armGprSpec.op_spec (code := .fshl 64)
    (pas := (.gpr (.reg .X1), .gpr (.reg .X2), .gpr (.reg .X8), ()))
    (dsts := (.gpr (.reg .X9), ())) (vh := .default)
    (vs := (0x100000002#64, 1#64, 0#64, ())) (P := (· = (0x100000002#64, ())))
    rfl (by simp [tupArgGprs, armScratch]) (by simp [tupDstGprs, armScratch])
    (.cons hx1_3 (.cons rx2_3 (.cons hx8_3 .nil))) rfl h3 ?_
  rintro s4 ⟨⟨_, rfl, hd3⟩, _⟩ hfr3
  have rx9 := tdst1 hd3
  have rx0_4 : GprHolds (armMach.getGpr s4 (.reg .X0)) i64 0x200000000#64 := by
    rw [hfr3.1 _ (by simp [tupDstGprs, armScratch])]; exact rx0_3
  have hx1_4 : GprHolds (armMach.getGpr s4 (.reg .X1)) i64 0x100000002#64 := by
    rw [hfr3.1 _ (by simp [tupDstGprs, armScratch])]; exact hx1_3
  have rx2_4 : GprHolds (armMach.getGpr s4 (.reg .X2)) i64 1#64 := by
    rw [hfr3.1 _ (by simp [tupDstGprs, armScratch])]; exact rx2_3
  have rx5_4 : GprHolds (armMach.getGpr s4 (.reg .X5)) i32 2#32 := by
    rw [hfr3.1 _ (by simp [tupDstGprs, armScratch])]; exact rx5_3
  have rx6_4 : GprHolds (armMach.getGpr s4 (.reg .X6)) i32 0xFFFFFFFF#32 := by
    rw [hfr3.1 _ (by simp [tupDstGprs, armScratch])]; exact rx6_3
  have rx7_4 : GprHolds (armMach.getGpr s4 (.reg .X7)) i32 0x12345678#32 := by
    rw [hfr3.1 _ (by simp [tupDstGprs, armScratch])]; exact rx7
  have hx8_4 : GprHolds (armMach.getGpr s4 (.reg .X8)) i64 0#64 := by
    rw [hfr3.1 _ (by simp [tupDstGprs, armScratch])]; exact hx8_3
  refine armGprSpec.op_spec (code := .fshr 32)
    (pas := (.imm 0x00000002#32, .imm 0x00000010#32, .imm 4#32, ()))
    (dsts := (.gpr (.reg .X10), ())) (vh := .default)
    (vs := (0x00000002#32, 0x00000010#32, 4#32, ())) (P := (· = (0x20000001#32, ())))
    rfl (by simp [tupArgGprs]) (by simp [tupDstGprs, armScratch])
    (.cons rfl (.cons rfl (.cons rfl .nil))) rfl h4 ?_
  rintro s5 ⟨⟨_, rfl, hd4⟩, _⟩ hfr4
  have rx10 := tdst1 hd4
  have rx0_5 : GprHolds (armMach.getGpr s5 (.reg .X0)) i64 0x200000000#64 := by
    rw [hfr4.1 _ (by simp [tupDstGprs, armScratch])]; exact rx0_4
  have hx1_5 : GprHolds (armMach.getGpr s5 (.reg .X1)) i64 0x100000002#64 := by
    rw [hfr4.1 _ (by simp [tupDstGprs, armScratch])]; exact hx1_4
  have rx2_5 : GprHolds (armMach.getGpr s5 (.reg .X2)) i64 1#64 := by
    rw [hfr4.1 _ (by simp [tupDstGprs, armScratch])]; exact rx2_4
  have rx5_5 : GprHolds (armMach.getGpr s5 (.reg .X5)) i32 2#32 := by
    rw [hfr4.1 _ (by simp [tupDstGprs, armScratch])]; exact rx5_4
  have rx6_5 : GprHolds (armMach.getGpr s5 (.reg .X6)) i32 0xFFFFFFFF#32 := by
    rw [hfr4.1 _ (by simp [tupDstGprs, armScratch])]; exact rx6_4
  have rx7_5 : GprHolds (armMach.getGpr s5 (.reg .X7)) i32 0x12345678#32 := by
    rw [hfr4.1 _ (by simp [tupDstGprs, armScratch])]; exact rx7_4
  have hx8_bool : GprHolds (armMach.getGpr s5 (.reg .X8)) .bool false := by
    have h64 : GprHolds (armMach.getGpr s5 (.reg .X8)) i64 0#64 := by
      rw [hfr4.1 _ (by simp [tupDstGprs, armScratch])]; exact hx8_4
    simpa [GprHolds] using congrArg (BitVec.setWidth 8) h64.2
  have rx9_5 : GprHolds (armMach.getGpr s5 (.reg .X9)) i64 0x100000002#64 := by
    rw [hfr4.1 _ (by simp [tupDstGprs, armScratch])]; exact rx9
  refine armGprSpec.op_spec (code := .select i64)
    (pas := (.gpr (.reg .X8), .gpr (.reg .X1), .gpr (.reg .X2), ()))
    (dsts := (.gpr (.reg .X11), ())) (vh := .default)
    (vs := (false, 0x100000002#64, 1#64, ())) (P := (· = (1#64, ())))
    rfl (by simp [tupArgGprs, armScratch]) (by simp [tupDstGprs, armScratch])
    (.cons hx8_bool (.cons hx1_5 (.cons rx2_5 .nil))) rfl h5 ?_
  rintro s6 ⟨⟨_, rfl, hd5⟩, _⟩ hfr5
  have rx11 := tdst1 hd5
  refine armMach_run_end ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rx11⟩
  · rw [hfr5.1 _ (by simp [tupDstGprs, armScratch])]; exact rx0_5
  · rw [hfr5.1 _ (by simp [tupDstGprs, armScratch])]; exact rx2_5
  · rw [hfr5.1 _ (by simp [tupDstGprs, armScratch])]; exact rx5_5
  · rw [hfr5.1 _ (by simp [tupDstGprs, armScratch])]; exact rx6_5
  · rw [hfr5.1 _ (by simp [tupDstGprs, armScratch])]; exact rx7_5
  · rw [hfr5.1 _ (by simp [tupDstGprs, armScratch])]; exact rx9_5
  · rw [hfr5.1 _ (by simp [tupDstGprs, armScratch])]; exact rx10

/-! ## 7. Sub-word `8`/`16` shifts, `cmp`, and `sdiv` with upper garbage bits -/

def sub0 : List Directive :=
  (armGpr.op (.ashr i8) (.gpr (.reg .X1), .gpr (.reg .X2), ()) (.gpr (.reg .X3), ()) .default).elim [] Prod.fst
def sub1 : List Directive :=
  (armGpr.op (.shl i16) (.gpr (.reg .X4), .gpr (.reg .X5), ()) (.gpr (.reg .X6), ()) .default).elim [] Prod.fst
def sub2 : List Directive :=
  (armGpr.op (.cmp .slt i8) (.gpr (.reg .X1), .imm 1#8, ()) (.gpr (.reg .X7), ()) .default).elim [] Prod.fst
def sub3 : List Directive :=
  (armGpr.op (.sdiv 16) (.gpr (.reg .X4), .imm 0xFFFF#16, ()) (.gpr (.reg .X8), ()) .default).elim [] Prod.fst

def subwordProg : List Directive := sub0 ++ sub1 ++ sub2 ++ sub3

theorem subwordProg_small : (Kraken.Layout.apply iselLayout subwordProg).sizeBefore subwordProg.length < 2 ^ 64 := by
  simp only [Kraken.Layout.apply, Kraken.Executable.sizeBefore, Kraken.Layout.size]
  decide

@[instance_reducible] def subwordHost : Host := Host.ofLayout subwordProg iselLayout subwordProg_small

/-- Non-zero upper garbage bits `[8..63]`/`[16..63]` do not pollute sub-word shifts, comparisons, or `sdiv`. -/
theorem subword_garbage_witness {s : MachineData}
    (hx1 : armMach.getGpr s (.reg .X1) = 0xDEAD0000_0000FF80#64)
    (hx2 : armMach.getGpr s (.reg .X2) = 0x12340000_0000FF03#64)
    (hx4 : armMach.getGpr s (.reg .X4) = 0xBEEF0000_00FF0008#64)
    (hx5 : armMach.getGpr s (.reg .X5) = 0xCAFE0000_0000FF14#64) :
    armMach.Run subwordHost 0 s fun st =>
      st.pc = armMach.addrOf subwordHost subwordProg.length ∧
      GprHolds (armMach.getGpr st.data (.reg .X3)) i8 0xF0#8 ∧
      GprHolds (armMach.getGpr st.data (.reg .X6)) i16 0x0080#16 ∧
      GprHolds (armMach.getGpr st.data (.reg .X7)) .bool true ∧
      GprHolds (armMach.getGpr st.data (.reg .X8)) i16 0xFFF8#16 := by
  have hi : subwordProg.IsInfixAt (armMach.prog subwordHost) 0 := ⟨[], rfl⟩
  obtain ⟨h012, h3⟩ := hi.append
  obtain ⟨h01, h2⟩ := h012.append
  obtain ⟨h0, h1⟩ := h01.append
  simp only [List.length_append, ← Nat.add_assoc] at h1 h2 h3
  have gx1 : GprHolds (armMach.getGpr s (.reg .X1)) i8 0x80#8 := ⟨by decide, by rw [hx1]; rfl⟩
  have gx2 : GprHolds (armMach.getGpr s (.reg .X2)) i8 0x03#8 := ⟨by decide, by rw [hx2]; rfl⟩
  have gx4 : GprHolds (armMach.getGpr s (.reg .X4)) i16 0x0008#16 := ⟨by decide, by rw [hx4]; rfl⟩
  have gx5 : GprHolds (armMach.getGpr s (.reg .X5)) i16 0xFF14#16 := ⟨by decide, by rw [hx5]; rfl⟩
  refine armGprSpec.op_spec (code := .ashr i8) (pas := (.gpr (.reg .X1), .gpr (.reg .X2), ()))
    (dsts := (.gpr (.reg .X3), ())) (vh := .default) (vs := (0x80#8, 0x03#8, ()))
    (P := (· = (0xF0#8, ()))) rfl (by simp [tupArgGprs, armScratch]) (by simp [tupDstGprs, armScratch])
    (.cons gx1 (.cons gx2 .nil)) (by dsimp [OpCode.wp]; decide) h0 ?_
  rintro s1 ⟨⟨_, rfl, hd0⟩, _⟩ hfr0
  have rx3 := tdst1 hd0
  have gx1_1 : GprHolds (armMach.getGpr s1 (.reg .X1)) i8 0x80#8 := by
    rw [hfr0.1 _ (by simp [tupDstGprs, armScratch])]; exact gx1
  have gx4_1 : GprHolds (armMach.getGpr s1 (.reg .X4)) i16 0x0008#16 := by
    rw [hfr0.1 _ (by simp [tupDstGprs, armScratch])]; exact gx4
  have gx5_1 : GprHolds (armMach.getGpr s1 (.reg .X5)) i16 0xFF14#16 := by
    rw [hfr0.1 _ (by simp [tupDstGprs, armScratch])]; exact gx5
  refine armGprSpec.op_spec (code := .shl i16) (pas := (.gpr (.reg .X4), .gpr (.reg .X5), ()))
    (dsts := (.gpr (.reg .X6), ())) (vh := .default) (vs := (0x0008#16, 0xFF14#16, ()))
    (P := (· = (0x0080#16, ()))) rfl (by simp [tupArgGprs, armScratch]) (by simp [tupDstGprs, armScratch])
    (.cons gx4_1 (.cons gx5_1 .nil)) (by dsimp [OpCode.wp]; decide) h1 ?_
  rintro s2 ⟨⟨_, rfl, hd1⟩, _⟩ hfr1
  have rx6 := tdst1 hd1
  have rx3_2 : GprHolds (armMach.getGpr s2 (.reg .X3)) i8 0xF0#8 := by
    rw [hfr1.1 _ (by simp [tupDstGprs, armScratch])]; exact rx3
  have gx1_2 : GprHolds (armMach.getGpr s2 (.reg .X1)) i8 0x80#8 := by
    rw [hfr1.1 _ (by simp [tupDstGprs, armScratch])]; exact gx1_1
  have gx4_2 : GprHolds (armMach.getGpr s2 (.reg .X4)) i16 0x0008#16 := by
    rw [hfr1.1 _ (by simp [tupDstGprs, armScratch])]; exact gx4_1
  refine armGprSpec.op_spec (code := .cmp .slt i8) (pas := (.gpr (.reg .X1), .imm 1#8, ()))
    (dsts := (.gpr (.reg .X7), ())) (vh := .default) (vs := (0x80#8, 1#8, ()))
    (P := (· = (true, ()))) rfl (by simp [tupArgGprs, armScratch]) (by simp [tupDstGprs, armScratch])
    (.cons gx1_2 (.cons rfl .nil)) (by dsimp [OpCode.wp, liftCmp, CmpOp.evalBits]) h2 ?_
  rintro s3 ⟨⟨_, rfl, hd2⟩, _⟩ hfr2
  have rx7 := tdst1 hd2
  have rx3_3 : GprHolds (armMach.getGpr s3 (.reg .X3)) i8 0xF0#8 := by
    rw [hfr2.1 _ (by simp [tupDstGprs, armScratch])]; exact rx3_2
  have rx6_3 : GprHolds (armMach.getGpr s3 (.reg .X6)) i16 0x0080#16 := by
    rw [hfr2.1 _ (by simp [tupDstGprs, armScratch])]; exact rx6
  have gx4_3 : GprHolds (armMach.getGpr s3 (.reg .X4)) i16 0x0008#16 := by
    rw [hfr2.1 _ (by simp [tupDstGprs, armScratch])]; exact gx4_2
  refine armGprSpec.op_spec (code := .sdiv 16) (pas := (.gpr (.reg .X4), .imm 0xFFFF#16, ()))
    (dsts := (.gpr (.reg .X8), ())) (vh := .default) (vs := (0x0008#16, 0xFFFF#16, ()))
    (P := (· = (0xFFF8#16, ()))) rfl (by simp [tupArgGprs, armScratch]) (by simp [tupDstGprs, armScratch])
    (.cons gx4_3 (.cons rfl .nil)) (by dsimp [OpCode.wp, sdivDefined]; decide) h3 ?_
  rintro s4 ⟨⟨_, rfl, hd3⟩, _⟩ hfr3
  have rx8 := tdst1 hd3
  refine armMach_run_end ⟨rfl, ?_, ?_, ?_, rx8⟩
  · rw [hfr3.1 _ (by simp [tupDstGprs, armScratch])]; exact rx3_3
  · rw [hfr3.1 _ (by simp [tupDstGprs, armScratch])]; exact rx6_3
  · rw [hfr3.1 _ (by simp [tupDstGprs, armScratch])]; exact rx7

/-! ## 8. `.SP` corner cases (unaligned `SP`, `.bool .flag` store/load, `movi`/`mov`/`setcc`/`jnzGpr`) & `jnzGpr` upper bits -/

def spMovi : List Directive := armGpr.movi .SP 0x123456789ABCDEF3#64
def spMov : List Directive := armGpr.mov (.reg .X0) .SP
def spStFlag : List Directive := (armGpr.store .bool (.flag .eq) (.baseDisp .SP 16)).elim [] Prod.fst
def spLdFlag : List Directive := (armGpr.load .bool (.reg .X1) (.baseDisp .SP 16)).elim [] Prod.fst
def spSetcc : List Directive := armGpr.setcc .SP .cs
def spJnz : List Directive := (armGpr.jnzGpr .SP "L_taken").1

def spProg : List Directive :=
  spMovi ++ spMov ++ spStFlag ++ spLdFlag ++ spSetcc ++ spJnz ++ [.label "L_taken"]

theorem spProg_small : (Kraken.Layout.apply iselLayout spProg).sizeBefore spProg.length < 2 ^ 64 := by
  have : (Kraken.Layout.apply iselLayout spProg).sizeBefore spProg.length = 48 := by
    simp only [Kraken.Layout.apply, Kraken.Executable.sizeBefore, Kraken.Layout.size]
    decide
  omega

@[instance_reducible] def spHost : Host := Host.ofLayout spProg iselLayout spProg_small

/-- Unaligned `.SP` works cleanly across `movi`, `mov`, flag `store`/`load`, `setcc`, and `jnzGpr`. -/
theorem sp_corner_witness {s : MachineData}
    (heq : armMach.evalCond s .eq = true)
    (hcs : armMach.evalCond s .cs = true)
    (hok : storeOk (armMach.mem s) .bool (0x123456789ABCDEF3#64 + 16#64)) :
    armMach.Run spHost 0 s fun st =>
      st.pc = armMach.addrOf spHost (spProg.length - 1) ∧
      armMach.getGpr st.data (.reg .X0) = 0x123456789ABCDEF3#64 ∧
      GprHolds (armMach.getGpr st.data (.reg .X1)) .bool true ∧
      GprHolds (armMach.getGpr st.data .SP) .bool true := by
  have hi : spProg.IsInfixAt (armMach.prog spHost) 0 := ⟨[], rfl⟩
  obtain ⟨h012345, _⟩ := hi.append
  obtain ⟨h01234, h5⟩ := h012345.append
  obtain ⟨h0123, h4⟩ := h01234.append
  obtain ⟨h012, h3⟩ := h0123.append
  obtain ⟨h01, h2⟩ := h012.append
  obtain ⟨h0, h1⟩ := h01.append
  simp only [List.length_append, ← Nat.add_assoc] at h1 h2 h3 h4 h5
  refine armGprSpec.movi_spec (rd := .SP) (c := 0x123456789ABCDEF3#64) h0 ?_
  rintro s1 ⟨hsp1, hm1⟩ hfr1
  have heq1 : armMach.evalCond s1 .eq = true := by rw [hfr1.2.2 _ (by decide)]; exact heq
  have hcs1 : armMach.evalCond s1 .cs = true := by rw [hfr1.2.2 _ (by decide)]; exact hcs
  refine armGprSpec.mov_spec (rd := .reg .X0) (rs := .SP) h1 ?_
  rintro s2 ⟨hx0_2, hm2⟩ hfr2
  have hx0_val : armMach.getGpr s2 (.reg .X0) = 0x123456789ABCDEF3#64 := hx0_2.trans hsp1
  have hsp2 : armMach.getGpr s2 .SP = 0x123456789ABCDEF3#64 := by rw [hfr2.1 _ (by simp)]; exact hsp1
  have heq2 : armMach.evalCond s2 .eq = true := by rw [hfr2.2.2 _ (by decide)]; exact heq1
  have hcs2 : armMach.evalCond s2 .cs = true := by rw [hfr2.2.2 _ (by decide)]; exact hcs1
  have hok2 : storeOk (armMach.mem s2) .bool ((AddrArg.baseDisp .SP 16).eval (armMach.getGpr s2)) := by
    dsimp only [AddrArg.eval, armMach] at hm1 hm2 hsp2 hok ⊢
    rw [hm2, hm1, hsp2]
    exact hok
  refine armGprSpec.store_spec (t := .bool) (pa := .flag .eq) (a := .baseDisp .SP 16) (v := true)
    rfl (by simp [PArg.gprs, AddrArg.regs, armScratch]) heq2 hok2 h2 ?_
  rintro s3 hm3 hfr3
  have hx0_3 : armMach.getGpr s3 (.reg .X0) = 0x123456789ABCDEF3#64 := by
    rw [hfr3.1 _ (by simp [armScratch])]; exact hx0_val
  have hsp3 : armMach.getGpr s3 .SP = 0x123456789ABCDEF3#64 := by
    rw [hfr3.1 _ (by simp [armScratch])]; exact hsp2
  have hcs3 : armMach.evalCond s3 .cs = true := by rw [hfr3.2.2 _ (by decide)]; exact hcs2
  have hld3 : loadVal (armMach.mem s3) .bool ((AddrArg.baseDisp .SP 16).eval (armMach.getGpr s3)) = some true := by
    rw [hm3]
    have ha : (AddrArg.baseDisp .SP 16).eval (armMach.getGpr s2) =
        (AddrArg.baseDisp .SP 16).eval (armMach.getGpr s3) := by
      dsimp only [AddrArg.eval, armMach] at hsp2 hsp3 ⊢; rw [hsp2, hsp3]
    rw [← ha]
    exact loadVal_storeMem _ .bool _ true (by decide)
  refine armGprSpec.load_spec (t := .bool) (rd := .reg .X1) (a := .baseDisp .SP 16)
    rfl (by simp [armScratch]) (by simp [AddrArg.regs, armScratch]) hld3 h3 ?_
  rintro s4 ⟨hx1_4, _⟩ hfr4
  have hx0_4 : armMach.getGpr s4 (.reg .X0) = 0x123456789ABCDEF3#64 := by
    rw [hfr4.1 _ (by simp [armScratch])]; exact hx0_3
  have hcs4 : armMach.evalCond s4 .cs = true := by rw [hfr4.2.2 _ (by decide)]; exact hcs3
  refine armGprSpec.setcc_spec (rd := .SP) (c := .cs) (by simp [armScratch]) h4 ?_
  rintro s5 ⟨hsp5, _⟩ hfr5
  have hsp_true : GprHolds (armMach.getGpr s5 .SP) .bool true := by rw [hcs4] at hsp5; exact hsp5
  have hx0_5 : armMach.getGpr s5 (.reg .X0) = 0x123456789ABCDEF3#64 := by
    rw [hfr5.1 _ (by simp [armScratch])]; exact hx0_4
  have hx1_5 : GprHolds (armMach.getGpr s5 (.reg .X1)) .bool true := by
    rw [hfr5.1 _ (by simp [armScratch])]; exact hx1_4
  have hlbl : armMach.labelAddr spHost "L_taken" = armMach.addrOf spHost (spProg.length - 1) :=
    letI := spHost
    Host.label_eq_addrOf rfl ((Host.labelsUnique_of_nodup (by decide)).first rfl)
  refine armGprSpec.jnzGpr_spec (r := .SP) (l := "L_taken") (b := true)
    h5 hlbl (by simp [armScratch]) hsp_true ?_
  rintro s6 hfr6 _
  refine ⟨fun _ => armMach_run_end ⟨rfl, ?_, ?_, ?_⟩, fun hf => Bool.noConfusion hf⟩
  · rw [hfr6.1 _ (by simp [armScratch])]; exact hx0_5
  · rw [hfr6.1 _ (by simp [armScratch])]; exact hx1_5
  · rw [hfr6.1 _ (by simp [armScratch])]; exact hsp_true

def jnzFalseProg : List Directive :=
  (armGpr.jnzGpr (.reg .X2) "L_taken").1 ++ armGpr.mov (.reg .X3) (.reg .X2) ++ [.label "L_taken"]

theorem jnzFalseProg_small :
    (Kraken.Layout.apply iselLayout jnzFalseProg).sizeBefore jnzFalseProg.length < 2 ^ 64 := by
  have : (Kraken.Layout.apply iselLayout jnzFalseProg).sizeBefore jnzFalseProg.length = 8 := by
    simp only [Kraken.Layout.apply, Kraken.Executable.sizeBefore, Kraken.Layout.size,
      jnzFalseProg, armJnzGpr, armMov]
    decide
  omega

@[instance_reducible] def jnzFalseHost : Host := Host.ofLayout jnzFalseProg iselLayout jnzFalseProg_small

/-- `jnzGpr` takes fallthrough on `.bool false` even when bits `8..63` are all `1`. -/
theorem jnzGpr_false_witness {s : MachineData}
    (hx2 : armMach.getGpr s (.reg .X2) = 0xFFFFFFFFFFFFFF00#64) :
    armMach.Run jnzFalseHost 0 s fun st =>
      st.pc = armMach.addrOf jnzFalseHost 2 ∧
      armMach.getGpr st.data (.reg .X3) = 0xFFFFFFFFFFFFFF00#64 := by
  have hi : jnzFalseProg.IsInfixAt (armMach.prog jnzFalseHost) 0 := ⟨[], rfl⟩
  obtain ⟨h01, _⟩ := hi.append
  obtain ⟨h0, h1⟩ := h01.append
  have gx2 : GprHolds (armMach.getGpr s (.reg .X2)) .bool false := by
    change (armMach.getGpr s (.reg .X2)).setWidth 8 = 0#8
    rw [hx2]; rfl
  have hlbl : armMach.labelAddr jnzFalseHost "L_taken" = armMach.addrOf jnzFalseHost 2 :=
    letI := jnzFalseHost
    Host.label_eq_addrOf rfl ((Host.labelsUnique_of_nodup (by decide)).first rfl)
  refine armGprSpec.jnzGpr_spec (r := .reg .X2) (l := "L_taken") (b := false)
    h0 hlbl (by simp [armScratch]) gx2 ?_
  rintro s1 hfr1 _
  refine ⟨fun ht => Bool.noConfusion ht, fun _ => ?_⟩
  refine armGprSpec.mov_spec (rd := .reg .X3) (rs := .reg .X2) h1 ?_
  rintro s2 ⟨hx3, _⟩ _
  refine armMach_run_end ⟨rfl, ?_⟩
  rw [hx3, hfr1.1 _ (by simp [armScratch]), hx2]

/-! ## 8b. Full `armGpr` + `armFrame` `Bignum` Regression (`T7c-fix`) -/

@[expose] meta def armEmptyVecIsa : VecIsa Reg Empty ArmCond Directive where
  vecScratch := []
  vecAllocatable := []
  vecArgRegs := []
  vecRetRegs := []
  isAbiVec _ := false
  vecSlotWidth _ := none
  vmov _ _ _ := []
  vmovi _ _ _ := none
  vslotSt _ _ _ := []
  vslotLd _ _ _ := []
  vop _ _ _ _ := none
  vload _ _ _ := none
  vstore _ _ _ := none
  supportsVecOp _ _ := false

/-- Scalar AArch64 `Isa` combining `armGpr` and `armFrame`. -/
@[expose] meta def fullArm64Isa : Isa where
  Reg := Reg
  VReg := Empty
  Cond := ArmCond
  Directive := Directive
  gpr := armGpr
  vec := armEmptyVecIsa
  frame := armFrame

meta def armCompileMod (m : Module) : Except String (List Directive × List (Sym × Nat)) :=
  let hs := m.fns.map (Fn.computeHints fullArm64Isa LegalTarget.aarch64)
  compileModule fullArm64Isa LegalTarget.aarch64 fullArm64Isa.frame.raBytes [] m.exits 0 m.fns hs

#guard (armCompileMod Examples.Bignum.mul4x4Module).isOk = true
#guard (armCompileMod Examples.Bignum.addMod25519Module).isOk = true
#guard (armCompileMod Examples.Bignum.subMod25519Module).isOk = true

/-! ## 8c. C6 Scaled-Index, C1c Upper-32 Zeroing & Inline Constants -/

theorem armTarget_addrIdx_rfl :
    armTarget.toIsa.supportsAddrIdx (.bits 8) .s1 0 = true ∧
    armTarget.toIsa.supportsAddrIdx (.bits 16) .s2 0 = true ∧
    armTarget.toIsa.supportsAddrIdx (.bits 32) .s4 0 = true ∧
    armTarget.toIsa.supportsAddrIdx (.bits 64) .s8 0 = true ∧
    armTarget.toIsa.supportsAddrIdx (.bits 32) .s4 4 = false ∧
    armTarget.toIsa.supportsAddrIdx (.bits 64) .s4 0 = false ∧
    armTarget.toIsa.supportsAddrIdx (.bits 8) .s2 0 = false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem armLoadStore_addrIdx_neg_rfl :
    armGpr.load i32 (.reg .X0) (.baseIdxDisp (.reg .X1) (.reg .X2) .s4 4) = none ∧
    armGpr.load i32 (.reg .X0) (.baseIdxDisp .SP (.reg .X2) .s4 0) = none ∧
    armGpr.load i32 (.reg .X0) (.baseIdxDisp (.reg .X1) .SP .s4 0) = none ∧
    armGpr.load i64 (.reg .X0) (.baseIdxDisp (.reg .X1) (.reg .X2) .s4 0) = none ∧
    armGpr.store i32 (.gpr (.reg .X0)) (.baseIdxDisp (.reg .X1) (.reg .X2) .s4 4) = none ∧
    armGpr.store i64 (.gpr (.reg .X0)) (.baseIdxDisp .SP (.reg .X2) .s8 0) = none ∧
    (armGpr.load i32 (.reg .X0) (.baseIdxDisp (.reg .X1) (.reg .X2) .s4 0)).isSome = true ∧
    (armGpr.store i64 (.gpr (.reg .X0))
      (.baseIdxDisp (.reg .X1) (.reg .X2) .s8 0)).isSome = true := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem armZeroUpper32_rfl :
    armGpr.zeroUpper32Load = true ∧
    armGpr.elideZext32 = true ∧
    armGpr.zeroUpper32Op (.add i32) (.gpr (.reg .X1), .imm 1#32, ()) (.gpr (.reg .X0), ()) =
      true ∧
    armGpr.zeroUpper32Op (.sext 8 32) (.gpr (.reg .X1), ()) (.gpr (.reg .X0), ()) = true ∧
    armGpr.zeroUpper32Op (.zext 16 32) (.gpr (.reg .X1), ()) (.gpr (.reg .X0), ()) = true ∧
    armGpr.zeroUpper32Op (.add i64) (.gpr (.reg .X1), .imm 1#64, ()) (.gpr (.reg .X0), ()) =
      false ∧
    armGpr.zeroUpper32Op (.add i32) (.gpr (.reg .X1), .imm 1#32, ()) (.gpr .SP, ()) = false ∧
    armGpr.zeroUpper32Op (.copy .bool) (.gpr (.reg .X1), ()) (.gpr (.reg .X0), ()) = false := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

#guard (armGpr.movi (.reg .X0) 0#64).length == 1
#guard (armGpr.movi (.reg .X0) 0x1234#64).length == 1
#guard (armGpr.movi (.reg .X0) 0x12340000#64).length == 1
#guard (armGpr.movi (.reg .X0) (~~~0x1234#64)).length == 1
#guard (armGpr.movi (.reg .X0) 0x1234_0000_5678#64).length == 2
#guard (armGpr.movi (.reg .X0) (~~~0x1234_0000_5678#64)).length == 2
#guard (armGpr.movi (.reg .X0) 0x0123_4567_89AB_CDEF#64).length == 1
#guard ((armGpr.op (.add i64) (.gpr (.reg .X1), .imm 0x4000#64, ())
  (.gpr (.reg .X0), ()) .default).elim [] Prod.fst).length == 1
#guard ((armGpr.op (.sub i32) (.gpr (.reg .X1), .imm 0xFFF000#32, ())
  (.gpr (.reg .X0), ()) .default).elim [] Prod.fst).length == 1
#guard ((armGpr.op (.and i32) (.gpr (.reg .X1), .imm 0xFF#32, ())
  (.gpr (.reg .X0), ()) .default).elim [] Prod.fst).length == 1
#guard ((armGpr.op (.or i64) (.gpr (.reg .X1), .imm 0x0F0F0F0F_0F0F0F0F#64, ())
  (.gpr (.reg .X0), ()) .default).elim [] Prod.fst).length == 1

def c6C1cProg : List Directive :=
  (armGpr.load i32 (.reg .X0) (.baseIdxDisp (.reg .X1) (.reg .X2) .s4 0)).elim [] Prod.fst ++
  (armGpr.op (.add i32) (.gpr (.reg .X0), .imm 0x2000#32, ())
    (.gpr (.reg .X0), ()) .default).elim [] Prod.fst ++
  armGpr.movi (.reg .X3) 0x00120000_00000034#64 ++
  (armGpr.store i64 (.gpr (.reg .X0))
    (.baseIdxDisp (.reg .X1) (.reg .X2) .s8 0)).elim [] Prod.fst

theorem c6C1cProg_small :
    (Kraken.Layout.apply iselLayout c6C1cProg).sizeBefore c6C1cProg.length < 2 ^ 64 := by
  have : (Kraken.Layout.apply iselLayout c6C1cProg).sizeBefore c6C1cProg.length = 20 := by
    simp only [Kraken.Layout.apply, Kraken.Executable.sizeBefore, Kraken.Layout.size]
    decide
  omega

@[instance_reducible] def c6C1cHost : Host := Host.ofLayout c6C1cProg iselLayout c6C1cProg_small

/-- Execution witness combining C6 `[xb, xm, lsl #k]` load/store, C1c `load_zero32` +
`op_zero32` (32-bit `ADD_e` `.S12`), and 2-insn inline `MOVZ+MOVK`. -/
theorem c6_c1c_opt_witness {s : MachineData} {v : BitVec 32}
    (hld : loadVal (armMach.mem s) i32
      (armMach.getGpr s (.reg .X1) + (armMach.getGpr s (.reg .X2) <<< 2)) = some v)
    (hok : storeOk (armMach.mem s) i64
      (armMach.getGpr s (.reg .X1) + (armMach.getGpr s (.reg .X2) <<< 3))) :
    armMach.Run c6C1cHost 0 s fun st =>
      st.pc = armMach.addrOf c6C1cHost c6C1cProg.length ∧
      armMach.getGpr st.data (.reg .X0) = (v + 0x2000#32).setWidth 64 ∧
      armMach.getGpr st.data (.reg .X3) = 0x00120000_00000034#64 ∧
      armMach.mem st.data = storeMem (armMach.mem s) i64
        (armMach.getGpr s (.reg .X1) + (armMach.getGpr s (.reg .X2) <<< 3))
        ((v + 0x2000#32).setWidth 64) := by
  have hi : c6C1cProg.IsInfixAt (armMach.prog c6C1cHost) 0 := ⟨[], rfl⟩
  obtain ⟨h012, h3⟩ := hi.append
  obtain ⟨h01, h2⟩ := h012.append
  obtain ⟨h0, h1⟩ := h01.append
  simp only [List.length_append, ← Nat.add_assoc] at h1 h2 h3
  have ha0 : (AddrArg.baseIdxDisp (.reg .X1) (.reg .X2) .s4 0).eval (armMach.getGpr s) =
      armMach.getGpr s (.reg .X1) + (armMach.getGpr s (.reg .X2) <<< 2) := by
    simp [AddrArg.eval, AddrScale.shift]
  refine armGprSpec.load_zero32 rfl (rd := .reg .X0) (a := .baseIdxDisp (.reg .X1) (.reg .X2) .s4 0)
    rfl (by simp [armScratch]) (by simp [AddrArg.regs, armScratch])
    (by rw [ha0]; exact hld) h0 ?_
  rintro s1 ⟨hx0_1, hm1⟩ hfr1
  have hp1 : armMach.PArgHolds s1 i32 (.gpr (.reg .X0)) v := by
    refine ⟨by decide, ?_⟩
    rw [hx0_1, BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq]
  have hrel1 : TRel (armMach.PArgHolds s1) (as := [i32, i32])
      (.gpr (.reg .X0), .imm 0x2000#32, ()) (v, 0x2000#32, ()) :=
    .cons hp1 (.cons rfl .nil)
  refine armGprSpec.op_zero32 (code := .add i32)
    (pas := (.gpr (.reg .X0), .imm 0x2000#32, ())) (dsts := (.gpr (.reg .X0), ()))
    (rd := .reg .X0) (vh := .default) (P := fun r => r = (v + 0x2000#32, ()))
    rfl rfl rfl (by simp [tupArgGprs, PArg.gprs, armScratch]) (by simp [armScratch])
    hrel1 rfl h1 ?_
  rintro s2 ⟨⟨rv, hrv, hx0_2⟩, hm2⟩ hfr2
  have hx0_2' : armMach.getGpr s2 (.reg .X0) = (v + 0x2000#32).setWidth 64 := by
    rw [hx0_2, (Prod.mk.inj hrv).1]
  refine armGprSpec.movi_spec (rd := .reg .X3) (c := 0x00120000_00000034#64) h2 ?_
  rintro s3 ⟨hx3_3, hm3⟩ hfr3
  have hx0_3 : armMach.getGpr s3 (.reg .X0) = (v + 0x2000#32).setWidth 64 := by
    rw [hfr3.1 _ (by simp [armScratch])]; exact hx0_2'
  have hx1_3 : armMach.getGpr s3 (.reg .X1) = armMach.getGpr s (.reg .X1) := by
    rw [hfr3.1 _ (by simp [armScratch]), hfr2.1 _ (by simp [armScratch]),
      hfr1.1 _ (by simp [armScratch])]
  have hx2_3 : armMach.getGpr s3 (.reg .X2) = armMach.getGpr s (.reg .X2) := by
    rw [hfr3.1 _ (by simp [armScratch]), hfr2.1 _ (by simp [armScratch]),
      hfr1.1 _ (by simp [armScratch])]
  have ha3 : (AddrArg.baseIdxDisp (.reg .X1) (.reg .X2) .s8 0).eval (armMach.getGpr s3) =
      armMach.getGpr s (.reg .X1) + (armMach.getGpr s (.reg .X2) <<< 3) := by
    calc (AddrArg.baseIdxDisp (.reg .X1) (.reg .X2) .s8 0).eval (armMach.getGpr s3)
        = armMach.getGpr s3 (.reg .X1) + (armMach.getGpr s3 (.reg .X2) <<< 3) := by
          simp [AddrArg.eval, AddrScale.shift]
      _ = armMach.getGpr s (.reg .X1) + (armMach.getGpr s (.reg .X2) <<< 3) := by
          rw [hx1_3, hx2_3]
  have hm3' : armMach.mem s3 = armMach.mem s := hm3.trans (hm2.trans hm1)
  have hok3 : storeOk (armMach.mem s3) i64
      ((AddrArg.baseIdxDisp (.reg .X1) (.reg .X2) .s8 0).eval (armMach.getGpr s3)) := by
    rw [hm3', ha3]; exact hok
  have hp3 : armMach.PArgHolds s3 i64 (.gpr (.reg .X0)) ((v + 0x2000#32).setWidth 64) :=
    ⟨by decide, by rw [hx0_3, BitVec.setWidth_eq]⟩
  refine armGprSpec.store_spec rfl (by simp [PArg.gprs, AddrArg.regs, armScratch])
    hp3 hok3 h3 ?_
  rintro s4 hm4 hfr4
  refine armMach_run_end ⟨rfl, ?_, ?_, ?_⟩
  · rw [hfr4.1 _ (by simp [armScratch])]; exact hx0_3
  · rw [hfr4.1 _ (by simp [armScratch])]; exact hx3_3
  · rw [hm4, hm3', ha3]

/-! ## 9. Standard-axiom audit -/

#print axioms LeanQbe.T.Arm64.armGprSpec
#print axioms LeanQbe.T.Arm64.armClearFlags_noLab
#print axioms LeanQbe.T.Arm64.armMov_noLab
#print axioms LeanQbe.T.Arm64.armMovi_noLab
#print axioms LeanQbe.T.Arm64.armSetcc_noLab
#print axioms LeanQbe.T.Arm64.armJmp_noLab
#print axioms LeanQbe.T.Arm64.armJcc_noLab
#print axioms LeanQbe.T.Arm64.armJnzGpr_noLab
#print axioms LeanQbe.T.Arm64.armLoad_noLab
#print axioms LeanQbe.T.Arm64.armStore_noLab
#print axioms LeanQbe.T.Arm64.armOp_noLab
#print axioms div0_witness
#print axioms bitCount_witness
#print axioms carry_borrow_chain_witness
#print axioms mul_funnel_select_witness
#print axioms subword_garbage_witness
#print axioms sp_corner_witness
#print axioms jnzGpr_false_witness
#print axioms c6_c1c_opt_witness

end LeanQbeTest.T.Arm64IselTest
