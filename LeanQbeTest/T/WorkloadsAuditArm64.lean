module

import LeanQbe.T.Arm64.ChaCha
import LeanQbe.T.Arm64.Bignum
import LeanQbe.T.Arm64.UnionFind
import LeanQbe.T.Logic.MemLemmas

/-!
# Verified Workloads (`ChaCha20`, `Curve25519 Bignum`, `UnionFind`) — AAPCS64 AArch64 Audit

Self-contained machine-level audit for compiled `chacha20Block` (scalarized from `v4i32` by the
verified `armLegalTarget` pass), Curve25519 bignum kernels (`mul4x4`, `addMod25519`,
`subMod25519`), and Union-Find (`find`, `union`, `unionInline`) on AAPCS64 AArch64
(`Kraken.AArch64`). This module imports only `Kraken.AArch64` (`LeanQbe.T.Arm64.*`), never
`Kraken.X64`.

## What This Workstream Proves
1. **ChaCha20 block (`Arm64.ChaCha`)**:
   * Closed Kraken AArch64 `Eventually (step1 Host.exe)` correctness (`audit_chacha`) proving
     that scalarized `chacha20Block` writes `(rfcChaCha20Core init).toRows` to `out` (`X0`) from
     `inp` (`X1`), restoring callee-saved registers (`X19`..`X29`) and `SP`.
   * Concrete RFC 8439 §2.3.2 execution witness (`audit_chacha_rfc`) checking all 64 output bytes.
2. **Curve25519 Bignum (`Arm64.Bignum`)**:
   * Closed Kraken AArch64 correctness for `mul4x4`, `addMod25519`, and `subMod25519`
     (`audit_mul4x4`, `audit_add25519`, `audit_sub25519`) plus concrete wrapping witnesses
     (`audit_mul4x4_nv`, `audit_add_nv`, `audit_sub_nv`).
3. **Union-Find (`Arm64.UnionFind`)**:
   * Closed Kraken AArch64 correctness for `find`, `union` (cross-function calls), and
     `unionInline` (`audit_uf_find`, `audit_uf_union`, `audit_union_in`) plus concrete execution
     witnesses (`audit_uf_nv`).

## Inputs / Assumptions
* Arbitrary Kraken AArch64 `Host` containing the compiled directive list as an infix with
  `Host.LabelsUnique`, AAPCS64 16-byte stack alignment (`SP % 16 = 0`), return address `ra` in
  `X30`, and disjoint caller-owned buffers/frame `R`.

## Trusted Computing Base (TCB)
* Lean 4 kernel (`propext`, `Classical.choice`, `Quot.sound`).
* Kraken AArch64 operational semantics (`Kraken.AArch64.step1`, `Host.exe`, `MachineData`,
  `Mem 64`).
* Functional specifications (`rfcChaCha20Core`, `limbsVal`, `p25519`, `Forest` / `merge`).
* The compiler pipeline (`earlyOpt`, `legal`, `lateOpt`, `Rega.lowerFn`, `armTarget`) is
  **verified**, not in the TCB.
-/

set_option autoImplicit false

section

namespace WorkloadsAuditArm64

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.Arm64 Kraken
open LeanQbe.T.Examples

/-! ## 1. ChaCha20 Block (Scalarized) on AArch64 -/

theorem audit_chacha [hh : Host] (k₀ : Nat)
    (hc : Arm64.ChaCha.compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (out inp : BitVec 64) (init : ChaCha.State) (old : List ChaCha.Row) (hold : old.length = 4)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hout : (s.regs.getXReg .X0).toBitVec = out)
    (hinp : (s.regs.getXReg .X1).toBitVec = inp)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (array (t := v4i32) out old ⋆ array (t := v4i32) inp init.toRows) ⋆
      region (s.regs.SP.toBitVec -
          BitVec.ofNat 64 (Arm64.ChaCha.compiled.bound "chacha20Block"))
        (Arm64.ChaCha.compiled.bound "chacha20Block") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆
          (array (t := v4i32) out (ChaCha.rfcChaCha20Core init).toRows ⋆
            array (t := v4i32) inp init.toRows) ⋆
          region (s.regs.SP.toBitVec -
              BitVec.ofNat 64 (Arm64.ChaCha.compiled.bound "chacha20Block"))
            (Arm64.ChaCha.compiled.bound "chacha20Block") ⋆ R))
      ⟨s, Labels.label "chacha20Block"⟩ :=
  Arm64.ChaCha.chacha20Block_arm64_correct (hh := hh) k₀ hc hu out inp init old hold s ra R
    hout hinp hra hsp hmem

attribute [local instance] Arm64.ChaCha.chachaHost in
theorem audit_chacha_rfc :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧
        st.data.dmem.loadBytes 0x1000#64 64 = some ChaCha.rfc8439_expected_bytes ∧
        ∃ res : ChaCha.State,
          res.toWords = ChaCha.rfc8439_expected_words ∧
          res.toBytes = ChaCha.rfc8439_expected_bytes ∧
          (st.data.dmem =⋆
            (array (t := v4i32) 0x1000#64 res.toRows ⋆
              array (t := v4i32) 0x1040#64 ChaCha.rfc8439_test_init.toRows) ⋆
            region (0x1000#64 -
                BitVec.ofNat 64 (Arm64.ChaCha.compiled.bound "chacha20Block"))
              (Arm64.ChaCha.compiled.bound "chacha20Block") ⋆ emp))
      ⟨Arm64.ChaCha.chachaState0, Labels.label "chacha20Block"⟩ :=
  Arm64.ChaCha.rfc8439_vector_arm64_nonvacuous

/-! ## 2. Curve25519 Bignum Kernels on AArch64 -/

theorem audit_mul4x4 [hh : Host] (k₀ : Nat)
    (hc : Arm64.Bignum.mul4x4Compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (out pa pb : BitVec 64) (as bs out0 : List (BitVec 64))
    (has : as.length = 4) (hbs : bs.length = 4) (hout : out0.length = 8)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hout_reg : (s.regs.getXReg .X0).toBitVec = out)
    (hpa : (s.regs.getXReg .X1).toBitVec = pa)
    (hpb : (s.regs.getXReg .X2).toBitVec = pb)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ (array64 out out0 ⋆ array64 pa as ⋆ array64 pb bs) ⋆
      region (s.regs.SP.toBitVec -
          BitVec.ofNat 64 (Arm64.Bignum.mul4x4Compiled.bound "mul4x4"))
        (Arm64.Bignum.mul4x4Compiled.bound "mul4x4") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆
          (fun m' => ∃ rs : List (BitVec 64), rs.length = 8 ∧
            limbsVal rs = limbsVal as * limbsVal bs ∧
            (array64 out rs ⋆ array64 pa as ⋆ array64 pb bs) m') ⋆
          region (s.regs.SP.toBitVec -
              BitVec.ofNat 64 (Arm64.Bignum.mul4x4Compiled.bound "mul4x4"))
            (Arm64.Bignum.mul4x4Compiled.bound "mul4x4") ⋆ R))
      ⟨s, Labels.label "mul4x4"⟩ :=
  Arm64.Bignum.mul4x4_arm64_correct (hh := hh) k₀ hc hu out pa pb as bs out0 has hbs hout
    s ra R hout_reg hpa hpb hra hsp hmem

theorem audit_add25519 [hh : Host] (k₀ : Nat)
    (hc : Arm64.Bignum.addMod25519Compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (out pa pb : BitVec 64) (as bs out0 : List (BitVec 64))
    (has : as.length = 4) (hbs : bs.length = 4) (hout : out0.length = 4)
    (ha_lt : limbsVal as < Bignum.p25519) (hb_lt : limbsVal bs < Bignum.p25519)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hout_reg : (s.regs.getXReg .X0).toBitVec = out)
    (hpa : (s.regs.getXReg .X1).toBitVec = pa)
    (hpb : (s.regs.getXReg .X2).toBitVec = pb)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ (array64 out out0 ⋆ array64 pa as ⋆ array64 pb bs) ⋆
      region (s.regs.SP.toBitVec -
          BitVec.ofNat 64 (Arm64.Bignum.addMod25519Compiled.bound "addMod25519"))
        (Arm64.Bignum.addMod25519Compiled.bound "addMod25519") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆
          (fun m' => ∃ rs : List (BitVec 64), rs.length = 4 ∧
            limbsVal rs = (limbsVal as + limbsVal bs) % Bignum.p25519 ∧
            limbsVal rs < Bignum.p25519 ∧
            (array64 out rs ⋆ array64 pa as ⋆ array64 pb bs) m') ⋆
          region (s.regs.SP.toBitVec -
              BitVec.ofNat 64 (Arm64.Bignum.addMod25519Compiled.bound "addMod25519"))
            (Arm64.Bignum.addMod25519Compiled.bound "addMod25519") ⋆ R))
      ⟨s, Labels.label "addMod25519"⟩ :=
  Arm64.Bignum.addMod25519_arm64_correct (hh := hh) k₀ hc hu out pa pb as bs out0 has hbs hout
    ha_lt hb_lt s ra R hout_reg hpa hpb hra hsp hmem

theorem audit_sub25519 [hh : Host] (k₀ : Nat)
    (hc : Arm64.Bignum.subMod25519Compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (out pa pb : BitVec 64) (as bs out0 : List (BitVec 64))
    (has : as.length = 4) (hbs : bs.length = 4) (hout : out0.length = 4)
    (ha_lt : limbsVal as < Bignum.p25519) (hb_lt : limbsVal bs < Bignum.p25519)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hout_reg : (s.regs.getXReg .X0).toBitVec = out)
    (hpa : (s.regs.getXReg .X1).toBitVec = pa)
    (hpb : (s.regs.getXReg .X2).toBitVec = pb)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ (array64 out out0 ⋆ array64 pa as ⋆ array64 pb bs) ⋆
      region (s.regs.SP.toBitVec -
          BitVec.ofNat 64 (Arm64.Bignum.subMod25519Compiled.bound "subMod25519"))
        (Arm64.Bignum.subMod25519Compiled.bound "subMod25519") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆
          (fun m' => ∃ rs : List (BitVec 64), rs.length = 4 ∧
            limbsVal rs = (if limbsVal bs ≤ limbsVal as then limbsVal as - limbsVal bs
                           else limbsVal as + Bignum.p25519 - limbsVal bs) ∧
            limbsVal rs < Bignum.p25519 ∧
            (array64 out rs ⋆ array64 pa as ⋆ array64 pb bs) m') ⋆
          region (s.regs.SP.toBitVec -
              BitVec.ofNat 64 (Arm64.Bignum.subMod25519Compiled.bound "subMod25519"))
            (Arm64.Bignum.subMod25519Compiled.bound "subMod25519") ⋆ R))
      ⟨s, Labels.label "subMod25519"⟩ :=
  Arm64.Bignum.subMod25519_arm64_correct (hh := hh) k₀ hc hu out pa pb as bs out0 has hbs hout
    ha_lt hb_lt s ra R hout_reg hpa hpb hra hsp hmem

attribute [local instance] Arm64.Bignum.mul4x4Host in
theorem audit_mul4x4_nv :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧
        (st.data.dmem =⋆
          (fun m' => ∃ rs : List (BitVec 64), rs.length = 8 ∧
            limbsVal rs = limbsVal Arm64.Bignum.nvMulA * limbsVal Arm64.Bignum.nvMulB ∧
            (array64 0x1000#64 rs ⋆ array64 0x1040#64 Arm64.Bignum.nvMulA ⋆
              array64 0x1060#64 Arm64.Bignum.nvMulB) m') ⋆
          region (0x1000#64 -
              BitVec.ofNat 64 (Arm64.Bignum.mul4x4Compiled.bound "mul4x4"))
            (Arm64.Bignum.mul4x4Compiled.bound "mul4x4") ⋆ emp))
      ⟨Arm64.Bignum.mul4x4State0, Labels.label "mul4x4"⟩ :=
  Arm64.Bignum.mul4x4_arm64_nonvacuous

attribute [local instance] Arm64.Bignum.addMod25519Host in
theorem audit_add_nv :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧
        (st.data.dmem =⋆
          (fun m' => ∃ rs : List (BitVec 64), rs.length = 4 ∧ limbsVal rs = 19 ∧
            (array64 0x1000#64 rs ⋆ array64 0x1020#64 Arm64.Bignum.nvAddA ⋆
              array64 0x1040#64 Arm64.Bignum.nvAddB) m') ⋆
          region (0x1000#64 -
              BitVec.ofNat 64 (Arm64.Bignum.addMod25519Compiled.bound "addMod25519"))
            (Arm64.Bignum.addMod25519Compiled.bound "addMod25519") ⋆ emp))
      ⟨Arm64.Bignum.addMod25519State0, Labels.label "addMod25519"⟩ :=
  Arm64.Bignum.addMod25519_arm64_nonvacuous

attribute [local instance] Arm64.Bignum.subMod25519Host in
theorem audit_sub_nv :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧
        (st.data.dmem =⋆
          (fun m' => ∃ rs : List (BitVec 64), rs.length = 4 ∧
            limbsVal rs = Bignum.p25519 - 20 ∧
            (array64 0x1000#64 rs ⋆ array64 0x1020#64 Arm64.Bignum.nvSubA ⋆
              array64 0x1040#64 Arm64.Bignum.nvSubB) m') ⋆
          region (0x1000#64 -
              BitVec.ofNat 64 (Arm64.Bignum.subMod25519Compiled.bound "subMod25519"))
            (Arm64.Bignum.subMod25519Compiled.bound "subMod25519") ⋆ emp))
      ⟨Arm64.Bignum.subMod25519State0, Labels.label "subMod25519"⟩ :=
  Arm64.Bignum.subMod25519_arm64_nonvacuous

/-! ## 3. Union-Find (`find`, `union`, `unionInline`) on AArch64 -/

theorem audit_uf_find [hh : Host] (k₀ : Nat)
    (hc : Arm64.UnionFind.compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (p x : BitVec 64) (n : Nat) (rep : BitVec 64 → BitVec 64) (hx : x.toNat < n)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hp : (s.regs.getXReg .X0).toBitVec = p) (hxx : (s.regs.getXReg .X1).toBitVec = x)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ UnionFind.uf p n rep ⋆
      region (s.regs.SP.toBitVec -
          BitVec.ofNat 64 (Arm64.UnionFind.compiled.bound "find"))
        (Arm64.UnionFind.compiled.bound "find") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ (st.data.regs.getXReg .X0).toBitVec = rep x ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆ UnionFind.uf p n rep ⋆
          region (s.regs.SP.toBitVec -
              BitVec.ofNat 64 (Arm64.UnionFind.compiled.bound "find"))
            (Arm64.UnionFind.compiled.bound "find") ⋆ R))
      ⟨s, Labels.label "find"⟩ :=
  Arm64.UnionFind.find_arm64_correct (hh := hh) k₀ hc hu p x n rep hx s ra R hp hxx hra hsp hmem

theorem audit_uf_union [hh : Host] (k₀ : Nat)
    (hc : Arm64.UnionFind.compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (p x y : BitVec 64) (n : Nat) (rep : BitVec 64 → BitVec 64)
    (hx : x.toNat < n) (hy : y.toNat < n) (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hp : (s.regs.getXReg .X0).toBitVec = p) (hxx : (s.regs.getXReg .X1).toBitVec = x)
    (hyy : (s.regs.getXReg .X2).toBitVec = y)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ UnionFind.uf p n rep ⋆
      region (s.regs.SP.toBitVec -
          BitVec.ofNat 64 (Arm64.UnionFind.compiled.bound "union"))
        (Arm64.UnionFind.compiled.bound "union") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆ UnionFind.uf p n (UnionFind.merge rep x y) ⋆
          region (s.regs.SP.toBitVec -
              BitVec.ofNat 64 (Arm64.UnionFind.compiled.bound "union"))
            (Arm64.UnionFind.compiled.bound "union") ⋆ R))
      ⟨s, Labels.label "union"⟩ :=
  Arm64.UnionFind.union_arm64_correct (hh := hh) k₀ hc hu p x y n rep hx hy s ra R
    hp hxx hyy hra hsp hmem

theorem audit_union_in [hh : Host] (k₀ : Nat)
    (hc : Arm64.UnionFind.compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (p x y : BitVec 64) (n : Nat) (rep : BitVec 64 → BitVec 64)
    (hx : x.toNat < n) (hy : y.toNat < n) (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hp : (s.regs.getXReg .X0).toBitVec = p) (hxx : (s.regs.getXReg .X1).toBitVec = x)
    (hyy : (s.regs.getXReg .X2).toBitVec = y)
    (hra : s.regs.X30 = ra.toUInt64) (hsp : s.regs.SP.toNat % 16 = 0)
    (hmem : s.dmem =⋆ UnionFind.uf p n rep ⋆
      region (s.regs.SP.toBitVec -
          BitVec.ofNat 64 (Arm64.UnionFind.compiled.bound "unionInline"))
        (Arm64.UnionFind.compiled.bound "unionInline") ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [XReg.X19, .X20, .X21, .X22, .X23, .X24, .X25, .X26, .X27, .X28, .X29],
          st.data.regs.getXReg r = s.regs.getXReg r) ∧
        st.data.regs.SP = s.regs.SP ∧
        (st.data.dmem =⋆ UnionFind.uf p n (UnionFind.merge rep x y) ⋆
          region (s.regs.SP.toBitVec -
              BitVec.ofNat 64 (Arm64.UnionFind.compiled.bound "unionInline"))
            (Arm64.UnionFind.compiled.bound "unionInline") ⋆ R))
      ⟨s, Labels.label "unionInline"⟩ :=
  Arm64.UnionFind.unionInline_arm64_correct (hh := hh) k₀ hc hu p x y n rep hx hy s ra R
    hp hxx hyy hra hsp hmem

attribute [local instance] Arm64.UnionFind.ufHost in
theorem audit_uf_nv :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ (st.data.regs.getXReg .X0).toBitVec = 3#64 ∧
        (st.data.dmem =⋆ UnionFind.uf 0x1000#64 4 id ⋆
          region (0x1000#64 - BitVec.ofNat 64 (Arm64.UnionFind.compiled.bound "find"))
            (Arm64.UnionFind.compiled.bound "find") ⋆ emp))
      ⟨Arm64.UnionFind.findState0, Labels.label "find"⟩ ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧
        (st.data.dmem =⋆ UnionFind.uf 0x1000#64 4 (UnionFind.merge id 1 2) ⋆
          region (0x1000#64 - BitVec.ofNat 64 (Arm64.UnionFind.compiled.bound "union"))
            (Arm64.UnionFind.compiled.bound "union") ⋆ emp) ∧
        UnionFind.merge id 1 2 1 = UnionFind.merge id 1 2 2 ∧
        UnionFind.merge id 1 2 0 ≠ UnionFind.merge id 1 2 1)
      ⟨Arm64.UnionFind.unionState0, Labels.label "union"⟩ ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧
        (st.data.dmem =⋆ UnionFind.uf 0x1000#64 4 (UnionFind.merge id 1 2) ⋆
          region (0x1000#64 - BitVec.ofNat 64 (Arm64.UnionFind.compiled.bound "unionInline"))
            (Arm64.UnionFind.compiled.bound "unionInline") ⋆ emp) ∧
        UnionFind.merge id 1 2 1 = UnionFind.merge id 1 2 2 ∧
        UnionFind.merge id 1 2 0 ≠ UnionFind.merge id 1 2 1)
      ⟨Arm64.UnionFind.unionInlineState0, Labels.label "unionInline"⟩ :=
  ⟨Arm64.UnionFind.find_arm64_nonvacuous,
   Arm64.UnionFind.union_arm64_nonvacuous,
   Arm64.UnionFind.unionInline_arm64_nonvacuous⟩

/-! ## 4. Logical Foundations Audit (`#print axioms`) -/

#print axioms audit_chacha
#print axioms audit_chacha_rfc
#print axioms audit_mul4x4
#print axioms audit_add25519
#print axioms audit_sub25519
#print axioms audit_mul4x4_nv
#print axioms audit_add_nv
#print axioms audit_sub_nv
#print axioms audit_uf_find
#print axioms audit_uf_union
#print axioms audit_union_in
#print axioms audit_uf_nv

end WorkloadsAuditArm64
