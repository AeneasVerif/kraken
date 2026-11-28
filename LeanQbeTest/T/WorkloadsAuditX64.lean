module

import LeanQbe.T.Amd64.ChaCha
import LeanQbe.T.Amd64.Bignum
import LeanQbe.T.Amd64.UnionFind
import LeanQbe.T.Logic.MemLemmas

/-!
# Verified Workloads (`ChaCha20`, `Curve25519 Bignum`, `UnionFind`) — SysV x86-64 Machine Audit

Self-contained machine-level audit for compiled `chacha20Block` (128-bit `v4i32` SIMD),
Curve25519 bignum kernels (`mul4x4` using `mulx`/`adcx`/`adox` with zero `setcc`,
`addMod25519`, `subMod25519`), and Union-Find (`find`, `union`, `unionInline`) on SysV x86-64
(`Kraken.X64`). This module imports only `Kraken.X64` (`LeanQbe.T.Amd64.*`), never
`Kraken.AArch64`.

## What This Workstream Proves
1. **ChaCha20 block (`Amd64.ChaCha`)**:
   * Closed Kraken x64 `Eventually (step1 Host.exe)` correctness (`audit_chacha`) writing
     `(rfcChaCha20Core init).toRows` to `out` (`rdi`) from `inp` (`rsi`), restoring callee-saved
     registers and stack.
   * Concrete RFC 8439 §2.3.2 execution witness (`audit_chacha_rfc`) checking all 64 output bytes.
2. **Curve25519 Bignum (`Amd64.Bignum`)**:
   * Closed Kraken x64 correctness for `mul4x4`, `addMod25519`, and `subMod25519` (`audit_mul4x4`,
     `audit_add25519`, `audit_sub25519`) plus concrete wrapping witnesses (`audit_mul4x4_nv`,
     `audit_add_nv`, `audit_sub_nv`) and instruction checks (`11 mulx`, `12 adcx`,
     `12 adox`, `0 setcc`).
3. **Union-Find (`Amd64.UnionFind`)**:
   * Closed Kraken x64 correctness for `find`, `union` (cross-function calls), and `unionInline`
     (`audit_uf_find`, `audit_uf_union`, `audit_union_in`) plus concrete execution witnesses.

## Inputs / Assumptions
* Arbitrary Kraken x64 `Host` containing the compiled directive list as an infix with
  `Host.LabelsUnique`, SysV 16-byte stack alignment (`(rsp + 8) % 16 = 0`), return address `ra`
  at `rsp`, and disjoint caller-owned buffers/frame `R`.

## Trusted Computing Base (TCB)
* Lean 4 kernel (`propext`, `Classical.choice`, `Quot.sound`).
* Kraken x86-64 operational semantics (`Kraken.X64.step1`, `Host.exe`, `MachineData`, `Mem 64`).
* Functional specifications (`rfcChaCha20Core`, `limbsVal`, `p25519`, `Forest` / `merge`).
* The compiler pipeline (`earlyOpt`, `legal`, `lateOpt`, `Rega.lowerFn`, `x64Target`) is
  **verified**, not in the TCB.
-/

set_option autoImplicit false

section

namespace WorkloadsAuditX64

open Std Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.Amd64 Kraken
open LeanQbe.T.Examples

/-! ## 1. ChaCha20 Block (`v4i32` SIMD) on x86-64 -/

theorem audit_chacha [hh : Host] (k₀ : Nat)
    (hc : Amd64.ChaCha.compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (out inp : BitVec 64) (init : ChaCha.State) (old : List ChaCha.Row) (hold : old.length = 4)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hout : s.regs.get64 .rdi = out) (hinp : s.regs.get64 .rsi = inp)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆
      (array (t := v4i32) out old ⋆ array (t := v4i32) inp init.toRows) ⋆
      (region (s.regs.get64 .rsp -
          BitVec.ofNat 64 (Amd64.ChaCha.compiled.bound "chacha20Block"))
          (Amd64.ChaCha.compiled.bound "chacha20Block") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆
          (array (t := v4i32) out (ChaCha.rfcChaCha20Core init).toRows ⋆
            array (t := v4i32) inp init.toRows) ⋆
          region (s.regs.get64 .rsp -
              BitVec.ofNat 64 (Amd64.ChaCha.compiled.bound "chacha20Block"))
            (Amd64.ChaCha.compiled.bound "chacha20Block" + 8) ⋆ R))
      ⟨s, Labels.label "chacha20Block"⟩ :=
  Amd64.ChaCha.chacha20Block_x64_correct (hh := hh) k₀ hc hu out inp init old hold s ra R
    hout hinp hsp hmem

attribute [local instance] Amd64.ChaCha.chachaHost in
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
            region (0x0ff8#64 -
                BitVec.ofNat 64 (Amd64.ChaCha.compiled.bound "chacha20Block"))
              (Amd64.ChaCha.compiled.bound "chacha20Block" + 8) ⋆ emp))
      ⟨Amd64.ChaCha.chachaState0, Labels.label "chacha20Block"⟩ :=
  Amd64.ChaCha.rfc8439_vector_x64_nonvacuous

/-! ## 2. Curve25519 Bignum Kernels on x86-64 -/

theorem audit_mul4x4 [hh : Host] (k₀ : Nat)
    (hc : Amd64.Bignum.mul4x4Compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (out pa pb : BitVec 64) (as bs out0 : List (BitVec 64))
    (has : as.length = 4) (hbs : bs.length = 4) (hout : out0.length = 8)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hout_reg : s.regs.get64 .rdi = out) (hpa : s.regs.get64 .rsi = pa)
    (hpb : s.regs.get64 .rdx = pb) (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ (array64 out out0 ⋆ array64 pa as ⋆ array64 pb bs) ⋆
      (region (s.regs.get64 .rsp -
          BitVec.ofNat 64 (Amd64.Bignum.mul4x4Compiled.bound "mul4x4"))
          (Amd64.Bignum.mul4x4Compiled.bound "mul4x4") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆
          (fun m' => ∃ rs : List (BitVec 64), rs.length = 8 ∧
            limbsVal rs = limbsVal as * limbsVal bs ∧
            (array64 out rs ⋆ array64 pa as ⋆ array64 pb bs) m') ⋆
          region (s.regs.get64 .rsp -
              BitVec.ofNat 64 (Amd64.Bignum.mul4x4Compiled.bound "mul4x4"))
            (Amd64.Bignum.mul4x4Compiled.bound "mul4x4" + 8) ⋆ R))
      ⟨s, Labels.label "mul4x4"⟩ :=
  Amd64.Bignum.mul4x4_x64_correct (hh := hh) k₀ hc hu out pa pb as bs out0 has hbs hout
    s ra R hout_reg hpa hpb hsp hmem

theorem audit_add25519 [hh : Host] (k₀ : Nat)
    (hc : Amd64.Bignum.addMod25519Compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (out pa pb : BitVec 64) (as bs out0 : List (BitVec 64))
    (has : as.length = 4) (hbs : bs.length = 4) (hout : out0.length = 4)
    (ha_lt : limbsVal as < Bignum.p25519) (hb_lt : limbsVal bs < Bignum.p25519)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hout_reg : s.regs.get64 .rdi = out) (hpa : s.regs.get64 .rsi = pa)
    (hpb : s.regs.get64 .rdx = pb) (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ (array64 out out0 ⋆ array64 pa as ⋆ array64 pb bs) ⋆
      (region (s.regs.get64 .rsp -
          BitVec.ofNat 64 (Amd64.Bignum.addMod25519Compiled.bound "addMod25519"))
          (Amd64.Bignum.addMod25519Compiled.bound "addMod25519") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆
          (fun m' => ∃ rs : List (BitVec 64), rs.length = 4 ∧
            limbsVal rs = (limbsVal as + limbsVal bs) % Bignum.p25519 ∧
            limbsVal rs < Bignum.p25519 ∧
            (array64 out rs ⋆ array64 pa as ⋆ array64 pb bs) m') ⋆
          region (s.regs.get64 .rsp -
              BitVec.ofNat 64 (Amd64.Bignum.addMod25519Compiled.bound "addMod25519"))
            (Amd64.Bignum.addMod25519Compiled.bound "addMod25519" + 8) ⋆ R))
      ⟨s, Labels.label "addMod25519"⟩ :=
  Amd64.Bignum.addMod25519_x64_correct (hh := hh) k₀ hc hu out pa pb as bs out0 has hbs hout
    ha_lt hb_lt s ra R hout_reg hpa hpb hsp hmem

theorem audit_sub25519 [hh : Host] (k₀ : Nat)
    (hc : Amd64.Bignum.subMod25519Compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (out pa pb : BitVec 64) (as bs out0 : List (BitVec 64))
    (has : as.length = 4) (hbs : bs.length = 4) (hout : out0.length = 4)
    (ha_lt : limbsVal as < Bignum.p25519) (hb_lt : limbsVal bs < Bignum.p25519)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hout_reg : s.regs.get64 .rdi = out) (hpa : s.regs.get64 .rsi = pa)
    (hpb : s.regs.get64 .rdx = pb) (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ (array64 out out0 ⋆ array64 pa as ⋆ array64 pb bs) ⋆
      (region (s.regs.get64 .rsp -
          BitVec.ofNat 64 (Amd64.Bignum.subMod25519Compiled.bound "subMod25519"))
          (Amd64.Bignum.subMod25519Compiled.bound "subMod25519") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆
          (fun m' => ∃ rs : List (BitVec 64), rs.length = 4 ∧
            limbsVal rs = (if limbsVal bs ≤ limbsVal as then limbsVal as - limbsVal bs
                           else limbsVal as + Bignum.p25519 - limbsVal bs) ∧
            limbsVal rs < Bignum.p25519 ∧
            (array64 out rs ⋆ array64 pa as ⋆ array64 pb bs) m') ⋆
          region (s.regs.get64 .rsp -
              BitVec.ofNat 64 (Amd64.Bignum.subMod25519Compiled.bound "subMod25519"))
            (Amd64.Bignum.subMod25519Compiled.bound "subMod25519" + 8) ⋆ R))
      ⟨s, Labels.label "subMod25519"⟩ :=
  Amd64.Bignum.subMod25519_x64_correct (hh := hh) k₀ hc hu out pa pb as bs out0 has hbs hout
    ha_lt hb_lt s ra R hout_reg hpa hpb hsp hmem

attribute [local instance] Amd64.Bignum.mul4x4Host in
theorem audit_mul4x4_nv :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧
        (st.data.dmem =⋆
          (fun m' => ∃ rs : List (BitVec 64), rs.length = 8 ∧
            limbsVal rs = limbsVal Amd64.Bignum.nvMulA * limbsVal Amd64.Bignum.nvMulB ∧
            (array64 0x1000#64 rs ⋆ array64 0x1040#64 Amd64.Bignum.nvMulA ⋆
              array64 0x1060#64 Amd64.Bignum.nvMulB) m') ⋆
          region (0x0ff8#64 -
              BitVec.ofNat 64 (Amd64.Bignum.mul4x4Compiled.bound "mul4x4"))
            (Amd64.Bignum.mul4x4Compiled.bound "mul4x4" + 8) ⋆ emp))
      ⟨Amd64.Bignum.mul4x4State0, Labels.label "mul4x4"⟩ :=
  Amd64.Bignum.mul4x4_x64_nonvacuous

attribute [local instance] Amd64.Bignum.addMod25519Host in
theorem audit_add_nv :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧
        (st.data.dmem =⋆
          (fun m' => ∃ rs : List (BitVec 64), rs.length = 4 ∧ limbsVal rs = 19 ∧
            (array64 0x1000#64 rs ⋆ array64 0x1020#64 Amd64.Bignum.nvAddA ⋆
              array64 0x1040#64 Amd64.Bignum.nvAddB) m') ⋆
          region (0x0ff8#64 -
              BitVec.ofNat 64 (Amd64.Bignum.addMod25519Compiled.bound "addMod25519"))
            (Amd64.Bignum.addMod25519Compiled.bound "addMod25519" + 8) ⋆ emp))
      ⟨Amd64.Bignum.addMod25519State0, Labels.label "addMod25519"⟩ :=
  Amd64.Bignum.addMod25519_x64_nonvacuous

attribute [local instance] Amd64.Bignum.subMod25519Host in
theorem audit_sub_nv :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧
        (st.data.dmem =⋆
          (fun m' => ∃ rs : List (BitVec 64), rs.length = 4 ∧
            limbsVal rs = Bignum.p25519 - 20 ∧
            (array64 0x1000#64 rs ⋆ array64 0x1020#64 Amd64.Bignum.nvSubA ⋆
              array64 0x1040#64 Amd64.Bignum.nvSubB) m') ⋆
          region (0x0ff8#64 -
              BitVec.ofNat 64 (Amd64.Bignum.subMod25519Compiled.bound "subMod25519"))
            (Amd64.Bignum.subMod25519Compiled.bound "subMod25519" + 8) ⋆ emp))
      ⟨Amd64.Bignum.subMod25519State0, Labels.label "subMod25519"⟩ :=
  Amd64.Bignum.subMod25519_x64_nonvacuous

/-! ## 3. Union-Find (`find`, `union`, `unionInline`) on x86-64 -/

theorem audit_uf_find [hh : Host] (k₀ : Nat)
    (hc : Amd64.UnionFind.compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (p x : BitVec 64) (n : Nat) (rep : BitVec 64 → BitVec 64) (hx : x.toNat < n)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hp : s.regs.get64 .rdi = p) (hxx : s.regs.get64 .rsi = x)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ UnionFind.uf p n rep ⋆
      (region (s.regs.get64 .rsp -
          BitVec.ofNat 64 (Amd64.UnionFind.compiled.bound "find"))
          (Amd64.UnionFind.compiled.bound "find") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧ st.data.regs.get64 .rax = rep x ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆ UnionFind.uf p n rep ⋆
          region (s.regs.get64 .rsp -
              BitVec.ofNat 64 (Amd64.UnionFind.compiled.bound "find"))
            (Amd64.UnionFind.compiled.bound "find" + 8) ⋆ R))
      ⟨s, Labels.label "find"⟩ :=
  Amd64.UnionFind.find_x64_correct (hh := hh) k₀ hc hu p x n rep hx s ra R hp hxx hsp hmem

theorem audit_uf_union [hh : Host] (k₀ : Nat)
    (hc : Amd64.UnionFind.compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (p x y : BitVec 64) (n : Nat) (rep : BitVec 64 → BitVec 64)
    (hx : x.toNat < n) (hy : y.toNat < n)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hp : s.regs.get64 .rdi = p) (hxx : s.regs.get64 .rsi = x) (hyy : s.regs.get64 .rdx = y)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ UnionFind.uf p n rep ⋆
      (region (s.regs.get64 .rsp -
          BitVec.ofNat 64 (Amd64.UnionFind.compiled.bound "union"))
          (Amd64.UnionFind.compiled.bound "union") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆ UnionFind.uf p n (UnionFind.merge rep x y) ⋆
          region (s.regs.get64 .rsp -
              BitVec.ofNat 64 (Amd64.UnionFind.compiled.bound "union"))
            (Amd64.UnionFind.compiled.bound "union" + 8) ⋆ R))
      ⟨s, Labels.label "union"⟩ :=
  Amd64.UnionFind.union_x64_correct (hh := hh) k₀ hc hu p x y n rep hx hy s ra R
    hp hxx hyy hsp hmem

theorem audit_union_in [hh : Host] (k₀ : Nat)
    (hc : Amd64.UnionFind.compiled.code.IsInfixAt Host.prog k₀) (hu : Host.LabelsUnique)
    (p x y : BitVec 64) (n : Nat) (rep : BitVec 64 → BitVec 64)
    (hx : x.toNat < n) (hy : y.toNat < n)
    (s : MachineData) (ra : Int64) (R : Mem 64 → Prop)
    (hp : s.regs.get64 .rdi = p) (hxx : s.regs.get64 .rsi = x) (hyy : s.regs.get64 .rdx = y)
    (hsp : (s.regs.get64 .rsp + 8#64).toNat % 16 = 0)
    (hmem : s.dmem =⋆ UnionFind.uf p n rep ⋆
      (region (s.regs.get64 .rsp -
          BitVec.ofNat 64 (Amd64.UnionFind.compiled.bound "unionInline"))
          (Amd64.UnionFind.compiled.bound "unionInline") ⋆
        cell64 (s.regs.get64 .rsp) ra.toBitVec) ⋆ R) :
    Eventually (step1 Host.exe)
      (fun st => st.pc = ra ∧
        (∀ r ∈ [Reg64.rbx, .rbp, .r12, .r13, .r14, .r15],
          st.data.regs.get64 r = s.regs.get64 r) ∧
        st.data.regs.get64 .rsp = s.regs.get64 .rsp + 8#64 ∧
        (st.data.dmem =⋆ UnionFind.uf p n (UnionFind.merge rep x y) ⋆
          region (s.regs.get64 .rsp -
              BitVec.ofNat 64 (Amd64.UnionFind.compiled.bound "unionInline"))
            (Amd64.UnionFind.compiled.bound "unionInline" + 8) ⋆ R))
      ⟨s, Labels.label "unionInline"⟩ :=
  Amd64.UnionFind.unionInline_x64_correct (hh := hh) k₀ hc hu p x y n rep hx hy s ra R
    hp hxx hyy hsp hmem

attribute [local instance] Amd64.UnionFind.ufHost in
theorem audit_uf_nv :
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧ st.data.regs.get64 .rax = 3#64 ∧
        (st.data.dmem =⋆ UnionFind.uf 0x1000#64 4 id ⋆
          region (0x0ff8#64 - BitVec.ofNat 64 (Amd64.UnionFind.compiled.bound "find"))
            (Amd64.UnionFind.compiled.bound "find" + 8) ⋆ emp))
      ⟨Amd64.UnionFind.findState0, Labels.label "find"⟩ ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧
        (st.data.dmem =⋆ UnionFind.uf 0x1000#64 4 (UnionFind.merge id 1 2) ⋆
          region (0x0ff8#64 - BitVec.ofNat 64 (Amd64.UnionFind.compiled.bound "union"))
            (Amd64.UnionFind.compiled.bound "union" + 8) ⋆ emp) ∧
        UnionFind.merge id 1 2 1 = UnionFind.merge id 1 2 2 ∧
        UnionFind.merge id 1 2 0 ≠ UnionFind.merge id 1 2 1)
      ⟨Amd64.UnionFind.unionState0, Labels.label "union"⟩ ∧
    Eventually (step1 Host.exe)
      (fun st => st.pc = 0x1234 ∧
        (st.data.dmem =⋆ UnionFind.uf 0x1000#64 4 (UnionFind.merge id 1 2) ⋆
          region (0x0ff8#64 - BitVec.ofNat 64 (Amd64.UnionFind.compiled.bound "unionInline"))
            (Amd64.UnionFind.compiled.bound "unionInline" + 8) ⋆ emp) ∧
        UnionFind.merge id 1 2 1 = UnionFind.merge id 1 2 2 ∧
        UnionFind.merge id 1 2 0 ≠ UnionFind.merge id 1 2 1)
      ⟨Amd64.UnionFind.unionInlineState0, Labels.label "unionInline"⟩ :=
  ⟨Amd64.UnionFind.find_x64_nonvacuous,
   Amd64.UnionFind.union_x64_nonvacuous,
   Amd64.UnionFind.unionInline_x64_nonvacuous⟩

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

end WorkloadsAuditX64
