module

/- `vcgen` with an explicit rewrite set that folds the machine state as it steps. -/
public import Kraken.X64.Registers
public import Std.Tactic.Do.Syntax

public section

theorem BitVec.add_assoc_rev {w : Nat} (a b c : BitVec w) : a + (b + c) = a + b + c :=
  (BitVec.add_assoc a b c).symm

/-- `vcgen` with the register state folded. -/
syntax (name := kvcgen64) "kvcgen64" (" [" ident,* "]")? (" with " vcgenDischarge)? : tactic

macro_rules
  | `(tactic| kvcgen64 $[[$ids,*]]? $[with $d]?) => do
    let lemmas ← (ids.map (·.getElems) |>.getD #[]).mapM fun i =>
      `(Lean.Parser.Tactic.simpLemma| $i:ident)
    `(tactic| vcgen [$lemmas,*] simplifying_assumptions [
        Reg64s.set64_rax,
        Reg64s.set64_rbx,
        Reg64s.set64_rcx,
        Reg64s.set64_rdx,
        Reg64s.set64_rsi,
        Reg64s.set64_rdi,
        Reg64s.set64_rsp,
        Reg64s.set64_rbp,
        Reg64s.set64_r8,
        Reg64s.set64_r9,
        Reg64s.set64_r10,
        Reg64s.set64_r11,
        Reg64s.set64_r12,
        Reg64s.set64_r13,
        Reg64s.set64_r14,
        Reg64s.set64_r15,
        Reg64s.get64_rax,
        Reg64s.get64_rbx,
        Reg64s.get64_rcx,
        Reg64s.get64_rdx,
        Reg64s.get64_rsi,
        Reg64s.get64_rdi,
        Reg64s.get64_rsp,
        Reg64s.get64_rbp,
        Reg64s.get64_r8,
        Reg64s.get64_r9,
        Reg64s.get64_r10,
        Reg64s.get64_r11,
        Reg64s.get64_r12,
        Reg64s.get64_r13,
        Reg64s.get64_r14,
        Reg64s.get64_r15,
        Reg64s.rax_mk,
        Reg64s.rbx_mk,
        Reg64s.rcx_mk,
        Reg64s.rdx_mk,
        Reg64s.rsi_mk,
        Reg64s.rdi_mk,
        Reg64s.rsp_mk,
        Reg64s.rbp_mk,
        Reg64s.r8_mk,
        Reg64s.r9_mk,
        Reg64s.r10_mk,
        Reg64s.r11_mk,
        Reg64s.r12_mk,
        Reg64s.r13_mk,
        Reg64s.r14_mk,
        Reg64s.r15_mk,
        UInt64.toBitVec_ofBitVec,
        MachineData.regs_mk,
        MachineData.zmms_mk,
        MachineData.status_mk,
        MachineData.dmem_mk,
        BitVec.add_assoc_rev,
        Int64.toBitVec_ofNat,
        BitVec.ofNat_eq_ofNat,
        BitVec.setWidth_eq,
        StatusFlags.cf_from_result,
        StatusFlags.from_result.Remaining.cf_mk,
        BitVec.add_zero,
        BitVec.unsigned_eq,
        BitVec.toNat_ofNat,
        Nat.zero_mod,
        Int.add_zero,
        Int.cast_ofNat_Int,
        bne_self_eq_false,
        Bool.toNat_false,
        ite_true,
        ite_false] $[with $d]?)
