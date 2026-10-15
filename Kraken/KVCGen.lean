module

/-
`kvcgen64 [defs] with step` is `vcgen` with the machine state folded as it
goes. A write to a named register or to a part of one rebuilds the register file as a literal,
and a read of a named register from a literal is the field. The projections
of the machine record, the `UInt64` round trip and reassociation present
adjacent literals to `evalGround`, so a chain of ground arithmetic and its
flags fold while `vcgen` steps. The rewrite set is the explicit list below:
nothing else changes what `kvcgen64` rewrites with. Both the state wp and the
separation wp use it.
-/
public import Kraken.X64.Registers
public import Std.Tactic.Do.Syntax
public meta import Lean.Elab.Tactic

public section

/-- Reassociation, so a chain of additions over a symbolic start presents
adjacent literals to `evalGround`. -/
theorem BitVec.add_assoc_rev {w : Nat} (a b c : BitVec w) : a + (b + c) = a + b + c :=
  (BitVec.add_assoc a b c).symm

theorem MachineState.data_mk (d : MachineData) (pc : Int64) : (⟨d, pc⟩ : MachineState).data = d := rfl

open Lean Meta Elab Tactic in
elab "kunfold" ids:(ppSpace colGt ident)* : tactic => do
  for id in ids do
    let [c] ← (try resolveGlobalConst id catch _ => pure []) | continue
    liftMetaTactic1 fun goal => do
      let tgt ← instantiateMVars (← goal.getType)
      let tgt' ← Meta.transform tgt (post := fun e => do
        unless e.isAppOfArity `Fragment.mk 3 && (e.getArg! 1).isConstOf c do return .continue
        let some v ← unfoldDefinition? (e.getArg! 1) | return .continue
        let d := e.getArg! 1
        let h ← mkExpectedTypeHint (← mkEqRefl d) (← mkEq d v)
        let inst ← mkAppOptM `Embeds.cast #[e.getArg! 0, d, v, h, e.getArg! 2]
        return .done (mkAppN e.getAppFn #[e.getArg! 0, v, inst]))
      goal.change tgt'

/-- `vcgen` with the register state folded. -/
syntax (name := kvcgen64) "kvcgen64" (" [" ident,* "]")? (" with " vcgenDischarge)? : tactic

macro_rules
  | `(tactic| kvcgen64 $[[$ids,*]]? $[with $d]?) => do
    let lemmas ← (ids.map (·.getElems) |>.getD #[]).mapM fun i =>
      `(Lean.Parser.Tactic.simpLemma| $i:ident)
    `(tactic| kunfold $(ids.map (·.getElems) |>.getD #[])* ; vcgen [$lemmas,*] simplifying_assumptions [
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
        Reg64s.set_low_W64,
        Reg64s.set_low_W32,
        Reg64s.set_low_W16,
        Reg64s.set_low_W8,
        Reg64s.set_ah,
        Reg64s.set_bh,
        Reg64s.set_ch,
        Reg64s.set_dh,
        Reg64s.get_low_W64,
        Reg64s.get_low_W32,
        Reg64s.get_low_W16,
        Reg64s.get_low_W8,
        BitVec.take_replaceLow_8,
        BitVec.take_replaceLow_16,
        BitVec.take_zeroExtend_32,
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
        MachineState.data_mk,
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
