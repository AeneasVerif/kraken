module

public import LeanQbe.T.Arm64.VllArm64
public import LeanQbe.T.Arm64.VllAsmArm64
public import LeanQbe.T.Vll.RegaInst
public import LeanQbe.T.Arm64.Isa
import LeanQbe.T.Arm64.IselLemmas4
import LeanQbe.T.Arm64.FrameLemmas
import LeanQbe.T.Arm64.Targ
import LeanQbe.T.AbiLemmas
import LeanQbe.T.Logic.MemLemmas
import Kraken.AArch64.WP.Control

/-!
# AArch64 Native-Step Lifting Bridge & Pure-Directive Lemmas (`Arm64.VllFactorArm640`)

Foundation module for `LeanQbe.T.Arm64.VllFactorArm64`, providing a generic, axiom-clean bridge from
Kraken AArch64 `armMach.FallsTo` / `armMach.Run` proofs (from `Arm64/IselLemmas*` and
`Arm64/FrameLemmas`) to `BedrockMach` L1 `vllMach arm64Arch` on `ds.map Instr.native`:

* `dirPure symOk`: decidable PC-independence and label-target check for Kraken `Directive`s.
* `dir_interp_det`: universal determinism and label/PC-independence of `Directive.interp`.
* `armFallsTo_to_vllNative` and `armBranchRun_to_vllNative`: lift straight-line `armMach.FallsTo`
  and conditional-branch `armMach.Run` specifications into `vllMach arm64Arch` via synthetic hosts.
* `dirPure` + length bound lemmas for all `Arm64/Isel.lean` builders (`armOp`, `armStore`,
  `armTestOp`, `armLeaArith`, `armLoadZextIdx`, `armLoadSextZextIdx`, `armStoreZextIdx`,
  `armLeaArithZext`, `armJnzGpr`, `armCmpZeroJcc`, `armTestJcc`), plus `NoVllLab` helpers.

Strictly AArch64 only (zero `Amd64`/`Kraken.X64` imports, zero public `*Lemmas*` imports).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Arm64

open LeanQbe.T
open LeanQbe.T.Vll

/-! ## 1. PC-Independent Pure Directives & Universal `Directive.interp` Determinism -/

/-- True iff `e : ConstExpr` depends on neither `Labels` nor the instruction PC interval `p`. -/
@[expose] def constPure : ConstExpr → Bool
  | .int64 _ => true
  | .add a b | .sub a b => constPure a && constPure b
  | .pg_hi21 a | .lo12 a => constPure a
  | .label _ | .before_current_instruction | .after_current_instruction => false

/-- True iff `e : ExtOrImmReg` has no PC- or label-dependent immediate. -/
@[expose] def extOrImmPure : ExtOrImmReg → Bool
  | .ext _ => true
  | .imm i => constPure i.imm

/-- True iff `a : AddrExpr` has no PC- or label-dependent immediate. -/
@[expose] def addrExprPure (a : AddrExpr) : Bool :=
  match a.off with
  | .reg _ => true
  | .imm i => constPure i.imm

/-- True iff `a : UnscaledAddrExpr` has no PC- or label-dependent immediate. -/
@[expose] def unscaledAddrPure (a : UnscaledAddrExpr) : Bool :=
  constPure a.imm

/-- True iff `a : AddrOrLit` uses only PC/label-independent addresses or literal pools. -/
@[expose] def addrOrLitPure : AddrOrLit → Bool
  | .addr a => addrExprPure a
  | .lit (.pool lp) => constPure lp.expr
  | .lit (.addr _) => false

/-- True iff branch target `t` is the exact label `symOk = some l`. -/
@[expose] def branchTgtPure (symOk : Option Sym) : ConstExpr → Bool
  | .label l => symOk == some l
  | _ => false

/-- True iff `op : Operation w` is PC-independent and only jumps (if at all) to `symOk`. -/
@[expose] def opPure (symOk : Option Sym) {w : RegWidth} : Operation w → Bool
  | .LDR _ src | .LDRSW _ src => addrOrLitPure src
  | .LDRB _ src | .LDRSB _ src | .LDRH _ src | .LDRSH _ src
  | .LDP _ _ src | .LDPSW _ _ src
  | .STR _ src | .STRB _ src | .STRH _ src | .STP _ _ src => addrExprPure src
  | .LDUR _ src | .LDURB _ src | .LDURSB _ src | .LDURH _ src | .LDURSH _ src | .LDURSW _ src
  | .STUR _ src | .STURB _ src | .STURH _ src => unscaledAddrPure src
  | .ADD_e _ _ s2 | .SUB_e _ _ s2 | .ADDS_e _ _ s2 | .SUBS_e _ _ s2 => extOrImmPure s2
  | .AND_i _ _ imm | .ANDS_i _ _ imm | .ORR_i _ _ imm | .EOR_i _ _ imm
  | .MOVZ _ imm _ | .MOVK _ imm _ | .MOVN _ imm _ => constPure imm
  | .ADD_s .. | .SUB_s .. | .ADDS_s .. | .SUBS_s ..
  | .ADC .. | .ADCS .. | .SBC .. | .SBCS ..
  | .MADD .. | .MSUB .. | .SMULH .. | .UMULH .. | .SDIV .. | .UDIV ..
  | .SMADDL .. | .UMADDL .. | .SMSUBL .. | .UMSUBL ..
  | .AND_s .. | .ANDS_s .. | .ORR_s .. | .ORN_s ..
  | .EOR_s .. | .EON_s .. | .BIC_s .. | .BICS_s ..
  | .BFM .. | .SBFM .. | .UBFM ..
  | .CLZ .. | .CLS .. | .RBIT .. | .REV .. | .REV16 .. | .REV32 .. | .EXTR ..
  | .LSLV .. | .LSRV .. | .ASRV .. | .RORV ..
  | .CSEL .. | .CSINC .. | .CSINV .. | .CSNEG ..
  | .CCMP_reg .. | .CCMP_imm .. | .CCMN_reg .. | .CCMN_imm .. | .NOP => true
  | .B t | .B_cond _ t | .CBZ _ t | .CBNZ _ t | .TBZ _ _ t | .TBNZ _ _ t =>
    branchTgtPure symOk t
  | .ADR .. | .ADRP .. | .BL .. | .BLR .. | .BR .. | .RET .. => false

/-- True iff `d : Directive` is an `.instr i` satisfying `opPure symOk i.operation`. -/
@[expose] def dirPure (symOk : Option Sym) : _root_.Directive → Bool
  | .instr i => opPure symOk i.operation
  | .label _ | .byteArray _ | .word _ _ => false

private theorem constPure_interp {e : ConstExpr} (h : constPure e = true)
    (L₁ L₂ : Labels) (p₁ p₂ : Std.Rco Int64) :
    @ConstExpr.interp L₁ e p₁ = @ConstExpr.interp L₂ e p₂ := by
  induction e with
  | int64 _ => rfl
  | label _ | before_current_instruction | after_current_instruction => cases h
  | add a b iha ihb =>
    simp only [constPure, Bool.and_eq_true] at h
    simp only [ConstExpr.interp, iha h.1, ihb h.2]
  | sub a b iha ihb =>
    simp only [constPure, Bool.and_eq_true] at h
    simp only [ConstExpr.interp, iha h.1, ihb h.2]
  | pg_hi21 a iha | lo12 a iha =>
    simp only [constPure] at h
    simp only [ConstExpr.interp, iha h]

private theorem extOrImmPure_interp {w : RegWidth} {e : ExtOrImmReg} (h : extOrImmPure e = true)
    (L₁ L₂ : Labels) (regs : Reg64s) (p₁ p₂ : Std.Rco Int64) :
    @ExtOrImmReg.interp L₁ w e regs p₁ = @ExtOrImmReg.interp L₂ w e regs p₂ := by
  cases e with
  | ext _ => rfl
  | imm i => simp only [ExtOrImmReg.interp, constPure_interp h L₁ L₂ p₁ p₂]

private theorem addrExprPure_eval {a : AddrExpr} (h : addrExprPure a = true)
    (L₁ L₂ : Labels) (s : MachineData) (p₁ p₂ : Std.Rco Int64) :
    @AddrExpr.eval L₁ a s p₁ = @AddrExpr.eval L₂ a s p₂ := by
  cases a with
  | mk base off =>
    cases off with
    | reg _ => rfl
    | imm i => simp only [AddrExpr.eval, constPure_interp h L₁ L₂ p₁ p₂]

private theorem unscaledAddrPure_eval {a : UnscaledAddrExpr} (h : unscaledAddrPure a = true)
    (L₁ L₂ : Labels) (s : MachineData) (p₁ p₂ : Std.Rco Int64) :
    @UnscaledAddrExpr.eval L₁ a s p₁ = @UnscaledAddrExpr.eval L₂ a s p₂ := by
  simp only [UnscaledAddrExpr.eval, constPure_interp h L₁ L₂ p₁ p₂]

private theorem branchTgtPure_eq {symOk : Option Sym} {t : ConstExpr}
    (h : branchTgtPure symOk t = true) : ∃ l, t = .label l ∧ symOk = some l := by
  cases t with
  | label l =>
    simp only [branchTgtPure, beq_iff_eq] at h
    exact ⟨l, rfl, h⟩
  | _ => cases h

private theorem all_checkSP_det {a : AddrExpr} {s : MachineData} {ok₁ : Unit → Effects}
    {P : MachineState → Prop} (h : (a.checkSPAlignment s ok₁).All P) :
    (ok₁ ()).All P ∧
      ∀ ok₂ Q, (a.checkSPAlignment s ok₂).All Q ↔ (ok₂ ()).All Q := by
  dsimp only [AddrExpr.checkSPAlignment] at h ⊢
  split at h
  · split at h
    · cases h
    · rename_i hne; exact ⟨h, fun _ _ => by simp only [hne, Bool.false_eq_true, ↓reduceIte]⟩
  · exact ⟨h, fun _ _ => Iff.rfl⟩

private theorem all_uCheckSP_det {a : UnscaledAddrExpr} {s : MachineData} {ok₁ : Unit → Effects}
    {P : MachineState → Prop} (h : (a.checkSPAlignment s ok₁).All P) :
    (ok₁ ()).All P ∧
      ∀ ok₂ Q, (a.checkSPAlignment s ok₂).All Q ↔ (ok₂ ()).All Q := by
  dsimp only [UnscaledAddrExpr.checkSPAlignment] at h ⊢
  split at h
  · split at h
    · cases h
    · rename_i hne; exact ⟨h, fun _ _ => by simp only [hne, Bool.false_eq_true, ↓reduceIte]⟩
  · exact ⟨h, fun _ _ => Iff.rfl⟩

private theorem all_load_det {s : MachineData} {addr : BitVec 64} {w : MemWidth}
    {ret₁ : w.type → MachineData → Effects} {P : MachineState → Prop}
    (h : (s.load addr w ret₁).All P) :
    ∃ v, (ret₁ v s).All P ∧
      ∀ ret₂ Q, (s.load addr w ret₂).All Q ↔ (ret₂ v s).All Q := by
  dsimp only [MachineData.load, Effects.All] at h ⊢
  cases hl : Mem.loadInt s.dmem addr w.bytes with
  | none => rw [hl] at h; cases h
  | some i => rw [hl] at h; exact ⟨.ofInt _ i, h, fun _ _ => Iff.rfl⟩

private theorem all_store_det {s : MachineData} {addr : BitVec 64} {w : MemWidth} {v : w.type}
    {ret₁ : MachineData → Effects} {P : MachineState → Prop}
    (h : (s.store addr v ret₁).All P) :
    ∃ s', (ret₁ s').All P ∧
      ∀ ret₂ Q, (s.store addr v ret₂).All Q ↔ (ret₂ s').All Q := by
  dsimp only [MachineData.store, Effects.All] at h ⊢
  cases hl : Mem.loadInt s.dmem addr w.bytes with
  | none => rw [hl] at h; cases h
  | some i => rw [hl] at h; exact ⟨{ s with dmem := Mem.storeInt s.dmem addr w.bytes v.toInt }, h,
      fun _ _ => Iff.rfl⟩

private theorem all_addrLoad_det [L₁ : Labels] {a : AddrExpr} (hp : addrExprPure a = true)
    {w : MemWidth} {s : MachineData} {p₁ : Std.Rco Int64}
    {ret₁ : w.type → MachineData → Effects} {P : MachineState → Prop}
    (h : (@AddrExpr.interpLoad L₁ w a s p₁ ret₁).All P) :
    ∃ v s', (ret₁ v s').All P ∧
      ∀ [L₂ : Labels] p₂ ret₂ Q,
        (@AddrExpr.interpLoad L₂ w a s p₂ ret₂).All Q ↔ (ret₂ v s').All Q := by
  obtain ⟨h1, hsp⟩ := all_checkSP_det h
  rcases hev : @AddrExpr.eval L₁ a s p₁ with ⟨addr, s'⟩
  rw [hev] at h1
  obtain ⟨v, hv, hld⟩ := all_load_det h1
  refine ⟨v, s', hv, fun {L₂} p₂ ret₂ Q => ?_⟩
  dsimp only [AddrExpr.interpLoad]
  rw [hsp, ← addrExprPure_eval hp L₁ L₂ s p₁ p₂, hev]
  exact hld ret₂ Q

private theorem all_addrStore_det [L₁ : Labels] {a : AddrExpr} (hp : addrExprPure a = true)
    {w : MemWidth} {s : MachineData} {p₁ : Std.Rco Int64} {v : w.type}
    {ret₁ : MachineData → Effects} {P : MachineState → Prop}
    (h : (@AddrExpr.interpStore L₁ w a s p₁ v ret₁).All P) :
    ∃ s', (ret₁ s').All P ∧
      ∀ [L₂ : Labels] p₂ ret₂ Q,
        (@AddrExpr.interpStore L₂ w a s p₂ v ret₂).All Q ↔ (ret₂ s').All Q := by
  obtain ⟨h1, hsp⟩ := all_checkSP_det h
  rcases hev : @AddrExpr.eval L₁ a s p₁ with ⟨addr, s1⟩
  rw [hev] at h1
  obtain ⟨s', hs', hst⟩ := all_store_det h1
  refine ⟨s', hs', fun {L₂} p₂ ret₂ Q => ?_⟩
  dsimp only [AddrExpr.interpStore]
  rw [hsp, ← addrExprPure_eval hp L₁ L₂ s p₁ p₂, hev]
  exact hst ret₂ Q

private theorem all_uAddrLoad_det [L₁ : Labels] {a : UnscaledAddrExpr}
    (hp : unscaledAddrPure a = true) {w : MemWidth} {s : MachineData} {p₁ : Std.Rco Int64}
    {ret₁ : w.type → MachineData → Effects} {P : MachineState → Prop}
    (h : (@UnscaledAddrExpr.interpLoad L₁ w a s p₁ ret₁).All P) :
    ∃ v, (ret₁ v s).All P ∧
      ∀ [L₂ : Labels] p₂ ret₂ Q,
        (@UnscaledAddrExpr.interpLoad L₂ w a s p₂ ret₂).All Q ↔ (ret₂ v s).All Q := by
  obtain ⟨h1, hsp⟩ := all_uCheckSP_det h
  obtain ⟨v, hv, hld⟩ := all_load_det h1
  refine ⟨v, hv, fun {L₂} p₂ ret₂ Q => ?_⟩
  dsimp only [UnscaledAddrExpr.interpLoad]
  rw [hsp, ← unscaledAddrPure_eval hp L₁ L₂ s p₁ p₂, hld]

private theorem all_uAddrStore_det [L₁ : Labels] {a : UnscaledAddrExpr}
    (hp : unscaledAddrPure a = true) {w : MemWidth} {s : MachineData} {p₁ : Std.Rco Int64}
    {v : w.type} {ret₁ : MachineData → Effects} {P : MachineState → Prop}
    (h : (@UnscaledAddrExpr.interpStore L₁ w a s p₁ v ret₁).All P) :
    ∃ s', (ret₁ s').All P ∧
      ∀ [L₂ : Labels] p₂ ret₂ Q,
        (@UnscaledAddrExpr.interpStore L₂ w a s p₂ v ret₂).All Q ↔ (ret₂ s').All Q := by
  obtain ⟨h1, hsp⟩ := all_uCheckSP_det h
  obtain ⟨s', hs', hst⟩ := all_store_det h1
  refine ⟨s', hs', fun {L₂} p₂ ret₂ Q => ?_⟩
  dsimp only [UnscaledAddrExpr.interpStore]
  rw [hsp, ← unscaledAddrPure_eval hp L₁ L₂ s p₁ p₂, hst]

private theorem all_aolLoad_det [L₁ : Labels] {a : AddrOrLit} (hp : addrOrLitPure a = true)
    {w : MemWidth} {s : MachineData} {p₁ : Std.Rco Int64}
    {ret₁ : w.type → MachineData → Effects} {P : MachineState → Prop}
    (h : (@AddrOrLit.interpLoad L₁ w a s p₁ ret₁).All P) :
    ∃ v s', (ret₁ v s').All P ∧
      ∀ [L₂ : Labels] p₂ ret₂ Q,
        (@AddrOrLit.interpLoad L₂ w a s p₂ ret₂).All Q ↔ (ret₂ v s').All Q := by
  cases a with
  | addr ae => exact all_addrLoad_det hp h
  | lit lit =>
    cases lit with
    | addr _ => cases hp
    | pool lp =>
      refine ⟨BitVec.ofInt w.bits (Int64.toInt (@ConstExpr.interp L₁ lp.expr p₁)), s, h,
        fun {L₂} p₂ _ _ => ?_⟩
      simp only [AddrOrLit.interpLoad, Literal.interpLoad, constPure_interp hp L₁ L₂ p₁ p₂]

private theorem op_interp_det [L₁ : Labels] {symOk : Option Sym} {w : RegWidth} {op : Operation w}
    (hp : opPure symOk op = true) {s : MachineData} {p₁ : Std.Rco Int64}
    {next₁ : MachineData → Effects} {jmp₁ : Int64 → MachineData → Effects}
    {P : MachineState → Prop}
    (h : (@Operation.interp L₁ w op p₁ s next₁ jmp₁).All P) :
    (∃ s', (next₁ s').All P ∧
      ∀ [L₂ : Labels] p₂ next₂ jmp₂ Q,
        (@Operation.interp L₂ w op p₂ s next₂ jmp₂).All Q ↔ (next₂ s').All Q) ∨
    (∃ l, symOk = some l ∧ (jmp₁ (@Labels.label L₁ l) s).All P ∧
      ∀ [L₂ : Labels] p₂ next₂ jmp₂ Q,
        (@Operation.interp L₂ w op p₂ s next₂ jmp₂).All Q ↔
          (jmp₂ (@Labels.label L₂ l) s).All Q) := by
  cases op with
  | LDR dst src | LDRSW dst src =>
    obtain ⟨v, s₁, h1, h2⟩ := all_aolLoad_det hp h
    exact Or.inl ⟨_, h1, fun {L₂} p₂ next₂ _ Q => h2 p₂ _ Q⟩
  | LDRB dst src | LDRSB dst src | LDRH dst src | LDRSH dst src =>
    obtain ⟨v, s₁, h1, h2⟩ := all_addrLoad_det hp h
    exact Or.inl ⟨_, h1, fun {L₂} p₂ next₂ _ Q => h2 p₂ _ Q⟩
  | LDP d1 d2 src =>
    dsimp only [Operation.interp] at h
    obtain ⟨hsp1, hsp⟩ := all_checkSP_det h
    rcases hev : @AddrExpr.eval L₁ src s p₁ with ⟨addr, s1⟩
    rw [hev] at hsp1
    obtain ⟨v1, hv1, hld1⟩ := all_load_det hsp1
    obtain ⟨v2, hv2, hld2⟩ := all_load_det hv1
    refine Or.inl ⟨_, hv2, fun {L₂} p₂ next₂ _ Q => ?_⟩
    dsimp only [Operation.interp]
    rw [hsp, ← addrExprPure_eval hp L₁ L₂ s p₁ p₂, hev]
    dsimp only; rw [hld1, hld2]; rfl
  | LDPSW d1 d2 src =>
    dsimp only [Operation.interp] at h
    obtain ⟨hsp1, hsp⟩ := all_checkSP_det h
    rcases hev : @AddrExpr.eval L₁ src s p₁ with ⟨addr, s1⟩
    rw [hev] at hsp1
    obtain ⟨v1, hv1, hld1⟩ := all_load_det hsp1
    obtain ⟨v2, hv2, hld2⟩ := all_load_det hv1
    refine Or.inl ⟨_, hv2, fun {L₂} p₂ next₂ _ Q => ?_⟩
    dsimp only [Operation.interp]
    rw [hsp, ← addrExprPure_eval hp L₁ L₂ s p₁ p₂, hev]
    dsimp only; rw [hld1, hld2]; rfl
  | LDUR dst src | LDURB dst src | LDURSB dst src | LDURH dst src | LDURSH dst src
  | LDURSW dst src =>
    obtain ⟨v, h1, h2⟩ := all_uAddrLoad_det hp h
    exact Or.inl ⟨_, h1, fun {L₂} p₂ next₂ _ Q => h2 p₂ _ Q⟩
  | STR src dst | STRB src dst | STRH src dst =>
    obtain ⟨s₁, h1, h2⟩ := all_addrStore_det hp h
    exact Or.inl ⟨s₁, h1, fun {L₂} p₂ next₂ _ Q => h2 p₂ _ Q⟩
  | STP s1 s2 dst =>
    dsimp only [Operation.interp] at h
    obtain ⟨hsp1, hsp⟩ := all_checkSP_det h
    rcases hev : @AddrExpr.eval L₁ dst s p₁ with ⟨addr, sa⟩
    rw [hev] at hsp1
    obtain ⟨s', hs', hst1⟩ := all_store_det hsp1
    obtain ⟨s'', hs'', hst2⟩ := all_store_det hs'
    refine Or.inl ⟨s'', hs'', fun {L₂} p₂ next₂ _ Q => ?_⟩
    dsimp only [Operation.interp]
    rw [hsp, ← addrExprPure_eval hp L₁ L₂ s p₁ p₂, hev]
    dsimp only; rw [hst1, hst2]
  | STUR src dst | STURB src dst | STURH src dst =>
    obtain ⟨s₁, h1, h2⟩ := all_uAddrStore_det hp h
    exact Or.inl ⟨s₁, h1, fun {L₂} p₂ next₂ _ Q => h2 p₂ _ Q⟩
  | ADD_e dst s1 s2 | SUB_e dst s1 s2 | ADDS_e dst s1 s2 | SUBS_e dst s1 s2 =>
    refine Or.inl ⟨_, h, fun {L₂} p₂ _ _ _ => ?_⟩
    simp only [Operation.interp, MachineData.setRegOrSp, MachineData.setRegOrZr,
      extOrImmPure_interp hp L₁ L₂ s.regs p₁ p₂]
  | AND_i dst s1 imm | ANDS_i dst s1 imm | ORR_i dst s1 imm | EOR_i dst s1 imm
  | MOVZ dst imm _ | MOVK dst imm _ | MOVN dst imm _ =>
    refine Or.inl ⟨_, h, fun {L₂} p₂ _ _ _ => ?_⟩
    simp only [Operation.interp, MachineData.setRegOrSp, MachineData.setRegOrZr,
      constPure_interp hp L₁ L₂ p₁ p₂]
  | B t =>
    obtain ⟨l, rfl, hsym⟩ := branchTgtPure_eq hp
    exact Or.inr ⟨l, hsym, h, fun {_} _ _ _ _ => Iff.rfl⟩
  | B_cond c t | CBZ _ t | CBNZ _ t | TBZ _ _ t | TBNZ _ _ t =>
    obtain ⟨l, rfl, hsym⟩ := branchTgtPure_eq hp
    dsimp only [Operation.interp] at h ⊢
    split at h
    · rename_i ht
      exact Or.inr ⟨l, hsym, h, fun {_} _ _ _ _ => by simp only [ht, ↓reduceIte]; rfl⟩
    · rename_i hf
      exact Or.inl ⟨s, h, fun {_} _ _ _ _ => by simp only [hf]; rfl⟩
  | ADR _ _ | ADRP _ _ | BL _ | BLR _ | BR _ | RET _ => cases hp
  | _ => exact Or.inl ⟨_, h, fun {_} _ _ _ _ => Iff.rfl⟩

/-- Universal determinism & PC/label-independence of `Directive.interp` on `dirPure symOk`. -/
theorem dir_interp_det [L₁ : Labels] {symOk : Option Sym} {d : _root_.Directive}
    (hp : dirPure symOk d = true) {s : MachineData} {p₁ : Std.Rco Int64}
    {next₁ : MachineData → Effects} {jmp₁ : Int64 → MachineData → Effects}
    {P : MachineState → Prop}
    (h : (@Directive.interp L₁ d s p₁ next₁ jmp₁).All P) :
    (∃ s', (next₁ s').All P ∧
      ∀ [L₂ : Labels] p₂ next₂ jmp₂ Q,
        (@Directive.interp L₂ d s p₂ next₂ jmp₂).All Q ↔ (next₂ s').All Q) ∨
    (∃ l, symOk = some l ∧ (jmp₁ (@Labels.label L₁ l) s).All P ∧
      ∀ [L₂ : Labels] p₂ next₂ jmp₂ Q,
        (@Directive.interp L₂ d s p₂ next₂ jmp₂).All Q ↔ (jmp₂ (@Labels.label L₂ l) s).All Q) := by
  cases d with
  | instr i => exact op_interp_det hp h
  | label _ | byteArray _ | word _ _ => cases hp

/-! ## 2. Synthetic Kraken `Host` & `armMach` → `vllMach arm64Arch` Lifting -/

@[instance_reducible] private def synLayout : _root_.Layout where
  start := 0
  instrSize _ := 1
  instrSize_pos _ := Nat.zero_lt_one

private theorem synLayout_size_dirPure {symOk : Option Sym} {d : _root_.Directive}
    (hp : dirPure symOk d = true) (i : Nat) : synLayout.size d i = 1 := by
  cases d with
  | instr _ => rfl
  | label _ | byteArray _ | word _ _ => cases hp

private theorem synSize_prefix {symOk : Option Sym} {ds rest : List _root_.Directive}
    (hp : ds.all (dirPure symOk) = true) :
    ∀ {k : Nat}, k ≤ ds.length →
      (synLayout.apply (ds ++ rest)).sizeBefore k = k := by
  letI : _root_.Layout := synLayout
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk' : k < ds.length := by omega
    have hget : (ds ++ rest)[k]? = some ds[k] := by
      rw [List.getElem?_append_left hk', List.getElem?_eq_getElem hk']
    have hdPure : dirPure symOk ds[k] = true :=
      List.all_eq_true.mp hp ds[k] (List.getElem_mem hk')
    have hprog : (synLayout.apply (ds ++ rest)).program[k]? =
        some { directive := ds[k], size := synLayout.size ds[k] k } := by
      rw [Layout.apply_getElem?, hget]; rfl
    rw [Kraken.Executable.sizeBefore_succ _ hprog, ih (by omega),
      synLayout_size_dirPure hdPure k]

private theorem synSize_straight {ds : List _root_.Directive}
    (hp : ds.all (dirPure none) = true) :
    (synLayout.apply (ds ++ [.word 1 (.int64 0)])).sizeBefore (ds.length + 1) = ds.length + 1 := by
  letI : _root_.Layout := synLayout
  have hget : (ds ++ [.word 1 (.int64 0)])[ds.length]? = some (.word 1 (.int64 0)) := by
    rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
  have hprog : (synLayout.apply (ds ++ [.word 1 (.int64 0)])).program[ds.length]? =
      some { directive := .word 1 (.int64 0), size := 1 } := by
    rw [Layout.apply_getElem?, hget]; rfl
  rw [Kraken.Executable.sizeBefore_succ _ hprog, synSize_prefix hp (Nat.le_refl _)]

private theorem synSize_branch {ds : List _root_.Directive} {l : Sym}
    (hp : ds.all (dirPure (some l)) = true) :
    let prog := ds ++ [.word 1 (.int64 0), .label l, .word 1 (.int64 0)]
    (synLayout.apply prog).sizeBefore ds.length = ds.length ∧
    (synLayout.apply prog).sizeBefore (ds.length + 1) = ds.length + 1 ∧
    (synLayout.apply prog).sizeBefore (ds.length + 2) = ds.length + 1 ∧
    (synLayout.apply prog).sizeBefore (ds.length + 3) = ds.length + 2 := by
  letI : _root_.Layout := synLayout
  intro prog
  have h0 : (synLayout.apply prog).sizeBefore ds.length = ds.length :=
    synSize_prefix hp (Nat.le_refl _)
  have hg0 : prog[ds.length]? = some (.word 1 (.int64 0)) := by
    dsimp only [prog]; rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
  have hg1 : prog[ds.length + 1]? = some (.label l) := by
    dsimp only [prog]; rw [List.getElem?_append_right (by omega)]
    rw [show ds.length + 1 - ds.length = 1 by omega]; rfl
  have hg2 : prog[ds.length + 2]? = some (.word 1 (.int64 0)) := by
    dsimp only [prog]; rw [List.getElem?_append_right (by omega)]
    rw [show ds.length + 2 - ds.length = 2 by omega]; rfl
  have hp0 : (synLayout.apply prog).program[ds.length]? =
      some { directive := .word 1 (.int64 0), size := 1 } := by
    rw [Layout.apply_getElem?, hg0]; rfl
  have hp1 : (synLayout.apply prog).program[ds.length + 1]? =
      some { directive := .label l, size := 0 } := by
    rw [Layout.apply_getElem?, hg1]; rfl
  have hp2 : (synLayout.apply prog).program[ds.length + 2]? =
      some { directive := .word 1 (.int64 0), size := 1 } := by
    rw [Layout.apply_getElem?, hg2]; rfl
  have h1 : (synLayout.apply prog).sizeBefore (ds.length + 1) = ds.length + 1 := by
    rw [Kraken.Executable.sizeBefore_succ _ hp0, h0]
  have h2 : (synLayout.apply prog).sizeBefore (ds.length + 2) = ds.length + 1 := by
    rw [Kraken.Executable.sizeBefore_succ _ hp1, h1]; exact Nat.add_zero _
  have h3 : (synLayout.apply prog).sizeBefore (ds.length + 3) = ds.length + 2 := by
    rw [Kraken.Executable.sizeBefore_succ _ hp2, h2]; rfl
  exact ⟨h0, h1, h2, h3⟩

@[instance_reducible] private def synStraightHost (ds : List _root_.Directive)
    (hp : ds.all (dirPure none) = true) (hlen : ds.length + 1 < 2 ^ 64) : Host :=
  Host.ofLayout (ds ++ [.word 1 (.int64 0)]) synLayout (by
    simpa [List.length_append, synSize_straight hp] using hlen)

@[instance_reducible] private def synBranchHost (ds : List _root_.Directive) (l : Sym)
    (hp : ds.all (dirPure (some l)) = true) (hlen : ds.length + 2 < 2 ^ 64) : Host :=
  Host.ofLayout (ds ++ [.word 1 (.int64 0), .label l, .word 1 (.int64 0)]) synLayout (by
    have h3 := (synSize_branch hp).2.2.2
    simpa [List.length_append, h3] using hlen)

private theorem vllFrame_of_armFrame {sm sm' : MachineData} {gClob : List Arm64.Reg}
    {fClob : FlagMask} (h : armMach.Frame armCondReads sm sm' gClob [] fClob) :
    (vllMach arm64Arch).Frame arm64Arch.condReads (machDataToVll sm) (machDataToVll sm')
      gClob [] fClob :=
  ⟨h.1, fun v => v.elim, h.2.2⟩

private theorem arm64NativeStep_fall_iff {d : _root_.Directive} {symAddr : Sym → BitVec 64}
    {sm sm' : MachineData}
    (hdet : ∀ [L₂ : Labels] p₂ next₂ jmp₂ Q,
      (@Directive.interp L₂ d sm p₂ next₂ jmp₂).All Q ↔ (next₂ sm').All Q) :
    ∀ out, arm64NativeStep d symAddr (machDataToVll sm) out ↔ out = .fall (machDataToVll sm') := by
  intro out
  cases out with
  | halt _ _ => simp [arm64NativeStep]
  | jump pc' sv' =>
    simp only [arm64NativeStep, vllToMachData_machDataToVll, reduceCtorEq, iff_false]
    intro hall
    have h0 := (hdet (L₂ := labelsOfSymAddr symAddr) ⟨0, 4⟩ _ _ _).mp (hall ⟨0, 4⟩)
    cases h0
  | fall sv' =>
    simp only [arm64NativeStep, vllToMachData_machDataToVll, NativeOutcome.fall.injEq]
    constructor
    · intro hall
      exact ((hdet (L₂ := labelsOfSymAddr symAddr) ⟨0, 4⟩ _ _ _).mp (hall ⟨0, 4⟩)).symm
    · rintro rfl p₂
      exact (hdet (L₂ := labelsOfSymAddr symAddr) p₂ _ _ _).mpr rfl

private theorem arm64NativeStep_jump_iff {d : _root_.Directive} {symAddr : Sym → BitVec 64}
    {l : Sym} {sm : MachineData}
    (hdet : ∀ [L₂ : Labels] p₂ next₂ jmp₂ Q,
      (@Directive.interp L₂ d sm p₂ next₂ jmp₂).All Q ↔ (jmp₂ (@Labels.label L₂ l) sm).All Q) :
    ∀ out, arm64NativeStep d symAddr (machDataToVll sm) out ↔
      out = .jump (symAddr l) (machDataToVll sm) := by
  intro out
  cases out with
  | halt _ _ => simp [arm64NativeStep]
  | fall sv' =>
    simp only [arm64NativeStep, vllToMachData_machDataToVll, reduceCtorEq, iff_false]
    intro hall
    have h0 := (hdet (L₂ := labelsOfSymAddr symAddr) ⟨0, 4⟩ _ _ _).mp (hall ⟨0, 4⟩)
    cases h0
  | jump pc' sv' =>
    simp only [arm64NativeStep, vllToMachData_machDataToVll, NativeOutcome.jump.injEq]
    constructor
    · intro hall
      obtain ⟨h1, h2⟩ := (hdet (L₂ := labelsOfSymAddr symAddr) ⟨0, 4⟩ _ _ _).mp (hall ⟨0, 4⟩)
      have h1' : symAddr l = pc' := by
        simpa only [Int64.toBitVec_ofBitVec] using
          (show (Int64.ofBitVec (symAddr l)).toBitVec = pc' from h1)
      exact ⟨h1'.symm, h2.symm⟩
    · rintro ⟨rfl, rfl⟩ p₂
      refine (hdet (L₂ := labelsOfSymAddr symAddr) p₂ _ _ _).mpr ?_
      exact ⟨Int64.toBitVec_ofBitVec (symAddr l), rfl⟩

/-- Lift any straight-line `armMach.FallsTo` proof (polymorphic over `h : Host`) for a list `ds`
of PC/label-independent directives into `(vllMach arm64Arch).FallsTo` on `ds.map .native`. -/
theorem armFallsTo_to_vllNative {ds : List _root_.Directive}
    (hp : ds.all (dirPure none) = true) (hlen : ds.length + 1 < 2 ^ 64)
    {vh : VllHost arm64Arch} {k : Nat} {gClob : List Arm64.Reg} {fClob : FlagMask}
    {s : MachSt arm64Arch} {Q : MachSt arm64Arch → Prop} {post : Config arm64Arch → Prop}
    (harm : ∀ (h : Host) (postH : MachineState → Prop),
      armMach.FallsTo armCondReads h 0 ds gClob [] fClob (vllToMachData s)
        (fun sm' => Q (machDataToVll sm')) postH) :
    (vllMach arm64Arch).FallsTo arm64Arch.condReads vh k (ds.map .native) gClob [] fClob s Q
      post := by
  intro hc cont
  let h : Host := synStraightHost ds hp hlen
  letI : Host := h
  let postH : MachineState → Prop := fun st =>
    st.pc = Host.addrOf ds.length ∧ Q (machDataToVll st.data) ∧
      armMach.Frame armCondReads (vllToMachData s) st.data gClob [] fClob
  have hinfH : ds.IsInfixAt Host.prog 0 := ⟨[.word 1 (.int64 0)], rfl⟩
  have hev : Eventually (step1 Host.exe) postH ⟨vllToMachData s, Host.addrOf 0⟩ :=
    harm h postH hinfH fun sm' hq hfr => Eventually.done _ ⟨by simp, hq, hfr⟩
  have hlift : ∀ (st : MachineState), Eventually (step1 Host.exe) postH st →
      ∀ (i : Nat), i ≤ ds.length → st.pc = Host.addrOf i →
      (vllMach arm64Arch).Run vh (k + i) (machDataToVll st.data) post := by
    intro st hev'
    induction hev' with
    | done st hpost =>
      intro i hi hpc
      have hsz : Host.exe.sizeBefore i = Host.exe.sizeBefore ds.length :=
        Host.sizeBefore_eq_of_addrOf_eq (hpc.symm.trans hpost.1)
      change (synLayout.apply (ds ++ [.word 1 (.int64 0)])).sizeBefore i =
        (synLayout.apply (ds ++ [.word 1 (.int64 0)])).sizeBefore ds.length at hsz
      rw [synSize_prefix hp hi, synSize_prefix hp (Nat.le_refl _)] at hsz
      subst hsz
      have hfrV := vllFrame_of_armFrame hpost.2.2
      rw [machDataToVll_vllToMachData] at hfrV
      simpa only [List.length_map] using cont (machDataToVll st.data) hpost.2.1 hfrV
    | step st mid_p hstep _ ih =>
      intro i hi hpc
      rcases Nat.eq_or_lt_of_le hi with rfl | hlt
      · exfalso
        have hget : Host.prog[ds.length]? = some (.word 1 (.int64 0)) := by
          show (ds ++ [.word 1 (.int64 0)])[ds.length]? = _
          rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
        have hst' : step1 Host.exe ⟨st.data, Host.addrOf ds.length⟩ mid_p := by
          rcases st with ⟨sd, pc⟩; dsimp only at hpc; subst hpc; exact hstep
        have hall := (Host.step1_iff_interp hget Nat.zero_lt_one).mp hst'
        cases hall
      · have hget : Host.prog[i]? = some ds[i] := by
          show (ds ++ [.word 1 (.int64 0)])[i]? = _
          rw [List.getElem?_append_left hlt, List.getElem?_eq_getElem hlt]
        have hdPure : dirPure none ds[i] = true :=
          List.all_eq_true.mp hp ds[i] (List.getElem_mem hlt)
        have hst' : step1 Host.exe ⟨st.data, Host.addrOf i⟩ mid_p := by
          rcases st with ⟨sd, pc⟩; dsimp only at hpc; subst hpc; exact hstep
        have hpos : Host.layout.size ds[i] i > 0 := by
          rw [show Host.layout.size ds[i] i = 1 from synLayout_size_dirPure hdPure i]
          exact Nat.zero_lt_one
        have hall := (Host.step1_iff_interp hget hpos).mp hst'
        rcases dir_interp_det hdPure hall with ⟨sm', hmid, hdet⟩ | ⟨_, hsome, _, _⟩
        · have hvh_get : vh.prog[k + i]? = some (.native ds[i]) := by
            obtain ⟨rest, hdrop⟩ := hc
            change _ = List.drop k vh.prog at hdrop
            have h1 : (vh.prog.drop k)[i]? = some (.native ds[i]) := by
              rw [← hdrop, List.getElem?_append_left (by simpa using hlt),
                List.getElem?_map, List.getElem?_eq_getElem hlt]; rfl
            rwa [List.getElem?_drop] at h1
          have hiff := arm64NativeStep_fall_iff (symAddr := vh.labelAddr) hdet
          refine vllMach_native_jump (A := arm64Arch) (h := vh) (k := k + i) (d := ds[i])
            (List.isInfixAt_singleton.mpr hvh_get)
            ⟨.fall (machDataToVll sm'), (hiff _).mpr rfl⟩ ?_ ?_ ?_
          · intro sv1 hstep1
            have hEq := (hiff (.fall sv1)).mp hstep1; cases hEq
            have hrun := ih ⟨sm', Host.addrOf (i + 1)⟩ hmid (i + 1) (by omega) rfl
            simpa only [Nat.add_assoc] using hrun
          · intro pc1 sv1 hstep1
            have hEq := (hiff (.jump pc1 sv1)).mp hstep1; cases hEq
          · intro c1 sv1 hstep1
            have hEq := (hiff (.halt c1 sv1)).mp hstep1; cases hEq
        · cases hsome
  have h0 := hlift ⟨vllToMachData s, Host.addrOf 0⟩ hev 0 (Nat.zero_le _) rfl
  simpa only [Nat.add_zero, machDataToVll_vllToMachData] using h0

/-- Lift any conditional-branch `armMach.Run` proof (polymorphic over `h : Host`) for a list `ds`
of directives jumping at most to label `l` into `(vllMach arm64Arch).Run` on `ds.map .native`. -/
theorem armBranchRun_to_vllNative {ds : List _root_.Directive} {l : Sym}
    (hp : ds.all (dirPure (some l)) = true) (hlen : ds.length + 2 < 2 ^ 64)
    {vh : VllHost arm64Arch} {k j : Nat} {fClob : FlagMask} {cond : Bool}
    {s : MachSt arm64Arch} {post : Config arm64Arch → Prop}
    (hc : (ds.map (Instr.native (A := arm64Arch))).IsInfixAt vh.prog k)
    (hl : vh.labelAddr l = vh.addrOf j)
    (harm : ∀ (h : Host) (jt : Nat) (postH : MachineState → Prop),
      ds.IsInfixAt (armMach.prog h) 0 → armMach.labelAddr h l = armMach.addrOf h jt →
      (∀ sm', armMach.Frame armCondReads (vllToMachData s) sm' armScratch [] fClob →
        sm'.dmem = s.mem →
        (cond = true → armMach.Run h jt sm' postH) ∧
        (cond = false → armMach.Run h ds.length sm' postH)) →
      armMach.Run h 0 (vllToMachData s) postH)
    (hcont : ∀ s', (vllMach arm64Arch).Frame arm64Arch.condReads s s' armScratch [] fClob →
      s'.mem = s.mem →
      (cond = true → (vllMach arm64Arch).Run vh j s' post) ∧
      (cond = false → (vllMach arm64Arch).Run vh (k + ds.length) s' post)) :
    (vllMach arm64Arch).Run vh k s post := by
  let h : Host := synBranchHost ds l hp hlen
  letI : Host := h
  have hsz := synSize_branch hp
  have hlabH : armMach.labelAddr h l = armMach.addrOf h (ds.length + 1) := by
    refine Host.label_eq_addrOf ?_ ?_
    · show (ds ++ [.word 1 (.int64 0), .label l, .word 1 (.int64 0)])[ds.length + 1]? = _
      rw [List.getElem?_append_right (by omega), show ds.length + 1 - ds.length = 1 by omega]; rfl
    · intro m hm heq
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hm) with hlt | rfl
      · have hgm : Host.prog[m]? = some ds[m] := by
          show (ds ++ _)[m]? = _
          rw [List.getElem?_append_left hlt, List.getElem?_eq_getElem hlt]
        rw [hgm] at heq
        have hdP := List.all_eq_true.mp hp ds[m] (List.getElem_mem hlt)
        have hEq : ds[m] = .label l := Option.some.inj heq
        rw [hEq] at hdP; cases hdP
      · have hg : Host.prog[ds.length]? = some (.word 1 (.int64 0)) := by
          show (ds ++ _)[ds.length]? = _
          rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
        rw [hg] at heq; cases heq
  let postH : MachineState → Prop := fun st =>
    ((st.pc = Host.addrOf (ds.length + 1) ∧ cond = true) ∨
     (st.pc = Host.addrOf ds.length ∧ cond = false)) ∧
    armMach.Frame armCondReads (vllToMachData s) st.data armScratch [] fClob ∧
    st.data.dmem = s.mem
  have hinfH : ds.IsInfixAt (armMach.prog h) 0 :=
    ⟨[.word 1 (.int64 0), .label l, .word 1 (.int64 0)], rfl⟩
  have hev : Eventually (step1 Host.exe) postH ⟨vllToMachData s, Host.addrOf 0⟩ :=
    harm h (ds.length + 1) postH hinfH hlabH fun sm' hfr hm =>
      ⟨fun ht => Eventually.done _ ⟨Or.inl ⟨rfl, ht⟩, hfr, hm⟩,
       fun hf => Eventually.done _ ⟨Or.inr ⟨rfl, hf⟩, hfr, hm⟩⟩
  have hlift : ∀ (st : MachineState), Eventually (step1 Host.exe) postH st →
      ∀ (i : Nat), i ≤ ds.length + 1 → st.pc = Host.addrOf i →
      if i = ds.length + 1 then (vllMach arm64Arch).Run vh j (machDataToVll st.data) post
      else (vllMach arm64Arch).Run vh (k + i) (machDataToVll st.data) post := by
    intro st hev'
    induction hev' with
    | done st hpost =>
      intro i hi hpc
      have hfrV := vllFrame_of_armFrame hpost.2.1
      rw [machDataToVll_vllToMachData] at hfrV
      rcases hpost.1 with ⟨htpc, hct⟩ | ⟨hfpc, hcf⟩
      · have heqSz := Host.sizeBefore_eq_of_addrOf_eq (hpc.symm.trans htpc)
        change (synLayout.apply (ds ++ _)).sizeBefore i =
          (synLayout.apply (ds ++ _)).sizeBefore (ds.length + 1) at heqSz
        rcases Nat.eq_or_lt_of_le hi with rfl | hlt
        · simp only [↓reduceIte]; exact (hcont (machDataToVll st.data) hfrV hpost.2.2).1 hct
        · rw [synSize_prefix hp (Nat.le_of_lt_succ hlt), hsz.2.1] at heqSz; omega
      · have heqSz := Host.sizeBefore_eq_of_addrOf_eq (hpc.symm.trans hfpc)
        change (synLayout.apply (ds ++ _)).sizeBefore i =
          (synLayout.apply (ds ++ _)).sizeBefore ds.length at heqSz
        rcases Nat.eq_or_lt_of_le hi with rfl | hlt
        · rw [hsz.2.1, hsz.1] at heqSz; omega
        · have hle : i ≤ ds.length := Nat.le_of_lt_succ hlt
          rw [synSize_prefix hp hle, hsz.1] at heqSz; subst heqSz
          simp only [show ds.length ≠ ds.length + 1 by omega, ↓reduceIte]
          exact (hcont (machDataToVll st.data) hfrV hpost.2.2).2 hcf
    | step st mid_p hstep _ ih =>
      intro i hi hpc
      have hst' : step1 Host.exe ⟨st.data, Host.addrOf i⟩ mid_p := by
        rcases st with ⟨sd, pc⟩; dsimp only at hpc; subst hpc; exact hstep
      rcases Nat.eq_or_lt_of_le hi with rfl | hlt1
      · exfalso
        have haddrEq : Host.addrOf (ds.length + 1) = Host.addrOf (ds.length + 2) := by
          simp only [Host.addrOf, Kraken.Executable.addrOf]
          congr 1; congr 1
          exact hsz.2.1.trans hsz.2.2.1.symm
        have hget : Host.prog[ds.length + 2]? = some (.word 1 (.int64 0)) := by
          show (ds ++ _)[ds.length + 2]? = _
          rw [List.getElem?_append_right (by omega), show ds.length + 2 - ds.length = 2 by omega]
          rfl
        rw [haddrEq] at hst'
        cases (Host.step1_iff_interp hget Nat.zero_lt_one).mp hst'
      · rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hlt1) with rfl | hlt
        · exfalso
          have hget : Host.prog[ds.length]? = some (.word 1 (.int64 0)) := by
            show (ds ++ _)[ds.length]? = _
            rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
          cases (Host.step1_iff_interp hget Nat.zero_lt_one).mp hst'
        · simp only [show i ≠ ds.length + 1 by omega, ↓reduceIte]
          have hget : Host.prog[i]? = some ds[i] := by
            show (ds ++ _)[i]? = _
            rw [List.getElem?_append_left hlt, List.getElem?_eq_getElem hlt]
          have hdPure : dirPure (some l) ds[i] = true :=
            List.all_eq_true.mp hp ds[i] (List.getElem_mem hlt)
          have hpos : Host.layout.size ds[i] i > 0 := by
            rw [show Host.layout.size ds[i] i = 1 from synLayout_size_dirPure hdPure i]
            exact Nat.zero_lt_one
          have hall := (Host.step1_iff_interp hget hpos).mp hst'
          have hvh_get : vh.prog[k + i]? = some (.native ds[i]) := by
            obtain ⟨rest, hdrop⟩ := hc
            have h1 : (vh.prog.drop k)[i]? = some (.native ds[i]) := by
              rw [← hdrop, List.getElem?_append_left (by simpa using hlt),
                List.getElem?_map, List.getElem?_eq_getElem hlt]; rfl
            rwa [List.getElem?_drop] at h1
          rcases dir_interp_det hdPure hall with ⟨sm', hmid, hdet⟩ | ⟨l', hsym, hmid, hdet⟩
          · have hiff := arm64NativeStep_fall_iff (symAddr := vh.labelAddr) hdet
            refine vllMach_native_jump (A := arm64Arch) (h := vh) (k := k + i) (d := ds[i])
              (List.isInfixAt_singleton.mpr hvh_get)
              ⟨.fall (machDataToVll sm'), (hiff _).mpr rfl⟩ ?_ ?_ ?_
            · intro sv1 hstep1
              have hEq := (hiff (.fall sv1)).mp hstep1; cases hEq
              have hrun := ih ⟨sm', Host.addrOf (i + 1)⟩ hmid (i + 1) (by omega) rfl
              simp only [show i + 1 ≠ ds.length + 1 by omega, ↓reduceIte] at hrun
              simpa only [Nat.add_assoc] using hrun
            · intro pc1 sv1 hstep1
              have hEq := (hiff (.jump pc1 sv1)).mp hstep1; cases hEq
            · intro c1 sv1 hstep1
              have hEq := (hiff (.halt c1 sv1)).mp hstep1; cases hEq
          · cases hsym
            have hiff := arm64NativeStep_jump_iff (symAddr := vh.labelAddr) hdet
            refine vllMach_native_jump (A := arm64Arch) (h := vh) (k := k + i) (d := ds[i])
              (List.isInfixAt_singleton.mpr hvh_get)
              ⟨.jump (vh.labelAddr l) (machDataToVll st.data), (hiff _).mpr rfl⟩ ?_ ?_ ?_
            · intro sv1 hstep1
              have hEq := (hiff (.fall sv1)).mp hstep1; cases hEq
            · intro pc1 sv1 hstep1
              have hEq := (hiff (.jump pc1 sv1)).mp hstep1; cases hEq
              rw [hl]
              have hrun := ih ⟨st.data, Labels.label l⟩ hmid (ds.length + 1) (Nat.le_refl _) hlabH
              simp only [↓reduceIte] at hrun
              exact hrun
            · intro c1 sv1 hstep1
              have hEq := (hiff (.halt c1 sv1)).mp hstep1; cases hEq
  have h0 := hlift ⟨vllToMachData s, Host.addrOf 0⟩ hev 0 (Nat.zero_le _) rfl
  simp only [show (0 : Nat) ≠ ds.length + 1 by omega, ↓reduceIte, Nat.add_zero,
    machDataToVll_vllToMachData] at h0
  exact h0

/-! ## 3. `dirPure` & Bounded-Length Lemmas for `Arm64/Isel.lean` Builders -/

/-- Check that every `Instr` in `cs` satisfies `opPure symOk i.operation`. -/
@[expose] def insPure (symOk : Option Sym) (cs : List _root_.Instr) : Prop :=
  (emitClean cs).all (dirPure symOk) = true

theorem insPure_nil (symOk : Option Sym) : insPure symOk [] := rfl

theorem insPure_cons {symOk : Option Sym} {i : _root_.Instr} {cs : List _root_.Instr}
    (hi : opPure symOk i.operation = true) (hcs : insPure symOk cs) :
    insPure symOk (i :: cs) := by
  simp only [insPure, emitClean_cons, List.all_cons, dirPure, hi, Bool.true_and]
  exact hcs

theorem insPure_append {symOk : Option Sym} {a b : List _root_.Instr}
    (ha : insPure symOk a) (hb : insPure symOk b) : insPure symOk (a ++ b) := by
  unfold insPure at ha hb ⊢
  simp only [emitClean_append, List.all_append, ha, hb, Bool.and_self]

theorem insPure_one {symOk : Option Sym} {i : _root_.Instr}
    (hi : opPure symOk i.operation = true) : insPure symOk [i] :=
  insPure_cons hi (insPure_nil _)

theorem insPure_map_native_noLab {ds : List _root_.Directive} :
    NoVllLab (ds.map (Instr.native (A := arm64Arch))) := by
  intro l hm
  rcases List.mem_map.mp hm with ⟨_, _, hEq⟩
  cases hEq

private theorem armMovImmI_pure_len (d : XReg) (c : BitVec 64) :
    insPure none (armMovImmI d c) ∧ (armMovImmI d c).length ≤ 2 := by
  unfold armMovImmI
  split; · exact ⟨insPure_one rfl, by simp⟩
  split; · exact ⟨insPure_one rfl, by simp⟩
  split; · exact ⟨insPure_one rfl, by simp⟩
  split; · exact ⟨insPure_one rfl, by simp⟩
  split; · exact ⟨insPure_one rfl, by simp⟩
  split; · exact ⟨insPure_cons rfl (insPure_one rfl), by simp⟩
  split; · exact ⟨insPure_cons rfl (insPure_one rfl), by simp⟩
  exact ⟨insPure_one rfl, by simp⟩

private theorem armMovImmI_pure_le (d : XReg) (c : BitVec 64) {k : Nat} (hk : 2 ≤ k) :
    insPure none (armMovImmI d c) ∧ (armMovImmI d c).length ≤ k :=
  ⟨(armMovImmI_pure_len d c).1, Nat.le_trans (armMovImmI_pure_len d c).2 hk⟩

private theorem armArgInIns_pure_len {n : Nat} {tmp : XReg}
    {pa : PArg Arm64.Reg Empty ArmCond (.bits n)} {cs : List _root_.Instr} {rx : XReg}
    (h : armArgInIns tmp pa = some (cs, rx)) :
    insPure none cs ∧ cs.length ≤ 2 := by
  cases pa with
  | gpr r => cases r with | SP => cases h | reg _ => cases h; exact ⟨insPure_nil _, by simp⟩
  | imm c => cases h; exact armMovImmI_pure_len tmp _
  | vec v => exact v.elim

private theorem armBoolArgInIns_pure_len {tmp : XReg} {pa : PArg Arm64.Reg Empty ArmCond .bool}
    {cs : List _root_.Instr} {rx : XReg} (h : armBoolArgInIns tmp pa = some (cs, rx)) :
    insPure none cs ∧ cs.length ≤ 2 := by
  cases pa with
  | gpr r => cases r with | SP => cases h | reg _ => cases h; exact ⟨insPure_nil _, by simp⟩
  | imm b => cases h; exact armMovImmI_pure_len tmp _
  | flag _ => cases h; exact ⟨insPure_one rfl, by simp⟩
  | vec v => exact v.elim

private theorem armImm12?_pure {n : Nat} {c : BitVec n} {ei : ExtOrImmReg}
    (h : armImm12? c = some ei) : extOrImmPure ei = true := by
  unfold armImm12? at h
  split at h
  · cases h; rfl
  · split at h <;> cases h; rfl

private theorem armAddSubImmI?_pure {n : Nat} {isSub : Bool} {w : RegWidth} {d rx : XReg}
    {c : BitVec n} {i : _root_.Instr} (h : armAddSubImmI? isSub w d rx c = some i) :
    opPure none i.operation = true := by
  unfold armAddSubImmI? at h
  cases h1 : armImm12? c with
  | some ei =>
    rw [h1] at h; cases h
    cases isSub <;> exact armImm12?_pure h1
  | none =>
    rw [h1] at h
    cases h2 : armImm12? (-c) with
    | none => simp [h2] at h
    | some ei =>
      rw [h2] at h; cases h
      cases isSub <;> exact armImm12?_pure h2

private theorem armSetupIdxDispIns_pure_len (zextIdx : Bool) (scale : Nat) (rb ri : XReg)
    (sc : AddrScale) (disp : Int64) :
    let p := armSetupIdxDispIns zextIdx scale rb ri sc disp
    insPure none p.1 ∧ p.1.length ≤ 1 ∧ addrExprPure p.2 = true := by
  unfold armSetupIdxDispIns
  split
  · exact ⟨insPure_nil _, by simp, rfl⟩
  · split
    · exact ⟨insPure_one (by cases zextIdx <;> rfl), by simp, rfl⟩
    · cases h1 : armMemExtendAmount scale sc with
      | none => exact ⟨insPure_nil _, by simp, rfl⟩
      | some amt =>
        cases h2 : armAddSubImmI? false .W64 .X16 rb disp.toBitVec with
        | none => exact ⟨insPure_nil _, by simp, rfl⟩
        | some addIns => exact ⟨insPure_one (armAddSubImmI?_pure h2), by simp, rfl⟩

private theorem armSetupAddrIns_pure_len (scale : Nat) (a : AddrArg Arm64.Reg) :
    let p := armSetupAddrIns scale a
    insPure none p.1 ∧ p.1.length ≤ 3 ∧ addrExprPure p.2 = true := by
  cases a with
  | imm c =>
    dsimp only [armSetupAddrIns]
    have hm := armMovImmI_pure_len .X16 c
    exact ⟨hm.1, by omega, rfl⟩
  | baseDisp base disp =>
    cases base with
    | reg rb =>
      dsimp only [armSetupAddrIns]
      split
      · exact ⟨insPure_nil _, by simp, rfl⟩
      · split
        · exact ⟨insPure_nil _, by simp, rfl⟩
        · have hm := armMovImmI_pure_len .X16 disp.toBitVec
          exact ⟨hm.1, by dsimp only; omega, rfl⟩
    | SP =>
      dsimp only [armSetupAddrIns]
      split
      · exact ⟨insPure_one rfl, by simp, rfl⟩
      · split
        · exact ⟨insPure_one rfl, by simp, rfl⟩
        · have hm := armMovImmI_pure_len .X16 disp.toBitVec
          exact ⟨insPure_append hm.1 (insPure_one rfl), by simp; omega, rfl⟩
  | baseIdxDisp base idx sc disp =>
    cases base with
    | SP => dsimp only [armSetupAddrIns]; exact ⟨insPure_nil _, by simp, rfl⟩
    | reg rb =>
      cases idx with
      | SP => dsimp only [armSetupAddrIns]; exact ⟨insPure_nil _, by simp, rfl⟩
      | reg ri =>
        dsimp only [armSetupAddrIns]
        have hp := armSetupIdxDispIns_pure_len false scale rb ri sc disp
        exact ⟨hp.1, by omega, hp.2.2⟩

private theorem armSetupAddrZextIns_pure_len {scale : Nat} {base idx : Arm64.Reg}
    {sc : AddrScale} {disp : Int64} {cs : List _root_.Instr} {addr : AddrExpr}
    (h : armSetupAddrZextIns scale base idx sc disp = some (cs, addr)) :
    insPure none cs ∧ cs.length ≤ 1 ∧ addrExprPure addr = true := by
  cases base with
  | SP => cases h
  | reg rb =>
    cases idx with
    | SP => cases h
    | reg ri =>
      dsimp only [armSetupAddrZextIns] at h
      split at h
      · rw [Option.some.injEq] at h
        have hp := armSetupIdxDispIns_pure_len true scale rb ri sc disp
        rw [h] at hp; exact hp
      · cases h

private theorem armStoreValInIns_pure_len {t : Ty} {pa : PArg Arm64.Reg Empty ArmCond t}
    {cs : List _root_.Instr} {rx : XRegOrXzr} (h : armStoreValInIns t pa = some (cs, rx)) :
    insPure none cs ∧ cs.length ≤ 2 := by
  cases t with
  | bool =>
    cases pa with
    | gpr r => cases r with
      | reg _ => cases h; exact ⟨insPure_nil _, by simp⟩
      | SP => cases h; exact ⟨insPure_one rfl, by simp⟩
    | imm b => cases b with
      | false => cases h; exact ⟨insPure_nil _, by simp⟩
      | true => cases h; exact armMovImmI_pure_len .X17 1#64
    | flag _ => cases h; exact ⟨insPure_one rfl, by simp⟩
    | vec v => exact v.elim
  | bits n =>
    cases pa with
    | gpr r => cases r with
      | reg _ => cases h; exact ⟨insPure_nil _, by simp⟩
      | SP => cases h; exact ⟨insPure_one rfl, by simp⟩
    | imm c =>
      dsimp only [armStoreValInIns] at h
      split at h
      · cases h; exact ⟨insPure_nil _, by simp⟩
      · cases h; exact armMovImmI_pure_len .X17 (c.setWidth 64)
    | vec v => exact v.elim
  | float _ | pair _ _ => cases h

private theorem armLoadDirI_pure {t : Ty} {d : XReg} {addr : AddrExpr} {i : _root_.Instr}
    (ha : addrExprPure addr = true) (h : armLoadDirI t d addr = some i) :
    opPure none i.operation = true := by
  cases t with
  | bool => cases h; exact ha
  | bits n =>
    dsimp only [armLoadDirI] at h
    split at h <;> cases h <;> exact ha
  | float _ | pair _ _ => cases h

private theorem armLoadSextDirI_pure {m : Nat} {d : XReg} {addr : AddrExpr} {i : _root_.Instr}
    (ha : addrExprPure addr = true) (h : armLoadSextDirI m d addr = some i) :
    opPure none i.operation = true := by
  dsimp only [armLoadSextDirI] at h
  split at h <;> cases h <;> exact ha

private theorem armStoreDirI_pure {t : Ty} {rx : XRegOrXzr} {addr : AddrExpr} {i : _root_.Instr}
    (ha : addrExprPure addr = true) (h : armStoreDirI t rx addr = some i) :
    opPure none i.operation = true := by
  cases t with
  | bool => cases h; exact ha
  | bits n =>
    dsimp only [armStoreDirI] at h
    split at h <;> cases h <;> exact ha
  | float _ | pair _ _ => cases h

theorem armStore_pure_len {t : Ty} {pa : PArg Arm64.Reg Empty ArmCond t}
    {a : AddrArg Arm64.Reg} {ds : List _root_.Directive} {cl : FlagMask}
    (h : armStore t pa a = some (ds, cl)) :
    ds.all (dirPure none) = true ∧ ds.length + 1 < 2 ^ 64 := by
  obtain ⟨ci, hci, rfl⟩ := emitCleanPair_eq_some.mp h
  dsimp only [armStoreIns, bind, Option.bind] at hci
  cases hsc : armMemScale t with
  | none => simp [hsc] at hci
  | some scale =>
    simp only [hsc] at hci; split at hci
    · cases hci
    · cases hv : armStoreValInIns t pa with
      | none => simp [hv] at hci
      | some p1 =>
        rcases p1 with ⟨vs, rx⟩
        simp only [hv] at hci
        cases hd : armStoreDirI t rx (armSetupAddrIns scale a).2 with
        | none => simp [hd] at hci
        | some dir =>
          simp only [hd, Option.some.injEq, Prod.mk.injEq] at hci
          rcases hci with ⟨rfl, rfl⟩
          have hvs := armStoreValInIns_pure_len hv
          have had := armSetupAddrIns_pure_len scale a
          refine ⟨insPure_append (insPure_append hvs.1 had.1)
            (insPure_one (armStoreDirI_pure had.2.2 hd)), ?_⟩
          simp only [emitClean, List.length_map, List.length_append, List.length_singleton]
          omega

theorem armLoadZextIdx_pure_len {t : Ty} {rd base idx : Arm64.Reg} {sc : AddrScale}
    {disp : Int64} {ds : List _root_.Directive} {cl : FlagMask}
    (h : armLoadZextIdx t rd base idx sc disp = some (ds, cl)) :
    ds.all (dirPure none) = true ∧ ds.length + 1 < 2 ^ 64 := by
  obtain ⟨ci, hci, rfl⟩ := emitCleanPair_eq_some.mp h
  dsimp only [armLoadZextIdxIns, bind, Option.bind] at hci
  cases hsc : armMemScale t with
  | none => simp [hsc] at hci
  | some scale =>
    simp only [hsc] at hci
    cases ha : armSetupAddrZextIns scale base idx sc disp with
    | none => simp [ha] at hci
    | some p =>
      rcases p with ⟨setup, addr⟩
      simp only [ha] at hci
      have had := armSetupAddrZextIns_pure_len ha
      cases rd with
      | reg d =>
        dsimp only [armLoadTailIns, bind, Option.bind] at hci
        cases hd : armLoadDirI t d addr with
        | none => simp [hd] at hci
        | some dir =>
          simp only [hd, Option.some.injEq, Prod.mk.injEq] at hci; rcases hci with ⟨rfl, rfl⟩
          refine ⟨insPure_append had.1 (insPure_one (armLoadDirI_pure had.2.2 hd)), ?_⟩
          simp only [emitClean, List.length_map, List.length_append, List.length_singleton]; omega
      | SP =>
        dsimp only [armLoadTailIns, bind, Option.bind] at hci
        cases hd : armLoadDirI t .X16 addr with
        | none => simp [hd] at hci
        | some dir =>
          simp only [hd, Option.some.injEq, Prod.mk.injEq] at hci; rcases hci with ⟨rfl, rfl⟩
          refine ⟨insPure_append had.1
            (insPure_cons (armLoadDirI_pure had.2.2 hd) (insPure_one rfl)), ?_⟩
          simp only [emitClean, List.length_map, List.length_append, List.length_cons,
            List.length_nil]; omega

theorem armLoadSextZextIdx_pure_len {m n : Nat} {rd base idx : Arm64.Reg} {sc : AddrScale}
    {disp : Int64} {ds : List _root_.Directive} {cl : FlagMask}
    (h : armLoadSextZextIdx m n rd base idx sc disp = some (ds, cl)) :
    ds.all (dirPure none) = true ∧ ds.length + 1 < 2 ^ 64 := by
  obtain ⟨ci, hci, rfl⟩ := emitCleanPair_eq_some.mp h
  dsimp only [armLoadSextZextIdxIns, bind, Option.bind] at hci
  split at hci
  · cases hci
  · cases hsc : armMemScale (.bits m) with
    | none => simp [hsc] at hci
    | some scale =>
      simp only [hsc] at hci
      cases ha : armSetupAddrZextIns scale base idx sc disp with
      | none => simp [ha] at hci
      | some p =>
        rcases p with ⟨setup, addr⟩
        simp only [ha] at hci
        have had := armSetupAddrZextIns_pure_len ha
        cases rd with
        | reg d =>
          dsimp only [armLoadSextTailIns, bind, Option.bind] at hci
          cases hd : armLoadSextDirI m d addr with
          | none => simp [hd] at hci
          | some dir =>
            simp only [hd, Option.some.injEq, Prod.mk.injEq] at hci; rcases hci with ⟨rfl, rfl⟩
            refine ⟨insPure_append had.1 (insPure_one (armLoadSextDirI_pure had.2.2 hd)), ?_⟩
            simp only [emitClean, List.length_map, List.length_append, List.length_singleton]; omega
        | SP =>
          dsimp only [armLoadSextTailIns, bind, Option.bind] at hci
          cases hd : armLoadSextDirI m .X16 addr with
          | none => simp [hd] at hci
          | some dir =>
            simp only [hd, Option.some.injEq, Prod.mk.injEq] at hci; rcases hci with ⟨rfl, rfl⟩
            refine ⟨insPure_append had.1
              (insPure_cons (armLoadSextDirI_pure had.2.2 hd) (insPure_one rfl)), ?_⟩
            simp only [emitClean, List.length_map, List.length_append, List.length_cons,
              List.length_nil]; omega

theorem armStoreZextIdx_pure_len {t : Ty} {pa : PArg Arm64.Reg Empty ArmCond t}
    {base idx : Arm64.Reg} {sc : AddrScale} {disp : Int64}
    {ds : List _root_.Directive} {cl : FlagMask}
    (h : armStoreZextIdx t pa base idx sc disp = some (ds, cl)) :
    ds.all (dirPure none) = true ∧ ds.length + 1 < 2 ^ 64 := by
  obtain ⟨ci, hci, rfl⟩ := emitCleanPair_eq_some.mp h
  dsimp only [armStoreZextIdxIns, bind, Option.bind] at hci
  cases hsc : armMemScale t with
  | none => simp [hsc] at hci
  | some scale =>
    simp only [hsc] at hci
    cases ha : armSetupAddrZextIns scale base idx sc disp with
    | none => simp [ha] at hci
    | some p =>
      rcases p with ⟨setup, addr⟩
      simp only [ha] at hci
      cases hv : armStoreValInIns t pa with
      | none => simp [hv] at hci
      | some p2 =>
        rcases p2 with ⟨vs, rx⟩
        simp only [hv] at hci
        cases hd : armStoreDirI t rx addr with
        | none => simp [hd] at hci
        | some dir =>
          simp only [hd, Option.some.injEq, Prod.mk.injEq] at hci; rcases hci with ⟨rfl, rfl⟩
          have had := armSetupAddrZextIns_pure_len ha
          have hvs := armStoreValInIns_pure_len hv
          refine ⟨insPure_append (insPure_append hvs.1 had.1)
            (insPure_one (armStoreDirI_pure had.2.2 hd)), ?_⟩
          simp only [emitClean, List.length_map, List.length_append, List.length_singleton]; omega

theorem armLeaArith_pure_len {w : Nat} {base? : Option Arm64.Reg} {idx : Arm64.Reg}
    {sc : AddrScale} {disp : Int64} {rd : Arm64.Reg} {ds : List _root_.Directive} {cl : FlagMask}
    (h : armLeaArith w base? idx sc disp rd = some (ds, cl)) :
    ds.all (dirPure none) = true ∧ ds.length + 1 < 2 ^ 64 := by
  obtain ⟨ci, hci, rfl⟩ := emitCleanPair_eq_some.mp h
  dsimp only [armLeaArithIns] at hci
  split at hci; · cases hci
  split at hci; · cases hci
  cases rd with | SP => cases hci | reg d =>
  cases idx with | SP => cases hci | reg ri =>
  cases base? with
  | none => cases hci
  | some b =>
    cases b with
    | SP => cases hci
    | reg rb =>
      simp only [bind, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hci
      rcases hci with ⟨rfl, rfl⟩
      exact ⟨insPure_one rfl, by simp [emitClean]⟩

theorem armLeaArithZext_pure_len {base? : Option Arm64.Reg} {idx : Arm64.Reg} {shift : Nat}
    {disp : Int64} {rd : Arm64.Reg} {ds : List _root_.Directive} {cl : FlagMask}
    (h : armLeaArithZext base? idx shift disp rd = some (ds, cl)) :
    ds.all (dirPure none) = true ∧ ds.length + 1 < 2 ^ 64 := by
  obtain ⟨ci, hci, rfl⟩ := emitCleanPair_eq_some.mp h
  cases rd with
  | SP => cases base? <;> simp [armLeaArithZextIns] at hci
  | reg d =>
    cases idx with
    | SP => cases base? <;> simp [armLeaArithZextIns] at hci
    | reg ri =>
      cases base? with
      | some b =>
        cases b with
        | SP => simp [armLeaArithZextIns] at hci
        | reg rb =>
          dsimp only [armLeaArithZextIns, bind, Option.bind] at hci
          cases hamt : armExtendAmount? shift with
          | none => simp [hamt] at hci
          | some amt =>
            simp only [hamt] at hci
            split at hci
            · cases hci; exact ⟨insPure_one rfl, by simp [emitClean]⟩
            · cases hadd : armAddSubImmI? false .W64 d .X16 disp.toBitVec with
              | none => simp [hadd] at hci
              | some addDisp =>
                simp only [hadd, Option.some.injEq, Prod.mk.injEq] at hci
                rcases hci with ⟨rfl, rfl⟩
                exact ⟨insPure_cons rfl (insPure_one (armAddSubImmI?_pure hadd)),
                  by simp [emitClean]⟩
      | none =>
        dsimp only [armLeaArithZextIns, bind, Option.bind] at hci
        split at hci; · cases hci
        split at hci
        · cases hci
          refine ⟨insPure_one (by cases hsh : (shift == 0) <;> rfl), by simp [emitClean]⟩
        · cases hadd : armAddSubImmI? false .W64 d .X16 disp.toBitVec with
          | none => simp [hadd] at hci
          | some addDisp =>
            simp only [hadd, Option.some.injEq, Prod.mk.injEq] at hci
            rcases hci with ⟨rfl, rfl⟩
            exact ⟨insPure_cons (by cases hsh : (shift == 0) <;> rfl)
              (insPure_one (armAddSubImmI?_pure hadd)), by simp [emitClean]⟩

private theorem armTestDirectIns_pure_len {n : Nat}
    {pa pb : PArg Arm64.Reg Empty ArmCond (.bits n)}
    {cs : List _root_.Instr} (h : armTestDirectIns n pa pb = some cs) :
    insPure none cs ∧ cs.length ≤ 5 := by
  dsimp only [armTestDirectIns] at h
  split at h
  · have hri : ∀ (rx : XReg) (cy : BitVec n),
        (let c64 := cy.setWidth 64
         if armIsValidLogicalImm (armWidthOf n) c64 then
           some [armIselInsI (.ANDS_i (xzr (armWidthOf n)) (zr rx (armWidthOf n))
             (.int64 (Int64.ofBitVec c64)))]
         else if cy == ~~~0#n then
           some [armIselInsI (.ANDS_s (xzr (armWidthOf n)) (zr rx (armWidthOf n)) (sh rx))]
         else if cy == 0#n then
           some [armIselInsI (.ANDS_s (xzr (armWidthOf n)) (xzr (armWidthOf n))
             { reg := xzr (armWidthOf n), amount := 0, shift := .LSL })]
         else do
           let (cb, ry) ← armArgInIns .X17 (.imm cy)
           some (cb ++ [armIselInsI
             (.ANDS_s (xzr (armWidthOf n)) (zr rx (armWidthOf n)) (sh ry))])) = some cs →
        insPure none cs ∧ cs.length ≤ 5 := by
      intro rx cy h1; dsimp only at h1
      split at h1; · cases h1; exact ⟨insPure_one rfl, by simp⟩
      split at h1; · cases h1; exact ⟨insPure_one rfl, by simp⟩
      split at h1; · cases h1; exact ⟨insPure_one rfl, by simp⟩
      simp only [armArgInIns, bind, Option.bind_some, Option.some.injEq] at h1; subst h1
      have hm := armMovImmI_pure_len .X17 (cy.setWidth 64)
      exact ⟨insPure_append hm.1 (insPure_one rfl), by simp; omega⟩
    cases pa with
    | vec v => exact v.elim
    | gpr r1 =>
      cases r1 with | SP => cases h | reg rx =>
      cases pb with
      | vec v => exact v.elim
      | gpr r2 =>
        cases r2 with
        | SP => cases h
        | reg ry => cases h; exact ⟨insPure_one rfl, by simp⟩
      | imm cy => exact hri rx cy h
    | imm cx =>
      cases pb with
      | vec v => exact v.elim
      | gpr r2 => cases r2 with | SP => cases h | reg ry => exact hri ry cx h
      | imm cy =>
        simp only [armArgInIns, bind, Option.bind_some, Option.some.injEq] at h; subst h
        have h1 := armMovImmI_pure_len .X16 (cx.setWidth 64)
        have h2 := armMovImmI_pure_len .X17 (cy.setWidth 64)
        exact ⟨insPure_append (insPure_append h1.1 h2.1) (insPure_one rfl), by simp; omega⟩
  · have hri : ∀ (rx : XReg) (cy : BitVec n),
        (let c64 := cy.setWidth 64
         if armIsValidLogicalImm .W32 c64 then
           some [armIselInsI (.ANDS_i (xzr .W32) (zr rx .W32) (.int64 (Int64.ofBitVec c64)))]
         else if cy == 0#n then
           some [armIselInsI (.ANDS_s (xzr .W32) (xzr .W32)
             { reg := xzr .W32, amount := 0, shift := .LSL })]
         else
           some (armMovImmI .X17 c64 ++
             [armIselInsI (.ANDS_s (xzr .W32) (zr rx .W32) (sh .X17))])) = some cs →
        insPure none cs ∧ cs.length ≤ 5 := by
      intro rx cy h1; dsimp only at h1
      split at h1; · cases h1; exact ⟨insPure_one rfl, by simp⟩
      split at h1; · cases h1; exact ⟨insPure_one rfl, by simp⟩
      cases h1; have hm := armMovImmI_pure_len .X17 (cy.setWidth 64)
      exact ⟨insPure_append hm.1 (insPure_one rfl), by simp; omega⟩
    cases pa with
    | vec v => exact v.elim
    | gpr r1 =>
      cases r1 with | SP => cases h | reg rx =>
      cases pb with
      | vec v => exact v.elim
      | gpr r2 => cases r2 with | SP => cases h | reg ry =>
        cases h; exact ⟨insPure_cons rfl (insPure_one rfl), by simp⟩
      | imm cy => exact hri rx cy h
    | imm cx =>
      cases pb with
      | vec v => exact v.elim
      | gpr r2 => cases r2 with | SP => cases h | reg ry => exact hri ry cx h
      | imm cy =>
        cases h
        have h1 := armMovImmI_pure_len .X16 (cx.setWidth 64)
        have h2 := armMovImmI_pure_len .X17 (cy.setWidth 64)
        exact ⟨insPure_append (insPure_append h1.1 h2.1) (insPure_one rfl), by simp; omega⟩

theorem armTestOp_pure_len {n : Nat} {neg : Bool}
    {pa pb : PArg Arm64.Reg Empty ArmCond (.bits n)} {pd : PDst Arm64.Reg Empty ArmCond .bool}
    {ds : List _root_.Directive} {cl : FlagMask} (h : armTestOp n neg pa pb pd = some (ds, cl)) :
    ds.all (dirPure none) = true ∧ ds.length + 1 < 2 ^ 64 := by
  obtain ⟨ci, hci, rfl⟩ := emitCleanPair_eq_some.mp h
  dsimp only [armTestOpIns] at hci
  split at hci; · cases hci
  cases pd with
  | vec v => exact v.elim
  | flag c =>
    dsimp only [bind, Option.bind] at hci
    cases hcw : (c == (if neg then ArmCond.ne else ArmCond.eq))
    · simp only [hcw, Bool.false_eq_true, ↓reduceIte] at hci; cases hci
    · simp only [hcw, ↓reduceIte] at hci
      cases ht : armTestDirectIns n pa pb with
      | none => rw [ht] at hci; cases hci
      | some tst =>
        rw [ht] at hci; cases hci
        have hp := armTestDirectIns_pure_len ht
        exact ⟨hp.1, by simp [emitClean]; omega⟩
  | gpr rd =>
    cases rd with | SP => cases hci | reg d =>
    cases pa with
    | vec v => exact v.elim
    | imm cx =>
      cases pb with
      | vec v => exact v.elim
      | imm cy =>
        cases hci
        have hm := armMovImmI_pure_len d
          (BitVec.ofNat 64 ((if neg then CmpOp.ne else CmpOp.eq).evalBits (cx &&& cy) 0#n).toNat)
        exact ⟨hm.1, by simp only [emitClean, List.length_map]; omega⟩
      | gpr r2 =>
        dsimp only [bind, Option.bind] at hci
        cases ht : armTestDirectIns n (.imm cx) (.gpr r2) with
        | none => rw [ht] at hci; cases hci
        | some tst =>
          rw [ht] at hci; cases hci
          have hp := armTestDirectIns_pure_len ht
          exact ⟨insPure_append hp.1 (insPure_one rfl), by simp [emitClean]; omega⟩
    | gpr r1 =>
      dsimp only [bind, Option.bind] at hci
      cases ht : armTestDirectIns n (.gpr r1) pb with
      | none => rw [ht] at hci; cases hci
      | some tst =>
        rw [ht] at hci; cases hci
        have hp := armTestDirectIns_pure_len ht
        exact ⟨insPure_append hp.1 (insPure_one rfl), by simp [emitClean]; omega⟩

theorem armJnzGprInv_pure_len (r : Arm64.Reg) (inv : Bool) (l : Sym) :
    (armJnzGprInv r inv l).1.all (dirPure (some l)) = true ∧
      (armJnzGprInv r inv l).1.length + 2 < 2 ^ 64 := by
  cases r with
  | reg x =>
    cases inv <;> refine ⟨?_, by simp [armJnzGprInv, emitClean]⟩ <;>
      simp [armJnzGprInv, emitClean, dirPure, opPure, branchTgtPure]
  | SP =>
    cases inv <;> refine ⟨?_, by simp [armJnzGprInv, emitClean]⟩ <;>
      simp [armJnzGprInv, emitClean, dirPure, opPure, branchTgtPure,
        extOrImmPure, constPure]

theorem armJnzGpr_pure_len (r : Arm64.Reg) (l : Sym) :
    (armJnzGpr r l).1.all (dirPure (some l)) = true ∧ (armJnzGpr r l).1.length + 2 < 2 ^ 64 :=
  armJnzGprInv_pure_len r false l

theorem armCmpZeroJcc_pure_len {co : CmpOp} {n : Nat} {r : Arm64.Reg} {l : Sym}
    {ds : List _root_.Directive} {cl : FlagMask}
    (h : armCmpZeroJcc co n r l = some (ds, cl)) :
    ds.all (dirPure (some l)) = true ∧ ds.length + 2 < 2 ^ 64 := by
  obtain ⟨ci, hci, rfl⟩ := emitCleanPair_eq_some.mp h
  dsimp only [armCmpZeroJccIns] at hci
  split at hci; · cases hci
  cases r with | SP => cases hci | reg x =>
  have hcb : ∀ (isNz : Bool),
      insPure (some l) (armCmpZeroCbIns isNz n x l) ∧
        (armCmpZeroCbIns isNz n x l).length ≤ 2 := by
    intro isNz; dsimp only [armCmpZeroCbIns]
    split
    · exact ⟨insPure_one (by cases isNz <;> simp [opPure, branchTgtPure]), by simp⟩
    · exact ⟨insPure_cons rfl (insPure_one (by cases isNz <;> simp [opPure, branchTgtPure])),
        by simp⟩
  cases co <;> dsimp only at hci <;> try (cases hci; done)
  · cases hci; have hc := hcb false; exact ⟨hc.1, by simp [emitClean]; omega⟩
  · cases hci; have hc := hcb true; exact ⟨hc.1, by simp [emitClean]; omega⟩
  · cases hci; have hc := hcb false; exact ⟨hc.1, by simp [emitClean]; omega⟩
  · cases hci; have hc := hcb true; exact ⟨hc.1, by simp [emitClean]; omega⟩
  · cases hci
    exact ⟨insPure_one (by simp [opPure, branchTgtPure]), by simp [emitClean]⟩
  · cases hci
    exact ⟨insPure_one (by simp [opPure, branchTgtPure]), by simp [emitClean]⟩

theorem armTestJcc_pure_len {neg : Bool} {n : Nat} {r : Arm64.Reg} {mask : BitVec n} {l : Sym}
    {ds : List _root_.Directive} {cl : FlagMask}
    (h : armTestJcc neg n r mask l = some (ds, cl)) :
    ds.all (dirPure (some l)) = true ∧ ds.length + 2 < 2 ^ 64 := by
  obtain ⟨ci, hci, rfl⟩ := emitCleanPair_eq_some.mp h
  dsimp only [armTestJccIns] at hci
  split at hci; · cases hci
  cases r with | SP => cases hci | reg x =>
  cases hs : armSingleBit? n mask with
  | none => simp [hs] at hci
  | some k =>
    simp only [hs, Option.some.injEq, Prod.mk.injEq] at hci; rcases hci with ⟨rfl, rfl⟩
    exact ⟨insPure_one (by cases neg <;> simp [opPure, branchTgtPure]), by simp [emitClean]⟩

/-! ### `armOp_pure_len` (covering every branch of `armOp`) -/

private theorem armBoolAndOrIns_pure_len {isOr : Bool}
    {pa pb : PArg Arm64.Reg Empty ArmCond .bool} {d : XReg}
    {cs : List _root_.Instr} {cl : FlagMask} (h : armBoolAndOrIns isOr pa pb d = some (cs, cl)) :
    insPure none cs ∧ cs.length ≤ 5 := by
  have hfg : ∀ c r,
      insPure none (if isOr then
        [armIselInsI (.CSINC (zr d .W32) (zr r .W32) (xzr .W32) (armNegCond c).toKraken)]
      else
        [armIselInsI (.CSEL (zr d .W32) (zr r .W32) (xzr .W32) c.toKraken)]) ∧
      (if isOr then
        [armIselInsI (.CSINC (zr d .W32) (zr r .W32) (xzr .W32) (armNegCond c).toKraken)]
      else
        [armIselInsI (.CSEL (zr d .W32) (zr r .W32) (xzr .W32) c.toKraken)]).length ≤ 1 := by
    intro c r; cases isOr <;> exact ⟨insPure_one rfl, by simp⟩
  have hfb : ∀ {cs' cl'},
      (do
        let (ca, ra) ← armBoolArgInIns .X16 pa
        let (cb, rb) ← armBoolArgInIns .X17 pb
        let insDir := if isOr then armIselInsI (.ORR_s (zr d .W32) (zr ra .W32) (sh rb))
          else armIselInsI (.AND_s (zr d .W32) (zr ra .W32) (sh rb))
        some (ca ++ cb ++ [insDir], maskNone)) = some (cs', cl') →
      insPure none cs' ∧ cs'.length ≤ 5 := by
    intro cs' cl' hf
    simp only [bind, Option.bind_eq_some_iff] at hf
    rcases hf with ⟨⟨ca, ra⟩, ha, ⟨cb, rb⟩, hb, hEq⟩
    cases hEq
    have h1 := armBoolArgInIns_pure_len ha
    have h2 := armBoolArgInIns_pure_len hb
    exact ⟨insPure_append (insPure_append h1.1 h2.1) (insPure_one (by cases isOr <;> rfl)),
      by simp; omega⟩
  cases pa with
  | vec v => exact v.elim
  | gpr r =>
    cases r with
    | SP => dsimp only [armBoolAndOrIns] at h; exact hfb h
    | reg rx =>
      cases pb with
      | vec v => exact v.elim
      | gpr _ => dsimp only [armBoolAndOrIns] at h; exact hfb h
      | flag c =>
        dsimp only [armBoolAndOrIns] at h; cases h
        have h1 := hfg c rx; exact ⟨h1.1, by omega⟩
      | imm b =>
        dsimp only [armBoolAndOrIns] at h
        split at h
        · cases h
          have hm := armMovImmI_pure_len d (BitVec.ofNat 64 isOr.toNat)
          exact ⟨hm.1, by omega⟩
        · cases h; exact ⟨insPure_one rfl, by simp⟩
  | flag c1 =>
    cases pb with
    | vec v => exact v.elim
    | gpr r =>
      cases r with
      | SP => dsimp only [armBoolAndOrIns] at h; exact hfb h
      | reg rx =>
        dsimp only [armBoolAndOrIns] at h; cases h
        have h1 := hfg c1 rx; exact ⟨h1.1, by omega⟩
    | flag c2 =>
      dsimp only [armBoolAndOrIns] at h; cases h
      split
      · exact ⟨insPure_one rfl, by simp⟩
      · split
        · have hm := armMovImmI_pure_len d (BitVec.ofNat 64 isOr.toNat)
          exact ⟨hm.1, by omega⟩
        · have h1 := hfg c2 .X16
          exact ⟨insPure_cons rfl h1.1, by simp; omega⟩
    | imm b =>
      dsimp only [armBoolAndOrIns] at h
      split at h
      · cases h
        have hm := armMovImmI_pure_len d (BitVec.ofNat 64 isOr.toNat)
        exact ⟨hm.1, by omega⟩
      · cases h; exact ⟨insPure_one rfl, by simp⟩
  | imm b =>
    cases pb with
    | vec v => exact v.elim
    | gpr r =>
      cases r with
      | SP => dsimp only [armBoolAndOrIns] at h; exact hfb h
      | reg rx =>
        dsimp only [armBoolAndOrIns] at h
        split at h
        · cases h
          have hm := armMovImmI_pure_len d (BitVec.ofNat 64 isOr.toNat)
          exact ⟨hm.1, by omega⟩
        · cases h; exact ⟨insPure_one rfl, by simp⟩
    | flag c =>
      dsimp only [armBoolAndOrIns] at h
      split at h
      · cases h
        have hm := armMovImmI_pure_len d (BitVec.ofNat 64 isOr.toNat)
        exact ⟨hm.1, by omega⟩
      · cases h; exact ⟨insPure_one rfl, by simp⟩
    | imm _ => dsimp only [armBoolAndOrIns] at h; exact hfb h

private theorem armBoolXorIns_pure_len {pa pb : PArg Arm64.Reg Empty ArmCond .bool} {d : XReg}
    {cs : List _root_.Instr} {cl : FlagMask} (h : armBoolXorIns pa pb d = some (cs, cl)) :
    insPure none cs ∧ cs.length ≤ 5 := by
  have hfb : ∀ {cs' cl'},
      (do
        let (ca, ra) ← armBoolArgInIns .X16 pa
        let (cb, rb) ← armBoolArgInIns .X17 pb
        some (ca ++ cb ++ [armIselInsI (.EOR_s (zr d .W32) (zr ra .W32) (sh rb))], maskNone)) =
        some (cs', cl') →
      insPure none cs' ∧ cs'.length ≤ 5 := by
    intro cs' cl' hf
    simp only [bind, Option.bind_eq_some_iff] at hf
    rcases hf with ⟨⟨ca, ra⟩, ha, ⟨cb, rb⟩, hb, hEq⟩
    cases hEq
    have h1 := armBoolArgInIns_pure_len ha
    have h2 := armBoolArgInIns_pure_len hb
    exact ⟨insPure_append (insPure_append h1.1 h2.1) (insPure_one rfl), by simp; omega⟩
  cases pa with
  | vec v => exact v.elim
  | gpr r =>
    cases r with
    | SP => dsimp only [armBoolXorIns] at h; exact hfb h
    | reg rx =>
      cases pb with
      | vec v => exact v.elim
      | imm b =>
        dsimp only [armBoolXorIns] at h; cases h
        cases b <;> exact ⟨insPure_one rfl, by simp⟩
      | gpr _ | flag _ => dsimp only [armBoolXorIns] at h; exact hfb h
  | flag c =>
    cases pb with
    | vec v => exact v.elim
    | imm b => dsimp only [armBoolXorIns] at h; cases h; exact ⟨insPure_one rfl, by simp⟩
    | gpr _ | flag _ => dsimp only [armBoolXorIns] at h; exact hfb h
  | imm b =>
    cases pb with
    | vec v => exact v.elim
    | gpr r =>
      cases r with
      | SP => dsimp only [armBoolXorIns] at h; exact hfb h
      | reg rx =>
        dsimp only [armBoolXorIns] at h; cases h
        cases b <;> exact ⟨insPure_one rfl, by simp⟩
    | flag c => dsimp only [armBoolXorIns] at h; cases h; exact ⟨insPure_one rfl, by simp⟩
    | imm _ => dsimp only [armBoolXorIns] at h; exact hfb h

private theorem armCopyBitsIns_pure_len {n : Nat} {pa : PArg Arm64.Reg Empty ArmCond (.bits n)}
    {d : XReg} {cs : List _root_.Instr} {cl : FlagMask}
    (h : armCopyBitsIns n pa d = some (cs, cl)) : insPure none cs ∧ cs.length ≤ 2 := by
  cases pa with
  | vec v => exact v.elim
  | gpr r => cases r with | SP => cases h | reg _ => cases h; exact ⟨insPure_one rfl, by simp⟩
  | imm c => cases h; exact armMovImmI_pure_len d _

private theorem armBinOpIns_pure_len {k : ArmBinK} {n : Nat}
    {pa pb : PArg Arm64.Reg Empty ArmCond (.bits n)} {d : XReg}
    {cs : List _root_.Instr} {cl : FlagMask} (h : armBinOpIns k n pa pb d = some (cs, cl)) :
    insPure none cs ∧ cs.length ≤ 5 := by
  have hmul : ∀ (w : RegWidth) (r : XReg) (imm : BitVec n),
      insPure none (armMulRegImmIns w d r imm) ∧ (armMulRegImmIns w d r imm).length ≤ 5 := by
    intro w r imm; unfold armMulRegImmIns
    split; · have hm := armMovImmI_pure_len d 0#64; exact ⟨hm.1, by omega⟩
    split; · exact ⟨insPure_one rfl, by simp⟩
    split
    · split <;> exact ⟨insPure_one rfl, by simp⟩
    · split
      · exact ⟨insPure_one rfl, by simp⟩
      · have hm := armMovImmI_pure_len .X17 (imm.setWidth 64)
        exact ⟨insPure_append hm.1 (insPure_one rfl), by simp; omega⟩
  have hbinDir : ∀ (w : RegWidth) (ra rb : XReg),
      opPure none (armBinDirI k w d ra rb).operation = true := by
    intro w ra rb; cases k <;> rfl
  have hfb : ∀ {cs' cl'},
      (do
        let (ca, ra) ← armArgInIns .X16 pa
        let (cb, rb) ← armArgInIns .X17 pb
        some (ca ++ cb ++ [armBinDirI k (armWidthOf n) d ra rb], maskNone)) = some (cs', cl') →
      insPure none cs' ∧ cs'.length ≤ 5 := by
    intro cs' cl' hf
    simp only [bind, Option.bind_eq_some_iff] at hf
    rcases hf with ⟨⟨ca, ra⟩, ha, ⟨cb, rb⟩, hb, hEq⟩; cases hEq
    have h1 := armArgInIns_pure_len ha; have h2 := armArgInIns_pure_len hb
    exact ⟨insPure_append (insPure_append h1.1 h2.1) (insPure_one (hbinDir _ _ _)), by simp; omega⟩
  dsimp only [armBinOpIns] at h
  split at h; · cases h
  cases pa with
  | vec v => exact v.elim
  | imm ca =>
    cases pb with
    | vec v => exact v.elim
    | imm cb => cases k <;> exact hfb h
    | gpr rb =>
      cases rb with
      | SP => cases k <;> exact hfb h
      | reg rx =>
        cases k
        · dsimp only at h
          cases h1 : armAddSubImmI? false (armWidthOf n) d rx ca with
          | some dir =>
            simp [h1] at h; rcases h with ⟨rfl, rfl⟩
            exact ⟨insPure_one (armAddSubImmI?_pure h1), by simp⟩
          | none =>
            simp only [h1, armArgInIns, bind, Option.bind_some, Option.some.injEq,
              Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩; have hm := armMovImmI_pure_len .X16 (ca.setWidth 64)
            exact ⟨insPure_append hm.1 (insPure_one rfl), by simp; omega⟩
        · dsimp only at h
          split at h; · cases h; exact ⟨insPure_one rfl, by simp⟩
          split at h; · cases h; exact ⟨insPure_one rfl, by simp⟩
          simp only [armArgInIns, bind, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩; have hm := armMovImmI_pure_len .X16 (ca.setWidth 64)
          exact ⟨insPure_append hm.1 (insPure_one rfl), by simp; omega⟩
        · cases h; exact hmul _ rx ca
        · dsimp only [bind, Option.bind] at h; split at h
          · cases h; exact ⟨insPure_one rfl, by simp⟩
          · simp only [armArgInIns, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩; have hm := armMovImmI_pure_len .X16 (ca.setWidth 64)
            exact ⟨insPure_append hm.1 (insPure_one (hbinDir _ _ _)), by simp; omega⟩
        · dsimp only [bind, Option.bind] at h; split at h
          · cases h; exact ⟨insPure_one rfl, by simp⟩
          · simp only [armArgInIns, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩; have hm := armMovImmI_pure_len .X16 (ca.setWidth 64)
            exact ⟨insPure_append hm.1 (insPure_one (hbinDir _ _ _)), by simp; omega⟩
        · dsimp only [bind, Option.bind] at h; split at h
          · cases h; exact ⟨insPure_one rfl, by simp⟩
          · simp only [armArgInIns, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩; have hm := armMovImmI_pure_len .X16 (ca.setWidth 64)
            exact ⟨insPure_append hm.1 (insPure_one (hbinDir _ _ _)), by simp; omega⟩
  | gpr ra =>
    cases ra with
    | SP => cases pb with | vec v => exact v.elim | _ => cases k <;> exact hfb h
    | reg rx =>
      cases pb with
      | vec v => exact v.elim
      | gpr rb => cases rb <;> cases k <;> exact hfb h
      | imm cb =>
        cases k
        · dsimp only at h
          cases h1 : armAddSubImmI? false (armWidthOf n) d rx cb with
          | some dir =>
            simp [h1] at h; rcases h with ⟨rfl, rfl⟩
            exact ⟨insPure_one (armAddSubImmI?_pure h1), by simp⟩
          | none =>
            simp only [h1, armArgInIns, bind, Option.bind_some, Option.some.injEq,
              Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩; have hm := armMovImmI_pure_len .X17 (cb.setWidth 64)
            exact ⟨insPure_append hm.1 (insPure_one rfl), by simp; omega⟩
        · dsimp only at h
          cases h1 : armAddSubImmI? true (armWidthOf n) d rx cb with
          | some dir =>
            simp [h1] at h; rcases h with ⟨rfl, rfl⟩
            exact ⟨insPure_one (armAddSubImmI?_pure h1), by simp⟩
          | none =>
            simp only [h1, armArgInIns, bind, Option.bind_some, Option.some.injEq,
              Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩; have hm := armMovImmI_pure_len .X17 (cb.setWidth 64)
            exact ⟨insPure_append hm.1 (insPure_one rfl), by simp; omega⟩
        · cases h; exact hmul _ rx cb
        · dsimp only [bind, Option.bind] at h; split at h
          · cases h; exact ⟨insPure_one rfl, by simp⟩
          · simp only [armArgInIns, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩; have hm := armMovImmI_pure_len .X17 (cb.setWidth 64)
            exact ⟨insPure_append hm.1 (insPure_one (hbinDir _ _ _)), by simp; omega⟩
        · dsimp only [bind, Option.bind] at h; split at h
          · cases h; exact ⟨insPure_one rfl, by simp⟩
          · simp only [armArgInIns, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩; have hm := armMovImmI_pure_len .X17 (cb.setWidth 64)
            exact ⟨insPure_append hm.1 (insPure_one (hbinDir _ _ _)), by simp; omega⟩
        · dsimp only [bind, Option.bind] at h; split at h
          · cases h; exact ⟨insPure_one rfl, by simp⟩
          · simp only [armArgInIns, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩; have hm := armMovImmI_pure_len .X17 (cb.setWidth 64)
            exact ⟨insPure_append hm.1 (insPure_one (hbinDir _ _ _)), by simp; omega⟩

private theorem armExt32I_pure (s : Bool) (n : Nat) (d r : XReg) :
    opPure none (armExt32I s n d r).operation = true := by
  cases s <;> rfl

private theorem armShiftOpIns_pure_len {k : ArmShiftK} {n : Nat}
    {pa pb : PArg Arm64.Reg Empty ArmCond (.bits n)} {d : XReg}
    {cs : List _root_.Instr} {cl : FlagMask} (h : armShiftOpIns k n pa pb d = some (cs, cl)) :
    insPure none cs ∧ cs.length ≤ 7 := by
  dsimp only [armShiftOpIns, bind, Option.bind] at h
  cases hok : ![8, 16, 32, 64].contains n
  · simp only [hok, Bool.false_eq_true, ↓reduceIte] at h
    cases hw : (n == 32 || n == 64)
    · simp only [hw, Bool.false_eq_true, ↓reduceIte] at h
      cases h1 : armArgInIns .X16 pa with
      | none => simp [h1] at h
      | some p1 =>
        rcases p1 with ⟨ca, ra⟩; simp only [h1] at h
        cases h2 : armArgInIns .X17 pb with
        | none => simp [h2] at h
        | some p2 =>
          rcases p2 with ⟨cb, rb⟩; simp only [h2, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          have ha := armArgInIns_pure_len h1; have hb := armArgInIns_pure_len h2
          cases k <;> refine ⟨insPure_append (insPure_append (insPure_append
              (insPure_append ha.1 hb.1) ?_) (insPure_one rfl)) (insPure_one rfl),
              by simp; omega⟩
          · exact insPure_nil _
          · exact insPure_one rfl
          · exact insPure_one rfl
    · simp only [hw, ↓reduceIte] at h
      cases pa with
      | vec v => exact v.elim
      | gpr r1 =>
        cases r1 with
        | SP => simp [armArgInIns] at h
        | reg ra =>
          cases pb with
          | vec v => exact v.elim
          | imm _ => cases h; exact ⟨insPure_one (by cases k <;> rfl), by simp⟩
          | gpr r2 =>
            cases r2 with | SP => simp [armArgInIns] at h | reg _ =>
            cases h; exact ⟨insPure_one (by cases k <;> rfl), by simp⟩
      | imm ca =>
        dsimp only at h
        rw [show armArgInIns .X16 (.imm ca) = some (armMovImmI .X16 (ca.setWidth 64), .X16)
          from rfl] at h
        cases h2 : armArgInIns .X17 pb with
        | none => simp [h2] at h
        | some p2 =>
          rcases p2 with ⟨cb, rb⟩; simp only [h2, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          have h1 := armMovImmI_pure_len .X16 (ca.setWidth 64)
          have h2' := armArgInIns_pure_len h2
          exact ⟨insPure_append (insPure_append h1.1 h2'.1) (insPure_one (by cases k <;> rfl)),
            by simp; omega⟩
  · simp only [hok, ↓reduceIte] at h; cases h

private theorem armRotOpIns_pure_len {isLeft : Bool} {n : Nat}
    {pa pb : PArg Arm64.Reg Empty ArmCond (.bits n)} {d : XReg}
    {cs : List _root_.Instr} {cl : FlagMask} (h : armRotOpIns isLeft n pa pb d = some (cs, cl)) :
    insPure none cs ∧ cs.length ≤ 10 := by
  dsimp only [armRotOpIns] at h
  cases hok : ![8, 16, 32, 64].contains n
  · simp only [hok, Bool.false_eq_true, ↓reduceIte] at h
    cases hw : (n == 32 || n == 64)
    · simp only [hw, Bool.false_eq_true, ↓reduceIte, bind, Option.bind_eq_some_iff] at h
      rcases h with ⟨⟨ca, ra⟩, h1, ⟨cb, rb⟩, h2, hEq⟩; cases hEq
      have ha := armArgInIns_pure_len h1; have hb := armArgInIns_pure_len h2
      cases isLeft <;>
        refine ⟨insPure_append (insPure_append (insPure_append (insPure_append ha.1 hb.1)
          (insPure_cons rfl (insPure_one rfl)))
          (by first | exact insPure_one rfl | exact insPure_cons rfl (insPure_one rfl)))
          (insPure_one rfl), by simp; omega⟩
    · simp only [hw, ↓reduceIte] at h
      have hfb : ∀ {cs' cl'},
          (do
            let (ca, ra) ← armArgInIns .X16 pa
            let (cb, rb) ← armArgInIns .X17 pb
            if isLeft then
              some (ca ++ cb ++
                [armIselInsI (.SUB_s (zr .X17 (armWidthOf n)) (xzr (armWidthOf n)) (sh rb)),
                 armIselInsI (.RORV (zr d (armWidthOf n)) (zr ra (armWidthOf n))
                   (zr .X17 (armWidthOf n)))], maskNone)
            else
              some (ca ++ cb ++
                [armIselInsI (.RORV (zr d (armWidthOf n)) (zr ra (armWidthOf n))
                  (zr rb (armWidthOf n)))], maskNone)) =
            some (cs', cl') → insPure none cs' ∧ cs'.length ≤ 10 := by
        intro cs' cl' hf; simp only [bind, Option.bind_eq_some_iff] at hf
        rcases hf with ⟨⟨ca, ra⟩, h1, ⟨cb, rb⟩, h2, htail⟩
        have ha := armArgInIns_pure_len h1; have hb := armArgInIns_pure_len h2
        cases isLeft <;>
          simp only [↓reduceIte, Bool.false_eq_true, Option.some.injEq, Prod.mk.injEq] at htail <;>
          rcases htail with ⟨rfl, rfl⟩
        · exact ⟨insPure_append (insPure_append ha.1 hb.1) (insPure_one rfl), by simp; omega⟩
        · exact ⟨insPure_append (insPure_append ha.1 hb.1)
            (insPure_cons rfl (insPure_one rfl)), by simp; omega⟩
      cases pa with
      | vec v => exact v.elim
      | imm _ => dsimp only at h; exact hfb h
      | gpr r1 => cases r1 with
        | SP => dsimp only at h; exact hfb h
        | reg ra => cases pb with
          | vec v => exact v.elim
          | imm _ => cases h; exact ⟨insPure_one rfl, by simp⟩
          | gpr _ => dsimp only at h; exact hfb h
  · simp only [hok, ↓reduceIte] at h; cases h

private theorem armDivRemOpIns_pure_len {k : ArmDivK} {n : Nat}
    {pa pb : PArg Arm64.Reg Empty ArmCond (.bits n)} {d : XReg}
    {cs : List _root_.Instr} {cl : FlagMask} (h : armDivRemOpIns k n pa pb d = some (cs, cl)) :
    insPure none cs ∧ cs.length ≤ 8 := by
  dsimp only [armDivRemOpIns] at h
  cases hok : ![8, 16, 32, 64].contains n
  · simp only [hok, Bool.false_eq_true, ↓reduceIte] at h
    cases hw : (n == 32 || n == 64)
    · simp only [hw, Bool.false_eq_true, ↓reduceIte, bind, Option.bind_eq_some_iff] at h
      rcases h with ⟨⟨ca, ra⟩, h1, ⟨cb, rb⟩, h2, htail⟩
      have ha := armArgInIns_pure_len h1; have hb := armArgInIns_pure_len h2
      cases k <;>
        simp only [↓reduceIte, Bool.false_eq_true, Option.some.injEq, Prod.mk.injEq] at htail <;>
        rcases htail with ⟨rfl, rfl⟩ <;>
        refine ⟨insPure_append (insPure_append (insPure_append ha.1 hb.1)
          (insPure_cons (armExt32I_pure _ _ _ _) (insPure_one (armExt32I_pure _ _ _ _)))) ?_,
          by simp; omega⟩
      all_goals first | exact insPure_one rfl | exact insPure_cons rfl (insPure_one rfl)
    · simp only [hw, ↓reduceIte] at h
      cases pa with
      | vec v => exact v.elim
      | imm _ => cases pb with
        | vec v => exact v.elim
        | imm _ => cases h; exact armMovImmI_pure_le _ _ (by decide)
        | gpr _ =>
          dsimp only at h; simp only [bind, Option.bind_eq_some_iff] at h
          rcases h with ⟨⟨ca, ra⟩, h1, ⟨cb, rb⟩, h2, htail⟩
          have ha := armArgInIns_pure_len h1; have hb := armArgInIns_pure_len h2
          cases k <;>
            simp only [↓reduceIte, Bool.false_eq_true, Option.some.injEq,
              Prod.mk.injEq] at htail <;>
            rcases htail with ⟨rfl, rfl⟩ <;>
            first
            | exact ⟨insPure_append (insPure_append ha.1 hb.1) (insPure_one rfl), by simp; omega⟩
            | exact ⟨insPure_append (insPure_append ha.1 hb.1)
                (insPure_cons rfl (insPure_one rfl)), by simp; omega⟩
      | gpr _ =>
        dsimp only at h; simp only [bind, Option.bind_eq_some_iff] at h
        rcases h with ⟨⟨ca, ra⟩, h1, ⟨cb, rb⟩, h2, htail⟩
        have ha := armArgInIns_pure_len h1; have hb := armArgInIns_pure_len h2
        cases k <;>
          simp only [↓reduceIte, Bool.false_eq_true, Option.some.injEq, Prod.mk.injEq] at htail <;>
          rcases htail with ⟨rfl, rfl⟩ <;>
          first
          | exact ⟨insPure_append (insPure_append ha.1 hb.1) (insPure_one rfl), by simp; omega⟩
          | exact ⟨insPure_append (insPure_append ha.1 hb.1)
              (insPure_cons rfl (insPure_one rfl)), by simp; omega⟩
  · simp only [hok, ↓reduceIte] at h; cases h

private theorem armCmpImmIns?_pure_len {m : Nat} {w : RegWidth} {rx : XReg} {imm : BitVec m}
    {cs : List _root_.Instr} (h : armCmpImmIns? w rx imm = some cs) :
    insPure none cs ∧ cs.length ≤ 1 := by
  unfold armCmpImmIns? at h
  cases h1 : armImm12? imm with
  | some ei => rw [h1] at h; cases h; exact ⟨insPure_one (armImm12?_pure h1), by simp⟩
  | none =>
    rw [h1] at h
    cases h0 : (imm == 0#m) <;> simp only [h0, Bool.false_eq_true, ↓reduceIte] at h
    · cases h2 : armImm12? (-imm) with
      | none => simp [h2] at h
      | some ei => rw [h2] at h; cases h; exact ⟨insPure_one (armImm12?_pure h2), by simp⟩
    · cases h

private theorem armZeroCmpIns?_pure_len {o : CmpOp} {n : Nat} {rx : XReg}
    {dst : PDst Arm64.Reg Empty ArmCond .bool} {cs : List _root_.Instr} {cl : FlagMask}
    (h : armZeroCmpIns? o n rx dst = some (cs, cl)) : insPure none cs ∧ cs.length ≤ 2 := by
  unfold armZeroCmpIns? at h
  cases o with
  | slt =>
    cases dst with
    | vec v => exact v.elim | flag _ => cases h
    | gpr r => cases r with | SP => cases h | reg _ => cases h; exact ⟨insPure_one rfl, by simp⟩
  | sge =>
    cases dst with
    | vec v => exact v.elim | flag _ => cases h
    | gpr r =>
      cases r with | SP => cases h | reg _ =>
      cases hw : (n == 8 || n == 16) <;> simp only [hw, Bool.false_eq_true, ↓reduceIte] at h
      · cases h
      · cases h; exact ⟨insPure_cons rfl (insPure_one rfl), by simp⟩
  | eq =>
    cases hw : (n == 8 || n == 16) <;> simp only [hw, Bool.false_eq_true, ↓reduceIte] at h
    · cases h
    · cases dst with
      | vec v => exact v.elim
      | flag cf =>
        cases hc : (cf == armCmpCond .eq) <;> simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
        · cases h
        · cases h; exact ⟨insPure_one rfl, by simp⟩
      | gpr r =>
        cases r with
        | SP => cases h
        | reg _ => cases h; exact ⟨insPure_cons rfl (insPure_one rfl), by simp⟩
  | ne =>
    cases hw : (n == 8 || n == 16) <;> simp only [hw, Bool.false_eq_true, ↓reduceIte] at h
    · cases h
    · cases dst with
      | vec v => exact v.elim
      | flag cf =>
        cases hc : (cf == armCmpCond .ne) <;> simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
        · cases h
        · cases h; exact ⟨insPure_one rfl, by simp⟩
      | gpr r =>
        cases r with
        | SP => cases h
        | reg _ => cases h; exact ⟨insPure_cons rfl (insPure_one rfl), by simp⟩
  | ule | ugt =>
    cases dst with
    | vec v => exact v.elim | flag _ => cases h
    | gpr r =>
      cases r with | SP => cases h | reg _ =>
      cases hw : (n == 8 || n == 16) <;> simp only [hw, Bool.false_eq_true, ↓reduceIte] at h
      · cases h
      · cases h; exact ⟨insPure_cons rfl (insPure_one rfl), by simp⟩
  | ult | uge | sle | sgt => cases h

private def armCmpFin (dst : PDst Arm64.Reg Empty ArmCond .bool)
    (cmpCode : List _root_.Instr) (cond : ArmCond) : Option (List _root_.Instr × FlagMask) :=
  match dst with
  | .flag c => if c == cond then some (cmpCode, maskNZCV) else none
  | .gpr (.reg d) => some (cmpCode ++ [armCset64I d cond], maskNZCV)
  | .gpr .SP | .vec _ => none

private theorem armCmpFin_pure_len {dst : PDst Arm64.Reg Empty ArmCond .bool}
    {cmpCode : List _root_.Instr} {cond : ArmCond} {cs' : List _root_.Instr} {cl' : FlagMask}
    (hp : insPure none cmpCode) (hl : cmpCode.length ≤ 9)
    (hf : armCmpFin dst cmpCode cond = some (cs', cl')) :
    insPure none cs' ∧ cs'.length ≤ 10 := by
  cases dst with
  | vec v => exact v.elim
  | flag c =>
    dsimp only [armCmpFin] at hf
    cases hc : (c == cond) <;> simp only [hc, Bool.false_eq_true, ↓reduceIte] at hf
    · cases hf
    · cases hf; exact ⟨hp, by omega⟩
  | gpr r => cases r with | SP => cases hf | reg _ =>
    cases hf; exact ⟨insPure_append hp (insPure_one rfl), by simp; omega⟩

private theorem armCmpOpIns_pure_len {o : CmpOp} {n : Nat}
    {pa pb : PArg Arm64.Reg Empty ArmCond (.bits n)} {dst : PDst Arm64.Reg Empty ArmCond .bool}
    {cs : List _root_.Instr} {cl : FlagMask} (h : armCmpOpIns o n pa pb dst = some (cs, cl)) :
    insPure none cs ∧ cs.length ≤ 10 := by
  have hfb : ∀ {cs' cl'},
      (do
        let (ca, ra) ← armArgInIns .X16 pa
        let (cb, rb) ← armArgInIns .X17 pb
        if n == 32 || n == 64 then
          armCmpFin dst (ca ++ cb ++
            [armIselInsI (.SUBS_s (xzr (armWidthOf n)) (zr ra (armWidthOf n)) (sh rb))])
            (armCmpCond o)
        else
          armCmpFin dst (ca ++ cb ++ [armExt32I (armIsSignedCmp o) n .X16 ra,
            armExt32I (armIsSignedCmp o) n .X17 rb,
            armIselInsI (.SUBS_s (xzr .W32) (zr .X16 .W32) (sh .X17))]) (armCmpCond o)) =
        some (cs', cl') →
      insPure none cs' ∧ cs'.length ≤ 10 := by
    intro cs' cl' hf; simp only [bind, Option.bind_eq_some_iff] at hf
    rcases hf with ⟨⟨ca, ra⟩, ha, ⟨cb, rb⟩, hb, htail⟩
    have h1 := armArgInIns_pure_len ha; have h2 := armArgInIns_pure_len hb
    cases hw : (n == 32 || n == 64) <;> simp only [hw, Bool.false_eq_true, ↓reduceIte] at htail
    · exact armCmpFin_pure_len (insPure_append (insPure_append h1.1 h2.1)
        (insPure_cons (armExt32I_pure _ _ _ _)
          (insPure_cons (armExt32I_pure _ _ _ _) (insPure_one rfl)))) (by simp; omega) htail
    · exact armCmpFin_pure_len (insPure_append (insPure_append h1.1 h2.1) (insPure_one rfl))
        (by simp; omega) htail
  have hregImm : ∀ (rx : XReg) (cv : BitVec n) (o' : CmpOp)
      (immArg : PArg Arm64.Reg Empty ArmCond (.bits n)) (isSwap : Bool),
      (if cv == 0#n then
         match armZeroCmpIns? o' n rx dst with
         | some r => some r
         | none =>
           if n == 32 || n == 64 then
             match armCmpImmIns? (armWidthOf n) rx cv with
             | some cmp => armCmpFin dst cmp (armCmpCond o')
             | none => none
           else
             match armCmpImmIns? .W32 .X16 0#32 with
             | some cmp => armCmpFin dst (armExt32I (armIsSignedCmp o) n .X16 rx :: cmp)
                 (armCmpCond o')
             | none => none
       else if n == 32 || n == 64 then
         match armCmpImmIns? (armWidthOf n) rx cv with
         | some cmp => armCmpFin dst cmp (armCmpCond o')
         | none => do
           let (ci, ri) ← armArgInIns (if isSwap then .X16 else .X17) immArg
           let cmp := if isSwap then
               ci ++ [armIselInsI (.SUBS_s (xzr (armWidthOf n)) (zr ri (armWidthOf n)) (sh rx))]
             else
               ci ++ [armIselInsI (.SUBS_s (xzr (armWidthOf n)) (zr rx (armWidthOf n)) (sh ri))]
           armCmpFin dst cmp (armCmpCond o)
       else
         let sgn := armIsSignedCmp o
         let c32 := if sgn then cv.signExtend 32 else cv.setWidth 32
         let ext := armExt32I sgn n .X16 rx
         let cmp := match armCmpImmIns? .W32 .X16 c32 with
           | some cmp => ext :: cmp
           | none => ext :: armMovImmI .X17 (c32.setWidth 64) ++
               [armIselInsI (.SUBS_s (xzr .W32) (zr .X16 .W32) (sh .X17))]
         armCmpFin dst cmp (armCmpCond o')) = some (cs, cl) →
      insPure none cs ∧ cs.length ≤ 10 := by
    intro rx cv o' immArg isSwap hr
    cases h0 : (cv == 0#n) <;> simp only [h0, Bool.false_eq_true, ↓reduceIte] at hr
    · cases hw : (n == 32 || n == 64) <;> simp only [hw, Bool.false_eq_true, ↓reduceIte] at hr
      · cases hc : armCmpImmIns? .W32 .X16
            (if armIsSignedCmp o = true then cv.signExtend 32 else cv.setWidth 32) with
        | some cmp =>
          simp only [hc] at hr; have hcp := armCmpImmIns?_pure_len hc
          exact armCmpFin_pure_len (insPure_cons (armExt32I_pure _ _ _ _) hcp.1)
            (by simp; omega) hr
        | none =>
          simp only [hc] at hr
          have hm := armMovImmI_pure_len .X17
            ((if armIsSignedCmp o = true then cv.signExtend 32 else cv.setWidth 32).setWidth 64)
          exact armCmpFin_pure_len (insPure_append (insPure_cons (armExt32I_pure _ _ _ _) hm.1)
            (insPure_one rfl)) (by simp; omega) hr
      · cases hc : armCmpImmIns? (armWidthOf n) rx cv with
        | some cmp =>
          rw [hc] at hr; have hcp := armCmpImmIns?_pure_len hc
          exact armCmpFin_pure_len hcp.1 (by omega) hr
        | none =>
          rw [hc] at hr; simp only [bind, Option.bind_eq_some_iff] at hr
          rcases hr with ⟨⟨ci, ri⟩, hci, htail⟩; have hip := armArgInIns_pure_len hci
          cases isSwap <;> simp only [↓reduceIte, Bool.false_eq_true] at htail <;>
            exact armCmpFin_pure_len (insPure_append hip.1 (insPure_one rfl))
              (by simp; omega) htail
    · cases hz : armZeroCmpIns? o' n rx dst with
      | some r =>
        rw [hz] at hr; cases hr; have hzp := armZeroCmpIns?_pure_len hz; exact ⟨hzp.1, by omega⟩
      | none =>
        rw [hz] at hr; dsimp only at hr
        cases hw : (n == 32 || n == 64) <;> simp only [hw, Bool.false_eq_true, ↓reduceIte] at hr
        · cases hc : armCmpImmIns? .W32 .X16 0#32 with
          | none => simp [hc] at hr
          | some cmp =>
            rw [hc] at hr; have hcp := armCmpImmIns?_pure_len hc
            exact armCmpFin_pure_len (insPure_cons (armExt32I_pure _ _ _ _) hcp.1)
              (by simp; omega) hr
        · cases hc : armCmpImmIns? (armWidthOf n) rx cv with
          | none => simp [hc] at hr
          | some cmp =>
            rw [hc] at hr; have hcp := armCmpImmIns?_pure_len hc
            exact armCmpFin_pure_len hcp.1 (by omega) hr
  dsimp only [armCmpOpIns] at h
  cases hok : ![8, 16, 32, 64].contains n <;> simp only [hok, Bool.false_eq_true, ↓reduceIte] at h
  · cases pa with
    | vec v => exact v.elim
    | gpr r1 => cases r1 with | SP => dsimp only at h; exact hfb h | reg ra =>
      cases pb with
      | vec v => exact v.elim
      | gpr _ => dsimp only at h; exact hfb h
      | imm cb => dsimp only at h; exact hregImm ra cb o (.imm cb) false h
    | imm ca => cases pb with
      | vec v => exact v.elim
      | imm _ => dsimp only at h; exact hfb h
      | gpr r2 => cases r2 with | SP => dsimp only at h; exact hfb h | reg rb =>
        dsimp only at h; exact hregImm rb ca o.swap (.imm ca) true h
  · cases h

private theorem armSelectCondIns_pure_len {n : Nat} {cond : ArmCond}
    {pa pb : PArg Arm64.Reg Empty ArmCond (.bits n)} {d : XReg} {cs : List _root_.Instr}
    (h : armSelectCondIns n cond pa pb d = some cs) : insPure none cs ∧ cs.length ≤ 5 := by
  have hfb : ∀ {cs'},
      (do
        let (ca, ra) ← armArgInIns .X16 pa
        let (cb, rb) ← armArgInIns .X17 pb
        some (ca ++ cb ++ [armIselInsI (.CSEL (zr d (armWidthOf n))
          (.low (.reg ra) (armWidthOf n)) (.low (.reg rb) (armWidthOf n)) cond.toKraken)])) =
        some cs' →
      insPure none cs' ∧ cs'.length ≤ 5 := by
    intro cs' hf; simp only [bind, Option.bind_eq_some_iff] at hf
    rcases hf with ⟨⟨ca, ra⟩, ha, ⟨cb, rb⟩, hb, hEq⟩; cases hEq
    have h1 := armArgInIns_pure_len ha; have h2 := armArgInIns_pure_len hb
    exact ⟨insPure_append (insPure_append h1.1 h2.1) (insPure_one rfl), by simp; omega⟩
  dsimp only [armSelectCondIns] at h
  cases pa with
  | vec v => exact v.elim
  | imm ca => cases pb with
    | vec v => exact v.elim
    | imm cb =>
      dsimp only at h
      cases h1 : (ca == cb) <;> simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
      · cases h2 : (ca == 1#n && cb == 0#n) <;> simp only [h2, Bool.false_eq_true, ↓reduceIte] at h
        · cases h3 : (ca == 0#n && cb == 1#n) <;>
            simp only [h3, Bool.false_eq_true, ↓reduceIte] at h
          · cases h4 : (ca == ~~~0#n && cb == 0#n) <;>
              simp only [h4, Bool.false_eq_true, ↓reduceIte] at h
            · cases h5 : (ca == 0#n && cb == ~~~0#n) <;>
                simp only [h5, Bool.false_eq_true, ↓reduceIte] at h
              · exact hfb h
              · cases h; exact ⟨insPure_one rfl, by simp⟩
            · cases h; exact ⟨insPure_one rfl, by simp⟩
          · cases h; exact ⟨insPure_one rfl, by simp⟩
        · cases h; exact ⟨insPure_one rfl, by simp⟩
      · cases h; exact armMovImmI_pure_le _ _ (by decide)
    | gpr r2 => cases r2 with | SP => dsimp only at h; exact hfb h | reg rb =>
      dsimp only at h
      cases h1 : (ca == 0#n) <;> simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
      · cases h2 : (ca == 1#n) <;> simp only [h2, Bool.false_eq_true, ↓reduceIte] at h
        · cases h3 : (ca == ~~~0#n) <;> simp only [h3, Bool.false_eq_true, ↓reduceIte] at h
          · simp only [armArgInIns, bind, Option.bind_some, Option.some.injEq] at h; subst h
            have hm := armMovImmI_pure_len .X16 (ca.setWidth 64)
            exact ⟨insPure_append hm.1 (insPure_one rfl), by simp; omega⟩
          · cases h; exact ⟨insPure_one rfl, by simp⟩
        · cases h; exact ⟨insPure_one rfl, by simp⟩
      · cases h; exact ⟨insPure_one rfl, by simp⟩
  | gpr r1 => cases r1 with | SP => dsimp only at h; exact hfb h | reg ra =>
    cases pb with
    | vec v => exact v.elim
    | gpr _ => dsimp only at h; exact hfb h
    | imm cb =>
      dsimp only at h
      cases h1 : (cb == 0#n) <;> simp only [h1, Bool.false_eq_true, ↓reduceIte] at h
      · cases h2 : (cb == 1#n) <;> simp only [h2, Bool.false_eq_true, ↓reduceIte] at h
        · cases h3 : (cb == ~~~0#n) <;> simp only [h3, Bool.false_eq_true, ↓reduceIte] at h
          · simp only [armArgInIns, bind, Option.bind_some, Option.some.injEq] at h; subst h
            have hm := armMovImmI_pure_len .X17 (cb.setWidth 64)
            exact ⟨insPure_append hm.1 (insPure_one rfl), by simp; omega⟩
          · cases h; exact ⟨insPure_one rfl, by simp⟩
        · cases h; exact ⟨insPure_one rfl, by simp⟩
      · cases h; exact ⟨insPure_one rfl, by simp⟩

private theorem armAddcSubb_pure_len (isSub : Bool) {n : Nat}
    {pa pb : PArg Arm64.Reg Empty ArmCond (.bits n)} {cin : PArg Arm64.Reg Empty ArmCond .bool}
    {d : XReg} {cout : PDst Arm64.Reg Empty ArmCond .bool} {vh : VariantHint}
    {cs : List _root_.Instr} {cl : FlagMask}
    (h : (if isSub then armSubbOpIns n pa pb cin d cout vh
          else armAddcOpIns n pa pb cin d cout vh) = some (cs, cl)) :
    insPure none cs ∧ cs.length ≤ 10 := by
  cases isSub <;> (
    dsimp only [armAddcOpIns, armSubbOpIns] at h
    cases hok : (!(n == 32 || n == 64) || vh != VariantHint.default)
    · simp only [hok, Bool.false_eq_true, ↓reduceIte, bind, Option.bind_eq_some_iff] at h
      rcases h with ⟨p, hp, ⟨ca, ra⟩, h1, ⟨cb, rb⟩, h2, m, hm, hEq⟩
      cases hEq
      have hpp : insPure none p ∧ p.length ≤ 1 := by
        cases cout with
        | vec v => exact v.elim
        | flag c =>
          cases c <;> (dsimp only at hp; try (cases hp; done))
          cases hp; exact ⟨insPure_nil _, by simp⟩
        | gpr r => cases r with
          | SP => cases hp
          | reg dc =>
            cases heq : (dc == d) <;> simp only [heq, ↓reduceIte, Bool.false_eq_true] at hp
            · cases hp; exact ⟨insPure_one rfl, by simp⟩
            · cases hp
      have ha := armArgInIns_pure_len h1; have hb := armArgInIns_pure_len h2
      have hmm : insPure none m ∧ m.length ≤ 8 := by
        cases cin with
        | vec v => exact v.elim
        | flag cf =>
          cases cf <;> (dsimp only at hm; try (cases hm; done))
          cases hm
          exact ⟨insPure_append (insPure_append ha.1 hb.1) (insPure_one rfl), by simp; omega⟩
        | imm b =>
          cases b <;> cases hm
          · exact ⟨insPure_append (insPure_append ha.1 hb.1) (insPure_one rfl), by simp; omega⟩
          · exact ⟨insPure_append (insPure_append (insPure_cons rfl ha.1) hb.1)
              (insPure_one rfl), by simp; omega⟩
        | gpr r =>
          cases r with | SP => cases hm | reg rc =>
          cases hm
          exact ⟨insPure_append (insPure_append (insPure_cons rfl (insPure_cons rfl ha.1)) hb.1)
            (insPure_one rfl), by simp; omega⟩
      exact ⟨insPure_append hmm.1 hpp.1, by simp; omega⟩
    · simp only [hok, ↓reduceIte] at h; cases h)

private theorem armMulwOpIns_pure_len {isSigned : Bool} {n : Nat}
    {pa pb : PArg Arm64.Reg Empty ArmCond (.bits n)} {dlo dhi : XReg}
    {cs : List _root_.Instr} {cl : FlagMask}
    (h : armMulwOpIns isSigned n pa pb dlo dhi = some (cs, cl)) :
    insPure none cs ∧ cs.length ≤ 8 := by
  dsimp only [armMulwOpIns, bind, Option.bind] at h
  split at h; · cases h
  cases h1 : armArgInIns .X16 pa with
  | none => simp [h1] at h
  | some p1 =>
    rcases p1 with ⟨ca, ra⟩; simp only [h1] at h
    cases h2 : armArgInIns .X17 pb with
    | none => simp [h2] at h
    | some p2 =>
      rcases p2 with ⟨cb, rb⟩; simp only [h2] at h
      have ha := armArgInIns_pure_len h1; have hb := armArgInIns_pure_len h2
      split at h
      · cases h
        exact ⟨insPure_append (insPure_append ha.1 hb.1)
          (insPure_cons (by cases isSigned <;> rfl) (insPure_one rfl)), by simp; omega⟩
      · split at h
        · cases h
          exact ⟨insPure_append (insPure_append ha.1 hb.1)
            (insPure_cons (by cases isSigned <;> rfl) (insPure_one rfl)), by simp; omega⟩
        · split at h
          · cases h
            exact ⟨insPure_append (insPure_append ha.1 hb.1)
              (insPure_cons rfl (insPure_one (by cases isSigned <;> rfl))), by simp; omega⟩
          · cases h
            exact ⟨insPure_append (insPure_append ha.1 hb.1)
              (insPure_cons (by cases isSigned <;> rfl) (insPure_cons rfl (insPure_one rfl))),
              by simp; omega⟩

private theorem armFunnelOpIns_pure_len {isLeft : Bool} {n : Nat}
    {pa pb pc : PArg Arm64.Reg Empty ArmCond (.bits n)} {d : XReg}
    {cs : List _root_.Instr} {cl : FlagMask}
    (h : armFunnelOpIns isLeft n pa pb pc d = some (cs, cl)) :
    insPure none cs ∧ cs.length ≤ 12 := by
  dsimp only [armFunnelOpIns, bind, Option.bind] at h
  split at h; · cases h
  cases h1 : armArgInIns .X16 pa with
  | none => simp [h1] at h
  | some p1 =>
    rcases p1 with ⟨ca, ra⟩; simp only [h1] at h
    cases h2 : armArgInIns .X17 pb with
    | none => simp [h2] at h
    | some p2 =>
      rcases p2 with ⟨cb, rb⟩; simp only [h2] at h
      have ha := armArgInIns_pure_len h1; have hb := armArgInIns_pure_len h2
      cases pc with
      | vec v => exact v.elim
      | imm cc =>
        cases isLeft
        · cases h
          exact ⟨insPure_append (insPure_append ha.1 hb.1) (insPure_one rfl), by simp; omega⟩
        · dsimp only at h
          cases h0 : (cc.toNat % n == 0) <;>
            simp only [h0, ↓reduceIte, Bool.false_eq_true] at h <;> cases h
          · exact ⟨insPure_append (insPure_append ha.1 hb.1) (insPure_one rfl), by simp; omega⟩
          · exact ⟨insPure_append ha.1 (insPure_one rfl), by simp; omega⟩
      | gpr r =>
        cases r with | SP => cases h | reg rc =>
        cases h
        cases pa with
        | vec v => exact v.elim
        | _ =>
          cases pb with
          | vec v => exact v.elim
          | _ =>
            refine ⟨insPure_append (insPure_append ha.1 hb.1) ?_, ?_⟩
            · cases isLeft <;>
                repeat (first | exact insPure_nil _ | apply insPure_cons rfl)
            · cases isLeft <;> simp <;> omega

/-- Every `armOp` output consists solely of PC/label-independent instructions and has
length < 2^64. -/
theorem armOp_pure_len {sig rs : List Ty} {code : OpCode sig rs}
    {pas : Tup (PArg Arm64.Reg Empty ArmCond) sig} {dsts : Tup (PDst Arm64.Reg Empty ArmCond) rs}
    {vh : VariantHint} {ds : List _root_.Directive} {cl : FlagMask}
    (h : armOp code pas dsts vh = some (ds, cl)) :
    ds.all (dirPure none) = true ∧ ds.length + 1 < 2 ^ 64 := by
  obtain ⟨ci, hci, rfl⟩ := emitCleanPair_eq_some.mp h
  suffices hs : insPure none ci ∧ ci.length ≤ 16 by
    exact ⟨hs.1, by simp only [emitClean, List.length_map]; omega⟩
  cases code with
  | copy t =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t with
    | bool =>
      cases pd with | vec v => exact v.elim | flag _ => cases hci | gpr rd =>
      cases rd with | SP => cases hci | reg d =>
      dsimp only [armOpIns, armBoolOpIns] at hci
      cases pa with
      | vec v => exact v.elim
      | gpr r =>
        cases r with | SP => cases hci | reg _ => cases hci; exact ⟨insPure_one rfl, by simp⟩
      | imm _ => cases hci; exact armMovImmI_pure_le _ _ (by decide)
      | flag _ => cases hci; exact ⟨insPure_one rfl, by simp⟩
    | bits n =>
      cases pd with | vec v => exact v.elim | gpr rd =>
      cases rd with | SP => cases hci | reg d =>
      dsimp only [armOpIns] at hci; split at hci
      · have hp := armCopyBitsIns_pure_len hci; exact ⟨hp.1, by omega⟩
      · cases hci
    | float _ | pair _ _ => cases hci
  | bitcast t u _ =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t with | bool | float _ | pair _ _ => cases hci | bits m =>
    cases u with | bool | float _ | pair _ _ => cases hci | bits n =>
    cases pd with | vec v => exact v.elim | gpr rd =>
    cases rd with | SP => cases hci | reg d =>
    dsimp only [armOpIns] at hci; split at hci
    · have hp := armCopyBitsIns_pure_len hci; exact ⟨hp.1, by omega⟩
    · cases hci
  | and t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t with
    | bool =>
      cases pd with | vec v => exact v.elim | flag _ => cases hci | gpr rd =>
      cases rd with | SP => cases hci | reg d =>
      dsimp only [armOpIns, armBoolOpIns] at hci
      have hp := armBoolAndOrIns_pure_len hci; exact ⟨hp.1, by omega⟩
    | bits n =>
      cases pd with | vec v => exact v.elim | gpr rd =>
      cases rd with | SP => cases hci | reg d =>
      dsimp only [armOpIns] at hci
      have hp := armBinOpIns_pure_len hci; exact ⟨hp.1, by omega⟩
    | float _ | pair _ _ => cases hci
  | or t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t with
    | bool =>
      cases pd with | vec v => exact v.elim | flag _ => cases hci | gpr rd =>
      cases rd with | SP => cases hci | reg d =>
      dsimp only [armOpIns, armBoolOpIns] at hci
      have hp := armBoolAndOrIns_pure_len hci; exact ⟨hp.1, by omega⟩
    | bits n =>
      cases pd with | vec v => exact v.elim | gpr rd =>
      cases rd with | SP => cases hci | reg d =>
      dsimp only [armOpIns] at hci
      have hp := armBinOpIns_pure_len hci; exact ⟨hp.1, by omega⟩
    | float _ | pair _ _ => cases hci
  | xor t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t with
    | bool =>
      cases pd with | vec v => exact v.elim | flag _ => cases hci | gpr rd =>
      cases rd with | SP => cases hci | reg d =>
      dsimp only [armOpIns, armBoolOpIns] at hci
      have hp := armBoolXorIns_pure_len hci; exact ⟨hp.1, by omega⟩
    | bits n =>
      cases pd with | vec v => exact v.elim | gpr rd =>
      cases rd with | SP => cases hci | reg d =>
      dsimp only [armOpIns] at hci
      have hp := armBinOpIns_pure_len hci; exact ⟨hp.1, by omega⟩
    | float _ | pair _ _ => cases hci
  | not t =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t with
    | bool =>
      cases pd with | vec v => exact v.elim | flag _ => cases hci | gpr rd =>
      cases rd with | SP => cases hci | reg d =>
      dsimp only [armOpIns, armBoolOpIns] at hci
      cases pa with
      | vec v => exact v.elim
      | imm _ => cases hci; exact armMovImmI_pure_le _ _ (by decide)
      | flag _ => cases hci; exact ⟨insPure_one rfl, by simp⟩
      | gpr r =>
        cases r with | SP => cases hci | reg _ => cases hci; exact ⟨insPure_one rfl, by simp⟩
    | bits n =>
      cases pd with | vec v => exact v.elim | gpr rd =>
      cases rd with | SP => cases hci | reg d =>
      dsimp only [armOpIns] at hci; split at hci; · cases hci
      cases pa with
      | vec v => exact v.elim
      | imm _ => cases hci; exact armMovImmI_pure_le _ _ (by decide)
      | gpr r =>
        cases r with | SP => cases hci | reg _ => cases hci; exact ⟨insPure_one rfl, by simp⟩
    | float _ | pair _ _ => cases hci
  | neg t =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t with | bool | float _ | pair _ _ => cases hci | bits n =>
    cases pd with | vec v => exact v.elim | gpr rd =>
    cases rd with | SP => cases hci | reg d =>
    dsimp only [armOpIns] at hci; split at hci; · cases hci
    cases pa with
    | vec v => exact v.elim
    | imm _ => cases hci; exact armMovImmI_pure_le _ _ (by decide)
    | gpr r =>
      cases r with | SP => cases hci | reg _ => cases hci; exact ⟨insPure_one rfl, by simp⟩
  | add t | sub t | mul t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t with | bool | float _ | pair _ _ => cases hci | bits n =>
    cases pd with | vec v => exact v.elim | gpr rd =>
    cases rd with | SP => cases hci | reg d =>
    dsimp only [armOpIns] at hci
    have hp := armBinOpIns_pure_len hci; exact ⟨hp.1, by omega⟩
  | shl t | lshr t | ashr t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t with | bool | float _ | pair _ _ => cases hci | bits n =>
    cases pd with | vec v => exact v.elim | gpr rd =>
    cases rd with | SP => cases hci | reg d =>
    dsimp only [armOpIns] at hci
    have hp := armShiftOpIns_pure_len hci; exact ⟨hp.1, by omega⟩
  | rotl t | rotr t =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t with | bool | float _ | pair _ _ => cases hci | bits n =>
    cases pd with | vec v => exact v.elim | gpr rd =>
    cases rd with | SP => cases hci | reg d =>
    dsimp only [armOpIns] at hci
    have hp := armRotOpIns_pure_len hci; exact ⟨hp.1, by omega⟩
  | udiv _ | udiv0 _ | sdiv _ | sdiv0 _ | urem _ | srem _ =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd with | vec v => exact v.elim | gpr rd =>
    cases rd with | SP => cases hci | reg d =>
    dsimp only [armOpIns] at hci
    have hp := armDivRemOpIns_pure_len hci; exact ⟨hp.1, by omega⟩
  | zext m n =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd with | vec v => exact v.elim | gpr rd =>
    cases rd with | SP => cases hci | reg d =>
    dsimp only [armOpIns, armZextOpIns] at hci; split at hci; · cases hci
    cases pa with
    | vec v => exact v.elim
    | imm _ => cases hci; exact armMovImmI_pure_le _ _ (by decide)
    | gpr r => cases r with | SP => cases hci | reg _ =>
      cases h8 : (m == 8) <;> simp only [h8, Bool.false_eq_true, ↓reduceIte] at hci
      · cases h16 : (m == 16) <;> simp only [h16, Bool.false_eq_true, ↓reduceIte] at hci
        · cases h32 : (m == 32) <;> simp only [h32, Bool.false_eq_true, ↓reduceIte] at hci <;>
            (cases hci; exact ⟨insPure_one rfl, by simp⟩)
        · cases hci; exact ⟨insPure_one rfl, by simp⟩
      · cases hci; exact ⟨insPure_one rfl, by simp⟩
  | sext m n =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd with | vec v => exact v.elim | gpr rd =>
    cases rd with | SP => cases hci | reg d =>
    dsimp only [armOpIns, armSextOpIns] at hci; split at hci; · cases hci
    cases pa with
    | vec v => exact v.elim
    | imm _ => cases hci; exact armMovImmI_pure_le _ _ (by decide)
    | gpr r => cases r with | SP => cases hci | reg _ =>
      cases h8 : (m == 8) <;> simp only [h8, Bool.false_eq_true, ↓reduceIte] at hci
      · cases h16 : (m == 16) <;> simp only [h16, Bool.false_eq_true, ↓reduceIte] at hci
        · cases h32 : (m == 32) <;> simp only [h32, Bool.false_eq_true, ↓reduceIte] at hci <;>
            (cases hci; exact ⟨insPure_one rfl, by simp⟩)
        · cases hci; exact ⟨insPure_one rfl, by simp⟩
      · cases hci; exact ⟨insPure_one rfl, by simp⟩
  | trunc m n =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd with | vec v => exact v.elim | gpr rd =>
    cases rd with | SP => cases hci | reg d =>
    dsimp only [armOpIns, armTruncOpIns] at hci; split at hci; · cases hci
    cases pa with
    | vec v => exact v.elim
    | imm _ => cases hci; exact armMovImmI_pure_le _ _ (by decide)
    | gpr r =>
      cases r with | SP => cases hci | reg _ => cases hci; exact ⟨insPure_one rfl, by simp⟩
  | ofBool n =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd with | vec v => exact v.elim | gpr rd =>
    cases rd with | SP => cases hci | reg d =>
    dsimp only [armOpIns, armOfBoolOpIns] at hci; split at hci; · cases hci
    cases pa with
    | vec v => exact v.elim
    | imm _ => cases hci; exact armMovImmI_pure_le _ _ (by decide)
    | flag _ => cases hci; exact ⟨insPure_one rfl, by simp⟩
    | gpr r =>
      cases r with | SP => cases hci | reg _ => cases hci; exact ⟨insPure_one rfl, by simp⟩
  | bswap t =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t with | bool | float _ | pair _ _ => cases hci | bits n =>
    cases pd with | vec v => exact v.elim | gpr rd =>
    cases rd with | SP => cases hci | reg d =>
    dsimp only [armOpIns, bind, Option.bind] at hci; split at hci; · cases hci
    cases h1 : armArgInIns .X16 pa with
    | none => simp [h1] at hci
    | some p1 =>
      rcases p1 with ⟨ca, ra⟩; simp only [h1, Option.some.injEq, Prod.mk.injEq] at hci
      rcases hci with ⟨rfl, rfl⟩; have ha := armArgInIns_pure_len h1
      have hrev : insPure none
          [if (n == 16) = true then armIselInsI (.REV16 (zr d .W32) (zr ra .W32))
           else if (n == 32) = true then armIselInsI (.REV (zr d .W32) (zr ra .W32))
           else armIselInsI (.REV (zr d .W64) (zr ra .W64))] := by
        cases (n == 16) <;> simp only [Bool.false_eq_true, ↓reduceIte]
        · cases (n == 32) <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
            exact insPure_one rfl
        · exact insPure_one rfl
      exact ⟨insPure_append ha.1 hrev, by simp; omega⟩
  | clz n | cls n | rbit n =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd with | vec v => exact v.elim | gpr rd =>
    cases rd with | SP => cases hci | reg d =>
    dsimp only [armOpIns, bind, Option.bind] at hci; split at hci; · cases hci
    cases h1 : armArgInIns .X16 pa with
    | none => simp [h1] at hci
    | some p1 =>
      rcases p1 with ⟨ca, ra⟩; simp only [h1, Option.some.injEq, Prod.mk.injEq] at hci
      rcases hci with ⟨rfl, rfl⟩; have ha := armArgInIns_pure_len h1
      exact ⟨insPure_append ha.1 (insPure_one rfl), by simp; omega⟩
  | ctz n =>
    rcases pas with ⟨pa, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd with | vec v => exact v.elim | gpr rd =>
    cases rd with | SP => cases hci | reg d =>
    dsimp only [armOpIns, bind, Option.bind] at hci; split at hci; · cases hci
    cases h1 : armArgInIns .X16 pa with
    | none => simp [h1] at hci
    | some p1 =>
      rcases p1 with ⟨ca, ra⟩; simp only [h1, Option.some.injEq, Prod.mk.injEq] at hci
      rcases hci with ⟨rfl, rfl⟩; have ha := armArgInIns_pure_len h1
      exact ⟨insPure_append ha.1 (insPure_cons rfl (insPure_one rfl)), by simp; omega⟩
  | cmp o t m hm =>
    subst hm; rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t with | bool | float _ | pair _ _ => cases hci | bits n =>
    dsimp only [armOpIns] at hci
    have hp := armCmpOpIns_pure_len hci; exact ⟨hp.1, by omega⟩
  | select t =>
    rcases pas with ⟨pc, pa, pb, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases t with | bool | float _ | pair _ _ => cases hci | bits n =>
    cases pd with | vec v => exact v.elim | gpr rd =>
    cases rd with | SP => cases hci | reg d =>
    dsimp only [armOpIns, armSelectOpIns, bind, Option.bind] at hci; split at hci; · cases hci
    cases pc with
    | vec v => exact v.elim
    | imm b => cases b <;> (have hp := armCopyBitsIns_pure_len hci; exact ⟨hp.1, by omega⟩)
    | flag cond =>
      cases hs : armSelectCondIns n cond pa pb d with
      | none => simp [hs] at hci
      | some sel =>
        simp only [hs, Option.some.injEq, Prod.mk.injEq] at hci; rcases hci with ⟨rfl, rfl⟩
        have hp := armSelectCondIns_pure_len hs; exact ⟨hp.1, by omega⟩
    | gpr r => cases r with | SP => cases hci | reg rc =>
      cases hs : armSelectCondIns n .ne pa pb d with
      | none => simp [hs] at hci
      | some sel =>
        simp only [hs, Option.some.injEq, Prod.mk.injEq] at hci; rcases hci with ⟨rfl, rfl⟩
        have hp := armSelectCondIns_pure_len hs; exact ⟨insPure_cons rfl hp.1, by simp; omega⟩
  | addc _ =>
    rcases pas with ⟨pa, pb, cin, ⟨⟩⟩; rcases dsts with ⟨pd, cout, ⟨⟩⟩
    cases pd with | vec v => exact v.elim | gpr rd =>
    cases rd with | SP => cases hci | reg d =>
    dsimp only [armOpIns] at hci
    have hp := armAddcSubb_pure_len false hci; exact ⟨hp.1, by omega⟩
  | subb _ =>
    rcases pas with ⟨pa, pb, bin, ⟨⟩⟩; rcases dsts with ⟨pd, bout, ⟨⟩⟩
    cases pd with | vec v => exact v.elim | gpr rd =>
    cases rd with | SP => cases hci | reg d =>
    dsimp only [armOpIns] at hci
    have hp := armAddcSubb_pure_len true hci; exact ⟨hp.1, by omega⟩
  | umulw _ | smulw _ =>
    rcases pas with ⟨pa, pb, ⟨⟩⟩; rcases dsts with ⟨p1, p2, ⟨⟩⟩
    cases p1 with | vec v => exact v.elim | gpr r1 =>
    cases r1 with | SP => cases hci | reg dlo =>
    cases p2 with | vec v => exact v.elim | gpr r2 =>
    cases r2 with | SP => cases hci | reg dhi =>
    dsimp only [armOpIns] at hci
    have hp := armMulwOpIns_pure_len hci; exact ⟨hp.1, by omega⟩
  | fshl _ | fshr _ =>
    rcases pas with ⟨pa, pb, pc, ⟨⟩⟩; rcases dsts with ⟨pd, ⟨⟩⟩
    cases pd with | vec v => exact v.elim | gpr rd =>
    cases rd with | SP => cases hci | reg d =>
    dsimp only [armOpIns] at hci
    have hp := armFunnelOpIns_pure_len hci; exact ⟨hp.1, by omega⟩
  | _ => dsimp only [armOpIns] at hci; cases hci

end LeanQbe.T.Arm64
