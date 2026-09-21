/-
Omnisemantics for x64.
-/

import Kraken.Attribute
import Kraken.OmniSemantics
import Kraken.X64.Semantics

@[kstep] def Effects.All (post : MachineState → Prop) : Effects → Prop
  | .done a => post a
  | .unimplemented _ => False
  | .gp_unaligned .. => False
  | .nonmem_load .. => False
  | .nonmem_store .. => False
  | @Effects.undefined α _ cont => ∀ v: α, (cont v).All post
  | .require_read_access _ _ cont => (cont ()).All post
  | .require_write_access _ _ cont => (cont ()).All post
  | .require_exec_access _ cont => (cont ()).All post

theorem Effects.All_of_false {_e₁ e₂ : Effects} {_post₁ post₂ : MachineState → Prop}
    (h : False) : e₂.All post₂ := False.elim h

theorem Effects.All_undefined {α : Type} [NondetSupportingType α]
    {cont₁ cont₂ : α → Effects} {post₁ post₂ : MachineState → Prop}
    (hcont : ∀ v, (cont₁ v).All post₁ → (cont₂ v).All post₂)
    (h : (@Effects.undefined α _ cont₁).All post₁) :
    (@Effects.undefined α _ cont₂).All post₂ :=
  fun v => hcont v (h v)

theorem Effects.All_ite {c : Prop} [Decidable c] {t₁ t₂ e₁ e₂ : Effects} {post₁ post₂ : MachineState → Prop}
    (ht : t₁.All post₁ → t₂.All post₂) (he : e₁.All post₁ → e₂.All post₂) :
    (if c then t₁ else e₁).All post₁ → (if c then t₂ else e₂).All post₂ := by
  split
  · exact ht
  · exact he

theorem Effects.All_dite {c : Prop} [Decidable c] {t₁ t₂ : c → Effects} {e₁ e₂ : ¬c → Effects} {post₁ post₂ : MachineState → Prop}
    (ht : ∀ h, (t₁ h).All post₁ → (t₂ h).All post₂) (he : ∀ h, (e₁ h).All post₁ → (e₂ h).All post₂) :
    (if h : c then t₁ h else e₁ h).All post₁ → (if h : c then t₂ h else e₂ h).All post₂ := by
  split
  · exact ht ‹_›
  · exact he ‹_›

#gen_mono
  Reg.interp
  MachineData.load
  MachineData.loadAvx
  MachineData.store
  MachineData.storeAvx
  RegOrMem.interp
  AvxRegOrMem.interp
  MachineData.set
  MachineData.setAvx
  MachineData.setAvxLegacy
  Operand.interp
  AvxOperand.interp
  RelRegOrMem.interp
  AvxOperation.interp
  Operation.interp
  Instr.interp
  Directive.interp

instance [Layout] : OmniSemantics Directive MachineData Effects where
  All := Effects.All
  done := Effects.done
  step := Executable.step
  straightline := Executable.straightline
  interpDirectives e := let _ := Executable.labels e; Directives.interp
  interpDirective e := let _ := Executable.labels e; Directive.interp
  interpDirective_mono e := let _ := Executable.labels e; Directive.interp_mono

def step1 [Layout] (e: Executable) (s: MachineState) (post: @Post MachineState) : Prop :=
  (Executable.step e s .done).All post

def straightlineStep [Layout] (e: Executable) (s: MachineState) (post: @Post MachineState) : Prop :=
  (Executable.straightline e s .done).All post

theorem eventually_step [Layout] (e: Executable) (hwf : e.WellFormed) (st: MachineState) (post: @Post MachineState) :
    straightlineStep e st post → Eventually (step1 e) post st :=
  OmniSemantics.eventually_step e hwf st post

theorem eventually_step_cps [Layout] (e : Executable) (hwf : e.WellFormed)
    (st : MachineState) (post : @Post MachineState) :
    straightlineStep e st (fun mid => Eventually (step1 e) post mid) →
    Eventually (step1 e) post st :=
  OmniSemantics.eventually_step_cps e hwf st post

theorem straightlineStep_mono [Layout] (e : Executable) (st : MachineState)
    {p q : @Post MachineState} (hpq : ∀ s, p s → q s) :
    straightlineStep e st p → straightlineStep e st q :=
  OmniSemantics.straightlineStep_mono e st hpq

theorem tailrec_loop_straightline [Layout] (e : Executable) (hwf : e.WellFormed)
    (post : @Post MachineState) (initial : MachineState)
    (P : Nat → @Post MachineState) (v0 : Nat) (hP : P v0 initial)
    (hbody : ∀ v state, P v state →
      straightlineStep e state (fun mid_s => post mid_s ∨ ∃ v', P v' mid_s ∧ v' < v)) :
    straightlineStep e initial (fun mid => Eventually (step1 e) post mid) :=
  OmniSemantics.tailrec_loop_straightline e hwf post initial P v0 hP hbody

