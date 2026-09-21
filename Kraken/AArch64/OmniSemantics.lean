/-
Omnisemantics for AArch64.
-/

import Kraken.AArch64.Semantics
import Kraken.Attribute
import Kraken.OmniSemantics

@[kstep] def Effects.All (post : MachineState → Prop) : Effects → Prop
  | .done a => post a
  | .unimplemented _ => False
  | .unaligned_sp .. => False
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
  RegOrSp.interp
  RegOrZr.interp
  MachineData.load
  MachineData.store
  AddrExpr.checkSPAlignment
  AddrExpr.interpLoad
  AddrExpr.interpStore
  UnscaledAddrExpr.checkSPAlignment
  UnscaledAddrExpr.interpLoad
  UnscaledAddrExpr.interpStore
  Literal.interpLoad
  AddrOrLit.interpLoad
  MachineData.setRegOrSp
  MachineData.setRegOrZr
  Operation.interp
  Instr.interp
  Directive.interp

theorem Directives.interp_mono [Labels]
    (ds : List (Directive × Nat)) (s : MachineData) (pc : Int64)
    {ret₁ ret₂ : Int64 → MachineData → Effects}
    {post₁ post₂ : MachineState → Prop}
    (hret : ∀ pc' s', (ret₁ pc' s').All post₁ → (ret₂ pc' s').All post₂)
    (h : (Directives.interp ds s pc ret₁).All post₁) :
    (Directives.interp ds s pc ret₂).All post₂ := by
  induction ds generalizing s pc with
  | nil =>
    exact hret pc s h
  | cons head tail ih =>
    obtain ⟨d, sz⟩ := head
    dsimp [Directives.interp] at *
    exact Directive.interp_mono d s (.mk pc (pc + .ofNat sz))
      (fun s' => ih s' (pc + .ofNat sz))
      hret
      h

def step1 [Layout] (e: Executable) (s: MachineState) (post: @Post MachineState) : Prop :=
  (Executable.step e s .done).All post

def straightlineStep [Layout] (e: Executable) (s: MachineState) (post: @Post MachineState) : Prop :=
  (Executable.straightline e s .done).All post
