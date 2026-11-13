module

public import KrakenIris.OmniSemantics
public import Kraken.X64.OmniSemantics
public import Iris.BI.Lib.Fixpoint

/-!
# `Eventually`, in Iris

`Eventually` (`Kraken/OmniSemantics.lean`) is a least fixpoint in `Prop`, and
`EventuallyI` below is the same least fixpoint in `IProp`.
A specification reads as before:

    EventuallyI (straightlineStepI (layout prog)) post ⟨s, layout.start⟩

* whatever `Eventually` proves, `EventuallyI` proves too: `eventuallyI_of_eventually`;
* a loop that accesses the shared memory on every round can be proved by Löb induction, since
  each access puts a `▷` in front of what follows; such a proof does not show termination.
-/

@[expose] public section

open Iris BI

section
variable {GF : BundledGFunctors} {State : Type}

def EventuallyI.pre (trans : State → (State → IProp GF) → IProp GF) (post : State → IProp GF)
    (ev : State → IProp GF) (s : State) : IProp GF :=
  iprop(post s ∨ ∃ mid : State → IProp GF, trans s mid ∗ ∀ s', mid s' -∗ ev s')

variable [OFE State] [OFE.Discrete State]
variable {trans : State → (State → IProp GF) → IProp GF} {post : State → IProp GF}

instance EventuallyI.pre_mono : BIMonoPred (EventuallyI.pre trans post) where
  mono_pred := by
    intro p q _ _
    iintro #H %s Hpre
    unfold EventuallyI.pre
    icases Hpre with (Hpost | ⟨%mid, Htrans, Hmid⟩)
    · ileft
      iexact Hpost
    · iright
      iexists mid
      iframe Htrans
      iintro %s' Hm
      iapply H
      iapply Hmid $$ Hm
  mono_pred_ne := ⟨fun {_ _ _} h => .of_eq (congrArg _ (OFE.discrete h))⟩

/-- `EventuallyI` is defined as a least fixpoint, in the same way as `Eventually`. -/
def EventuallyI (trans : State → (State → IProp GF) → IProp GF) (post : State → IProp GF)
    (s : State) : IProp GF :=
  bi_least_fixpoint (EventuallyI.pre trans post) s

theorem EventuallyI.unfold (s : State) :
    EventuallyI trans post s = iprop(post s ∨ ∃ mid : State → IProp GF,
      trans s mid ∗ ∀ s', mid s' -∗ EventuallyI trans post s') :=
  least_fixpoint_unfold (EventuallyI.pre trans post)

theorem EventuallyI.done (s : State) : post s ⊢ EventuallyI trans post s := by
  rw [EventuallyI.unfold]
  iintro H
  ileft
  iexact H

theorem EventuallyI.step (s : State) (mid : State → IProp GF) :
    trans s mid -∗ (∀ s', mid s' -∗ EventuallyI trans post s') -∗ EventuallyI trans post s := by
  rw [EventuallyI.unfold]
  iintro Htrans Hmid
  iright
  iexists mid
  iframe Htrans Hmid

theorem EventuallyI.step_cps (s : State) :
    trans s (EventuallyI trans post) ⊢ EventuallyI trans post s := by
  iintro H
  iapply EventuallyI.step s (EventuallyI trans post) $$ H
  iintro %s' H
  iexact H

end

section x64
variable {GF : BundledGFunctors} [InvGS GF] [G : krakenGS GF]

instance : OFE MachineState := OFE.ofDiscrete _
instance : OFE.Discrete MachineState := ⟨fun h => h⟩

def straightlineStepI (e : Executable) (s : MachineState) (post : MachineState → IProp GF) :
    IProp GF := (Executable.straightline e s .done).AllI ⊤ post

/-! ## Sequential proofs carry over -/

theorem Effects.AllI₀_of_All (post : MachineState → Prop) (e : Effects) (h : e.All post) :
    ⊢ (|={∅, ⊤}=> emp) -∗ e.AllI₀ (GF := GF) (fun s => iprop(⌜post s⌝)) := by
  induction e with
  | done s =>
    rw [Effects.AllI₀]
    iintro Hclose
    imod Hclose
    imodintro
    ipureintro
    exact h
  | unimplemented msg => exact absurd h id
  | gp_unaligned addr w => exact absurd h id
  | nonmem_load dmem a w k ih => exact absurd h id
  | nonmem_store dmem a v k ih => exact absurd h id
  | undefined k ih =>
    rw [Effects.AllI₀]
    iintro Hclose %v
    imodintro
    iapply ih v (h v) $$ Hclose
  | require_read_access span k ih =>
    rw [Effects.AllI₀]
    exact ih () h
  | require_write_access span k ih =>
    rw [Effects.AllI₀]
    exact ih () h
  | require_exec_access p k ih =>
    rw [Effects.AllI₀]
    exact ih () h
  | yield k ih =>
    rw [Effects.AllI₀]
    iintro Hclose
    imod Hclose
    imodintro
    iapply fupd_mask_intro (by simp)
    iintro Hclose
    iapply ih () h $$ Hclose

theorem Effects.AllI_of_All (post : MachineState → Prop) (e : Effects) (h : e.All post) :
    ⊢ e.AllI (GF := GF) ⊤ (fun s => iprop(⌜post s⌝)) := by
  unfold Effects.AllI
  iapply fupd_mask_intro (by simp)
  iintro Hclose
  iapply Effects.AllI₀_of_All post e h $$ Hclose

/-- `Eventually` implies `EventuallyI`. -/
theorem eventuallyI_of_eventually [Layout] (e : Executable) (post : MachineState → Prop)
    (s : MachineState) (h : Eventually (straightlineStep e) post s) :
    ⊢ EventuallyI (straightlineStepI (GF := GF) e) (fun s' => iprop(⌜post s'⌝)) s := by
  induction h with
  | done s hpost =>
    iapply EventuallyI.done
    ipureintro
    exact hpost
  | step s mid_p hstep _ ih =>
    iapply EventuallyI.step s (fun s' => iprop(⌜mid_p s'⌝))
    · rw [straightlineStepI]
      iapply Effects.AllI_of_All mid_p _ hstep
    · iintro %s' %hmid
      iapply ih s' hmid

end x64
