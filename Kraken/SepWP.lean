/-
The separation-logic weakest precondition. Assertions of the program logic
keep registers and flags state-passing and send only the memory through the
separation algebra of Kraken/MProp.lean:
`Reg64s → RegZmms → StatusFlags → MProp 64`, and `Int64 →` that for the exit
channel.

`Program.run q Q E s` is the run of the fragment `q` from `s` in the
baseline interpreter: in any burst that runs `q` and continues into the rest
of its directive list, `q` falls through with `Q` or exits with `E`.
`straightlineStep_of_sep_triple` reads a triple back as the `straightlineStep`
judgment of the laid-out program. `SepWP.instWP` interprets a
`Program` at the separation assertion language with the frame rule
internalized on both channels: a triple `⦃P⦄ p ⦃Q; E⦄` holds when the run
validates it under every memory frame, held across the fall-through and
across every exit. `SepWP.sep_intro` is the one door in, and `SepWP.frames`
says every program frames every memory assertion, which is what the frame
inference of `vcgen` consumes.
-/
import Kraken.MProp
import Kraken.X64.OmniSemantics

open Std.WP
open Lean.Order

/-! ## The run of a fragment

The run of a fragment is stated over the baseline interpreter's burst:
`Directives.interp` runs a list of directives, falling through from one to
the next and stopping at a jump or at the end of the list, which is how
`straightlineStep` runs a program. The fragment is a prefix of the list, and
the run hands the rest of the list the state the fragment falls through
with. `Program.run_straightlineStep` reads the run of a whole program as the
`straightlineStep` judgment of the laid-out program, for any layout. -/

/-- The address behind a run of directives of sizes `zs` from `pc`. -/
def Program.endPc (pc : Int64) (zs : List Nat) : Int64 := zs.foldl (fun pc z => pc + .ofNat z) pc

/-- The run of the fragment `q` from `s`: whatever label table, directive
sizes and continuation `rest` the fragment sits in, the burst from `pc`
satisfies `Φ` as soon as `rest` does from every state satisfying `Q` at the
end of `q`, and `Φ` holds at every exit satisfying `E`. -/
def Program.run (q : Program) (Q : MachineData → Prop) (E : Int64 → MachineData → Prop)
    (s : MachineData) : Prop :=
  ∀ (L : Labels) (ds rest : List (Directive × Nat)) (pc : Int64) (Φ : MachineState → Prop),
    ds.map (·.1) = q →
    (∀ s', Q s' →
      (@Directives.interp L rest s' (Program.endPc pc (ds.map (·.2))) fun pc s => .done (s, pc)).All Φ) →
    (∀ a s', E a s' → Φ (s', a)) →
    (@Directives.interp L (ds ++ rest) s pc fun pc s => .done (s, pc)).All Φ

/-- A run of a program is the baseline judgment of the laid-out program: from
the layout's start, the burst of `straightlineStep` ends in a state
satisfying `post` when the fall-through and every exit do. -/
theorem Program.run_straightlineStep [layout : Layout] {p : Program} {Q : MachineData → Prop}
    {E : Int64 → MachineData → Prop} {e : Executable} {st : MachineState}
    {post : MachineState → Prop} (h : Program.run p Q E st.1) (he : e = layout p)
    (hpc : st.2 = layout.start) (hQ : ∀ st', Q st'.1 → post st')
    (hE : ∀ a s', E a s' → post (s', a)) :
    straightlineStep e st post := by
  obtain ⟨s, pc⟩ := st
  subst he hpc
  show (@Directives.interp (Executable.labels (layout p)) ((layout p).directivesFromAddress
    layout.start) s layout.start fun pc s => .done (s, pc)).All _
  rw [Kraken.Executable.directivesFromStart, ← List.append_nil (p.mapIdx _)]
  exact h (Executable.labels (layout p)) _ [] layout.start _ (List.ext_getElem (by simp) (by simp))
    (fun s' hq => hQ (s', _) hq) hE

/- With a `Directives.interp` that returns its final state as
`Effects MachineState` instead of passing it to `ret`, the run would be the
burst's `.All` of the post, without the continuation `rest` and the post `Φ`:
`(Directives.interp ds s pc).All fun st => (st.2 = endPc pc sizes ∧ Q st.1) ∨ E st.2 st.1`.
`Program.run_cons` would then be the bind law of `Effects.All`, and the lemma
above the instance `ds := (layout p).2`. -/

theorem Program.run_mono {q : Program} {Q₁ Q₂ : MachineData → Prop}
    {E₁ E₂ : Int64 → MachineData → Prop} (hQ : ∀ s, Q₁ s → Q₂ s) (hE : ∀ a s, E₁ a s → E₂ a s)
    {s : MachineData} (h : Program.run q Q₁ E₁ s) : Program.run q Q₂ E₂ s :=
  fun L ds rest pc Φ hds hQ₂ hE₂ =>
    h L ds rest pc Φ hds (fun s' h' => hQ₂ s' (hQ s' h')) (fun a s' h' => hE₂ a s' (hE a s' h'))

/-- The run of `d :: q` is the run of `d` with the run of `q` as its post:
the burst falls through `d` into `q`. -/
theorem Program.run_cons {d : Directive} {q : Program} {Q : MachineData → Prop}
    {E : Int64 → MachineData → Prop} {s : MachineData}
    (h : Program.run [d] (fun s' => Program.run q Q E s') E s) : Program.run (d :: q) Q E s := by
  intro L ds rest pc Φ hds hQ hE
  match ds, hds with
  | (d', z) :: ds', hds =>
    obtain ⟨rfl, hq⟩ := List.cons.inj hds
    exact h L [(d', z)] (ds' ++ rest) pc Φ rfl
      (fun s' hrun => hrun L ds' rest (pc + Int64.ofNat z) Φ hq hQ hE) hE

/-! ## The frame operator

The frame is a pure memory assertion. It acts on an assertion of the program
logic pointwise through the state-passing layers, and `FrameOp` derives its
companion on the exit channel through one more layer. -/

namespace SepWP

/-- Frame a memory resource onto an assertion: `∗` under the register, vector
and flag layers. -/
def frameOp (F : MProp 64) (P : Reg64s → RegZmms → StatusFlags → MProp 64) :
    Reg64s → RegZmms → StatusFlags → MProp 64 :=
  fun r z f => F ∗ P r z f

instance (F : MProp 64) : PreservesSup (frameOp F) :=
  inferInstanceAs (PreservesSup (Function.comp (Function.comp (Function.comp (MProp.sep F)))))

@[simp, grind =] theorem frameOp_apply (F : MProp 64)
    (P : Reg64s → RegZmms → StatusFlags → MProp 64) (r : Reg64s) (z : RegZmms)
    (f : StatusFlags) : frameOp F P r z f = F ∗ P r z f := rfl

/-! ## The instance -/

/-- The run, read at the separation assertion language: the memory is
curried out of `MachineData`. -/
@[instance_reducible] private def base :
    WP Program Unit (Reg64s → RegZmms → StatusFlags → MProp 64)
      (Int64 → Reg64s → RegZmms → StatusFlags → MProp 64) where
  trans q := ⟨fun Q E regs zmms flags => MProp.mk fun mem =>
    Program.run q (fun s' => (Q () s'.regs s'.zmms s'.status).get s'.dmem)
      (fun a s' => (E a s'.regs s'.zmms s'.status).get s'.dmem)
      ⟨regs, zmms, flags, mem⟩⟩
  trans_monotone q := by
    intro Q Q' E E' hE hQ regs zmms flags
    refine (MProp.le_def _ _).mpr fun mem h => ?_
    dsimp only at h ⊢
    rw [MProp.get_mk] at h ⊢
    exact Program.run_mono
      (fun s' => (MProp.le_def _ _).mp (hQ () s'.regs s'.zmms s'.status) s'.dmem)
      (fun a s' => (MProp.le_def _ _).mp (hE a s'.regs s'.zmms s'.status) s'.dmem) h

/-- The run read back out of the base transformer. -/
private theorem get_base_apply (q : Program)
    (Q : Unit → Reg64s → RegZmms → StatusFlags → MProp 64)
    (E : Int64 → Reg64s → RegZmms → StatusFlags → MProp 64)
    (regs : Reg64s) (zmms : RegZmms) (flags : StatusFlags) (mem : Mem 64) :
    ((base.trans q).apply Q E regs zmms flags).get mem ↔
      Program.run q (fun s' => (Q () s'.regs s'.zmms s'.status).get s'.dmem)
        (fun a s' => (E a s'.regs s'.zmms s'.status).get s'.dmem) ⟨regs, zmms, flags, mem⟩ :=
  Iff.of_eq (congrArg (· mem) (MProp.get_mk _))

/-- Triples of the separation examples: the frame rule internalized on both
channels over the run. -/
noncomputable scoped instance instWP :
    WP Program Unit (Reg64s → RegZmms → StatusFlags → MProp 64)
      (Int64 → Reg64s → RegZmms → StatusFlags → MProp 64) :=
  WP.withFrameClosure frameOp base

/-- Prove a separation triple: the run validates it under an arbitrary memory
frame, held across the fall-through and across every exit. -/
theorem sep_intro {q : Program}
    {P : Reg64s → RegZmms → StatusFlags → MProp 64}
    {Q : Unit → Reg64s → RegZmms → StatusFlags → MProp 64}
    {E : Int64 → Reg64s → RegZmms → StatusFlags → MProp 64}
    (h : ∀ (F : MProp 64) (s : MachineData),
      (F ∗ P s.regs s.zmms s.status).get s.dmem →
      Program.run q (fun s' => (F ∗ Q () s'.regs s'.zmms s'.status).get s'.dmem)
        (fun a s' => (F ∗ E a s'.regs s'.zmms s'.status).get s'.dmem) s) :
    ⦃ P ⦄ q ⦃ Q; E ⦄ := by
  refine ⟨WP.le_wp_of_withFrameClosure_eq (base := base) rfl ?_⟩
  intro F regs zmms flags
  refine (MProp.le_def _ _).mpr fun mem hpre => ?_
  exact (get_base_apply q _ _ regs zmms flags mem).mpr (h F ⟨regs, zmms, flags, mem⟩ hpre)

/-- Consume a separation triple's wp under a frame: the run of the framed
pre- and postconditions follows, which is how a spec's proof enters the run
of the tail. The dual of `sep_intro`. -/
theorem sep_elim {q : Program} {F : MProp 64}
    {Q : Unit → Reg64s → RegZmms → StatusFlags → MProp 64}
    {E : Int64 → Reg64s → RegZmms → StatusFlags → MProp 64} {s : MachineData}
    (h : (F ∗ WP.wp (self := instWP) q Q E s.regs s.zmms s.status).get s.dmem) :
    Program.run q (fun s' => (F ∗ Q () s'.regs s'.zmms s'.status).get s'.dmem)
      (fun a s' => (F ∗ E a s'.regs s'.zmms s'.status).get s'.dmem) s := by
  have hle := (PredTrans.le_frameClosure_iff frameOp (base.trans q) (Q := Q) (E := E)
    (pre := WP.wp (self := instWP) q Q E)).mp PartialOrder.rel_refl F
  exact (get_base_apply q _ _ s.regs s.zmms s.status s.dmem).mp
    ((MProp.le_def _ _).mp (hle s.regs s.zmms s.status) s.dmem h)

/-- Every program frames every memory assertion, on both channels: the
interpretation is a frame closure, and `∗` composes resources by `sep_assoc`.
This is the fact the frame inference of `vcgen` discharges per spec
application. -/
theorem frames (q : Program) (F : MProp 64) : WP.Frames frameOp q F := by
  refine WP.frames_of_frameClosure frameOp MProp.sep ?_ ?_ ⟨fun q => base.trans q, fun _ => rfl⟩
  · intro r r' a
    funext regs zmms flags
    show (r ∗ r') ∗ a regs zmms flags = r ∗ (r' ∗ a regs zmms flags)
    exact MProp.sep_assoc r r' (a regs zmms flags)
  · intro r r' E
    funext a regs zmms flags
    show (r ∗ r') ∗ E a regs zmms flags = r ∗ (r' ∗ E a regs zmms flags)
    exact MProp.sep_assoc r r' (E a regs zmms flags)

/-- Triples of one directive: the interpretation of the singleton program. -/
noncomputable scoped instance :
    WP Directive Unit (Reg64s → RegZmms → StatusFlags → MProp 64)
      (Int64 → Reg64s → RegZmms → StatusFlags → MProp 64) where
  trans d := WP.trans (self := instWP) [d]
  trans_monotone d := WP.trans_monotone (self := instWP) [d]

theorem triple_directive {d : Directive}
    {P : Reg64s → RegZmms → StatusFlags → MProp 64}
    {Q : Unit → Reg64s → RegZmms → StatusFlags → MProp 64}
    {E : Int64 → Reg64s → RegZmms → StatusFlags → MProp 64} :
    (⦃ P ⦄ d ⦃ Q; E ⦄) ↔ (⦃ P ⦄ [d] ⦃ Q; E ⦄) :=
  ⟨fun h => ⟨h.1⟩, fun h => ⟨h.1⟩⟩

/-- Chaining: a program runs its first directive with the wp of the rest as
the post. Every instruction spec is a triple of one directive; this rule is
where `vcgen` sequences them. -/
@[spec] theorem cons_spec (d : Directive) (p : Program)
    {Q : Unit → Reg64s → RegZmms → StatusFlags → MProp 64}
    {E : Int64 → Reg64s → RegZmms → StatusFlags → MProp 64} :
    ⦃ WP.wp d (fun _ => WP.wp p Q E) E ⦄ (d :: p) ⦃ Q; E ⦄ := by
  refine sep_intro fun F s hpre => ?_
  have h1 := sep_elim (q := [d]) (Q := fun _ => WP.wp p Q E) hpre
  exact Program.run_cons
    (Program.run_mono (fun s' hs' => sep_elim (q := p) hs') (fun _ _ h => h) h1)

/-- The frame fact of one directive: what the frame inference of `vcgen`
discharges per spec application. -/
@[grind .] theorem frames_directive (d : Directive) (F : MProp 64) :
    WP.Frames frameOp d F :=
  ⟨(frames [d] F).op_wp_le_wp_op⟩

end SepWP

/-! ## Reading a triple back as the baseline judgment

A triple of a program with no exits is a run of the laid-out program. Take a
state `st` at the layout's start whose memory satisfies `footprint` next to
`frame`. The triple from `st`'s registers, vector registers and flags,
owning `footprint`, gives `post` of the final state when its postcondition,
given `frame` back, is `post` of the whole final state at every pc. -/

open SepWP in
theorem straightlineStep_of_sep_triple [layout : Layout] {p : Program} {e : Executable}
    {st : MachineState} {post : MachineState → Prop} {footprint frame : MProp 64}
    (hmem : (footprint ∗ frame).get st.1.dmem)
    (he : e = layout p := by rfl) (hpc : st.2 = layout.start := by rfl)
    (ht : ⦃ fun r z f => ⌜r = st.1.regs ∧ z = st.1.zmms ∧ f = st.1.status⌝ ⊓ footprint ⦄ p
      ⦃ fun _ r z f => frame -∗ MProp.mk fun m => ∀ pc, post (⟨r, z, f, m⟩, pc) ⦄) :
    straightlineStep e st post := by
  have ⟨m₁, m₂, hu, hd, hfp, hfr⟩ := (MProp.get_sep_apply_iff _ _ _).mp hmem
  have hpre : (⌜st.1.regs = st.1.regs ∧ st.1.zmms = st.1.zmms ∧ st.1.status = st.1.status⌝
      ⊓ footprint).get m₁ :=
    (MProp.get_meet_apply_iff _ _ _).mpr ⟨(MProp.get_ofProp_apply_iff _ _).mpr ⟨rfl, rfl, rfl⟩, hfp⟩
  have hown : (_ ∗ frame).get st.1.dmem :=
    (MProp.get_sep_apply_iff _ _ _).mpr ⟨m₁, m₂, hu, hd, hpre, hfr⟩
  rw [MProp.sep_comm] at hown
  refine Program.run_straightlineStep (sep_elim ((MProp.le_def _ _).mp
    (MProp.sep_mono_right _ (ht.le_wp st.1.regs st.1.zmms st.1.status)) _ hown)) he hpc
    (fun st' hq => ?_) (fun a s' he => ?_)
  · have h := (MProp.le_def _ _).mp (MProp.sep_wand_elim _ _) _ hq
    rw [MProp.get_mk] at h
    exact h st'.2
  · exact (MProp.of_get_sep he
      ((bot_le (fun _ _ _ _ => (⌜False⌝ : MProp 64))) a s'.regs s'.zmms s'.status)).elim

open SepWP in
/-- `straightlineStep_of_sep_triple` for a burst that ends the run. -/
theorem eventually_straightlineStep_of_sep_triple [layout : Layout] {p : Program}
    {e : Executable} {st : MachineState} {post : MachineState → Prop} {footprint frame : MProp 64}
    (hmem : (footprint ∗ frame).get st.1.dmem)
    (he : e = layout p := by rfl) (hpc : st.2 = layout.start := by rfl)
    (ht : ⦃ fun r z f => ⌜r = st.1.regs ∧ z = st.1.zmms ∧ f = st.1.status⌝ ⊓ footprint ⦄ p
      ⦃ fun _ r z f => frame -∗ MProp.mk fun m => ∀ pc, post (⟨r, z, f, m⟩, pc) ⦄) :
    Eventually (straightlineStep e) post st :=
  .step _ _ (straightlineStep_of_sep_triple hmem he hpc ht) fun _ h => .done _ h
