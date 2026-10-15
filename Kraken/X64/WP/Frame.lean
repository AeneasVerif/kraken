module

/-
The separation-logic weakest precondition. Assertions of the program logic
keep registers and flags state-passing and send only the memory through the
separation algebra of Kraken/MProp.lean:
`Reg64s → RegZmms → StatusFlags → MProp 64`, and `Int64 →` that for the exit
channel.

`Program.FrameWP.instWP` interprets a `Program` over the run `Program.wp` of
Kraken/X64/WP/Basic.lean, at the separation assertion language with the frame rule
internalized on both channels: a triple `⦃P⦄ p ⦃Q; E⦄` holds when the run
validates it under every memory frame, held across the fall-through and
across every exit. `Program.FrameWP.sep_intro` is the one door in, and `Program.FrameWP.frames`
says every program frames every memory assertion, which is what the frame
inference of `vcgen` consumes. `Program.FrameWP.straightline_of_wp` reads the wp back
as the `Eventually` judgment of the laid-out program.
-/
public import Kraken.MProp
public import Kraken.X64.WP

@[expose] public section

open Std.WP
open Lean.Order

/-! ## The frame operator

The frame is a pure memory assertion. It acts on an assertion of the program
logic pointwise through the state-passing layers, and `FrameOp` derives its
companion on the exit channel through one more layer. -/

namespace Program.FrameWP

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
@[instance_reducible] def base [Host] [BlockEntries] [FunDecls] :
    WP Fragment Unit (Reg64s → RegZmms → StatusFlags → MProp 64)
      (Int64 → Reg64s → RegZmms → StatusFlags → MProp 64) where
  trans q := ⟨fun Q E regs zmms flags => MProp.mk fun mem =>
    @Program.wp _ _ _ q.prog q.embeds (fun s' => (Q () s'.regs s'.zmms s'.status).get s'.dmem)
      (fun a s' => (E a s'.regs s'.zmms s'.status).get s'.dmem)
      ⟨regs, zmms, flags, mem⟩⟩
  trans_monotone q := by
    intro Q Q' E E' hE hQ regs zmms flags
    refine (MProp.le_def _ _).mpr fun mem h => ?_
    dsimp only at h ⊢
    rw [MProp.get_mk] at h ⊢
    exact @Program.wp_mono _ _ _ q.prog q.embeds _ _ _ _
      (fun s' => (MProp.le_def _ _).mp (hQ () s'.regs s'.zmms s'.status) s'.dmem)
      (fun a s' => (MProp.le_def _ _).mp (hE a s'.regs s'.zmms s'.status) s'.dmem) _ h

/-- The run read back out of the base transformer. -/
theorem get_base_apply [Host] [BlockEntries] [FunDecls] (q : Fragment)
    (Q : Unit → Reg64s → RegZmms → StatusFlags → MProp 64)
    (E : Int64 → Reg64s → RegZmms → StatusFlags → MProp 64)
    (regs : Reg64s) (zmms : RegZmms) (flags : StatusFlags) (mem : Mem 64) :
    ((base.trans q).apply Q E regs zmms flags).get mem ↔
      @Program.wp _ _ _ q.prog q.embeds (fun s' => (Q () s'.regs s'.zmms s'.status).get s'.dmem)
        (fun a s' => (E a s'.regs s'.zmms s'.status).get s'.dmem) ⟨regs, zmms, flags, mem⟩ :=
  Iff.of_eq (congrArg (· mem) (MProp.get_mk _))

/-- Triples of the separation examples: the frame rule internalized on both
channels over the run. -/
noncomputable scoped instance instWP [Host] [BlockEntries] [FunDecls] :
    WP Fragment Unit (Reg64s → RegZmms → StatusFlags → MProp 64)
      (Int64 → Reg64s → RegZmms → StatusFlags → MProp 64) :=
  WP.withFrameClosure frameOp base

/-- Prove a separation triple: the run validates it under an arbitrary memory
frame, held across the fall-through and across every exit. -/
theorem sep_intro [Host] [BlockEntries] [FunDecls] {q : Fragment}
    {P : Reg64s → RegZmms → StatusFlags → MProp 64}
    {Q : Unit → Reg64s → RegZmms → StatusFlags → MProp 64}
    {E : Int64 → Reg64s → RegZmms → StatusFlags → MProp 64}
    (h : ∀ (F : MProp 64) (s : MachineData),
      (F ∗ P s.regs s.zmms s.status).get s.dmem →
      @Program.wp _ _ _ q.prog q.embeds (fun s' => (F ∗ Q () s'.regs s'.zmms s'.status).get s'.dmem)
        (fun a s' => (F ∗ E a s'.regs s'.zmms s'.status).get s'.dmem) s) :
    ⦃ P ⦄ q ⦃ Q; E ⦄ := by
  refine ⟨WP.le_wp_of_withFrameClosure_eq (base := base) rfl ?_⟩
  intro F regs zmms flags
  refine (MProp.le_def _ _).mpr fun mem hpre => ?_
  exact (get_base_apply q _ _ regs zmms flags mem).mpr (h F ⟨regs, zmms, flags, mem⟩ hpre)

/-- Consume a separation triple's wp under a frame: the run of the framed
pre- and postconditions follows, which is how a spec's proof enters the run
of the tail. The dual of `sep_intro`. -/
theorem sep_elim [Host] [BlockEntries] [FunDecls] {q : Fragment} {F : MProp 64}
    {Q : Unit → Reg64s → RegZmms → StatusFlags → MProp 64}
    {E : Int64 → Reg64s → RegZmms → StatusFlags → MProp 64} {s : MachineData}
    (h : (F ∗ WP.wp (self := instWP) q Q E s.regs s.zmms s.status).get s.dmem) :
    @Program.wp _ _ _ q.prog q.embeds (fun s' => (F ∗ Q () s'.regs s'.zmms s'.status).get s'.dmem)
      (fun a s' => (F ∗ E a s'.regs s'.zmms s'.status).get s'.dmem) s := by
  have hle := (PredTrans.le_frameClosure_iff frameOp (base.trans q) (Q := Q) (E := E)
    (pre := WP.wp (self := instWP) q Q E)).mp PartialOrder.rel_refl F
  exact (get_base_apply q _ _ s.regs s.zmms s.status s.dmem).mp
    ((MProp.le_def _ _).mp (hle s.regs s.zmms s.status) s.dmem h)

/-- Every program frames every memory assertion, on both channels: the
interpretation is a frame closure, and `∗` composes resources by `sep_assoc`.
This is the fact the frame inference of `vcgen` discharges per spec
application. -/
theorem frames [Host] [BlockEntries] [FunDecls] (q : Fragment) (F : MProp 64) : WP.Frames frameOp q F := by
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
noncomputable scoped instance [Host] [BlockEntries] [FunDecls] :
    WP DirectiveAt Unit (Reg64s → RegZmms → StatusFlags → MProp 64)
      (Int64 → Reg64s → RegZmms → StatusFlags → MProp 64) where
  trans d := WP.trans (self := instWP) (@Fragment.mk _ [d.directive] d.embeds)
  trans_monotone d := WP.trans_monotone (self := instWP) (@Fragment.mk _ [d.directive] d.embeds)

theorem triple_directive [Host] [BlockEntries] [FunDecls] {d : Directive} [Embeds [d]]
    {P : Reg64s → RegZmms → StatusFlags → MProp 64}
    {Q : Unit → Reg64s → RegZmms → StatusFlags → MProp 64}
    {E : Int64 → Reg64s → RegZmms → StatusFlags → MProp 64} :
    (⦃ P ⦄ DirectiveAt.mk d ⦃ Q; E ⦄) ↔ (⦃ P ⦄ frag% [d] ⦃ Q; E ⦄) :=
  ⟨fun h => ⟨h.1⟩, fun h => ⟨h.1⟩⟩

/-- Chaining: a program runs its first directive with the wp of the rest as
the post. Every instruction spec is a triple of one directive; this rule is
where `vcgen` sequences them. -/
@[spec] theorem cons_spec [Host] [BlockEntries] [FunDecls] (d : Directive) (p : Program) [H : Embeds (d :: p)]
    [hN : _root_.NoEntries (d :: p)]
    {Q : Unit → Reg64s → RegZmms → StatusFlags → MProp 64}
    {E : Int64 → Reg64s → RegZmms → StatusFlags → MProp 64} :
    ⦃ haveI : Embeds [d] := .ofIsInfixAt H (List.isInfixAt_cons_head d p)
      WP.wp (DirectiveAt.mk d) (fun _ =>
        haveI : Embeds p := .ofIsInfixAt H (List.isInfixAt_cons_tail d p)
        WP.wp (frag% p) Q E) E ⦄ frag% (d :: p) ⦃ Q; E ⦄ := by
  refine sep_intro fun F s hpre => ?_
  letI : Embeds [d] := .ofIsInfixAt H (List.isInfixAt_cons_head d p)
  letI : Embeds p := .ofIsInfixAt H (List.isInfixAt_cons_tail d p)
  have h1 := sep_elim (q := frag% [d]) (Q := fun _ => WP.wp (frag% p) Q E) hpre
  exact Program.wp_cons hN.out (Program.wp_mono (fun s' hs' => sep_elim (q := frag% p) hs') (fun _ _ h => h) h1)

/-- The empty program: its wp is the postcondition. -/
@[spec] theorem nil_spec [Host] [BlockEntries] [FunDecls] [Embeds []]
    {Q : Unit → Reg64s → RegZmms → StatusFlags → MProp 64}
    {E : Int64 → Reg64s → RegZmms → StatusFlags → MProp 64} :
    ⦃ fun rg z f => Q () rg z f ⦄ frag% [] ⦃ Q; E ⦄ :=
  sep_intro fun _ _ hpre => Program.wp_nil hpre

/-- The frame fact of one directive: what the frame inference of `vcgen`
discharges per spec application. -/
@[grind .] theorem frames_directive [Host] [BlockEntries] [FunDecls] (d : DirectiveAt) (F : MProp 64) :
    WP.Frames frameOp d F :=
  ⟨(frames (@Fragment.mk _ [d.directive] d.embeds) F).op_wp_le_wp_op⟩

end Program.FrameWP

/-! ## Reading the wp back as the baseline judgment

The wp of a program with no exits is a run of the laid-out program. Take a
state `s` whose memory satisfies `footprint` next to `frame`. If `footprint`
entails the wp of the program at `s`'s registers, vector registers and flags,
for the postcondition that gives `frame` back and asks `post` of the whole
final state at every pc, then the run from `s` at the layout's start
eventually ends in `post`. The entailment is asked in every linked program. The laid-out program is a
valid executable. -/

open Program.FrameWP in
theorem Program.FrameWP.step1_of_wp_at [Host] [BlockEntries] [FunDecls] {p : Program} [h : Embeds p]
    {s : MachineData} {post : @Post MachineState} {footprint frame : MProp 64}
    (hmem : (footprint ∗ frame).get s.dmem)
    (ht : footprint ⊑ WP.wp (frag% p)
      (fun _ r z f => frame -∗ MProp.mk fun m => ∀ pc, post ⟨⟨r, z, f, m⟩, pc⟩)
      ⊥ s.regs s.zmms s.status) :
    Eventually (step1 Host.exe) post ⟨s, Host.addrOf h.embedding.start⟩ := by
  rw [MProp.sep_comm] at hmem
  have hw := sep_elim (q := frag% p) (F := frame) ((MProp.le_def _ _).mp (MProp.sep_mono_right _ ht) _ hmem)
  refine Program.step1_of_wp hw (fun s' hq => ?_) (fun a s' he => ?_)
  · have h := (MProp.le_def _ _).mp (MProp.sep_wand_elim _ _) _ hq
    rw [MProp.get_mk] at h
    exact h _
  · exact (MProp.of_get_sep he
      ((bot_le (fun _ _ _ _ => (⌜False⌝ : MProp 64))) a s'.regs s'.zmms s'.status)).elim

open Program.FrameWP in
theorem Program.FrameWP.step1_of_wp [Host] [BlockEntries] [FunDecls] {p : Program}
    (hp : p.IsInfix Host.prog) {s : MachineData}
    {post : @Post MachineState} {footprint frame : MProp 64}
    (hmem : (footprint ∗ frame).get s.dmem)
    (ht : footprint ⊑ WP.wp (@Fragment.mk _ p (Embeds.ofIsInfix hp))
      (fun _ r z f => frame -∗ MProp.mk fun m => ∀ pc, post ⟨⟨r, z, f, m⟩, pc⟩)
      ⊥ s.regs s.zmms s.status) :
    Eventually (step1 Host.exe) post ⟨s, startAddr hp⟩ :=
  @Program.FrameWP.step1_of_wp_at _ _ _ p (Embeds.ofIsInfix hp) s post footprint frame hmem ht
