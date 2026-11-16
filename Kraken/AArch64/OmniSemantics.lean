module

/-
Omnisemantics for AArch64.
-/

public import Kraken.AArch64.Semantics
import Kraken.Attribute
public import Kraken.OmniSemantics

@[expose] public section

open Kraken (Layout WellFormedLayout)

@[kstep] def Effects.All [Labels] (post : MachineState → Prop) : Effects → Prop
  | .done a => post a
  | .unimplemented _ => False
  | .resolve_label lbl k =>
    match label? lbl with
    | .some a => (k a).All post
    | .none => False
  | .unaligned_sp .. => False
  | .nonmem_load .. => False
  | .nonmem_store .. => False
  | @Effects.undefined α _ cont => ∀ v: α, (cont v).All post
  | .require_read_access _ _ cont => (cont ()).All post
  | .require_write_access _ _ cont => (cont ()).All post
  | .require_exec_access _ cont => (cont ()).All post

@[ksimp] theorem Effects.All_resolve_label [Labels] (lbl : Label) (k : Int64 → Effects)
    (post : MachineState → Prop) :
    (Effects.resolve_label lbl k).All post =
      (match label? lbl with | .some a => (k a).All post | .none => False) := by
  rw [Effects.All]

def step1 (e : Executable) (s : MachineState) (post : @Post MachineState) : Prop :=
  letI := e.labels
  (Executable.step e s .done).All post

/- More general version of `step_at` theorem which does not constrain the shape of the postcondition. -/
theorem eventually_of_interp {p : Program} [l : WellFormedLayout p]
    {k : Nat} {d : Directive} (hd : p[k]? = some d) {post : @Post MachineState} {s : MachineData}
    (h : letI := Executable.labels p.toExecutable
      (d.interp s
        ⟨p.toExecutable.addrOf k, p.toExecutable.addrOf (k + 1)⟩
        (fun s' => .done ⟨s', p.toExecutable.addrOf (k + 1)⟩)
        (fun a s' => .done ⟨s', a⟩)).All post) :
    Eventually (step1 p.toExecutable) post ⟨s, p.toExecutable.addrOf k⟩ := by
  have hc : p.toExecutable.program[k]? = some {directive := d, size := l.size k} := by
    simp [Kraken.Layout.apply_getElem?, hd]
  have hsucc := p.toExecutable.addrOf_succ hc
  letI : Labels := Executable.labels p.toExecutable
  match hsize : l.size k with
  | 0 =>
    apply Eventually.done
    simpa [hsucc, hsize, inert_of_size_zero hd hsize, Effects.All] using h
  | _ + 1 =>
    refine .step _ post ?_ fun _ => .done _
    obtain ⟨pre, hat, hpre⟩ := Kraken.Program.directivesAtAddress_addrOf p hd (by grind only)
    have hmem := fun c (hc : c ∈ pre) => Kraken.Program.mem_of_zeroSizePrefix hat hpre hc
    unfold step1 Executable.step
    dsimp only
    rw [hat]
    clear hat hpre
    induction pre with
    | nil => simpa [Directives.interp, hsucc, hsize] using h
    | cons c pre ih =>
      obtain ⟨m, d', hd', rfl, hz0⟩ := hmem c List.mem_cons_self
      simp only [List.cons_append, Directives.interp, Int64.reduceOfNat, Int64.add_zero,
        inert_of_size_zero hd' hz0]
      exact ih fun c' hc' => hmem c' (List.mem_cons_of_mem _ hc')

/- This theorem is meant to be used when the user is doing a proof over `Eventually` and wants to keep the
   state of the goal as an `Eventually` -/
theorem step_at {p : Program} [WellFormedLayout p] {k : Nat} {d : Directive}
    (hd : p[k]? = some d) {post : @Post MachineState} {s : MachineData}
    (h : letI := Executable.labels p.toExecutable
      (d.interp s
        ⟨p.toExecutable.addrOf k, p.toExecutable.addrOf (k + 1)⟩
        (fun s' => .done ⟨s', p.toExecutable.addrOf (k + 1)⟩)
        (fun a s' => .done ⟨s', a⟩)).All (Eventually (step1 p.toExecutable) post)) :
    Eventually (step1 p.toExecutable) post ⟨s, p.toExecutable.addrOf k⟩ :=
  eventually_trans _ _ _ _ (eventually_of_interp hd h) fun _ => id

theorem label?_eq_some_addrOf {p : Program} [l : Layout p] {lbl : Label} {k : Nat}
    (hk : p.findIdx? (·.isLabel lbl) = some k) :
    @Labels.label? (Executable.labels p.toExecutable) lbl = some (p.toExecutable.addrOf k) :=
  Kraken.Layout.withAddresses_findSome?_label p lbl hk
