module

/-
Omnisemantics for AArch64.
-/

public import Kraken.AArch64.Semantics
import Kraken.Attribute
public import Kraken.OmniSemantics

@[expose] public section

open Kraken (Layout)

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

theorem Directives.interp_directivesAtAddress_of_zeroSizePrefix
    {p : Program} {l : Layout} {pc : Int64} {rest : List (Kraken.Sized Directive)}
    (h : Kraken.ZeroSizePrefix ((l.apply p).directivesAtAddress pc) rest)
    (s : MachineData) (ret : Int64 → MachineData → Effects) :
    Directives.interp ((l.apply p).directivesAtAddress pc) s pc ret =
      Directives.interp rest s pc ret := by
  obtain ⟨pre, hpre, hz⟩ := h
  rw [hpre]
  have hmem := fun c (hc : c ∈ pre) => Kraken.Program.mem_of_zeroSizePrefix hpre hz hc
  clear hpre hz
  induction pre generalizing s with
  | nil => rfl
  | cons c pre ih =>
    obtain ⟨m, d', hd', rfl, hz0⟩ := hmem c List.mem_cons_self
    simp only [List.cons_append, Directives.interp, Int64.reduceOfNat, Int64.add_zero,
      inert_of_size_zero hd' hz0]
    exact ih s (fun c' hc' => hmem c' (List.mem_cons_of_mem _ hc'))

/- More general version of `step_at` theorem which does not constrain the shape of the postcondition. -/
theorem eventually_of_interp {p : Program} {l : Layout} (hl : p.AssemblableWith l)
    {k : Nat} {d : Directive} (hd : p[k]? = some d) {post : @Post MachineState} {s : MachineData}
    (h : letI := Executable.labels (l.apply p)
      (d.interp s
        ⟨(l.apply p).addrOf k, (l.apply p).addrOf (k + 1)⟩
        (fun s' => .done ⟨s', (l.apply p).addrOf (k + 1)⟩)
        (fun a s' => .done ⟨s', a⟩)).All post) :
    Eventually (step1 (l.apply p)) post ⟨s, (l.apply p).addrOf k⟩ := by
  have hc : (l.apply p).program[k]? = some {directive := d, size := l.dirSize p k} := by
    simp [Kraken.Layout.apply_getElem?, hd]
  have hsucc := (l.apply p).addrOf_succ hc
  letI : Labels := Executable.labels (l.apply p)
  match hsize : l.dirSize p k with
  | 0 =>
    apply Eventually.done
    simpa [hsucc, hsize, inert_of_size_zero hd hsize, Effects.All] using h
  | _ + 1 =>
    refine .step _ post ?_ fun _ => .done _
    unfold step1 Executable.step
    dsimp only
    rw [Directives.interp_directivesAtAddress_of_zeroSizePrefix
      (Kraken.Program.directivesAtAddress_addrOf hl hd (by grind only))]
    simpa [Directives.interp, hsucc, hsize] using h

/- This theorem is meant to be used when the user is doing a proof over `Eventually` and wants to keep the
   state of the goal as an `Eventually` -/
theorem step_at {p : Program} {l : Layout} [hl : p.AssemblableWith l] {k : Nat} {d : Directive}
    (hd : p[k]? = some d) {post : @Post MachineState} {s : MachineData}
    (h : letI := Executable.labels (l.apply p)
      (d.interp s
        ⟨(l.apply p).addrOf k, (l.apply p).addrOf (k + 1)⟩
        (fun s' => .done ⟨s', (l.apply p).addrOf (k + 1)⟩)
        (fun a s' => .done ⟨s', a⟩)).All (Eventually (step1 (l.apply p)) post)) :
    Eventually (step1 (l.apply p)) post ⟨s, (l.apply p).addrOf k⟩ :=
  eventually_trans _ _ _ _ (eventually_of_interp hl hd h) fun _ => id

theorem label?_eq_some_addrOf {p : Program} {l : Layout} {lbl : Label} {k : Nat}
    (hk : p.findIdx? (·.isLabel lbl) = some k) :
    @Labels.label? (Executable.labels (l.apply p)) lbl = some ((l.apply p).addrOf k) :=
  Kraken.Layout.withAddresses_findSome?_label p l lbl hk
