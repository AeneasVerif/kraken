module

/-
Omnisemantics for x64.
-/

import Kraken.Attribute
public import Kraken.OmniSemantics
public import Kraken.X64.Semantics

@[expose] public section

@[kstep] def Effects.All (post : MachineState → Prop) : Effects → Prop
  | .done a => post a
  | .unimplemented _ => False
  | .gp_unaligned .. => False
  | .nonmem_load .. => False
  | .nonmem_store .. => False
  | @Effects.undefined α _ cont => ∀ v: α, (cont v).All post
  | .require_read_access _ cont => (cont ()).All post
  | .require_write_access _ cont => (cont ()).All post
  | .require_exec_access _ cont => (cont ()).All post

@[ksimp] theorem Effects.All_require_read_access (addr : BitVec 64) (bytes : UInt64)
    (ok : Unit → Effects) (post : MachineState → Prop) :
    (require_access require_read_access addr bytes ok).All post = (ok ()).All post := by
  dsimp only [require_access]
  split <;> rfl

@[ksimp] theorem Effects.All_require_write_access (addr : BitVec 64) (bytes : UInt64)
    (ok : Unit → Effects) (post : MachineState → Prop) :
    (require_access require_write_access addr bytes ok).All post = (ok ()).All post := by
  dsimp only [require_access]
  split <;> rfl

def step1 (e : Executable) (s : MachineState) (post : @Post MachineState) : Prop :=
  (Executable.step e s .done).All post

theorem eventually_of_interp {p : Program} [l : Layout p]
    (hinj : ∀ j k, p.toExecutable.addrOf j = p.toExecutable.addrOf k →
      p.toExecutable.sizeBefore j = p.toExecutable.sizeBefore k)
    {k : Nat} {d : Directive} (hd : p[k]? = some d) {post : @Post MachineState} {s : MachineData}
    (h : (@Directive.interp (Executable.labels p.toExecutable) d s
      ⟨p.toExecutable.addrOf k, p.toExecutable.addrOf (k + 1)⟩
      (fun s' => .done ⟨s', p.toExecutable.addrOf (k + 1)⟩)
      (fun a s' => .done ⟨s', a⟩)).All post) :
    Eventually (step1 p.toExecutable) post ⟨s, p.toExecutable.addrOf k⟩ := by
  have hc : p.toExecutable.program[k]? = some {directive := d, size := l.size d k} := by
    simp [Kraken.Layout.apply_getElem?, hd]
  have hsucc := p.toExecutable.addrOf_succ hc
  letI : Labels := Executable.labels p.toExecutable
  rcases Nat.eq_zero_or_pos (l.size d k) with h0 | hz
  · rw [inert_of_size_zero h0, hsucc, h0] at h
    simpa [Effects.All] using Eventually.done _ h
  · refine .step _ post ?_ fun _ => .done _
    obtain ⟨pre, hat, hpre⟩ := p.toExecutable.directivesAtAddress_addrOf hinj hc hz
    unfold step1 Executable.step
    dsimp only
    rw [hat]
    clear hat
    induction pre with
    | nil => simpa [Directives.interp, hsucc] using h
    | cons c pre ih =>
      obtain ⟨hmem, hz0⟩ := hpre c List.mem_cons_self
      obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp hmem
      obtain ⟨d', _, rfl⟩ := Option.map_eq_some_iff.mp (Kraken.Layout.apply_getElem? p m ▸ hm)
      have hz0' : l.size d' m = 0 := hz0
      simp only [hz0', List.cons_append, Directives.interp, Int64.reduceOfNat, Int64.add_zero,
        inert_of_size_zero hz0']
      exact ih fun c' hc' => hpre c' (List.mem_cons_of_mem _ hc')

@[ksimp] theorem Int64.add_sub_cancel_left (a b : Int64) : a + (b - a) = b := by grind
@[ksimp] theorem Int64.ofBitVec_toBitVec_ksimp (a : Int64) : Int64.ofBitVec a.toBitVec = a :=
  Int64.ofBitVec_toBitVec a

theorem step_at {p : Program} [nw : WellFormedLayout p] {k : Nat} {d : Directive}
    (hd : p[k]? = some d) {post : @Post MachineState} {s : MachineData}
    (h : (@Directive.interp (Executable.labels p.toExecutable) d s
      ⟨p.toExecutable.addrOf k, p.toExecutable.addrOf (k + 1)⟩
      (fun s' => .done ⟨s', p.toExecutable.addrOf (k + 1)⟩)
      (fun a s' => .done ⟨s', a⟩)).All (Eventually (step1 p.toExecutable) post)) :
    Eventually (step1 p.toExecutable) post ⟨s, p.toExecutable.addrOf k⟩ :=
  eventually_trans _ _ _ _
    (eventually_of_interp (fun _ _ => Kraken.Program.sizeBefore_eq_of_addrOf_eq p) hd h) fun _ => id

theorem label_eq_addrOf {p : Program} [l : Layout p] {lbl : Label} {k : Nat}
    (hk : p.findIdx? (·.isLabel lbl) = some k) :
    @Labels.label (Executable.labels p.toExecutable) lbl = p.toExecutable.addrOf k :=
  Kraken.Layout.withAddresses_findSome?_label p lbl hk

theorem step_label {p : Program} [l : Layout p] {lbl : Label} {k : Nat}
    (hk : p.findIdx? (·.isLabel lbl) = some k) {post : @Post MachineState} {s : MachineData}
    (h : Eventually (step1 p.toExecutable) post ⟨s, p.toExecutable.addrOf k⟩) :
    Eventually (step1 p.toExecutable) post ⟨s, @Labels.label (Executable.labels p.toExecutable) lbl⟩ := by
  rwa [label_eq_addrOf hk]
