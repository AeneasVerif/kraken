module

/-
Omnisemantics for AArch64.
-/

public import Kraken.AArch64.Semantics
import Kraken.Attribute
public import Kraken.OmniSemantics

@[expose] public section

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

def step1 (e : Executable) (s : MachineState) (post : @Post MachineState) : Prop :=
  (Executable.step e s .done).All post

private theorem interp_size_zero [l : Layout] [Labels] {i : Nat} {d : Directive}
    (hz : l.size d i = 0) (s : MachineData) (rng : Std.Rco Int64)
    (next : MachineData → Effects) (jmp : Int64 → MachineData → Effects) :
    d.interp s rng next jmp = next s := by
  cases d with
  | instr inst => exact absurd hz (Nat.ne_of_gt (l.instrSize inst i).property)
  | label _ => rfl
  | byteArray bs => simp [Directive.interp, ByteArray.isEmpty, show bs.size = 0 from hz]

theorem eventually_of_interp [l : Layout] {p : Program}
    (hinj : ∀ j k, (l p).addrOf j = (l p).addrOf k → (l p).sizeBefore j = (l p).sizeBefore k)
    {k : Nat} {d : Directive} (hd : p[k]? = some d) {post : @Post MachineState} {s : MachineData}
    (h : (@Directive.interp (Executable.labels (l p)) d s
      ⟨(l p).addrOf k, (l p).addrOf (k + 1)⟩
      (fun s' => .done ⟨s', (l p).addrOf (k + 1)⟩)
      (fun a s' => .done ⟨s', a⟩)).All post) :
    Eventually (step1 (l p)) post ⟨s, (l p).addrOf k⟩ := by
  have hc : (l p).program[k]? = some {directive := d, size := l.size d k} := by
    simp [l.apply_getElem?, hd]
  have hsucc := (l p).addrOf_succ hc
  letI : Labels := Executable.labels (l p)
  rcases Nat.eq_zero_or_pos (l.size d k) with h0 | hz
  · rw [interp_size_zero h0, hsucc, h0] at h
    simpa [Effects.All] using Eventually.done _ h
  · refine .step _ post ?_ fun _ => .done _
    obtain ⟨pre, hat, hpre⟩ := (l p).directivesAtAddress_addrOf hinj hc hz
    unfold step1 Executable.step
    dsimp only
    rw [hat]
    clear hat
    induction pre with
    | nil => simpa [Directives.interp, hsucc] using h
    | cons c pre ih =>
      obtain ⟨hmem, hz0⟩ := hpre c List.mem_cons_self
      obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp hmem
      obtain ⟨d', _, rfl⟩ := Option.map_eq_some_iff.mp (l.apply_getElem? p m ▸ hm)
      have hz0' : l.size d' m = 0 := hz0
      simp only [hz0', List.cons_append, Directives.interp, Int64.reduceOfNat, Int64.add_zero,
        interp_size_zero hz0']
      exact ih fun c' hc' => hpre c' (List.mem_cons_of_mem _ hc')

theorem step_at [l : Layout] {p : Program} [nw : l.NoWrap p] {k : Nat} {d : Directive}
    (hd : p[k]? = some d) {post : @Post MachineState} {s : MachineData}
    (h : (@Directive.interp (Executable.labels (l p)) d s
      ⟨(l p).addrOf k, (l p).addrOf (k + 1)⟩
      (fun s' => .done ⟨s', (l p).addrOf (k + 1)⟩)
      (fun a s' => .done ⟨s', a⟩)).All (Eventually (step1 (l p)) post)) :
    Eventually (step1 (l p)) post ⟨s, (l p).addrOf k⟩ :=
  eventually_trans _ _ _ _
    (eventually_of_interp (fun _ _ => nw.sizeBefore_eq_of_addrOf_eq) hd h) fun _ => id

theorem label_eq_addrOf [l : Layout] {p : Program} {lbl : Label} {k : Nat}
    (hk : p.findIdx? (·.isLabel lbl) = some k) :
    @Labels.label (Executable.labels (l p)) lbl = (l p).addrOf k :=
  l.withAddresses_findSome?_label p lbl hk

theorem step_label [l : Layout] {p : Program} {lbl : Label} {k : Nat}
    (hk : p.findIdx? (·.isLabel lbl) = some k) {post : @Post MachineState} {s : MachineData}
    (h : Eventually (step1 (l p)) post ⟨s, (l p).addrOf k⟩) :
    Eventually (step1 (l p)) post ⟨s, @Labels.label (Executable.labels (l p)) lbl⟩ := by
  rwa [label_eq_addrOf hk]
