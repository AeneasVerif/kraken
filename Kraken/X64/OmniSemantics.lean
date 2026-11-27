module

/-
Omnisemantics for x64.
-/

import Kraken.Attribute
public import Kraken.OmniSemantics
public import Kraken.X64.Semantics

@[expose] public section

open Kraken (Layout)

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

theorem Effects.All_storeAvx {s : MachineData} {addr : BitVec 64} {w : AvxWidth}
    {v : w.type} {i : Int} {ret : MachineData → Effects} {post : MachineState → Prop}
    {checkAlign : Bool} (ha : checkAlign → isAligned w.bytes addr)
    (h : Mem.loadInt s.dmem addr w.bytes = some i)
    (hk : (ret { s with dmem := Mem.storeInt s.dmem addr w.bytes v.toInt }).All post) :
    (s.storeAvx addr v ret checkAlign).All post := by
  unfold MachineData.storeAvx
  split
  · cases checkAlign <;> simp_all
  rw [Effects.All_require_write_access]
  simp only [h]
  exact hk

theorem Effects.All_loadAvx {s : MachineData} {addr : BitVec 64} {w : AvxWidth} {i : Int}
    {ret : w.type → MachineData → Effects} {post : MachineState → Prop} {checkAlign : Bool}
    (ha : checkAlign → isAligned w.bytes addr)
    (h : Mem.loadInt s.dmem addr w.bytes = some i)
    (hk : (ret (.ofInt _ i) s).All post) :
    (s.loadAvx addr w ret checkAlign).All post := by
  unfold MachineData.loadAvx
  split
  · cases checkAlign <;> simp_all
  rw [Effects.All_require_read_access]
  simp only [h]
  exact hk

section
variable [L : Labels]

def step1 (e : Executable) (s : MachineState) (post : @Post MachineState) : Prop :=
  letI := L.update e
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

theorem eventually_of_interp {p : Program} {l : Layout} (hl : p.AssemblableWith l)
    {k : Nat} {d : Directive} (hd : p[k]? = some d) {post : @Post MachineState} {s : MachineData}
    (h : letI := L.update (l.apply p)
      (d.interp s
        ⟨(l.apply p).addrOf k, (l.apply p).addrOf (k + 1)⟩
        (fun s' => .done ⟨s', (l.apply p).addrOf (k + 1)⟩)
        (fun a s' => .done ⟨s', a⟩)).All post) :
    Eventually (step1 (l.apply p)) post ⟨s, (l.apply p).addrOf k⟩ := by
  have hc : (l.apply p).program[k]? = some {directive := d, size := l.dirSize p k} := by
    simp [Kraken.Layout.apply_getElem?, hd]
  have hsucc := (l.apply p).addrOf_succ hc
  letI : Labels := L.update (l.apply p)
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

@[ksimp] theorem Int64.add_sub_cancel_left (a b : Int64) : a + (b - a) = b := by grind
@[ksimp] theorem Int64.ofBitVec_toBitVec_ksimp (a : Int64) : Int64.ofBitVec a.toBitVec = a :=
  Int64.ofBitVec_toBitVec a

theorem step_at {p : Program} {l : Layout} [hl : p.AssemblableWith l] {k : Nat} {d : Directive}
    (hd : p[k]? = some d) {post : @Post MachineState} {s : MachineData}
    (h : letI := L.update (l.apply p)
      (d.interp s
        ⟨(l.apply p).addrOf k, (l.apply p).addrOf (k + 1)⟩
        (fun s' => .done ⟨s', (l.apply p).addrOf (k + 1)⟩)
        (fun a s' => .done ⟨s', a⟩)).All (Eventually (step1 (L := L) (l.apply p)) post)) :
    Eventually (step1 (L := L) (l.apply p)) post ⟨s, (l.apply p).addrOf k⟩ :=
  eventually_trans _ _ _ _ (eventually_of_interp hl hd h) fun _ => id

end

theorem label_update_eq_addrOf {p : Program} {l : Layout} {L : Labels} {lbl : Label} {k : Nat}
    (hk : p.findIdx? (·.isLabel lbl) = some k) :
    (L.update (l.apply p)).label lbl = (l.apply p).addrOf k := by
  change (Executable.label? (l.apply p) lbl).getD (L.label lbl) = _
  unfold Executable.label?
  rw [Kraken.Layout.withAddresses_findSome?_label p l lbl hk]
  rfl

theorem Labels.update_idem (L : Labels) (e : Executable) :
    (L.update e).update e = L.update e := by
  ext lbl
  change (Executable.label? e lbl).getD ((Executable.label? e lbl).getD (L.label lbl)) =
    (Executable.label? e lbl).getD (L.label lbl)
  cases Executable.label? e lbl <;> rfl

theorem label?_eq_some_mem {p : Program} {layout : Layout} {l : Label} {a : Int64}
    (h : Executable.label? (layout.apply p) l = some a) : l ∈ Kraken.Program.labels p := by
  obtain ⟨x, hx, hfx⟩ := List.exists_of_findSome?_eq_some h
  have hd : x.directive = .label l := by rcases x with ⟨d, _, _⟩; dsimp only at hfx; split at hfx <;> simp_all
  have hmem : Kraken.Directive.label l ∈ p :=
    Kraken.Program.map_directive_withAddresses p layout ▸ hd ▸ List.mem_map_of_mem (f := (·.directive)) hx
  exact List.mem_filterMap.mpr ⟨.label l, hmem, rfl⟩

theorem Labels.update_append_left (p₁ p₂ : Program) (l : Layout) (L : Labels) :
    (L.update ((l.offset p₁).apply p₂)).update (l.apply p₁) = L.update (l.apply (p₁ ++ p₂)) := by
  ext lbl
  change (Executable.label? (l.apply p₁) lbl).getD
      ((Executable.label? ((l.offset p₁).apply p₂) lbl).getD (L.label lbl)) =
    (Executable.label? (l.apply (p₁ ++ p₂)) lbl).getD (L.label lbl)
  unfold Executable.label?
  rw [Kraken.Program.apply_append_withAddresses p₁ p₂ l, List.findSome?_append]
  cases List.findSome? _ (l.apply p₁).withAddresses <;> rfl

theorem Labels.update_append_right {p₁ p₂ : Program} {l : Layout}
    (hl : Kraken.Program.AssemblableWith (p₁ ++ p₂) l) (L : Labels) :
    (L.update (l.apply p₁)).update ((l.offset p₁).apply p₂) = L.update (l.apply (p₁ ++ p₂)) := by
  ext lbl
  change (Executable.label? ((l.offset p₁).apply p₂) lbl).getD
      ((Executable.label? (l.apply p₁) lbl).getD (L.label lbl)) =
    (Executable.label? (l.apply (p₁ ++ p₂)) lbl).getD (L.label lbl)
  unfold Executable.label?
  rw [Kraken.Program.apply_append_withAddresses p₁ p₂ l, List.findSome?_append]
  cases h₁ : List.findSome? _ (l.apply p₁).withAddresses with
  | none => rfl
  | some a₁ =>
    cases h₂ : List.findSome? _ ((l.offset p₁).apply p₂).withAddresses with
    | none => rfl
    | some a₂ =>
      have hmem₁ : lbl ∈ Kraken.Program.labels p₁ := label?_eq_some_mem h₁
      have hmem₂ : lbl ∈ Kraken.Program.labels p₂ := label?_eq_some_mem h₂
      have hnodup : (Kraken.Program.labels p₁ ++ Kraken.Program.labels p₂).Nodup := by
        simpa [Kraken.Program.labels, List.filterMap_append] using hl.unique_labels
      exact absurd rfl ((List.nodup_append.mp hnodup).2.2 lbl hmem₁ lbl hmem₂)

theorem Eventually.mono_of_zeroSizePrefix {p q : Program} {lp lq : Layout} {Lp Lq : Labels}
    (hlabels : Lp.update (lp.apply p) = Lq.update (lq.apply q))
    (hdirs : ∀ pc, Kraken.Program.ContainsAddr p lp pc →
      Kraken.ZeroSizePrefix ((lq.apply q).directivesAtAddress pc)
        ((lp.apply p).directivesAtAddress pc))
    {post : MachineState → Prop} {init : MachineState}
    (h : Eventually (step1 (L := Lp) (lp.apply p)) post init) :
    Eventually (step1 (L := Lq) (lq.apply q)) post init := by
  induction h with
  | done s hp => exact .done s hp
  | step s mid_p hstep _ ih =>
    by_cases hpc : Kraken.Program.ContainsAddr p lp s.pc
    · refine .step s mid_p ?_ ih
      dsimp only [step1, Executable.step] at hstep ⊢
      rw [← hlabels]
      letI := Lp.update (lp.apply p)
      rw [Directives.interp_directivesAtAddress_of_zeroSizePrefix (hdirs s.pc hpc)]
      exact hstep
    · have hall0 : Kraken.ZeroSizePrefix ((lp.apply p).directivesAtAddress s.pc) [] :=
        ⟨(lp.apply p).directivesAtAddress s.pc, by simp,
          fun c hc => Classical.byContradiction fun hz =>
            hpc (Kraken.Program.containsAddr_of_mem_directivesAtAddress p lp hc (Nat.pos_of_ne_zero hz))⟩
      dsimp only [step1, Executable.step] at hstep
      letI := Lp.update (lp.apply p)
      rw [Directives.interp_directivesAtAddress_of_zeroSizePrefix hall0,
          Directives.interp, Effects.All] at hstep
      exact ih ⟨s.data, s.pc⟩ hstep

theorem Eventually.append_left {p₁ p₂ : Program} {l : Layout} [L : Labels]
    (hl : Kraken.Program.AssemblableWith (p₁ ++ p₂) l)
    {post : MachineState → Prop} {init : MachineState}
    (h : letI := L.update ((l.offset p₁).apply p₂)
         Eventually (step1 (l.apply p₁)) post init) :
    Eventually (step1 (l.apply (p₁ ++ p₂))) post init :=
  Eventually.mono_of_zeroSizePrefix (Labels.update_append_left p₁ p₂ l L)
    (fun pc hpc => ⟨[], by simp [Kraken.Program.directivesAtAddress_append_left hl pc hpc], by simp⟩) h

theorem Eventually.append_right {p₁ p₂ : Program} {l : Layout} [L : Labels]
    (hl : Kraken.Program.AssemblableWith (p₁ ++ p₂) l)
    {post : MachineState → Prop} {init : MachineState}
    (h : letI := L.update (l.apply p₁)
         Eventually (step1 ((l.offset p₁).apply p₂)) post init) :
    Eventually (step1 (l.apply (p₁ ++ p₂))) post init :=
  Eventually.mono_of_zeroSizePrefix (Labels.update_append_right hl L)
    (Kraken.Program.directivesAtAddress_append_right hl) h


/-
theorem Directives.mono {L₁ L₂ : Labels} (hL : L₁ ⊆ L₂)
  {ret₁ ret₂ : MachineState → Effects }  (hret : ∀ ms, (ret₁ ms).CompatibleWith (ret₂ ms))
  {ds : List (Sized Directive)} :
    ()
-/
