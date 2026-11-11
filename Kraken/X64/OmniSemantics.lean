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
  | .unresolved_label _ => False
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

private theorem Directives.interp_size_zero_append {p : Program} [l : Layout p] [Labels]
    {pre rest : List (Kraken.Sized Directive)}
    (hpre : ∀ c ∈ pre, c ∈ p.toExecutable.program ∧ c.size = 0)
    (s : MachineData) (pc : Int64) (ret : Int64 → MachineData → Effects) :
    Directives.interp (pre ++ rest) s pc ret = Directives.interp rest s pc ret := by
  induction pre generalizing s with
  | nil => rfl
  | cons c pre ih =>
    obtain ⟨hmem, hz0⟩ := hpre c List.mem_cons_self
    obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp hmem
    obtain ⟨d', _, rfl⟩ := Option.map_eq_some_iff.mp (Kraken.Layout.apply_getElem? p m ▸ hm)
    have hz0' : l.size d' m = 0 := hz0
    simp only [hz0', List.cons_append, Directives.interp, Int64.reduceOfNat, Int64.add_zero,
      inert_of_size_zero hz0']
    exact ih (fun c' hc' => hpre c' (List.mem_cons_of_mem _ hc')) s

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
    rw [hat, Directives.interp_size_zero_append hpre]
    simpa [Directives.interp, hsucc] using h

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

theorem label?_eq_some_addrOf {p : Program} [l : Layout p] {lbl : Label} {k : Nat}
    (hk : p.findIdx? (·.isLabel lbl) = some k) :
    @Labels.label? (Executable.labels (Kraken.Layout.apply p l)) lbl =
      some ((Kraken.Layout.apply p l).addrOf k) :=
  Kraken.Layout.withAddresses_findSome?_label p lbl hk

/-- `L₁ ⊆ L₂` means every label resolved by `L₁` resolves to the same address in `L₂`. -/
instance : HasSubset Labels where
  Subset L₁ L₂ := ∀ l a, L₁.label? l = some a → L₂.label? l = some a

section LabelsMono

private def Effects.Le (e₁ e₂ : Effects) : Prop :=
  ∀ (post : MachineState → Prop), e₁.All post → e₂.All post

private theorem load_le {s : MachineData} {addr : BitVec 64} {w : Width}
    {r₁ r₂ : w.type → MachineData → Effects} (hr : ∀ v s', (r₁ v s').Le (r₂ v s')) :
    (s.load addr w r₁).Le (s.load addr w r₂) := by
  intro post; simp only [MachineData.load, Effects.All_require_read_access]
  cases Mem.loadInt s.dmem addr w.bytes with | some _ => exact hr _ _ post | none => exact False.elim

private theorem loadAvx_le {s : MachineData} {addr : BitVec 64} {w : AvxWidth} {ca : Bool}
    {r₁ r₂ : w.type → MachineData → Effects} (hr : ∀ v s', (r₁ v s').Le (r₂ v s')) :
    (s.loadAvx addr w r₁ ca).Le (s.loadAvx addr w r₂ ca) := by
  intro post; dsimp only [MachineData.loadAvx]; split
  · exact id
  · simp only [Effects.All_require_read_access]
    cases Mem.loadInt s.dmem addr w.bytes with | some _ => exact hr _ _ post | none => exact False.elim

private theorem store_le {s : MachineData} {addr : BitVec 64} {w : Width} {v : w.type}
    {r₁ r₂ : MachineData → Effects} (hr : ∀ s', (r₁ s').Le (r₂ s')) :
    (s.store addr v r₁).Le (s.store addr v r₂) := by
  intro post; simp only [MachineData.store, Effects.All_require_write_access]
  cases Mem.loadInt s.dmem addr w.bytes with | some _ => exact hr _ post | none => exact False.elim

private theorem storeAvx_le {s : MachineData} {addr : BitVec 64} {w : AvxWidth} {v : w.type} {ca : Bool}
    {r₁ r₂ : MachineData → Effects} (hr : ∀ s', (r₁ s').Le (r₂ s')) :
    (s.storeAvx addr v r₁ ca).Le (s.storeAvx addr v r₂ ca) := by
  intro post; dsimp only [MachineData.storeAvx]; split
  · exact id
  · simp only [Effects.All_require_write_access]
    cases Mem.loadInt s.dmem addr w.bytes with | some _ => exact hr _ post | none => exact False.elim

private theorem undef_le {α : Type} [NondetSupportingType α] {r₁ r₂ : α → Effects}
    (hr : ∀ v, (r₁ v).Le (r₂ v)) : (@Effects.undefined α _ r₁).Le (@Effects.undefined α _ r₂) :=
  fun post h v => hr v post (h v)

private theorem ite_le {c : Prop} [Decidable c] {a₁ a₂ b₁ b₂ : Effects}
    (ha : a₁.Le a₂) (hb : b₁.Le b₂) : (if c then a₁ else b₁).Le (if c then a₂ else b₂) := by
  split <;> assumption

private theorem repeatString_le [AddressSize]
    {step : MachineData → (MachineData → Effects) → Effects}
    (hstep : ∀ s (r₁ r₂ : MachineData → Effects), (∀ s', (r₁ s').Le (r₂ s')) → (step s r₁).Le (step s r₂))
    (count : Nat) (s : MachineData) {r₁ r₂ : MachineData → Effects} (hr : ∀ s', (r₁ s').Le (r₂ s')) :
    (MachineData.repeatString step count s r₁).Le (MachineData.repeatString step count s r₂) := by
  induction count generalizing s with
  | zero => exact hr s
  | succ count ih => exact hstep s _ _ fun s' => ih (s'.stepString .rcx (-1))

private theorem repString_le [AddressSize]
    {step : MachineData → (MachineData → Effects) → Effects}
    (hstep : ∀ s (r₁ r₂ : MachineData → Effects), (∀ s', (r₁ s').Le (r₂ s')) → (step s r₁).Le (step s r₂))
    (rs : List Reg64) (s : MachineData) {r₁ r₂ : MachineData → Effects} (hr : ∀ s', (r₁ s').Le (r₂ s')) :
    (MachineData.repString step rs s r₁).Le (MachineData.repString step rs s r₂) := by
  dsimp only [MachineData.repString]
  split
  · exact undef_le fun _ => hr _
  · exact repeatString_le hstep _ s hr

variable {L₁ L₂ : Labels} (hL : L₁ ⊆ L₂)
include hL

private theorem label_le (l : Label) {r₁ r₂ : Int64 → Effects} (hr : ∀ a, (r₁ a).Le (r₂ a)) :
    (@label L₁ l r₁).Le (@label L₂ l r₂) := fun post => by
  dsimp only [label]; cases h : L₁.label? l with
  | none => exact False.elim
  | some a => rw [hL l a h]; exact hr a post

private theorem constExpr_le (e : ConstExpr) (p : Std.Rco Int64)
    {r₁ r₂ : Int64 → Effects} (hr : ∀ v, (r₁ v).Le (r₂ v)) :
    (@ConstExpr.interp L₁ e p r₁).Le (@ConstExpr.interp L₂ e p r₂) := by
  induction e generalizing r₁ r₂ with
  | label l => exact label_le hL l hr
  | add e1 e2 ih1 ih2 => exact ih1 fun v1 => ih2 fun v2 => hr (v1 + v2)
  | sub e1 e2 ih1 ih2 => exact ih1 fun v1 => ih2 fun v2 => hr (v1 - v2)
  | _ => exact hr _

private theorem shiftCount_le (c : ShiftCountExpr) (s : MachineData) (p : Std.Rco Int64)
    {r₁ r₂ : BitVec 8 → Effects} (hr : ∀ v, (r₁ v).Le (r₂ v)) :
    (@ShiftCountExpr.interp L₁ c s p r₁).Le (@ShiftCountExpr.interp L₂ c s p r₂) := by
  cases c with | cl => exact hr _ | imm8 v => exact constExpr_le hL v p fun _ => hr _

section Addr
variable [AddressSize]

private theorem regOrMem_le {w : Width} (o : RegOrMem w) (s : MachineData) (p : Std.Rco Int64)
    {r₁ r₂ : w.type → MachineData → Effects} (hr : ∀ v s', (r₁ v s').Le (r₂ v s')) :
    (@RegOrMem.interp w L₁ _ o s p r₁).Le (@RegOrMem.interp w L₂ _ o s p r₂) := by
  cases o with | reg _ => exact hr _ _ | mem a => exact constExpr_le hL a.disp p fun _ => load_le hr

private theorem avxRegOrMem_le {w : AvxWidth} (o : AvxRegOrMem w) (s : MachineData) (p : Std.Rco Int64)
    {ca : Bool} {r₁ r₂ : w.type → MachineData → Effects} (hr : ∀ v s', (r₁ v s').Le (r₂ v s')) :
    (@AvxRegOrMem.interp w L₁ _ o s p r₁ ca).Le (@AvxRegOrMem.interp w L₂ _ o s p r₂ ca) := by
  cases o with | avx _ => exact hr _ _ | mem a => exact constExpr_le hL a.disp p fun _ => loadAvx_le hr

private theorem set_le {w : Width} (s : MachineData) (d : Dst w) (v : w.type) (p : Std.Rco Int64)
    {r₁ r₂ : MachineData → Effects} (hr : ∀ s', (r₁ s').Le (r₂ s')) :
    (@MachineData.set w L₁ _ s d v p r₁).Le (@MachineData.set w L₂ _ s d v p r₂) := by
  cases d with | reg _ => exact hr _ | mem a => exact constExpr_le hL a.disp p fun _ => store_le hr

private theorem setAvx_le {w : AvxWidth} (s : MachineData) (d : AvxDst w) (v : w.type) (p : Std.Rco Int64)
    {ca : Bool} {r₁ r₂ : MachineData → Effects} (hr : ∀ s', (r₁ s').Le (r₂ s')) :
    (@MachineData.setAvx w L₁ _ s d v p r₁ ca).Le (@MachineData.setAvx w L₂ _ s d v p r₂ ca) := by
  cases d with | avx _ => exact hr _ | mem a => exact constExpr_le hL a.disp p fun _ => storeAvx_le hr

private theorem setAvxLegacy_le {w : AvxWidth} (s : MachineData) (d : AvxDst w) (v : w.type) (p : Std.Rco Int64)
    {ca : Bool} {r₁ r₂ : MachineData → Effects} (hr : ∀ s', (r₁ s').Le (r₂ s')) :
    (@MachineData.setAvxLegacy w L₁ _ s d v p r₁ ca).Le (@MachineData.setAvxLegacy w L₂ _ s d v p r₂ ca) := by
  cases d with | avx _ => exact hr _ | mem a => exact constExpr_le hL a.disp p fun _ => storeAvx_le hr

private theorem operand_le {w : Width} (o : Operand w) (s : MachineData) (p : Std.Rco Int64)
    {r₁ r₂ : w.type → MachineData → Effects} (hr : ∀ v s', (r₁ v s').Le (r₂ v s')) :
    (@Operand.interp w L₁ _ o s p r₁).Le (@Operand.interp w L₂ _ o s p r₂) := by
  cases o with | regOrMem rm => exact regOrMem_le hL rm s p hr | imm v => exact constExpr_le hL v p fun _ => hr _ _

private theorem avxOperand_le {w : AvxWidth} (o : AvxOperand w) (s : MachineData) (p : Std.Rco Int64)
    {ca : Bool} {r₁ r₂ : w.type → MachineData → Effects} (hr : ∀ v s', (r₁ v s').Le (r₂ v s')) :
    (@AvxOperand.interp w L₁ _ o s p r₁ ca).Le (@AvxOperand.interp w L₂ _ o s p r₂ ca) := by
  cases o with | regOrMem rm => exact avxRegOrMem_le hL rm s p hr

private theorem relRegOrMem_le (o : RelRegOrMem) (s : MachineData) (p : Std.Rco Int64)
    {r₁ r₂ : BitVec 64 → MachineData → Effects} (hr : ∀ v s', (r₁ v s').Le (r₂ v s')) :
    (@RelRegOrMem.interp L₁ _ o s p r₁).Le (@RelRegOrMem.interp L₂ _ o s p r₂) := by
  cases o with
  | rel c => exact constExpr_le hL c p fun _ => hr _ _
  | reg _ => exact hr _ _
  | mem a => exact constExpr_le hL a.disp p fun _ => load_le hr

private theorem operation_le {w : Width} (op : Operation w) (p : Std.Rco Int64) (s : MachineData)
    {next₁ next₂ : MachineData → Effects} (hn : ∀ s', (next₁ s').Le (next₂ s'))
    (jmp : Int64 → MachineData → Effects) :
    (@Operation.interp L₁ _ w op p s next₁ jmp).Le (@Operation.interp L₂ _ w op p s next₂ jmp) := by
  cases op <;> dsimp only [Operation.interp, Reg.interp, AddrExpr.interp, ShiftCountExpr.interpMasked] <;>
    repeat (first
      | (with_reducible apply operand_le hL); intro _ _
      | (with_reducible apply regOrMem_le hL); intro _ _
      | (with_reducible apply constExpr_le hL); intro _
      | (with_reducible apply shiftCount_le hL); intro _
      | (with_reducible apply relRegOrMem_le hL); intro _ _
      | (with_reducible apply repString_le ?_ _ _ hn); intro _ _ _ hn
      | (with_reducible apply load_le); intro _ _
      | (with_reducible apply store_le); intro _
      | (with_reducible apply set_le hL); intro _
      | (with_reducible apply undef_le); intro _
      | (with_reducible apply label_le hL); intro _
      | (with_reducible apply ite_le)
      | split
      | exact hn _
      | exact fun _ h => h)

private theorem avxOperation_le {w : AvxWidth} (op : AvxOperation w) (p : Std.Rco Int64)
    (s : MachineData) {next₁ next₂ : MachineData → Effects} (hn : ∀ s', (next₁ s').Le (next₂ s')) :
    (@AvxOperation.interp L₁ _ w op p s next₁).Le (@AvxOperation.interp L₂ _ w op p s next₂) := by
  cases op <;> dsimp only [AvxOperation.interp] <;>
    repeat (first
      | (with_reducible apply avxOperand_le hL); intro _ _
      | (with_reducible apply avxRegOrMem_le hL); intro _ _
      | (with_reducible apply regOrMem_le hL); intro _ _
      | (with_reducible apply constExpr_le hL); intro _
      | (with_reducible apply set_le hL); intro _
      | (with_reducible apply setAvx_le hL); intro _
      | (with_reducible apply setAvxLegacy_le hL); intro _
      | exact hn _
      | exact fun _ h => h)

end Addr

private theorem directive_le (d : Directive) (s : MachineData) (p : Std.Rco Int64)
    {next₁ next₂ : MachineData → Effects} (hn : ∀ s', (next₁ s').Le (next₂ s'))
    (jmp : Int64 → MachineData → Effects) :
    (@Directive.interp L₁ d s p next₁ jmp).Le (@Directive.interp L₂ d s p next₂ jmp) := by
  match d with
  | .label _ => exact hn s
  | .byteArray _ =>
    dsimp only [Directive.interp]
    split
    · exact hn s
    · exact fun _ h => h
  | .word 0 _ => exact hn s
  | .word (_ + 1) _ => exact fun _ h => h
  | .instr (.regular addr_sz _ op) =>
    letI : AddressSize := ⟨addr_sz⟩; exact operation_le hL op p s hn jmp
  | .instr (.avx addr_sz _ op) =>
    letI : AddressSize := ⟨addr_sz⟩; exact avxOperation_le hL op p s hn

private theorem Directives.interp_mono_labels (ds : List (Kraken.Sized Directive))
    (s : MachineData) (pc : Int64) (ret : Int64 → MachineData → Effects) :
    (@Directives.interp L₁ ds s pc ret).Le (@Directives.interp L₂ ds s pc ret) := by
  induction ds generalizing s pc with
  | nil => exact fun _ h => h
  | cons d ds ih =>
    rcases d with ⟨d, sz⟩
    exact directive_le hL d s ⟨pc, pc + .ofNat sz⟩ (fun s' => ih s' (pc + .ofNat sz)) ret

end LabelsMono

private theorem label?_eq_some_mem {p : Program} [Kraken.Layout p] {l : Label} {a : Int64}
    (h : (Executable.labels p.toExecutable).label? l = some a) : l ∈ Kraken.Program.labels p := by
  obtain ⟨x, hx, hfx⟩ := List.exists_of_findSome?_eq_some h
  have hd : x.directive = .label l := by rcases x with ⟨d, _, _⟩; dsimp only at hfx; split at hfx <;> simp_all
  have hmem : Kraken.Directive.label l ∈ p :=
    Kraken.Program.map_directive_withAddresses p ▸ hd ▸ List.mem_map_of_mem (f := (·.directive)) hx
  exact List.mem_filterMap.mpr ⟨.label l, hmem, rfl⟩

private theorem labels_take_subset {p₁ p₂ : Program} [l : Kraken.Layout (p₁ ++ p₂)] :
    letI := l.take p₁
    Executable.labels p₁.toExecutable ⊆ Executable.labels (p₁ ++ p₂).toExecutable := by
  intro lbl a ha
  change (List.findSome? _ _) = some a at ha ⊢
  rw [Kraken.Program.toExecutable_append_withAddresses p₁ p₂, List.findSome?_append, ha]; rfl

variable (p₁ p₂ : Program) [layout : Kraken.WellFormedLayout (p₁ ++ p₂)]

private theorem labels_drop_subset :
    letI := layout.drop p₁
    Executable.labels p₂.toExecutable ⊆ Executable.labels (p₁ ++ p₂).toExecutable := by
  intro lbl a ha
  have hmem₂ : lbl ∈ Kraken.Program.labels p₂ := by
    letI := layout.toLayout.drop p₁; exact label?_eq_some_mem ha
  have happ := Kraken.Program.toExecutable_append_withAddresses p₁ p₂ (l := layout.toLayout)
  change List.findSome? _ _ = some a at ha ⊢
  rw [happ, List.findSome?_append]
  cases h₁ : List.findSome? _ (letI := layout.toLayout.take p₁; p₁.toExecutable).withAddresses with
  | none => exact ha
  | some _ =>
    have hmem₁ : lbl ∈ Kraken.Program.labels p₁ := by
      letI := layout.toLayout.take p₁; exact label?_eq_some_mem h₁
    have hnodup : (Kraken.Program.labels p₁ ++ Kraken.Program.labels p₂).Nodup := by
      simpa [Kraken.Program.labels, List.filterMap_append] using layout.unique_labels
    exact absurd rfl ((List.nodup_append.mp hnodup).2.2 lbl hmem₁ lbl hmem₂)

private theorem Eventually.lift_sub {p_sub p_full : Program}
    [l_sub : Layout p_sub] [l_full : Layout p_full]
    (hL : Executable.labels p_sub.toExecutable ⊆ Executable.labels p_full.toExecutable)
    (hat : ∀ pc, (∃ c ∈ p_sub.toExecutable.directivesAtAddress pc, 0 < c.size) →
      ∃ pre, p_full.toExecutable.directivesAtAddress pc = pre ++ p_sub.toExecutable.directivesAtAddress pc ∧
        ∀ c ∈ pre, c.size = 0)
    {post : MachineState → Prop} {init : MachineState}
    (h : Eventually (step1 p_sub.toExecutable) post init) :
    Eventually (step1 p_full.toExecutable) post init := by
  induction h with
  | done s hp => exact .done s hp
  | step s mid_p hstep _ ih =>
    by_cases hpos : ∃ c ∈ p_sub.toExecutable.directivesAtAddress s.pc, 0 < c.size
    · obtain ⟨pre, heq, hpre⟩ := hat s.pc hpos
      have hpre' : ∀ c ∈ pre, c ∈ p_full.toExecutable.program ∧ c.size = 0 := fun c hc => by
        obtain ⟨i, rfl, -⟩ := Kraken.Program.mem_directivesAtAddress p_full (heq ▸ List.mem_append_left _ hc)
        refine ⟨List.mem_iff_getElem?.mpr ⟨i, ?_⟩, hpre _ hc⟩
        simp [Kraken.Layout.apply_getElem?]
      refine .step s mid_p ?_ ih
      dsimp only [step1, Executable.step] at hstep ⊢
      letI := Executable.labels p_full.toExecutable
      rw [heq, Directives.interp_size_zero_append hpre']
      exact Directives.interp_mono_labels hL (p_sub.toExecutable.directivesAtAddress s.pc)
        s.data s.pc (fun pc s => .done ⟨s, pc⟩) mid_p hstep
    · have hall0 : ∀ c ∈ p_sub.toExecutable.directivesAtAddress s.pc, c ∈ p_sub.toExecutable.program ∧ c.size = 0 :=
        fun c hc => by
          have hz := Classical.byContradiction fun h => hpos ⟨c, hc, Nat.pos_of_ne_zero h⟩
          obtain ⟨i, rfl, -⟩ := Kraken.Program.mem_directivesAtAddress p_sub hc
          refine ⟨List.mem_iff_getElem?.mpr ⟨i, ?_⟩, hz⟩
          simp [Kraken.Layout.apply_getElem?]
      dsimp only [step1, Executable.step] at hstep
      letI := Executable.labels p_sub.toExecutable
      rw [← List.append_nil (p_sub.toExecutable.directivesAtAddress s.pc),
          Directives.interp_size_zero_append hall0,
          Directives.interp, Effects.All] at hstep
      exact ih ⟨s.data, s.pc⟩ hstep

theorem Eventually.prepend
  (post : MachineState → Prop) (init : MachineState)
  (h : letI := layout.drop p₁
       Eventually (step1 p₂.toExecutable) post init) :
    Eventually (step1 (p₁ ++ p₂).toExecutable) post init :=
  letI := layout.drop p₁
  Eventually.lift_sub (labels_drop_subset p₁ p₂)
    (Kraken.Program.directivesAtAddress_drop_eq p₁ p₂) h

theorem Eventually.append
  (post : MachineState → Prop) (init : MachineState)
  (h : letI := layout.take p₁
       Eventually (step1 p₁.toExecutable) post init) :
    Eventually (step1 (p₁ ++ p₂).toExecutable) post init :=
  letI := layout.take p₁
  Eventually.lift_sub (labels_take_subset (l := layout.toLayout))
    (fun pc hpos => ⟨[], by rw [List.nil_append]; exact Kraken.Program.directivesAtAddress_take_eq p₁ p₂ pc hpos, by simp⟩) h
