module

public import LeanQbe.Rega
public import LeanQbe.Wf
public import LeanQbe.AbiLemmas
import all Kraken.Separation

/-!
# Correctness of `Rega.lower`

`lower_correct`: if the source term `e₁ : Expr Val Cont` and the name term `e₂ : Expr Nat Nat` are
related by `Wf G D`, `lower` succeeds on `e₂` with code placed at index `k` of the host, and the
machine state agrees with the symbolic location file, then the source `wp` implies that the machine
eventually reaches the function's `FnSpec` postcondition. Generic in the `Target`.

The proof is one induction on `Wf` (plan section 2.2):

* `Agree G R s σ`: every entry of `R` holds the value `G` gives its name, in a register of `s` or in
  the spill slots `σ` of the frame.
* `Inv m s σ`: the frame invariant. The stack pointer is the entry one minus the frame, the
  callee-saved registers are unchanged since entry, and the memory is the source memory `m`, the
  slots `σ`, the frame overhead `Saved`, the stack left for callees, and the caller's frame `R`.
* A join point `ℓ` is instantiated with `LabJ G ℓ`: "label `ℓ` is at some index `k`, and from every
  state agreeing with `ℓ`'s entry map, the machine reaches the postcondition from `k`". The `label`
  case picks this `J` for the source's `∀ J`; the `block` case proves `J` closed under the block body
  at its own index; the `jump` case uses `J` after the checked moves.
* A `call` uses the callee's `FnSpec` (through `Target.call_fnspec`); a callee's exit becomes the
  function's own exit.
* No liveness, no dominance, no fixpoint: a wrong hint makes `lower` fail.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe
namespace Rega

open Std.ExtHashMap (sep_comm sep_assoc)

variable {T : Target}

/-! ## Agreement of the symbolic location file -/

/-- Location `l` holds `v` in registers `s` and slots `σ`. -/
def LocHolds (s : T.MData) (σ : List Val) : Loc T.toIsa → Val → Prop
  | .reg r, v => T.get s r = v
  | .slot i, v => σ[i]? = some v

/-- Every entry of `R` holds the value of its name (or its constant). -/
def Agree (G : List (Val × Nat)) (R : SymRegs T.toIsa) (s : T.MData) (σ : List Val) : Prop :=
  ∀ a l, (a, l) ∈ R → ∀ a₁, ArgRel G a₁ a → LocHolds s σ l a₁.val

theorem lookup_mem {I : Isa} {R : SymRegs I} {x : Nat} {r : I.Reg} (h : lookup R x = some r) :
    (.var x, .reg r) ∈ R := by
  unfold lookup at h
  obtain ⟨⟨a, l⟩, hp, hf⟩ := List.exists_of_findSome?_eq_some h
  by_cases ha : a = .var x
  · subst ha
    cases l with
    | reg r' => simp at hf; subst hf; exact hp
    | slot _ => simp at hf
  · simp [ha] at hf

theorem lookupLoc_mem {I : Isa} {R : SymRegs I} {x : Nat} {l : Loc I}
    (h : lookupLoc R x = some l) : (.var x, l) ∈ R := by
  unfold lookupLoc at h
  split at h
  · rename_i r hr; simp only [Option.some.injEq] at h; subst h; exact lookup_mem hr
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨a, l'⟩, hp, rfl⟩ := h
    have := List.mem_of_find?_eq_some hp
    have hx := List.find?_some hp
    simp only [beq_iff_eq] at hx
    subst hx; exact this

theorem Agree.reg {G : List (Val × Nat)} {R : SymRegs T.toIsa} {s : T.MData} {σ : List Val}
    (hA : Agree G R s σ) {a : Arg Nat} {r : T.Reg} (hm : (a, .reg r) ∈ R) {a₁ : Arg Val}
    (hr : ArgRel G a₁ a) : T.get s r = a₁.val := hA a (.reg r) hm a₁ hr

theorem argReg_ok {G : List (Val × Nat)} {R : SymRegs T.toIsa} {s : T.MData} {σ : List Val}
    (hA : Agree G R s σ) {a₁ : Arg Val} {a : Arg Nat} (hr : ArgRel G a₁ a) {a' : Arg T.Reg}
    (h : argReg R a = some a') :
    a'.map (T.get s) = a₁ ∧ ∀ r, r ∈ a'.vars → r ∉ T.scratch := by
  cases hr with
  | @var v x hvx =>
    simp only [argReg] at h
    split at h
    · rename_i r hr
      split at h
      · simp at h
      · rename_i hs
        simp only [Option.some.injEq] at h; subst h
        refine ⟨?_, fun r' hr' => ?_⟩
        · simp only [Arg.map]; rw [hA.reg (lookup_mem hr) (.var hvx)]; rfl
        · simp only [Arg.vars, List.mem_singleton] at hr'; subst hr'; exact hs
    · simp at h
  | imm c =>
    simp only [argReg, Option.some.injEq] at h; subst h
    exact ⟨rfl, fun r hr => by simp [Arg.vars] at hr⟩

theorem opRegs_ok {G : List (Val × Nat)} {R : SymRegs T.toIsa} {s : T.MData} {σ : List Val}
    (hA : Agree G R s σ) {op₁ : Op Val} {op₂ : Op Nat} (hr : OpRel G op₁ op₂) {o : Op T.Reg}
    (h : opRegs R op₂ = some o) : o.map (T.get s) = op₁ ∧ ∀ r, r ∈ o.vars → r ∉ T.scratch := by
  cases hr with
  | bin k o' ha hb =>
    simp only [opRegs] at h
    split at h
    · rename_i a' b' ha' hb'
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨e1, s1⟩ := argReg_ok hA ha ha'
      obtain ⟨e2, s2⟩ := argReg_ok hA hb hb'
      refine ⟨by simp only [Op.map, e1, e2], fun r hr => ?_⟩
      simp only [Op.vars, List.mem_append] at hr
      exact hr.elim (s1 r) (s2 r)
    · simp at h
  | cmp k o' ha hb =>
    simp only [opRegs] at h
    split at h
    · rename_i a' b' ha' hb'
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨e1, s1⟩ := argReg_ok hA ha ha'
      obtain ⟨e2, s2⟩ := argReg_ok hA hb hb'
      refine ⟨by simp only [Op.map, e1, e2], fun r hr => ?_⟩
      simp only [Op.vars, List.mem_append] at hr
      exact hr.elim (s1 r) (s2 r)
    · simp at h
  | ext k sz sg ha =>
    simp only [opRegs] at h
    split at h
    · rename_i a' ha'
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨e1, s1⟩ := argReg_ok hA ha ha'
      exact ⟨by simp only [Op.map, e1], fun r hr => s1 r (by simpa [Op.vars] using hr)⟩
    · simp at h
  | copy k ha =>
    simp only [opRegs] at h
    split at h
    · rename_i a' ha'
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨e1, s1⟩ := argReg_ok hA ha ha'
      exact ⟨by simp only [Op.map, e1], fun r hr => s1 r (by simpa [Op.vars] using hr)⟩
    · simp at h

/-- Registers outside `d` and the scratch registers kept, slots kept. -/
theorem Agree.clob {G : List (Val × Nat)} {R : SymRegs T.toIsa} {s s' : T.MData} {σ : List Val}
    {d : Option T.Reg} (hA : Agree G R s σ)
    (hs : ∀ r, some r ≠ d → r ∉ T.scratch → T.get s' r = T.get s r) :
    Agree G (Rega.clob d R) s' σ := by
  intro a l hx a₁ hv
  simp only [Rega.clob, List.mem_filter] at hx
  obtain ⟨hx, hk⟩ := hx
  cases l with
  | reg r =>
    simp only [keepAfter, Bool.and_eq_true, decide_eq_true_eq] at hk
    show T.get s' r = _
    rw [hs r hk.1 hk.2]; exact hA _ _ hx _ hv
  | slot i => exact hA _ _ hx _ hv

theorem Agree.slotsOnly {G : List (Val × Nat)} {R : SymRegs T.toIsa} {s s' : T.MData}
    {σ : List Val} (hA : Agree G R s σ) : Agree G (Rega.slotsOnly R) s' σ := by
  intro a l hx a₁ hv
  simp only [Rega.slotsOnly, List.mem_filter] at hx
  cases l with
  | reg r => simp at hx
  | slot i => exact hA _ _ hx.1 _ hv

theorem _root_.LeanQbe.ArgRel.mono {G G' : List (Val × Nat)} (hG : ∀ p ∈ G, p ∈ G')
    {a₁ : Arg Val} {a : Arg Nat} (h : ArgRel G a₁ a) : ArgRel G' a₁ a := by
  cases h with
  | var h => exact .var (hG _ h)
  | imm c => exact .imm c

theorem _root_.LeanQbe.ArgRel.uncons {G : List (Val × Nat)} {v : Val} {x : Nat} {a₁ : Arg Val}
    {a : Arg Nat} (h : ArgRel ((v, x) :: G) a₁ a) (hne : a ≠ .var x) : ArgRel G a₁ a := by
  cases h with
  | @var v₁ y hy =>
    simp only [List.mem_cons, Prod.mk.injEq] at hy
    rcases hy with ⟨-, rfl⟩ | hy
    · exact absurd rfl hne
    · exact .var hy
  | imm c => exact .imm c

theorem Agree.bindN {G : List (Val × Nat)} {R : SymRegs T.toIsa} {s : T.MData} {σ : List Val}
    {x : Nat} {r : T.Reg} {v : Val} (hA : Agree G R s σ) (hx : ∀ p ∈ G, p.2 < x)
    (hr : T.get s r = v) : Agree ((v, x) :: G) (Rega.bindN x r R) s σ := by
  intro a l hy a₁ hw
  simp only [Rega.bindN, List.mem_cons, List.mem_filter, Prod.mk.injEq, bne_iff_ne,
    ne_eq] at hy
  rcases hy with ⟨rfl, rfl⟩ | ⟨hy, hne⟩
  · cases hw with
    | @var v₁ _ hy =>
      simp only [List.mem_cons, Prod.mk.injEq] at hy
      rcases hy with ⟨rfl, -⟩ | hy
      · exact hr
      · exact absurd (hx _ hy) (by simp)
  · exact hA _ _ hy _ (hw.uncons hne)

theorem Agree.mono {G G' : List (Val × Nat)} {R : SymRegs T.toIsa} {s : T.MData} {σ : List Val}
    (hA : Agree G R s σ) (hG : ∀ p ∈ G', p ∈ G) : Agree G' R s σ :=
  fun a l hx a₁ hv => hA a l hx a₁ (hv.mono hG)

theorem mem_copyTo {I : Isa} {l d : Loc I} {R : SymRegs I} {a : Arg Nat} {l' : Loc I}
    (h : (a, l') ∈ copyTo l d R) : l' = d ∧ (a, l) ∈ R := by
  simp only [copyTo, List.mem_map, List.mem_filter, decide_eq_true_eq] at h
  obtain ⟨⟨a', l''⟩, ⟨hm, rfl⟩, he⟩ := h
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact ⟨rfl, hm⟩

/-- A move `d := s` between registers. -/
theorem Agree.mov {G : List (Val × Nat)} {R : SymRegs T.toIsa} {s s' : T.MData} {σ : List Val}
    {d r : T.Reg} (hA : Agree G R s σ) (hs : ∀ r', r' ∉ [d] → T.get s' r' = T.get s r')
    (hd : T.get s' d = T.get s r) : Agree G (movSym (.mov d r) R) s' σ := by
  intro a l hx a₁ hv
  simp only [movSym] at hx
  split at hx
  · rename_i hdr
    subst hdr
    cases l with
    | reg q =>
      show T.get s' q = _
      by_cases hq : q = d
      · subst hq; rw [hd]; exact hA _ _ hx _ hv
      · rw [hs q (by simpa using hq)]; exact hA _ _ hx _ hv
    | slot i => exact hA _ _ hx _ hv
  · rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨rfl, hm⟩ := mem_copyTo hx
      show T.get s' d = _
      rw [hd]; exact hA _ _ hm _ hv
    · simp only [List.mem_filter, decide_eq_true_eq] at hx
      cases l with
      | reg q =>
        show T.get s' q = _
        have hq : q ≠ d := fun e => hx.2 (by rw [e])
        rw [hs q (by simpa using hq)]; exact hA _ _ hx.1 _ hv
      | slot i => exact hA _ _ hx.1 _ hv

/-- `d := c`. -/
theorem Agree.movi {G : List (Val × Nat)} {R : SymRegs T.toIsa} {s s' : T.MData} {σ : List Val}
    {d : T.Reg} {c : Val} (hA : Agree G R s σ)
    (hs : ∀ r', r' ∉ d :: T.scratch → T.get s' r' = T.get s r') (hd : T.get s' d = c) :
    Agree G (movSym (.movi d c) R) s' σ := by
  intro a l hx a₁ hv
  simp only [movSym, List.mem_cons, Prod.mk.injEq] at hx
  rcases hx with ⟨rfl, rfl⟩ | hx
  · cases hv with
    | imm c => exact hd
  · refine (hA.clob (d := some d) (fun r h1 h2 => hs r ?_)) _ _ hx _ hv
    simp only [List.mem_cons, not_or]
    exact ⟨fun e => h1 (by rw [e]), h2⟩

/-- `d := slot i`. -/
theorem Agree.ld {G : List (Val × Nat)} {R : SymRegs T.toIsa} {s s' : T.MData} {σ : List Val}
    {d : T.Reg} {i : Nat} {v : Val} (hA : Agree G R s σ) (hv : σ[i]? = some v)
    (hs : ∀ r', r' ∉ d :: T.scratch → T.get s' r' = T.get s r') (hd : T.get s' d = v) :
    Agree G (movSym (.ld d i) R) s' σ := by
  intro a l hx a₁ ha
  simp only [movSym] at hx
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨rfl, hm⟩ := mem_copyTo hx
    have := hA _ _ hm _ ha
    simp only [LocHolds] at this ⊢
    rw [hv] at this
    rw [hd]; exact Option.some.inj this
  · refine (hA.clob (d := some d) (fun r h1 h2 => hs r ?_)) _ _ hx _ ha
    simp only [List.mem_cons, not_or]
    exact ⟨fun e => h1 (by rw [e]), h2⟩

/-- `slot i := s`. -/
theorem Agree.st {G : List (Val × Nat)} {R : SymRegs T.toIsa} {s s' : T.MData} {σ : List Val}
    {i : Nat} {r : T.Reg} (hA : Agree G R s σ) (hi : i < σ.length)
    (hs : ∀ r', r' ∉ T.scratch → T.get s' r' = T.get s r') :
    Agree G (movSym (.st i r) R) s' (σ.set i (T.get s r)) := by
  intro a l hx a₁ ha
  simp only [movSym] at hx
  have hx' := hx
  simp only [Rega.clob, List.mem_filter] at hx'
  obtain ⟨hx', hk⟩ := hx'
  rcases List.mem_append.mp hx' with hx' | hx'
  · obtain ⟨rfl, hm⟩ := mem_copyTo hx'
    simp only [LocHolds, List.getElem?_set_self hi]
    rw [hA.reg hm ha]
  · simp only [List.mem_filter, decide_eq_true_eq] at hx'
    cases l with
    | reg q =>
      simp only [keepAfter, Bool.and_eq_true, decide_eq_true_eq] at hk
      show T.get s' q = _
      rw [hs q hk.2]; exact hA _ _ hx'.1 _ ha
    | slot j =>
      have hj : j ≠ i := fun e => hx'.2 (by rw [e])
      have := hA _ _ hx'.1 _ ha
      simp only [LocHolds] at this ⊢
      rw [List.getElem?_set_ne (Ne.symm hj)]; exact this

/-! ## The frame invariant -/

section Frame
variable (hints : Hints T.toIsa) (s₀ : T.MData) (ra : T.Addr) (n : Nat) (Rf : Mem 64 → Prop)

/-- Bytes of the frame. -/
abbrev frame : Nat := T.frameSize hints.nslots

/-- Address of slot 0: the entry stack pointer minus the frame. -/
abbrev base : Val := T.get s₀ T.sp - BitVec.ofNat 64 (frame hints)

/-- What surrounds the slots: frame overhead, the stack left for callees, the caller's frame. -/
def Fr : Mem 64 → Prop :=
  T.Saved (T.get s₀ T.sp) ra hints.nslots ⋆
    (region (T.get s₀ T.sp - BitVec.ofNat 64 n) (n - frame hints) ⋆ Rf)

/-- The frame invariant, with source memory `m` and slot contents `σ`. -/
def Inv (m : Mem 64) (s : T.MData) (σ : List Val) : Prop :=
  σ.length = hints.nslots ∧ T.get s T.sp = base hints s₀ ∧
  (∀ r, r ∈ T.calleeSaved → T.get s r = T.get s₀ r) ∧
  (T.mem s =⋆ Eq m ⋆ (slots (base hints s₀) σ ⋆ Fr hints s₀ ra n Rf))

end Frame

section
variable {hints : Hints T.toIsa} {s₀ : T.MData} {ra : T.Addr} {n : Nat} {Rf : Mem 64 → Prop}

theorem Inv.regs {s s' : T.MData} {m : Mem 64} {σ : List Val} (hI : Inv hints s₀ ra n Rf m s σ)
    (hm : T.mem s' = T.mem s)
    (hs : ∀ r, r ∉ T.allocatable → r ∉ T.scratch → T.get s' r = T.get s r) :
    Inv hints s₀ ra n Rf m s' σ := by
  obtain ⟨hl, hsp, hcs, hmem⟩ := hI
  refine ⟨hl, ?_, fun r hr => ?_, hm ▸ hmem⟩
  · rw [hs _ T.sp_not_allocatable T.sp_not_scratch]; exact hsp
  · rw [hs r (T.calleeSaved_not_allocatable r hr) (T.calleeSaved_not_scratch r hr)]
    exact hcs r hr

theorem slots_set {a : Val} (σ : List Val) (i : Nat) (hi : i < σ.length) (v : Val) :
    slots a (σ.set i v) = slots a (σ.take i) ⋆
      (word (a + BitVec.ofNat 64 (8 * i)) v ⋆
        slots (a + BitVec.ofNat 64 (8 * i) + 8#64) (σ.drop (i + 1))) := by
  rw [slots_get (σ.set i v) i (by simpa using hi)]
  simp [List.take_set_of_le (Nat.le_refl i), List.drop_set_of_lt (Nat.lt_succ_self i)]

/-- The rest of the memory when slot `i` is taken out. -/
abbrev slotRest (hints : Hints T.toIsa) (s₀ : T.MData) (ra : T.Addr) (n : Nat) (Rf : Mem 64 → Prop)
    (m : Mem 64) (σ : List Val) (i : Nat) : Mem 64 → Prop :=
  Eq m ⋆ (slots (base hints s₀) (σ.take i) ⋆
    (slots (base hints s₀ + BitVec.ofNat 64 (8 * i) + 8#64) (σ.drop (i + 1)) ⋆
      Fr hints s₀ ra n Rf))

theorem Inv.slot {s : T.MData} {m : Mem 64} {σ : List Val} (hI : Inv hints s₀ ra n Rf m s σ)
    {i : Nat} (hi : i < σ.length) :
    T.mem s =⋆ word (T.get s T.sp + BitVec.ofNat 64 (8 * i)) σ[i] ⋆
      slotRest hints s₀ ra n Rf m σ i := by
  obtain ⟨-, hsp, -, hmem⟩ := hI
  rw [slots_get σ i hi] at hmem
  rw [hsp]
  unfold slotRest
  exact sep_ac' (by ac_rfl) hmem

theorem Inv.slotSet {s s' : T.MData} {m : Mem 64} {σ : List Val} (hI : Inv hints s₀ ra n Rf m s σ)
    {i : Nat} (hi : i < σ.length) {v : Val}
    (hmem : T.mem s' =⋆ word (T.get s T.sp + BitVec.ofNat 64 (8 * i)) v ⋆
      slotRest hints s₀ ra n Rf m σ i)
    (hs : ∀ r, r ∉ T.scratch → T.get s' r = T.get s r) :
    Inv hints s₀ ra n Rf m s' (σ.set i v) := by
  obtain ⟨hl, hsp, hcs, -⟩ := hI
  refine ⟨by simp [hl], ?_, fun r hr => ?_, ?_⟩
  · rw [hs _ T.sp_not_scratch]; exact hsp
  · rw [hs r (T.calleeSaved_not_scratch r hr)]; exact hcs r hr
  · rw [slots_set σ i hi v]
    rw [hsp] at hmem
    unfold slotRest at hmem
    exact sep_ac' (by ac_rfl) hmem

end

/-- Writing an allocatable or scratch register `d` and the scratch registers. -/
theorem keeps_dest {s s' : T.MData} {d : T.Reg} (hd : d ∈ T.allocatable ∨ d ∈ T.scratch)
    (hs : ∀ r, r ∉ d :: T.scratch → T.get s' r = T.get s r) :
    ∀ r, r ∉ T.allocatable → r ∉ T.scratch → T.get s' r = T.get s r := by
  intro r h1 h2
  refine hs r ?_
  simp only [List.mem_cons, not_or]
  exact ⟨fun e => hd.elim (fun h => h1 (e ▸ h)) (fun h => h2 (e ▸ h)), h2⟩

theorem keeps_dest' {s s' : T.MData} {d : T.Reg}
    (hs : ∀ r, r ∉ d :: T.scratch → T.get s' r = T.get s r) :
    ∀ r, some r ≠ some d → r ∉ T.scratch → T.get s' r = T.get s r := by
  intro r h1 h2
  refine hs r ?_
  simp only [List.mem_cons, not_or]
  exact ⟨fun e => h1 (by rw [e]), h2⟩

theorem keeps_one {s s' : T.MData} {d : T.Reg} (hd : d ∈ T.allocatable ∨ d ∈ T.scratch)
    (hs : ∀ r, r ∉ [d] → T.get s' r = T.get s r) :
    ∀ r, r ∉ T.allocatable → r ∉ T.scratch → T.get s' r = T.get s r := by
  intro r h1 h2
  refine hs r ?_
  simp only [List.mem_singleton]
  exact fun e => hd.elim (fun h => h1 (e ▸ h)) (fun h => h2 (e ▸ h))

/-! ## Labels -/

theorem labelAddr_of_unique {h : T.Host} (hu : T.LabelsUnique h) {j : Nat} {l : String}
    (hj : (T.prog h)[j]? = some (T.label l)) : T.labelAddr h l = T.addrOf h j :=
  T.labelAddr_eq hj fun j' hj' e => by have := hu _ _ _ e hj; omega

/-! ## Moves -/

section Moves
variable {h : T.Host} {post : T.State → Prop} {hints : Hints T.toIsa} {s₀ : T.MData}
  {ra : T.Addr} {n : Nat} {Rf : Mem 64 → Prop}

theorem spOk_of_inv (hspE : T.spEntry (T.get s₀ T.sp)) {m : Mem 64} {s : T.MData}
    {σ : List Val} (hI : Inv hints s₀ ra n Rf m s σ) : T.spOk (T.get s T.sp) := by
  rw [hI.2.1]; exact T.spOk_frame _ _ hspE

theorem moves_ok (hspE : T.spEntry (T.get s₀ T.sp)) {G : List (Val × Nat)} {m : Mem 64} :
    ∀ (mvs : List (Move T.toIsa)) (R R' : SymRegs T.toIsa) (k : Nat) (s : T.MData) (σ : List Val),
    execMoves hints.nslots mvs R = some R' → (movesCode mvs).IsInfixAt (T.prog h) k →
    Agree G R s σ → Inv hints s₀ ra n Rf m s σ →
    (∀ s' σ', Agree G R' s' σ' → Inv hints s₀ ra n Rf m s' σ' →
      T.Run h (k + (movesCode mvs).length) s' post) →
    T.Run h k s post
  | [], R, R', k, s, σ, he, _, hA, hI, kont => by
    simp only [execMoves, Option.some.injEq] at he; subst he
    simpa [movesCode] using kont s σ hA hI
  | mv :: mvs, R, R', k, s, σ, he, hc, hA, hI, kont => by
    simp only [execMoves] at he
    split at he
    · rename_i hok
      simp only [movesCode] at hc
      have hlen : ∀ s', T.Run h (k + (movesCode (mv :: mvs)).length) s' post →
          T.Run h (k + mv.code.length + (movesCode mvs).length) s' post := by
        intro s' hr; simpa [movesCode, Nat.add_assoc] using hr
      have rest := fun s1 σ1 hA1 hI1 => moves_ok hspE mvs _ R' _ s1 σ1 he (hc.append).2 hA1 hI1
        fun s2 σ2 hA2 hI2 => hlen s2 (kont s2 σ2 hA2 hI2)
      cases mv with
      | mov d r =>
        simp only [Move.ok, decide_eq_true_eq] at hok
        exact T.mov_spec (hc.append).1 fun s1 hd1 hs1 hm1 =>
          rest s1 σ (hA.mov hs1 hd1) (hI.regs hm1 (keeps_one hok hs1))
      | movi d c =>
        simp only [Move.ok, decide_eq_true_eq] at hok
        exact T.movi_spec (hc.append).1 fun s1 hd1 hs1 hm1 =>
          rest s1 σ (hA.movi hs1 hd1) (hI.regs hm1 (keeps_dest hok hs1))
      | ld d i =>
        simp only [Move.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
        have hi : i < σ.length := by rw [hI.1]; exact hok.2
        exact T.slotLd_spec (hc.append).1 (spOk_of_inv hspE hI) (hI.slot hi)
          fun s1 hd1 hs1 hm1 => rest s1 σ (hA.ld (List.getElem?_eq_getElem hi) hs1 hd1)
            (hI.regs hm1 (keeps_dest hok.1 hs1))
      | st i r =>
        simp only [Move.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
        have hi : i < σ.length := by rw [hI.1]; exact hok.2
        exact T.slotSt_spec (hc.append).1 hok.1 (spOk_of_inv hspE hI)
          (sep_mono (fun _ => word_region) (hI.slot hi))
          fun s1 hs1 hm1 => rest s1 _ (hA.st hi hs1) (hI.slotSet hi hm1 hs1)
    · simp at he

/-- Every target `(a, l)` holds. -/
def Holds (G : List (Val × Nat)) (tgts : SymRegs T.toIsa) (s : T.MData) (σ : List Val) : Prop :=
  ∀ a l, (a, l) ∈ tgts → ∀ a₁, ArgRel G a₁ a → LocHolds s σ l a₁.val

theorem shuffle_ok (hspE : T.spEntry (T.get s₀ T.sp)) {G : List (Val × Nat)} {m : Mem 64}
    {R tgts R' : SymRegs T.toIsa} {c : List T.Directive} {k : Nat} {s : T.MData} {σ : List Val}
    (hs : shuffle hints.nslots R tgts = some (c, R')) (hc : c.IsInfixAt (T.prog h) k)
    (hA : Agree G R s σ) (hI : Inv hints s₀ ra n Rf m s σ)
    (kont : ∀ s' σ', Holds G tgts s' σ' → Agree G R' s' σ' → Inv hints s₀ ra n Rf m s' σ' →
      T.Run h (k + c.length) s' post) :
    T.Run h k s post := by
  unfold shuffle at hs
  dsimp only at hs
  split at hs
  · rename_i R'' hR''
    split at hs
    · rename_i hall
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      refine moves_ok hspE _ R _ k s σ hR'' hc hA hI fun s' σ' hA' hI' =>
        kont s' σ' (fun a l hx a₁ hv => ?_) hA' hI'
      simp only [List.all_eq_true, decide_eq_true_eq] at hall
      exact hA' a l (hall _ hx) a₁ hv
    · simp at hs
  · simp at hs

end Moves

theorem valsIn_of_holds {G : List (Val × Nat)} {s : T.MData} {σ : List Val} :
    ∀ {as₁ : List (Arg Val)} {as : List (Arg Nat)} {rs : List T.Reg},
    Forall₂ (ArgRel G) as₁ as → as.length ≤ rs.length → Holds G (tgtsIn as rs) s σ →
    T.ValsIn rs (as₁.map Arg.val) s
  | _, _, _, .nil, _, _ => by simp [Target.ValsIn]
  | _, _, r :: rs, .cons hab hrest, hl, hz => by
    have h1 := hz _ (.reg r) (by simp [tgtsIn]) _ hab
    have h2 := valsIn_of_holds (rs := rs) hrest (by simpa using hl)
      fun x r' hx v hv => hz x r' (by simp [tgtsIn] at hx ⊢; exact Or.inr hx) v hv
    simp only [Target.ValsIn, List.map_cons, List.length_cons, List.take_succ_cons,
      List.map_cons] at h2 ⊢
    simp only [LocHolds] at h1
    rw [h1, h2]
  | _, _, [], .cons _ _, hl, _ => by simp at hl

theorem valsIn_cons {regs : List T.Reg} {vs : List Val} {s : T.MData} {r : T.Reg} {v : Val} :
    T.ValsIn (r :: regs) (v :: vs) s ↔ T.get s r = v ∧ T.ValsIn regs vs s := by
  simp [Target.ValsIn]

theorem valsIn_keep {regs : List T.Reg} {vs : List Val} {s s' : T.MData}
    (hk : ∀ r, r ∈ regs → T.get s' r = T.get s r) (h : T.ValsIn regs vs s) : T.ValsIn regs vs s' := by
  unfold Target.ValsIn at h ⊢
  exact (List.map_congr_left fun r hr => hk r (List.mem_of_mem_take hr)).trans h

theorem prepend_ok {I : Isa} {pre : List I.Directive} {r : Res I} {c : List I.Directive}
    {nv nl ip : Nat} (h : prepend pre r = .ok (c, nv, nl, ip)) :
    ∃ c', r = .ok (c', nv, nl, ip) ∧ c = pre ++ c' := by
  unfold prepend at h
  split at h <;> simp_all

/-! ## The function context -/

section Ctx
variable (h : T.Host) (hints : Hints T.toIsa) (E : Ext) (fn : String) (Γ : Env)
  (Q : LeanQbe.Post) (X : XPost) (s₀ : T.MData) (ra : T.Addr) (n nX : Nat) (Rf : Mem 64 → Prop)
  (bound : String → Nat)

/-- The postcondition of `FnSpec` for the function entered with data `s₀`, return address `ra`,
stack bound `n` and caller frame `Rf`. -/
def FnPost : T.State → Prop := fun st =>
  (T.pc st = ra ∧ ∃ rets m', Q rets m' ∧ T.RetsIn rets (T.data st) ∧
    T.Restored s₀ (T.data st) ∧
    (T.mem (T.data st) =⋆ Eq m' ⋆ T.Exit (T.get s₀ T.sp) n ⋆ Rf)) ∨
  (∃ sym' as m', X sym' as m' ∧ T.Defined h sym' ∧ T.pc st = T.labelAddr h sym' ∧
    T.ArgsIn as (T.data st) ∧ T.spEntry (T.get (T.data st) T.sp) ∧
    ∃ (ra' : T.Addr) (n' : Nat) (F : Mem 64 → Prop), nX ≤ n' ∧ n' + T.raBytes ≤ 2 ^ 64 ∧
      T.raReg (T.data st) ra' ∧
      (T.mem (T.data st) =⋆ Eq m' ⋆ T.Entry (T.get (T.data st) T.sp) ra' n' ⋆ F ⋆ Rf))

/-- What the function-level proof provides. -/
structure Hyps : Prop where
  unique : T.LabelsUnique h
  spE : T.spEntry (T.get s₀ T.sp)
  frame_le : frame hints ≤ n
  frame_bound : frame hints + T.raBytes ≤ 2 ^ 64
  stack_bound : n + T.raBytes ≤ 2 ^ 64
  callees : ∀ g, g ∈ E.callees → T.FnSpec h g (Γ g) (bound g) nX ∧
    frame hints + T.raBytes + bound g ≤ n
  exits : ∀ g, g ∈ E.exits → T.Defined h g ∧ nX ≤ n

/-- The machine meaning of label `ℓ`, chosen for the source join point. -/
def LabJ (G : List (Val × Nat)) (ℓ : Nat) : Cont := fun as m =>
  ∃ k, (T.prog h)[k]? = some (T.label (lname fn ℓ)) ∧
    ∀ s σ, Agree G (hints.entry ℓ).live s σ → T.ValsIn (hints.entry ℓ).ploc as s →
      Inv hints s₀ ra n Rf m s σ → T.Run h k s (FnPost h Q X s₀ ra n nX Rf)

/-- Every join point in scope is a `LabJ` of an earlier context. -/
def DOk (G : List (Val × Nat)) (D : List (Cont × Nat)) : Prop :=
  ∀ J ℓ, (J, ℓ) ∈ D → ∃ G', (∀ p ∈ G', p ∈ G) ∧ J = LabJ h hints fn Q X s₀ ra n nX Rf G' ℓ

end Ctx

theorem DOk.cons {h : T.Host} {hints : Hints T.toIsa} {fn : String} {Q : LeanQbe.Post}
    {X : XPost} {s₀ : T.MData} {ra : T.Addr} {n nX : Nat} {Rf : Mem 64 → Prop}
    {G : List (Val × Nat)} {D : List (Cont × Nat)}
    (hD : DOk h hints fn Q X s₀ ra n nX Rf G D) (p : Val × Nat) :
    DOk h hints fn Q X s₀ ra n nX Rf (p :: G) D := by
  intro J ℓ hJ
  obtain ⟨G', hG', rfl⟩ := hD J ℓ hJ
  exact ⟨G', fun q hq => List.mem_cons_of_mem _ (hG' q hq), rfl⟩

/-! ## Leaving the frame: `ret` and `exit` -/

section Leave
variable {h : T.Host} {hints : Hints T.toIsa} {E : Ext} {Γ : Env} {Q : LeanQbe.Post}
  {X : XPost} {s₀ : T.MData} {ra : T.Addr} {n nX : Nat} {Rf : Mem 64 → Prop} {bound : String → Nat}

theorem base_add_frame : base hints s₀ + BitVec.ofNat 64 (frame hints) = T.get s₀ T.sp :=
  BitVec.sub_add_cancel _ _

theorem below_add (hFn : frame hints ≤ n) :
    T.get s₀ T.sp - BitVec.ofNat 64 n + BitVec.ofNat 64 (n - frame hints) = base hints s₀ := by
  apply BitVec.eq_of_toNat_eq
  simp only [base, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := (T.get s₀ T.sp).isLt
  omega

/-- Put the frame back together: what the epilogue leaves is the caller's `Entry` footprint. -/
theorem frame_close (hy : Hyps h hints E Γ s₀ n nX bound) {m : Mem 64} {σ : List Val}
    (hσ : σ.length = hints.nslots) {M : Mem 64}
    (hM : M =⋆ T.RetAddr (T.get s₀ T.sp) ra ⋆
      region (base hints s₀ + BitVec.ofNat 64 (8 * hints.nslots))
        (frame hints - 8 * hints.nslots) ⋆
      (Eq m ⋆ (slots (base hints s₀) σ ⋆
        (region (T.get s₀ T.sp - BitVec.ofNat 64 n) (n - frame hints) ⋆ Rf)))) :
    M =⋆ Eq m ⋆ (T.Entry (T.get s₀ T.sp) ra n ⋆ Rf) := by
  have h8 : 8 * hints.nslots ≤ frame hints := T.slots_le_frameSize _
  have hF := hy.frame_bound
  have hFn := hy.frame_le
  have hn := hy.stack_bound
  -- slots to a region
  have h1 : M =⋆ slots (base hints s₀) σ ⋆ (T.RetAddr (T.get s₀ T.sp) ra ⋆
      region (base hints s₀ + BitVec.ofNat 64 (8 * hints.nslots))
        (frame hints - 8 * hints.nslots) ⋆
      (Eq m ⋆ (region (T.get s₀ T.sp - BitVec.ofNat 64 n) (n - frame hints) ⋆ Rf))) :=
    sep_ac' (by ac_rfl) hM
  have h2 : M =⋆ region (base hints s₀) (8 * hints.nslots) ⋆ (T.RetAddr (T.get s₀ T.sp) ra ⋆
      region (base hints s₀ + BitVec.ofNat 64 (8 * hints.nslots))
        (frame hints - 8 * hints.nslots) ⋆
      (Eq m ⋆ (region (T.get s₀ T.sp - BitVec.ofNat 64 n) (n - frame hints) ⋆ Rf))) := by
    have := sep_mono (P := slots (base hints s₀) σ)
      (P' := region (base hints s₀) (8 * σ.length))
      (fun _ hs => slots_region (by rw [hσ]; omega) hs) h1
    rwa [hσ] at this
  -- the slots and the padding are the frame
  have h3 : M =⋆ (region (base hints s₀) (8 * hints.nslots) ⋆
      region (base hints s₀ + BitVec.ofNat 64 (8 * hints.nslots))
        (frame hints - 8 * hints.nslots)) ⋆
      (T.RetAddr (T.get s₀ T.sp) ra ⋆
        (Eq m ⋆ (region (T.get s₀ T.sp - BitVec.ofNat 64 n) (n - frame hints) ⋆ Rf))) :=
    sep_ac' (by ac_rfl) h2
  rw [← region_split (by omega), Nat.add_sub_cancel' h8] at h3
  -- the stack below and the frame are the callee area of `Entry`
  have h4 : M =⋆ (region (T.get s₀ T.sp - BitVec.ofNat 64 n) (n - frame hints) ⋆
      region (T.get s₀ T.sp - BitVec.ofNat 64 n + BitVec.ofNat 64 (n - frame hints))
        (frame hints)) ⋆
      (T.RetAddr (T.get s₀ T.sp) ra ⋆ (Eq m ⋆ Rf)) := by
    rw [below_add hFn]; exact sep_ac' (by ac_rfl) h3
  rw [← region_split (by omega), Nat.sub_add_cancel hFn] at h4
  simp only [Target.Entry]
  exact sep_ac' (by ac_rfl) h4

theorem raReg_keep {s s' : T.MData} {a : T.Addr} (hs : ∀ r, r ∉ T.scratch → T.get s' r = T.get s r)
    (h : T.raReg s a) : T.raReg s' a :=
  T.raReg_of_raRegs s s' a (fun r hr => hs r (T.raRegs_not_scratch r hr)) h

/-- The epilogue, from the frame invariant. -/
theorem epilogue_ok (hy : Hyps h hints E Γ s₀ n nX bound) {k : Nat} {s : T.MData} {m : Mem 64}
    {σ : List Val} {post : T.State → Prop}
    (hc : (T.epilogue hints.nslots).IsInfixAt (T.prog h) k) (hI : Inv hints s₀ ra n Rf m s σ)
    (kont : ∀ s', T.get s' T.sp = T.get s₀ T.sp → T.raReg s' ra →
      (∀ r, r ∉ T.sp :: T.raRegs ++ T.scratch → T.get s' r = T.get s r) →
      (T.mem s' =⋆ Eq m ⋆ (T.Entry (T.get s₀ T.sp) ra n ⋆ Rf)) →
      T.Run h (k + (T.epilogue hints.nslots).length) s' post) :
    T.Run h k s post := by
  obtain ⟨hσ, hsp, -, hmem⟩ := hI
  have hsp' : T.get s T.sp + BitVec.ofNat 64 (frame hints) = T.get s₀ T.sp := by
    rw [hsp]; exact base_add_frame
  refine T.epilogue_spec hc (by rw [hsp]; exact T.spOk_frame _ _ hy.spE) hy.frame_bound
    (G := Eq m ⋆ (slots (base hints s₀) σ ⋆
      (region (T.get s₀ T.sp - BitVec.ofNat 64 n) (n - frame hints) ⋆ Rf)))
    (by rw [hsp']; unfold Fr at hmem; exact sep_ac' (by ac_rfl) hmem)
    fun s' hsp2 hra hk hm => kont s' (by rw [hsp2, hsp']) hra hk ?_
  rw [hsp', hsp] at hm
  exact frame_close hy hσ hm

/-- `epilogue; ret` with the results in place. -/
theorem ret_ok (hy : Hyps h hints E Γ s₀ n nX bound) {k : Nat} {s : T.MData} {m : Mem 64}
    {σ : List Val} {rets : List Val}
    (hc : (T.epilogue hints.nslots ++ T.ret).IsInfixAt (T.prog h) k)
    (hI : Inv hints s₀ ra n Rf m s σ) (hrets : T.ValsIn T.retRegs rets s) (hQ : Q rets m) :
    T.Run h k s (FnPost h Q X s₀ ra n nX Rf) := by
  have hcs := hI.2.2.1
  refine epilogue_ok hy (hc.append).1 hI fun s2 hsp2 hra2 hk2 hm2 => ?_
  have hm2' : T.mem s2 =⋆ T.RetAddr (T.get s2 T.sp) ra ⋆
      (Eq m ⋆ (region (T.get s₀ T.sp - BitVec.ofNat 64 n) n ⋆ Rf)) := by
    rw [hsp2]; simp only [Target.Entry] at hm2; exact sep_ac' (by ac_rfl) hm2
  refine T.ret_spec (hc.append).2 hra2 hm2' fun s3 hk3 hsp3 hm3 => ?_
  have keep2 : ∀ r, r ≠ T.sp → r ∉ T.raRegs → r ∉ T.scratch → T.get s3 r = T.get s r := by
    intro r h1 h2 h3
    rw [hk3 r (by simp [h1, h3]), hk2 r (by simp [h1, h2, h3])]
  refine Eventually.done _ (Or.inl ⟨T.pc_mk _ _, rets, m, hQ, ?_, ⟨?_, ?_⟩, ?_⟩)
  · rw [T.data_mk]
    refine valsIn_keep (fun r hr => keep2 r (fun e => T.sp_not_retRegs (e ▸ hr))
      (fun h' => T.raRegs_not_retRegs r h' hr) (T.retRegs_not_scratch r hr)) hrets
  · intro r hr
    rw [T.data_mk, keep2 r (fun e => T.sp_not_calleeSaved (e ▸ hr))
      (fun h' => T.raRegs_not_calleeSaved r h' hr) (T.calleeSaved_not_scratch r hr)]
    exact hcs r hr
  · rw [T.data_mk, hsp3, hsp2]
  · rw [T.data_mk, hm3]; exact T.exit_of_entry_assoc hy.stack_bound hm2

/-- `epilogue; tailJmp g` with the arguments in place. -/
theorem exit_ok (hy : Hyps h hints E Γ s₀ n nX bound) {k : Nat} {s : T.MData} {m : Mem 64}
    {σ : List Val} {g : String} {as : List Val}
    (hc : (T.epilogue hints.nslots ++ T.tailJmp g).IsInfixAt (T.prog h) k)
    (hI : Inv hints s₀ ra n Rf m s σ) (hargs : T.ArgsIn as s) (hX : X g as m)
    (hg : g ∈ E.exits) :
    T.Run h k s (FnPost h Q X s₀ ra n nX Rf) := by
  refine epilogue_ok hy (hc.append).1 hI fun s2 hsp2 hra2 hk2 hm2 => ?_
  refine T.tailJmp_spec (hc.append).2 fun s3 hk3 hm3 => ?_
  have hsp3 : T.get s3 T.sp = T.get s₀ T.sp := by rw [hk3 _ T.sp_not_scratch, hsp2]
  refine Eventually.done _ (Or.inr ⟨g, as, m, hX, (hy.exits g hg).1, T.pc_mk _ _, ?_, ?_, ra, n,
    Std.ExtHashMap.emp, (hy.exits g hg).2, hy.stack_bound, ?_, ?_⟩)
  · rw [T.data_mk]
    unfold Target.ArgsIn at hargs ⊢
    refine valsIn_keep (fun r hr => ?_) hargs
    rw [hk3 r (T.argRegs_not_scratch r hr), hk2 r ?_]
    simp only [List.mem_cons, List.mem_append, not_or]
    exact ⟨⟨fun e => T.sp_not_argRegs (e ▸ hr), fun h' => T.raRegs_not_argRegs r h' hr⟩,
      T.argRegs_not_scratch r hr⟩
  · rw [T.data_mk, hsp3]; exact hy.spE
  · rw [T.data_mk]; exact raReg_keep hk3 hra2
  · rw [T.data_mk, hm3, hsp3, Std.ExtHashMap.sep_emp]
    exact sep_ac' (by ac_rfl) hm2

end Leave

theorem _root_.LeanQbe.Forall₂.append_single {α β : Type} {R : α → β → Prop} {a : α} {b : β} :
    ∀ {as : List α} {bs : List β}, Forall₂ R as bs → R a b → Forall₂ R (as ++ [a]) (bs ++ [b])
  | _, _, .nil, h => .cons h .nil
  | _, _, .cons h1 h2, h => .cons h1 (h2.append_single h)

end Rega
end LeanQbe


namespace LeanQbe
namespace Rega

variable {T : Target}

private theorem sub_add_sub (x : BitVec 64) {n m : Nat} (h : m ≤ n) :
    x - BitVec.ofNat 64 n + BitVec.ofNat 64 (n - m) = x - BitVec.ofNat 64 m := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := x.isLt
  omega

private theorem sub_ofNat_add (x : BitVec 64) (a b : Nat) :
    x - BitVec.ofNat 64 (a + b) = x - BitVec.ofNat 64 a - BitVec.ofNat 64 b := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := x.isLt
  omega

section Main
variable {hints : Hints T.toIsa} {s₀ : T.MData} {ra : T.Addr} {n : Nat} {Rf : Mem 64 → Prop}

theorem Inv.mem {s s' : T.MData} {m m' : Mem 64} {σ : List Val}
    (hI : Inv hints s₀ ra n Rf m s σ)
    (hm : T.mem s' =⋆ Eq m' ⋆ (slots (base hints s₀) σ ⋆ Fr hints s₀ ra n Rf))
    (hs : ∀ r, r ∉ T.allocatable → r ∉ T.scratch → T.get s' r = T.get s r) :
    Inv hints s₀ ra n Rf m' s' σ := by
  obtain ⟨hl, hsp, hcs, -⟩ := hI
  refine ⟨hl, ?_, fun r hr => ?_, hm⟩
  · rw [hs _ T.sp_not_allocatable T.sp_not_scratch]; exact hsp
  · rw [hs r (T.calleeSaved_not_allocatable r hr) (T.calleeSaved_not_scratch r hr)]
    exact hcs r hr

/-- The callee area below the frame: `b + raBytes` bytes right below the stack pointer. -/
theorem callee_split {b : Nat} (hb : frame hints + T.raBytes + b ≤ n) (hn : n ≤ 2 ^ 64) :
    region (T.get s₀ T.sp - BitVec.ofNat 64 n) (n - frame hints) =
      region (T.get s₀ T.sp - BitVec.ofNat 64 n) (n - frame hints - (b + T.raBytes)) ⋆
      region (base hints s₀ - BitVec.ofNat 64 T.raBytes - BitVec.ofNat 64 b) (b + T.raBytes) := by
  have e : n - frame hints = n - frame hints - (b + T.raBytes) + (b + T.raBytes) := by omega
  conv => lhs; rw [e]
  rw [region_split (by omega)]
  have e2 : T.get s₀ T.sp - BitVec.ofNat 64 n + BitVec.ofNat 64 (n - frame hints - (b + T.raBytes)) =
      base hints s₀ - BitVec.ofNat 64 T.raBytes - BitVec.ofNat 64 b := by
    rw [Nat.sub_sub, sub_add_sub _ (by omega), Nat.add_comm b T.raBytes, ← Nat.add_assoc,
      sub_ofNat_add, sub_ofNat_add]
  rw [e2]

end Main

section Lower
variable (h : T.Host) (hints : Hints T.toIsa) (E : Ext) (fn : String) (Γ : Env)
  (Q : LeanQbe.Post) (X : XPost) (s₀ : T.MData) (ra : T.Addr) (n nX : Nat) (Rf : Mem 64 → Prop)
  (bound : String → Nat)

/-- Correctness of `lower`, for every term related by `Wf`. -/
theorem lower_correct (hy : Hyps h hints E Γ s₀ n nX bound) {G : List (Val × Nat)}
    {D : List (Cont × Nat)} {e₁ : Expr Val Cont} {e₂ : Expr Nat Nat} (hwf : Wf G D e₁ e₂) :
    ∀ (st : St T.toIsa) (code : List T.Directive) (nv' nl' ip' : Nat),
    lower hints E fn e₂ st = .ok (code, nv', nl', ip') →
    (∀ p ∈ G, p.2 < st.nv) →
    st.nv ≤ nv' ∧
    ∀ (k : Nat) (args : List Val) (acc : List Cont) (m : Mem 64) (s : T.MData) (σ : List Val),
    code.IsInfixAt (T.prog h) k →
    DOk h hints fn Q X s₀ ra n nX Rf G D →
    Forall₂ (fun J ℓ => J = LabJ h hints fn Q X s₀ ra n nX Rf G ℓ) acc st.pend →
    Agree G st.R s σ → T.ValsIn st.PL args s → Inv hints s₀ ra n Rf m s σ →
    wp Γ Q X e₁ args acc m → T.Run h k s (FnPost h Q X s₀ ra n nX Rf) := by
  have fresh : ∀ {G : List (Val × Nat)} {n : Nat}, (∀ p ∈ G, p.2 < n) →
      ∀ v, ∀ p ∈ (v, n) :: G, p.2 < n + 1 := by
    intro G n hG v p hp
    simp only [List.mem_cons] at hp
    rcases hp with rfl | hp
    · simp
    · have := hG _ hp; omega
  have nilR : ∀ {s : T.MData}, T.ValsIn ([] : List T.Reg) [] s := by simp [Target.ValsIn]
  induction hwf with
  | @let_ G D op₁ op₂ k₁ k₂ hop _ ih =>
    intro st code nv' nl' ip' hl hG
    simp only [lower] at hl
    split at hl
    · simp at hl
    · rename_i R1 hR1
      split at hl
      · rename_i d o hd ho
        split at hl
        · rename_i hda
          split at hl
          · rename_i c hc
            obtain ⟨c', hl', rfl⟩ := prepend_ok hl
            have ih' := fun v => ih v st.nv _ c' nv' nl' ip' hl' (fresh hG v)
            refine ⟨by have := (ih' 0).1; simp at this; omega, ?_⟩
            intro k args acc m s σ hcode hD hP hA hR hI hw
            simp only [wp] at hw
            obtain ⟨rfl, v, hv, hw⟩ := hw
            refine moves_ok hy.spE _ st.R R1 k s σ hR1 hcode.append.1.append.1 hA hI
              fun s1 σ1 hA1 hI1 => ?_
            obtain ⟨e1, hsc⟩ := opRegs_ok hA1 hop ho
            refine T.op_spec hc hcode.append.1.append.2 hsc (by rw [e1]; exact hv)
              fun s' hd' hs' hm' => ?_
            have := (ih' v).2 _ [] [] _ s' σ1 hcode.append.2 (hD.cons _) .nil
              ((hA1.clob (keeps_dest' hs')).bindN hG hd') nilR
              (hI1.regs hm' (keeps_dest (.inl hda) hs')) hw
            simpa only [Target.Run, List.length_append, Nat.add_assoc] using this
          · simp at hl
        · simp at hl
      · simp at hl
  | @load G D cl sz sg a₁ a₂ k₁ k₂ ha _ ih =>
    intro st code nv' nl' ip' hl hG
    simp only [lower] at hl
    split at hl
    · simp at hl
    · rename_i R1 hR1
      split at hl
      · rename_i d a' hd ha'
        split at hl
        · rename_i hda
          split at hl
          · rename_i c hc
            obtain ⟨c', hl', rfl⟩ := prepend_ok hl
            have ih' := fun v => ih v st.nv _ c' nv' nl' ip' hl' (fresh hG v)
            refine ⟨by have := (ih' 0).1; simp at this; omega, ?_⟩
            intro k args acc m s σ hcode hD hP hA hR hI hw
            simp only [wp] at hw
            obtain ⟨rfl, v, hv, hw⟩ := hw
            refine moves_ok hy.spE _ st.R R1 k s σ hR1 hcode.append.1.append.1 hA hI
              fun s1 σ1 hA1 hI1 => ?_
            obtain ⟨e1, hsc⟩ := argReg_ok hA1 ha ha'
            refine T.load_spec hc hcode.append.1.append.2 hsc
              (by rw [e1]; exact loadVal_frame hI1.2.2.2 hv)
              fun s' hd' hs' hm' => ?_
            have := (ih' v).2 _ [] [] _ s' σ1 hcode.append.2 (hD.cons _) .nil
              ((hA1.clob (keeps_dest' hs')).bindN hG hd') nilR
              (hI1.regs hm' (keeps_dest (.inl hda) hs')) hw
            simpa only [Target.Run, List.length_append, Nat.add_assoc] using this
          · simp at hl
        · simp at hl
      · simp at hl
  | @store G D sz v₁ v₂ a₁ a₂ k₁ k₂ hv ha _ ih =>
    intro st code nv' nl' ip' hl hG
    simp only [lower] at hl
    split at hl
    · simp at hl
    · rename_i R1 hR1
      split at hl
      · rename_i v' a' hv' ha'
        split at hl
        · rename_i c hc
          obtain ⟨c', hl', rfl⟩ := prepend_ok hl
          have ih' := ih _ c' nv' nl' ip' hl' hG
          refine ⟨ih'.1, ?_⟩
          intro k args acc m s σ hcode hD hP hA hR hI hw
          simp only [wp] at hw
          obtain ⟨rfl, hok, hw⟩ := hw
          refine moves_ok hy.spE _ st.R R1 k s σ hR1 hcode.append.1.append.1 hA hI
            fun s1 σ1 hA1 hI1 => ?_
          obtain ⟨e1, s1v⟩ := argReg_ok hA1 hv hv'
          obtain ⟨e2, s2v⟩ := argReg_ok hA1 ha ha'
          refine T.store_spec hc hcode.append.1.append.2
            (fun r hr => (List.mem_append.mp hr).elim (s1v r) (s2v r))
            (by rw [e2]; exact storeOk_frame hI1.2.2.2 hok)
            fun s' hs' hm' => ?_
          rw [e1, e2] at hm'
          have := ih'.2 _ [] [] _ s' σ1 hcode.append.2 hD .nil
            (hA1.clob (fun r _ h2 => hs' r h2)) nilR
            (hI1.mem (by rw [hm']; exact storeMem_frame hI1.2.2.2 hok _)
              (fun r _ h2 => hs' r h2)) hw
          simpa only [Target.Run, List.length_append, Nat.add_assoc] using this
        · simp at hl
      · simp at hl
  | @call G D g as₁ as₂ k₁ k₂ has _ ih =>
    intro st code nv' nl' ip' hl hG
    simp only [lower] at hl
    split at hl
    · simp at hl
    · rename_i R1 hR1
      split at hl
      · rename_i hcond
        obtain ⟨hg, hlen⟩ := hcond
        split at hl
        · rename_i c R2 hsh
          obtain ⟨c', hl', rfl⟩ := prepend_ok hl
          have ih' := ih _ c' nv' nl' ip' hl' hG
          refine ⟨ih'.1, ?_⟩
          intro k args acc m s σ hcode hD hP hA hR hI hw
          simp only [wp] at hw
          obtain ⟨rfl, P, E', hspec, hcont, hexit⟩ := hw
          obtain ⟨hf, hbound⟩ := hy.callees g hg
          have hn' : n ≤ 2 ^ 64 := by have := hy.stack_bound; omega
          have hc1 := hcode.append.1
          refine moves_ok hy.spE _ st.R R1 k s σ hR1 hc1.append.1.append.1 hA hI
            fun s1 σ1 hA1 hI1 => ?_
          refine shuffle_ok hy.spE hsh hc1.append.1.append.2 hA1 hI1
            fun s2 σ2 hT2 hA2 hI2 => ?_
          have hargs : T.ArgsIn (as₁.map Arg.val) s2 := valsIn_of_holds has hlen hT2
          have hm2 := hI2.2.2.2
          unfold Fr at hm2
          rw [callee_split hbound hn'] at hm2
          have hcall : (T.call g).IsInfixAt (T.prog h)
              (k + (movesCode (hints.pre st.ip)).length + c.length) := by
            simpa only [List.length_append, Nat.add_assoc] using hc1.append.2
          refine T.call_fnspec hcall hf hspec hargs
            (by rw [hI2.2.1]; exact T.spEntry_call _ _ hy.spE)
            (by have := hy.stack_bound; omega)
            (G := slots (base hints s₀) σ2 ⋆
              (T.Saved (T.get s₀ T.sp) ra hints.nslots ⋆
                (region (T.get s₀ T.sp - BitVec.ofNat 64 n)
                  (n - frame hints - (bound g + T.raBytes)) ⋆ Rf)))
            (by rw [hI2.2.1]; exact sep_ac' (by ac_rfl) hm2)
            (fun s' rets m' hP' hrets hcs' hsp' hm' => ?_)
            (fun st' sym' as' m' ra' n' F hE' hdef hpc has' hspE hnX hb hra' hmx => ?_)
          · have hI' : Inv hints s₀ ra n Rf m' s' σ2 :=
              ⟨hI2.1, hsp'.trans hI2.2.1, fun r hr => (hcs' r hr).trans (hI2.2.2.1 r hr), by
                rw [hI2.2.1] at hm'
                unfold Fr
                rw [callee_split hbound hn']
                exact sep_ac' (by ac_rfl) hm'⟩
            have := ih'.2 _ rets [] m' s' σ2 hcode.append.2 hD .nil
              hA2.slotsOnly hrets hI' (hcont rets m' hP')
            simpa only [Target.Run, List.length_append, Nat.add_assoc] using this
          · refine Or.inr ⟨sym', as', m', hexit sym' as' m' hE', hdef, hpc, has', hspE, ra', n',
              F ⋆ (slots (base hints s₀) σ2 ⋆
                (T.Saved (T.get s₀ T.sp) ra hints.nslots ⋆
                  region (T.get s₀ T.sp - BitVec.ofNat 64 n)
                    (n - frame hints - (bound g + T.raBytes)))),
              hnX, hb, hra', sep_ac' (by ac_rfl) hmx⟩
        · simp at hl
      · simp at hl
  | @jnz G D c₁ c₂ t₁ t₂ e₁ e₂ hc _ _ iht ihe =>
    intro st code nv' nl' ip' hl hG
    cases hc with
    | imm c =>
      simp only [lower] at hl
      split at hl
      · simp at hl
      · rename_i R1 hR1
        obtain ⟨c', hl', rfl⟩ := prepend_ok hl
        split at hl'
        · rename_i htr
          have iht' := iht _ c' nv' nl' ip' hl' hG
          refine ⟨iht'.1, ?_⟩
          intro k args acc m s σ hcode hD hP hA hR hI hw
          simp only [wp] at hw
          obtain ⟨rfl, hwt, -⟩ := hw
          refine moves_ok hy.spE _ st.R R1 k s σ hR1 hcode.append.1 hA hI
            fun s1 σ1 hA1 hI1 => ?_
          exact iht'.2 _ [] [] m s1 σ1 hcode.append.2 hD .nil hA1 nilR hI1 (hwt htr)
        · rename_i htr
          have ihe' := ihe _ c' nv' nl' ip' hl' hG
          refine ⟨ihe'.1, ?_⟩
          intro k args acc m s σ hcode hD hP hA hR hI hw
          simp only [wp] at hw
          obtain ⟨rfl, -, hwe⟩ := hw
          refine moves_ok hy.spE _ st.R R1 k s σ hR1 hcode.append.1 hA hI
            fun s1 σ1 hA1 hI1 => ?_
          exact ihe'.2 _ [] [] m s1 σ1 hcode.append.2 hD .nil hA1 nilR hI1 (hwe htr)
    | @var v x hvx =>
      simp only [lower] at hl
      split at hl
      · simp at hl
      · rename_i R1 hR1
        split at hl
        · rename_i rc hrc
          split at hl
          · rename_i ce nv1 nl1 ip1 hle
            obtain ⟨c', hl', rfl⟩ := prepend_ok hl
            have ihe' := ihe _ ce nv1 nl1 ip1 hle hG
            have iht' := iht _ c' nv' nl' ip' hl'
              (fun p hp => by have := hG p hp; simp at ihe' ⊢; omega)
            refine ⟨by simp at iht' ihe'; omega, ?_⟩
            intro k args acc m s σ hcode hD hP hA hR hI hw
            simp only [wp] at hw
            obtain ⟨rfl, hwt, hwe⟩ := hw
            have hc1 := hcode.append.1
            refine moves_ok hy.spE _ st.R R1 k s σ hR1 hc1.append.1.append.1.append.1 hA hI
              fun s1 σ1 hA1 hI1 => ?_
            obtain ⟨e1, hsc⟩ := argReg_ok hA1 (.var hvx) hrc
            simp only [Arg.map, Arg.var.injEq] at e1
            have hlab : (T.prog h)[k + (movesCode (hints.pre st.ip)).length +
                (T.jnz rc (lname fn st.nl)).length + ce.length]? =
                some (T.label (lname fn st.nl)) := by
              have := hc1.append.2
              simpa [Nat.add_assoc] using (List.isInfixAt_singleton.mp this)
            have hjnz : (T.jnz rc (lname fn st.nl)).IsInfixAt (T.prog h)
                (k + (movesCode (hints.pre st.ip)).length) := hc1.append.1.append.1.append.2
            refine T.jnz_spec hjnz (labelAddr_of_unique hy.unique hlab)
              (hsc rc (by simp [Arg.vars])) fun s' hs' hm' => ⟨fun h0 => ?_, fun h0 => ?_⟩
            · refine T.label_spec hlab ?_
              have := iht'.2 _ [] [] m s' σ1 hcode.append.2 hD .nil
                (hA1.clob (fun r _ h2 => hs' r h2)) nilR
                (hI1.regs hm' (fun r _ h2 => hs' r h2)) (hwt (by rw [← e1]; exact h0))
              simpa only [Target.Run, List.length_append, List.length_singleton, Nat.add_assoc]
                using this
            · have := ihe'.2 _ [] [] m s' σ1 hc1.append.1.append.2 hD .nil
                (hA1.clob (fun r _ h2 => hs' r h2)) nilR
                (hI1.regs hm' (fun r _ h2 => hs' r h2)) (hwe (by rw [← e1]; exact h0))
              simpa only [Target.Run, List.length_append, Nat.add_assoc] using this
          · simp at hl
        · simp at hl
  | @jump G D j₁ j₂ as₁ as₂ hj has =>
    intro st code nv' nl' ip' hl hG
    simp only [lower] at hl
    split at hl
    · simp at hl
    · rename_i R1 hR1
      split at hl
      · rename_i hcond
        obtain ⟨hlen, hnsc⟩ := hcond
        simp only [List.all_eq_true] at hnsc
        split at hl
        · rename_i c R2 hsh
          simp only [Except.ok.injEq, Prod.mk.injEq] at hl
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hl
          refine ⟨Nat.le_refl _, ?_⟩
          intro k args acc m s σ hcode hD hP hA hR hI hw
          simp only [wp] at hw
          obtain ⟨rfl, hw⟩ := hw
          obtain ⟨G', hG', rfl⟩ := hD _ _ hj
          obtain ⟨kℓ, hkℓ, hJ⟩ := hw
          have hc1 := hcode.append.1
          refine moves_ok hy.spE _ st.R R1 k s σ hR1 hc1.append.1 hA hI
            fun s1 σ1 hA1 hI1 => ?_
          refine shuffle_ok hy.spE hsh hc1.append.2 hA1 hI1
            fun s2 σ2 ht _ hI2 => ?_
          have hjmp : (T.jmp (lname fn j₂)).IsInfixAt (T.prog h)
              (k + (movesCode (hints.pre st.ip)).length + c.length) := by
            simpa only [List.length_append, Nat.add_assoc] using hcode.append.2
          refine T.jmp_spec hjmp (labelAddr_of_unique hy.unique hkℓ)
            fun s' hs' hm' => hJ s' σ2 ?_ ?_ (hI2.regs hm' (fun r _ h2 => hs' r h2))
          · intro a l hx a₁ hv
            have hx' := List.mem_append_left (tgtsIn as₂ (hints.entry j₂).ploc) hx
            have h1 := ht a l hx' a₁ (hv.mono hG')
            cases l with
            | reg r =>
              have hr := of_decide_eq_true (hnsc (a, .reg r) hx')
              simp only [LocHolds] at h1 ⊢
              rw [hs' r hr, h1]
            | slot i => exact h1
          · refine valsIn_of_holds (σ := σ2) has (by omega) fun a l hx a₁ hv => ?_
            have hx' := List.mem_append_right (hints.entry j₂).live hx
            have h1 := ht a l hx' a₁ hv
            cases l with
            | reg r =>
              have hr := of_decide_eq_true (hnsc (a, .reg r) hx')
              simp only [LocHolds] at h1 ⊢
              rw [hs' r hr, h1]
            | slot i => exact h1
        · simp at hl
      · simp at hl
  | @ret G D vs₁ vs₂ hvs =>
    intro st code nv' nl' ip' hl hG
    simp only [lower] at hl
    split at hl
    · simp at hl
    · rename_i R1 hR1
      split at hl
      · rename_i hlen
        split at hl
        · rename_i c R2 hsh
          simp only [Except.ok.injEq, Prod.mk.injEq] at hl
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hl
          refine ⟨Nat.le_refl _, ?_⟩
          intro k args acc m s σ hcode hD hP hA hR hI hw
          simp only [wp] at hw
          obtain ⟨rfl, hw⟩ := hw
          have hc1 := hcode.append.1.append.1
          refine moves_ok hy.spE _ st.R R1 k s σ hR1 hc1.append.1 hA hI
            fun s1 σ1 hA1 hI1 => ?_
          refine shuffle_ok hy.spE hsh hc1.append.2 hA1 hI1
            fun s2 σ2 ht _ hI2 => ?_
          have hret_c : (T.epilogue hints.nslots ++ T.ret).IsInfixAt (T.prog h)
              (k + (movesCode (hints.pre st.ip)).length + c.length) := by
            rw [List.append_assoc (movesCode (hints.pre st.ip) ++ c)] at hcode
            simpa only [List.length_append, Nat.add_assoc] using hcode.append.2
          exact ret_ok hy hret_c hI2 (valsIn_of_holds hvs hlen ht) hw
        · simp at hl
      · simp at hl
  | @exit G D g as₁ as₂ has =>
    intro st code nv' nl' ip' hl hG
    simp only [lower] at hl
    split at hl
    · simp at hl
    · rename_i R1 hR1
      split at hl
      · rename_i hcond
        obtain ⟨hg, hlen⟩ := hcond
        split at hl
        · rename_i c R2 hsh
          simp only [Except.ok.injEq, Prod.mk.injEq] at hl
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hl
          refine ⟨Nat.le_refl _, ?_⟩
          intro k args acc m s σ hcode hD hP hA hR hI hw
          simp only [wp] at hw
          obtain ⟨rfl, hw⟩ := hw
          have hc1 := hcode.append.1.append.1
          refine moves_ok hy.spE _ st.R R1 k s σ hR1 hc1.append.1 hA hI
            fun s1 σ1 hA1 hI1 => ?_
          refine shuffle_ok hy.spE hsh hc1.append.2 hA1 hI1
            fun s2 σ2 ht _ hI2 => ?_
          have hexit_c : (T.epilogue hints.nslots ++ T.tailJmp g).IsInfixAt (T.prog h)
              (k + (movesCode (hints.pre st.ip)).length + c.length) := by
            rw [List.append_assoc (movesCode (hints.pre st.ip) ++ c)] at hcode
            simpa only [List.length_append, Nat.add_assoc] using hcode.append.2
          exact exit_ok hy hexit_c hI2 (valsIn_of_holds has hlen ht) hw hg
        · simp at hl
      · simp at hl
  | hlt =>
    intro st code nv' nl' ip' hl hG
    simp only [lower, Except.ok.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hl
    exact ⟨Nat.le_refl _, fun _ _ _ _ _ _ _ _ _ _ _ _ hw => by simp [wp] at hw⟩
  | @param G D f₁ f₂ _ ih =>
    intro st code nv' nl' ip' hl hG
    simp only [lower] at hl
    split at hl
    · simp at hl
    · rename_i r PL hPL
      refine ⟨by have := (ih 0 st.nv _ code nv' nl' ip' hl (fresh hG 0)).1; simp at this; omega, ?_⟩
      intro k args acc m s σ hcode hD hP hA hR hI hw
      rw [hPL] at hR
      cases args with
      | nil => simp [wp] at hw
      | cons a as =>
        obtain ⟨hra, hR⟩ := valsIn_cons.mp hR
        simp only [wp] at hw
        exact (ih a st.nv _ code nv' nl' ip' hl (fresh hG a)).2 k as [] m s σ hcode (hD.cons _) .nil
          (hA.bindN hG hra) hR hI hw
  | @label G D f₁ f₂ _ ih =>
    intro st code nv' nl' ip' hl hG
    simp only [lower] at hl
    let J := LabJ h hints fn Q X s₀ ra n nX Rf G st.nl
    have ih' := ih J st.nl _ code nv' nl' ip' hl hG
    refine ⟨ih'.1, ?_⟩
    intro k args acc m s σ hcode hD hP hA hR hI hw
    simp only [wp] at hw
    obtain ⟨rfl, hw⟩ := hw
    refine ih'.2 k [] (acc ++ [J]) m s σ hcode ?_ (hP.append_single rfl) hA hR hI (hw J)
    intro J' ℓ hJ'
    simp only [List.mem_cons, Prod.mk.injEq] at hJ'
    rcases hJ' with ⟨rfl, rfl⟩ | hJ'
    · exact ⟨G, fun p hp => hp, rfl⟩
    · exact hD J' ℓ hJ'
  | @block G D b₁ b₂ r₁ r₂ _ _ ihb ihr =>
    intro st code nv' nl' ip' hl hG
    simp only [lower] at hl
    split at hl
    · simp at hl
    · rename_i ℓ pend hpend
      split at hl
      · rename_i cr nv1 nl1 ip1 hlr
        obtain ⟨c', hl', rfl⟩ := prepend_ok hl
        have ihr' := ihr _ cr nv1 nl1 ip1 hlr hG
        have ihb' := ihb _ c' nv' nl' ip' hl'
          (fun p hp => by have := hG p hp; simp at ihr' ⊢; omega)
        refine ⟨by simp at ihr' ihb'; omega, ?_⟩
        intro k args acc m s σ hcode hD hP hA hR hI hw
        simp only [wp] at hw
        obtain ⟨rfl, hw⟩ := hw
        rw [hpend] at hP
        cases hP with
        | @cons J _ acc' _ hJ hP =>
          simp only at hw
          have hlab : (T.prog h)[k + cr.length]? = some (T.label (lname fn ℓ)) :=
            List.isInfixAt_singleton.mp ((hcode.append).1.append).2
          refine ihr'.2 k [] acc' m s σ ((hcode.append).1.append).1 hD hP hA hR hI (hw ?_)
          intro as m' hb
          rw [hJ]
          refine ⟨k + cr.length, hlab, fun s' σ' hA' hR' hI' => T.label_spec hlab ?_⟩
          have := ihb'.2 _ as [] m' s' σ' (hcode.append).2 hD .nil hA' hR' hI' hb
          simpa only [Target.Run, List.length_append, List.length_singleton, Nat.add_assoc]
            using this
      · simp at hl

end Lower

/-! ## Functions -/

private theorem region_slots_sep {a : Val} {n : Nat} {F : Mem 64 → Prop} {M : Mem 64}
    (hn : 8 * n ≤ 2 ^ 64) (h : (region a (8 * n) ⋆ F) M) :
    ∃ σ : List Val, σ.length = n ∧ (slots a σ ⋆ F) M := by
  obtain ⟨f1, f2, hu, hd, h1, h2⟩ := h
  obtain ⟨σ, hl, hσ⟩ := region_slots hn h1
  exact ⟨σ, hl, f1, f2, hu, hd, hσ, h2⟩

/-- The compiled function satisfies its source `wp` as a `FnSpec`. -/
theorem lowerFn_correct (h : T.Host) (hints : Hints T.toIsa) (E : Ext) (f : Fn) (Γ : Env)
    (bound : String → Nat) (n nX : Nat) (code : List T.Directive) (k₀ : Nat)
    (hlow : lowerFn hints E f = .ok code) (hcode : code.IsInfixAt (T.prog h) k₀)
    (hu : T.LabelsUnique h) (hwf : Func.Wf f.body)
    (hFn : frame hints ≤ n) (hn : n + T.raBytes ≤ 2 ^ 64)
    (hcallees : ∀ g ∈ E.callees,
      T.FnSpec h g (Γ g) (bound g) nX ∧ frame hints + T.raBytes + bound g ≤ n)
    (hexits : ∀ g ∈ E.exits, T.Defined h g ∧ nX ≤ n) :
    T.FnSpec h f.name (Func.spec Γ f.body) n nX := by
  unfold lowerFn at hlow
  split at hlow
  · rename_i c nv' nl' ip' hl
    simp only [Except.ok.injEq] at hlow
    subst hlow
    have hlab := (hcode.cons).1
    have hpro := (hcode.cons).2.append.1
    have hc := (hcode.cons).2.append.2
    intro args m Q X hspec s₀ ra Rf hargs hra hspE hmem
    rw [labelAddr_of_unique hu hlab]
    refine T.label_spec hlab ?_
    have hy : Hyps h hints E Γ s₀ n nX bound :=
      ⟨hu, hspE, hFn, by omega, hn, hcallees, hexits⟩
    have e_n : n = n - frame hints + frame hints := by omega
    have hmem1 : T.mem s₀ =⋆ T.RetAddr (T.get s₀ T.sp) ra ⋆
        region (base hints s₀) (frame hints) ⋆
        (Eq m ⋆ (region (T.get s₀ T.sp - BitVec.ofNat 64 n) (n - frame hints) ⋆ Rf)) := by
      simp only [Target.Entry] at hmem
      conv at hmem => arg 1; arg 2; arg 1; arg 2; rw [e_n]
      rw [region_split (by omega), below_add hFn] at hmem
      exact sep_ac' (by ac_rfl) hmem
    refine T.prologue_spec hpro hra hspE hy.frame_bound hmem1
      fun s1 hsp1 hk1 hm1 => ?_
    have h8 : 8 * hints.nslots ≤ frame hints := T.slots_le_frameSize _
    have hm1' : (region (base hints s₀) (8 * hints.nslots) ⋆
        (Eq m ⋆ Fr hints s₀ ra n Rf)) (T.mem s1) := by
      unfold Fr base frame
      exact sep_ac' (by ac_rfl) hm1
    obtain ⟨σ, hσ, hm1''⟩ := region_slots_sep (by omega) hm1'
    have hargs1 : T.ValsIn T.argRegs args s1 := by
      refine valsIn_keep (fun r hr => hk1 r ?_) hargs
      simp only [List.mem_cons, List.mem_append, not_or]
      exact ⟨⟨fun e => T.sp_not_argRegs (e ▸ hr), fun h' => T.raRegs_not_argRegs r h' hr⟩,
        T.argRegs_not_scratch r hr⟩
    have hI1 : Inv hints s₀ ra n Rf m s1 σ := by
      refine ⟨hσ, hsp1, fun r hr => hk1 r ?_, sep_ac' (by ac_rfl) hm1''⟩
      simp only [List.mem_cons, List.mem_append, not_or]
      exact ⟨⟨fun e => T.sp_not_calleeSaved (e ▸ hr), fun h' => T.raRegs_not_calleeSaved r h' hr⟩,
        T.calleeSaved_not_scratch r hr⟩
    exact (lower_correct h hints E f.name Γ Q X s₀ ra n nX Rf bound hy
      (hwf Val Nat Cont Nat) (St.init T.toIsa) c nv' nl' ip' hl (by simp)).2
      (k₀ + 1 + (T.prologue hints.nslots).length) args [] m s1 σ hc
      (fun _ _ hJ => by simp at hJ) .nil (fun _ _ hx => by simp [St.init] at hx)
      hargs1 hI1 hspec
  · simp at hlow

end Rega
end LeanQbe
