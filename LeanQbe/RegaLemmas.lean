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

@[simp] theorem locEq_eq_true {I : Isa} {a b : Loc I} : locEq a b = true ↔ a = b := by
  cases a <;> cases b <;> simp [locEq]

@[simp] theorem locEq_eq_false {I : Isa} {a b : Loc I} : locEq a b = false ↔ a ≠ b := by
  rw [← Bool.not_eq_true, locEq_eq_true]

@[simp] theorem argNatEq_eq_true {a b : Arg Nat} : argNatEq a b = true ↔ a = b := by
  cases a <;> cases b <;> simp [argNatEq]

@[simp] theorem argNatEq_eq_false {a b : Arg Nat} : argNatEq a b = false ↔ a ≠ b := by
  rw [← Bool.not_eq_true, argNatEq_eq_true]

@[simp] theorem symRegMem_eq_true {I : Isa} {t : Arg Nat × Loc I} {R : SymRegs I} :
    symRegMem t R = true ↔ t ∈ R := by
  simp [symRegMem]

theorem lookup_mem {I : Isa} {R : SymRegs I} {x : Nat} {r : I.Reg} (h : lookup R x = some r) :
    (.var x, .reg r) ∈ R := by
  unfold lookup at h
  obtain ⟨⟨a, l⟩, hp, hf⟩ := List.exists_of_findSome?_eq_some h
  by_cases ha : a = .var x
  · grind
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
    simp only [argNatEq_eq_true] at hx
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
  cases hr <;> simp only [opRegs] at h <;> split at h <;> try contradiction
  all_goals
    simp only [Option.some.injEq] at h; subst h
    first
    | (rename_i a' b' ha' hb'
       obtain ⟨e1, s1⟩ := argReg_ok hA (by assumption) ha'
       obtain ⟨e2, s2⟩ := argReg_ok hA (by assumption) hb'
       exact ⟨by simp only [Op.map, e1, e2], fun r hr =>
         (List.mem_append.mp (by simpa [Op.vars] using hr)).elim (s1 r) (s2 r)⟩)
    | (rename_i a' ha'
       obtain ⟨e1, s1⟩ := argReg_ok hA (by assumption) ha'
       exact ⟨by simp only [Op.map, e1], fun r hr => s1 r (by simpa [Op.vars] using hr)⟩)

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

theorem Agree.afterCall {G : List (Val × Nat)} {saved : List T.Reg} {R : SymRegs T.toIsa}
    {s s' : T.MData} {σ : List Val} (hA : Agree G R s σ)
    (hcs : ∀ r ∈ T.calleeSaved, T.get s' r = T.get s r) (hsub : ∀ r ∈ saved, r ∈ T.calleeSaved) :
    Agree G (Rega.afterCall saved R) s' σ := by
  intro a l hx a₁ hv
  simp only [Rega.afterCall, List.mem_filter] at hx
  cases l with
  | reg r =>
    simp only [decide_eq_true_eq] at hx
    show T.get s' r = a₁.val
    rw [hcs r (hsub r hx.2)]
    exact hA _ _ hx.1 _ hv
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
  simp only [Rega.bindN, List.mem_cons, List.mem_filter, Prod.mk.injEq, Bool.not_eq_true',
    argNatEq_eq_false, ne_eq] at hy
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

theorem Agree.dropVar {G : List (Val × Nat)} {R : SymRegs T.toIsa} {s : T.MData} {σ : List Val}
    (v : Val) (x : Nat) (hA : Agree G R s σ) :
    Agree ((v, x) :: G) (R.filter (fun p => !argNatEq p.1 (.var x))) s σ := by
  intro a l hx a₁ ha
  simp only [List.mem_filter, Bool.not_eq_true', argNatEq_eq_false, ne_eq] at hx
  exact hA a l hx.1 a₁ (ha.uncons hx.2)

/-- Take hypothesis `h` apart at every `match` and `if`, closing `.error _ = .ok _` branches. -/
macro "invert_ok " h:ident : tactic =>
  `(tactic| repeat' (first | contradiction | (split at $h:ident)))

theorem CmpOp.eval_neg {n : Nat} (co : CmpOp) (a b : BitVec n) :
    co.neg.eval a b = !co.eval a b := by
  cases co <;> simp [CmpOp.neg, CmpOp.eval] <;> grind

theorem eval_cmp_neg {cls : Cls} {co : CmpOp} {a b : Arg Val} {v : Val}
    (h : (Op.cmp cls co a b).eval = some v) :
    ∃ v', (Op.cmp cls co.neg a b).eval = some v' ∧ (Truthy v' ↔ ¬ Truthy v) := by
  cases cls <;> simp only [Op.eval, Option.some.injEq] at h <;> subst h
  · refine ⟨_, rfl, ?_⟩
    rw [CmpOp.eval_neg]
    cases co.eval (lo32 a.val) (lo32 b.val) <;> decide
  · refine ⟨_, rfl, ?_⟩
    rw [CmpOp.eval_neg]
    cases co.eval a.val b.val <;> decide

theorem eval_cmp_truthy (v : Val) :
    ∃ v', (Op.cmp .w .ne (.var v) (.imm 0)).eval = some v' ∧ (Truthy v' ↔ Truthy v) := by
  refine ⟨_, rfl, ?_⟩
  simp only [Truthy, CmpOp.eval, Arg.val, lo32]
  by_cases h : v.setWidth 32 = 0#32 <;> simp [h, boolVal]

theorem stepPre_some {I : Isa} {h : Hints I} {st : St I} {R : SymRegs I}
    (hs : stepPre h st = some R) :
    st.pend = [] ∧ execMoves h.nslots h.saved (h.pre st.ip) st.R = some R := by
  unfold stepPre at hs
  split at hs
  · exact ⟨List.isEmpty_iff.mp ‹_›, hs⟩
  · contradiction

theorem finishJnz_nv {I : Isa} {fn : String} {nl : Nat} {inv : Bool} {tgt? : Option Nat}
    {t e : Expr Nat Nat} {br ce ct c : List I.Directive} {nv2 nl2 ip2 nv' nl' ip' : Nat}
    (hf : finishJnz I fn nl inv tgt? t e br ce ct nv2 nl2 ip2 = .ok (c, nv', nl', ip')) :
    nv2 = nv' := by
  unfold finishJnz finishJnzBranch at hf
  invert_ok hf
  all_goals (simp only [Except.ok.injEq, Prod.mk.injEq] at hf; exact hf.2.1)

theorem mem_copyTo {I : Isa} {l d : Loc I} {R : SymRegs I} {a : Arg Nat} {l' : Loc I}
    (h : (a, l') ∈ copyTo l d R) : l' = d ∧ (a, l) ∈ R := by
  simp only [copyTo, List.mem_map, List.mem_filter, locEq_eq_true] at h
  grind

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
    · simp only [List.mem_filter, Bool.not_eq_true', locEq_eq_false] at hx
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
    grind

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
    grind
  · refine (hA.clob (d := some d) (fun r h1 h2 => hs r ?_)) _ _ hx _ ha
    grind

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
  · simp only [List.mem_filter, Bool.not_eq_true', locEq_eq_false] at hx'
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

/-- Bytes of the frame (spill slots + saved callee-saved registers). -/
abbrev frame : Nat := T.frameSize hints.totalSlots

/-- Address of slot 0: the entry stack pointer minus the frame. -/
abbrev base : Val := T.get s₀ T.sp - BitVec.ofNat 64 (frame hints)

/-- Saved callee-saved registers at slots `hints.nslots .. hints.nslots + hints.saved.length - 1`. -/
def csSlots : Mem 64 → Prop :=
  slots (base hints s₀ + BitVec.ofNat 64 (8 * hints.nslots)) (hints.saved.map (T.get s₀))

/-- What surrounds the slots: saved callee-saved regs, frame overhead, stack left for callees, caller's frame. -/
def Fr : Mem 64 → Prop :=
  csSlots hints s₀ ⋆
    (T.Saved (T.get s₀ T.sp) ra hints.totalSlots ⋆
      (region (T.get s₀ T.sp - BitVec.ofNat 64 n) (n - frame hints) ⋆ Rf))

/-- The frame invariant, with source memory `m` and slot contents `σ`. -/
def Inv (m : Mem 64) (s : T.MData) (σ : List Val) : Prop :=
  σ.length = hints.nslots ∧ T.get s T.sp = base hints s₀ ∧
  (∀ r, r ∈ T.calleeSaved → r ∉ hints.saved → T.get s r = T.get s₀ r) ∧
  (T.mem s =⋆ Eq m ⋆ (slots (base hints s₀) σ ⋆ Fr hints s₀ ra n Rf)) ∧
  (∀ r ∈ hints.saved, r ∈ T.calleeSaved) ∧ hints.saved.Nodup

end Frame

section
variable {hints : Hints T.toIsa} {s₀ : T.MData} {ra : T.Addr} {n : Nat} {Rf : Mem 64 → Prop}

theorem Inv.regs {s s' : T.MData} {m : Mem 64} {σ : List Val} (hI : Inv hints s₀ ra n Rf m s σ)
    (hm : T.mem s' = T.mem s)
    (hs : ∀ r, r ∉ T.allocatable → r ∉ hints.saved → r ∉ T.scratch → T.get s' r = T.get s r) :
    Inv hints s₀ ra n Rf m s' σ := by
  obtain ⟨hl, hsp, hcs, hmem, hsub, hnd⟩ := hI
  refine ⟨hl, ?_, fun r hr hns => ?_, hm ▸ hmem, hsub, hnd⟩
  · rw [hs _ T.sp_not_allocatable (fun h => T.sp_not_calleeSaved (hsub _ h)) T.sp_not_scratch]
    exact hsp
  · rw [hs r (T.calleeSaved_not_allocatable r hr) hns (T.calleeSaved_not_scratch r hr)]
    exact hcs r hr hns

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
  obtain ⟨-, hsp, -, hmem, -, -⟩ := hI
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
  obtain ⟨hl, hsp, hcs, -, hsub, hnd⟩ := hI
  refine ⟨by simp [hl], ?_, fun r hr hns => ?_, ?_, hsub, hnd⟩
  · rw [hs _ T.sp_not_scratch]; exact hsp
  · rw [hs r (T.calleeSaved_not_scratch r hr)]; exact hcs r hr hns
  · rw [slots_set σ i hi v]
    rw [hsp] at hmem
    unfold slotRest at hmem
    exact sep_ac' (by ac_rfl) hmem

end

/-- Writing an allocatable, saved, or scratch register `d` and the scratch registers. -/
theorem keeps_dest {s s' : T.MData} {saved : List T.Reg} {d : T.Reg}
    (hd : d ∈ T.allocatable ∨ d ∈ saved ∨ d ∈ T.scratch)
    (hs : ∀ r, r ∉ d :: T.scratch → T.get s' r = T.get s r) :
    ∀ r, r ∉ T.allocatable → r ∉ saved → r ∉ T.scratch → T.get s' r = T.get s r := by
  grind

theorem keeps_dest' {s s' : T.MData} {d : T.Reg}
    (hs : ∀ r, r ∉ d :: T.scratch → T.get s' r = T.get s r) :
    ∀ r, some r ≠ some d → r ∉ T.scratch → T.get s' r = T.get s r := by
  grind

theorem keeps_one {s s' : T.MData} {saved : List T.Reg} {d : T.Reg}
    (hd : d ∈ T.allocatable ∨ d ∈ saved ∨ d ∈ T.scratch)
    (hs : ∀ r, r ∉ [d] → T.get s' r = T.get s r) :
    ∀ r, r ∉ T.allocatable → r ∉ saved → r ∉ T.scratch → T.get s' r = T.get s r := by
  grind

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
    execMoves hints.nslots hints.saved mvs R = some R' → (movesCode mvs).IsInfixAt (T.prog h) k →
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
    (hs : shuffle hints.nslots hints.saved R tgts = some (c, R')) (hc : c.IsInfixAt (T.prog h) k)
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
      simp only [List.all_eq_true, symRegMem_eq_true] at hall
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

/-- Every join point in scope is defined in `h` and is a `LabJ` of an earlier context. -/
def DOk (G : List (Val × Nat)) (D : List (Cont × Nat)) : Prop :=
  ∀ J ℓ, (J, ℓ) ∈ D → (∃ k : Nat, (T.prog h)[k]? = some (T.label (lname fn ℓ))) ∧
    ∃ G', (∀ p ∈ G', p ∈ G) ∧ J = LabJ h hints fn Q X s₀ ra n nX Rf G' ℓ

end Ctx

theorem DOk.cons {h : T.Host} {hints : Hints T.toIsa} {fn : String} {Q : LeanQbe.Post}
    {X : XPost} {s₀ : T.MData} {ra : T.Addr} {n nX : Nat} {Rf : Mem 64 → Prop}
    {G : List (Val × Nat)} {D : List (Cont × Nat)}
    (hD : DOk h hints fn Q X s₀ ra n nX Rf G D) (p : Val × Nat) :
    DOk h hints fn Q X s₀ ra n nX Rf (p :: G) D := by
  intro J ℓ hJ
  obtain ⟨hdef, G', hG', rfl⟩ := hD J ℓ hJ
  exact ⟨hdef, G', fun q hq => List.mem_cons_of_mem _ (hG' q hq), rfl⟩

/-! ## Leaving the frame: `ret` and `exit` -/

section Leave
variable {h : T.Host} {hints : Hints T.toIsa} {E : Ext} {Γ : Env} {Q : LeanQbe.Post}
  {X : XPost} {s₀ : T.MData} {ra : T.Addr} {n nX : Nat} {Rf : Mem 64 → Prop} {bound : String → Nat}

theorem base_add_frame : base hints s₀ + BitVec.ofNat 64 (frame hints) = T.get s₀ T.sp :=
  BitVec.sub_add_cancel _ _

theorem below_add (hFn : frame hints ≤ n) :
    T.get s₀ T.sp - BitVec.ofNat 64 n + BitVec.ofNat 64 (n - frame hints) = base hints s₀ := by
  grind

private theorem add_ofNat_8 (x : BitVec 64) (i : Nat) :
    x + BitVec.ofNat 64 (8 * i) + 8#64 = x + BitVec.ofNat 64 (8 * (i + 1)) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.mul_add, Nat.mul_one]

theorem saveCs_ok {h : T.Host} {post : T.State → Prop} {s₀ : T.MData} {G : Mem 64 → Prop} :
    ∀ (i : Nat) (rs : List T.Reg) (k : Nat) (s : T.MData),
    (saveCs i rs).IsInfixAt (T.prog h) k → T.spOk (T.get s T.sp) → 8 * rs.length ≤ 2 ^ 64 →
    (∀ r ∈ rs, r ∈ T.calleeSaved) → (∀ r ∈ rs, T.get s r = T.get s₀ r) →
    (T.mem s =⋆ region (T.get s T.sp + BitVec.ofNat 64 (8 * i)) (8 * rs.length) ⋆ G) →
    (∀ s', (∀ r, r ∉ T.scratch → T.get s' r = T.get s r) →
      (T.mem s' =⋆ slots (T.get s T.sp + BitVec.ofNat 64 (8 * i)) (rs.map (T.get s₀)) ⋆ G) →
      T.Run h (k + (saveCs i rs).length) s' post) →
    T.Run h k s post
  | _, [], _, s, _, _, _, _, _, hmem, kont => by
    simp only [List.length_nil, Nat.mul_zero, region_zero] at hmem ⊢
    exact kont s (fun _ _ => rfl) hmem
  | i, r :: rs, k, s, hc, hsp, hlen, hsub, hvals, hmem, kont => by
    simp only [saveCs] at hc
    have hsplit : 8 * (r :: rs).length = 8 + 8 * rs.length := by
      simp [List.length_cons, Nat.mul_add]; omega
    have hmem1 : T.mem s =⋆ region (T.get s T.sp + BitVec.ofNat 64 (8 * i)) 8 ⋆
        (region (T.get s T.sp + BitVec.ofNat 64 (8 * (i + 1))) (8 * rs.length) ⋆ G) := by
      rw [hsplit, region_split (by rw [← hsplit]; exact hlen), add_ofNat_8] at hmem
      exact sep_ac' (by ac_rfl) hmem
    have hr_cs : r ∈ T.calleeSaved := hsub r List.mem_cons_self
    refine T.slotSt_spec (hc.append).1 (T.calleeSaved_not_scratch r hr_cs) hsp hmem1
      fun s1 hs1 hm1 => ?_
    have hsp1 : T.get s1 T.sp = T.get s T.sp := hs1 T.sp T.sp_not_scratch
    have hmem2 : T.mem s1 =⋆ region (T.get s1 T.sp + BitVec.ofNat 64 (8 * (i + 1))) (8 * rs.length) ⋆
        (word (T.get s T.sp + BitVec.ofNat 64 (8 * i)) (T.get s₀ r) ⋆ G) := by
      rw [hvals r List.mem_cons_self] at hm1
      rw [hsp1]
      exact sep_ac' (by ac_rfl) hm1
    refine saveCs_ok (i + 1) rs (k + (T.slotSt i r).length) s1 (hc.append).2 (hsp1 ▸ hsp)
      (by simp only [List.length_cons, Nat.mul_add] at hlen; omega)
      (fun q hq => hsub q (List.mem_cons_of_mem _ hq))
      (fun q hq => (hs1 q (T.calleeSaved_not_scratch q (hsub q (List.mem_cons_of_mem _ hq)))).trans
        (hvals q (List.mem_cons_of_mem _ hq)))
      hmem2 fun s' hs' hm' => ?_
    have hm'_final : T.mem s' =⋆
        slots (T.get s T.sp + BitVec.ofNat 64 (8 * i)) ((r :: rs).map (T.get s₀)) ⋆ G := by
      rw [hsp1] at hm'
      simp only [List.map_cons, slots_cons]
      rw [add_ofNat_8]
      exact sep_ac' (by ac_rfl) hm'
    have hkeep : ∀ q, q ∉ T.scratch → T.get s' q = T.get s q :=
      fun q hq => (hs' q hq).trans (hs1 q hq)
    simpa [saveCs, Nat.add_assoc] using kont s' hkeep hm'_final

theorem restoreCs_ok {h : T.Host} {post : T.State → Prop} {s₀ : T.MData} {G : Mem 64 → Prop} :
    ∀ (i : Nat) (rs : List T.Reg) (k : Nat) (s : T.MData),
    (restoreCs i rs).IsInfixAt (T.prog h) k → T.spOk (T.get s T.sp) →
    rs.Nodup → (∀ r ∈ rs, r ∈ T.calleeSaved) →
    (T.mem s =⋆ slots (T.get s T.sp + BitVec.ofNat 64 (8 * i)) (rs.map (T.get s₀)) ⋆ G) →
    (∀ s', (∀ r ∈ rs, T.get s' r = T.get s₀ r) →
      (∀ r, r ∉ rs → r ∉ T.scratch → T.get s' r = T.get s r) →
      T.mem s' = T.mem s →
      T.Run h (k + (restoreCs i rs).length) s' post) →
    T.Run h k s post
  | _, [], _, s, _, _, _, _, _, kont => by
    simpa only [restoreCs, List.length_nil, Nat.add_zero] using kont s (fun _ hr => nomatch hr) (fun _ _ _ => rfl) rfl
  | i, r :: rs, k, s, hc, hsp, hnd, hsub, hmem, kont => by
    simp only [restoreCs] at hc
    obtain ⟨hr_notin, hnd_rs⟩ := List.nodup_cons.mp hnd
    have hr_cs : r ∈ T.calleeSaved := hsub r List.mem_cons_self
    have hmem1 : T.mem s =⋆ word (T.get s T.sp + BitVec.ofNat 64 (8 * i)) (T.get s₀ r) ⋆
        (slots (T.get s T.sp + BitVec.ofNat 64 (8 * (i + 1))) (rs.map (T.get s₀)) ⋆ G) := by
      simp only [List.map_cons, slots_cons] at hmem
      rw [← add_ofNat_8]
      exact sep_ac' (by ac_rfl) hmem
    refine T.slotLd_spec (hc.append).1 hsp hmem1 fun s1 hd1 hs1 hm1 => ?_
    have hsp1 : T.get s1 T.sp = T.get s T.sp := by
      refine hs1 T.sp ?_
      simp only [List.mem_cons, not_or]
      exact ⟨fun e => T.sp_not_calleeSaved (e ▸ hr_cs), T.sp_not_scratch⟩
    have hmem2 : T.mem s1 =⋆ slots (T.get s1 T.sp + BitVec.ofNat 64 (8 * (i + 1))) (rs.map (T.get s₀)) ⋆
        (word (T.get s T.sp + BitVec.ofNat 64 (8 * i)) (T.get s₀ r) ⋆ G) := by
      rw [hm1, hsp1]
      exact sep_ac' (by ac_rfl) hmem1
    refine restoreCs_ok (i + 1) rs (k + (T.slotLd r i).length) s1 (hc.append).2 (hsp1 ▸ hsp)
      hnd_rs (fun q hq => hsub q (List.mem_cons_of_mem _ hq)) hmem2 fun s' hrest_rs hkeep_rs hm' => ?_
    have hrest : ∀ q ∈ r :: rs, T.get s' q = T.get s₀ q := by
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact (hkeep_rs q hr_notin (T.calleeSaved_not_scratch q hr_cs)).trans hd1
      · exact hrest_rs q hq
    have hkeep : ∀ q, q ∉ r :: rs → q ∉ T.scratch → T.get s' q = T.get s q := by
      grind
    simpa [restoreCs, Nat.add_assoc] using kont s' hrest hkeep (hm'.trans hm1)

/-- Put the frame back together: what the epilogue leaves is the caller's `Entry` footprint. -/
theorem frame_close (hy : Hyps h hints E Γ s₀ n nX bound) {m : Mem 64} {M : Mem 64}
    (hM : M =⋆ T.RetAddr (T.get s₀ T.sp) ra ⋆
      region (base hints s₀ + BitVec.ofNat 64 (8 * hints.totalSlots))
        (frame hints - 8 * hints.totalSlots) ⋆
      (Eq m ⋆ (region (base hints s₀) (8 * hints.totalSlots) ⋆
        (region (T.get s₀ T.sp - BitVec.ofNat 64 n) (n - frame hints) ⋆ Rf)))) :
    M =⋆ Eq m ⋆ (T.Entry (T.get s₀ T.sp) ra n ⋆ Rf) := by
  have h8 : 8 * hints.totalSlots ≤ frame hints := T.slots_le_frameSize _
  have hF := hy.frame_bound
  have hFn := hy.frame_le
  have hn := hy.stack_bound
  -- the slots and the padding are the frame
  have h3 : M =⋆ (region (base hints s₀) (8 * hints.totalSlots) ⋆
      region (base hints s₀ + BitVec.ofNat 64 (8 * hints.totalSlots))
        (frame hints - 8 * hints.totalSlots)) ⋆
      (T.RetAddr (T.get s₀ T.sp) ra ⋆
        (Eq m ⋆ (region (T.get s₀ T.sp - BitVec.ofNat 64 n) (n - frame hints) ⋆ Rf))) :=
    sep_ac' (by ac_rfl) hM
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

/-- Merge spill slots and saved callee-saved register slots into the full slot region. -/
private theorem slots_merge_cs (hy : Hyps h hints E Γ s₀ n nX bound) {σ : List Val}
    (hσ : σ.length = hints.nslots) {M : Mem 64} {G : Mem 64 → Prop}
    (hM : M =⋆ slots (base hints s₀) σ ⋆ (csSlots hints s₀ ⋆ G)) :
    M =⋆ region (base hints s₀) (8 * hints.totalSlots) ⋆ G := by
  have h8 : 8 * hints.totalSlots ≤ frame hints := T.slots_le_frameSize _
  have hF := hy.frame_bound
  have e : 8 * hints.totalSlots = 8 * hints.nslots + 8 * hints.saved.length := by
    simp [Hints.totalSlots, Nat.mul_add]
  have h1 : M =⋆ region (base hints s₀) (8 * hints.nslots) ⋆ (csSlots hints s₀ ⋆ G) := by
    have := sep_mono (P := slots (base hints s₀) σ)
      (P' := region (base hints s₀) (8 * σ.length))
      (fun _ hs => slots_region (by rw [hσ]; omega) hs) hM
    rwa [hσ] at this
  have h1' : M =⋆ csSlots hints s₀ ⋆ (region (base hints s₀) (8 * hints.nslots) ⋆ G) :=
    sep_ac' (by ac_rfl) h1
  have h2 : M =⋆ region (base hints s₀ + BitVec.ofNat 64 (8 * hints.nslots)) (8 * hints.saved.length) ⋆
      (region (base hints s₀) (8 * hints.nslots) ⋆ G) := by
    have := sep_mono (P := csSlots hints s₀)
      (P' := region (base hints s₀ + BitVec.ofNat 64 (8 * hints.nslots))
        (8 * (hints.saved.map (T.get s₀)).length))
      (fun _ hs => slots_region (by simp only [List.length_map]; omega) hs) h1'
    simpa only [List.length_map] using this
  have h3 : M =⋆ (region (base hints s₀) (8 * hints.nslots) ⋆
      region (base hints s₀ + BitVec.ofNat 64 (8 * hints.nslots)) (8 * hints.saved.length)) ⋆ G :=
    sep_ac' (by ac_rfl) h2
  rw [← region_split (by omega), ← e] at h3
  exact h3

/-- The epilogue, from the restored slot region. -/
theorem epilogue_ok (hy : Hyps h hints E Γ s₀ n nX bound) {post : T.State → Prop}
    {k : Nat} {s : T.MData} {m : Mem 64}
    (hc : (T.epilogue hints.totalSlots).IsInfixAt (T.prog h) k)
    (hsp : T.get s T.sp = base hints s₀)
    (hmem : T.mem s =⋆ Eq m ⋆ (region (base hints s₀) (8 * hints.totalSlots) ⋆
      (T.Saved (T.get s₀ T.sp) ra hints.totalSlots ⋆
        (region (T.get s₀ T.sp - BitVec.ofNat 64 n) (n - frame hints) ⋆ Rf))))
    (kont : ∀ s', T.get s' T.sp = T.get s₀ T.sp → T.raReg s' ra →
      (∀ r, r ∉ T.sp :: T.raRegs ++ T.scratch → T.get s' r = T.get s r) →
      (T.mem s' =⋆ Eq m ⋆ (T.Entry (T.get s₀ T.sp) ra n ⋆ Rf)) →
      T.Run h (k + (T.epilogue hints.totalSlots).length) s' post) :
    T.Run h k s post := by
  have hsp' : T.get s T.sp + BitVec.ofNat 64 (frame hints) = T.get s₀ T.sp := by
    rw [hsp]; exact base_add_frame
  refine T.epilogue_spec hc (by rw [hsp]; exact T.spOk_frame _ _ hy.spE) hy.frame_bound
    (G := Eq m ⋆ (region (base hints s₀) (8 * hints.totalSlots) ⋆
      (region (T.get s₀ T.sp - BitVec.ofNat 64 n) (n - frame hints) ⋆ Rf)))
    (by rw [hsp']; exact sep_ac' (by ac_rfl) hmem)
    fun s' hsp2 hra hk hm => kont s' (by rw [hsp2, hsp']) hra hk ?_
  rw [hsp', hsp] at hm
  exact frame_close hy hm

/-- `restoreCs; epilogue` before `ret` or `tailJmp`. -/
private theorem restoreCs_epilogue_ok (hy : Hyps h hints E Γ s₀ n nX bound) {k : Nat}
    {s : T.MData} {m : Mem 64} {σ : List Val} {tail : List T.Directive}
    (hc : (restoreCs hints.nslots hints.saved ++ T.epilogue hints.totalSlots ++ tail).IsInfixAt
      (T.prog h) k) (hI : Inv hints s₀ ra n Rf m s σ)
    (hk : ∀ s1 s2, (∀ r, r ∉ hints.saved → r ∉ T.scratch → T.get s1 r = T.get s r) →
      (∀ r, r ∈ hints.saved → T.get s1 r = T.get s₀ r) →
      (∀ r, r ∉ T.sp :: T.raRegs ++ T.scratch → T.get s2 r = T.get s1 r) →
      T.get s2 T.sp = T.get s₀ T.sp → T.raReg s2 ra →
      tail.IsInfixAt (T.prog h)
        (k + (restoreCs hints.nslots hints.saved).length +
          (T.epilogue hints.totalSlots).length) →
      (T.mem s2 =⋆ Eq m ⋆ (T.Entry (T.get s₀ T.sp) ra n ⋆ Rf)) →
      T.Run h (k + (restoreCs hints.nslots hints.saved).length +
        (T.epilogue hints.totalSlots).length) s2 (FnPost h Q X s₀ ra n nX Rf)) :
    T.Run h k s (FnPost h Q X s₀ ra n nX Rf) := by
  obtain ⟨hσ, hsp, _, hmem, hsub, hnd⟩ := hI
  unfold Fr at hmem
  have hmem_cs : T.mem s =⋆ slots (T.get s T.sp + BitVec.ofNat 64 (8 * hints.nslots))
      (hints.saved.map (T.get s₀)) ⋆
      (Eq m ⋆ (slots (base hints s₀) σ ⋆ (T.Saved (T.get s₀ T.sp) ra hints.totalSlots ⋆
        (region (T.get s₀ T.sp - BitVec.ofNat 64 n) (n - frame hints) ⋆ Rf)))) := by
    rw [hsp]; unfold csSlots at hmem; exact sep_ac' (by ac_rfl) hmem
  refine restoreCs_ok hints.nslots hints.saved k s hc.append.1.append.1
    (by rw [hsp]; exact T.spOk_frame _ _ hy.spE) hnd hsub hmem_cs
    fun s1 hrest1 hkeep1 hm1 => ?_
  have hsp1 : T.get s1 T.sp = base hints s₀ := by
    rw [hkeep1 T.sp (fun hs => T.sp_not_calleeSaved (hsub _ hs)) T.sp_not_scratch, hsp]
  have hmem1 : T.mem s1 =⋆ Eq m ⋆ (region (base hints s₀) (8 * hints.totalSlots) ⋆
      (T.Saved (T.get s₀ T.sp) ra hints.totalSlots ⋆
        (region (T.get s₀ T.sp - BitVec.ofNat 64 n) (n - frame hints) ⋆ Rf))) := by
    rw [hm1]
    have hm' := slots_merge_cs hy hσ (G := Eq m ⋆ (T.Saved (T.get s₀ T.sp) ra hints.totalSlots ⋆
        (region (T.get s₀ T.sp - BitVec.ofNat 64 n) (n - frame hints) ⋆ Rf)))
      (sep_ac' (by ac_rfl) hmem)
    exact sep_ac' (by ac_rfl) hm'
  refine epilogue_ok hy hc.append.1.append.2 hsp1 hmem1 fun s2 hsp2 hra2 hk2 hm2 =>
    hk s1 s2 hkeep1 hrest1 hk2 hsp2 hra2
      (by simpa only [List.length_append, Nat.add_assoc] using hc.append.2) hm2

/-- `restoreCs; epilogue; ret` with the return values in place. -/
theorem ret_ok (hy : Hyps h hints E Γ s₀ n nX bound) {k : Nat} {s : T.MData} {m : Mem 64}
    {σ : List Val} {rets : List Val}
    (hc : (restoreCs hints.nslots hints.saved ++ T.epilogue hints.totalSlots ++ T.ret).IsInfixAt
      (T.prog h) k)
    (hI : Inv hints s₀ ra n Rf m s σ) (hrets : T.ValsIn T.retRegs rets s) (hQ : Q rets m) :
    T.Run h k s (FnPost h Q X s₀ ra n nX Rf) := by
  have hcs := hI.2.2.1; have hsub := hI.2.2.2.2.1
  refine restoreCs_epilogue_ok hy hc hI fun s1 s2 hkeep1 hrest1 hk2 hsp2 hra2 htail hm2 => ?_
  have hcs1 : ∀ r, r ∈ T.calleeSaved → T.get s1 r = T.get s₀ r := fun r hr => by
    by_cases hrs : r ∈ hints.saved
    · exact hrest1 r hrs
    · exact (hkeep1 r hrs (T.calleeSaved_not_scratch r hr)).trans (hcs r hr hrs)
  have hrets1 : T.ValsIn T.retRegs rets s1 :=
    valsIn_keep (fun r hr => hkeep1 r (fun hs => T.calleeSaved_not_retRegs r (hsub _ hs) hr)
      (T.retRegs_not_scratch r hr)) hrets
  have hm2' : T.mem s2 =⋆ T.RetAddr (T.get s2 T.sp) ra ⋆
      (Eq m ⋆ (region (T.get s₀ T.sp - BitVec.ofNat 64 n) n ⋆ Rf)) := by
    rw [hsp2]; simp only [Target.Entry] at hm2; exact sep_ac' (by ac_rfl) hm2
  refine T.ret_spec htail hra2 hm2' fun s3 hk3 hsp3 hm3 => ?_
  have keep2 : ∀ r, r ≠ T.sp → r ∉ T.raRegs → r ∉ T.scratch → T.get s3 r = T.get s1 r := by grind
  refine Eventually.done _ (Or.inl ⟨T.pc_mk _ _, rets, m, hQ, ?_, ⟨?_, ?_⟩, ?_⟩)
  · rw [T.data_mk]
    refine valsIn_keep (fun r hr => keep2 r (fun e => T.sp_not_retRegs (e ▸ hr))
      (fun h' => T.raRegs_not_retRegs r h' hr) (T.retRegs_not_scratch r hr)) hrets1
  · intro r hr
    rw [T.data_mk, keep2 r (fun e => T.sp_not_calleeSaved (e ▸ hr))
      (fun h' => T.raRegs_not_calleeSaved r h' hr) (T.calleeSaved_not_scratch r hr)]
    exact hcs1 r hr
  · rw [T.data_mk, hsp3, hsp2]
  · rw [T.data_mk, hm3]; exact T.exit_of_entry_assoc hy.stack_bound hm2

/-- `restoreCs; epilogue; tailJmp g` with the arguments in place. -/
theorem exit_ok (hy : Hyps h hints E Γ s₀ n nX bound) {k : Nat} {s : T.MData} {m : Mem 64}
    {σ : List Val} {g : String} {as : List Val}
    (hc : (restoreCs hints.nslots hints.saved ++ T.epilogue hints.totalSlots ++
      T.tailJmp g).IsInfixAt (T.prog h) k)
    (hI : Inv hints s₀ ra n Rf m s σ) (hargs : T.ArgsIn as s) (hX : X g as m)
    (hg : g ∈ E.exits) :
    T.Run h k s (FnPost h Q X s₀ ra n nX Rf) := by
  have hsub := hI.2.2.2.2.1
  refine restoreCs_epilogue_ok hy hc hI fun s1 s2 hkeep1 _ hk2 hsp2 hra2 htail hm2 => ?_
  have hargs1 : T.ArgsIn as s1 := by
    unfold Target.ArgsIn at hargs ⊢
    exact valsIn_keep (fun r hr => hkeep1 r (fun hs => T.calleeSaved_not_argRegs r (hsub _ hs) hr)
      (T.argRegs_not_scratch r hr)) hargs
  refine T.tailJmp_spec htail fun s3 hk3 hm3 => ?_
  have hsp3 : T.get s3 T.sp = T.get s₀ T.sp := by rw [hk3 _ T.sp_not_scratch, hsp2]
  refine Eventually.done _ (Or.inr ⟨g, as, m, hX, (hy.exits g hg).1, T.pc_mk _ _, ?_, ?_, ra, n,
    Std.ExtHashMap.emp, (hy.exits g hg).2, hy.stack_bound, ?_, ?_⟩)
  · rw [T.data_mk]
    unfold Target.ArgsIn at hargs1 ⊢
    refine valsIn_keep (fun r hr => ?_) hargs1
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

section Main
variable {hints : Hints T.toIsa} {s₀ : T.MData} {ra : T.Addr} {n : Nat} {Rf : Mem 64 → Prop}

theorem Inv.mem {s s' : T.MData} {m m' : Mem 64} {σ : List Val}
    (hI : Inv hints s₀ ra n Rf m s σ)
    (hm : T.mem s' =⋆ Eq m' ⋆ (slots (base hints s₀) σ ⋆ Fr hints s₀ ra n Rf))
    (hs : ∀ r, r ∉ T.allocatable → r ∉ hints.saved → r ∉ T.scratch → T.get s' r = T.get s r) :
    Inv hints s₀ ra n Rf m' s' σ := by
  obtain ⟨hl, hsp, hcs, -, hsub, hnd⟩ := hI
  refine ⟨hl, ?_, fun r hr hns => ?_, hm, hsub, hnd⟩
  · rw [hs _ T.sp_not_allocatable (fun h => T.sp_not_calleeSaved (hsub _ h)) T.sp_not_scratch]
    exact hsp
  · rw [hs r (T.calleeSaved_not_allocatable r hr) hns (T.calleeSaved_not_scratch r hr)]
    exact hcs r hr hns

/-- The callee area below the frame: `b + raBytes` bytes right below the stack pointer. -/
theorem callee_split {b : Nat} (hb : frame hints + T.raBytes + b ≤ n) (hn : n ≤ 2 ^ 64) :
    region (T.get s₀ T.sp - BitVec.ofNat 64 n) (n - frame hints) =
      region (T.get s₀ T.sp - BitVec.ofNat 64 n) (n - frame hints - (b + T.raBytes)) ⋆
      region (base hints s₀ - BitVec.ofNat 64 T.raBytes - BitVec.ofNat 64 b) (b + T.raBytes) := by
  have e : n - frame hints = n - frame hints - (b + T.raBytes) + (b + T.raBytes) := by omega
  conv => lhs; rw [e]
  rw [region_split (by omega)]
  grind

end Main

theorem jnzCond_pend {I : Isa} {h : Hints I} {x : Nat} {st : St I} {fused : Fused I}
    {r : List I.Directive × SymRegs I × Cls × CmpOp × Arg I.Reg × Arg I.Reg}
    (hc : jnzCond h x st fused = some r) : st.pend = [] := by
  cases fused with
  | some p =>
    simp only [jnzCond] at hc; invert_ok hc; simp_all
  | none =>
    simp only [jnzCond] at hc
    cases hpre : stepPre h st with
    | none => simp [hpre] at hc
    | some _ => exact (stepPre_some hpre).1

theorem pend_mem {I : Isa} {h : Hints I} {E : Ext} {fn : String} :
    ∀ {e : Expr Nat Nat} {st : St I} {ft : Option Nat} {fused : Fused I}
      {c : List I.Directive} {nv' nl' ip' : Nat},
    lower h E fn e st ft fused = .ok (c, nv', nl', ip') →
    ∀ ℓ ∈ st.pend, I.label (lname fn ℓ) ∈ c
  | .label _, st, _, none, _, _, _, _, hl, ℓ, hℓ => by
    simp only [lower] at hl; exact pend_mem hl ℓ (List.mem_append_left [st.nl] hℓ)
  | .block _ _, st, _, none, _, _, _, _, hl, ℓ, hℓ => by
    simp only [lower] at hl; invert_ok hl
    rename_i ℓ₀ pend hpend _ cr nv1 nl1 ip1 hlr
    obtain ⟨_, _, rfl⟩ := prepend_ok hl; rw [hpend] at hℓ
    rcases List.mem_cons.mp hℓ with rfl | hℓ
    · simp
    · exact List.mem_append_left _ (List.mem_append_left _ (pend_mem hlr ℓ hℓ))
  | .jnz (.var x) _ _, st, _, fused, _, _, _, _, hl, _, hℓ => by
    simp only [lower] at hl
    cases hjc : jnzCond h x st fused with
    | none => simp [hjc] at hl
    | some _ => have := jnzCond_pend hjc; simp_all
  | .param _, _, _, none, _, _, _, _, hl, _, hℓ
  | .hlt, _, _, none, _, _, _, _, hl, _, hℓ => by
    simp only [lower] at hl; invert_ok hl; simp_all
  | .let_ _ _, st, _, none, _, _, _, _, hl, _, hℓ
  | .load _ _ _ _ _, st, _, none, _, _, _, _, hl, _, hℓ
  | .store _ _ _ _, st, _, none, _, _, _, _, hl, _, hℓ
  | .call _ _ _, st, _, none, _, _, _, _, hl, _, hℓ
  | .jnz (.imm _) _ _, st, _, none, _, _, _, _, hl, _, hℓ
  | .jump _ _, st, _, none, _, _, _, _, hl, _, hℓ
  | .ret _, st, _, none, _, _, _, _, hl, _, hℓ
  | .exit _ _, st, _, none, _, _, _, _, hl, _, hℓ => by
    simp only [lower] at hl
    cases hpre : stepPre h st with
    | none => simp [hpre] at hl
    | some _ => have := (stepPre_some hpre).1; simp_all

section Lower
variable {h : T.Host} {hints : Hints T.toIsa} {E : Ext} {fn : String} {Γ : Env}
  {Q : LeanQbe.Post} {X : XPost} {s₀ : T.MData} {ra : T.Addr} {n nX : Nat} {Rf : Mem 64 → Prop}
  {bound : String → Nat}

/-- Invariant for a fused comparison `(xf, cls, co, a', b')`. -/
def FusedOk (G : List (Val × Nat)) (s : T.MData) : Fused T.toIsa → Prop
  | none => True
  | some (xf, cls, co, a', b') =>
    (∀ r ∈ a'.vars ++ b'.vars, r ∉ T.scratch) ∧
    ∀ v, (v, xf) ∈ G → (Op.cmp cls co (a'.map (T.get s)) (b'.map (T.get s))).eval = some v

/-- Post-state agreement and frame invariant after a snippet that writes `v` to `d`. -/
theorem bind_post {G : List (Val × Nat)} {R1 : SymRegs T.toIsa} {x : Nat} {d : T.Reg} {v : Val}
    {m : Mem 64} {s1 s' : T.MData} {σ1 : List Val}
    (hG : ∀ p ∈ G, p.2 < x) (hda : d ∈ T.allocatable ∨ d ∈ hints.saved)
    (hA1 : Agree G R1 s1 σ1) (hI1 : Inv hints s₀ ra n Rf m s1 σ1)
    (hd' : T.get s' d = v) (hs' : ∀ r, r ∉ d :: T.scratch → T.get s' r = T.get s1 r)
    (hm' : T.mem s' = T.mem s1) :
    Agree ((v, x) :: G) (bindN x d (clob (some d) R1)) s' σ1 ∧
    Inv hints s₀ ra n Rf m s' σ1 :=
  ⟨(hA1.clob (keeps_dest' hs')).bindN hG hd',
   hI1.regs hm' (keeps_dest (hda.elim .inl (fun h => .inr (.inl h))) hs')⟩

/-- Shared instruction step for `let_`, `load`, and `store`: run `st.ip`'s pre-moves, run snippet
`c`, and continue with `c'` at the advanced program position. -/
theorem inst_step (hy : Hyps h hints E Γ s₀ n nX bound) {G : List (Val × Nat)}
    {st : St T.toIsa} {R1 : SymRegs T.toIsa} {c c' : List T.Directive} {ft : Option Nat}
    {k : Nat} {m : Mem 64} {s : T.MData} {σ : List Val}
    (hpre : stepPre hints st = some R1)
    (hcode : ((movesCode (hints.pre st.ip) ++ c) ++ c').IsInfixAt (T.prog h) k)
    (hft : ∀ ℓf, ft = some ℓf →
      (T.prog h)[k + ((movesCode (hints.pre st.ip) ++ c) ++ c').length]? =
        some (T.label (lname fn ℓf)))
    (hA : Agree G st.R s σ) (hI : Inv hints s₀ ra n Rf m s σ)
    (hsnip : ∀ s1 σ1, Agree G R1 s1 σ1 → Inv hints s₀ ra n Rf m s1 σ1 →
      c.IsInfixAt (T.prog h) (k + (movesCode (hints.pre st.ip)).length) →
      (∀ s',
        (∀ k', c'.IsInfixAt (T.prog h) k' →
          (∀ ℓf, ft = some ℓf → (T.prog h)[k' + c'.length]? = some (T.label (lname fn ℓf))) →
          T.Run h k' s' (FnPost h Q X s₀ ra n nX Rf)) →
        T.Run h (k + (movesCode (hints.pre st.ip)).length + c.length) s'
          (FnPost h Q X s₀ ra n nX Rf)) →
      T.Run h (k + (movesCode (hints.pre st.ip)).length) s1 (FnPost h Q X s₀ ra n nX Rf)) :
    T.Run h k s (FnPost h Q X s₀ ra n nX Rf) := by
  refine moves_ok hy.spE _ st.R R1 k s σ (stepPre_some hpre).2 hcode.append.1.append.1 hA hI
    fun s1 σ1 hA1 hI1 => hsnip s1 σ1 hA1 hI1 hcode.append.1.append.2 fun s' hcont => ?_
  simpa only [Target.Run, List.length_append, Nat.add_assoc] using
    hcont _ hcode.append.2 fun ℓf hf => by
      simpa [List.length_append, Nat.add_assoc] using hft ℓf hf

theorem jnzCond_ok (hy : Hyps h hints E Γ s₀ n nX bound) {G : List (Val × Nat)}
    {x : Nat} {v : Val} {st : St T.toIsa} {fused : Fused T.toIsa}
    {mvs : List T.Directive} {R : SymRegs T.toIsa} {cls : Cls} {co : CmpOp} {a' b' : Arg T.Reg}
    {k : Nat} {m : Mem 64} {s : T.MData} {σ : List Val} {post : T.State → Prop}
    (hcond : jnzCond hints x st fused = some (mvs, R, cls, co, a', b'))
    (hmvs : mvs.IsInfixAt (T.prog h) k) (hvx : (v, x) ∈ G)
    (hA : Agree G st.R s σ) (hI : Inv hints s₀ ra n Rf m s σ) (hfused : FusedOk G s fused)
    (kont : ∀ s1 σ1 v₁, Agree G R s1 σ1 → Inv hints s₀ ra n Rf m s1 σ1 →
      (∀ r ∈ a'.vars ++ b'.vars, r ∉ T.scratch) →
      (Op.cmp cls co (a'.map (T.get s1)) (b'.map (T.get s1))).eval = some v₁ →
      (Truthy v₁ ↔ Truthy v) →
      T.Run h (k + mvs.length) s1 post) :
    T.Run h k s post := by
  cases fused with
  | some p =>
    rcases p with ⟨xf, cls0, co0, a0, b0⟩
    simp only [jnzCond] at hcond; invert_ok hcond
    rename_i hchk
    simp only [Bool.and_eq_true, beq_iff_eq] at hchk
    rcases hchk with ⟨⟨rfl, _⟩, _⟩
    simp only [Option.some.injEq, Prod.mk.injEq] at hcond
    rcases hcond with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact kont s σ v hA hI hfused.1 (hfused.2 v hvx) Iff.rfl
  | none =>
    simp only [jnzCond] at hcond
    cases hpre : stepPre hints st with
    | none => simp [hpre] at hcond
    | some R1 =>
      rw [hpre] at hcond; dsimp only at hcond
      cases hrc : argReg R1 (.var x) with
      | none => simp [hrc] at hcond
      | some a1 =>
        cases a1 with
        | imm _ => simp [hrc] at hcond
        | var rc =>
          simp only [hrc, Option.some.injEq, Prod.mk.injEq] at hcond
          rcases hcond with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
          refine moves_ok hy.spE _ st.R R1 k s σ (stepPre_some hpre).2 hmvs hA hI
            fun s1 σ1 hA1 hI1 => ?_
          obtain ⟨e1, hsc⟩ := argReg_ok hA1 (.var hvx) hrc
          simp only [Arg.map] at e1
          obtain ⟨v₁, hv₁, htr₁⟩ := eval_cmp_truthy v
          refine kont s1 σ1 v₁ hA1 hI1 (fun r hr => ?_) (by simpa [Arg.map, e1] using hv₁) htr₁
          simp only [Arg.vars, List.append_nil] at hr
          exact hsc r hr

theorem finishJnzBranch_ok (hy : Hyps h hints E Γ s₀ n nX bound)
    {G : List (Val × Nat)} {D : List (Cont × Nat)}
    {nl : Nat} {tgt? : Option Nat} {ft : Option Nat}
    {b₁ : Expr Val Cont} {b₂ : Expr Nat Nat} (hwf_b : Wf G D b₁ b₂)
    {cls : Cls} {co' : CmpOp} {a' b' : Arg T.Reg}
    {br c_ft c_taken c' : List T.Directive} {nv2 nl2 ip2 nv' nl' ip' : Nat}
    {k' : Nat} {m : Mem 64} {s1 : T.MData} {σ1 : List Val} {R : SymRegs T.toIsa}
    {v' : Val} {P : Prop} {post : T.State → Prop}
    (hfin : finishJnzBranch T.toIsa fn nl tgt? b₂ br c_ft c_taken nv2 nl2 ip2 =
      .ok (c', nv', nl', ip'))
    (hc' : c'.IsInfixAt (T.prog h) k')
    (hft' : ∀ ℓf, ft = some ℓf → (T.prog h)[k' + c'.length]? = some (T.label (lname fn ℓf)))
    (hD : DOk h hints fn Q X s₀ ra n nX Rf G D)
    (hbr : T.jnzCmp cls co' a' b' (lname fn (tgt?.getD nl)) = some br)
    (hsc : ∀ r ∈ a'.vars ++ b'.vars, r ∉ T.scratch)
    (hv' : (Op.cmp cls co' (a'.map (T.get s1)) (b'.map (T.get s1))).eval = some v')
    (hP : Truthy v' ↔ P) (hA1 : Agree G R s1 σ1) (hI1 : Inv hints s₀ ra n Rf m s1 σ1)
    (ih_taken : ∀ k, c_taken.IsInfixAt (T.prog h) k →
      (∀ ℓf, (match tgt? with | some j => some j | none => ft) = some ℓf →
        (T.prog h)[k + c_taken.length]? = some (T.label (lname fn ℓf))) →
      ∀ s' σ', Agree G (clob none R) s' σ' → Inv hints s₀ ra n Rf m s' σ' → P →
        T.Run h k s' post)
    (ih_ft : ∀ k, c_ft.IsInfixAt (T.prog h) k →
      (∀ ℓf, (match tgt? with | some _ => ft | none => some nl) = some ℓf →
        (T.prog h)[k + c_ft.length]? = some (T.label (lname fn ℓf))) →
      ∀ s' σ', Agree G (clob none R) s' σ' → Inv hints s₀ ra n Rf m s' σ' → ¬ P →
        T.Run h k s' post) : T.Run h k' s1 post := by
  cases tgt? with
  | some j =>
    simp only [finishJnzBranch, Option.getD_some] at hfin hbr; invert_ok hfin
    rename_i j' as hchk
    simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hchk
    obtain ⟨rfl, rfl⟩ := hchk
    simp only [Except.ok.injEq, Prod.mk.injEq] at hfin; obtain ⟨rfl, -, -, -⟩ := hfin
    cases hwf_b with
    | jump hj _ =>
      obtain ⟨⟨k_j, hlab_j⟩, _⟩ := hD _ _ hj
      refine T.jnzCmp_spec hbr hc'.append.1 (labelAddr_of_unique hy.unique hlab_j) hsc hv'
        fun s' hs' hm' => ⟨fun ht => ih_taken k_j List.nil_prefix
          (fun ℓf hlf => by simp only [Option.some.injEq] at hlf; subst hlf; exact hlab_j)
          s' σ1 (hA1.clob (fun r _ h2 => hs' r h2)) (hI1.regs hm' (fun r _ _ h2 => hs' r h2))
          (hP.mp ht), fun hf => by
          simpa only [Target.Run, List.length_append, Nat.add_assoc] using
            ih_ft (k' + br.length) hc'.append.2
              (fun ℓf hlf => by simpa [List.length_append, Nat.add_assoc] using hft' ℓf hlf)
              s' σ1 (hA1.clob (fun r _ h2 => hs' r h2))
              (hI1.regs hm' (fun r _ _ h2 => hs' r h2)) (mt hP.mpr hf)⟩
  | none =>
    simp only [finishJnzBranch, Option.getD_none, Except.ok.injEq, Prod.mk.injEq] at hfin hbr
    obtain ⟨rfl, -, -, -⟩ := hfin; have hc1 := hc'.append.1
    have hlab : (T.prog h)[k' + br.length + c_ft.length]? = some (T.label (lname fn nl)) := by
      simpa [Nat.add_assoc] using List.isInfixAt_singleton.mp hc1.append.2
    refine T.jnzCmp_spec hbr hc1.append.1.append.1 (labelAddr_of_unique hy.unique hlab) hsc hv'
      fun s' hs' hm' => ⟨fun ht => T.label_spec hlab ?_, fun hf =>
        ih_ft (k' + br.length) hc1.append.1.append.2
          (fun ℓf hlf => by simp only [Option.some.injEq] at hlf; subst hlf; exact hlab)
          s' σ1 (hA1.clob (fun r _ h2 => hs' r h2)) (hI1.regs hm' (fun r _ _ h2 => hs' r h2))
          (mt hP.mpr hf)⟩
    have := ih_taken _ hc'.append.2
      (fun ℓf hlf => by
        simpa only [List.length_append, List.length_singleton, Nat.add_assoc,
          Nat.add_comm c_taken.length 1] using hft' ℓf hlf)
      s' σ1 (hA1.clob (fun r _ h2 => hs' r h2)) (hI1.regs hm' (fun r _ _ h2 => hs' r h2))
      (hP.mp ht)
    simpa only [Target.Run, List.length_append, List.length_singleton, Nat.add_assoc] using this

private theorem leave_step (hy : Hyps h hints E Γ s₀ n nX bound)
    {G : List (Val × Nat)} {st : St T.toIsa} {R1 R2 tgts : SymRegs T.toIsa}
    {c tail : List T.Directive}
    (hpre : stepPre hints st = some R1)
    (hsh : shuffle hints.nslots hints.saved R1 tgts = some (c, R2))
    {k : Nat} {m : Mem 64} {s : T.MData} {σ : List Val}
    (hcode : (movesCode (hints.pre st.ip) ++ c ++ restoreCs hints.nslots hints.saved ++
      T.epilogue hints.totalSlots ++ tail).IsInfixAt (T.prog h) k)
    (hA : Agree G st.R s σ) (hI : Inv hints s₀ ra n Rf m s σ)
    (hcont : ∀ s2 σ2, Holds G tgts s2 σ2 → Inv hints s₀ ra n Rf m s2 σ2 →
      (restoreCs hints.nslots hints.saved ++ T.epilogue hints.totalSlots ++ tail).IsInfixAt
        (T.prog h) (k + (movesCode (hints.pre st.ip)).length + c.length) →
      T.Run h (k + (movesCode (hints.pre st.ip)).length + c.length) s2
        (FnPost h Q X s₀ ra n nX Rf)) :
    T.Run h k s (FnPost h Q X s₀ ra n nX Rf) := by
  have hc1 := hcode.append.1.append.1.append.1
  refine moves_ok hy.spE _ st.R R1 k s σ (stepPre_some hpre).2 hc1.append.1 hA hI
    fun s1 σ1 hA1 hI1 => ?_
  refine shuffle_ok hy.spE hsh hc1.append.2 hA1 hI1 fun s2 σ2 ht _ hI2 => ?_
  have htail : (restoreCs hints.nslots hints.saved ++ T.epilogue hints.totalSlots ++ tail).IsInfixAt
      (T.prog h) (k + (movesCode (hints.pre st.ip)).length + c.length) := by
    rw [List.append_assoc (movesCode (hints.pre st.ip) ++ c),
      List.append_assoc (movesCode (hints.pre st.ip) ++ c)] at hcode
    simpa only [List.length_append, Nat.add_assoc] using hcode.append.2
  exact hcont s2 σ2 ht hI2 htail

variable (h hints E fn Γ Q X s₀ ra n nX Rf bound)

/-- Correctness of `lower`, for every term related by `Wf`. -/
theorem lower_correct (hy : Hyps h hints E Γ s₀ n nX bound) {G : List (Val × Nat)}
    {D : List (Cont × Nat)} {e₁ : Expr Val Cont} {e₂ : Expr Nat Nat} (hwf : Wf G D e₁ e₂) :
    ∀ (st : St T.toIsa) (code : List T.Directive) (nv' nl' ip' : Nat)
      (ft : Option Nat) (fused : Fused T.toIsa),
    lower hints E fn e₂ st ft fused = .ok (code, nv', nl', ip') →
    (∀ p ∈ G, p.2 < st.nv) →
    st.nv ≤ nv' ∧
    ∀ (k : Nat) (args : List Val) (acc : List Cont) (m : Mem 64) (s : T.MData) (σ : List Val),
    code.IsInfixAt (T.prog h) k →
    (∀ ℓf, ft = some ℓf → (T.prog h)[k + code.length]? = some (T.label (lname fn ℓf))) →
    DOk h hints fn Q X s₀ ra n nX Rf G D →
    Forall₂ (fun J ℓ => J = LabJ h hints fn Q X s₀ ra n nX Rf G ℓ) acc st.pend →
    Agree G st.R s σ → T.ValsIn st.PL args s → Inv hints s₀ ra n Rf m s σ →
    wp Γ Q X e₁ args acc m → FusedOk G s fused →
    T.Run h k s (FnPost h Q X s₀ ra n nX Rf) := by
  have fresh : ∀ {G : List (Val × Nat)} {n : Nat}, (∀ p ∈ G, p.2 < n) →
      ∀ v, ∀ p ∈ (v, n) :: G, p.2 < n + 1 := by grind
  have nilR : ∀ {s : T.MData}, T.ValsIn ([] : List T.Reg) [] s := by simp [Target.ValsIn]
  induction hwf with
  | @let_ G D op₁ op₂ k₁ k₂ hop _ ih =>
    intro st code nv' nl' ip' ft fused hl hG
    cases fused with
    | some _ => simp [lower] at hl
    | none =>
      simp only [lower] at hl; invert_ok hl
      · rename_i R1 hpre _ _ d o hd ho hda _ c hc
        obtain ⟨c', hl', rfl⟩ := prepend_ok hl
        have ih' := fun v => ih v st.nv _ c' nv' nl' ip' ft none hl' (fresh hG v)
        refine ⟨by have := (ih' 0).1; simp at this; omega,
          fun k args acc m s σ hcode hft hD _ hA _ hI hw _ => ?_⟩
        obtain ⟨rfl, v, hv, hw⟩ := hw
        refine inst_step hy hpre hcode hft hA hI fun s1 σ1 hA1 hI1 hcs hcont => ?_
        obtain ⟨e1, hsc⟩ := opRegs_ok hA1 hop ho
        refine T.op_spec hc hcs hsc (by rw [e1]; exact hv) fun s' hd' hs' hm' =>
          hcont s' fun k' hc' hft' => ?_
        obtain ⟨hA', hI'⟩ := bind_post hG hda hA1 hI1 hd' hs' hm'
        exact (ih' v).2 k' [] [] m s' σ1 hc' hft' (hD.cons _) .nil hA' nilR hI' hw trivial
      · rename_i R1 hpre _ _ cls co a' b' hd ho
        obtain ⟨c', hl', rfl⟩ := prepend_ok hl
        have ih' := fun v => ih v st.nv _ c' nv' nl' ip' ft
          (some (st.nv, cls, co, a', b')) hl' (fresh hG v)
        refine ⟨by have := (ih' 0).1; simp at this; omega,
          fun k args acc m s σ hcode hft hD _ hA _ hI hw _ => ?_⟩
        obtain ⟨rfl, v, hv, hw⟩ := hw
        refine moves_ok hy.spE _ st.R R1 k s σ (stepPre_some hpre).2 hcode.append.1 hA hI
          fun s1 σ1 hA1 hI1 => ?_
        obtain ⟨e1, hsc⟩ := opRegs_ok hA1 hop ho
        have := (ih' v).2 _ [] [] m s1 σ1 hcode.append.2
          (fun ℓf hf => by simpa [List.length_append, Nat.add_assoc] using hft ℓf hf)
          (hD.cons _) .nil (hA1.dropVar v st.nv) nilR hI1 hw
          ⟨fun r hr => hsc r (by simpa [Op.vars] using List.mem_append.mp hr),
            fun v' hv' => by
              have : v' = v := by grind
              subst this; rw [← Op.map, e1]; exact hv⟩
        simpa only [Target.Run, List.length_append, Nat.add_assoc] using this
  | @load G D cl sz sg a₁ a₂ k₁ k₂ ha _ ih =>
    intro st code nv' nl' ip' ft fused hl hG
    cases fused with
    | some _ => simp [lower] at hl
    | none =>
      simp only [lower] at hl; invert_ok hl
      rename_i R1 hpre _ _ d a' hd ha' hda _ c hc
      obtain ⟨c', hl', rfl⟩ := prepend_ok hl
      have ih' := fun v => ih v st.nv _ c' nv' nl' ip' ft none hl' (fresh hG v)
      refine ⟨by have := (ih' 0).1; simp at this; omega,
        fun k args acc m s σ hcode hft hD _ hA _ hI hw _ => ?_⟩
      obtain ⟨rfl, v, hv, hw⟩ := hw
      refine inst_step hy hpre hcode hft hA hI fun s1 σ1 hA1 hI1 hcs hcont => ?_
      obtain ⟨e1, hsc⟩ := argReg_ok hA1 ha ha'
      refine T.load_spec hc hcs hsc (by rw [e1]; exact loadVal_frame hI1.2.2.2.1 hv)
        fun s' hd' hs' hm' => hcont s' fun k' hc' hft' => ?_
      obtain ⟨hA', hI'⟩ := bind_post hG hda hA1 hI1 hd' hs' hm'
      exact (ih' v).2 k' [] [] m s' σ1 hc' hft' (hD.cons _) .nil hA' nilR hI' hw trivial
  | @store G D sz v₁ v₂ a₁ a₂ k₁ k₂ hv ha _ ih =>
    intro st code nv' nl' ip' ft fused hl hG
    cases fused with
    | some _ => simp [lower] at hl
    | none =>
      simp only [lower] at hl; invert_ok hl
      rename_i R1 hpre _ _ v' a' hv' ha' _ c hc
      obtain ⟨c', hl', rfl⟩ := prepend_ok hl
      have ih' := ih _ c' nv' nl' ip' ft none hl' hG
      refine ⟨ih'.1, fun k args acc m s σ hcode hft hD _ hA _ hI hw _ => ?_⟩
      obtain ⟨rfl, hok, hw⟩ := hw
      refine inst_step hy hpre hcode hft hA hI fun s1 σ1 hA1 hI1 hcs hcont => ?_
      obtain ⟨e1, s1v⟩ := argReg_ok hA1 hv hv'
      obtain ⟨e2, s2v⟩ := argReg_ok hA1 ha ha'
      refine T.store_spec hc hcs (fun r hr => (List.mem_append.mp hr).elim (s1v r) (s2v r))
        (by rw [e2]; exact storeOk_frame hI1.2.2.2.1 hok) fun s' hs' hm' =>
        hcont s' fun k' hc' hft' => ?_
      rw [e1, e2] at hm'
      exact ih'.2 k' [] [] _ s' σ1 hc' hft' hD .nil (hA1.clob (fun r _ h2 => hs' r h2)) nilR
        (hI1.mem (by rw [hm']; exact storeMem_frame hI1.2.2.2.1 hok _) (fun r _ _ h2 => hs' r h2))
        hw trivial
  | @call G D g as₁ as₂ k₁ k₂ has _ ih =>
    intro st code nv' nl' ip' ft fused hl hG
    cases fused with
    | some _ => simp [lower] at hl
    | none =>
      simp only [lower] at hl; invert_ok hl
      rename_i R1 hpre hcond _ c R2 hsh
      obtain ⟨c', hl', rfl⟩ := prepend_ok hl
      have ih' := ih _ c' nv' nl' ip' ft none hl' hG
      refine ⟨ih'.1, fun k args acc m s σ hcode hft hD _ hA _ hI hw _ => ?_⟩
      obtain ⟨rfl, P, E', hspec, hcont, hexit⟩ := hw
      obtain ⟨hf, hbound⟩ := hy.callees g hcond.1
      have hn' : n ≤ 2 ^ 64 := by have := hy.stack_bound; omega
      have hc1 := hcode.append.1
      refine moves_ok hy.spE _ st.R R1 k s σ (stepPre_some hpre).2 hc1.append.1.append.1 hA hI
        fun s1 σ1 hA1 hI1 => ?_
      refine shuffle_ok hy.spE hsh hc1.append.1.append.2 hA1 hI1 fun s2 σ2 hT2 hA2 hI2 => ?_
      have hargs : T.ArgsIn (as₁.map Arg.val) s2 := valsIn_of_holds has hcond.2 hT2
      have hm2 := hI2.2.2.2.1
      unfold Fr at hm2
      rw [callee_split hbound hn'] at hm2
      have hcall : (T.call g).IsInfixAt (T.prog h)
          (k + (movesCode (hints.pre st.ip)).length + c.length) := by
        simpa only [List.length_append, Nat.add_assoc] using hc1.append.2
      refine T.call_fnspec hcall hf hspec hargs
        (by rw [hI2.2.1]; exact T.spEntry_call _ _ hy.spE)
        (by have := hy.stack_bound; omega)
        (G := slots (base hints s₀) σ2 ⋆
          (csSlots hints s₀ ⋆
            (T.Saved (T.get s₀ T.sp) ra hints.totalSlots ⋆
              (region (T.get s₀ T.sp - BitVec.ofNat 64 n)
                (n - frame hints - (bound g + T.raBytes)) ⋆ Rf))))
        (by rw [hI2.2.1]; exact sep_ac' (by ac_rfl) hm2)
        (fun s' rets m' hP' hrets hcs' hsp' hm' => ?_)
        (fun st' sym' as' m' ra' n' F hE' hdef hpc has' hspE hnX hb hra' hmx => ?_)
      · have hI' : Inv hints s₀ ra n Rf m' s' σ2 :=
          ⟨hI2.1, hsp'.trans hI2.2.1, fun r hr hns => (hcs' r hr).trans (hI2.2.2.1 r hr hns),
            by
              rw [hI2.2.1] at hm'
              unfold Fr
              rw [callee_split hbound hn']
              exact sep_ac' (by ac_rfl) hm',
            hI2.2.2.2.2.1, hI2.2.2.2.2.2⟩
        have := ih'.2 _ rets [] m' s' σ2 hcode.append.2
          (fun ℓf hf => by simpa [List.length_append, Nat.add_assoc] using hft ℓf hf)
          hD .nil (hA2.afterCall hcs' hI2.2.2.2.2.1) hrets hI' (hcont rets m' hP') trivial
        simpa only [Target.Run, List.length_append, Nat.add_assoc] using this
      · refine Or.inr ⟨sym', as', m', hexit sym' as' m' hE', hdef, hpc, has', hspE, ra', n',
          F ⋆ (slots (base hints s₀) σ2 ⋆
            (csSlots hints s₀ ⋆
              (T.Saved (T.get s₀ T.sp) ra hints.totalSlots ⋆
                region (T.get s₀ T.sp - BitVec.ofNat 64 n)
                  (n - frame hints - (bound g + T.raBytes))))),
          hnX, hb, hra', sep_ac' (by ac_rfl) hmx⟩
  | @jnz G D c₁ c₂ t₁ t₂ e₁ e₂ hc hwf_t hwf_e iht ihe =>
    intro st code nv' nl' ip' ft fused hl hG
    cases hc with
    | imm c =>
      cases fused with
      | some _ => simp [lower] at hl
      | none =>
        simp only [lower] at hl; invert_ok hl
        · rename_i R1 hpre htr; obtain ⟨c', hl', rfl⟩ := prepend_ok hl
          have iht' := iht _ c' nv' nl' ip' ft none hl' hG
          refine ⟨iht'.1, fun k args acc m s σ hcode hft hD _ hA _ hI hw _ => ?_⟩
          obtain ⟨rfl, hwt, -⟩ := hw
          exact moves_ok hy.spE _ st.R R1 k s σ (stepPre_some hpre).2 hcode.append.1 hA hI
            fun s1 σ1 hA1 hI1 => iht'.2 _ [] [] m s1 σ1 hcode.append.2
              (fun ℓf hf => by simpa [List.length_append, Nat.add_assoc] using hft ℓf hf)
              hD .nil hA1 nilR hI1 (hwt htr) trivial
        · rename_i R1 hpre htr; obtain ⟨c', hl', rfl⟩ := prepend_ok hl
          have ihe' := ihe _ c' nv' nl' ip' ft none hl' hG
          refine ⟨ihe'.1, fun k args acc m s σ hcode hft hD _ hA _ hI hw _ => ?_⟩
          obtain ⟨rfl, -, hwe⟩ := hw
          exact moves_ok hy.spE _ st.R R1 k s σ (stepPre_some hpre).2 hcode.append.1 hA hI
            fun s1 σ1 hA1 hI1 => ihe'.2 _ [] [] m s1 σ1 hcode.append.2
              (fun ℓf hf => by simpa [List.length_append, Nat.add_assoc] using hft ℓf hf)
              hD .nil hA1 nilR hI1 (hwe htr) trivial
    | @var v x hvx =>
      simp only [lower] at hl
      cases hcond : jnzCond hints x st fused with
      | none => simp [hcond] at hl
      | some p =>
        rcases p with ⟨mvs, R, cls, co, a', b'⟩
        cases hm : jnzMode hints (clob none R) t₂ e₂ ft with
        | mk inv tgt? =>
          rw [hcond] at hl; dsimp only at hl; rw [hm] at hl; dsimp only at hl; invert_ok hl
          rename_i _ br hbr _ ce nv1 nl1 ip1 hle _ ct nv2 nl2 ip2 hlt
          obtain ⟨c', hfin, rfl⟩ := prepend_ok hl
          have hnv2 := finishJnz_nv hfin
          have ihe' := ihe _ ce nv1 nl1 ip1 _ none hle hG
          have iht' := iht _ ct nv2 nl2 ip2 _ none hlt
            (fun p hp => by have := hG p hp; have := ihe'.1; simp at *; omega)
          refine ⟨by have := ihe'.1; have := iht'.1; simp at *; omega,
            fun k args acc m s σ hcode hft hD _ hA _ hI hw hfused => ?_⟩
          obtain ⟨-, hwt, hwe⟩ := hw
          refine jnzCond_ok hy hcond hcode.append.1 hvx hA hI hfused
            fun s1 σ1 v₁ hA1 hI1 hsc hv₁ htr₁ => ?_
          have hft' : ∀ ℓf, ft = some ℓf →
              (T.prog h)[k + mvs.length + c'.length]? = some (T.label (lname fn ℓf)) :=
            fun ℓf hf => by simpa [List.length_append, Nat.add_assoc] using hft ℓf hf
          cases inv with
          | false =>
            exact finishJnzBranch_ok hy hwf_t hfin hcode.append.2 hft' hD hbr hsc hv₁ htr₁ hA1 hI1
              (fun k hc hft_t s' σ' hA' hI' ht =>
                iht'.2 k [] [] m s' σ' hc hft_t hD .nil hA' nilR hI' (hwt ht) trivial)
              (fun k hc hft_e s' σ' hA' hI' hf =>
                ihe'.2 k [] [] m s' σ' hc hft_e hD .nil hA' nilR hI' (hwe hf) trivial)
          | true =>
            obtain ⟨v₂, hv₂, htr₂⟩ := eval_cmp_neg hv₁
            exact finishJnzBranch_ok hy hwf_e hfin hcode.append.2 hft' hD hbr hsc hv₂
              (htr₂.trans (not_congr htr₁)) hA1 hI1
              (fun k hc hft_e s' σ' hA' hI' hf =>
                ihe'.2 k [] [] m s' σ' hc hft_e hD .nil hA' nilR hI' (hwe hf) trivial)
              (fun k hc hft_t s' σ' hA' hI' ht =>
                iht'.2 k [] [] m s' σ' hc hft_t hD .nil hA' nilR hI'
                  (hwt (Decidable.of_not_not ht)) trivial)
  | @jump G D j₁ j₂ as₁ as₂ hj has =>
    intro st code nv' nl' ip' ft fused hl hG
    cases fused with
    | some _ => simp [lower] at hl
    | none =>
      simp only [lower] at hl; invert_ok hl
      · rename_i R1 hpre hcond _ c R2 hsh hftj
        simp only [Except.ok.injEq, Prod.mk.injEq, List.append_nil] at hl
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hl
        refine ⟨Nat.le_refl _, fun k args acc m s σ hcode hft hD _ hA _ hI hw _ => ?_⟩
        obtain ⟨rfl, hw⟩ := hw
        obtain ⟨_, G', hG', rfl⟩ := hD _ _ hj
        obtain ⟨kℓ, hkℓ, hJ⟩ := hw
        have hlab := hft j₂ (beq_iff_eq.mp hftj)
        simp only [List.length_append, ← Nat.add_assoc] at hlab
        have hk_eq := hy.unique _ _ _ hlab hkℓ
        refine moves_ok hy.spE _ st.R R1 k s σ (stepPre_some hpre).2 hcode.append.1 hA hI
          fun s1 σ1 hA1 hI1 => ?_
        refine shuffle_ok hy.spE hsh hcode.append.2 hA1 hI1 fun s2 σ2 ht _ hI2 => ?_
        rw [hk_eq]
        refine hJ s2 σ2 (fun a l hx a₁ hv => ht a l (List.mem_append_left _ hx) a₁ (hv.mono hG'))
          (valsIn_of_holds (σ := σ2) has (by omega) fun a l hx a₁ hv =>
            ht a l (List.mem_append_right _ hx) a₁ hv) hI2
      · rename_i R1 hpre hcond _ c R2 hsh hftj
        simp only [Except.ok.injEq, Prod.mk.injEq] at hl
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hl
        have hnsc := List.all_eq_true.mp hcond.2
        refine ⟨Nat.le_refl _, fun k args acc m s σ hcode hft hD _ hA _ hI hw _ => ?_⟩
        obtain ⟨rfl, hw⟩ := hw
        obtain ⟨_, G', hG', rfl⟩ := hD _ _ hj
        obtain ⟨kℓ, hkℓ, hJ⟩ := hw
        have hc1 := hcode.append.1
        refine moves_ok hy.spE _ st.R R1 k s σ (stepPre_some hpre).2 hc1.append.1 hA hI
          fun s1 σ1 hA1 hI1 => ?_
        refine shuffle_ok hy.spE hsh hc1.append.2 hA1 hI1 fun s2 σ2 ht _ hI2 => ?_
        have hjmp : (T.jmp (lname fn j₂)).IsInfixAt (T.prog h)
            (k + (movesCode (hints.pre st.ip)).length + c.length) := by
          simpa only [List.length_append, Nat.add_assoc] using hcode.append.2
        refine T.jmp_spec hjmp (labelAddr_of_unique hy.unique hkℓ) fun s' hs' hm' => ?_
        have hloc : ∀ a l v, (a, l) ∈ (hints.entry j₂).live ++ tgtsIn as₂ (hints.entry j₂).ploc →
            LocHolds s2 σ2 l v → LocHolds s' σ2 l v := fun a l v hx h1 => by
          cases l with
          | reg r => simp only [LocHolds] at h1 ⊢; rw [hs' r (of_decide_eq_true (hnsc _ hx)), h1]
          | slot _ => exact h1
        exact hJ s' σ2
          (fun a l hx a₁ hv => hloc a l _ (List.mem_append_left _ hx)
            (ht a l (List.mem_append_left _ hx) a₁ (hv.mono hG')))
          (valsIn_of_holds (σ := σ2) has (by omega) fun a l hx a₁ hv =>
            hloc a l _ (List.mem_append_right _ hx) (ht a l (List.mem_append_right _ hx) a₁ hv))
          (hI2.regs hm' (fun r _ _ h2 => hs' r h2))
  | @ret G D vs₁ vs₂ hvs =>
    intro st code nv' nl' ip' ft fused hl hG
    cases fused with
    | some _ => simp [lower] at hl
    | none =>
      simp only [lower] at hl; invert_ok hl
      rename_i R1 hpre hlen _ c R2 hsh
      simp only [Except.ok.injEq, Prod.mk.injEq] at hl
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hl
      refine ⟨Nat.le_refl _, fun k args acc m s σ hcode _ _ _ hA _ hI hw _ => ?_⟩
      obtain ⟨rfl, hw⟩ := hw
      exact leave_step hy hpre hsh hcode hA hI fun s2 σ2 ht hI2 htail =>
        ret_ok hy htail hI2 (valsIn_of_holds hvs hlen ht) hw
  | @exit G D g as₁ as₂ has =>
    intro st code nv' nl' ip' ft fused hl hG
    cases fused with
    | some _ => simp [lower] at hl
    | none =>
      simp only [lower] at hl; invert_ok hl
      rename_i R1 hpre hcond _ c R2 hsh
      simp only [Except.ok.injEq, Prod.mk.injEq] at hl
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hl
      refine ⟨Nat.le_refl _, fun k args acc m s σ hcode _ _ _ hA _ hI hw _ => ?_⟩
      obtain ⟨rfl, hw⟩ := hw
      exact leave_step hy hpre hsh hcode hA hI fun s2 σ2 ht hI2 htail =>
        exit_ok hy htail hI2 (valsIn_of_holds has hcond.2 ht) hw hcond.1
  | hlt =>
    intro st code nv' nl' ip' ft fused hl hG
    cases fused with
    | some _ => simp [lower] at hl
    | none =>
      simp only [lower] at hl; invert_ok hl
      simp only [Except.ok.injEq, Prod.mk.injEq] at hl
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hl
      exact ⟨Nat.le_refl _, fun _ _ _ _ _ _ _ _ _ _ _ _ _ hw _ => by simp [wp] at hw⟩
  | @param G D f₁ f₂ _ ih =>
    intro st code nv' nl' ip' ft fused hl hG
    cases fused with
    | some _ => simp [lower] at hl
    | none =>
      simp only [lower] at hl; invert_ok hl
      rename_i r PL hPL hpend
      have hle := (ih 0 st.nv _ code nv' nl' ip' ft none hl (fresh hG 0)).1
      simp at hle
      refine ⟨by omega, fun k args acc m s σ hcode hft hD _ hA hR hI hw _ => ?_⟩
      rw [hPL] at hR
      cases args with
      | nil => simp [wp] at hw
      | cons a as =>
        obtain ⟨hra, hR⟩ := valsIn_cons.mp hR
        exact (ih a st.nv _ code nv' nl' ip' ft none hl (fresh hG a)).2 k as [] m s σ hcode hft
          (hD.cons _) .nil (hA.bindN hG hra) hR hI hw trivial
  | @label G D f₁ f₂ _ ih =>
    intro st code nv' nl' ip' ft fused hl hG
    cases fused with
    | some _ => simp [lower] at hl
    | none =>
      simp only [lower] at hl
      let J := LabJ h hints fn Q X s₀ ra n nX Rf G st.nl
      have ih' := ih J st.nl _ code nv' nl' ip' ft none hl hG
      refine ⟨ih'.1, fun k args acc m s σ hcode hft hD hP hA hR hI hw _ => ?_⟩
      obtain ⟨rfl, hw⟩ := hw
      have hmem := pend_mem hl st.nl (by simp)
      obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hmem
      have hdef : ∃ kℓ, (T.prog h)[kℓ]? = some (T.label (lname fn st.nl)) :=
        ⟨k + i, heq ▸ List.isInfixAt_iff_getElem?.mp hcode i hi⟩
      refine ih'.2 k [] (acc ++ [J]) m s σ hcode hft ?_ (hP.append_single rfl)
        hA hR hI (hw J) trivial
      intro J' ℓ hJ'
      rcases List.mem_cons.mp hJ' with ⟨rfl, rfl⟩ | hJ'
      · exact ⟨hdef, G, fun p hp => hp, rfl⟩
      · exact hD J' ℓ hJ'
  | @block G D b₁ b₂ r₁ r₂ _ _ ihb ihr =>
    intro st code nv' nl' ip' ft fused hl hG
    cases fused with
    | some _ => simp [lower] at hl
    | none =>
      simp only [lower] at hl; invert_ok hl
      rename_i ℓ pend hpend _ cr nv1 nl1 ip1 hlr
      obtain ⟨c', hl', rfl⟩ := prepend_ok hl
      have ihr' := ihr _ cr nv1 nl1 ip1 (some ℓ) none hlr hG
      have ihb' := ihb _ c' nv' nl' ip' ft none hl'
        (fun p hp => by have := hG p hp; simp at ihr' ⊢; omega)
      refine ⟨by simp at ihr' ihb'; omega,
        fun k args acc m s σ hcode hft hD hP hA hR hI hw _ => ?_⟩
      obtain ⟨rfl, hw⟩ := hw
      rw [hpend] at hP
      cases hP with
      | @cons J _ acc' _ hJ hP =>
        have hlab : (T.prog h)[k + cr.length]? = some (T.label (lname fn ℓ)) :=
          List.isInfixAt_singleton.mp ((hcode.append).1.append).2
        refine ihr'.2 k [] acc' m s σ ((hcode.append).1.append).1
          (fun ℓf hlf => by simp only [Option.some.injEq] at hlf; subst hlf; exact hlab)
          hD hP hA hR hI (hw ?_) trivial
        intro as m' hb
        rw [hJ]
        refine ⟨k + cr.length, hlab, fun s' σ' hA' hR' hI' => T.label_spec hlab ?_⟩
        have := ihb'.2 _ as [] m' s' σ' (hcode.append).2
          (fun ℓf hlf => by
            simpa only [List.length_append, List.length_singleton, Nat.add_assoc,
              Nat.add_comm c'.length 1] using hft ℓf hlf)
          hD .nil hA' hR' hI' hb trivial
        simpa only [Target.Run, List.length_append, List.length_singleton, Nat.add_assoc] using this

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
  · rename_i hsaved
    obtain ⟨hnd, hsub_b⟩ := hsaved
    have hsub : ∀ r ∈ hints.saved, r ∈ T.calleeSaved :=
      fun r hr => of_decide_eq_true (List.all_eq_true.mp hsub_b r hr)
    split at hlow
    · rename_i c nv' nl' ip' hl
      simp only [Except.ok.injEq] at hlow
      subst hlow
      have hlab := (hcode.cons).1
      have hpro := (hcode.cons).2.append.1.append.1
      have hsave := (hcode.cons).2.append.1.append.2
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
      have h8 : 8 * hints.totalSlots ≤ frame hints := T.slots_le_frameSize _
      have he8 : 8 * hints.totalSlots = 8 * hints.nslots + 8 * hints.saved.length := by
        simp [Hints.totalSlots, Nat.mul_add]
      have hm1_split : (region (base hints s₀) (8 * hints.nslots) ⋆
          (region (base hints s₀ + BitVec.ofNat 64 (8 * hints.nslots)) (8 * hints.saved.length) ⋆
            (Eq m ⋆ (T.Saved (T.get s₀ T.sp) ra hints.totalSlots ⋆
              (region (T.get s₀ T.sp - BitVec.ofNat 64 n) (n - frame hints) ⋆ Rf)))))
          (T.mem s1) := by
        rw [he8, region_split (by omega)] at hm1
        unfold base frame
        exact sep_ac' (by ac_rfl) hm1
      obtain ⟨σ, hσ, hm1''⟩ := region_slots_sep (by omega) hm1_split
      have hargs1 : T.ValsIn T.argRegs args s1 := by
        refine valsIn_keep (fun r hr => hk1 r ?_) hargs
        simp only [List.mem_cons, List.mem_append, not_or]
        exact ⟨⟨fun e => T.sp_not_argRegs (e ▸ hr), fun h' => T.raRegs_not_argRegs r h' hr⟩,
          T.argRegs_not_scratch r hr⟩
      have hcs1 : ∀ r, r ∈ T.calleeSaved → T.get s1 r = T.get s₀ r := by
        intro r hr
        refine hk1 r ?_
        simp only [List.mem_cons, List.mem_append, not_or]
        exact ⟨⟨fun e => T.sp_not_calleeSaved (e ▸ hr), fun h' => T.raRegs_not_calleeSaved r h' hr⟩,
          T.calleeSaved_not_scratch r hr⟩
      have hmem_save : T.mem s1 =⋆
          region (T.get s1 T.sp + BitVec.ofNat 64 (8 * hints.nslots)) (8 * hints.saved.length) ⋆
            (Eq m ⋆ (slots (base hints s₀) σ ⋆
              (T.Saved (T.get s₀ T.sp) ra hints.totalSlots ⋆
                (region (T.get s₀ T.sp - BitVec.ofNat 64 n) (n - frame hints) ⋆ Rf)))) := by
        rw [hsp1]
        exact sep_ac' (by ac_rfl) hm1''
      refine saveCs_ok hints.nslots hints.saved (k₀ + 1 + (T.prologue hints.totalSlots).length) s1
        hsave (by rw [hsp1]; exact T.spOk_frame _ _ hspE) (by omega) hsub
        (fun r hr => hcs1 r (hsub r hr)) hmem_save fun s2 hk2 hm2 => ?_
      have hsp2 : T.get s2 T.sp = base hints s₀ := by
        rw [hk2 T.sp T.sp_not_scratch, hsp1]
      have hargs2 : T.ValsIn T.argRegs args s2 :=
        valsIn_keep (fun r hr => hk2 r (T.argRegs_not_scratch r hr)) hargs1
      have hI2 : Inv hints s₀ ra n Rf m s2 σ := by
        refine ⟨hσ, hsp2, fun r hr _ => (hk2 r (T.calleeSaved_not_scratch r hr)).trans (hcs1 r hr),
          ?_, hsub, hnd⟩
        rw [hsp1] at hm2
        unfold Fr csSlots
        exact sep_ac' (by ac_rfl) hm2
      have hc' : c.IsInfixAt (T.prog h)
          (k₀ + 1 + (T.prologue hints.totalSlots).length + (saveCs hints.nslots hints.saved).length) := by
        simpa only [List.length_append, Nat.add_assoc] using hc
      have hrun := (lower_correct h hints E f.name Γ Q X s₀ ra n nX Rf bound hy
        (hwf Val Nat Cont Nat) (St.init T.toIsa) c nv' nl' ip' none none hl (by simp)).2
        (k₀ + 1 + (T.prologue hints.totalSlots).length + (saveCs hints.nslots hints.saved).length)
        args [] m s2 σ hc' (fun _ hf => by simp at hf) (fun _ _ hJ => by simp at hJ) .nil
        (fun _ _ hx => by simp [St.init] at hx) hargs2 hI2 hspec trivial
      unfold FnPost at hrun
      simpa only [Nat.add_assoc] using hrun
    · simp at hlow
  · simp at hlow

end Rega
end LeanQbe
