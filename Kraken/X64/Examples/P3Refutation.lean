import Kraken.X64.Examples.Examples

open Kraken.X64.Parser

set_option maxHeartbeats 4000000

/-! Machine-checked refutation of the ORIGINAL `p3_correct` statement.

Original statement (the postcondition's `s` shadows the theorem's `s`):

  ∀ [layout] (s : MachineData), p3_spec s < 2^64 →
    Eventually (straightlineStep (layout p3))
      (fun s => s.1.regs.rdx.toNat = p3_spec s.1 ∧ s.1.regs.rax = 0) (s, layout.start)

Refuted with layout `start := 0, size := fun _ => 1` and initial
`rax = 1, rbx = 1, rdx = 0`.
-/

namespace P3Refutation

instance L : Layout := { start := 0, size := fun _ => 1 }

/-- The original (shadowed) postcondition. -/
def origPost : @Post MachineState :=
  fun s => s.1.regs.rdx.toNat = p3_spec s.1 ∧ s.1.regs.rax = 0

/-- The counterexample initial state. -/
def s0 : MachineData := { regs := { rax := 1, rbx := 1, rdx := 0 } }

-- The bound hypothesis is satisfied: p3_spec s0 = 2^(2^1) = 4 < 2^64.
theorem s0_bound : p3_spec s0 < 2^64 := by decide

-- Concrete addresses under L.
theorem paddr2 : (paddr 2 : Int64) = 2 := by decide
theorem paddr8 : (paddr 8 : Int64) = 8 := by decide

theorem L_sane : SaneP3Layout (layout := L) := by
  constructor
  · intro i hi
    match i, hi with
    | 0, _ => decide
    | 1, _ => decide
  · intro i hi
    match i, hi with
    | 0, _ => decide
    | 1, _ => decide
    | 2, _ => decide
    | 3, _ => decide
    | 4, _ => decide
    | 5, _ => decide
    | 6, _ => decide
    | 7, _ => decide



/-- The reachable states from `s0`, characterised by pc and the three live
registers. Status flags and memory are irrelevant, so they are not constrained. -/
def Bad : @Post MachineState := fun m =>
  (m.2 = L.start ∧ m.1.regs.rax = 1 ∧ m.1.regs.rbx = 1 ∧ m.1.regs.rdx = 0) ∨
  (m.2 = paddr 2 ∧ m.1.regs.rax = 0 ∧ m.1.regs.rbx = 0 ∧ m.1.regs.rdx = 4) ∨
  (m.2 = paddr 8 ∧ m.1.regs.rax = 0 ∧ m.1.regs.rbx = 0 ∧ m.1.regs.rdx = 4) ∨
  (m.2 = paddr 10 ∧ m.1.regs.rax = 0 ∧ m.1.regs.rbx = 0 ∧ m.1.regs.rdx = 4)

theorem s0_bad : Bad (s0, L.start) := Or.inl ⟨rfl, rfl, rfl, rfl⟩

/-- No reachable state satisfies the original postcondition. -/
theorem bad_not_post (m : MachineState) (hb : Bad m) : ¬ origPost m := by
  rintro ⟨hrdx, hrax⟩
  rcases hb with ⟨_, ha, _, _⟩ | ⟨_, _, hbx, hdx⟩ | ⟨_, _, hbx, hdx⟩ | ⟨_, _, hbx, hdx⟩
  · rw [ha] at hrax; exact absurd hrax (by decide)
  all_goals
    rw [hdx] at hrdx
    simp only [p3_spec, hbx] at hrdx
    exact absurd hrdx (by decide)



/-! ### Extracting the successor from `Effects.All`

`kstep` only operates on goals, so to use a step in *hypothesis* position we
combine the backward step lemmas with these three general facts about
`Effects.All`. Together they say: `Effects.All` is a conjunctive, monotone
predicate over a chain, and on a chain that terminates it collapses to its
value at the final state. -/

theorem all_and : ∀ (e : Effects) (P Q : @Post MachineState),
    Effects.All P e → Effects.All Q e → Effects.All (fun s => P s ∧ Q s) e
  | .done a, _, _, hp, hq => ⟨hp, hq⟩
  | .unimplemented _, _, _, hp, _ => hp.elim
  | .gp_unaligned .., _, _, hp, _ => hp.elim
  | .nonmem_load .., _, _, hp, _ => hp.elim
  | .nonmem_store .., _, _, hp, _ => hp.elim
  | @Effects.undefined _ _ cont, P, Q, hp, hq => fun v => all_and (cont v) P Q (hp v) (hq v)
  | .require_read_access _ _ ok, P, Q, hp, hq => all_and (ok ()) P Q hp hq
  | .require_write_access _ _ ok, P, Q, hp, hq => all_and (ok ()) P Q hp hq
  | .require_exec_access _ ok, P, Q, hp, hq => all_and (ok ()) P Q hp hq

theorem all_mono : ∀ (e : Effects) (P Q : @Post MachineState),
    (∀ s, P s → Q s) → Effects.All P e → Effects.All Q e
  | .done a, _, _, himp, hp => himp a hp
  | .unimplemented _, _, _, _, hp => hp.elim
  | .gp_unaligned .., _, _, _, hp => hp.elim
  | .nonmem_load .., _, _, _, hp => hp.elim
  | .nonmem_store .., _, _, _, hp => hp.elim
  | @Effects.undefined _ _ cont, P, Q, himp, hp => fun v => all_mono (cont v) P Q himp (hp v)
  | .require_read_access _ _ ok, P, Q, himp, hp => all_mono (ok ()) P Q himp hp
  | .require_write_access _ _ ok, P, Q, himp, hp => all_mono (ok ()) P Q himp hp
  | .require_exec_access _ ok, P, Q, himp, hp => all_mono (ok ()) P Q himp hp

/-- On a chain that terminates (witnessed by `Effects.All (fun _ => True)`), a
constant `Effects.All` collapses to the constant. For `undefined` nodes we pick
the canonical inhabitant `NondetSupportingType.from_hash 0`. -/
theorem all_const : ∀ (e : Effects) (C : Prop),
    Effects.All (fun _ => True) e → Effects.All (fun _ => C) e → C
  | .done _, _, _, hc => hc
  | .unimplemented _, _, ht, _ => ht.elim
  | .gp_unaligned .., _, ht, _ => ht.elim
  | .nonmem_load .., _, ht, _ => ht.elim
  | .nonmem_store .., _, ht, _ => ht.elim
  | @Effects.undefined _ inst cont, C, ht, hc =>
      all_const (cont (@NondetSupportingType.from_hash _ inst 0)) C
        (ht _) (hc _)
  | .require_read_access _ _ ok, C, ht, hc => all_const (ok ()) C ht hc
  | .require_write_access _ _ ok, C, ht, hc => all_const (ok ()) C ht hc
  | .require_exec_access _ ok, C, ht, hc => all_const (ok ()) C ht hc


/-- An `Effects.All` chain always has a witness: error nodes make `All` false,
and `undefined` nodes are resolved with the canonical inhabitant. -/
theorem all_exists : ∀ (e : Effects) (P : @Post MachineState),
    Effects.All P e → ∃ s, P s
  | .done a, _, hp => ⟨a, hp⟩ -- witness is the final state
  | .unimplemented _, _, hp => hp.elim
  | .gp_unaligned .., _, hp => hp.elim
  | .nonmem_load .., _, hp => hp.elim
  | .nonmem_store .., _, hp => hp.elim
  | @Effects.undefined _ inst cont, P, hp =>
      all_exists (cont (@NondetSupportingType.from_hash _ inst 0)) P
        (hp (@NondetSupportingType.from_hash _ inst 0))
  | .require_read_access _ _ ok, P, hp => all_exists (ok ()) P hp
  | .require_write_access _ _ ok, P, hp => all_exists (ok ()) P hp
  | .require_exec_access _ ok, P, hp => all_exists (ok ()) P hp



-- The `_end` block: a label and a nop, so the state is unchanged and pc advances.
theorem step_end_block (s : MachineData) (Q : @Post MachineState)
    (hQ : Q (s, paddr 10)) :
    straightlineStep (L p3) (s, paddr 8) Q := by
  let ss := s
  change (straightlineStep _ (ss, _) _)
  obtain ⟨⟨rax,rbx,rcx,rdx,rsi,rdi,rsp,rbp,r8,r9,r10,r11,r12,r13,r14,r15⟩, zmms, flags, mem⟩ := s
  dsimp only [straightlineStep, Executable.straightline]
  rw [p3_from_8 L_sane]
  simp only [Layout.apply, p3, List.mapIdx_cons, List.mapIdx_nil, List.drop_succ_cons,
    List.drop_zero]
  sym =>
  kstep
  tactic =>
  exact hQ



theorem raddr_lt10 (i : Nat) (hi : i < 10) :
    raddr L.start ((L p3).2) i = paddr i := by
  simp only [Layout.apply, p3, List.mapIdx_cons, List.mapIdx_nil]
  match i, hi with
  | 0, _ => simp [raddr, paddr]
  | 1, _ => simp [raddr, paddr]
  | 2, _ => simp [raddr, paddr]
  | 3, _ => simp [raddr, paddr]
  | 4, _ => simp [raddr, paddr]
  | 5, _ => simp [raddr, paddr]
  | 6, _ => simp [raddr, paddr]
  | 7, _ => simp [raddr, paddr]
  | 8, _ => simp [raddr, paddr]
  | 9, _ => simp [raddr, paddr]

theorem raddr10 : raddr L.start ((L p3).2) 10 = paddr 10 := by
  simp only [Layout.apply, p3, List.mapIdx_cons, List.mapIdx_nil]
  simp [raddr, paddr]

theorem paddr_ne10 (i : Nat) (hi : i < 10) : (paddr i : Int64) ≠ paddr 10 := by
  match i, hi with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide
  | 4, _ => decide
  | 5, _ => decide
  | 6, _ => decide
  | 7, _ => decide
  | 8, _ => decide
  | 9, _ => decide

-- Past the end of the program: no directives, so the machine stutters.
theorem p3_from_10 : (L p3).directivesFromAddress (paddr 10) = [] := by
  have h := dfa_eq_drop (L p3) (paddr 10) 10 (by rw [p3_len]; omega)
    (fun i hi => by rw [p3_fst, raddr_lt10 i hi]; exact paddr_ne10 i hi)
    (by rw [p3_fst]; exact raddr10)
  rw [h]
  simp [Layout.apply, p3]


-- Past the end: the machine stutters at `paddr 10`.
theorem step_stutter (s : MachineData) (Q : @Post MachineState) (hQ : Q (s, paddr 10)) :
    straightlineStep (L p3) (s, paddr 10) Q := by
  dsimp only [straightlineStep, Executable.straightline]
  rw [p3_from_10]
  exact hQ

/-- `Bad` is closed under stepping: any successor allowed by a step from a `Bad`
state satisfying `Q` is again `Bad` and satisfies `Q`. -/
theorem bad_closed (m : MachineState) (hb : Bad m) (Q : @Post MachineState)
    (hs : straightlineStep (L p3) m Q) : ∃ m', Q m' ∧ Bad m' := by
  obtain ⟨md, pc⟩ := m
  have key : ∀ (R : @Post MachineState), straightlineStep (L p3) (md, pc) R →
      ∃ m', Q m' ∧ R m' := by
    intro R hR
    exact all_exists _ _ (all_and _ Q R hs hR)
  rcases hb with ⟨hpc, hax, hbx, hdx⟩ | ⟨hpc, hax, hbx, hdx⟩ | ⟨hpc, hax, hbx, hdx⟩
    | ⟨hpc, hax, hbx, hdx⟩
  · -- at L.start with rbx = 1
    simp only at hpc hax hbx hdx
    subst hpc
    refine key Bad (step_init_nz md (by rw [hbx]; exact (by decide : (1:UInt64) ≠ 0)) Bad ?_)
    intro st nrax nrdx nrbx hnrdx hnrax hnrbx
    refine Or.inr (Or.inl ⟨rfl, ?_, ?_, ?_⟩)
    · exact UInt64.eq_of_toBitVec_eq (by rw [hnrax]; rfl)
    · show nrbx = 0
      rw [hnrbx, hbx]; rfl
    · exact UInt64.eq_of_toBitVec_eq (by rw [hnrdx]; rfl)
  · -- at paddr 2 with rbx = 0
    simp only at hpc hax hbx hdx
    subst hpc
    refine key Bad (step_head_zero L_sane md hbx Bad ?_)
    intro st
    exact Or.inr (Or.inr (Or.inl ⟨rfl, hax, hbx, hdx⟩))
  · -- at paddr 8
    simp only at hpc hax hbx hdx
    subst hpc
    exact key Bad (step_end_block md Bad (Or.inr (Or.inr (Or.inr ⟨rfl, hax, hbx, hdx⟩))))
  · -- at paddr 10 (fixed point)
    simp only at hpc hax hbx hdx
    subst hpc
    exact key Bad (step_stutter md Bad (Or.inr (Or.inr (Or.inr ⟨rfl, hax, hbx, hdx⟩))))


/-- From a `Bad` state, `origPost` is never reachable. -/
theorem not_eventually (m : MachineState) (hb : Bad m) :
    ¬ Eventually (straightlineStep (L p3)) origPost m := by
  intro he
  induction he with
  | done init hp => exact bad_not_post init hb hp
  | step init mid_p ht _ ih =>
      obtain ⟨m', hmid, hbad'⟩ := bad_closed init hb mid_p ht
      exact ih m' hmid hbad'

/-- **The original `p3_correct` statement is false.**

Instantiated at `layout := L` and `s := s0` (whose bound hypothesis holds,
`p3_spec s0 = 4 < 2^64`), the conclusion fails. -/
theorem original_p3_correct_is_false :
    ¬ (∀ (layout : Layout) (s : MachineData), p3_spec s < 2^64 →
        Eventually (straightlineStep (layout p3))
          (fun s => s.1.regs.rdx.toNat = p3_spec s.1 ∧ s.1.regs.rax = 0)
          (s, layout.start)) := by
  intro hall
  exact not_eventually (s0, L.start) s0_bad (hall L s0 s0_bound)

end P3Refutation

namespace P3Refutation

/-- The same refutation, stated with the *exact* binder shape of the original
theorem (instance-implicit `[layout : Layout]`), leaving no doubt that this is
the statement that appeared in `Examples.lean`. -/
theorem original_p3_correct_is_false' :
    ¬ (∀ [layout : Layout] (s : MachineData), p3_spec s < 2^64 →
        Eventually (straightlineStep (layout p3))
          (fun s => s.1.regs.rdx.toNat = p3_spec s.1 ∧ s.1.regs.rax = 0)
          (s, layout.start)) := by
  intro hall
  exact not_eventually (s0, L.start) s0_bad (hall (layout := L) s0 s0_bound)

end P3Refutation

namespace P3Refutation

/-! ### The `rax = 0` hypothesis is necessary

Dropping `hrax` from the corrected `p3_correct` makes it false: with `rbx = 0`
the loop body never executes, so `rax` is never written. -/

/-- Counterexample state for the `rax = 0` hypothesis. -/
def t0 : MachineData := { regs := { rax := 1, rbx := 0, rdx := 0 } }

def BadR : @Post MachineState := fun m =>
  (m.2 = L.start ∨ m.2 = paddr 8 ∨ m.2 = paddr 10) ∧ m.1.regs.rax = 1 ∧
  m.1.regs.rbx = 0

theorem t0_badR : BadR (t0, L.start) := ⟨Or.inl rfl, rfl, rfl⟩

theorem badR_closed (m : MachineState) (hb : BadR m) (Q : @Post MachineState)
    (hs : straightlineStep (L p3) m Q) : ∃ m', Q m' ∧ BadR m' := by
  obtain ⟨md, pc⟩ := m
  obtain ⟨hpc, hax, hbx⟩ := hb
  have key : ∀ (R : @Post MachineState), straightlineStep (L p3) (md, pc) R →
      ∃ m', Q m' ∧ R m' := fun R hR => all_exists _ _ (all_and _ Q R hs hR)
  simp only at hpc hax hbx
  rcases hpc with hpc | hpc | hpc
  · subst hpc
    refine key BadR (step_init_zero md hbx BadR ?_)
    intro st nrdx _
    exact ⟨Or.inr (Or.inl rfl), hax, hbx⟩
  · subst hpc
    exact key BadR (step_end_block md BadR ⟨Or.inr (Or.inr rfl), hax, hbx⟩)
  · subst hpc
    exact key BadR (step_stutter md BadR ⟨Or.inr (Or.inr rfl), hax, hbx⟩)


/-- **The `rax = 0` hypothesis cannot be dropped.** Even with the corrected
(initial-state) postcondition and a sane layout, the theorem is false without it. -/
theorem rax_hypothesis_necessary :
    ¬ (∀ [layout : Layout], SaneP3Layout → ∀ (s : MachineData), p3_spec s < 2^64 →
        Eventually (straightlineStep (layout p3))
          (fun s' => s'.1.regs.rdx.toNat = p3_spec s ∧ s'.1.regs.rax = 0)
          (s, layout.start)) := by
  intro hall
  have he := hall (layout := L) L_sane t0 (by decide)
  -- but every reachable state has rax = 1
  have : ∀ m, BadR m → ¬ Eventually (straightlineStep (L p3))
      (fun s' => s'.1.regs.rdx.toNat = p3_spec t0 ∧ s'.1.regs.rax = 0) m := by
    intro m hb hev
    induction hev with
    | done init hp =>
        obtain ⟨_, hax, _⟩ := hb
        rw [hax] at hp
        exact absurd hp.2 (by decide)
    | step init mid_p ht _ ih =>
        obtain ⟨m', hmid, hbad'⟩ := badR_closed init hb mid_p ht
        exact ih m' hmid hbad'
  exact this _ t0_badR he


/-! ### The `SaneP3Layout` hypothesis is necessary

With the degenerate layout `size := fun _ => 0`, every directive sits at address
0, so `jmp start` re-executes `mov $2, %rdx`. Then `rdx` only ever takes the
values 2 and 4, and the theorem fails for `rbx = 2` (which needs `rdx = 16`). -/

end P3Refutation

namespace P3Degenerate

instance D : Layout := { start := 0, size := fun _ => 0 }

theorem D_start : (D.start : Int64) = 0 := rfl
theorem D_all_zero : ∀ i, (paddr i : Int64) = 0 := by
  intro i
  induction i with
  | zero => rfl
  | succ n ih => show (paddr n + Int64.ofNat (Layout.size n) : Int64) = 0
                 rw [ih]; rfl

-- Under D, `SaneP3Layout` FAILS (as expected).
theorem D_not_sane : ¬ SaneP3Layout (layout := D) := by
  intro h
  exact h.ne2 0 (by omega) (by rw [D_all_zero, D_all_zero])



theorem D_label_end : Labels.label (self := (D p3).labels) "_end" = (0 : Int64) := by
  rw [p3_label_end, D_all_zero]

theorem D_label_start : Labels.label (self := (D p3).labels) "start" = (0 : Int64) := by
  rw [p3_label_start, D_all_zero]

theorem D_label_end' :
    (List.findSome? (fun x => if x.2.1 = Directive.label "_end" then some x.1 else none)
      (D.apply p3).withAddresses).getD (-1) = (0 : Int64) := D_label_end

theorem D_label_start' :
    (List.findSome? (fun x => if x.2.1 = Directive.label "start" then some x.1 else none)
      (D.apply p3).withAddresses).getD (-1) = (0 : Int64) := D_label_start

set_option maxHeartbeats 4000000 in
theorem D_step_zero (s : MachineData) (hz : s.regs.rbx = 0) (Q : @Post MachineState)
    (hQ : ∀ (st : StatusFlags) (nrdx : UInt64), nrdx.toBitVec = 2#64 →
            Q ({ regs := { s.regs with rdx := nrdx }, zmms := s.zmms, status := st,
                 dmem := s.dmem }, 0)) :
    straightlineStep (D p3) (s, 0) Q := by
  let ss := s
  have h0 : (0 : Int64) = D.start := rfl
  rw [h0]
  change (straightlineStep _ (ss, _) _)
  obtain ⟨⟨rax,rbx,rcx,rdx,rsi,rdi,rsp,rbp,r8,r9,r10,r11,r12,r13,r14,r15⟩, zmms, flags, mem⟩ := s
  dsimp only [straightlineStep, Executable.straightline]
  rw [Executable.directivesFromStart]
  simp only [p3, List.mapIdx_cons, List.mapIdx_nil]
  simp at hz
  subst hz
  simp only at hQ
  sym =>
  kstep
  tactic =>
  rename_i v status
  apply all_ite
  · intro hc
    rw [D_label_end]
    exact hQ _ _ rfl
  · intro hc
    exfalso
    apply hc
    simp [v]


theorem D_jmp_back (X : Int64) :
    Int64.ofBitVec ((X + ((0 : Int64) - X)).toBitVec) = (0 : Int64) := by
  have h : X + ((0 : Int64) - X) = 0 := by
    apply Int64.toBitVec_inj.mp
    simp [Int64.toBitVec_add]
    exact BitVec.add_right_neg X.toBitVec
  rw [h]; rfl

set_option maxHeartbeats 4000000 in
theorem D_step_nz (s : MachineData) (hnz : s.regs.rbx ≠ 0) (Q : @Post MachineState)
    (hQ : ∀ (st : StatusFlags) (nrax nrdx nrbx : UInt64),
            nrdx.toBitVec = 4#64 → nrax.toBitVec = 0#64 → nrbx = s.regs.rbx - 1 →
            Q ({ regs := { s.regs with rax := nrax, rdx := nrdx, rbx := nrbx },
                 zmms := s.zmms, status := st, dmem := s.dmem }, 0)) :
    straightlineStep (D p3) (s, 0) Q := by
  let ss := s
  have h0 : (0 : Int64) = D.start := rfl
  rw [h0]
  change (straightlineStep _ (ss, _) _)
  obtain ⟨⟨rax,rbx,rcx,rdx,rsi,rdi,rsp,rbp,r8,r9,r10,r11,r12,r13,r14,r15⟩, zmms, flags, mem⟩ := s
  dsimp only [straightlineStep, Executable.straightline]
  rw [Executable.directivesFromStart]
  simp only [p3, List.mapIdx_cons, List.mapIdx_nil]
  simp at hnz
  simp only at hQ
  sym =>
  kstep
  tactic =>
  rename_i v status
  apply all_ite
  · intro hc
    exfalso
    apply hnz
    have : v = BitVec.zero 64 := by simpa using hc
    simp [v] at this
    exact UInt64.eq_of_toBitVec_eq (by simpa using this)
  · intro hc
    sym =>
    kstep
    tactic =>
    simp only [RelRegOrMem.interp, ConstExpr.interp, D_label_start', D_jmp_back]
    refine hQ _ _ _ _ ?_ ?_ ?_
    · show BitVec.ofInt 64 _ = _
      decide
    · show BitVec.ofInt 64 _ = _
      decide
    · show (⟨_⟩ : UInt64) = _
      congr 1
      simp +zetaDelta


open P3Refutation (all_and all_exists)

/-- Counterexample state for layout-necessity: `rbx = 2` needs `rdx = 16`. -/
def u0 : MachineData := { regs := { rax := 0, rbx := 2, rdx := 0 } }

/-- Under `D`, `rdx` only ever takes the values 0 (initially), 4 and 2. -/
def BadD : @Post MachineState := fun m =>
  m.2 = 0 ∧ m.1.regs.rax = 0 ∧
  (m.1.regs.rdx = 0 ∨ m.1.regs.rdx = 4 ∨ m.1.regs.rdx = 2)

theorem u0_badD : BadD (u0, 0) := ⟨rfl, rfl, Or.inl rfl⟩

theorem badD_closed (m : MachineState) (hb : BadD m) (Q : @Post MachineState)
    (hs : straightlineStep (D p3) m Q) : ∃ m', Q m' ∧ BadD m' := by
  obtain ⟨md, pc⟩ := m
  obtain ⟨hpc, hax, _⟩ := hb
  have key : ∀ (R : @Post MachineState), straightlineStep (D p3) (md, pc) R →
      ∃ m', Q m' ∧ R m' := fun R hR => all_exists _ _ (all_and _ Q R hs hR)
  simp only at hpc hax
  subst hpc
  by_cases hz : md.regs.rbx = 0
  · refine key BadD (D_step_zero md hz BadD ?_)
    intro st nrdx hnrdx
    exact ⟨rfl, hax, Or.inr (Or.inr (UInt64.eq_of_toBitVec_eq (by rw [hnrdx]; rfl)))⟩
  · refine key BadD (D_step_nz md hz BadD ?_)
    intro st nrax nrdx nrbx hnrdx hnrax _
    exact ⟨rfl, UInt64.eq_of_toBitVec_eq (by rw [hnrax]; rfl),
           Or.inr (Or.inl (UInt64.eq_of_toBitVec_eq (by rw [hnrdx]; rfl)))⟩

/-- **The `SaneP3Layout` hypothesis cannot be dropped.** Even with the corrected
(initial-state) postcondition and `rax = 0` initially, the theorem is false for
the degenerate layout. -/
theorem sane_layout_hypothesis_necessary :
    ¬ (∀ [layout : Layout] (s : MachineData), s.regs.rax = 0 → p3_spec s < 2^64 →
        Eventually (straightlineStep (layout p3))
          (fun s' => s'.1.regs.rdx.toNat = p3_spec s ∧ s'.1.regs.rax = 0)
          (s, layout.start)) := by
  intro hall
  have he : Eventually (straightlineStep (D p3))
      (fun s' => s'.1.regs.rdx.toNat = p3_spec u0 ∧ s'.1.regs.rax = 0) (u0, 0) :=
    hall (layout := D) u0 rfl (by decide)
  have key : ∀ m, BadD m → ¬ Eventually (straightlineStep (D p3))
      (fun s' => s'.1.regs.rdx.toNat = p3_spec u0 ∧ s'.1.regs.rax = 0) m := by
    intro m hb hev
    induction hev with
    | done init hp =>
        obtain ⟨_, _, hdx⟩ := hb
        -- p3_spec u0 = 2^(2^2) = 16, but rdx ∈ {0, 4, 2}
        rcases hdx with h | h | h <;> rw [h] at hp <;>
          exact absurd hp.1 (by decide)
    | step init mid_p ht _ ih =>
        obtain ⟨m', hmid, hbad'⟩ := badD_closed init hb mid_p ht
        exact ih m' hmid hbad'
  exact key _ u0_badD he

end P3Degenerate
