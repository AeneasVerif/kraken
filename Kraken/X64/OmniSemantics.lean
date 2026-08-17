/-
Omnisemantics for x64.
-/

import Kraken.Attribute
import Kraken.OmniSemantics
import Kraken.X64.Semantics

@[kstep] def Effects.All {α : Type} (post : α → Prop) : Effects α → Prop
  | .done a => post a
  | .unimplemented _ => False
  | .gp_unaligned .. => False
  | .nonmem_load .. => False
  | .nonmem_store .. => False
  | @Effects.undefined _ β _ cont => ∀ v : β, (cont v).All post
  | .require_read_access _ _ cont => (cont ()).All post
  | .require_write_access _ _ cont => (cont ()).All post
  | .require_exec_access _ cont => (cont ()).All post

/-- `All` is monotone in its postcondition. -/
theorem Effects.All.imp {α : Type} {post₁ post₂ : α → Prop} {m : Effects α}
    (h : ∀ a, post₁ a → post₂ a) : m.All post₁ → m.All post₂ := by
  induction m <;> simp only [Effects.All] <;> intro hall
  case done a => exact h a hall
  case unimplemented => exact hall
  case gp_unaligned => exact hall
  case nonmem_load => exact hall
  case nonmem_store => exact hall
  case undefined ret ih => exact fun v => ih v (hall v)
  case require_read_access _ _ _ ih => exact ih () hall
  case require_write_access _ _ _ ih => exact ih () hall
  case require_exec_access _ _ ih => exact ih () hall

/-- Universal interpretation turns effect sequencing into nested `All`. -/
theorem Effects.all_bind {α β : Type} {m : Effects α} {k : α → Effects β}
    {post : β → Prop} :
    (m.bind k).All post ↔ m.All fun a => (k a).All post := by
  induction m <;> simp [Effects.bind, Effects.All, *]

/-- `Effects.exec` chooses one of the outcomes described by `Effects.All`. -/
theorem Effects.exec_ok {α : Type} {post : α → Prop} {m : Effects α} {entropy : UInt64} {a : α}
    (hall : m.All post) (hexec : m.exec entropy = .ok a) : post a := by
  induction m with
  | done b => cases hexec; exact hall
  | unimplemented _ => exact absurd hexec (by simp [Effects.exec])
  | gp_unaligned _ _ => exact absurd hexec (by simp [Effects.exec])
  | nonmem_load _ _ _ _ _ => exact absurd hexec (by simp [Effects.exec])
  | nonmem_store _ _ _ _ _ => exact absurd hexec (by simp [Effects.exec])
  | undefined ret ih => exact ih _ (hall _) hexec
  | require_read_access _ _ _ ih => exact ih () hall hexec
  | require_write_access _ _ _ ih => exact ih () hall hexec
  | require_exec_access _ _ ih => exact ih () hall hexec

/-- Appending directives extends only the fall-through path; a jump from the
prefix bypasses the suffix. -/
theorem Directives.interp_append [Labels] (ds₁ ds₂ : List (Directive × Nat))
    (s : MachineData) (pc : Int64) :
    Directives.interp (ds₁ ++ ds₂) s pc =
      (Directives.interp ds₁ s pc).bind fun se =>
        match se with
        | (s', .fallthrough pc') => Directives.interp ds₂ s' pc'
        | (s', .jump t) => .done (s', .jump t) := by
  induction ds₁ generalizing s pc with
  | nil => rfl
  | cons hd rest ih =>
    obtain ⟨d, sz⟩ := hd
    simp only [List.cons_append, Directives.interp, Effects.bind_eq, Effects.bind_assoc]
    congr 1
    funext ⟨s', c⟩
    cases c with
    | next => exact ih ..
    | jmp t => rfl

/-- The append law when the suffix is obtained by fetching at the prefix's
fall-through address. -/
theorem Directives.interp_append_from [Labels]
    (ds rest : List (Directive × Nat))
    (fetch : Int64 → List (Directive × Nat))
    (s : MachineData) (pc : Int64)
    (hrest : fetch (Kraken.Directives.fallthroughPC ds pc) = rest) :
    Directives.interp (ds ++ rest) s pc =
      (Directives.interp ds s pc).bind fun se =>
        match se with
        | (s', .fallthrough pc') => Directives.interp (fetch pc') s' pc'
        | (s', .jump t) => .done (s', .jump t) := by
  induction ds generalizing s pc with
  | nil =>
    change fetch pc = rest at hrest
    simp [Directives.interp, Effects.bind, hrest]
  | cons hd ds ih =>
    obtain ⟨d, sz⟩ := hd
    simp only [List.cons_append, Directives.interp, Effects.bind_eq, Effects.bind_assoc]
    congr 1
    funext ⟨s', c⟩
    cases c with
    | next =>
      have hrest' :
          fetch (Kraken.Directives.fallthroughPC ds (pc + Int64.ofNat sz)) = rest := by
        simpa [Kraken.Directives.fallthroughPC] using hrest
      exact ih (s := s') (pc := pc + Int64.ofNat sz) hrest'
    | jmp t => rfl

/-- Inside a block, every fall-through exit lands at the statically computed
fall-through address, so a continuation may assume that pc. -/
theorem Directives.interp_fallthrough_pc [Labels] {α : Type}
    (ds : List (Directive × Nat)) (s : MachineData) (pc : Int64)
    (k : MachineData × BlockExit → Effects α) :
    (Directives.interp ds s pc).bind k =
      (Directives.interp ds s pc).bind (fun (s', ex) =>
        match ex with
        | .fallthrough _ => k (s', .fallthrough (Kraken.Directives.fallthroughPC ds pc))
        | .jump target => k (s', .jump target)) := by
  induction ds generalizing s pc with
  | nil => rfl
  | cons hd rest ih =>
    obtain ⟨d, size⟩ := hd
    simp only [Directives.interp, Effects.bind_eq, Effects.bind_assoc]
    congr 1
    funext se
    obtain ⟨s', ctrl⟩ := se
    cases ctrl with
    | next =>
      simpa [Kraken.Directives.fallthroughPC, List.foldl] using
        ih s' (pc + Int64.ofNat size)
    | jmp target => rfl

def step1 [Layout] (e: Executable) (s: MachineState) (post: @Post MachineState) : Prop :=
  (Executable.step e s .done).All post

def straightlineStep [Layout] (e: Executable) (s: MachineState) (post: @Post MachineState) : Prop :=
  (Executable.straightline e s .done).All post

/-- Execute `n` applications of the existing single-step semantics. -/
def Executable.runSteps (e : Executable) : Nat → MachineState → Effects MachineState
  | 0, s => .done s
  | n + 1, s => (e.step s .done).bind (e.runSteps n)

/-- A successful batched execution is a finite `step1` execution. -/
theorem Executable.runSteps_all_eventually [Layout] (e : Executable) (n : Nat)
    (s : MachineState) (post : @Post MachineState)
    (h : (e.runSteps n s).All post) : Eventually (step1 e) post s := by
  induction n generalizing s with
  | zero => exact .done s h
  | succ n ih =>
      apply step_cps
      exact Effects.All.imp (fun mid hmid => ih mid hmid) (Effects.all_bind.mp h)

/-- Cut a straight-line run after a listing prefix: prove the prefix's run,
with the remaining program as a fresh straight-line obligation at each
fall-through exit and `post` directly at each jump target. Together with
`kstep`'s step budget this advances a bounded number of directives and stops
at a sound resume point of the same shape. The side condition is the fetch
coherence at this one split, the fact `ResolvesFallthroughAt` states with the
block as the prefix. -/
theorem Executable.straightlineStep_cut [Layout] (e : Executable)
    (st : MachineState) (post : @Post MachineState)
    (pre : List (Directive × Nat))
    (hsplit : e.directivesFromAddress st.2
      = pre ++ e.directivesFromAddress (Kraken.Directives.fallthroughPC pre st.2))
    (h : (let _ : Labels := e.labels
          Directives.interp pre st.1 st.2).All
          (fun se => match se with
            | (s', .fallthrough pc') => straightlineStep e (s', pc') post
            | (s', .jump t) => post (s', t))) :
    straightlineStep e st post := by
  obtain ⟨s, pc⟩ := st
  have key := @Directives.interp_append_from e.labels pre
    (e.directivesFromAddress (Kraken.Directives.fallthroughPC pre pc))
    e.directivesFromAddress s pc rfl
  rw [← hsplit] at key
  unfold straightlineStep Executable.straightline
  dsimp only
  rw [key]
  simp only [Effects.bind_eq, Effects.bind_assoc]
  rw [Effects.all_bind]
  refine Effects.All.imp (fun ⟨s', ex⟩ hex => ?_) h
  cases ex with
  | jump t => exact hex
  | fallthrough pc' => exact hex

/-- The fetched suffix at `pc` decomposes as the block at `pc` followed by the
fetch at the block's fall-through address. This is the address-coherence fact
an honest layout provides; `Layout.size` alone does not guarantee it. -/
def Executable.ResolvesFallthroughAt (e : Executable) (pc : Int64) : Prop :=
  e.directivesFromAddress pc =
    Kraken.Directives.takeBlock (e.directivesFromAddress pc) ++
      e.directivesFromAddress (Kraken.Directives.fallthroughPC
        (Kraken.Directives.takeBlock (e.directivesFromAddress pc)) pc)

/-- A straight-line run executes the block at the current address, then
continues only on fall-through. A jump ends the run at its target. -/
theorem Executable.straightline_eq_step {α : Type}
    (e : Executable) (st : MachineState)
    (h : e.ResolvesFallthroughAt st.2)
    (ret : MachineState → Effects α) :
    e.straightline st ret =
      e.stepWithExit st fun s exit =>
        match exit with
        | .fallthrough pc => e.straightline (s, pc) ret
        | .jump target => ret (s, target) := by
  obtain ⟨s, pc⟩ := st
  unfold Executable.ResolvesFallthroughAt at h
  dsimp only at h
  have key := @Directives.interp_append_from e.labels
    (Kraken.Directives.takeBlock (e.directivesFromAddress pc))
    (e.directivesFromAddress (Kraken.Directives.fallthroughPC
      (Kraken.Directives.takeBlock (e.directivesFromAddress pc)) pc))
    e.directivesFromAddress s pc rfl
  rw [← h] at key
  simp only [Executable.straightline, Executable.stepWithExit]
  rw [key]
  simp only [Effects.bind_eq, Effects.bind_assoc]
  congr 1
  funext ⟨s', ex⟩
  cases ex <;> rfl

/-- A nonempty listing yields a nonempty block. -/
private theorem takeBlock_ne_nil {Directive : Type} {ds : List (Directive × Nat)}
    (h : ds ≠ []) : Kraken.Directives.takeBlock ds ≠ [] := by
  cases ds with
  | nil => exact absurd rfl h
  | cons entry rest =>
    by_cases hz : entry.2 = 0 <;>
      simp [Kraken.Directives.takeBlock, hz]

/-- A listing of zero-sized directives is one block. -/
private theorem takeBlock_of_all_zero {Directive : Type} :
    ∀ {ds : List (Directive × Nat)}, (∀ d ∈ ds, d.2 = 0) →
      Kraken.Directives.takeBlock ds = ds
  | [], _ => rfl
  | entry :: rest, h => by
    simp [Kraken.Directives.takeBlock, h entry (List.mem_cons_self ..),
      takeBlock_of_all_zero (fun d hd => h d (List.mem_cons_of_mem _ hd))]

private theorem eventually_step1_of_straightlineStep_aux [Layout] (e : Executable)
    (hres : ∀ pc, e.ResolvesFallthroughAt pc ∨
      ∀ d ∈ e.directivesFromAddress pc, d.2 = 0) (post : @Post MachineState) :
    ∀ (n : Nat) (s : MachineState), (e.directivesFromAddress s.2).length ≤ n →
      straightlineStep e s post → Eventually (step1 e) post s := by
  intro n
  induction n with
  | zero =>
    intro s hlen h
    haveI := e.labels
    apply Eventually.done
    have hnil : e.directivesFromAddress s.2 = [] :=
      List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)
    obtain ⟨sd, pc⟩ := s
    simp only [straightlineStep, Executable.straightline, hnil, Directives.interp,
      Effects.bind, Effects.All] at h
    exact h
  | succ n ih =>
    intro s hlen h
    haveI := e.labels
    by_cases hnil : e.directivesFromAddress s.2 = []
    · apply Eventually.done
      obtain ⟨sd, pc⟩ := s
      simp only [straightlineStep, Executable.straightline, hnil, Directives.interp,
        Effects.bind, Effects.All] at h
      exact h
    · rcases hres s.2 with hA | hz
      case inr =>
        -- Every remaining directive is zero-sized: one step runs the whole
        -- suffix, which is exactly the straight-line run.
        apply step_cps
        unfold straightlineStep at h
        simp only [Executable.straightline] at h
        simp only [step1, Executable.step, Executable.stepWithExit]
        rw [takeBlock_of_all_zero hz]
        exact Effects.All.imp (fun mid hm => Eventually.done mid hm) h
      -- Peel one block; every fall-through lands at the static address, whose
      -- fetched suffix is strictly shorter by address coherence.
      apply step_cps
      unfold straightlineStep at h
      rw [e.straightline_eq_step s hA] at h
      simp only [step1, Executable.step, Executable.stepWithExit] at h ⊢
      rw [@Directives.interp_fallthrough_pc e.labels _ _ _ _ _] at h ⊢
      rw [Effects.all_bind] at h ⊢
      have hdec : (e.directivesFromAddress (Kraken.Directives.fallthroughPC
          (Kraken.Directives.takeBlock (e.directivesFromAddress s.2)) s.2)).length ≤ n := by
        have hsplit := hA
        unfold Executable.ResolvesFallthroughAt at hsplit
        have hblock : Kraken.Directives.takeBlock (e.directivesFromAddress s.2) ≠ [] :=
          takeBlock_ne_nil hnil
        have hlens := congrArg List.length hsplit
        simp only [List.length_append] at hlens
        have hpos : 0 < (Kraken.Directives.takeBlock (e.directivesFromAddress s.2)).length := by
          cases hblk : Kraken.Directives.takeBlock (e.directivesFromAddress s.2) with
          | nil => exact absurd hblk hblock
          | cons a l => simp
        omega
      refine Effects.All.imp (fun ⟨s', ex⟩ hex => ?_) h
      cases ex with
      | jump target => exact Eventually.done _ hex
      | fallthrough pc' => exact ih _ hdec hex

/-- Block-level proofs transfer to the single-step semantics: on an executable
whose fetches are address-coherent, a spec proved against `straightlineStep`
holds along `step1` execution. -/
theorem Executable.eventually_step1_of_straightlineStep [Layout] (e : Executable)
    (hres : ∀ pc, e.ResolvesFallthroughAt pc ∨
      ∀ d ∈ e.directivesFromAddress pc, d.2 = 0) (s : MachineState)
    (post : @Post MachineState) (h : straightlineStep e s post) :
    Eventually (step1 e) post s :=
  eventually_step1_of_straightlineStep_aux e hres post
    (e.directivesFromAddress s.2).length s (Nat.le_refl _) h




/-- Binds push through branches: the canonical form keeps the branch at the
tree top, where `all_ite` can split it. -/
theorem Effects.ite_bind {α β : Type} {c : Prop} [Decidable c]
    (a b : Effects α) (k : α → Effects β) :
    (if c then a else b).bind k = if c then a.bind k else b.bind k := by
  by_cases hc : c <;> simp [hc]

attribute [ksimp] Effects.ite_bind

theorem all_ite {α : Type} {c : Prop} [Decidable c] (Q : α → Prop) (a b : Effects α) :
    (c → Effects.All Q a) → (¬ c → Effects.All Q b) → Effects.All Q (if c then a else b) := by
  intro ha hb
  by_cases hc : c
  · simp [hc]; exact ha hc
  · simp [hc]; exact hb hc

/-- Every address either fetches coherently (the block there is followed by
the fetch at its fall-through address) or reaches only zero-sized directives,
a terminal stutter that a single step runs in full. Concrete sane layouts
satisfy this, including programs that end in labels; an adversarial
`Layout.size` (aliasing, wraparound) need not. -/
def Executable.Resolves (e : Executable) : Prop :=
  ∀ pc, e.ResolvesFallthroughAt pc ∨
    ∀ d ∈ e.directivesFromAddress pc, d.2 = 0

instance (e : Executable) (pc : Int64) :
    Decidable (Executable.ResolvesFallthroughAt e pc) :=
  inferInstanceAs (Decidable (e.directivesFromAddress pc =
    Kraken.Directives.takeBlock (e.directivesFromAddress pc) ++
      e.directivesFromAddress (Kraken.Directives.fallthroughPC
        (Kraken.Directives.takeBlock (e.directivesFromAddress pc)) pc)))

private theorem dropWhile_ne_eq_nil {α : Type} (p : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, p x = true) → l.dropWhile p = []
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.dropWhile, h x (List.mem_cons_self ..)]
    exact dropWhile_ne_eq_nil p xs (fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- At an address where nothing starts, the fetch is empty and coherence is
trivial, so `Resolves` reduces to a check over the finitely many start
addresses of the executable. -/
theorem Executable.resolves_of_members (e : Executable)
    (h : ∀ p ∈ e.withAddresses.map (·.1), e.ResolvesFallthroughAt p ∨
      ∀ d ∈ e.directivesFromAddress p, d.2 = 0) :
    Executable.Resolves e := by
  intro pc
  by_cases hmem : pc ∈ e.withAddresses.map (·.1)
  · exact h pc hmem
  · refine Or.inl ?_
    have hnil : e.directivesFromAddress pc = [] := by
      unfold Kraken.Executable.directivesFromAddress
      have : e.withAddresses.dropWhile (·.1 ≠ pc) = [] := by
        apply dropWhile_ne_eq_nil
        intro x hx
        simp only [ne_eq, decide_eq_true_eq]
        intro heq
        exact hmem (List.mem_map.mpr ⟨x, hx, heq⟩)
      rw [this]
      rfl
    unfold Executable.ResolvesFallthroughAt
    rw [hnil]
    show ([] : List (Directive × Nat)) = [] ++ e.directivesFromAddress
        (Kraken.Directives.fallthroughPC [] pc)
    have : Kraken.Directives.fallthroughPC ([] : List (Directive × Nat)) pc = pc := rfl
    rw [this, List.nil_append, hnil]

/-- The Eventually-level transfer: a block-granular execution proof yields a
single-step one on a coherently-laid-out executable. -/
theorem Executable.eventually_step1_of_eventually_straightlineStep [Layout]
    (e : Executable) (hres : Executable.Resolves e) (post : @Post MachineState) :
    ∀ s, Eventually (straightlineStep e) post s → Eventually (step1 e) post s := by
  intro s h
  induction h with
  | done s hp => exact .done s hp
  | step s mid_p ht _ ih =>
    exact eventually_trans _ _ _ _
      (e.eventually_step1_of_straightlineStep hres s mid_p ht)
      (fun s' hs' => ih s' hs')

-- A trailing zero-sized label is a terminal stutter: coherence holds through
-- the second disjunct of `Resolves`.
private def nopThenLabel : Executable :=
  (0, [(.instr (.regular .W64 .W64 (.nop 1)), 1), (.label "end", 0)])

example : Executable.Resolves nopThenLabel := by
  apply Executable.resolves_of_members
  intro p hp
  simp only [nopThenLabel, Kraken.Executable.withAddresses, List.map,
    List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;>
    simp [Executable.ResolvesFallthroughAt, nopThenLabel,
      Kraken.Executable.directivesFromAddress, Kraken.Executable.withAddresses,
      List.dropWhile, Kraken.Directives.takeBlock, Kraken.Directives.fallthroughPC]

private def twoNops : Executable :=
  (0, [
    (.instr (.regular .W64 .W64 (.nop 1)), 1),
    (.instr (.regular .W64 .W64 (.nop 1)), 1)
  ])

-- `runSteps` threads the state produced by each step into the next one.
example [Layout] (s : MachineData) :
    Eventually (step1 twoNops) (fun st => st.2 = 2) (s, 0) := by
  apply Executable.runSteps_all_eventually twoNops 2
  simp [twoNops, Executable.runSteps, Executable.step, Executable.stepWithExit,
    BlockExit.pc, Kraken.Directives.takeBlock,
    Kraken.Executable.directivesFromAddress, Kraken.Executable.withAddresses,
    Directives.interp, Directive.interp, Instr.interp, Operation.interp,
    Effects.bind, Effects.All]
