/-
Kraken - Example Programs

This demonstrates our proof style using the `kstep` stepping tactic that
advances through ASM instructions. This is a work in progress, and is the result
of several experiments, which can be found in the Git history at revision
a556993a and earlier.

For semantics, see Kraken/Semantics.lean.
For tactics, see Kraken/Tactics.lean.
-/

import Kraken.Eval
import Kraken.SeparationTactics
import Kraken.Tactics
import Kraken.X64.OmniSemantics
import Kraken.X64.Parser
import Kraken.X64.Semantics
import Kraken.X64.Sep

open Kraken.X64.Parser

--------------------------------------------------------------------------------

def p1 := parse("start: mov $1, %rax")

-- Super-simple example to debug tactics
example [layout : Layout] s : straightlineStep (layout p1) (s, layout.start) (fun s => s.1.regs.rax = 1) := by
  kprologue p1 with s
  sym => kstep; tactic =>
  decide
  /- simp [Instr.interp,Operation.interp,Operand.interp,MachineData.set] -/
  /- simp [MachineData.setReg,Reg64s.set,Reg64s.set64,ConstExpr.interp] -/
  /- simp [Width.bits] -/
  /- simp [p1,step1,eval1,fetch,Instr.is_ctrl,strt1,eval_operand,eval_imm,set_reg_or_mem,next,MachineState.setReg,Registers.set] -/

def swap : Program := parse("
  xor %rbx, %rax
  xor %rax, %rbx
  xor %rbx, %rax")

theorem swap_correct [layout : Layout] (d : MachineData) :
      Eventually (straightlineStep (layout swap))
      (fun s' =>
          s'.1.regs.get Reg.rax = d.regs.get Reg.rbx ∧
          s'.1.regs.get Reg.rbx = d.regs.get Reg.rax)
      (d, layout.start) := by
  apply step_cps
  kprologue swap with d
  sym => kstep; tactic =>
  apply Eventually.done
  grind

-- Stepping demo. Ideally, this demo should be without the first .mov
def p2 : Program := parse("
start:
  mov $1, %rax
  xor %rax, %rax
  jnz start
  mov $2, %rax")

-- Example 2: stepping through both straightline and control instructions
example [layout : Layout] (s : MachineData): Eventually (straightlineStep (layout p2)) (fun s => s.1.regs.rax = 2) (s, layout.start) := by
  apply step_cps
  kprologue p2 with s
  sym =>
  kstep
  tactic =>
  -- TODO: would be nice to have these simp steps be part of kstep
  rename_i v v1 status
  have: v = 0 := by grind
  simp [this]
  sym =>
  kstep
  tactic =>
  apply Eventually.done
  bv_decide

-- Example 3, more sophisticated

-- TODO: restore p3

def p3: Program := parse("
init:
  mov $2, %rdx             # rdx: current result = 2
start:
  sub $0, %rbx             # TEST: zf = (rbx == 0)
  jz _end                 # end loop if rbx == 0 (a.k.a. « while rbx >= 0 »)
  mulx %rdx, %rdx, %rax    # BODY: rdx := rdx * rdx
  sub $1, %rbx              # rbx -= 1
  jmp start               # go back to test & loop body
_end:
  nop
")

def p3_spec (s: MachineData): Nat := 2^(2^s.regs.rbx.toNat)

--------------------------------------------------------------------------------
-- p3: verified. The ORIGINAL statement of `p3_correct` was FALSE; see below.
--
-- THE BUG: in the original postcondition
--   `fun s => s.1.regs.rdx.toNat = p3_spec s.1 ∧ s.1.regs.rax = 0`
-- the bound `s` SHADOWS the theorem's `s`, so `p3_spec` was read off the FINAL
-- state, not the initial one. The loop drives `rbx` to 0 while squaring `rdx`,
-- so where `rbx = n - j` we have `rdx = 2^(2^j)`; the postcondition then demands
-- `j = n - j`. Since `p3_spec s < 2^64` forces `rbx ≤ 5`, the odd cases
-- `rbx ∈ {1,3,5}` are outright counterexamples.
--
-- COUNTEREXAMPLE: layout `start := 0, size := fun _ => 1`; initial
-- `rax = 1, rbx = 1, rdx = 0` (bound holds: `p3_spec = 4`). The only reachable
-- `straightlineStep` boundaries are
--   (pc=0, rax=1,rbx=1,rdx=0) → (pc=2, rax=0,rbx=0,rdx=4) → (pc=8, …) → (pc=10, …),
-- the last a fixed point. The post needs `rdx = 2` at `rbx = 0`, but `rdx = 4`.
-- Nothing on this path is nondeterministic, so `Eventually` cannot dodge it.
--
-- `p3_correct` below fixes this by pinning `p3_spec s` to the INITIAL state. It
-- needs two more hypotheses, both of which are genuinely necessary:
--   * `s.regs.rax = 0`: if `rbx = 0` the loop body never runs, so `rax` is never
--     written;
--   * `SaneP3Layout`: `Layout.size` is arbitrary, and with all sizes 0 every
--     directive collides at one address, so `jmp start` re-runs `mov $2, %rdx`
--     and `rdx` never exceeds 4 — false from `rbx ≥ 2` on. The predicate just
--     says the two jump targets are not aliased by earlier directives; any
--     layout giving instructions a nonzero size satisfies it.
--
-- All of the above is machine-checked in `Kraken/X64/Examples/P3Refutation.lean`
-- (`original_p3_correct_is_false'`, `rax_hypothesis_necessary`,
-- `sane_layout_hypothesis_necessary`). Everything here and there is `sorry`-free
-- and uses only `propext, Classical.choice, Quot.sound`.
--------------------------------------------------------------------------------

theorem wa_cons (a : Int64) (d : Directive) (n : Nat) (ds : List (Directive × Nat)) :
    Executable.withAddresses (a, (d,n) :: ds)
      = (a, d, n) :: Executable.withAddresses (a + .ofNat n, ds) := by
  simp [Executable.withAddresses]

theorem wa_nil (a : Int64) : Executable.withAddresses (a, []) = [] := by
  simp [Executable.withAddresses]

def raddr (a : Int64) : List (Directive × Nat) → Nat → Int64
  | _, 0 => a
  | [], _+1 => a
  | (_,n) :: ds, i+1 => raddr (a + .ofNat n) ds i

theorem wa_dropWhile (tgt : Int64) :
    ∀ (k : Nat) (ds : List (Directive × Nat)) (a : Int64),
      k ≤ ds.length →
      (∀ i, i < k → raddr a ds i ≠ tgt) →
      raddr a ds k = tgt →
      (Executable.withAddresses (a, ds)).dropWhile (·.1 ≠ tgt)
        = Executable.withAddresses (raddr a ds k, ds.drop k)
  | 0, ds, a, _, _, hk => by
      cases ds with
      | nil => simp [wa_nil]
      | cons dn ds =>
        obtain ⟨d, n⟩ := dn
        simp only [raddr] at hk
        rw [wa_cons]
        simp only [List.dropWhile, hk, ne_eq, not_true_eq_false, decide_false, List.drop_zero]
        simp only [raddr, wa_cons]
  | k+1, [], a, hlen, _, _ => by simp at hlen
  | k+1, (d,n) :: ds, a, hlen, hne, hk => by
      have h0 : a ≠ tgt := by
        have := hne 0 (Nat.succ_pos k)
        simpa [raddr] using this
      rw [wa_cons]
      simp only [List.dropWhile, ne_eq, h0, not_false_eq_true, decide_true]
      simp only [raddr] at hk ⊢
      rw [wa_dropWhile tgt k ds (a + .ofNat n) (by simpa using Nat.le_of_succ_le_succ hlen)
        (fun i hi => by have := hne (i+1) (Nat.succ_lt_succ hi); simpa [raddr] using this) hk]
      simp [List.drop_succ_cons]

/-- `directivesFromAddress` at the address of index `k`. -/
theorem dfa_eq_drop (e : Executable) (tgt : Int64) (k : Nat)
    (hlen : k ≤ e.2.length)
    (hne : ∀ i, i < k → raddr e.1 e.2 i ≠ tgt)
    (hk : raddr e.1 e.2 k = tgt) :
    e.directivesFromAddress tgt = e.2.drop k := by
  show (List.map (·.2) ((Executable.withAddresses (e.1, e.2)).dropWhile (·.1 ≠ tgt))) = _
  rw [wa_dropWhile tgt k e.2 e.1 hlen hne hk, hk]
  -- withAddresses then map snd is the identity
  exact Executable.withAddresses_map_snd _ _

section
variable [layout : Layout]

def paddr : Nat → Int64
  | 0 => layout.start
  | n+1 => paddr n + .ofNat (layout.size n)

theorem p3_len : ((layout p3).2).length = 10 := by
  simp [Layout.apply, p3]

theorem p3_fst : (layout p3).1 = layout.start := rfl

theorem p3_raddr2 : raddr layout.start ((layout p3).2) 2 = paddr 2 := by
  simp only [Layout.apply, p3, List.mapIdx_cons, List.mapIdx_nil]
  simp [raddr, paddr]

theorem p3_raddr8 : raddr layout.start ((layout p3).2) 8 = paddr 8 := by
  simp only [Layout.apply, p3, List.mapIdx_cons, List.mapIdx_nil]
  simp [raddr, paddr]

theorem p3_raddr_lt2 (i : Nat) (hi : i < 2) :
    raddr layout.start ((layout p3).2) i = paddr i := by
  simp only [Layout.apply, p3, List.mapIdx_cons, List.mapIdx_nil]
  match i, hi with
  | 0, _ => simp [raddr, paddr]
  | 1, _ => simp [raddr, paddr]

theorem p3_raddr_lt8 (i : Nat) (hi : i < 8) :
    raddr layout.start ((layout p3).2) i = paddr i := by
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

/-- The layout places p3's directives so that the two jump targets are unambiguous. -/
structure SaneP3Layout : Prop where
  ne2 : ∀ i, i < 2 → (paddr i : Int64) ≠ paddr 2
  ne8 : ∀ i, i < 8 → (paddr i : Int64) ≠ paddr 8

theorem p3_from_2 (h : SaneP3Layout (layout := layout)) :
    (layout p3).directivesFromAddress (paddr 2) = ((layout p3).2).drop 2 := by
  refine dfa_eq_drop _ _ 2 (by rw [p3_len]; omega) ?_ ?_
  · intro i hi
    rw [p3_fst, p3_raddr_lt2 i hi]
    exact h.ne2 i hi
  · rw [p3_fst]; exact p3_raddr2

theorem p3_from_8 (h : SaneP3Layout (layout := layout)) :
    (layout p3).directivesFromAddress (paddr 8) = ((layout p3).2).drop 8 := by
  refine dfa_eq_drop _ _ 8 (by rw [p3_len]; omega) ?_ ?_
  · intro i hi
    rw [p3_fst, p3_raddr_lt8 i hi]
    exact h.ne8 i hi
  · rw [p3_fst]; exact p3_raddr8

/-- `label "start"` resolves to the address of directive #2. -/
theorem p3_label_start : Labels.label (self := (layout p3).labels) "start" = paddr 2 := by
  show (List.findSome? _ (Executable.withAddresses (layout p3))).getD (-1) = _
  show (List.findSome? _ (Executable.withAddresses (layout.start, (layout p3).2))).getD (-1) = _
  simp only [Layout.apply, p3, List.mapIdx_cons, List.mapIdx_nil]
  simp only [wa_cons, wa_nil, List.findSome?]
  simp only [paddr]
  rfl

/-- `label "_end"` resolves to the address of directive #8. -/
theorem p3_label_end : Labels.label (self := (layout p3).labels) "_end" = paddr 8 := by
  show (List.findSome? _ (Executable.withAddresses (layout p3))).getD (-1) = _
  show (List.findSome? _ (Executable.withAddresses (layout.start, (layout p3).2))).getD (-1) = _
  simp only [Layout.apply, p3, List.mapIdx_cons, List.mapIdx_nil]
  simp only [wa_cons, wa_nil, List.findSome?]
  simp only [paddr]
  rfl

end

theorem all_ite {c : Prop} [Decidable c] (Q : @Post MachineState) (a b : Effects) :
    (c → Effects.All Q a) → (¬ c → Effects.All Q b) → Effects.All Q (if c then a else b) := by
  intro ha hb
  by_cases hc : c
  · simp [hc]; exact ha hc
  · simp [hc]; exact hb hc

section
variable [layout : Layout]

theorem p3_label_start' :
    (List.findSome? (fun x => if x.2.1 = Directive.label "start" then some x.1 else none)
      (layout.apply p3).withAddresses).getD (-1) = paddr 2 := p3_label_start

theorem p3_label_end' :
    (List.findSome? (fun x => if x.2.1 = Directive.label "_end" then some x.1 else none)
      (layout.apply p3).withAddresses).getD (-1) = paddr 8 := p3_label_end

theorem jmp_back (X : Int64) :
    Int64.ofBitVec ((X + ((paddr 2 : Int64) - X)).toBitVec) = (paddr 2 : Int64) := by
  have h : X + ((paddr 2 : Int64) - X) = paddr 2 := by
    apply Int64.toBitVec_inj.mp
    simp [Int64.toBitVec_add, Int64.toBitVec_sub]
    rw [BitVec.add_comm, BitVec.sub_add_cancel]
  rw [h]; rfl

-- Loop head with `rbx = 0`: control falls through to `_end`, registers unchanged.
set_option maxHeartbeats 4000000 in
theorem step_head_zero (h : SaneP3Layout (layout := layout)) (s : MachineData)
    (hz : s.regs.rbx = 0) (Q : @Post MachineState)
    (hQ : ∀ st, Q ({ s with status := st }, paddr 8)) :
    straightlineStep (layout p3) (s, paddr 2) Q := by
  let ss := s
  change (straightlineStep _ (ss, _) _)
  obtain ⟨⟨rax,rbx,rcx,rdx,rsi,rdi,rsp,rbp,r8,r9,r10,r11,r12,r13,r14,r15⟩, zmms, flags, mem⟩ := s
  dsimp only [straightlineStep, Executable.straightline]
  rw [p3_from_2 h]
  simp only [Layout.apply, p3, List.mapIdx_cons, List.mapIdx_nil, List.drop_succ_cons,
    List.drop_zero]
  simp at hz
  subst hz
  simp only at hQ
  sym =>
  kstep
  tactic =>
  rename_i v status
  have hv : v = BitVec.zero 64 := by simp [v]
  simp [hv]
  rw [p3_label_end']
  exact hQ _

-- Unfolded form of the `_end` label lookup, as it appears after `kstep`.
set_option maxHeartbeats 4000000 in
theorem step_head_nz (h : SaneP3Layout (layout := layout)) (s : MachineData)
    (hnz : s.regs.rbx ≠ 0) (Q : @Post MachineState)
    (hQ : ∀ (st : StatusFlags) (nrax nrdx nrbx : UInt64),
            nrdx.toBitVec = BitVec.ofInt 64 ((s.regs.rdx.toNat : Int) * (s.regs.rdx.toNat : Int)) →
            nrax.toBitVec = BitVec.ofInt 64 (((s.regs.rdx.toNat : Int) * (s.regs.rdx.toNat : Int)) >>> 64) →
            nrbx = s.regs.rbx - 1 →
            Q ({ regs := { s.regs with rax := nrax, rdx := nrdx, rbx := nrbx },
                 zmms := s.zmms, status := st, dmem := s.dmem }, paddr 2)) :
    straightlineStep (layout p3) (s, paddr 2) Q := by
  let ss := s
  change (straightlineStep _ (ss, _) _)
  obtain ⟨⟨rax,rbx,rcx,rdx,rsi,rdi,rsp,rbp,r8,r9,r10,r11,r12,r13,r14,r15⟩, zmms, flags, mem⟩ := s
  dsimp only [straightlineStep, Executable.straightline]
  rw [p3_from_2 h]
  simp only [Layout.apply, p3, List.mapIdx_cons, List.mapIdx_nil, List.drop_succ_cons,
    List.drop_zero]
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
    simp only [RelRegOrMem.interp, ConstExpr.interp, p3_label_start', jmp_back]
    refine hQ _ _ _ _ ?_ ?_ ?_
    · show BitVec.ofInt 64 _ = _
      congr 1
      simp +zetaDelta
      rfl
    · show BitVec.ofInt 64 _ = _
      congr 1
      simp +zetaDelta
      rfl
    · show (⟨_⟩ : UInt64) = _
      congr 1
      simp +zetaDelta



-- Initial block with `rbx = 0`: sets `rdx := 2`, then falls through to `_end`.
set_option maxHeartbeats 4000000 in
theorem step_init_zero (s : MachineData) (hz : s.regs.rbx = 0) (Q : @Post MachineState)
    (hQ : ∀ (st : StatusFlags) (nrdx : UInt64), nrdx.toBitVec = 2#64 →
            Q ({ regs := { s.regs with rdx := nrdx }, zmms := s.zmms, status := st,
                 dmem := s.dmem }, paddr 8)) :
    straightlineStep (layout p3) (s, layout.start) Q := by
  let ss := s
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
    rw [p3_label_end]
    exact hQ _ _ rfl
  · intro hc
    exfalso
    apply hc
    simp [v]



-- Initial block with `rbx ≠ 0`: rdx := 2, then one loop body iteration (2 -> 4).
set_option maxHeartbeats 4000000 in
theorem step_init_nz (s : MachineData) (hnz : s.regs.rbx ≠ 0) (Q : @Post MachineState)
    (hQ : ∀ (st : StatusFlags) (nrax nrdx nrbx : UInt64),
            nrdx.toBitVec = 4#64 → nrax.toBitVec = 0#64 → nrbx = s.regs.rbx - 1 →
            Q ({ regs := { s.regs with rax := nrax, rdx := nrdx, rbx := nrbx },
                 zmms := s.zmms, status := st, dmem := s.dmem }, paddr 2)) :
    straightlineStep (layout p3) (s, layout.start) Q := by
  let ss := s
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
    simp only [RelRegOrMem.interp, ConstExpr.interp, p3_label_start', jmp_back]
    refine hQ _ _ _ _ ?_ ?_ ?_
    · show BitVec.ofInt 64 _ = _
      decide
    · show BitVec.ofInt 64 _ = _
      decide
    · show (⟨_⟩ : UInt64) = _
      congr 1
      simp +zetaDelta



-- Arithmetic helpers for the mulx bound.
theorem ofInt_toNat_of_lt (m : Nat) (hm : m < 2^64) :
    (BitVec.ofInt 64 (m : Int)).toNat = m := by
  simp [BitVec.toNat_ofInt]
  omega

theorem ofInt_shift_of_lt (m : Nat) (hm : m < 2^64) :
    (BitVec.ofInt 64 ((m : Int) >>> 64)) = 0#64 := by
  have : ((m : Int) >>> 64) = 0 := by
    rw [Int.shiftRight_eq_div_pow]
    omega
  rw [this]
  rfl



-- Loop invariant: at the loop head with `k` iterations left.
def p3_inv (n : Nat) (k : Nat) : @Post MachineState := fun m =>
  m.2 = paddr 2 ∧ m.1.regs.rbx.toNat = k ∧ k ≤ n ∧
  m.1.regs.rdx.toNat = 2^(2^(n-k)) ∧ m.1.regs.rax = 0

-- Invariant at k=0 implies the postcondition.
set_option maxHeartbeats 4000000 in
theorem inv_zero_post (h : SaneP3Layout (layout := layout)) (n : Nat)
    (target : Nat) (htgt : target = 2^(2^n)) (m : MachineState) (hinv : p3_inv n 0 m) :
    Eventually (straightlineStep (layout p3))
      (fun s' => s'.1.regs.rdx.toNat = target ∧ s'.1.regs.rax = 0) m := by
  obtain ⟨hpc, hrbx, hkn, hrdx, hrax⟩ := hinv
  apply step_cps
  obtain ⟨md, pc⟩ := m
  simp only at hpc hrbx hrdx hrax
  subst hpc
  apply step_head_zero h md (UInt64.toNat_inj.mp (by simpa using hrbx))
  intro st
  apply Eventually.done
  refine ⟨?_, ?_⟩
  · simp only
    rw [hrdx, htgt]
    simp
  · simpa using hrax



theorem uint64_sub_one_toNat (x : UInt64) (hx : x.toNat ≠ 0) :
    (x - 1).toNat = x.toNat - 1 := by
  have h1 : x.toNat < 2^64 := x.toNat_lt_size
  have h2 : UInt64.toNat 1 = 1 := rfl
  simp only [UInt64.toNat_sub, h2]
  omega

set_option maxHeartbeats 4000000 in
theorem inv_step (h : SaneP3Layout (layout := layout)) (n : Nat)
    (hbound : 2^(2^n) < 2^64) (m : MachineState) (k : Nat) (hk : k ≠ 0)
    (hinv : p3_inv n k m) :
    Eventually (straightlineStep (layout p3)) (p3_inv n (k-1)) m := by
  obtain ⟨hpc, hrbx, hkn, hrdx, hrax⟩ := hinv
  apply step_cps
  obtain ⟨md, pc⟩ := m
  simp only at hpc hrbx hrdx hrax
  subst hpc
  have hexp : n - (k-1) = (n-k) + 1 := by omega
  have hsq : md.regs.rdx.toNat * md.regs.rdx.toNat = 2^(2^(n-(k-1))) := by
    rw [hrdx, hexp, ← Nat.pow_add, ← Nat.two_mul, ← Nat.pow_succ']
  have hlt : md.regs.rdx.toNat * md.regs.rdx.toNat < 2^64 := by
    rw [hsq]
    refine Nat.lt_of_le_of_lt ?_ hbound
    apply Nat.pow_le_pow_right (by decide)
    apply Nat.pow_le_pow_right (by decide)
    omega
  have hcast : ((md.regs.rdx.toNat : Int) * (md.regs.rdx.toNat : Int))
      = ((md.regs.rdx.toNat * md.regs.rdx.toNat : Nat) : Int) :=
    Int.ofNat_mul_ofNat _ _
  have hrbxne : md.regs.rbx ≠ 0 := by
    intro hc
    rw [hc] at hrbx
    simp at hrbx
    omega
  apply step_head_nz h md hrbxne
  intro st nrax nrdx nrbx hnrdx hnrax hnrbx
  apply Eventually.done
  refine ⟨rfl, ?_, by omega, ?_, ?_⟩
  · show nrbx.toNat = k - 1
    rw [hnrbx, uint64_sub_one_toNat _ (by omega), hrbx]
  · show nrdx.toNat = _
    rw [show nrdx.toNat = (nrdx.toBitVec).toNat from rfl, hnrdx, hcast,
      ofInt_toNat_of_lt _ hlt, hsq]
  · show nrax = 0
    apply UInt64.eq_of_toBitVec_eq
    rw [hnrax, hcast]
    exact ofInt_shift_of_lt _ hlt



set_option maxHeartbeats 4000000 in
theorem p3_correct (h : SaneP3Layout (layout := layout)) (s : MachineData)
    (hrax : s.regs.rax = 0) (hb : p3_spec s < 2^64) :
    Eventually (straightlineStep (layout p3))
      (fun s' => s'.1.regs.rdx.toNat = p3_spec s ∧ s'.1.regs.rax = 0)
      (s, layout.start) := by
  have hbound : 2^(2^s.regs.rbx.toNat) < 2^64 := hb
  by_cases hz : s.regs.rbx = 0
  · apply step_cps
    apply step_init_zero s hz
    intro st nrdx hnrdx
    apply Eventually.done
    refine ⟨?_, ?_⟩
    · simp only [p3_spec]
      rw [show nrdx.toNat = (nrdx.toBitVec).toNat from rfl, hnrdx]
      simp [hz]
    · simpa using hrax
  · have hn0 : s.regs.rbx.toNat ≠ 0 := by
      intro hc
      exact hz (UInt64.toNat_inj.mp (by simpa using hc))
    apply step_cps
    apply step_init_nz s hz
    intro st nrax nrdx nrbx hnrdx hnrax hnrbx
    apply reg_dec_loop _ _ _ (p3_inv s.regs.rbx.toNat) (s.regs.rbx.toNat - 1)
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨rfl, ?_, by omega, ?_, ?_⟩
      · show nrbx.toNat = _
        rw [hnrbx, uint64_sub_one_toNat _ (by omega)]
      · show nrdx.toNat = _
        rw [show nrdx.toNat = (nrdx.toBitVec).toNat from rfl, hnrdx]
        have hgap : s.regs.rbx.toNat - (s.regs.rbx.toNat - 1) = 1 := by omega
        rw [hgap]
        rfl
      · show nrax = 0
        apply UInt64.eq_of_toBitVec_eq
        rw [hnrax]
        rfl
    · exact fun state hinv => inv_zero_post h _ (p3_spec s) rfl state hinv
    · exact fun state k hk hinv => inv_step h _ hbound state k hk hinv

end


-- `SaneP3Layout` is satisfiable, so `p3_correct` is not vacuous: an ordinary
-- layout (start at 0, one byte per directive) satisfies it. The `local instance`
-- is confined to this section so it cannot affect other examples.
section P3NonVacuous
local instance L1 : Layout := { start := 0, size := fun _ => 1 }

theorem L1_sane : SaneP3Layout (layout := L1) := by
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

/-- ...and it really applies to a nontrivial state: `rbx = 3`, so the program
must compute `rdx = 2^(2^3) = 256`. -/
example : Eventually (straightlineStep (L1 p3))
    (fun s' => s'.1.regs.rdx.toNat = p3_spec ({ regs := { rbx := 3 } } : MachineData)
               ∧ s'.1.regs.rax = 0)
    (({ regs := { rbx := 3 } } : MachineData), L1.start) := by
  apply p3_correct L1_sane
  · rfl
  · decide

end P3NonVacuous

def p4 := eval% parse("start: mov $2, %rax
dec %rax")

-- Super-simple example to debug tactics
example [layout : Layout] s : straightlineStep (layout p4) (s, layout.start) (fun s => s.1.regs.rax = 1) := by
  kprologue p4 with s
  sym =>
  kstep
  -- intros
  tactic =>
  decide

/- Examples -/

def p5 := parse("start: mov $2, %rax
dec %rax
start2:
dec %rax")

set_option maxHeartbeats 1000000
set_option pp.rawOnError true
/- set_option pp.all true -/

example [layout : Layout] s : straightlineStep (layout p5) (s, layout.start) (fun s => s.1.regs.rax = 0) := by
  kprologue p5 with s
  sym => kstep; tactic =>
  bv_decide

def p6 := parse("push %rax
mov $0, %rax
pop %rax")

set_option maxHeartbeats 1000000
set_option pp.rawOnError true
/- set_option pp.coercions false -/
/- set_option pp.all true -/

attribute [ksimp]
  BitVec.add_zero
  BitVec.ofInt_add
  BitVec.ofInt_ofNat
  BitVec.ofInt_toInt
  BitVec.ofNat_uInt64ToNat
  BitVec.reduceOfInt
  BitVec.setWidth_eq
  Int.add_zero
  Int.reduceBmod
  Int.reduceNeg
  Int64.reduceToInt
  Int64.toInt_neg
  Nat.reducePow
  Nat.shiftRight_zero
  Nat.sub_zero
  UInt64.ofBitVec_add
  UInt64.ofBitVec_ofNat
  UInt64.ofBitVec_sub
  UInt64.ofBitVec_toBitVec
  UInt64.sub_add_cancel
  UInt64.toBitVec_ofNat
  UInt64.toBitVec_sub
  UInt64.toNat_toBitVec

theorem p6_correct [layout : Layout] (s₀ : MachineData)
    (stack : List UInt8) (h_len : stack.length = 8) (R : DataMem → Prop)
    (h_mem : s₀.dmem =⋆ Eq (stack.At (s₀.regs.rsp.toBitVec - 8#64)) ⋆ R) :
    Eventually (straightlineStep (layout p6))
      (fun s' => s'.1.regs.rax = s₀.regs.rax ∧ s'.1.regs.rsp = s₀.regs.rsp)
      (s₀, layout.start) := by
  apply step_cps
  kprologue p6 with s₀
  have h_bs : stack.length = 8 := h_len
  have h_mem1 := Mem.storeInt_sep (rsp.toBitVec - 8#64) 8 stack R mem ⟨h_mem, h_bs⟩ rax.toBitVec.toInt
  sym =>
  kstep
  tactic =>
  apply Eventually.done
  rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  bv_decide

-- def bigp := parseFile("./ecc-secp521r1-modp.S")

/- set_option maxRecDepth 4000 -/
/- set_option maxHeartbeats 2000000 -/

-- example [layout : Layout] s
--   (hAlign: s.regs.rsp % 8 = 0)
--   (hContains: forall x, x ∈ s.dmem)
-- : straightlineStep (layout bigp) (s, layout.start) (fun s => s.1.regs.rax = 0) := by
--   -- Refine the state to make registers apparent -- note that `cases` consumes
--   -- the hypothesis, and substitutes it, so we make a copy of it to have a
--   -- refined state in the hypotheses, not the goal.
--   let ss := s
--   change (straightlineStep _ (ss, _) _)
--   cases s with | mk regs flags mem =>
--   cases regs with | mk rax =>
--   -- Rewrite the program to make layout, addresses, etc. apparent
--   delta bigp
--   dsimp only [straightlineStep,Executable.straightline]
--   rw [Executable.directivesFromStart]
--   simp [List.mapIdx,List.mapIdx.go]
--   sym =>
--   kstep
--   done


open Std
open Std.ExtHashMap

def move_2_regs_to_heap := parse("
    movq %rax, (%rdi)
    movq %rcx, 8(%rdi)
    movq (%rdi), %r12
    movq 8(%rdi), %r13
")

theorem move_2_regs_to_heap_correct [layout : Layout] (s₀ : MachineData)
  (v1 v2 : UInt64)
  (R : DataMem → Prop)
  (h_mem : s₀.dmem =⋆ Eq (v1.At s₀.regs.rdi.toBitVec) ⋆ Eq (v2.At (s₀.regs.rdi.toBitVec + 8#64)) ⋆ R)
  : Eventually (straightlineStep (layout move_2_regs_to_heap))
      (fun s' =>
        s'.1.regs.r12 = s₀.regs.rax ∧
        s'.1.regs.r13 = s₀.regs.rcx ∧
        s'.1.regs.rdi = s₀.regs.rdi)
      (s₀, layout.start) := by
  apply step_cps
  kprologue move_2_regs_to_heap with s₀

  have h_bs1 : v1.toBytes.length = 8 := UInt64.toBytes_length v1
  have h_bs2 : v2.toBytes.length = 8 := UInt64.toBytes_length v2
  have h_mem1 := Mem.storeInt_sep rdi.toBitVec 8 v1.toBytes (Eq (v2.At (rdi.toBitVec + 8#64)) ⋆ R) mem ⟨by ecancel, h_bs1⟩ rax.toBitVec.toInt
  have h_mem1' : (Eq (v2.At (rdi.toBitVec + 8#64)) ⋆ (Eq ((Int.toBytes 8 rax.toBitVec.toInt).At rdi) ⋆ R)) _ := cast (congrFun (by ac_rfl) _) h_mem1
  have h_mem2 := Mem.storeInt_sep (rdi.toBitVec + 8#64) 8 v2.toBytes _ _ ⟨h_mem1', h_bs2⟩ rcx.toBitVec.toInt
  have h_mem2' : (Eq ((Int.toBytes 8 rax.toBitVec.toInt).At rdi) ⋆ (Eq ((Int.toBytes 8 rcx.toBitVec.toInt).At (rdi.toBitVec + 8#64)) ⋆ R)) _ := cast (congrFun (by ac_rfl) _) h_mem2
  have h_mem2'' : (Eq ((Int.toBytes 8 rcx.toBitVec.toInt).At (rdi.toBitVec + 8#64)) ⋆ (Eq ((Int.toBytes 8 rax.toBitVec.toInt).At rdi.toBitVec) ⋆ R)) _ := cast (congrFun (by ac_rfl) _) h_mem2'
  simp at h_mem
  sym =>
  -- TODO: these would be prime examples for cancellation!
  -- TODO: the kstep tactic is supposed to apply `exact`, but `exact` only applies after `simp`, so
  -- clearly, stuff is missing from the simp-set in `kstep`
  kstep
  case h_mem => tactic => simp; ecancel
  case h_len => exact h_bs1
  kstep
  case h_mem => tactic => simp; exact h_mem1'
  case h_len => exact h_bs2
  kstep
  case h_mem => tactic => simp; exact h_mem2'
  case h_len => tactic => rfl
  kstep
  case h_mem => tactic => simp; exact h_mem2''
  case h_len => tactic => rfl
  kstep
  tactic =>
  apply Eventually.done
  rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl, BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  exact ⟨rfl, rfl, rfl⟩

def sib_example := parse("
    movq $42, %rax
    movq %rax, (%rdi, %r15, 8)
    movq $0, %rax
    movq (%rdi, %r15, 8), %rax
")

-- FIXME: I had to replace `s₀.regs.r15.toBitVec * 8#64` with `BitVec.ofInt 64
-- (s₀.regs.r15.toBitVec.toInt * 8)` to make the example go through. Why?
theorem sib_example_correct [layout : Layout] (s₀ : MachineData)
    (v : UInt64) (R : DataMem → Prop)
    (h_mem : s₀.dmem =⋆ Eq (v.At (s₀.regs.rdi.toBitVec + BitVec.ofInt 64 (s₀.regs.r15.toBitVec.toInt * 8))) ⋆ R) :
    Eventually (straightlineStep (layout sib_example))
      (fun s' => s'.1.regs.rax = 42)
      (s₀, layout.start) := by
  apply step_cps
  kprologue sib_example with s₀
  have h_bs : v.toBytes.length = 8 := UInt64.toBytes_length v
  simp at h_mem
  have h_mem' := Mem.storeInt_sep (rdi.toBitVec + BitVec.ofInt 64 (r15.toBitVec.toInt * 8)) 8 v.toBytes R mem ⟨h_mem, h_bs⟩ 42
  sym =>
  kstep
  case h_mem => tactic => simp; exact h_mem
  case h_len => exact h_bs
  kstep
  case h_mem => tactic => simp; exact h_mem'
  case h_len => exact by decide
  kstep
  tactic =>
  apply Eventually.done
  rfl

def alu_mem_example := parse("
    movq $42, %rax
    movq %rax, 136(%rdx)
    movq $100, %rcx
    addq 136(%rdx), %rcx
")

theorem alu_mem_example_correct [layout : Layout] (s₀ : MachineData)
    (v : UInt64) (R : DataMem → Prop)
    (h_mem : s₀.dmem =⋆ Eq (v.At (s₀.regs.rdx.toBitVec + 136#64)) ⋆ R) :
    Eventually (straightlineStep (layout alu_mem_example))
      (fun s' => s'.1.regs.rcx = 142)
      (s₀, layout.start) := by
  apply step_cps
  kprologue alu_mem_example with s₀
  have h_bs : v.toBytes.length = 8 := UInt64.toBytes_length v
  have h_mem1 := Mem.storeInt_sep (rdx.toBitVec + 136#64) 8 v.toBytes R mem ⟨h_mem, h_bs⟩ 42
  sym =>
  kstep
  case h_mem => tactic => simp; exact h_mem
  case h_len => exact h_bs
  kstep
  case h_mem => tactic => simp; exact h_mem1
  case h_len => exact Int.toBytes_length 8 _
  kstep
  tactic =>
  apply Eventually.done
  dsimp [UInt64.toBitVec]
  change (100 : UInt64) + { toBitVec := BitVec.ofInt 64 (Int.ofBytes (Int.toBytes 8 (42#64).toInt)) } = (142 : UInt64)
  rw [BitVec.ofInt_ofBytes_toBytes 64 8 rfl]
  rfl

def dynamic_stack_example := parse("
    movq $99, -8(%rsp)
    movq %rsp, %rbp
    leaq -1024(%rsp, %r9, 8), %rsp
    movq $42, %rax
    movq %rax, 16(%rsp, %r15, 8)
    movq $0, %rax
    movq 16(%rsp, %r15, 8), %rax
    movq %rbp, %rsp
    movq -8(%rsp), %rbx
")

theorem dynamic_stack_example_correct [layout : Layout] (s₀ : MachineData)
    (stack : List UInt8) (lstack : stack.length = 1024) R
    (h : s₀.regs.r9.toNat + s₀.regs.r15.toNat < 125)
    (h_mem : s₀.dmem =⋆ Eq (stack.At (s₀.regs.rsp.toBitVec - 1024)) ⋆ R) :
    Eventually (straightlineStep (layout dynamic_stack_example))
      (fun s' => s'.1.regs.rax = 42 ∧ s'.1.regs.rbx = 99 ∧ s'.1.regs.rsp = s₀.regs.rsp)
      (s₀, layout.start) := by
  apply step_cps
  kprologue dynamic_stack_example with s₀
  have h_bs : stack.length = 1024 := lstack
  have h_take_drop : stack = stack.take 1016 ++ stack.drop 1016 := by exact (List.take_append_drop 1016 stack).symm
  rw [h_take_drop] at h_mem
  have h_len_take : (stack.take 1016).length = 1016 := by
    rw [List.length_take]
    rw [h_bs]
    rfl
  have h_len_drop : (stack.drop 1016).length = 8 := by
    rw [List.length_drop]
    rw [h_bs]
  have h_At_append := Mem.At_append_sep (w := 64) (stack.take 1016) (stack.drop 1016) (rsp.toBitVec - 1024#64) (by
    rw [h_len_take, h_len_drop]
    decide)
  change (Eq ((stack.take 1016 ++ stack.drop 1016).At (rsp.toBitVec - 1024#64)) ⋆ R) mem at h_mem
  rw [h_At_append] at h_mem
  rw [sep_assoc] at h_mem
  have h_addr_eq : rsp.toBitVec - 1024#64 + BitVec.ofNat 64 (stack.take 1016).length = rsp.toBitVec + BitVec.ofNat 64 (2^64 - 8) := by
    rw [h_len_take]
    change rsp.toBitVec - 1024#64 + 1016#64 = rsp.toBitVec + BitVec.ofNat 64 (2^64 - 8)
    bv_decide
  rw [h_addr_eq] at h_mem
  replace h_mem : (Eq ((stack.drop 1016).At (rsp.toBitVec + BitVec.ofNat 64 (2^64 - 8))) ⋆ (Eq ((stack.take 1016).At (rsp.toBitVec - 1024#64)) ⋆ R)) _ := cast (congrFun (by ac_rfl) _) h_mem
  have h_mem1 := Mem.storeInt_sep (rsp.toBitVec + BitVec.ofNat 64 (2^64 - 8)) 8 (stack.drop 1016) (Eq ((stack.take 1016).At (rsp.toBitVec - 1024#64)) ⋆ R) mem ⟨h_mem, h_len_drop⟩ 99

  sym =>
  kstep
  case h_mem => tactic => simp; exact h_mem
  case h_len => exact h_len_drop
  sorry
  -- kstep
  -- tactic => sorry
  -- tactic => sorry
  -- tactic => sorry
  -- tactic => sorry
  -- tactic => sorry
  -- -- FIXME: kstep here takes too long
  -- done
