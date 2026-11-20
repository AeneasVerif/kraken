module

public import LeanQbe.T.Examples.Kissat.Full1
public import LeanQbe.T.Examples.Kissat.FullArena
public import LeanQbe.T.Examples.Kissat.FullInv2
public import LeanQbe.T.Examples.Kissat.DimacsLemmas
public import LeanQbe.T.Examples.Kissat.SolverIngestLemmas1
public import LeanQbe.T.Logic.C0Step
public meta import Lean.Elab.Tactic
public meta import LeanQbe.T.Logic.C0Step
import all Kraken.Mem
import all Kraken.Separation

/-!
# Soundness Proofs for Kissat `D-Full` DIMACS Body Ingestion (`Stage 4`, Part 1)

Defines strictly scoped `FullDimacsBodyTactics`, mirrored `FullDimacsBodySpecs` matching
`FullSpec1`/`FullSpec2` (including `#1037` `probing` framing and `#1043`/`#1045` witness
entailment threading), and proves `full_skip_cl_wp` (`Full1.full_skip_cl`).
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap LeanQbe.T.C0Step
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

namespace FullDimacsBodyTactics

theorem bv32_lshr1 (x : BitVec 32) : (x >>> (1 : Nat)).toNat = x.toNat / 2 := bv32_lshr_1 x

theorem bv32_beq_nat_eq {n : Nat} {x : BitVec 32} (hn : n < 2 ^ 32) :
    (x == BitVec.ofNat 32 n) = decide (x.toNat = n) := by
  by_cases h : x.toNat = n
  · have hx : x = BitVec.ofNat 32 n :=
      BitVec.eq_of_toNat_eq (by rw [bv32_ofNat_toNat hn]; exact h)
    simp [hx, bv32_ofNat_toNat hn]
  · have hx : x ≠ BitVec.ofNat 32 n := fun he =>
      h (by simpa [bv32_ofNat_toNat hn] using congrArg BitVec.toNat he)
    simp [h, hx]

theorem bv64_beq_eq {x y : BitVec 64} : (x == y) = decide (x = y) := by
  by_cases h : x = y <;> simp [h]

theorem i8_vals_beq0 {x : BitVec 8} (hx : x = 0#8 ∨ x = 1#8 ∨ x = 0xFF#8) :
    (x.signExtend 32 == 0#32) = decide (x = 0#8) := by
  rcases hx with rfl | rfl | rfl <;> decide

theorem bv32_ptag_ofNat {l : Nat} (hl : l < 2 ^ 32) :
    BitVec.setWidth 8 ((BitVec.ofNat 32 l &&& (1 : BitVec 32)) + (1 : BitVec 32)) =
      BitVec.ofNat 8 (l % 2 + 1) := by
  apply BitVec.eq_of_toNat_eq
  have hand : (BitVec.ofNat 32 l &&& (1 : BitVec 32)).toNat = l % 2 := by
    rw [BitVec.toNat_and, show (1 : BitVec 32).toNat = 1 from rfl,
      show (BitVec.ofNat 32 l).toNat = l from Nat.mod_eq_of_lt hl, Nat.and_one_is_mod]
  rw [BitVec.toNat_setWidth, BitVec.toNat_add, hand, show (1 : BitVec 32).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega : l % 2 + 1 < 2 ^ 32)]
  simp [Nat.mod_eq_of_lt (by omega : l % 2 + 1 < 2 ^ 8)]

theorem bv8_zext32_eq_zero {a : BitVec 8} : a.setWidth 32 = 0#32 ↔ a = 0#8 :=
  bv8_zext32_eq (b := 0#8)

theorem bv8_zext32_bne {a b : BitVec 8} :
    (a.setWidth 32 != b.setWidth 32) = decide (a ≠ b) := by
  by_cases h : a = b <;> simp [bne, h, bv8_zext32_eq]

theorem p_strip_wp {Γ rs Q X e m} (h : wp (rs := rs) Γ Q X e m) : wp Γ Q X e m := h
theorem p_strip_fwp {as rs Γ f args m Q X}
    (h : Func.wp (as := as) (rs := rs) Γ f args m Q X) : Func.wp Γ f args m Q X := h
theorem p_strip_le_wp {a b : Nat} {P : Prop} (h : a ≤ b) (hp : P) : a ≤ b ∧ P := ⟨h, hp⟩

scoped macro "p_lets" : tactic => `(tactic| (
  (try (first | refine p_strip_fwp ?_ | refine p_strip_wp ?_))
  (try c0_let_simp); repeat (refine p_strip_le_wp (by decide) ?_; try c0_let_simp)))

theorem wp_head_jnz_iff {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {c : Arg Val .bool} {b : Bool} {t e : Expr Val Cont rs} (hc : c.val = b)
    (h : (b = true → wp Γ Q X t m) ∧ (b = false → wp Γ Q X e m)) :
    wp Γ Q X (.jnz c t e) m := by subst hc; rw [wp_jnz]; exact h

scoped macro "c0_val_eq" : tactic => `(tactic| (
  (try simp only [liftCmp, Ty.hasFloat, Arg.val_var, Arg.val_imm, Prod.fst, Prod.snd,
    evalBits_eq_beq, evalBits_ne_bne, evalBits_ult_eq, evalBits_ule_eq, evalBits_ugt_eq,
    evalBits_uge_eq, evalBits_slt_eq, evalBits_sle_eq, evalBits_sgt_eq, evalBits_sge_eq,
    Bool.not_true, Bool.not_false,
    BitVec.reduceSignExtend, BitVec.reduceSetWidth, BitVec.reduceAdd, BitVec.reduceMul]);
  all_goals rfl))

section BvC0Extras
@[scoped bv_c0] theorem bv32_toNat_0 : (0 : BitVec 32).toNat = 0 := rfl
@[scoped bv_c0] theorem bv32_toNat_1 : (1 : BitVec 32).toNat = 1 := rfl
@[scoped bv_c0] theorem bv64_toNat_0 : (0 : BitVec 64).toNat = 0 := rfl
@[scoped bv_c0] theorem bv64_toNat_1 : (1 : BitVec 64).toNat = 1 := rfl
@[scoped bv_c0] theorem full_cfg_mv_mod (c : FullCfg) : c.mv % 2 ^ 64 = c.mv := by
  have := c.hmv; unfold dimacsBound at this; exact Nat.mod_eq_of_lt (by omega)
@[scoped bv_c0] theorem full_cfg_nc_mod (c : FullCfg) : c.nc % 2 ^ 64 = c.nc := by
  have := c.hnc; unfold dimacsBound at this; exact Nat.mod_eq_of_lt (by omega)
@[scoped bv_c0] theorem full_cfg_maxv_mod (c : FullCfg) : c.max_vars % 2 ^ 64 = c.max_vars := by
  have := c.hmaxv; unfold dimacsBound at this; exact Nat.mod_eq_of_lt (by omega)
@[scoped bv_c0] theorem bv32_toNat_mod64 (x : BitVec 32) : x.toNat % 2 ^ 64 = x.toNat :=
  Nat.mod_eq_of_lt (by have := x.isLt; omega)
@[scoped bv_c0] theorem bv32_div2_mod64 (x : BitVec 32) : (x.toNat / 2) % 2 ^ 64 = x.toNat / 2 :=
  Nat.mod_eq_of_lt (by have := x.isLt; omega)
@[scoped bv_c0] theorem bv64_toNat_mod64 (x : BitVec 64) : x.toNat % 2 ^ 64 = x.toNat :=
  Nat.mod_eq_of_lt x.isLt
attribute [scoped bv_c0] BitVec.toNat_ushiftRight BitVec.toNat_shiftLeft BitVec.toNat_xor
  BitVec.toNat_and Nat.shiftLeft_eq Nat.shiftRight_eq_div_pow List.length_set List.length_replicate
attribute [scoped bv_c0 high] LeanQbe.T.bv_c0_zext32_64 LeanQbe.T.bv_c0_zext8_64
  LeanQbe.T.bv_c0_zext8_32
end BvC0Extras

scoped elab "pi_unmdata" : tactic => Lean.Elab.Tactic.liftMetaTactic1 fun g => do
  let ty ← Lean.instantiateMVars (← g.getType)
  if ty.isMData then return some (← g.replaceTargetDefEq ty.consumeMData) else return some g

scoped macro "pi_clean" : tactic => `(tactic| simp only [Nat.reduceLeDiff, Nat.le_refl, true_and,
  and_true, Bool.false_or, Bool.or_false, Bool.true_and, Bool.and_true, Bool.not_true,
  Bool.not_false, decide_eq_true_eq, decide_eq_false_iff_not])

scoped macro "pi_steps" : tactic => `(tactic| (
  all_goals try pi_unmdata; c0_steps
  repeat (any_goals pi_clean; all_goals try pi_unmdata; c0_steps)))

end FullDimacsBodyTactics

namespace FullDimacsBodySpecs

/-! ## Canonical Stage-4 invariants mirrored from `FullSpec1` -/

def FullMrkZero (c : FullCfg) (s : FullState) : Prop :=
  ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8

def FullLitMarksClear (c : FullCfg) (s : FullState) : Prop :=
  FullMrkZero c s ∧ (∀ l < 2 * c.max_vars, s.core.lit_mark[l]?.getD 0#8 = 0#8)

def FullArenaVarsNodup (s : FullState) : Prop :=
  ∀ r ∈ fullArenaClauseRefs s, fullArenaClauseGarb s r = false →
    ((fullArenaClauseLits s r).map (· / 2)).Nodup

def FullLastLearnedWf (s : FullState) : Prop :=
  ∀ i < 8,
    let cr := s.scratch.last_learned[i]?.getD 0xFFFFFFFF#32
    cr = 0xFFFFFFFF#32 ∨ cr.toNat ∈ fullArenaClauseRefs s

def FullExtScratchOk (c : FullCfg) (s : FullState) : Prop :=
  FullLastLearnedWf s ∧ s.scratch.extend_len ≤ c.extend_cap

def FullSparseInv (c : FullCfg) (F0 : CNF Nat) (s : FullState) : Prop :=
  FullCoreInv c F0 s ∧ FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧
  FullExtScratchOk c s ∧ s.core.dense_mode = 0#64

def FullSparseInvW (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) : Prop :=
  s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullLitMarksClear c s ∧
  FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧ s.core.dense_mode = 0#64

theorem FullSparseInvW.toSparse {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s) : FullSparseInv c F0 s :=
  ⟨⟨h.1, F_cur, h.2.1⟩, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem FullSparseInv.exists_witness {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) : ∃ F_cur, FullSparseInvW c F0 F_cur s :=
  let ⟨F_cur, hw⟩ := h.1.witness
  ⟨F_cur, h.1.lengths, hw, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem FullLastLearnedWf.of_refs_subset {s s' : FullState}
    (h : FullLastLearnedWf s) (hll : s'.scratch.last_learned = s.scratch.last_learned)
    (hsub : ∀ r ∈ fullArenaClauseRefs s, r ∈ fullArenaClauseRefs s') : FullLastLearnedWf s' := by
  intro i hi; dsimp only; rw [hll]
  exact (h i hi).elim Or.inl fun hr => Or.inr (hsub _ hr)

theorem FullSparseInv.with_d {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) (cur' val' : BitVec 64) :
    FullSparseInv c F0 { s with core := { s.core with d_cur := cur', d_val := val' } } :=
  ⟨h.1.with_d cur' val', h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem FullSparseInvW.with_d {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullSparseInvW c F0 F_cur s) (cur' val' : BitVec 64) :
    FullSparseInvW c F0 F_cur { s with core := { s.core with d_cur := cur', d_val := val' } } :=
  ⟨⟨{ h.1.core_ok with vals_len := h.1.core_ok.vals_len }, h.1.scratch_ok⟩,
    { h.2.1 with
      arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
      watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
    h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

/-! ## Mirrored `FullSpec2` contracts (`full_assign_lvl`, `full_add_clause`, `dimacs_body`) -/

def fullAssignLvlSpec : Spec [i64, i32, i32, i32] [] :=
  fun (h, lit, rsn, alvl, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
      if s.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ s.core.trail_end ∨
          s.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8 then
        Q () m
      else
        let v := lit.toNat / 2
        let rsn' := if alvl = 0#32 then 0xFFFFFFFF#32 else rsn
        let unfl' := if alvl = 0#32 then s.core.unflushed + 1#64 else s.core.unflushed
        ∀ flags' unass' phases' m',
          flags'.length = c.max_vars → phases'.length = c.max_vars →
          let s' : FullState :=
            { s with
              core :=
                { s.core with
                  vals := (s.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
                  flags := flags', lvl := s.core.lvl.set v alvl, rsns := s.core.rsns.set v rsn'
                  trl := s.core.trl.set s.core.trail_end lit
                  trail_pos := s.core.trail_pos.set v (BitVec.ofNat 32 s.core.trail_end)
                  trail_end := s.core.trail_end + 1
                  unassigned := unass', unflushed := unfl' }
              scratch := { s.scratch with phases := phases' } }
          s'.LengthsOk c → (FullMem c s' ⋆ R) m' → Q () m'

def fullAddClauseSpec : Spec [i64, i32, i32, .bool] [i64] :=
  fun (h, len, _glue, _red, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ s.core.dense_mode = 0#64 ∧
      len.toNat ≤ c.max_vars ∧
      (2 ≤ len.toNat →
        (∀ l ∈ (s.core.tmp.take len.toNat).map BitVec.toNat, l < 2 * s.core.cur_vars) ∧
        ((s.core.tmp.take len.toNat).map fun x => x.toNat / 2).Nodup ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.core.tmp.take len.toNat).map BitVec.toNat))) ∧
      (FullMem c s ⋆ R) m ∧
      if len.toNat < 2 then
        Q (0xFFFFFFFF#64, ()) m
      else if len.toNat = 2 then
        ∀ r wvec' wstk' wlen' wusable' nb' wsort' m',
          let s' : FullState :=
            { s with
              core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen',
                                    wusable := wusable', num_binary := nb' }
              scratch := { s.scratch with wsort := wsort' } }
          (r = 0xFFFFFFFF#64 ∨ r = 0xFFFFFFFE#64) →
          s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → (FullMem c s' ⋆ R) m' → Q (r, ()) m'
      else
        ∀ r arena' alen' wvec' wstk' wlen' wusable' fred' ni' nr' wsort' m',
          let s' : FullState :=
            { s with
              core := { s.core with arena := arena', arena_len := alen', wvec := wvec',
                                    wstk := wstk', wlen := wlen', wusable := wusable',
                                    first_reducible := fred', num_irred := ni',
                                    num_redundant := nr' }
              scratch := { s.scratch with wsort := wsort' } }
          (r = 0xFFFFFFFF#64 ∨ r = BitVec.ofNat 64 s.core.arena_len) →
          s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
          (∀ ref ∈ fullArenaClauseRefs s, ref ∈ fullArenaClauseRefs s') →
          (FullArenaVarsNodup s → FullArenaVarsNodup s') →
          (r = BitVec.ofNat 64 s.core.arena_len →
            alen' = s.core.arena_len + 3 + len.toNat ∧
            s.core.arena_len ∈ fullArenaClauseRefs s' ∧
            fullArenaClauseGarb s' s.core.arena_len = false ∧
            fullArenaClauseLits s' s.core.arena_len =
              (s.core.tmp.take len.toNat).map BitVec.toNat) →
          (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullSkipClSpec : Spec [i64, i64] [.bool] := fun (cend, d, ()) m Q _ =>
  ∃ (cnf_ptr nc val0 : BitVec 64) (mv : Nat) (cnfBytes : List UInt8) (i0 : Nat)
    (R : Mem 64 → Prop),
    cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
    mv < 2 ^ 64 ∧ i0 ≤ cnfBytes.length ∧
    (bytes cnf_ptr cnfBytes ⋆
      dimacsState d (BitVec.ofNat 64 mv) nc (cnf_ptr + BitVec.ofNat 64 i0) val0 ⋆ R) m ∧
    match parseClause mv (cnfBytes.drop i0) with
    | none =>
      ∀ cur' val' m',
        (bytes cnf_ptr cnfBytes ⋆ dimacsState d (BitVec.ofNat 64 mv) nc cur' val' ⋆ R) m' →
        Q (false, ()) m'
    | some (cl, rest) =>
      ∀ j m', (∀ lit ∈ cl.literals, 1 ≤ lit.1) → i0 < j → j ≤ cnfBytes.length →
        cnfBytes.drop j = rest →
        (bytes cnf_ptr cnfBytes ⋆
          dimacsState d (BitVec.ofNat 64 mv) nc (cnf_ptr + BitVec.ofNat 64 j) 0#64 ⋆ R) m' →
        Q (true, ()) m'

def fullIngestClSpec : Spec [i64, i64] [i64] := fun (h, cend, ()) m Q _ =>
  ∃ (c : FullCfg) (accCnf : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (cnf_ptr : BitVec 64) (cnfBytes : List UInt8) (i0 : Nat) (R : Mem 64 → Prop),
    h = c.hdr ∧ cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧ i0 ≤ cnfBytes.length ∧
    s.core.cur_vars = c.mv ∧ s.core.d_cur = cnf_ptr + BitVec.ofNat 64 i0 ∧
    s.core.cur_level = 0 ∧ FullSparseInvW c (shiftDownCnf accCnf) F_cur s ∧
    (shiftDownCnf accCnf).Entails (cnfOfClauses F_cur) ∧
    (bytes cnf_ptr cnfBytes ⋆ FullMem c s ⋆ R) m ∧
    match parseClause c.mv (cnfBytes.drop i0) with
    | none =>
      ∀ s' m', s'.LengthsOk c → s'.core.fuel = s.core.fuel → s'.core.oom = s.core.oom →
        s'.core.probing = s.core.probing →
        (bytes cnf_ptr cnfBytes ⋆ FullMem c s' ⋆ R) m' → Q (0#64, ()) m'
    | some (cl, rest) =>
      ∀ r s' j m',
        (∀ lit ∈ cl.literals, 1 ≤ lit.1) →
        i0 < j → j ≤ cnfBytes.length → cnfBytes.drop j = rest →
        s'.LengthsOk c → s'.core.cur_vars = c.mv →
        s'.core.d_cur = cnf_ptr + BitVec.ofNat 64 j →
        s'.core.cur_level = 0 → s'.core.fuel = s.core.fuel → s'.core.oom = s.core.oom →
        s'.core.probing = s.core.probing →
        (r = 1#64 ∨ r = 2#64 ∨ r = 3#64) →
        (r = 1#64 → ∃ F_cur', FullSparseInvW c (shiftDownCnf (accCnf.add cl)) F_cur' s' ∧
          (shiftDownCnf (accCnf.add cl)).Entails (cnfOfClauses F_cur')) →
        (r = 2#64 → (shiftDownCnf (accCnf.add cl)).Unsat) →
        (∀ l < 2 * c.mv, cl = CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l] →
          s.core.vals[l]?.getD 0#8 = 0#8 →
          r = 1#64 ∧
          (∀ k < 2 * c.mv, s'.core.vals[k]?.getD 0#8 =
            ((s.core.vals.set l 1#8).set (l ^^^ 1) 0xFF#8)[k]?.getD 0#8) ∧
          s'.core.trail_end = s.core.trail_end + 1 ∧ s'.core.propagated = s.core.propagated) →
        (∀ l < 2 * c.mv, cl = CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l] →
          s.core.vals[l]?.getD 0#8 = 0xFF#8 → r = 2#64) →
        (bytes cnf_ptr cnfBytes ⋆ FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullParseBodySpec : Spec [i64, i64] [i64] := fun (h, cend, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (cnf_ptr : BitVec 64) (cnfBytes : List UInt8)
    (i0 : Nat) (R : Mem 64 → Prop),
    h = c.hdr ∧ cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
    cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧ i0 ≤ cnfBytes.length ∧
    parseHeader cnfBytes = some (c.mv, c.nc, cnfBytes.drop i0) ∧
    s.core.cur_vars = c.mv ∧ s.core.d_cur = cnf_ptr + BitVec.ofNat 64 i0 ∧
    s.core.cur_level = 0 ∧ s.core.trail_end = 0 ∧ s.core.propagated = 0 ∧
    s.core.arena_len = 0 ∧ s.core.oom = 0#64 ∧ s.core.probing = 0#64 ∧
    s.core.inconsistent = 0#64 ∧
    s.core.vals = List.replicate (2 * c.max_vars) 0#8 ∧
    s.core.wvec = List.replicate (4 * c.max_vars) 0#32 ∧
    FullSparseInv c (shiftDownCnf CNF.empty) s ∧
    (bytes cnf_ptr cnfBytes ⋆ FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) → s'.core.fuel = s.core.fuel →
      s'.core.oom = 0#64 → s'.core.probing = 0#64 →
      (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ cnf.Unsat) →
      (r = 1#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
        FullSparseInv c (shiftDownCnf cnf) s' ∧ s'.core.cur_level = 0) →
      (UnitUnsatTrace c.mv (s.core.vals.take (2 * c.mv)) (cnfBytes.drop i0) c.nc → r = 20#64) →
      (bytes cnf_ptr cnfBytes ⋆ FullMem c s' ⋆ R) m' → Q (r, ()) m'

end FullDimacsBodySpecs

section SkipClProof

open scoped FullArenaTactics FullDimacsBodyTactics
open FullDimacsBodyTactics FullDimacsBodySpecs

/-! ## `full_skip_cl` -/

theorem full_skip_cl_wp (Γ : Env)
    (hLit : ∀ args m Q X, kissatNextLitSpec args m Q X →
      Γ "kissat_next_lit" [i64, i64] [i64] args m Q X) :
    ∀ args m Q X, fullSkipClSpec args m Q X → Func.wp Γ full_skip_cl_body args m Q X := by
  rintro ⟨cend, d, ⟨⟩⟩ m Q X ⟨cnf_ptr, nc, val0, mv, cnfBytes, i0, R, rfl, hfit, hmv64, hi0, hm, hQ⟩
  unfold Func.wp full_skip_cl_body; wp_unfold
  refine wp_loop_group
    (fun r () ml => ∃ idx val_l revLits,
      i0 ≤ idx ∧ idx ≤ cnfBytes.length ∧ r = cnfBytes.length - idx ∧
      (∀ lit ∈ revLits, 1 ≤ lit.1) ∧
      parseClauseAux ((cnfBytes.drop idx).length + 1) mv revLits (cnfBytes.drop idx) =
        parseClause mv (cnfBytes.drop i0) ∧
      (bytes cnf_ptr cnfBytes ⋆
        dimacsState d (BitVec.ofNat 64 mv) nc (cnf_ptr + BitVec.ofNat 64 idx) val_l ⋆ R) ml)
    ?_ ?_
  · rintro L r ⟨⟩ ml ih ⟨idx, val_l, revLits, hi_le, hidx, rfl, hpos_acc, hpc_inv, hml⟩
    pi_steps
    · c0_call hLit
      refine ⟨cnf_ptr, nc, val_l, mv, cnfBytes, idx, R, rfl, hfit, hmv64, hidx, hml, ?_⟩
      cases hnl : nextLitPure mv (cnfBytes.drop idx) with
      | err =>
        intro cur' val' m' hm'; pi_steps
        · rw [← hpc_inv, parseClauseAux_eq_nextLitPure, hnl] at hQ; exact hQ cur' val' m' hm'
        · exact absurd rfl (by assumption : ¬(0#64 : BitVec 64) = 0)
      | endClause rest =>
        intro j m' hij hj hdrop hm'; pi_steps
        · rw [← hpc_inv, parseClauseAux_eq_nextLitPure, hnl] at hQ
          refine hQ j m' (fun lit hlit => ?_) (by omega) hj hdrop hm'
          simp only [CNF.Clause.literals_ofLiterals, List.mem_reverse] at hlit
          exact hpos_acc lit hlit
        · exact absurd rfl (by assumption : ¬(1#64 : BitVec 64) = 1)
      | lit l rest =>
        intro j m' _ _ hij hj hdrop hm'; pi_steps
        refine ih (cnfBytes.length - j) () m' (by omega)
          ⟨j, BitVec.ofNat 64 l, kissatLitToDimacsLiteral l :: revLits, by omega, hj, rfl,
            fun lit hlit => (List.mem_cons.mp hlit).elim
              (fun h => h ▸ by simp [kissatLitToDimacsLiteral]) (hpos_acc lit), ?_, hm'⟩
        have hstep :
            parseClauseAux ((cnfBytes.drop idx).length + 1) mv revLits (cnfBytes.drop idx) =
            parseClauseAux (cnfBytes.drop idx).length mv (kissatLitToDimacsLiteral l :: revLits)
              (cnfBytes.drop j) := by rw [parseClauseAux_eq_nextLitPure, hnl, ← hdrop]
        rw [← hpc_inv, hstep]; exact parseClauseAux_fuel_irrel (by simp) (by simp; omega)
    · cases (by assumption : true = false)
  · intro L hL; pi_steps; exact hL (cnfBytes.length - i0) () m
      ⟨i0, val0, [], Nat.le_refl _, hi0, rfl, (fun _ h => by cases h), rfl, hm⟩

end SkipClProof

end LeanQbe.T.Examples.Kissat.Full
