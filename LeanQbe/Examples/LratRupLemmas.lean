module

public import LeanQbe.Examples.LratRup
public import LeanQbe.Logic.ZeroTerm
public import LeanQbe.Logic.Rules
public import Kraken.Bedrock2.Test.LratTrimRupProof
public import Kraken.SeparationTactics
public import LeanQbe.Wf
import all Kraken.Mem
import all Kraken.Separation

/-!
# The RUP check: correctness

The specification is the one of Kraken's `br_check_clause_non_strictly_by_propagation_ok`
(`LratTrimRupProof.lean`), with `lrat_fail` an `exit` (decision D5). The model and memory predicates
(`assignBytes`, `ClauseTable`, `ZeroTermInts`, `kernelState`, `byte1Array`, …) and the pure RUP lemmas
(`phase1_step_*`, `phase2_inner_*`, `entails_insert_of_unit_prop`, …) are imported from there unchanged;
the loads and stores on those predicates, the bit-vector facts and `solve_bytes_at` are in
`LeanQbe/Logic/`; everything about the program is new.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.LratRup

open Std Std.ExtHashMap Std.Sat
open Std.Tactic.BVDecide.LRAT.Internal
open Kraken.Bedrock2.Test

/-! ## Bit-level facts -/

theorem abs_eq (lit : Val) : (lit ^^^ lit.sshiftRight 63) - lit.sshiftRight 63 = bvAbs lit := by
  rw [sar63, negif]; rfl

theorem negif_eq (b lit : Val) : (b ^^^ lit.sshiftRight 63) - lit.sshiftRight 63 = evalAssignedLit b lit := by
  rw [sar63, negif]; rfl

/-! ## The inline helpers -/

theorem assignedLit_spec {Γ : Env} {Q : Post} {X : XPost} {vb lit : Val} {mv : Nat}
    {assign : Assignment} {R : Mem 64 → Prop} {m : Mem 64} {k : Val → Val → Expr Val Cont}
    (hlit : IsValidLit mv lit) (hm : (byte1Array vb (assignBytes mv assign) ⋆ R) m)
    (hk : wp Γ Q X (k (bvAbs lit) (evalAssignedLit (assignByte assign (toLiteral lit).1) lit)) [] [] m) :
    wp Γ Q X (assignedLit vb lit k) [] [] m := by
  unfold assignedLit
  wp_unfold
  simp only [abs_eq, negif_eq]
  have hi' : (bvAbs lit).toNat < mv + 1 := by have := hlit.2.2.1; omega
  have hi : (bvAbs lit).toNat < (assignBytes mv assign).length := by simpa using hi'
  refine ⟨_, ?_, hk⟩
  rw [← ofNat_bvAbs_toNat lit, loadsb_byte1Array hi
    (by rw [getElem_assignBytes _ _ hi']; exact isInt8_assignByte _ _) hm, getElem_assignBytes _ _ hi']
  rfl

theorem assignLit_spec {Γ : Env} {Q : Post} {X : XPost} {vb tb te sla wlit idx : Val} {mv : Nat}
    {assign : Assignment} {trail : List Val} {t0 : Val} {tf : List Val} {R : Mem 64 → Prop}
    {m : Mem 64} {k : Val → Val → Expr Val Cont}
    (hwlit : IsValidLit mv wlit) (hidx : idx = bvAbs wlit)
    (hte : te = tb + BitVec.ofNat 64 (4 * trail.length))
    (hcov : TrailCoversAssign mv assign trail)
    (hm : ((byte1Array vb (assignBytes mv assign) ⋆ int4Array tb (trail ++ t0 :: tf)) ⋆ R) m)
    (hk : ∀ m', te + 4 = tb + BitVec.ofNat 64 (4 * (trail ++ [wlit]).length) →
      TrailCoversAssign mv (assign.insert (toLiteral wlit).1 (toLiteral wlit).2) (trail ++ [wlit]) →
      ((byte1Array vb (assignBytes mv (assign.insert (toLiteral wlit).1 (toLiteral wlit).2)) ⋆
        int4Array tb ((trail ++ [wlit]) ++ tf)) ⋆ R) m' →
      wp Γ Q X (k (te + 4) (sla + 1)) [] [] m') :
    wp Γ Q X (assignLit vb te sla wlit idx k) [] [] m := by
  unfold assignLit; subst hidx hte
  wp_unfold
  rw [show (BitVec.sshiftRight wlit 63 ||| 1) = bvSignByte wlit from rfl]
  have hi : (toLiteral wlit).1 < (assignBytes mv assign).length := by
    simp [toLiteral]; have := hwlit.2.2.1; omega
  rw [sep_assoc] at hm
  have ⟨ok1, hm1⟩ := storeb_byte1Array (bvSignByte wlit) hi hm
  rw [assignBytes_set_insert mv assign hwlit, sep_comm_l] at hm1
  have ⟨ok2, hm2⟩ := storew_int4Array (i := trail.length) wlit (by simp) hm1
  rw [show (trail ++ t0 :: tf).set trail.length wlit = (trail ++ [wlit]) ++ tf by
    simp [List.set_append_right]] at hm2
  have ha : vb + bvAbs wlit = vb + BitVec.ofNat 64 (toLiteral wlit).1 := by
    simp [toLiteral]
  rw [ha]
  refine ⟨ok1, ok2, hk _ ?_ (trailCoversAssign_insert wlit hcov) (sep_cast hm2 (by ac_rfl))⟩
  grind

theorem flush_spec {Γ : Env} {Q : Post} {X : XPost} {st te sr sla : Val} {k : KernelFields}
    {R : Mem 64 → Prop} {m : Mem 64} {kc : Expr Val Cont}
    (hm : (kernelState st k ⋆ R) m)
    (hk : ∀ m', (kernelState st
        { k with trail_end := te, stat_resolved := sr, stat_lit_assigned := sla } ⋆ R) m' →
      wp Γ Q X kc [] [] m') :
    wp Γ Q X (flush st te sr sla kc) [] [] m := by
  unfold flush; unfold kernelState at hm hk
  wp_unfold
  have ⟨ok1, hm1⟩ := storel_word8Array (i := 6) te (by simp [KernelFields.toList]) hm
  have ⟨ok2, hm2⟩ := storel_word8Array (i := 18) sr (by simp [KernelFields.toList]) hm1
  have ⟨ok3, hm3⟩ := storel_word8Array (i := 19) sla (by simp [KernelFields.toList]) hm2
  exact ⟨ok1, ok2, ok3, hk _ hm3⟩

theorem backtrack_spec {Γ : Env} {Q : Post} {X : XPost} {vb tb te : Val} {mv : Nat}
    {assign : Assignment} {trail tf : List Val} {R : Mem 64 → Prop} {m : Mem 64} {kc : Expr Val Cont}
    (hte : te = tb + BitVec.ofNat 64 (4 * trail.length))
    (hvalid : ∀ t ∈ trail, IsValidLit mv t) (hlen : 4 * trail.length < 2 ^ 64)
    (hcov : TrailCoversAssign mv assign trail)
    (hm : ((byte1Array vb (assignBytes mv assign) ⋆ int4Array tb (trail ++ tf)) ⋆ R) m)
    (hk : ∀ m', ((byte1Array vb (assignBytes mv Assignment.empty) ⋆ int4Array tb (trail ++ tf)) ⋆ R) m' →
      wp Γ Q X kc [] [] m') :
    wp Γ Q X (backtrack vb tb te kc) [] [] m := by
  unfold backtrack
  apply wp_loop (fun r as m => ∃ i, i ≤ trail.length ∧ r = trail.length - i ∧
    as = [tb + BitVec.ofNat 64 (4 * i)] ∧
    ((byte1Array vb (clearTrailBytes (assignBytes mv assign) (trail.take i)) ⋆
      int4Array tb (trail ++ tf)) ⋆ R) m)
  · rintro J r as m ⟨i, hi, rfl, rfl, hm⟩ ih
    wp_unfold
    refine ⟨fun heq => ?_, fun hne => ?_⟩
    · obtain rfl : i = trail.length := by
        grind
      rw [List.take_length, clearTrailBytes_assignBytes hcov] at hm
      exact hk m hm
    · have hlt : i < trail.length := by
        grind
      have hv := hvalid trail[i] (List.getElem_mem hlt)
      have hget : (trail ++ tf)[i]'(by simp; omega) = trail[i] := List.getElem_append_left hlt
      rw [sep_assoc, sep_comm_l] at hm
      have hld := loadsw_int4Array (i := i) (by simp; omega) (by rw [hget]; exact hv.1) hm
      rw [hget] at hld
      refine ⟨_, hld, ?_⟩
      rw [abs_eq, ← ofNat_bvAbs_toNat]
      rw [sep_comm_l] at hm
      have hidx : (bvAbs trail[i]).toNat < (clearTrailBytes (assignBytes mv assign) (trail.take i)).length := by
        simp; have := hv.2.2.1; omega
      have ⟨ok, hm1⟩ := storeb_byte1Array 0 hidx hm
      rw [clearTrailBytes_take_succ _ trail hlt] at hm1
      refine ⟨ok, ih _ _ _ (by omega) ⟨i + 1, hlt, rfl, ?_, by rwa [sep_assoc]⟩⟩
      simp [ptr_step_4]
  · intro J hJ
    wp_unfold
    exact hJ _ _ _ ⟨0, Nat.zero_le _, rfl, by simp, by simpa using hm⟩

/-! ## Propagation state -/

/-- The values array represents `assign`, the trail array holds `trail` and then the free space
`tf` (total length `N`), and `te` points just after `trail`. -/
def PState (mv : Nat) (vb tb te : Val) (assign : Assignment) (trail tf : List Val) (N : Nat) :
    Mem 64 → Prop := fun m =>
  te = tb + BitVec.ofNat 64 (4 * trail.length) ∧ TrailCoversAssign mv assign trail ∧
    (∀ t ∈ trail, IsValidLit mv t) ∧ trail.length + tf.length = N ∧
    (byte1Array vb (assignBytes mv assign) ⋆ int4Array tb (trail ++ tf)) m

theorem pstate_sep {mv : Nat} {vb tb te : Val} {assign : Assignment} {trail tf : List Val} {N : Nat}
    {F : Mem 64 → Prop} {m : Mem 64} :
    (PState mv vb tb te assign trail tf N ⋆ F) m ↔
      te = tb + BitVec.ofNat 64 (4 * trail.length) ∧ TrailCoversAssign mv assign trail ∧
      (∀ t ∈ trail, IsValidLit mv t) ∧ trail.length + tf.length = N ∧
      ((byte1Array vb (assignBytes mv assign) ⋆ int4Array tb (trail ++ tf)) ⋆ F) m := by
  unfold PState; simp only [sep_pure_l]

theorem assignedLit_pstate {Γ : Env} {Q : Post} {X : XPost} {vb tb te lit : Val}
    {mv N : Nat} {assign : Assignment} {trail tf : List Val} {R : Mem 64 → Prop} {m : Mem 64}
    {k : Val → Val → Expr Val Cont} (hlit : IsValidLit mv lit)
    (hm : (PState mv vb tb te assign trail tf N ⋆ R) m)
    (hk : wp Γ Q X (k (bvAbs lit) (evalAssignedLit (assignByte assign (toLiteral lit).1) lit)) [] [] m) :
    wp Γ Q X (assignedLit vb lit k) [] [] m := by
  have hm' := (pstate_sep.1 hm).2.2.2.2
  rw [sep_assoc] at hm'
  exact assignedLit_spec hlit hm' hk

theorem assignLit_pstate {Γ : Env} {Q : Post} {X : XPost} {vb tb te sla wlit idx : Val}
    {mv N : Nat} {assign : Assignment} {trail tf : List Val} {R : Mem 64 → Prop} {m : Mem 64}
    {k : Val → Val → Expr Val Cont}
    (hwlit : IsValidLit mv wlit) (hidx : idx = bvAbs wlit)
    (hm : (PState mv vb tb te assign trail tf N ⋆ R) m) (hcap : 1 ≤ tf.length)
    (hk : ∀ m' te' tf', tf'.length + 1 = tf.length →
      (PState mv vb tb te' (assign.insert (toLiteral wlit).1 (toLiteral wlit).2)
        (trail ++ [wlit]) tf' N ⋆ R) m' →
      wp Γ Q X (k te' (sla + 1)) [] [] m') :
    wp Γ Q X (assignLit vb te sla wlit idx k) [] [] m := by
  obtain ⟨hte, hcov, htv, hlen, hm⟩ := pstate_sep.1 hm
  rcases tf with _ | ⟨t0, tf'⟩
  · simp at hcap
  refine assignLit_spec hwlit hidx hte hcov hm fun m' hte' hcov' hm' => hk m' _ tf' rfl ?_
  refine pstate_sep.2 ⟨hte', hcov', ?_, by simp at hlen ⊢; omega, hm'⟩
  grind

/-! ## Phase 1 -/

theorem phase1_spec {Γ : Env} {Q : Post} {X : XPost} {finish ph2 : Cont}
    {vb tb lits sr : Val} {mv reserve : Nat} {ls tf0 : List Val} {R : Mem 64 → Prop} {m : Mem 64}
    (hvalid : ∀ x ∈ ls, IsValidLit mv x) (hcap : reserve + ls.length ≤ tf0.length)
    (hm : (PState mv vb tb tb Assignment.empty [] tf0 tf0.length ⋆ (ZeroTermInts lits ls ⋆ R)) m)
    (hfin : ∀ m' te sla assign trail tf,
      (PState mv vb tb te assign trail tf tf0.length ⋆ (ZeroTermInts lits ls ⋆ R)) m' →
      reserve ≤ tf.length →
      (∃ atom pol, (atom, pol) ∈ toClause ls ∧ (atom, !pol) ∈ toClause ls) → finish [te, sr, sla] m')
    (hph2 : ∀ m' te sla assign trail tf,
      (PState mv vb tb te assign trail tf tf0.length ⋆ (ZeroTermInts lits ls ⋆ R)) m' →
      reserve ≤ tf.length →
      (∀ x : Literal Nat, x ∈ toClause ls ↔ assign.get? x.1 = some !x.2) → ph2 [te, sla] m')
    (sla0 : Val) :
    wp Γ Q X (phase1 finish ph2 vb lits tb sr sla0) [] [] m := by
  unfold phase1
  have h32 : ∀ x ∈ ls, IsInt32 x := fun x hx => (hvalid x hx).1
  have hne0 : ∀ x ∈ ls, x ≠ 0 := fun x hx => (hvalid x hx).2.1
  apply wp_loop (fun r as m => ∃ i te sla assign trail tf,
    as = [lits + BitVec.ofNat 64 (4 * i), te, sla] ∧ i ≤ ls.length ∧ r = ls.length - i ∧
    reserve + (ls.length - i) ≤ tf.length ∧
    (PState mv vb tb te assign trail tf tf0.length ⋆ (ZeroTermInts lits ls ⋆ R)) m ∧
    ∀ x : Literal Nat, x ∈ (ls.take i).map toLiteral ↔ assign.get? x.1 = some !x.2)
  · rintro J r as m ⟨i, te, sla, assign, trail, tf, rfl, hi, rfl, hcap, hm, hinv⟩ ih
    wp_unfold
    refine zeroTerm_jnz_step hi h32 hne0 (by ecancel) (fun hlt => ?_) (fun heq => ?_)
    · have hlit := hvalid ls[i] (List.getElem_mem hlt)
      have hcases := evalAssignedLit_cases assign hlit
      refine assignedLit_pstate hlit hm ?_
      wp_unfold
      refine ⟨fun hneg => ih _ _ _ (by omega) ⟨i + 1, te, sla, assign, trail, tf, by rw [ptr4], hlt,
          rfl, by omega, hm, phase1_step_already_falsified hlt hinv (hcases.1 hneg)⟩,
        fun hneg => ⟨fun hpos => hfin m te sla assign trail tf hm (by omega)
          (phase1_step_tautology hlt hinv (hcases.2.1 ⟨hneg, hpos⟩)), fun hpos => ?_⟩⟩
      have hun := hcases.2.2 ⟨hneg, hpos⟩
      rw [show (0 : Val) - ls[i] = -ls[i] by simp]
      refine assignLit_pstate (isValidLit_neg hlit) (bvAbs_neg hlit).symm hm (by omega)
        fun m' te' tf' htf' hm' => ?_
      wp_unfold
      exact ih _ _ _ (by omega) ⟨i + 1, te', _, _, _, tf', by rw [ptr4], hlt, rfl, by omega, hm',
        phase1_step_insert hlt hlit hinv hun.1⟩
    · subst heq; rw [List.take_length] at hinv
      exact hph2 m te sla assign trail tf hm (by omega)
        fun x => by rw [← CNF.Clause.mem_literals_iff, literals_toClause, hinv x]
  · intro J hJ
    wp_unfold
    exact hJ _ _ _ ⟨0, tb, sla0, _, [], tf0, by simp, Nat.zero_le _, rfl, by omega, hm, by simp⟩

/-! ## Phase 2, inner loop -/

/-- The state of the inner loop after `i` literals of the antecedent: no unit yet and everything
falsified, or a unit literal `unit` that is now true and everything else falsified. -/
def InnerSt (mv reserve : Nat) (clits : List Val) (curAssign : Assignment) (i : Nat) (unit : Val)
    (assign : Assignment) (tf : List Val) : Prop :=
  (unit = 0 ∧ assign = curAssign ∧ reserve + 1 ≤ tf.length ∧
      ∀ x : Literal Nat, x ∈ (clits.take i).map toLiteral → curAssign.get? x.1 = some !x.2) ∨
  (unit ≠ 0 ∧ IsValidLit mv unit ∧ assign.get? (toLiteral unit).1 = some (toLiteral unit).2 ∧
      reserve ≤ tf.length ∧
      ((curAssign.get? (toLiteral unit).1 = none ∧
        assign = curAssign.insert (toLiteral unit).1 (toLiteral unit).2) ∨ assign = curAssign) ∧
      ∀ x : Literal Nat, x ∈ (clits.take i).map toLiteral →
        x = toLiteral unit ∨ curAssign.get? x.1 = some !x.2)

theorem inner_spec {Γ : Env} {Q : Post} {X : XPost} {fail done : Cont}
    {vb tb aid als te0 sr : Val} {mv reserve N : Nat} {clits : List Val} {f : CNF Nat}
    {initAssign curAssign : Assignment} {curTrail curTf : List Val} {R : Mem 64 → Prop} {m : Mem 64}
    (hvalid : ∀ x ∈ clits, IsValidLit mv x) (hcl : toClause clits ∈ f)
    (hent : CNF.Entails (f ++ initAssign.toCNF) (f ++ curAssign.toCNF))
    (hcap : reserve + 1 ≤ curTf.length)
    (hm : (PState mv vb tb te0 curAssign curTrail curTf N ⋆ (ZeroTermInts als clits ⋆ R)) m)
    (hfail : ∀ m' te sla assign trail tf,
      (PState mv vb tb te assign trail tf N ⋆ (ZeroTermInts als clits ⋆ R)) m' →
      fail [2, aid, te, sr, sla] m')
    (hdone : ∀ m' unit te sla assign trail tf,
      (PState mv vb tb te assign trail tf N ⋆ (ZeroTermInts als clits ⋆ R)) m' →
      ((unit = 0 ∧ reserve + 1 ≤ tf.length ∧ CNF.Unsat (f ++ initAssign.toCNF)) ∨
       (unit ≠ 0 ∧ IsInt32 unit ∧ reserve ≤ tf.length ∧
        CNF.Entails (f ++ initAssign.toCNF) (f ++ assign.toCNF))) →
      done [unit, te, sla] m')
    (sla0 : Val) :
    wp Γ Q X (inner fail done vb aid als te0 sr sla0) [] [] m := by
  unfold inner
  have h32 : ∀ x ∈ clits, IsInt32 x := fun x hx => (hvalid x hx).1
  have hne0 : ∀ x ∈ clits, x ≠ 0 := fun x hx => (hvalid x hx).2.1
  apply wp_loop (fun r as m => ∃ i unit te sla assign trail tf,
    as = [als + BitVec.ofNat 64 (4 * i), unit, te, sla] ∧ i ≤ clits.length ∧ r = clits.length - i ∧
    (PState mv vb tb te assign trail tf N ⋆ (ZeroTermInts als clits ⋆ R)) m ∧
    InnerSt mv reserve clits curAssign i unit assign tf)
  · rintro J r as m' ⟨i, unit, te, sla, assign, trail, tf, rfl, hi, rfl, hm', hst⟩ ih
    wp_unfold
    refine zeroTerm_jnz_step hi h32 hne0 (by ecancel) (fun hlt => ?_) (fun heq => ?_)
    · have hlit := hvalid clits[i] (List.getElem_mem hlt)
      have hcases := evalAssignedLit_cases assign hlit
      refine assignedLit_pstate hlit hm' ?_
      wp_unfold
      have hstep : ∀ unit' assign' trail' tf' te' sla' m'', (PState mv vb tb te' assign' trail' tf' N ⋆
          (ZeroTermInts als clits ⋆ R)) m'' → InnerSt mv reserve clits curAssign (i + 1) unit' assign' tf' →
          J [als + BitVec.ofNat 64 (4 * i) + 4, unit', te', sla'] m'' := fun _ _ _ _ _ _ _ hm'' hst' =>
        ih _ _ _ (by omega) ⟨i + 1, _, _, _, _, _, _, by rw [ptr4], hlt, rfl, hm'', hst'⟩
      refine ⟨fun hneg => ?_, fun hneg => ?_⟩
      · -- the literal is false: a conflict with the unit fails, otherwise go on
        have hfals := hcases.1 hneg
        rw [show (0 : Val) - clits[i] = -clits[i] by simp]
        refine ⟨fun _ => hfail m' te sla assign trail tf hm', fun hne => hstep _ _ _ _ _ _ _ hm' ?_⟩
        rcases hst with ⟨rfl, rfl, hc, hinv⟩ | ⟨hu, huv, hus, hc, hrel, hinv⟩
        · exact Or.inl ⟨rfl, rfl, hc, phase2_inner_falsified_unit0 hlt hinv hfals⟩
        · exact Or.inr ⟨hu, huv, hus, hc, hrel,
            phase2_inner_falsified_unit_ne0 hlt hlit hus hrel hinv hfals hne⟩
      · -- the literal is true or unassigned: it becomes the unit (`@setunit`)
        apply wp_join (fun as m'' => as = [] ∧ m'' = m' ∧ (unit = 0 ∨ unit = clits[i]))
        · rintro _ _ ⟨rfl, rfl, hu⟩
          wp_unfold
          refine ⟨fun hv0 => ?_, fun hv0 => ?_⟩
          · have hun := (hcases.2.2 ⟨hneg, by rw [hv0]; decide⟩).1
            rcases hst with ⟨rfl, rfl, hc, hinv⟩ | ⟨hu', _, hus, _, _, _⟩
            · refine assignLit_pstate hlit rfl hm' (by omega) fun m'' te' tf' htf' hm'' => ?_
              wp_unfold
              exact hstep _ _ _ _ _ _ _ hm''
                (Or.inr ⟨hlit.2.1, hlit, Assignment.get?_insert_of_eq rfl, by omega,
                  Or.inl ⟨hun, rfl⟩, phase2_inner_new_unit hlt hinv⟩)
            · grind
          · have hpos : (0 : Val).slt (evalAssignedLit (assignByte assign (toLiteral clits[i]).1)
                clits[i]) = true := by
              grind
            have hsat := hcases.2.1 ⟨hneg, hpos⟩
            refine hstep _ _ _ _ _ _ _ hm' ?_
            rcases hst with ⟨rfl, rfl, hc, hinv⟩ | ⟨hu', huv, hus, hc, hrel, hinv⟩
            · exact Or.inr ⟨hlit.2.1, hlit, hsat, by omega, Or.inr rfl, phase2_inner_new_unit hlt hinv⟩
            · rcases hu with hu | rfl
              · exact absurd hu hu'
              · exact Or.inr ⟨hu', huv, hus, hc, hrel, phase2_inner_dup_unit hlt rfl hinv⟩
        · intro K hK
          wp_unfold
          have hu32 : IsInt32 unit := by
            rcases hst with ⟨rfl, _⟩ | ⟨_, huv, _⟩
            · exact isInt32_zero
            · exact huv.1
          rw [truthy_iff _ hu32]
          grind
    · subst heq; rw [InnerSt, List.take_length] at hst
      rcases hst with ⟨rfl, rfl, hc, hall⟩ | ⟨hu, huv, _, hc, hrel, hinv⟩
      · refine hdone m' 0 te sla _ trail tf hm' (Or.inl ⟨rfl, hc, ?_⟩)
        exact unsat_of_all_falsified hcl hent fun x hx => by
          rw [← CNF.Clause.mem_literals_iff, literals_toClause] at hx; exact hall x hx
      · refine hdone m' unit te sla assign trail tf hm' (Or.inr ⟨hu, huv.1, hc, ?_⟩)
        rcases hrel with ⟨_, rfl⟩ | rfl
        · exact entails_insert_of_unit_prop hcl hent fun x hx => by
            rw [← CNF.Clause.mem_literals_iff, literals_toClause] at hx; exact hinv x hx
        · exact hent
  · intro J hJ
    wp_unfold
    exact hJ _ _ _ ⟨0, 0, te0, sla0, curAssign, curTrail, curTf, by simp, Nat.zero_le _, rfl, hm,
      Or.inl ⟨rfl, rfl, hcap, by simp⟩⟩

/-! ## Phase 2, outer loop -/

theorem phase2_spec {Γ : Env} {Q : Post} {X : XPost} {fail finish : Cont}
    {lb vb tb ants te0 sr0 : Val} {mv N : Nat} {lit_ptrs aids : List Val} {s : State}
    {initAssign assign0 : Assignment} {trail0 tf0 : List Val} {P_ro R : Mem 64 → Prop} {m : Mem 64}
    (hct : ClauseTable mv lb lit_ptrs s.formula P_ro)
    (haids_ro : ∃ R_aids, P_ro = (ZeroTermInts ants aids ⋆ R_aids))
    (haids_valid : ∀ aid ∈ aids, IsInt32 aid ∧ aid ≠ 0 ∧
      (aid.slt 0 = false → ∃ h : aid.toNat < lit_ptrs.length, lit_ptrs[aid.toNat] ≠ 0))
    (hcap0 : aids.length ≤ tf0.length)
    (hent0 : CNF.Entails (s.toCNF ++ initAssign.toCNF) (s.toCNF ++ assign0.toCNF))
    (hm : (PState mv vb tb te0 assign0 trail0 tf0 N ⋆ (R ⋆ P_ro)) m)
    (hfail : ∀ m' code aid te sr sla assign trail tf,
      (PState mv vb tb te assign trail tf N ⋆ (R ⋆ P_ro)) m' → fail [code, aid, te, sr, sla] m')
    (hfin : ∀ m' te sr sla assign trail tf,
      (PState mv vb tb te assign trail tf N ⋆ (R ⋆ P_ro)) m' →
      CNF.Unsat (s.toCNF ++ initAssign.toCNF) → finish [te, sr, sla] m')
    (sla0 : Val) :
    wp Γ Q X (phase2 fail finish lb vb ants te0 sr0 sla0) [] [] m := by
  unfold phase2
  obtain ⟨R_aids, hP_aids⟩ := haids_ro
  have h32 : ∀ x ∈ aids, IsInt32 x := fun x hx => (haids_valid x hx).1
  have hne0 : ∀ x ∈ aids, x ≠ 0 := fun x hx => (haids_valid x hx).2.1
  apply wp_loop (fun r as m => ∃ j te sr sla assign trail tf,
    as = [ants + BitVec.ofNat 64 (4 * j), te, sr, sla] ∧ j ≤ aids.length ∧ r = aids.length - j ∧
    aids.length - j ≤ tf.length ∧ (PState mv vb tb te assign trail tf N ⋆ (R ⋆ P_ro)) m ∧
    CNF.Entails (s.toCNF ++ initAssign.toCNF) (s.toCNF ++ assign.toCNF))
  · rintro J r as m ⟨j, te, sr, sla, assign, trail, tf, rfl, hj, rfl, hcap, hm, hent⟩ ih
    wp_unfold
    have hma := hm; rw [hP_aids] at hma
    refine zeroTerm_jnz_step hj h32 hne0 (by ecancel) (fun hlt => ?_)
      (fun _ => hfail m _ _ _ _ _ _ _ _ hm)
    obtain ⟨_, _, hpos⟩ := haids_valid aids[j] (List.getElem_mem hlt)
    refine ⟨fun _ => hfail m _ _ _ _ _ _ _ _ hm, fun hneg => ?_⟩
    obtain ⟨hal, hptr⟩ := hpos (by simpa using hneg)
    obtain ⟨R1, hP1⟩ := hct.1
    have hm1 : (PState mv vb tb te assign trail tf N ⋆ (R ⋆ (word8Array lb lit_ptrs ⋆ R1))) m :=
      hP1 ▸ hm
    refine ⟨_, loadl_word8Array (a := lb) hal (by ecancel), ?_⟩
    have haid0 : 0 < aids[j].toNat := by
      grind
    obtain ⟨clits, R2, hP2, hcl_valid, hcl_get⟩ := hct.2 aids[j].toNat hal haid0 hptr
    have hcl := mem_toCNF_of_formula_getElem? hcl_get
    apply wp_join (fun as m' => ∃ unit te2 sla2 assign' trail' tf', as = [unit, te2, sla2] ∧
      (PState mv vb tb te2 assign' trail' tf' N ⋆ (R ⋆ P_ro)) m' ∧
      ((unit = 0 ∧ CNF.Unsat (s.toCNF ++ initAssign.toCNF)) ∨
       (unit ≠ 0 ∧ IsInt32 unit ∧ aids.length - (j + 1) ≤ tf'.length ∧
        CNF.Entails (s.toCNF ++ initAssign.toCNF) (s.toCNF ++ assign'.toCNF))))
    · rintro _ m' ⟨unit, te2, sla2, assign', trail', tf', rfl, hm', hres⟩
      wp_unfold
      rcases hres with ⟨rfl, hunsat⟩ | ⟨hu, hu32, hc', hent'⟩
      · refine ⟨fun h => absurd h (by decide), fun _ => hfin _ _ _ _ _ _ _ hm' hunsat⟩
      · rw [truthy_iff _ hu32]
        refine ⟨fun _ => ih _ _ _ (by omega) ⟨j + 1, _, _, _, _, _, _, by rw [ptr4], hlt, rfl, hc',
          hm', hent'⟩, fun h => absurd hu h⟩
    · intro K hK
      have hm2 : (PState mv vb tb te assign trail tf N ⋆ (ZeroTermInts lit_ptrs[aids[j].toNat] clits ⋆
          (R ⋆ R2))) m := sep_cast (hP2 ▸ hm) (by ac_rfl)
      have back : ∀ {P : Mem 64 → Prop} {m'}, (P ⋆ (ZeroTermInts lit_ptrs[aids[j].toNat] clits ⋆
          (R ⋆ R2))) m' → (P ⋆ (R ⋆ P_ro)) m' := fun h => by rw [hP2]; exact sep_cast h (by ac_rfl)
      refine inner_spec (reserve := aids.length - (j + 1)) hcl_valid hcl hent (by omega) hm2
        (fun m' te' sla' assign' trail' tf' h => hfail _ _ _ _ _ _ _ _ _ (back h))
        (fun m' unit te' sla' assign' trail' tf' h hres => hK _ _ ⟨unit, te', sla', assign', trail',
          tf', rfl, back h, ?_⟩) sla
      grind
  · intro J hJ
    wp_unfold
    exact hJ _ _ _ ⟨0, te0, sr0, sla0, assign0, trail0, tf0, by simp, Nat.zero_le _, rfl, by omega,
      hm, hent0⟩

/-! ## The function -/

theorem loadl_kfield {st : Val} {k : KernelFields} {R : Mem 64 → Prop} {m : Mem 64} (i : Nat)
    (hi : i < 20) (h : (kernelState st k ⋆ R) m) {a : Val} (ha : a = st + BitVec.ofNat 64 (8 * i)) :
    loadVal m .l .l true a = some (k.toList[i]'(by simpa [KernelFields.toList] using hi)) := by
  subst ha; exact loadl_word8Array _ h

theorem checkRup_correct (Γ : Env) :
    ∀ args m Q X, checkRupSpec args m Q X → Func.spec Γ checkRup args m Q X := by
  rintro _ m Q X ⟨st, id, literals, antecedents, mv, k, lits, aids, lit_ptrs, tf0, s, P_ro, rfl,
    hk_trail, hct, ⟨R_lits, hP_lits⟩, haids_ro, hlits_valid, haids_valid, hcap, htf_len, hsep, hQ, hX⟩
  unfold checkRup Func.spec
  wp_unfold
  refine ⟨_, loadl_kfield 2 (by decide) (by ecancel) rfl, _, loadl_kfield 3 (by decide) (by ecancel) rfl,
    _, loadl_kfield 5 (by decide) (by ecancel) rfl, _, loadl_kfield 6 (by decide) (by ecancel) rfl,
    _, loadl_kfield 18 (by decide) (by ecancel) rfl, _, loadl_kfield 19 (by decide) (by ecancel) rfl, ?_⟩
  simp only [KernelFields.toList, List.getElem_cons_succ, List.getElem_cons_zero, hk_trail]
  -- `@fail`: flush, then exit
  apply wp_join (fun as m => ∃ code aid te sr sla, as = [code, aid, te, sr, sla] ∧
    ∃ F k', (kernelState st k' ⋆ F) m)
  · rintro _ m ⟨code, aid, te, sr, sla, rfl, F, k', hm⟩
    wp_unfold
    exact flush_spec hm fun _ _ => by wp_unfold; exact hX _ _
  intro Jfail hJfail
  -- `@finish`: backtrack, flush, return
  apply wp_join (fun as m => ∃ te sr sla assign trail tf, as = [te, sr, sla] ∧
    (PState mv k.values_begin k.trail_begin te assign trail tf tf0.length ⋆
      (kernelState st k ⋆ P_ro)) m ∧ CNF.EntailsClause s.toCNF (toClause lits))
  · rintro _ m ⟨te, sr, sla, assign, trail, tf, rfl, hm, hentc⟩
    wp_unfold
    obtain ⟨hte, hcov, htv, hlen, hm⟩ := pstate_sep.1 hm
    refine backtrack_spec hte htv (by omega) hcov hm fun m1 hm1 => ?_
    refine flush_spec (k := k) (by ecancel) fun m2 hm2 => ?_
    wp_unfold
    exact hQ m2 sr sla (trail ++ tf) (by simp [hlen]) (by ecancel) hentc
  intro Jfin hJfin
  -- `@ph2`: phase 2 from the negated clause
  apply wp_join (fun as m => ∃ te sla assign trail tf, as = [te, sla] ∧
    (PState mv k.values_begin k.trail_begin te assign trail tf tf0.length ⋆
      (kernelState st k ⋆ P_ro)) m ∧ aids.length ≤ tf.length ∧
    ∀ x : Literal Nat, x ∈ toClause lits ↔ assign.get? x.1 = some !x.2)
  · rintro _ m ⟨te, sla, assign, trail, tf, rfl, hm, hc, hiff⟩
    wp_unfold
    exact phase2_spec (initAssign := assign) hct haids_ro haids_valid hc (CNF.entails_refl _) hm
      (fun _ code aid te sr sla _ _ _ h => hJfail _ _ ⟨code, aid, te, sr, sla, rfl, _, k, sep_cast h (sep_comm_l _ _ _)⟩)
      (fun _ te sr sla assign' trail' tf' h hunsat => hJfin _ _ ⟨te, sr, sla, assign', trail', tf', rfl,
        h, entailsClause_of_unsat_of_iff_falsified hiff hunsat⟩) sla
  intro Jph2 hJph2
  -- phase 1
  have back : ∀ {P : Mem 64 → Prop} {m'}, (P ⋆ (ZeroTermInts literals lits ⋆ (kernelState st k ⋆ R_lits))) m' →
      (P ⋆ (kernelState st k ⋆ P_ro)) m' := fun h => by rw [hP_lits]; ecancel
  have hm1 : (PState mv k.values_begin k.trail_begin k.trail_begin Assignment.empty [] tf0 tf0.length ⋆
      (ZeroTermInts literals lits ⋆ (kernelState st k ⋆ R_lits))) m :=
    pstate_sep.2 ⟨by simp, trailCoversAssign_empty mv, by simp, by simp,
      by rw [List.nil_append, hP_lits] at *; ecancel⟩
  exact phase1_spec (reserve := aids.length) hlits_valid (by omega) hm1
    (fun _ te sla assign trail tf h _ htaut => hJfin _ _ ⟨te, _, sla, assign, trail, tf, rfl, back h,
      entailsClause_of_tautology htaut⟩)
    (fun _ te sla assign trail tf h hc hiff => hJph2 _ _ ⟨te, sla, assign, trail, tf, rfl,
      back h, hc, hiff⟩) _

theorem checkRup_wf : Func.Wf checkRup := by
  unfold checkRup phase1 phase2 inner backtrack flush assignedLit assignLit; wf_tac

/-! ## Non-vacuity -/

theorem KernelFields_toList_length (k : KernelFields) : k.toList.length = 20 := rfl

/-! ## A concrete instance: the tautology `[1, -1]` -/

def nvK : KernelFields :=
  { used_begin := 0, antecedents_begin := 0, literals_begin := 0, values_begin := 0x10a0,
    marks_begin := 0, trail_begin := 0x10a2, trail_end := 0x10a2, work_begin := 0, empty_clause := 0,
    first_proof_id := 0, strict := 0, trimming := 0, checking := 0, forward := 0,
    stat_trimmed_cnf := 0, stat_trimmed_prf := 0, stat_chk_total := 0, stat_chk_empty := 0,
    stat_resolved := 0, stat_lit_assigned := 0 }

def nvBytes : List UInt8 :=
  bytesN 8 nvK.toList ++ (bytesN 1 [0, 0] ++ (bytesN 4 [0, 0] ++ (bytesN 4 [1, -1, 0] ++ bytesN 4 [0])))

theorem nv_mem : ((byte1Array 0x10a0 (assignBytes 1 Assignment.empty) ⋆ int4Array 0x10a2 [0, 0]) ⋆
    (kernelState 0x1000 nvK ⋆ (ZeroTermInts 0x10aa [1, -1] ⋆ ZeroTermInts 0x10b6 []))) (nvBytes.At 0x1000) := by
  rw [assignBytes_empty]
  unfold kernelState ZeroTermInts nvBytes
  solve_bytes_at [KernelFields_toList_length]

/-- `checkRupSpec` is satisfiable: the tautology `[1, -1]`, no antecedents, a trail of two free
slots, in the 186 bytes of `nvBytes` at `0x1000`. -/
theorem checkRup_nonvacuous :
    checkRupSpec [0x1000, 7, 0x10aa, 0x10b6] (nvBytes.At 0x1000)
      (fun rs _ => rs = []) (fun f _ _ => f = "lrat_fail") :=
  ⟨0x1000, 7, 0x10aa, 0x10b6, 1, nvK, [1, -1], [], [], [0, 0], ⟨#[]⟩,
    ZeroTermInts 0x10aa [1, -1] ⋆ ZeroTermInts 0x10b6 [], rfl, rfl,
    ⟨⟨_, by rw [word8Array_nil, emp_sep]⟩, fun _ h => absurd h (by simp)⟩,
    ⟨_, rfl⟩, ⟨_, sep_comm _ _⟩,
    by intro x hx; simp at hx; rcases hx with rfl | rfl <;> (unfold IsValidLit bvAbs; decide),
    by simp, by decide, by decide, nv_mem, fun _ _ _ _ _ _ _ => rfl, fun _ _ => rfl⟩

/-- No assignment falsifies both literals of the tautology `[1, -1]`. -/
theorem not_falsify_taut (assign : Assignment) :
    ¬ ∀ x : Literal Nat, x ∈ toClause [1, -1] ↔ assign.get? x.1 = some !x.2 := by
  intro h
  have h1 := (h (toLiteral 1)).1 (by rw [← CNF.Clause.mem_literals_iff, literals_toClause]; simp)
  have h2 := (h (toLiteral (-1))).1 (by rw [← CNF.Clause.mem_literals_iff, literals_toClause]; simp)
  have e1 : toLiteral 1 = (1, true) := by decide
  have e2 : toLiteral (-1) = (1, false) := by decide
  grind

/-- Completeness data point (Bedrock2's spec has none): on the tautology `[1, -1]` the function
returns, it never exits to `lrat_fail`. -/
theorem checkRup_accepts_tautology (Γ : Env) :
    Func.spec Γ checkRup [0x1000, 7, 0x10aa, 0x10b6] (nvBytes.At 0x1000)
      (fun rs _ => rs = []) (fun _ _ _ => False) := by
  have hsep := nv_mem
  rw [assignBytes_empty] at hsep
  unfold checkRup Func.spec
  wp_unfold
  refine ⟨_, loadl_kfield 2 (by decide) (by ecancel) rfl, _, loadl_kfield 3 (by decide) (by ecancel) rfl,
    _, loadl_kfield 5 (by decide) (by ecancel) rfl, _, loadl_kfield 6 (by decide) (by ecancel) rfl,
    _, loadl_kfield 18 (by decide) (by ecancel) rfl, _, loadl_kfield 19 (by decide) (by ecancel) rfl, ?_⟩
  simp only [KernelFields.toList, List.getElem_cons_succ, List.getElem_cons_zero]
  -- `@fail` is unreachable
  apply wp_join (fun _ _ => False) (fun _ _ h => h.elim)
  intro Jfail _
  -- `@finish`: backtrack, flush, return
  apply wp_join (fun as m => ∃ te sr sla assign trail tf, as = [te, sr, sla] ∧
    (PState 1 nvK.values_begin nvK.trail_begin te assign trail tf ([0, 0] : List Val).length ⋆
      (kernelState 0x1000 nvK ⋆ (ZeroTermInts 0x10aa [1, -1] ⋆ ZeroTermInts 0x10b6 []))) m)
  · rintro _ m ⟨te, sr, sla, assign, trail, tf, rfl, hm⟩
    wp_unfold
    obtain ⟨hte, hcov, htv, hlen, hm⟩ := pstate_sep.1 hm
    refine backtrack_spec hte htv (by simp at hlen; omega) hcov hm fun m1 hm1 => ?_
    refine flush_spec (k := nvK) (by ecancel) fun m2 _ => ?_
    wp_unfold
  intro Jfin hJfin
  -- `@ph2` is unreachable: no assignment falsifies a tautology
  apply wp_join (fun as m => ∃ te sla assign trail tf, as = [te, sla] ∧
    (PState 1 nvK.values_begin nvK.trail_begin te assign trail tf ([0, 0] : List Val).length ⋆
      (kernelState 0x1000 nvK ⋆ (ZeroTermInts 0x10aa [1, -1] ⋆ ZeroTermInts 0x10b6 []))) m ∧
    ∀ x : Literal Nat, x ∈ toClause [1, -1] ↔ assign.get? x.1 = some !x.2)
  · rintro _ _ ⟨_, _, assign, _, _, _, _, hiff⟩
    exact absurd hiff (not_falsify_taut assign)
  intro Jph2 hJph2
  have hm1 : (PState 1 nvK.values_begin nvK.trail_begin nvK.trail_begin Assignment.empty [] [0, 0]
      ([0, 0] : List Val).length ⋆
      (ZeroTermInts 0x10aa [1, -1] ⋆ (kernelState 0x1000 nvK ⋆ ZeroTermInts 0x10b6 [])))
      (nvBytes.At 0x1000) :=
    pstate_sep.2 ⟨by simp, trailCoversAssign_empty 1, by simp, by simp,
      by rw [List.nil_append, assignBytes_empty]; ecancel⟩
  exact phase1_spec (reserve := 0) (by intro x hx; simp at hx; rcases hx with rfl | rfl <;>
      (unfold IsValidLit bvAbs; decide)) (by decide) hm1
    (fun _ te sla assign trail tf h _ _ => hJfin _ _ ⟨te, _, sla, assign, trail, tf, rfl, by ecancel⟩)
    (fun _ te sla assign trail tf h _ hiff => hJph2 _ _ ⟨te, sla, assign, trail, tf, rfl,
      by ecancel, hiff⟩) _

end LeanQbe.LratRup
