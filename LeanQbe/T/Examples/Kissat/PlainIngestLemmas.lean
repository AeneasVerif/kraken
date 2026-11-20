module

public import LeanQbe.T.Examples.Kissat.PlainIngestLemmas2
public import LeanQbe.T.Logic.C0Step
public meta import Lean.Elab.Tactic
public meta import LeanQbe.T.Logic.C0Step
import all Kraken.Mem
import all Kraken.Separation

/-!
# Soundness Proofs for Kissat `D-Plain` Assign, Backtrack & Parse (`Stage 3`, Part 3)

Proves parametric `Func.wp` specifications for:
1. `plain_assign` (`plainAssignSpec`, `plain_assign_wp`)
2. `plain_backtrack` (`plainBacktrackSpec`, `plain_backtrack_wp`)
3. `plain_parse_body` (`plainParseBodySpec`, `plain_parse_body_wp`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Plain

open Std Std.Sat Std.ExtHashMap LeanQbe.T.C0Step
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

open scoped PlainIngestTactics open PlainIngestTactics

private theorem bv64_sub1_toNat {x : BitVec 64} (hx : x ≠ 0#64) :
    (x - 1#64).toNat = x.toNat - 1 := by bv_omega

/-! ## 1. `plain_assign` -/

private def asgSt0 (s : PlainState) (lit : BitVec 32) : PlainState :=
  { s with vals := (s.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8 }

private def asgSt1 (s : PlainState) (lit : BitVec 32) (ph' : List (BitVec 8)) : PlainState :=
  { s with
    vals := (s.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8,
    heur := { s.heur with phases := ph' } }

private def asgSt2 (s : PlainState) (lit : BitVec 32) (ph' : List (BitVec 8)) : PlainState :=
  { s with
    vals := (s.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8,
    lvl := s.lvl.set (lit.toNat / 2) (BitVec.ofNat 32 s.cur_level),
    heur := { s.heur with phases := ph' } }

private def asgSt3 (s : PlainState) (lit rsn' : BitVec 32) (unfl' : BitVec 64)
    (ph' : List (BitVec 8)) : PlainState :=
  { s with
    vals := (s.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8,
    lvl := s.lvl.set (lit.toNat / 2) (BitVec.ofNat 32 s.cur_level),
    rsns := s.rsns.set (lit.toNat / 2) rsn', unflushed := unfl',
    heur := { s.heur with phases := ph' } }

private def asgFin (s : PlainState) (lit rsn' : BitVec 32) (unfl' : BitVec 64)
    (ph' : List (BitVec 8)) : PlainState :=
  { s with
    vals := (s.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8,
    lvl := s.lvl.set (lit.toNat / 2) (BitVec.ofNat 32 s.cur_level),
    rsns := s.rsns.set (lit.toNat / 2) rsn', trl := s.trl.set s.trail_end lit,
    trail_pos := s.trail_pos.set (lit.toNat / 2) (BitVec.ofNat 32 s.trail_end),
    trail_end := s.trail_end + 1, unflushed := unfl',
    heur := { s.heur with phases := ph' } }

private theorem assign_tail_wp {Γ : Env} {c : PlainCfg} {s : PlainState} {lit rsn' : BitVec 32}
    {unfl' : BitVec 64} {ph' : List (BitVec 8)} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []}
    {X : XPost} (hmv : c.mv < 2 ^ 28) (hvar : lit.toNat / 2 < c.mv) (hte : s.trail_end < c.mv)
    (htp : s.trail_pos.length = c.mv) (htr : s.trl.length = c.mv)
    (hte64 : s.trail_end < 2 ^ 64) (hte1_64 : s.trail_end + 1 < 2 ^ 64)
    (hm : (PlainMem c (asgSt3 s lit rsn' unfl' ph') ⋆ R) m)
    (hFin : ∀ m', (PlainMem c (asgFin s lit rsn' unfl' ph') ⋆ R) m' → Q () m') :
    wp Γ Q X
      (Expr.load i64 (Arg.var (c.hdr + 144)) fun ld =>
        Expr.let_ { sig := [i64], code := OpCode.trunc 64 32, args := (Arg.var ld, ()) } fun p =>
          Expr.store (t := i32) (Arg.var p.fst)
            (Arg.var (c.pTrailPos + BitVec.setWidth 64 (lit >>> 1) * 4))
            (Expr.let_
              { sig := [i64, i64], code := OpCode.add i64,
                args := (Arg.var c.hdr, Arg.imm 144, ()) } fun p =>
              Expr.load i64 (Arg.var p.fst) fun ld =>
                Expr.let_
                  { sig := [i64, i64], code := OpCode.mul i64,
                    args := (Arg.var ld, Arg.imm 4, ()) } fun p =>
                  Expr.let_
                    { sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var c.pTrail, Arg.var p.fst, ()) } fun p =>
                    Expr.store (t := i32) (Arg.var lit) (Arg.var p.fst)
                      (Expr.let_
                        { sig := [i64, i64], code := OpCode.add i64,
                          args := (Arg.var c.hdr, Arg.imm 144, ()) } fun p =>
                        Expr.load i64 (Arg.var p.fst) fun ld =>
                          Expr.let_
                            { sig := [i64, i64], code := OpCode.add i64,
                              args := (Arg.var ld, Arg.imm 1, ()) } fun p =>
                            Expr.let_
                              { sig := [i64, i64], code := OpCode.add i64,
                                args := (Arg.var c.hdr, Arg.imm 144, ()) } fun p_1 =>
                              Expr.store (t := i64) (Arg.var p.fst) (Arg.var p_1.fst)
                                (Expr.ret ())))) m := by
  have htp3 : (asgSt3 s lit rsn' unfl' ph').trail_pos.length = c.mv := htp
  have htr3 : (asgSt3 s lit rsn' unfl' ph').trl.length = c.mv := htr
  have hte3 : (asgSt3 s lit rsn' unfl' ph').trail_end = s.trail_end := rfl
  pi_head_steps
  simp only [hte3, bv_c0_zext32_64, bv32_lshr1, bv64_setWidth32_ofNat,
    bv64_ofNat_toNat hte64, bv64_add1_toNat hte1_64] at hm
  have hmFin : (PlainMem c (asgFin s lit rsn' unfl' ph') ⋆ R) _ := hm
  exact hFin _ hmFin

theorem plain_assign_wp (Γ : Env) :
    ∀ a m Q X, plainAssignSpec a m Q X → Func.wp Γ plain_assign_body a m Q X := by
  rintro ⟨h, lit, rsn, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hcl32, hm, hQ⟩
  have hmv := c.hmv; unfold dimacsBound at hmv
  have ⟨hvl, _, hll, hrsl, htrl, htpl, _, _, _, _, _, _, _, _, htel, _, _, _, hh⟩ := hlen
  have hphl := hh.phases_len
  have hte64 : s.trail_end < 2 ^ 64 := by omega
  have hte1_64 : s.trail_end + 1 < 2 ^ 64 := by omega
  unfold Func.wp plain_assign_body; pi_head_steps
  refine wp_jnz_of (fun hge => ?_) (fun hlt => ?_)
  · pi_head_steps
    have h1 : c.mv ≤ lit.toNat / 2 := by
      clear hm hQ; simp only [Arg.val_var, bv_c0] at hge; omega
    simp only [show c.mv ≤ lit.toNat / 2 ∨ c.mv ≤ s.trail_end from Or.inl h1, ite_true] at hQ
    exact hQ
  · have hvar : lit.toNat / 2 < c.mv := by
      clear hm hQ; simp only [Arg.val_var, bv_c0] at hlt; omega
    pi_head_steps; refine wp_jnz_of (fun hte_ge => ?_) (fun hte_lt => ?_)
    · pi_head_steps
      have h2 : c.mv ≤ s.trail_end := by
        clear hm hQ; simp only [Arg.val_var, bv_c0, Nat.reducePow] at hte_ge; omega
      simp only [show c.mv ≤ lit.toNat / 2 ∨ c.mv ≤ s.trail_end from Or.inr h2, ite_true] at hQ
      exact hQ
    · have hte : s.trail_end < c.mv := by
        clear hm hQ; simp only [Arg.val_var, bv_c0, Nat.reducePow] at hte_lt; omega
      simp only [show ¬ (c.mv ≤ lit.toNat / 2 ∨ c.mv ≤ s.trail_end) by omega, ite_false] at hQ
      have hFin : ∀ ph' rsn' unfl' m', ph'.length = c.mv →
          (s.cur_level = 0 → rsn' = 0xFFFFFFFF#32 ∧ unfl' = s.unflushed + 1#64) →
          (s.cur_level ≠ 0 → rsn' = rsn ∧ unfl' = s.unflushed) →
          (PlainMem c (asgFin s lit rsn' unfl' ph') ⋆ R) m' → Q () m' := by
        intro ph' rsn' unfl' m' hph' hcl0 hclne hm'
        have hlen' : (asgFin s lit rsn' unfl' ph').LengthsOk c :=
          { hlen with
            vals_len := by simp [asgFin, hvl], lvl_len := by simp [asgFin, hll],
            rsns_len := by simp [asgFin, hrsl], trl_len := by simp [asgFin, htrl],
            trail_pos_len := by simp [asgFin, htpl], trail_end_le := by simp [asgFin]; omega,
            propagated_le := by simp [asgFin]; have := hlen.propagated_le; omega,
            heur_ok := { hh with phases_len := hph' } }
        by_cases hc0 : s.cur_level = 0
        · obtain ⟨rfl, rfl⟩ := hcl0 hc0
          simp only [show (s.cur_level = 0) = True from eq_true hc0, ↓reduceIte] at hQ
          exact hQ ph' m' hph' hlen' hm'
        · obtain ⟨rfl, rfl⟩ := hclne hc0
          simp only [show (s.cur_level = 0) = False from eq_false hc0, ↓reduceIte] at hQ
          exact hQ ph' m' hph' hlen' hm'
      clear hQ; pi_head_steps
      simp only [bv_c0_zext32_64, BitVec.toNat_xor, show BitVec.toNat (1 : BitVec 32) = 1 from rfl,
        show BitVec.setWidth 8 (-1 : BitVec 32) = 0xFF#8 by decide] at hm
      have hm0 : (PlainMem c (asgSt0 s lit) ⋆ R) _ := hm; clear hm
      refine wp_join_group (ts := [])
        (fun () m1 => ∃ ph' : List (BitVec 8), ph'.length = c.mv ∧
          (PlainMem c (asgSt1 s lit ph') ⋆ R) m1) ?_ ?_
      · rintro _ ⟨⟩ m1 ⟨ph', hph', hm1'⟩
        have hll1 : (asgSt1 s lit ph').lvl.length = c.mv := hll
        pi_head_steps
        simp only [bv_c0_zext32_64, bv32_lshr1, bv64_setWidth32_ofNat] at hm
        have hm2 : (PlainMem c (asgSt2 s lit ph') ⋆ R) _ := hm; clear hm
        have hrsl2 : (asgSt2 s lit ph').rsns.length = c.mv := hrsl
        refine wp_join_group (ts := [])
          (fun () m2 => ∃ (rsn' : BitVec 32) (unfl' : BitVec 64),
            (s.cur_level = 0 → rsn' = 0xFFFFFFFF#32 ∧ unfl' = s.unflushed + 1#64) ∧
            (s.cur_level ≠ 0 → rsn' = rsn ∧ unfl' = s.unflushed) ∧
            (PlainMem c (asgSt3 s lit rsn' unfl' ph') ⋆ R) m2) ?_ ?_
        · rintro _ ⟨⟩ m2 ⟨rsn', unfl', hcl0, hclne, hm2'⟩
          pi_unmdata; try c0_let_simp
          exact assign_tail_wp hmv hvar hte htpl htrl hte64 hte1_64 hm2'
            (fun m' hm' => hFin ph' rsn' unfl' m' hph' hcl0 hclne hm')
        · intro J2 hJ2
          have hcl_2 : (asgSt2 s lit ph').cur_level = s.cur_level := rfl
          pi_head_steps; refine wp_jnz_of (fun hc0 => ?_) (fun hcn => ?_)
          · rw [hcl_2] at hc0; dsimp only [Arg.val_var] at hc0; rw [beq_iff_eq] at hc0
            pi_head_steps
            have hs0 : s.cur_level = 0 := (bv_eq_zero_iff (by omega)).mp hc0
            simp only [bv_c0_zext32_64, bv32_lshr1] at hm
            have hm3 : (PlainMem c (asgSt3 s lit 0xFFFFFFFF#32 (s.unflushed + 1#64) ph') ⋆ R) _ :=
              hm
            exact hJ2 () _ ⟨0xFFFFFFFF#32, s.unflushed + 1#64, fun _ => ⟨rfl, rfl⟩,
              fun h => absurd hs0 h, hm3⟩
          · rw [hcl_2] at hcn; dsimp only [Arg.val_var] at hcn; rw [beq_eq_false_iff_ne] at hcn
            pi_head_steps
            have hsn : s.cur_level ≠ 0 := fun h => hcn (by simp [h])
            simp only [bv_c0_zext32_64, bv32_lshr1] at hm
            have hm3 : (PlainMem c (asgSt3 s lit rsn s.unflushed ph') ⋆ R) _ := hm
            exact hJ2 () _ ⟨rsn, s.unflushed, fun h => absurd h hsn, fun _ => ⟨rfl, rfl⟩, hm3⟩
      · intro J1 hJ1
        have hph1 : (asgSt0 s lit).heur.phases.length = c.mv := hphl
        pi_head_steps; refine wp_jnz_of (fun hpr0 => ?_) (fun hprn => ?_)
        · c0_steps
          · simp only [bv_c0_zext32_64, bv32_lshr1] at hm
            have hm_p : (PlainMem c (asgSt1 s lit _) ⋆ R) _ := hm
            exact hJ1 () _ ⟨_, by simp [List.length_set, hph1], hm_p⟩
          · simp only [bv_c0_zext32_64, bv32_lshr1] at hm
            have hm_p : (PlainMem c (asgSt1 s lit _) ⋆ R) _ := hm
            exact hJ1 () _ ⟨_, by simp [List.length_set, hph1], hm_p⟩
        · pi_head_steps
          have hm_p : (PlainMem c (asgSt1 s lit s.heur.phases) ⋆ R) _ := hm0
          exact hJ1 () _ ⟨s.heur.phases, hphl, hm_p⟩

/-! ## 2. `plain_backtrack` -/

private structure BtPrefixInv (c : PlainCfg) (F0 : CNF Nat) (s : PlainState)
    (target_lvl te : Nat) (st : PlainState) : Prop where
  te_le : te ≤ s.trail_end
  agree : st = { s with vals := st.vals, lvl := st.lvl, rsns := st.rsns, heur := st.heur }
  len_ok : st.LengthsOk c
  vals_dom : ∀ l < 2 * c.mv, st.vals[l]?.getD 0#8 = 0#8 ∨
    st.vals[l]?.getD 0#8 = 1#8 ∨ st.vals[l]?.getD 0#8 = 0xFF#8
  vals_true : ∀ l < 2 * c.mv,
    st.vals[l]?.getD 0#8 = 1#8 ↔ ∃ i < te, (s.trl[i]?.getD 0#32).toNat = l
  vals_false : ∀ l < 2 * c.mv,
    st.vals[l]?.getD 0#8 = 0xFF#8 ↔ ∃ i < te, (s.trl[i]?.getD 0#32).toNat = l ^^^ 1
  lvl_eq : ∀ i < te,
    st.lvl[(s.trl[i]?.getD 0#32).toNat / 2]? = s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?
  rsns_eq : ∀ i < te,
    st.rsns[(s.trl[i]?.getD 0#32).toNat / 2]? = s.rsns[(s.trl[i]?.getD 0#32).toNat / 2]?
  popped_gt : ∀ i, te ≤ i → i < s.trail_end →
    target_lvl < (s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat

private theorem btPrefixInv_step {c : PlainCfg} {F0 : CNF Nat} {s st : PlainState}
    {target_lvl te : Nat} (hcore : PlainCoreInv c F0 s)
    (hbt : BtPrefixInv c F0 s target_lvl te st) (hte : 0 < te)
    (_hlvl_gt : target_lvl < (st.lvl[(s.trl[te - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat)
    {heur' : PlainHeur} (hhok : heur'.LengthsOk c) :
    let lit := s.trl[te - 1]?.getD 0#32
    BtPrefixInv c F0 s target_lvl (te - 1)
      { st with
        vals := (st.vals.set lit.toNat 0#8).set (lit.toNat ^^^ 1) 0#8,
        lvl := st.lvl.set (lit.toNat / 2) 0#32,
        rsns := st.rsns.set (lit.toNat / 2) 0xFFFFFFFF#32, heur := heur' } := by
  intro lit; have hte_le := hbt.te_le; have hlen := hbt.len_ok
  have hlt1 : lit.toNat < 2 * c.mv := hcore.trail_lits_lt (te - 1) (by omega)
  have hlt2 : lit.toNat ^^^ 1 < 2 * c.mv := litNeg_lt_two_mul hlt1
  have hnovar : ∀ i < te - 1, (s.trl[i]?.getD 0#32).toNat / 2 ≠ lit.toNat / 2 := fun i hi hv =>
    by have := hcore.trail_vars_nodup i (te - 1) (by omega) (by omega) hv; omega
  have hvals_ne : ∀ i < te - 1, (s.trl[i]?.getD 0#32).toNat ≠ lit.toNat ∧
      (s.trl[i]?.getD 0#32).toNat ≠ lit.toNat ^^^ 1 ∧
      ((s.trl[i]?.getD 0#32).toNat ^^^ 1) ≠ lit.toNat ∧
      ((s.trl[i]?.getD 0#32).toNat ^^^ 1) ≠ lit.toNat ^^^ 1 := fun i hi => by
    have hnv := hnovar i hi; have hx := litVar_litNeg (s.trl[i]?.getD 0#32).toNat
    have hy := litVar_litNeg lit.toNat; unfold litVar litNeg at hx hy; omega
  let st' : PlainState := { st with
    vals := (st.vals.set lit.toNat 0#8).set (lit.toNat ^^^ 1) 0#8,
    lvl := st.lvl.set (lit.toNat / 2) 0#32, rsns := st.rsns.set (lit.toNat / 2) 0xFFFFFFFF#32,
    heur := heur' }
  have hget_vals : ∀ l < 2 * c.mv, st'.vals[l]?.getD 0#8 =
      if l = lit.toNat ∨ l = lit.toNat ^^^ 1 then 0#8 else st.vals[l]?.getD 0#8 := fun l _ => by
    by_cases h2 : l = lit.toNat ^^^ 1
    · subst h2; dsimp [st']
      rw [List.getElem?_set_self (by rw [List.length_set, hlen.vals_len]; exact hlt2)]; simp
    · by_cases h1 : l = lit.toNat
      · subst h1; simp [st', h2, List.getElem?_set_ne (Ne.symm h2),
          List.getElem?_set_self (by rw [hlen.vals_len]; exact hlt1)]
      · simp [st', h1, h2, List.getElem?_set_ne (Ne.symm h2), List.getElem?_set_ne (Ne.symm h1)]
  refine ⟨by omega, congrArg (fun x : PlainState =>
      { x with vals := st'.vals, lvl := st'.lvl, rsns := st'.rsns, heur := heur' }) hbt.agree,
    { hlen with
      vals_len := by simp [hlen.vals_len], lvl_len := by simp [hlen.lvl_len],
      rsns_len := by simp [hlen.rsns_len], heur_ok := hhok }, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l hl; rw [hget_vals l hl]; split
    · exact Or.inl rfl
    · exact hbt.vals_dom l hl
  · intro l hl; rw [hget_vals l hl]; split
    · next heq => refine ⟨fun h => by simp at h, fun ⟨i, hi, hie⟩ => False.elim <| by
        rcases heq with rfl | rfl <;>
          first | exact (hvals_ne i hi).1 hie | exact (hvals_ne i hi).2.1 hie⟩
    · next hne =>
      rw [hbt.vals_true l hl]; refine ⟨fun ⟨i, hi, hie⟩ =>
        ⟨i, Nat.lt_of_not_ge fun h => hne (Or.inl ?_), hie⟩, fun ⟨i, hi, hie⟩ => ⟨i, by omega, hie⟩⟩
      rw [show i = te - 1 from by omega] at hie; exact hie.symm
  · intro l hl; rw [hget_vals l hl]; split
    · next heq => refine ⟨fun h => by simp at h, fun ⟨i, hi, hie⟩ => False.elim <| by
        have hx : ((s.trl[i]?.getD 0#32).toNat ^^^ 1) = l := by rw [hie]; exact litNeg_litNeg l
        rcases heq with rfl | rfl <;>
          first | exact (hvals_ne i hi).2.2.1 hx | exact (hvals_ne i hi).2.2.2 hx⟩
    · next hne =>
      rw [hbt.vals_false l hl]; refine ⟨fun ⟨i, hi, hie⟩ =>
        ⟨i, Nat.lt_of_not_ge fun h => hne (Or.inr ?_), hie⟩, fun ⟨i, hi, hie⟩ => ⟨i, by omega, hie⟩⟩
      rw [show i = te - 1 from by omega] at hie
      exact (litNeg_litNeg l).symm.trans (congrArg (· ^^^ 1) hie.symm)
  · intro i hi; dsimp [st']; rw [List.getElem?_set_ne (hnovar i hi).symm]
    exact hbt.lvl_eq i (by omega)
  · intro i hi; dsimp [st']; rw [List.getElem?_set_ne (hnovar i hi).symm]
    exact hbt.rsns_eq i (by omega)
  · intro i hi1 hi2; by_cases hie : i = te - 1
    · subst hie; have heq := hbt.lvl_eq (te - 1) (by omega); rwa [← congrArg (·.getD 0#32) heq]
    · exact hbt.popped_gt i (by omega) hi2

private theorem bt_cur_level_le {c : PlainCfg} {F0 : CNF Nat} {s s' : PlainState}
    {target_lvl te : Nat} (hcore : PlainCoreInv c F0 s) (hte_le : te ≤ s.trail_end)
    (hlvl_s' : ∀ i < te, s'.lvl[(s'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 =
      s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32)
    (hinhab : ∀ L, 1 ≤ L → L ≤ target_lvl →
      ∃ i < te, (s'.lvl[(s'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = L) :
    target_lvl ≤ te := by
  rcases Nat.eq_zero_or_pos target_lvl with rfl | hpos
  · exact Nat.zero_le _
  · have hchain : ∀ L, 1 ≤ L → L ≤ target_lvl →
        ∃ i < te, (s'.lvl[(s'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = L ∧
          L - 1 ≤ i := by
      intro L h1 h2; induction L with
      | zero => omega
      | succ k ih =>
        obtain ⟨i, hi, hie⟩ := hinhab (k + 1) (by omega) h2
        rcases Nat.eq_zero_or_pos k with rfl | hk
        · exact ⟨i, hi, hie, Nat.zero_le _⟩
        · obtain ⟨j, hj, hje, hjk⟩ := ih hk (by omega)
          have hij : j < i := Nat.lt_of_not_ge fun hle => by
            have hm := hcore.trail_mono i j hle (Nat.lt_of_lt_of_le hj hte_le)
            rw [hlvl_s' i hi] at hie; rw [hlvl_s' j hj] at hje; omega
          exact ⟨i, hi, hie, by omega⟩
    obtain ⟨i, hi, _, hle⟩ := hchain target_lvl hpos (Nat.le_refl _); omega

private abbrev BtPost (c : PlainCfg) (s : PlainState) (target_lvl : BitVec 64)
    (R : Mem 64 → Prop) (Q : Post []) : Prop :=
  ∀ vals' lvl' rsns' te' prop' heur' m',
    let s' : PlainState := { s with
      vals := vals', lvl := lvl', rsns := rsns', trail_end := te',
      propagated := prop', cur_level := target_lvl.toNat, heur := heur' }
    s'.LengthsOk c → te' ≤ s.trail_end → prop' ≤ te' →
    heur'.rel_trigger = s.heur.rel_trigger →
    (∀ i < te', (s.trl[i]?.getD 0#32).toNat < 2 * c.mv) →
    (∀ F0, PlainCoreInv c F0 s → target_lvl.toNat ≤ s.cur_level →
      PlainCoreInv c F0 s' ∧ ∀ i < s.trail_end,
        ((s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat ↔
          i < te')) →
    (PlainMem c s' ⋆ R) m' → Q () m'

private theorem backtrack_exit {c : PlainCfg} {s st : PlainState} {target_lvl : BitVec 64}
    {te prop' : Nat} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []}
    (hs_tel : s.trail_end ≤ c.mv) (hlen : st.LengthsOk c) (hte_le : te ≤ s.trail_end)
    (hagree : st = { s with vals := st.vals, lvl := st.lvl, rsns := st.rsns, heur := st.heur })
    (hprop : prop' = min s.propagated te) (hrt : st.heur.rel_trigger = s.heur.rel_trigger)
    (htrl_lt : ∀ i < te, (s.trl[i]?.getD 0#32).toNat < 2 * c.mv)
    (hexit : ∀ F0, PlainCoreInv c F0 s → target_lvl.toNat ≤ s.cur_level →
      BtPrefixInv c F0 s target_lvl.toNat te st ∧
      (te = 0 ∨
        (st.lvl[(s.trl[te - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat))
    (hm : (PlainMem c { st with
      trail_end := te, propagated := prop', cur_level := target_lvl.toNat } ⋆ R) m)
    (hQ : BtPost c s target_lvl R Q) : Q () m := by
  subst hprop
  let s' : PlainState := { s with
    vals := st.vals, lvl := st.lvl, rsns := st.rsns, trail_end := te,
    propagated := min s.propagated te, cur_level := target_lvl.toNat, heur := st.heur }
  have hlen' : s'.LengthsOk c :=
    { hlen with
      vals_len := hlen.vals_len, mrk_len := by dsimp [s']; rw [hagree] at hlen; exact hlen.mrk_len
      lvl_len := hlen.lvl_len, rsns_len := hlen.rsns_len,
      trl_len := by dsimp [s']; rw [hagree] at hlen; exact hlen.trl_len
      trail_pos_len := by dsimp [s']; rw [hagree] at hlen; exact hlen.trail_pos_len
      tmp_len_arr := by dsimp [s']; rw [hagree] at hlen; exact hlen.tmp_len_arr
      wvec_len := by dsimp [s']; rw [hagree] at hlen; exact hlen.wvec_len
      arena_len_arr := by dsimp [s']; rw [hagree] at hlen; exact hlen.arena_len_arr
      wstk_len_arr := by dsimp [s']; rw [hagree] at hlen; exact hlen.wstk_len_arr
      min_stk_len := by dsimp [s']; rw [hagree] at hlen; exact hlen.min_stk_len
      min_clr_len_arr := by dsimp [s']; rw [hagree] at hlen; exact hlen.min_clr_len_arr
      arena_len_le := by dsimp [s']; rw [hagree] at hlen; exact hlen.arena_len_le
      wlen_le := by dsimp [s']; rw [hagree] at hlen; exact hlen.wlen_le
      trail_end_le := Nat.le_trans hte_le hs_tel, propagated_le := Nat.min_le_right _ _
      tmp_len_le := by dsimp [s']; rw [hagree] at hlen; exact hlen.tmp_len_le
      min_clr_len_le := by dsimp [s']; rw [hagree] at hlen; exact hlen.min_clr_len_le
      heur_ok := hlen.heur_ok }
  have hmeq : { st with
      trail_end := te, propagated := min s.propagated te, cur_level := target_lvl.toNat } = s' :=
    congrArg (fun x => { x with
      trail_end := te, propagated := min s.propagated te, cur_level := target_lvl.toNat }) hagree
  rw [hmeq] at hm
  refine hQ st.vals st.lvl st.rsns te (min s.propagated te) st.heur m hlen' hte_le
    (Nat.min_le_right _ _) hrt htrl_lt (fun F0 hcore htl_cur => ?_) hm
  obtain ⟨hbt, hex⟩ := hexit F0 hcore htl_cur
  have hkeep : ∀ i < s.trail_end,
      (s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat → i < te :=
    fun i hi _ => Nat.lt_of_not_ge fun hge => by have := hbt.popped_gt i hge hi; omega
  have hlvl_s' : ∀ i < te, s'.lvl[(s'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 =
      s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32 :=
    fun i hi => congrArg (·.getD 0#32) (hbt.lvl_eq i hi)
  have hrsns_s' : ∀ i < te, s'.rsns[(s'.trl[i]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 =
      s.rsns[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 :=
    fun i hi => congrArg (·.getD 0xFFFFFFFF#32) (hbt.rsns_eq i hi)
  have hinhab : ∀ L, 1 ≤ L → L ≤ target_lvl.toNat →
      ∃ i < te, (s'.lvl[(s'.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = L := fun L h1 h2 =>
    let ⟨i, hi, hie⟩ := hcore.levels_inhabited L h1 (Nat.le_trans h2 htl_cur)
    have hi' := hkeep i hi (by omega); ⟨i, hi', by rw [hlvl_s' i hi']; exact hie⟩
  have hiff : ∀ i < s.trail_end,
      ((s.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤ target_lvl.toNat ↔
        i < te) := fun i hi =>
    ⟨hkeep i hi, fun hlt => by
      rcases hex with rfl | hex_le
      · cases hlt
      · have hm := hcore.trail_mono i (te - 1) (Nat.le_sub_one_of_lt hlt) (by omega)
        have heq := congrArg (·.getD 0#32) (hbt.lvl_eq (te - 1) (by omega))
        rw [heq] at hex_le; exact by omega⟩
  have har_s' : ArenaClausesInv c F0 s' :=
    ⟨hcore.arena.len_ok, hcore.arena.refs_wf, hcore.arena.no_shrk, hcore.arena.lits_lt,
      hcore.arena.entails⟩
  have hw_s' : WatchesInv c F0 s' := hcore.watches.with_wstk rfl rfl rfl rfl
  have harl_eq : ∀ r, arenaClauseLits s' r = arenaClauseLits s r := fun _ => rfl
  refine ⟨⟨hlen', har_s', hw_s', bt_cur_level_le hcore hte_le hlvl_s' hinhab,
    (fun i hi => hcore.trail_lits_lt i (Nat.lt_of_lt_of_le hi hte_le)),
    (fun i j hi hj => hcore.trail_vars_nodup i j
      (Nat.lt_of_lt_of_le hi hte_le) (Nat.lt_of_lt_of_le hj hte_le)),
    hbt.vals_dom, hbt.vals_true, hbt.vals_false,
    (fun i hi => by dsimp only [s'] at hi ⊢; rw [hlvl_s' i hi]
                    exact (hiff i (Nat.lt_of_lt_of_le hi hte_le)).mpr hi),
    (fun i j hij hj => by dsimp only [s'] at hj ⊢
                          rw [hlvl_s' i (Nat.lt_of_le_of_lt hij hj), hlvl_s' j hj]
                          exact hcore.trail_mono i j hij (Nat.lt_of_lt_of_le hj hte_le)),
    hinhab, (fun i hi hl0 => by dsimp only [s'] at hi hl0; rw [hlvl_s' i hi] at hl0
                                exact hcore.level0_sound i (Nat.lt_of_lt_of_le hi hte_le) hl0),
    (fun i hi => hcore.trail_pos_inv i (Nat.lt_of_lt_of_le hi hte_le)),
    (fun idx hidx hl0 => by dsimp only [s'] at hidx hl0 ⊢
                            rw [hlvl_s' idx hidx] at hl0; rw [hrsns_s' idx hidx]
                            exact hcore.level0_rsn_none idx (Nat.lt_of_lt_of_le hidx hte_le) hl0),
    (fun idx hidx hne => by dsimp only [s'] at hidx; rw [hrsns_s' idx hidx] at hne ⊢
                            exact hcore.reason_inv idx (Nat.lt_of_lt_of_le hidx hte_le) hne),
    (fun idx hidx hne hlg => by dsimp only [s'] at hidx; rw [hrsns_s' idx hidx] at hne hlg ⊢
                                rw [harl_eq]
                                exact hcore.reason_lit_mem idx (Nat.lt_of_lt_of_le hidx hte_le) hne
                                  hlg)⟩, hiff⟩

private theorem bt_lvl_at {c : PlainCfg} {s st : PlainState} (hlvl_len : st.lvl.length = c.mv)
    (htrl_s : st.trl = s.trl) {i : Nat} (hi_lt : (s.trl[i]?.getD 0#32).toNat < 2 * c.mv)
    (hlt_s : i < st.trl.length) :
    ∃ hlt_v : (st.trl[i]'hlt_s).toNat / 2 < st.lvl.length,
      (st.lvl[(s.trl[i]?.getD 0#32).toNat / 2]?.getD 0#32).toNat =
        (st.lvl[(st.trl[i]'hlt_s).toNat / 2]'hlt_v).toNat := by
  have hg : s.trl[i]?.getD 0#32 = st.trl[i]'hlt_s := by
    rw [List.getElem?_eq_getElem (by rwa [← htrl_s]), Option.getD_some]; simp only [htrl_s]
  have hv : (st.trl[i]'hlt_s).toNat / 2 < st.lvl.length := by rw [hlvl_len, ← hg]; omega
  exact ⟨hv, by rw [hg, List.getElem?_eq_getElem hv, Option.getD_some]⟩

private theorem backtrack_pop_step_wp {Γ : Env} {Q : Post []} {X : XPost} {c : PlainCfg}
    {st1 : PlainState} {te_v : BitVec 64} {v32 : BitVec 32} {rel0 : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64} {L : Cont [i64]}
    (hHeapPush : ∀ a m Q X, plainHeapPushSpec a m Q X →
      Γ "plain_heap_push" [i64, i32] [] a m Q X)
    (hst1_len : st1.LengthsOk c) (hrel : st1.heur.rel_trigger = rel0)
    (hv32_qs : (BitVec.setWidth 64 v32).toNat < st1.heur.q_stamp.length)
    (hm1 : (PlainMem c st1 ⋆ R) m)
    (hstep_b : ∀ (hr' : PlainHeur) (m' : Mem 64), hr'.LengthsOk c → hr'.rel_trigger = rel0 →
      (PlainMem c { st1 with heur := hr' } ⋆ R) m' → L (te_v - 1#64, ()) m') :
    wp Γ Q X
      (Expr.group (sig := [[]])
        (fun _ => Blocks.cons (fun _ =>
          Expr.let_
            { sig := [i64, i64], code := OpCode.sub i64,
              args := (Arg.var te_v, Arg.imm 1, ()) } fun p =>
            Expr.jump L (Arg.var p.fst, ())) Blocks.nil)
        fun Js =>
          Expr.let_
            { sig := [i64, i64], code := OpCode.add i64,
              args := (Arg.var c.hdr, Arg.imm 552, ()) } fun p =>
            Expr.load i64 (Arg.var p.fst) fun ld =>
              Expr.let_
                { sig := [i64, i64], code := OpCode.cmp CmpOp.ne i64 Ty.bool,
                  args := (Arg.var ld, Arg.imm 0, ()) } fun p =>
                Expr.jnz (Arg.var p.fst)
                  (Expr.call "plain_heap_push" (as := [i64, i32]) (bs := [])
                    (Arg.var c.hdr, Arg.var v32, ()) fun _ => Expr.jump Js.fst ())
                  (Expr.group (sig := [[]])
                    (fun _ => Blocks.cons (fun _ => Expr.jump Js.fst ()) Blocks.nil)
                    fun Js_1 =>
                      Expr.let_
                        { sig := [i32], code := OpCode.zext 32 64,
                          args := (Arg.var v32, ()) } fun p =>
                        Expr.let_
                          { sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64 Ty.bool,
                            args := (Arg.var p.fst, Arg.var (BitVec.ofNat 64 c.mv), ()) } fun p =>
                          Expr.jnz (Arg.var p.fst)
                            (Expr.let_
                              { sig := [i32], code := OpCode.zext 32 64,
                                args := (Arg.var v32, ()) } fun p =>
                              Expr.let_
                                { sig := [i64, i64], code := OpCode.mul i64,
                                  args := (Arg.var p.fst, Arg.imm 4, ()) } fun p =>
                                Expr.let_
                                  { sig := [i64, i64], code := OpCode.add i64,
                                    args := (Arg.var c.pQStamp, Arg.var p.fst, ()) } fun p =>
                                  Expr.load i32 (Arg.var p.fst) fun ld =>
                                    Expr.let_
                                      { sig := [i32], code := OpCode.zext 32 64,
                                        args := (Arg.var ld, ()) } fun p =>
                                      Expr.let_
                                        { sig := [i64, i64], code := OpCode.add i64,
                                          args := (Arg.var c.hdr, Arg.imm 632, ()) } fun p_1 =>
                                        Expr.load i64 (Arg.var p_1.fst) fun ld =>
                                          Expr.let_
                                            { sig := [i64, i64],
                                              code := OpCode.cmp CmpOp.ugt i64 Ty.bool,
                                              args := (Arg.var p.fst, Arg.var ld, ()) } fun p =>
                                            Expr.jnz (Arg.var p.fst)
                                              (Expr.let_
                                                { sig := [i32], code := OpCode.zext 32 64,
                                                  args := (Arg.var v32, ()) } fun p =>
                                                Expr.let_
                                                  { sig := [i64, i64], code := OpCode.add i64,
                                                    args := (Arg.var c.hdr, Arg.imm 624, ()) }
                                                  fun p_2 =>
                                                  Expr.store (Arg.var p.fst) (Arg.var p_2.fst)
                                                    (Expr.let_
                                                      { sig := [i32], code := OpCode.zext 32 64,
                                                        args := (Arg.var v32, ()) } fun p =>
                                                      Expr.let_
                                                        { sig := [i64, i64], code := OpCode.mul i64,
                                                          args := (Arg.var p.fst, Arg.imm 4, ()) }
                                                        fun p =>
                                                        Expr.let_
                                                          { sig := [i64, i64],
                                                            code := OpCode.add i64,
                                                            args := (Arg.var c.pQStamp,
                                                              Arg.var p.fst, ()) } fun p =>
                                                          Expr.load i32 (Arg.var p.fst) fun ld =>
                                                            Expr.let_
                                                              { sig := [i32],
                                                                code := OpCode.zext 32 64,
                                                                args := (Arg.var ld, ()) } fun p =>
                                                              Expr.let_
                                                                { sig := [i64, i64],
                                                                  code := OpCode.add i64,
                                                                  args := (Arg.var c.hdr,
                                                                    Arg.imm 632, ()) } fun p_3 =>
                                                                Expr.store (Arg.var p.fst)
                                                                  (Arg.var p_3.fst)
                                                                  (Expr.jump Js_1.fst ())))
                                              (Expr.jump Js_1.fst ()))
                            (Expr.jump Js_1.fst ()))) m := by
  refine wp_join_group (ts := []) (fun () m' => L (te_v - 1#64, ()) m') ?_ ?_
  · rintro _ ⟨⟩ m' hm'; pi_shallow_steps; exact hm'
  · intro Jn hJn; pi_shallow_steps
    refine wp_jnz_of (fun _ => ?_) (fun _ => ?_)
    · pi_shallow_steps; c0_call hHeapPush
      refine ⟨c, st1, R, rfl, hst1_len, hm1, fun heur' m' hhok' hrt' hm' => ?_⟩
      pi_shallow_steps; exact hJn () m' (hstep_b heur' m' hhok' (hrt'.trans hrel) hm')
    · pi_shallow_steps
      refine wp_join_group (ts := []) (fun () m' => L (te_v - 1#64, ()) m')
        (fun _ _ m' h => by pi_shallow_steps; exact hJn () m' h) ?_
      · intro Jn2 hJn2; pi_shallow_steps
        refine wp_jnz_of (fun _ => ?_) (fun _ => ?_)
        · pi_shallow_lets
          refine wp_load_of (c0_load_arena_q_stamp_arr hv32_qs hm1) ?_
          pi_shallow_steps; refine wp_jnz_of (fun _ => ?_) (fun _ => ?_)
          · let st_m1 : PlainState :=
              { st1 with heur := { st1.heur with q_search_idx := BitVec.setWidth 64 v32 } }
            let hr_f : PlainHeur := { st1.heur with
              q_search_idx := BitVec.setWidth 64 v32,
              q_search_stamp := BitVec.setWidth 64
                (st1.heur.q_stamp[(BitVec.setWidth 64 v32).toNat]'hv32_qs) }
            have hst_eq : { st_m1 with heur := { st_m1.heur with
                q_search_stamp := BitVec.setWidth 64
                  (st_m1.heur.q_stamp[(BitVec.setWidth 64 v32).toNat]'hv32_qs) } } =
                { st1 with heur := hr_f } := rfl
            pi_shallow_lets
            refine wp_store_sep (P := PlainMem c st_m1)
              (store_arena_q_search_idx (BitVec.setWidth 64 v32) hm1) ?_
            intro m2 hm2; pi_shallow_lets
            refine wp_load_of (c0_load_arena_q_stamp_arr (s := st_m1) hv32_qs hm2) ?_
            pi_shallow_lets
            have hs2 := store_arena_q_search_stamp (BitVec.setWidth 64
              (st_m1.heur.q_stamp[(BitVec.setWidth 64 v32).toNat]'hv32_qs)) hm2
            rw [hst_eq] at hs2
            refine wp_store_sep hs2 ?_
            intro m3 hm3; pi_shallow_steps
            exact hJn2 () m3 (hstep_b hr_f m3
              { hst1_len.heur_ok with phases_len := hst1_len.heur_ok.phases_len } hrel hm3)
          · pi_shallow_steps
            exact hJn2 () _ (hstep_b st1.heur _ hst1_len.heur_ok hrel hm1)
        · pi_shallow_steps
          exact hJn2 () _ (hstep_b st1.heur _ hst1_len.heur_ok hrel hm1)

theorem plain_backtrack_wp (Γ : Env)
    (hHeapPush : ∀ a m Q X, plainHeapPushSpec a m Q X →
      Γ "plain_heap_push" [i64, i32] [] a m Q X) :
    ∀ a m Q X, plainBacktrackSpec a m Q X → Func.wp Γ plain_backtrack_body a m Q X := by
  rintro ⟨h, target_lvl, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, htrl_lt, hm, hQ⟩
  have hmv := c.hmv; unfold dimacsBound at hmv; have hs_tel := hlen.trail_end_le
  pi_head_steps
  refine wp_join_group (ts := []) (fun () m0 => ∃ heur0 : PlainHeur, heur0.LengthsOk c ∧
      heur0.rel_trigger = s.heur.rel_trigger ∧ (PlainMem c { s with heur := heur0 } ⋆ R) m0) ?_ ?_
  · rintro _ ⟨⟩ m0 ⟨heur0, hhok0, hrt0, hm0⟩; pi_head_steps
    refine wp_join_group (ts := [i64]) (fun (te_v, ()) ml => ∃ st : PlainState,
        te_v.toNat ≤ s.trail_end ∧ st.LengthsOk c ∧
        st = { s with vals := st.vals, lvl := st.lvl, rsns := st.rsns, heur := st.heur } ∧
        st.heur.rel_trigger = s.heur.rel_trigger ∧
        (∀ F0, PlainCoreInv c F0 s → target_lvl.toNat ≤ s.cur_level →
          BtPrefixInv c F0 s target_lvl.toNat te_v.toNat st ∧
          (te_v.toNat = 0 ∨
            (st.lvl[(s.trl[te_v.toNat - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
              target_lvl.toNat)) ∧
        (PlainMem c st ⋆ R) ml) ?_ ?_
    · rintro _ ⟨te_v, ⟨⟩⟩ ml ⟨st, hte_le, hst_len, hag, hrt, hexit, hml⟩
      have hs_pr : st.propagated = s.propagated := by rw [hag]
      have hpr64 : st.propagated < 2 ^ 64 := by
        have := hst_len.propagated_le; have := hst_len.trail_end_le; omega
      have hte64 : te_v.toNat < 2 ^ 64 := by omega
      pi_shallow_steps
      refine wp_join_group (ts := []) (fun () m' => ∃ prop',
          prop' = min s.propagated te_v.toNat ∧
          (PlainMem c { st with trail_end := te_v.toNat, propagated := prop' } ⋆ R) m') ?_ ?_
      · rintro _ ⟨⟩ m' ⟨prop', rfl, hm'⟩
        pi_shallow_steps
        exact backtrack_exit (te := te_v.toNat) hs_tel hst_len hte_le hag rfl hrt
          (fun i hi => htrl_lt i (by omega)) hexit hm hQ
      · intro Jp hJp; pi_shallow_steps
        refine wp_jnz_of (fun hgt => ?_) (fun hle => ?_)
        · have hte_lt_pr : te_v.toNat ≤ s.propagated := by
            clear hm hQ; rw [← hs_pr]; simp only [Arg.val_var, bv_c0] at hgt; omega
          pi_shallow_steps
          exact hJp () _ ⟨te_v.toNat, (Nat.min_eq_right hte_lt_pr).symm, hm⟩
        · have hpr_le : s.propagated ≤ te_v.toNat := by
            clear hm hQ; rw [← hs_pr]; simp only [Arg.val_var, bv_c0] at hle; omega
          pi_shallow_steps
          exact hJp () _ ⟨s.propagated, (Nat.min_eq_left hpr_le).symm, by simpa [hs_pr] using hm⟩
    · intro B hB; pi_head_steps
      refine wp_loop_inv (fun (te_v : Tup Val [i64]) ml => ∃ st : PlainState,
          te_v.1.toNat ≤ s.trail_end ∧ st.LengthsOk c ∧
          st = { s with vals := st.vals, lvl := st.lvl, rsns := st.rsns, heur := st.heur } ∧
          st.heur.rel_trigger = s.heur.rel_trigger ∧
          (∀ F0, PlainCoreInv c F0 s → target_lvl.toNat ≤ s.cur_level →
            BtPrefixInv c F0 s target_lvl.toNat te_v.1.toNat st) ∧
          (PlainMem c st ⋆ R) ml) (fun te_v _ => te_v.1.toNat) ?_ ?_
      · intro L hL; pi_shallow_steps
        refine hL (BitVec.ofNat 64 s.trail_end, ()) m0 ⟨{ s with heur := heur0 }, ?_, ?_, rfl,
          hrt0, fun F0 hcore _ => ?_, hm0⟩
        · dsimp only; rw [bv64_ofNat_toNat (by omega)]; exact Nat.le_refl _
        · exact { hlen with heur_ok := hhok0 }
        · dsimp only; rw [bv64_ofNat_toNat (by omega)]
          exact ⟨Nat.le_refl _, rfl, { hlen with heur_ok := hhok0 }, hcore.vals_domain,
            hcore.vals_true_iff, hcore.vals_false_iff, fun _ _ => rfl, fun _ _ => rfl,
            fun _ h1 h2 => by omega⟩
      · intro L ⟨te_v, ⟨⟩⟩ ml ⟨st, hte_le, hst_len, hag, hrt, hbt_fn, hml⟩ hL
        dsimp only at hte_le hbt_fn hL
        have hte_mv : te_v.toNat ≤ c.mv := Nat.le_trans hte_le hs_tel
        have htrl_s : st.trl = s.trl := by rw [hag]
        have hte64 : te_v.toNat < 2 ^ 64 := by omega
        pi_shallow_steps
        refine wp_jnz_of (fun hc => ?_) (fun hnz => ?_)
        · have hp : 0 < te_v.toNat := by
            clear hml hQ; simp only [Arg.val_var, bv_c0] at hc; omega
          have hsub : (te_v - 1#64).toNat = te_v.toNat - 1 :=
            bv64_sub1_toNat fun h0 => by have := congrArg BitVec.toNat h0; simp at this; omega
          have ht_lt : (te_v - 1#64).toNat < st.trl.length := by
            rw [htrl_s, hlen.trl_len, hsub]; omega
          have hlit_get : st.trl[(te_v - 1#64).toNat]'ht_lt =
              s.trl[te_v.toNat - 1]?.getD 0#32 := by
            rw [List.getElem?_eq_getElem (by rw [hlen.trl_len]; omega), Option.getD_some]
            simp only [htrl_s, hsub]
          have hlit_lt_nat : (st.trl[(te_v - 1#64).toNat]'ht_lt).toNat < 2 * c.mv := by
            rw [hlit_get]; exact htrl_lt (te_v.toNat - 1) (by omega)
          have ⟨hv_lt, hlvl_eq⟩ := bt_lvl_at hst_len.lvl_len htrl_s
            (htrl_lt (te_v.toNat - 1) (by omega)) (hsub ▸ ht_lt)
          have h1 : (BitVec.setWidth 64 (st.trl[(te_v - 1#64).toNat]'ht_lt)).toNat <
              st.vals.length := by rw [hst_len.vals_len, bv_c0_zext32_64]; exact hlit_lt_nat
          have h2 : (BitVec.setWidth 64 (st.trl[(te_v - 1#64).toNat]'ht_lt ^^^ 1#32)).toNat <
              st.vals.length := by
            rw [hst_len.vals_len, bv_c0_zext32_64, BitVec.toNat_xor,
              show (1#32 : BitVec 32).toNat = 1 from rfl]; exact litNeg_lt_two_mul hlit_lt_nat
          have h3 : (BitVec.setWidth 64 (st.trl[(te_v - 1#64).toNat]'ht_lt >>> 1)).toNat <
              st.lvl.length := by rw [hst_len.lvl_len, bv_c0_zext32_64, bv32_lshr_1]; omega
          have h4 : (BitVec.setWidth 64 (st.trl[(te_v - 1#64).toNat]'ht_lt >>> 1)).toNat <
              st.rsns.length := by rw [hst_len.rsns_len, ← hst_len.lvl_len]; exact h3
          pi_shallow_steps
          refine wp_jnz_of (fun hle => ?_) (fun hgt => ?_)
          · have hle' : (st.lvl[(s.trl[te_v.toNat - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat ≤
                target_lvl.toNat := by
              rw [hlvl_eq]; clear hml hQ
              simp only [Arg.val_var, bv_c0, Nat.reducePow] at hle
              simp only [show (18446744073709551616 - 1 + te_v.toNat) % 18446744073709551616 =
                te_v.toNat - 1 by omega] at hle
              exact hle
            pi_shallow_steps
            exact hB (te_v, ()) ml ⟨st, hte_le, hst_len, hag, hrt,
              fun F0 hcore htl => ⟨hbt_fn F0 hcore htl, Or.inr hle'⟩, hml⟩
          · have hgt' : target_lvl.toNat <
                (st.lvl[(s.trl[te_v.toNat - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := by
              rw [hlvl_eq]; clear hml hQ
              simp only [Arg.val_var, bv_c0, Nat.reducePow] at hgt
              simp only [show (18446744073709551616 - 1 + te_v.toNat) % 18446744073709551616 =
                te_v.toNat - 1 by omega] at hgt
              exact Nat.lt_of_not_le hgt
            let lit := s.trl[te_v.toNat - 1]?.getD 0#32
            let st1 : PlainState := { st with
              vals := (st.vals.set lit.toNat 0#8).set (lit.toNat ^^^ 1) 0#8,
              lvl := st.lvl.set (lit.toNat / 2) 0#32,
              rsns := st.rsns.set (lit.toNat / 2) 0xFFFFFFFF#32 }
            have hst1_len : st1.LengthsOk c :=
              { hst_len with
                vals_len := by simp [st1, hst_len.vals_len],
                lvl_len := by simp [st1, hst_len.lvl_len],
                rsns_len := by simp [st1, hst_len.rsns_len] }
            have hlit_eq : st.trl[(te_v - 1).toNat]'ht_lt = lit := hlit_get
            have hstep_b : ∀ (hr' : PlainHeur) (m' : Mem 64), hr'.LengthsOk c →
                hr'.rel_trigger = st.heur.rel_trigger →
                (PlainMem c { st1 with heur := hr' } ⋆ R) m' → L (te_v - 1#64, ()) m' :=
              fun hr' m' hhok' hrt' hm' =>
              hL (te_v - 1#64, ()) m' (by dsimp only; rw [hsub]; omega)
                ⟨{ st1 with heur := hr' }, by dsimp only; rw [hsub]; omega,
                  { hst1_len with heur_ok := hhok' },
                  (by dsimp only [st1]; exact congrArg (fun x => { x with
                    vals := st1.vals, lvl := st1.lvl, rsns := st1.rsns, heur := hr' }) hag),
                  hrt'.trans hrt, fun F0 hcore htl => by
                    dsimp only; rw [hsub]
                    exact btPrefixInv_step hcore (hbt_fn F0 hcore htl) hp hgt' hhok', hm'⟩
            pi_shallow_steps
            have hm1 : (PlainMem c st1 ⋆ R) m := by
              dsimp only [st1]
              simpa only [← hlit_eq, bv_c0_zext32_64, bv32_lshr_1, BitVec.toNat_xor,
                show (1 : BitVec 32).toNat = 1 from rfl,
                show (0 : BitVec 32) = 0#32 from rfl,
                show (4294967295 : BitVec 32) = 0xFFFFFFFF#32 from rfl] using hm
            clear hm
            have hv32_qs : (BitVec.setWidth 64 (st.trl[(te_v - 1).toNat] >>> 1)).toNat <
                st1.heur.q_stamp.length := by
              rw [hst1_len.heur_ok.q_stamp_len, ← hst_len.lvl_len]; exact h3
            exact backtrack_pop_step_wp hHeapPush hst1_len rfl hv32_qs hm1 hstep_b
        · pi_shallow_steps
          exact hB (te_v, ()) ml ⟨st, hte_le, hst_len, hag, hrt,
            fun F0 hcore htl => ⟨hbt_fn F0 hcore htl, Or.inl (by
              clear hml hQ; simp only [Arg.val_var, bv_c0] at hnz; omega)⟩, hml⟩
  · intro J0 hJ0; pi_head_steps
    refine wp_jnz_of (fun _ => ?_) (fun _ => ?_)
    · pi_head_steps; refine wp_jnz_of (fun _ => ?_) (fun _ => ?_)
      · pi_head_steps
        refine wp_join_group (ts := []) (fun () m1 => ∃ heur1 : PlainHeur, heur1.LengthsOk c ∧
            heur1.rel_trigger = s.heur.rel_trigger ∧
            (PlainMem c { s with heur := heur1 } ⋆ R) m1) ?_ ?_
        · rintro _ ⟨⟩ m1 ⟨heur1, hhok1, hrt1, hm1⟩; pi_head_steps
          refine wp_join_group (ts := []) (fun () m2 => ∃ heur2 : PlainHeur,
              heur2.LengthsOk c ∧ heur2.rel_trigger = s.heur.rel_trigger ∧
              (PlainMem c { s with heur := heur2 } ⋆ R) m2)
            (fun _ _ m2 h => by pi_shallow_steps; exact hJ0 () m2 h) ?_
          · intro J0' hJ0'; pi_head_steps; refine wp_jnz_of (fun _ => ?_) (fun _ => ?_)
            · pi_shallow_steps
              refine wp_loop_inv (fun (kv : Tup Val [i64]) ml => ∃ pb' : List (BitVec 8),
                  kv.1.toNat ≤ c.mv ∧ pb'.length = c.mv ∧
                  (PlainMem c { s with heur := { heur1 with
                    best_assigned := BitVec.ofNat 64 s.trail_end, phases_best := pb' } } ⋆ R) ml)
                (fun kv _ => c.mv - kv.1.toNat) ?_ ?_
              · intro Lk hLk; pi_shallow_steps
                exact hLk (0#64, ()) _ ⟨heur1.phases_best, Nat.zero_le _, hhok1.phases_best_len, hm⟩
              · intro Lk ⟨kv, ⟨⟩⟩ ml ⟨pb', hkle, hpbl, hml⟩ hLk
                dsimp only at hkle; p_lets
                refine wp_head_jnz_iff (b := decide (kv.toNat < c.mv)) (by
                  simp only [Arg.val_var]; rw [← bv_ofNat_toNat_eq kv,
                    bv_ult_eq kv.isLt (by omega), bv64_ofNat_toNat kv.isLt]) ?_
                rw [decide_eq_true_eq, decide_eq_false_iff_not]
                refine ⟨fun hklt => ?_, fun hkge => ?_⟩
                · pi_shallow_lets
                  refine wp_load_of (c0_load_arena_vals
                    (by rw [hlen.vals_len]; clear hml hQ; bv_omega) hml) ?_
                  pi_shallow_lets
                  apply wp_store_sep
                  · refine c0_store_arena_phases_best _ (by simp [hpbl]; exact hklt) hml
                  intro m' hm'; pi_shallow_steps
                  have hk1 : (kv + 1#64).toNat = kv.toNat + 1 := by
                    clear hml hm' hQ; simp only [bv_c0]; omega
                  exact hLk (kv + 1#64, ()) m' (by dsimp only; rw [hk1]; omega)
                    ⟨pb'.set kv.toNat _, by dsimp only; rw [hk1]; omega, by simp [hpbl], hm'⟩
                · pi_shallow_steps
                  let hr' : PlainHeur := { heur1 with
                    best_assigned := BitVec.ofNat 64 s.trail_end, phases_best := pb' }
                  exact hJ0' () _ ⟨hr', { hhok1 with phases_best_len := hpbl }, hrt1, hml⟩
            · pi_shallow_steps; exact hJ0' () _ ⟨heur1, hhok1, hrt1, hm1⟩
        · intro J1 hJ1; pi_head_steps
          refine wp_jnz_of (fun _ => ?_) (fun _ => ?_)
          · pi_shallow_steps
            refine wp_loop_inv (fun (kv : Tup Val [i64]) ml => ∃ pt' : List (BitVec 8),
                kv.1.toNat ≤ c.mv ∧ pt'.length = c.mv ∧
                (PlainMem c { s with heur := { s.heur with
                  target_assigned := BitVec.ofNat 64 s.trail_end, phases_target := pt' } } ⋆ R) ml)
              (fun kv _ => c.mv - kv.1.toNat) ?_ ?_
            · intro Lk hLk; pi_shallow_steps
              exact hLk (0#64, ()) _ ⟨s.heur.phases_target, Nat.zero_le _,
                hlen.heur_ok.phases_target_len, hm⟩
            · intro Lk ⟨kv, ⟨⟩⟩ ml ⟨pt', hkle, hptl, hml⟩ hLk
              dsimp only at hkle; p_lets
              refine wp_head_jnz_iff (b := decide (kv.toNat < c.mv)) (by
                simp only [Arg.val_var]; rw [← bv_ofNat_toNat_eq kv,
                  bv_ult_eq kv.isLt (by omega), bv64_ofNat_toNat kv.isLt]) ?_
              rw [decide_eq_true_eq, decide_eq_false_iff_not]
              refine ⟨fun hklt => ?_, fun hkge => ?_⟩
              · pi_shallow_lets
                refine wp_load_of (c0_load_arena_vals
                  (by rw [hlen.vals_len]; clear hml hQ; bv_omega) hml) ?_
                pi_shallow_lets
                apply wp_store_sep
                · refine c0_store_arena_phases_target _ (by simp [hptl]; exact hklt) hml
                intro m' hm'; pi_shallow_steps
                have hk1 : (kv + 1#64).toNat = kv.toNat + 1 := by
                  clear hml hm' hQ; simp only [bv_c0]; omega
                exact hLk (kv + 1#64, ()) m' (by dsimp only; rw [hk1]; omega)
                  ⟨pt'.set kv.toNat _, by dsimp only; rw [hk1]; omega, by simp [hptl], hm'⟩
              · pi_shallow_steps
                let hr' : PlainHeur := { s.heur with
                  target_assigned := BitVec.ofNat 64 s.trail_end, phases_target := pt' }
                exact hJ1 () _ ⟨hr', { hlen.heur_ok with phases_target_len := hptl }, rfl, hml⟩
          · pi_shallow_steps; exact hJ1 () _ ⟨s.heur, hlen.heur_ok, rfl, hm⟩
      · pi_shallow_steps; exact hJ0 () _ ⟨s.heur, hlen.heur_ok, rfl, hm⟩
    · pi_shallow_steps; exact hJ0 () _ ⟨s.heur, hlen.heur_ok, rfl, hm⟩

/-! ## 5. `plain_parse_body` -/

private theorem plain_mem_to_dimacs {c : PlainCfg} {s : PlainState} {cnf_ptr : BitVec 64}
    {cnfBytes : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (bytes cnf_ptr cnfBytes ⋆ PlainMem c s ⋆ R) m) :
    (bytes cnf_ptr cnfBytes ⋆
      dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.d_cur s.d_val ⋆
      (PlainRest c s ⋆ R)) m := by rw [plainMem_eq_dimacs_sep] at h; exact sep_ac h

private theorem plain_dimacs_to_mem {c : PlainCfg} {s : PlainState} {cur' val' cnf_ptr : BitVec 64}
    {cnfBytes : List UInt8} {R : Mem 64 → Prop} {m : Mem 64}
    (h : (bytes cnf_ptr cnfBytes ⋆
      dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) cur' val' ⋆
      (PlainRest c s ⋆ R)) m) :
    (bytes cnf_ptr cnfBytes ⋆ PlainMem c { s with d_cur := cur', d_val := val' } ⋆ R) m := by
  rw [plainMem_eq_dimacs_sep, plainRest_d_irrel]; exact sep_ac h

private structure ParseBodyInv (c : PlainCfg) (s : PlainState) (cnf_ptr : BitVec 64)
    (cnfBytes : List UInt8) (i0 i idx : Nat) (accCnf : CNF Nat) (unsat oom : Bool)
    (st : PlainState) : Prop where
  i_le : i ≤ c.nc
  idx_le : idx ≤ cnfBytes.length
  d_cur_eq : st.d_cur = cnf_ptr + BitVec.ofNat 64 idx
  len_ok : st.LengthsOk c
  cl0 : st.cur_level = 0
  fuel_eq : st.fuel = s.fuel
  oom_eq : st.oom = 0#64
  prb_eq : st.probing = 0#64
  rt_eq : st.heur.rel_trigger = s.heur.rel_trigger
  vars_pos : CnfVarsPos accCnf
  pc_eq : parseClauses c.mv (c.nc - i) accCnf (cnfBytes.drop idx) = parseDimacs cnfBytes
  uns_inv : unsat = true → (shiftDownCnf accCnf).Unsat
  ok_inv : unsat = false → oom = false → PlainInv c (shiftDownCnf accCnf) st
  sat_tr : ∀ vals' te', UnitSatTrace c.mv s.vals 0 (cnfBytes.drop i0) c.nc vals' te' →
    unsat = false ∧ oom = false ∧ st.propagated = 0 ∧ st.arena_len = 0 ∧ st.wvec = s.wvec ∧
    UnitSatTrace c.mv st.vals st.trail_end (cnfBytes.drop idx) (c.nc - i) vals' te'
  uns_tr : UnitUnsatTrace c.mv s.vals (cnfBytes.drop i0) c.nc →
    oom = false ∧
    ((unsat = false ∧ UnitUnsatTrace c.mv st.vals (cnfBytes.drop idx) (c.nc - i)) ∨
     (unsat = true ∧ ∃ cnf, parseClauses c.mv (c.nc - i) CNF.empty (cnfBytes.drop idx) = some cnf))

private theorem parse_body_skip_step {c : PlainCfg} {s st st' : PlainState}
    {cnf_ptr : BitVec 64} {cnfBytes rest : List UInt8} {i0 i idx j : Nat} {accCnf : CNF Nat}
    {oom : Bool} {cl : CNF.Clause Nat}
    (hp : ParseBodyInv c s cnf_ptr cnfBytes i0 i idx accCnf true oom st)
    (hi : i < c.nc) (hpc1 : parseClause c.mv (cnfBytes.drop idx) = some (cl, rest))
    (hcl_pos : ∀ lit ∈ cl.literals, 1 ≤ lit.1) (hj : j ≤ cnfBytes.length)
    (hdrop : cnfBytes.drop j = rest)
    (hst' : st' = { st with d_cur := cnf_ptr + BitVec.ofNat 64 j, d_val := 0#64 }) :
    ParseBodyInv c s cnf_ptr cnfBytes i0 (i + 1) j (accCnf.add cl) true oom st' := by
  have hsub : c.nc - i = (c.nc - (i + 1)) + 1 := by omega
  refine ⟨by omega, hj, by rw [hst'],
    by rw [hst']; exact { hp.len_ok with vals_len := hp.len_ok.vals_len },
    by rw [hst']; exact hp.cl0, by rw [hst']; exact hp.fuel_eq, by rw [hst']; exact hp.oom_eq,
    by rw [hst']; exact hp.prb_eq, by rw [hst']; exact hp.rt_eq,
    cnfVarsPos_add hp.vars_pos hcl_pos,
    by rw [← hp.pc_eq, hsub, parseClauses, hpc1, ← hdrop]; rfl,
    (fun _ => by rw [shiftDownCnf_add]; exact cnf_unsat_add (hp.uns_inv rfl)),
    (fun hc => by cases hc),
    (fun vals' te' hst => by have h1 := (hp.sat_tr vals' te' hst).1; cases h1),
    (fun hut => by
      obtain ⟨hoom, hdisj⟩ := hp.uns_tr hut; refine ⟨hoom, Or.inr ⟨rfl, ?_⟩⟩
      rcases hdisj with ⟨hf, _⟩ | ⟨_, cnf_r, hr⟩
      · cases hf
      · rw [hsub, parseClauses, hpc1, ← hdrop] at hr; exact parseClauses_some_of_acc hr)⟩

private theorem parse_body_ingest_step {c : PlainCfg} {s st st' : PlainState}
    {cnf_ptr : BitVec 64} {cnfBytes rest : List UInt8} {i0 i idx j : Nat} {accCnf : CNF Nat}
    {r_in : BitVec 64} {cl : CNF.Clause Nat}
    (hp : ParseBodyInv c s cnf_ptr cnfBytes i0 i idx accCnf false false st)
    (hi : i < c.nc) (hpc1 : parseClause c.mv (cnfBytes.drop idx) = some (cl, rest))
    (hcl_pos : ∀ lit ∈ cl.literals, 1 ≤ lit.1) (hj : j ≤ cnfBytes.length)
    (hdrop : cnfBytes.drop j = rest) (hlen' : st'.LengthsOk c)
    (hd' : st'.d_cur = cnf_ptr + BitVec.ofNat 64 j) (hcl' : st'.cur_level = 0)
    (hfu' : st'.fuel = st.fuel) (hoom' : st'.oom = st.oom) (hprb' : st'.probing = st.probing)
    (hrt' : st'.heur.rel_trigger = st.heur.rel_trigger)
    (hr_dom : r_in = 1#64 ∨ r_in = 2#64 ∨ r_in = 3#64)
    (hok_in : r_in = 1#64 → PlainInv c (shiftDownCnf (accCnf.add cl)) st')
    (huns_in : r_in = 2#64 → (shiftDownCnf (accCnf.add cl)).Unsat)
    (hunit_ok : ∀ l < 2 * c.mv, cl = CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l] →
      st.vals[l]?.getD 0#8 = 0#8 → r_in = 1#64 ∧
      st'.vals = (st.vals.set l 1#8).set (l ^^^ 1) 0xFF#8 ∧ st'.trail_end = st.trail_end + 1 ∧
      st'.propagated = st.propagated ∧ st'.arena_len = st.arena_len ∧
      st'.wlen = st.wlen ∧ st'.wvec = st.wvec)
    (hunit_fl : ∀ l < 2 * c.mv, cl = CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l] →
      st.vals[l]?.getD 0#8 = 0xFF#8 → r_in = 2#64) :
    ParseBodyInv c s cnf_ptr cnfBytes i0 (i + 1) j (accCnf.add cl)
      (decide (r_in = 2#64)) (decide (r_in = 3#64)) st' := by
  have hsub : c.nc - i = (c.nc - (i + 1)) + 1 := by omega
  have hpc_next : parseClauses c.mv (c.nc - (i + 1)) (accCnf.add cl) (cnfBytes.drop j) =
      parseDimacs cnfBytes := by rw [← hp.pc_eq, hsub, parseClauses, hpc1, ← hdrop]; rfl
  rcases hr_dom with rfl | rfl | rfl <;>
    refine ⟨by omega, hj, hd', hlen', hcl', hfu'.trans hp.fuel_eq, hoom'.trans hp.oom_eq,
      hprb'.trans hp.prb_eq, hrt'.trans hp.rt_eq,
      cnfVarsPos_add hp.vars_pos hcl_pos, hpc_next, ?_, ?_, ?_, ?_⟩
  · exact fun hc => by cases hc
  · exact fun _ _ => hok_in rfl
  · intro vals' te' hst; obtain ⟨_, _, hpr_z, har_z, hwv_z, htr⟩ := hp.sat_tr vals' te' hst
    rw [hsub] at htr; cases htr with
    | step hl hpc_s hv0 htr_next =>
      rw [hpc1] at hpc_s; rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, hreq⟩
      obtain ⟨_, hvs, htes, hprs, hars, _, hwvs⟩ := hunit_ok _ hl hcl_eq hv0
      refine ⟨rfl, rfl, by rw [hprs, hpr_z], by rw [hars, har_z], by rw [hwvs, hwv_z], ?_⟩
      rw [hvs, htes, hdrop, hreq]; exact htr_next
  · intro hut; refine ⟨rfl, Or.inl ⟨rfl, ?_⟩⟩
    rcases (hp.uns_tr hut).2 with ⟨_, htr⟩ | ⟨ht, _⟩
    · rw [hsub] at htr; cases htr with
      | conflict hl hpc_s hvf _ =>
        rw [hpc1] at hpc_s; rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, _⟩
        have hr2 := hunit_fl _ hl hcl_eq hvf; cases hr2
      | step hl hpc_s hv0 htr_next =>
        rw [hpc1] at hpc_s; rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, hreq⟩
        obtain ⟨_, hvs, _, _, _, _, _⟩ := hunit_ok _ hl hcl_eq hv0
        rw [hvs, hdrop, hreq]; exact htr_next
    · cases ht
  · exact fun _ => huns_in rfl
  · exact fun hc => by cases hc
  · intro vals' te' hst; have htr := (hp.sat_tr vals' te' hst).2.2.2.2.2; rw [hsub] at htr
    cases htr with | step hl hpc_s hv0 _ =>
      rw [hpc1] at hpc_s; rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, _⟩
      exact absurd (hunit_ok _ hl hcl_eq hv0).1 (by decide)
  · intro hut; refine ⟨rfl, Or.inr ⟨rfl, ?_⟩⟩
    rcases (hp.uns_tr hut).2 with ⟨_, htr⟩ | ⟨ht, _⟩
    · rw [hsub] at htr; cases htr with
      | conflict _ hpc_s _ hrest =>
        rw [hpc1] at hpc_s; rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨_, hreq⟩
        rwa [hdrop, hreq]
      | step hl hpc_s hv0 _ =>
        rw [hpc1] at hpc_s; rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, _⟩
        exact absurd (hunit_ok _ hl hcl_eq hv0).1 (by decide)
    · cases ht
  · exact fun hc => by cases hc
  · exact fun _ hc => by cases hc
  · intro vals' te' hst; have htr := (hp.sat_tr vals' te' hst).2.2.2.2.2; rw [hsub] at htr
    cases htr with | step hl hpc_s hv0 _ =>
      rw [hpc1] at hpc_s; rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, _⟩
      exact absurd (hunit_ok _ hl hcl_eq hv0).1 (by decide)
  · intro hut; rcases (hp.uns_tr hut).2 with ⟨_, htr⟩ | ⟨ht, _⟩
    · rw [hsub] at htr; cases htr with
      | conflict hl hpc_s hvf _ =>
        rw [hpc1] at hpc_s; rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, _⟩
        exact absurd (hunit_fl _ hl hcl_eq hvf) (by decide)
      | step hl hpc_s hv0 _ =>
        rw [hpc1] at hpc_s; rcases Prod.mk.inj (Option.some.inj hpc_s) with ⟨hcl_eq, _⟩
        exact absurd (hunit_ok _ hl hcl_eq hv0).1 (by decide)
    · cases ht

private abbrev ParseBodyPost (c : PlainCfg) (s : PlainState) (cnf_ptr : BitVec 64)
    (cnfBytes : List UInt8) (i0 : Nat) (R : Mem 64 → Prop) (Q : Post [i64]) : Prop :=
  ∀ r st' m', st'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) → st'.fuel = s.fuel →
    st'.oom = 0#64 → st'.probing = 0#64 → st'.heur.rel_trigger = s.heur.rel_trigger →
    (r = 20#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧ CNF.Unsat cnf) →
    (r = 1#64 → ∃ cnf, parseDimacs cnfBytes = some cnf ∧
      PlainInv c (shiftDownCnf cnf) st' ∧ st'.cur_level = 0) →
    (∀ vals' te', UnitSatTrace c.mv s.vals 0 (cnfBytes.drop i0) c.nc vals' te' →
      r = 1#64 ∧ st'.vals = vals' ∧ st'.trail_end = te' ∧ st'.propagated = 0 ∧
      st'.arena_len = 0 ∧ st'.wvec = s.wvec) →
    (UnitUnsatTrace c.mv s.vals (cnfBytes.drop i0) c.nc → r = 20#64) →
    (bytes cnf_ptr cnfBytes ⋆ PlainMem c st' ⋆ R) m' → Q (r, ()) m'

private theorem parse_body_oom_exit {c : PlainCfg} {s st : PlainState}
    {cnf_ptr : BitVec 64} {cnfBytes : List UInt8} {i0 i idx : Nat} {accCnf : CNF Nat}
    {unsat_v : Bool} {R : Mem 64 → Prop} {ml : Mem 64} {Q : Post [i64]}
    (hp : ParseBodyInv c s cnf_ptr cnfBytes i0 i idx accCnf unsat_v true st)
    (hml : (bytes cnf_ptr cnfBytes ⋆ PlainMem c st ⋆ R) ml)
    (hQ : ParseBodyPost c s cnf_ptr cnfBytes i0 R Q) : Q (0#64, ()) ml :=
  hQ 0#64 st ml hp.len_ok (Or.inl rfl) hp.fuel_eq hp.oom_eq hp.prb_eq hp.rt_eq
    (fun h => by cases h) (fun h => by cases h)
    (fun vals' te' hst => by cases (hp.sat_tr vals' te' hst).2.1)
    (fun hut => by cases (hp.uns_tr hut).1) hml

private theorem parse_body_eof_ne {c : PlainCfg} {s st : PlainState}
    {cnf_ptr : BitVec 64} {cnfBytes : List UInt8} {i0 idx j : Nat} {accCnf : CNF Nat}
    {unsat_v oom_v : Bool} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i64]}
    (hp : ParseBodyInv c s cnf_ptr cnfBytes i0 c.nc idx accCnf unsat_v oom_v st)
    (_hidx : idx ≤ cnfBytes.length) (hj : j ≤ cnfBytes.length)
    (hsw : cnfBytes.drop j = skipWsComments (cnfBytes.drop idx))
    (hne : cnf_ptr + BitVec.ofNat 64 j ≠ cnf_ptr + BitVec.ofNat 64 cnfBytes.length)
    (hfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ PlainMem c { st with d_cur := cnf_ptr + BitVec.ofNat 64 j }
      ⋆ R) m') (hQ : ParseBodyPost c s cnf_ptr cnfBytes i0 R Q) : Q (0#64, ()) m' := by
  have hj_lt : j < cnfBytes.length := by
    have hj_ne : j ≠ cnfBytes.length := fun heq =>
      hne ((cursor_eq_iff (base := cnf_ptr) (by omega) (by omega)).mpr heq)
    omega
  have hne_emp : (skipWsComments (cnfBytes.drop idx)).isEmpty = false := by
    rw [← hsw, List.drop_eq_getElem_cons hj_lt]; rfl
  exact hQ 0#64 { st with d_cur := cnf_ptr + BitVec.ofNat 64 j } m'
    { hp.len_ok with vals_len := hp.len_ok.vals_len } (Or.inl rfl) hp.fuel_eq hp.oom_eq
    hp.prb_eq hp.rt_eq (fun h => by cases h) (fun h => by cases h)
    (fun vals' te' hst => by
      have htr := (hp.sat_tr vals' te' hst).2.2.2.2.2; rw [Nat.sub_self] at htr
      cases htr with | done hemp => rw [hne_emp] at hemp; cases hemp)
    (fun hut => by
      rcases (hp.uns_tr hut).2 with ⟨_, htr⟩ | ⟨_, _, hr⟩
      · rw [Nat.sub_self] at htr; cases htr
      · rw [Nat.sub_self] at hr
        simp only [parseClauses, hne_emp, Bool.false_eq_true, ↓reduceIte] at hr; cases hr) hm

private theorem parse_body_eof_done {c : PlainCfg} {s st : PlainState}
    {cnf_ptr : BitVec 64} {cnfBytes : List UInt8} {i0 idx j : Nat} {accCnf : CNF Nat}
    {unsat_v oom_v : Bool} {R : Mem 64 → Prop} {m' : Mem 64} {Q : Post [i64]}
    (hp : ParseBodyInv c s cnf_ptr cnfBytes i0 c.nc idx accCnf unsat_v oom_v st)
    (_hidx : idx ≤ cnfBytes.length) (hj : j ≤ cnfBytes.length)
    (hsw : cnfBytes.drop j = skipWsComments (cnfBytes.drop idx))
    (heq : cnf_ptr + BitVec.ofNat 64 j = cnf_ptr + BitVec.ofNat 64 cnfBytes.length)
    (hfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hm : (bytes cnf_ptr cnfBytes ⋆ PlainMem c { st with d_cur := cnf_ptr + BitVec.ofNat 64 j }
      ⋆ R) m') (hQ : ParseBodyPost c s cnf_ptr cnfBytes i0 R Q)
    (hret : (unsat_v = true ∧ cnf_ptr = cnf_ptr) ∨ (unsat_v = false ∧ oom_v = false)) :
    Q (if unsat_v then 20#64 else 1#64, ()) m' := by
  have hj_len : j = cnfBytes.length := (cursor_eq_iff (by omega) (by omega)).mp heq
  have hemp : (skipWsComments (cnfBytes.drop idx)).isEmpty = true := by
    rw [← hsw, hj_len, List.drop_length]; rfl
  have hpc_eq := hp.pc_eq; simp only [Nat.sub_self, parseClauses] at hpc_eq
  have hpd_some : parseDimacs cnfBytes = some accCnf := by rw [← hpc_eq]; simp [hemp]
  let sf : PlainState := { st with d_cur := cnf_ptr + BitVec.ofNat 64 j }
  have hlen_sf : sf.LengthsOk c := { hp.len_ok with vals_len := hp.len_ok.vals_len }
  rcases hret with ⟨hunt, _⟩ | ⟨huf, hnf⟩
  · subst hunt
    exact hQ 20#64 sf m' hlen_sf (Or.inr (Or.inr rfl)) hp.fuel_eq hp.oom_eq hp.prb_eq hp.rt_eq
      (fun _ => ⟨accCnf, hpd_some, shiftDownCnf_unsat hp.vars_pos (hp.uns_inv rfl)⟩)
      (fun h => by cases h) (fun vals' te' hst => by cases (hp.sat_tr vals' te' hst).1)
      (fun _ => rfl) hm
  · subst huf hnf
    have hinv_sf := (hp.ok_inv rfl rfl).with_d (cnf_ptr + BitVec.ofNat 64 j) st.d_val
    exact hQ 1#64 sf m' hlen_sf (Or.inr (Or.inl rfl)) hp.fuel_eq hp.oom_eq hp.prb_eq hp.rt_eq
      (fun h => by cases h) (fun _ => ⟨accCnf, hpd_some, hinv_sf, hp.cl0⟩)
      (fun vals' te' hst => by
        obtain ⟨_, _, hpr_z, har_z, hwv_z, htr⟩ := hp.sat_tr vals' te' hst
        rw [Nat.sub_self] at htr; cases htr with
        | done _ => exact ⟨rfl, rfl, rfl, hpr_z, har_z, hwv_z⟩)
      (fun hut => by rcases (hp.uns_tr hut).2 with ⟨_, htr⟩ | ⟨ht, _⟩
                     · rw [Nat.sub_self] at htr; cases htr
                     · cases ht) hm

theorem plain_parse_body_wp (Γ : Env)
    (hSkip : ∀ a m Q X, plainSkipClSpec a m Q X → Γ "plain_skip_cl" [i64, i64] [.bool] a m Q X)
    (hIngest : ∀ a m Q X, plainIngestClSpec a m Q X →
      Γ "plain_ingest_cl" [i64, i64] [i64] a m Q X)
    (hSwc : ∀ a m Q X, kissatSkipWsCommentsSpec a m Q X →
      Γ "kissat_skip_ws_comments" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, plainParseBodySpec a m Q X → Func.wp Γ plain_parse_body_body a m Q X := by
  rintro ⟨h, cend, ⟨⟩⟩ m Q X
    ⟨c, s, cnf_ptr, cnfBytes, i0, R, rfl, rfl, hfit, hi0, hhdr, hdcur, hcl0, hte0, hpr0, har0,
      hoom0, hprb0, hinv0, hm, hQ⟩
  have hnc_bd := c.hnc; have hmv_bd := c.hmv; unfold dimacsBound at hnc_bd hmv_bd
  have hpd_init : parseClauses c.mv c.nc CNF.empty (cnfBytes.drop i0) = parseDimacs cnfBytes := by
    simp [parseDimacs, hhdr]
  pi_steps
  refine wp_loop_group (fun r (unsat_v, oom_v, iv, ()) ml => ∃ i idx accCnf st,
      r = c.nc - i ∧ iv = BitVec.ofNat 64 i ∧ ParseBodyInv c s cnf_ptr cnfBytes i0 i idx accCnf
        unsat_v oom_v st ∧ (bytes cnf_ptr cnfBytes ⋆ PlainMem c st ⋆ R) ml) ?_ ?_
  · rintro L r ⟨unsat_v, oom_v, iv, ⟨⟩⟩ ml ih ⟨i, idx, accCnf, st, rfl, rfl, hp, hml⟩
    have hile := hp.i_le; have hidx := hp.idx_le; have hdcur_st := hp.d_cur_eq
    have hlen_st := hp.len_ok; have hcl_st := hp.cl0; have hfu_st := hp.fuel_eq
    have hoom_st := hp.oom_eq; have hprb_st := hp.prb_eq; have hrt_st := hp.rt_eq
    pi_steps
    · have hilt : i < c.nc := by clear hm hml hQ; c0_bound
      have hunt : unsat_v = true := by assumption
      subst hunt; have hsub_eq : c.nc - i = (c.nc - (i + 1)) + 1 := by omega
      have hinc : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := by
        apply BitVec.eq_of_toNat_eq; change (i % 2 ^ 64 + 1) % 2 ^ 64 = (i + 1) % 2 ^ 64; omega
      c0_call hSkip
      refine ⟨cnf_ptr, BitVec.ofNat 64 c.nc, st.d_val, c.mv, cnfBytes, idx,
        PlainRest c st ⋆ R, rfl, hfit, by omega, hidx,
        by rw [← hdcur_st]; exact plain_mem_to_dimacs hml, ?_⟩
      cases hpc1 : parseClause c.mv (cnfBytes.drop idx) with
      | none =>
        intro cur' val' m' hm'; pi_steps
        · exact False.elim (Bool.false_ne_true (by assumption))
        · exact hQ 0#64 { st with d_cur := cur', d_val := val' } m'
            { hlen_st with vals_len := hlen_st.vals_len } (Or.inl rfl) hfu_st hoom_st hprb_st
            hrt_st (fun h => by cases h) (fun h => by cases h)
            (fun vals' te' hst => by cases (hp.sat_tr vals' te' hst).1)
            (fun hut => by rcases (hp.uns_tr hut).2 with ⟨hf, _⟩ | ⟨_, _, hr⟩
                           · cases hf
                           · rw [hsub_eq, parseClauses, hpc1] at hr; cases hr)
            (plain_dimacs_to_mem hm')
      | some p =>
        rcases p with ⟨cl, rest⟩; intro j m' hcl_pos _ hj hdrop hm'; pi_steps
        · exact ih (c.nc - (i + 1)) _ _ (by omega)
            ⟨i + 1, j, accCnf.add cl, _, rfl, hinc,
              parse_body_skip_step hp hilt hpc1 hcl_pos hj hdrop rfl, plain_dimacs_to_mem hm'⟩
        · cases (by assumption : true = false)
    · have hoo : oom_v = true := by assumption
      subst hoo; exact parse_body_oom_exit hp hml hQ
    · have hilt : i < c.nc := by clear hm hml hQ; c0_bound
      have huf : unsat_v = false := by assumption
      have hnf : oom_v = false := by assumption
      subst huf hnf; have hsub_eq : c.nc - i = (c.nc - (i + 1)) + 1 := by omega
      have hinc : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i + 1) := by
        apply BitVec.eq_of_toNat_eq; change (i % 2 ^ 64 + 1) % 2 ^ 64 = (i + 1) % 2 ^ 64; omega
      c0_call hIngest
      refine ⟨c, accCnf, st, cnf_ptr, cnfBytes, idx, R, rfl, rfl, hfit, hidx, hdcur_st,
        hcl_st, hp.ok_inv rfl rfl, hml, ?_⟩
      cases hpc1 : parseClause c.mv (cnfBytes.drop idx) with
      | none =>
        intro st' m' hlen' hfu' hoom' hprb' hrt' hm'; pi_steps
        · exact hQ 0#64 st' m' hlen' (Or.inl rfl) (hfu'.trans hfu_st) (hoom'.trans hoom_st)
            (hprb'.trans hprb_st) (hrt'.trans hrt_st) (fun h => by cases h) (fun h => by cases h)
            (fun vals' te' hst => by
              have htr := (hp.sat_tr vals' te' hst).2.2.2.2.2; rw [hsub_eq] at htr
              cases htr with | step _ hpc_s _ _ => rw [hpc1] at hpc_s; cases hpc_s)
            (fun hut => by rcases (hp.uns_tr hut).2 with ⟨_, htr⟩ | ⟨ht, _⟩
                           · rw [hsub_eq] at htr; cases htr with
                             | conflict _ hpc_s _ _ => rw [hpc1] at hpc_s; cases hpc_s
                             | step _ hpc_s _ _ => rw [hpc1] at hpc_s; cases hpc_s
                           · cases ht) hm'
        · exact absurd rfl (by assumption : ¬(0#64 : BitVec 64) = 0)
      | some p =>
        rcases p with ⟨cl, rest⟩
        intro r_in st' j m' hcl_pos _ hj hdrop hlen' hd' hcl' hfu' hoom' hprb' hrt' hr_dom
          hok_in huns_in hunit_ok hunit_fl hm'
        rcases hr_dom with rfl | rfl | rfl <;> pi_steps <;>
          first
          | (exact absurd rfl (by assumption : ¬(2#64 : BitVec 64) = 2))
          | (exact absurd rfl (by assumption : ¬(3#64 : BitVec 64) = 3))
          | exact ih (c.nc - (i + 1)) _ _ (by omega)
              ⟨i + 1, j, accCnf.add cl, st', rfl, hinc, by
                simpa using parse_body_ingest_step hp hilt hpc1 hcl_pos hj hdrop hlen'
                  hd' hcl' hfu' hoom' hprb' hrt' (by simp) hok_in huns_in hunit_ok hunit_fl, hm'⟩
    · have hoo : oom_v = true := by assumption
      subst hoo; exact parse_body_oom_exit hp hml hQ
    · have hieq : i = c.nc := by clear hml hQ; c0_bound
      subst hieq; c0_call hSwc
      refine ⟨cnf_ptr, cnfBytes, idx, PlainMem c st ⋆ R, hdcur_st, rfl, hfit, hidx,
        sep_ac hml, fun j _ hj hsw => ?_⟩
      pi_steps
      · exact parse_body_eof_ne hp hidx hj hsw (by assumption) hfit (sep_ac hm) hQ
      · have hunt : unsat_v = true := by assumption
        simpa [hunt] using parse_body_eof_done hp hidx hj hsw (by assumption) hfit (sep_ac hm) hQ
          (Or.inl ⟨hunt, rfl⟩)
      · have huf : unsat_v = false := by assumption
        have hnf : oom_v = false := by assumption
        simpa [huf] using parse_body_eof_done hp hidx hj hsw (by assumption) hfit (sep_ac hm) hQ
          (Or.inr ⟨huf, hnf⟩)
  · intro L hL; pi_steps
    exact hL c.nc _ m ⟨0, i0, CNF.empty, s, by simp, rfl,
      ⟨Nat.zero_le _, hi0, hdcur, hinv0.core.lengths, hcl0, rfl, hoom0, hprb0, rfl,
        cnfVarsPos_empty, by simpa using hpd_init, (fun hc => by cases hc), fun _ _ => hinv0,
        fun vals' te' hst => ⟨rfl, rfl, hpr0, har0, rfl, by simpa [hte0] using hst⟩,
        fun hut => ⟨rfl, Or.inl ⟨rfl, by simpa using hut⟩⟩⟩, hm⟩

end LeanQbe.T.Examples.Kissat.Plain
