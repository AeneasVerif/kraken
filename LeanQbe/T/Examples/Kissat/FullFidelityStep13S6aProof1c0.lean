/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityTumbleSpec
import LeanQbe.T.Examples.Kissat.FullDimacsBodyLemmas1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 Shard `S6a` — `full_ingest_cl_tum` Helpers & Read Loop (`Proof1c0`)

Pure tumble/unit/keep helpers and read-loop lemma `s6a_ingest_read_loop_wp` factored out of
`FullFidelityTumbleProofIngest.lean` so `FullFidelityStep13S6aProof1c.lean` keeps every theorem
`<= 450` LOC and every file `< 1,500` LOC (`<= std3`, `0` `@[expose]` on theorems/lemmas).
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full LeanQbe.T.Examples.Kissat.FullFidelityTumble
open Kraken.Bedrock2.Test

@[expose] public section

def ingestTumStR (s : FullState) (dc dv : BitVec 64) (mk : List (BitVec 8))
    (tp fd : List (BitVec 32)) (elen : Nat) : FullState :=
  { core := { s.core with d_cur := dc, d_val := dv, mrk := mk, tmp := tp, frame_dec := fd }
    scratch := { s.scratch with extend_len := elen } }

def IngestTumReadInv (c : FullCfg) (accCnf : CNF Nat) (s : FullState)
    (cnfBytes : List UInt8) (i0 idx tlen elen : Nat) (taut : Bool) (revLits : List Nat)
    (mrk' : List (BitVec 8)) (tmp' fd' : List (BitVec 32)) : Prop :=
  let tum := decide (c.mv < c.extend_cap)
  i0 ≤ idx ∧ idx ≤ cnfBytes.length ∧ tlen ≤ c.mv ∧
  mrk'.length = c.max_vars ∧ tmp'.length = c.max_vars ∧ fd'.length = c.max_vars + 1 ∧
  s.scratch.extend_len ≤ elen ∧ elen ≤ c.extend_cap ∧
  TumbleInv tum c.mv elen fd' ∧
  TumbleCovers tum fd' (shiftDownCnf accCnf) ∧
  CNF.relabel (tumblePi tum fd') (shiftDownCnf accCnf) =
    CNF.relabel (tumblePi tum s.core.frame_dec) (shiftDownCnf accCnf) ∧
  (∀ e < c.mv, s.core.frame_dec[e]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
    fd'[e]?.getD 0xFFFFFFFF#32 = s.core.frame_dec[e]?.getD 0xFFFFFFFF#32) ∧
  (∀ vext, TumbleValsRel tum c.mv s.core.frame_dec vext s.core.vals →
    TumbleUnusedZero tum c.mv s.scratch.extend_len s.core.vals →
    TumbleValsRel tum c.mv fd' vext s.core.vals) ∧
  (∀ l ∈ revLits, l < 2 * c.mv) ∧
  (tum = true → ∀ l ∈ revLits, fd'[l / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) ∧
  (∀ k < tlen, (tmp'[k]?.getD 0#32).toNat < 2 * c.mv) ∧
  (∀ k1 k2, k1 < tlen → k2 < tlen →
    (tmp'[k1]?.getD 0#32).toNat / 2 = (tmp'[k2]?.getD 0#32).toNat / 2 → k1 = k2) ∧
  (∀ v < c.max_vars, (∀ k < tlen, (tmp'[k]?.getD 0#32).toNat / 2 ≠ v) →
    mrk'[v]?.getD 0#8 = 0#8) ∧
  (∀ k < tlen, mrk'[(tmp'[k]?.getD 0#32).toNat / 2]?.getD 0#8 =
    BitVec.ofNat 8 ((tmp'[k]?.getD 0#32).toNat % 2 + 1)) ∧
  (taut = false → ∀ l ∈ revLits, ∃ k < tlen, (tmp'[k]?.getD 0#32).toNat = tumbleLit tum fd' l) ∧
  (∀ k < tlen, (tmp'[k]?.getD 0#32).toNat ∈ revLits.map (tumbleLit tum fd')) ∧
  (revLits = [] → taut = false) ∧
  (∀ l, revLits = [l] → taut = false ∧ tlen = 1 ∧
    (tmp'[0]?.getD 0#32).toNat = tumbleLit tum fd' l)

def IngestTumPruneInv (c : FullCfg) (s : FullState) (tmp' fd' : List (BitVec 32))
    (revLits : List Nat) (tlen keep i : Nat) (tmp'' : List (BitVec 32)) : Prop :=
  let tum := decide (c.mv < c.extend_cap)
  keep ≤ i ∧ i ≤ tlen ∧ tmp''.length = c.max_vars ∧
  (∀ k, i ≤ k → k < tlen → tmp''[k]? = tmp'[k]?) ∧
  (∀ k < keep, (tmp''[k]?.getD 0#32).toNat < 2 * c.mv ∧
    s.core.vals[(tmp''[k]?.getD 0#32).toNat]?.getD 0#8 = 0#8) ∧
  (∀ k < keep, ∃ m < i, tmp''[k]? = tmp'[m]?) ∧
  (∀ k1 k2, k1 < keep → k2 < keep →
    (tmp''[k1]?.getD 0#32).toNat / 2 = (tmp''[k2]?.getD 0#32).toNat / 2 → k1 = k2) ∧
  (∀ k < i, (∃ j < keep, tmp''[j]? = tmp'[k]?) ∨
    s.core.vals[(tmp'[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8) ∧
  (∀ l < 2 * c.mv, revLits = [l] → s.core.vals[tumbleLit tum fd' l]?.getD 0#8 = 0#8 →
    i = 1 → keep = 1 ∧ (tmp''[0]?.getD 0#32).toNat = tumbleLit tum fd' l) ∧
  (∀ l < 2 * c.mv, revLits = [l] → s.core.vals[tumbleLit tum fd' l]?.getD 0#8 = 0xFF#8 →
    i = 1 → keep = 0)

def ingestGroupFn (V : Ty → Type) (L : List Ty → Type)
    (h cend tmp mrk vals fd : V i64) (tum : V .bool) (d : V i64) : Expr V L [i64] :=
  match full_ingest_cl_tum_body V L (h, cend, ()) with
  | Expr.let_ (ts := [.bits 64]) _ k1 => match k1 (d, ()) with
    | Expr.load (.bits 64) _ k2 => match k2 tmp with
      | Expr.let_ (ts := [.bits 64]) _ k3 => match k3 (d, ()) with
        | Expr.load (.bits 64) _ k4 => match k4 mrk with
          | Expr.let_ (ts := [.bits 64]) _ k5 => match k5 (d, ()) with
            | Expr.load (.bits 64) _ k6 => match k6 vals with
              | Expr.let_ (ts := [.bits 64]) _ k7 => match k7 (d, ()) with
                | Expr.load (.bits 64) _ k8 => match k8 fd with
                  | Expr.let_ (ts := [.bits 64]) _ k9 => match k9 (d, ()) with
                    | Expr.load (.bits 64) _ k10 => match k10 d with
                      | Expr.load (.bits 64) _ k11 => match k11 d with
                        | Expr.let_ (ts := [.bool]) _ k12 => k12 (tum, ())
                        | e => e
                      | e => e
                    | e => e
                  | e => e
                | e => e
              | e => e
            | e => e
          | e => e
        | e => e
      | e => e
    | e => e
  | e => e

end

public section

open scoped FullArenaTactics FullDimacsBodyTactics
open FullArenaTactics FullDimacsBodyTactics

/-! ## 1. Pure BitVec, Relabeling & Witness Helpers -/

theorem bv32_tumble_lit_eq {iv l : Nat} (hiv : iv < 2 ^ 31) (hl : l < 2 ^ 32) :
    ((BitVec.ofNat 32 iv <<< (1 : Nat)) ||| (BitVec.ofNat 32 l &&& (1 : BitVec 32))) =
      BitVec.ofNat 32 (2 * iv + l % 2) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (BitVec.ofNat 32 iv <<< (1 : Nat)).toNat = 2 * iv := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.shiftLeft_eq, Nat.pow_one, Nat.mod_eq_of_lt (by omega)]; omega
  have h2 : (BitVec.ofNat 32 l &&& (1 : BitVec 32)).toNat = l % 2 := by
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl,
      Nat.mod_eq_of_lt hl, Nat.and_one_is_mod]
  rw [BitVec.toNat_or, h1, h2, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : 2 * iv + l % 2 < 2 ^ 32)]
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_or]
  cases i with
  | zero =>
    simp only [Nat.testBit_zero, show (2 * iv) % 2 = 0 from by omega]
    have hm : (2 * iv + l % 2) % 2 = l % 2 := by omega
    rw [hm]; cases Nat.mod_two_eq_zero_or_one l with
    | inl h => simp [h]
    | inr h => simp [h]
  | succ k =>
    have hlo : Nat.testBit (l % 2) (k + 1) = false := by
      rw [Nat.testBit_succ]; have : (l % 2) / 2 = 0 := by omega
      rw [this]; exact Nat.zero_testBit k
    rw [hlo, Bool.or_false, Nat.testBit_succ, Nat.testBit_succ,
      show (2 * iv) / 2 = iv from by omega, show (2 * iv + l % 2) / 2 = iv from by omega]

theorem bv32_trunc64_ofNat_lt {n : Nat} (hn : n < 2 ^ 32) :
    (BitVec.ofNat 64 n).setWidth 32 = BitVec.ofNat 32 n :=
  bv64_trunc32_ofNat hn

theorem bv64_add1_nat {n : Nat} (hn : n + 1 < 2 ^ 64) :
    BitVec.ofNat 64 n + (1 : BitVec 64) = BitVec.ofNat 64 (n + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega : n < 2 ^ 64), Nat.mod_eq_of_lt hn]

theorem bv32_add1_nat {n : Nat} (hn : n + 1 < 2 ^ 32) :
    BitVec.ofNat 32 n + (1 : BitVec 32) = BitVec.ofNat 32 (n + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega : n < 2 ^ 32), Nat.mod_eq_of_lt hn]

theorem fullIngestTum_unit_rev {revLits : List Nat} {l : Nat}
    (hcleq : CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral) =
      CNF.Clause.ofLiterals [kissatLitToDimacsLiteral l]) : revLits = [l] := by
  have hlits_eq := congrArg CNF.Clause.literals hcleq
  simp only [CNF.Clause.literals_ofLiterals] at hlits_eq
  cases hr : revLits.reverse with
  | nil => rw [hr] at hlits_eq; simp at hlits_eq
  | cons a rest_r =>
    rw [hr] at hlits_eq
    cases rest_r with
    | nil =>
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hlits_eq
      have ha := kissatLitToDimacsLiteral_inj hlits_eq; subst ha
      simpa using congrArg List.reverse hr
    | cons _ _ => simp at hlits_eq

theorem relabel_entails_add (π : Nat → Nat) (accCnf : CNF Nat) (cl : CNF.Clause Nat) :
    (CNF.relabel π (shiftDownCnf (accCnf.add cl))).Entails
      (CNF.relabel π (shiftDownCnf accCnf)) := by
  have h := shiftDownCnf_entails_add accCnf cl
  rw [CNF.entails_def] at h ⊢
  intro α hα
  rw [CNF.Sat, CNF.eval_relabel] at hα ⊢
  exact h (α ∘ π) hα

theorem relabel_entails_added (π : Nat → Nat) (accCnf : CNF Nat) (cl : CNF.Clause Nat) :
    (CNF.relabel π (shiftDownCnf (accCnf.add cl))).EntailsClause
      (CNF.Clause.relabel π (shiftDownClause cl)) := by
  have h := shiftDownCnf_entails_added accCnf cl
  rw [CNF.entails_clause_def] at h ⊢
  intro α hα
  rw [CNF.Sat, CNF.eval_relabel] at hα
  have h1 := h (α ∘ π) hα
  rw [CNF.Clause.sat_iff_exists_mem_eq] at h1 ⊢
  obtain ⟨l, hl, heq⟩ := h1
  refine ⟨(π l.1, l.2), ?_, heq⟩
  change (π l.1, l.2) ∈ (CNF.Clause.relabel π (shiftDownClause cl)).literals
  rw [CNF.Clause.literals_relabel, List.mem_map]
  exact ⟨l, hl, rfl⟩

theorem entails_cnfOfClauses_cons_tum {F0 : CNF Nat} {cl : List Nat} {F : List (List Nat)}
    (hF : F0.Entails (cnfOfClauses F)) (hcl : F0.EntailsClause (cnfClause cl)) :
    F0.Entails (cnfOfClauses (cl :: F)) := by
  rw [CNF.entails_def] at hF ⊢
  rw [CNF.entails_clause_def] at hcl
  intro α hα
  rw [cnf_sat_cnfOfClauses_iff]
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc'
  · exact hcl α hα
  · exact (cnf_sat_cnfOfClauses_iff α F).mp (hF α hα) c hc'

theorem cnfOfClauses_cons_entails_tum (cl : List Nat) (F : List (List Nat)) :
    (cnfOfClauses (cl :: F)).Entails (cnfOfClauses F) := by
  rw [CNF.entails_def]
  intro α hα
  rw [cnf_sat_cnfOfClauses_iff] at hα ⊢
  intro c hc; exact hα c (List.mem_cons_of_mem _ hc)

theorem cnfOfClauses_cons_entails_head_tum (cl : List Nat) (F : List (List Nat)) :
    (cnfOfClauses (cl :: F)).EntailsClause (cnfClause cl) := by
  rw [CNF.entails_clause_def]
  intro α hα
  rw [cnf_sat_cnfOfClauses_iff] at hα
  exact hα cl List.mem_cons_self

theorem extUnsatSound_of_entails_tum {F0 : CNF Nat} {mv : Nat} {F : List (List Nat)}
    (hb : VarsBounded mv F) (hent : F0.Entails (cnfOfClauses F)) : ExtUnsatSound F0 mv F := by
  refine ⟨hb, fun hu => ?_⟩
  rw [CNF.entails_def] at hent
  rw [CNF.unsat_iff_not_sat] at hu ⊢
  intro α hα; exact hu α (hent α hα)

theorem varsBounded_cons_tum {mv : Nat} {cl : List Nat} {F : List (List Nat)}
    (hcl : ∀ l ∈ cl, l < 2 * mv) (hb : VarsBounded mv F) : VarsBounded mv (cl :: F) := by
  intro c hc l hl
  rcases List.mem_cons.mp hc with rfl | hc'
  · exact Nat.div_lt_of_lt_mul (hcl l hl)
  · exact hb c hc' l hl

theorem nodup_of_pairwise_div2_tum {xs : List (BitVec 32)} {n : Nat} (hn : n ≤ xs.length)
    (hnd : ∀ k1 k2, k1 < n → k2 < n →
      (xs[k1]?.getD 0#32).toNat / 2 = (xs[k2]?.getD 0#32).toNat / 2 → k1 = k2) :
    ((xs.take n).map fun x => x.toNat / 2).Nodup := by
  rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
  intro i j hi hj hij
  rw [List.length_map, List.length_take] at hi hj
  have hi' : i < n := by omega
  have hj' : j < n := by omega
  simp only [List.getElem_map, List.getElem_take]
  intro heq
  have hget : (xs[i]?.getD 0#32).toNat / 2 = (xs[j]?.getD 0#32).toNat / 2 := by
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)]
    exact heq
  have hij_eq := hnd i j hi' hj' hget
  omega

theorem addUnit_preserves_witness_tum {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState}
    (hcl : k.LengthsOk c) (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {lit : BitVec 32} {flags' : List (BitVec 32)} {unassigned' unflushed' : BitVec 64}
    (_hfll : flags'.length = c.max_vars)
    (hlit : lit.toNat < 2 * k.cur_vars) (hun : k.vals[lit.toNat]?.getD 0#8 = 0#8)
    (hl0 : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat])) :
    let v := lit.toNat / 2
    FullWitnessInv c F0 F_cur
      { k with
        vals := (k.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
        flags := flags', lvl := k.lvl.set v 0#32
        rsns := k.rsns.set v 0xFFFFFFFF#32, trl := k.trl.set k.trail_end lit
        trail_pos := k.trail_pos.set v (BitVec.ofNat 32 k.trail_end)
        trail_end := k.trail_end + 1
        unassigned := unassigned', unflushed := unflushed' } := by
  intro v
  let k' : FullCoreState :=
    { k with
      vals := (k.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 0xFF#8
      flags := flags', lvl := k.lvl.set v 0#32
      rsns := k.rsns.set v 0xFFFFFFFF#32, trl := k.trl.set k.trail_end lit
      trail_pos := k.trail_pos.set v (BitVec.ofNat 32 k.trail_end)
      trail_end := k.trail_end + 1
      unassigned := unassigned', unflushed := unflushed' }
  have hcv' : k'.cur_vars = k.cur_vars := rfl
  have hte' : k'.trail_end = k.trail_end + 1 := rfl
  have hclv' : k'.cur_level = k.cur_level := rfl
  have hv_lt : v < k.cur_vars := Nat.div_lt_of_lt_mul hlit
  have hv_mv : v < c.max_vars := Nat.lt_of_lt_of_le hv_lt hcl.cur_vars_le
  have hcv_mv : k.cur_vars ≤ c.max_vars := hcl.cur_vars_le
  have hlit_neg : lit.toNat ^^^ 1 < 2 * k.cur_vars := litNeg_lt_two_mul hlit
  have hte_lt : k.trail_end < k.cur_vars := hw.trail_end_lt_of_unassigned hlit hun
  have hte_mv : k.trail_end < c.max_vars := Nat.lt_of_lt_of_le hte_lt hcv_mv
  have hte_lt32 : k.trail_end < 2 ^ 32 := by
    have := c.hmaxv; unfold dimacsBound at this; omega
  have hne_lit : lit.toNat ^^^ 1 ≠ lit.toNat := litNeg_ne_self lit.toNat
  have hnot_var : ∀ i < k.trail_end, (k.trl[i]?.getD 0#32).toNat / 2 ≠ v :=
    (hw.vals_zero_iff hlit).mp hun
  have hvals_get : ∀ l < 2 * k.cur_vars,
      k'.vals[l]?.getD 0#8 =
        if l = lit.toNat ^^^ 1 then 0xFF#8
        else if l = lit.toNat then 1#8
        else k.vals[l]?.getD 0#8 := fun l hl => by
    have hl1 : lit.toNat < k.vals.length := by rw [hcl.vals_len]; omega
    have hl2 : lit.toNat ^^^ 1 < (k.vals.set lit.toNat 1#8).length := by
      rw [List.length_set, hcl.vals_len]; omega
    by_cases hneg : l = lit.toNat ^^^ 1
    · subst hneg; dsimp only [k']; rw [List.getElem?_set_self hl2]; simp
    · dsimp only [k']; rw [List.getElem?_set_ne (Ne.symm hneg)]
      by_cases hpos : l = lit.toNat
      · subst hpos; rw [List.getElem?_set_self hl1]; simp [hneg]
      · rw [List.getElem?_set_ne (Ne.symm hpos)]; simp [hneg, hpos]
  have htrl_get : ∀ i < k.trail_end + 1,
      (k'.trl[i]?.getD 0#32).toNat =
        if i = k.trail_end then lit.toNat else (k.trl[i]?.getD 0#32).toNat := fun i _ => by
    by_cases hie : i = k.trail_end
    · subst hie; simp [k', List.getElem?_set_self (by rw [hcl.trl_len]; exact hte_mv)]
    · simp [k', hie, List.getElem?_set_ne (Ne.symm hie)]
  have hlvl_get : ∀ u < c.max_vars,
      (k'.lvl[u]?.getD 0#32).toNat =
        if u = v then 0 else (k.lvl[u]?.getD 0#32).toNat := fun u _ => by
    by_cases huv : u = v
    · subst huv; simp [k', List.getElem?_set_self (by rw [hcl.lvl_len]; exact hv_mv)]
    · simp [k', huv, List.getElem?_set_ne (Ne.symm huv)]
  have hrsn_get : ∀ u < c.max_vars,
      k'.rsns[u]?.getD 0xFFFFFFFF#32 =
        if u = v then 0xFFFFFFFF#32 else k.rsns[u]?.getD 0xFFFFFFFF#32 := fun u _ => by
    by_cases huv : u = v
    · subst huv; simp [k', List.getElem?_set_self (by rw [hcl.rsns_len]; exact hv_mv)]
    · simp [k', huv, List.getElem?_set_ne (Ne.symm huv)]
  refine
    { ext_sound := hw.ext_sound
      inconsistent_sound := hw.inconsistent_sound
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
      cur_level_le := by rw [hclv', hcl0]; exact Nat.zero_le _
      trail_lits_lt := fun i hi => by
        rw [hte'] at hi; rw [hcv', htrl_get i hi]; split
        · exact hlit
        · exact hw.trail_lits_lt i (by omega)
      trail_vars_nodup := fun i j hi hj heq => by
        rw [hte'] at hi hj; rw [htrl_get i hi, htrl_get j hj] at heq
        by_cases hie : i = k.trail_end <;> by_cases hje : j = k.trail_end
        · omega
        · subst hie; simp only [↓reduceIte, hje] at heq
          exact absurd heq.symm (hnot_var j (by omega))
        · subst hje; simp only [↓reduceIte, hie] at heq
          exact absurd heq (hnot_var i (by omega))
        · simp only [hie, hje, ↓reduceIte] at heq
          exact hw.trail_vars_nodup i j (by omega) (by omega) heq
      vals_domain := fun l hl => by
        rw [hcv'] at hl; rw [hvals_get l hl]; split
        · exact Or.inr (Or.inr rfl)
        · split
          · exact Or.inr (Or.inl rfl)
          · exact hw.vals_domain l hl
      vals_true_iff := fun l hl => by
        rw [hcv'] at hl; rw [hvals_get l hl, hte']
        constructor
        · intro h1; by_cases hneg : l = lit.toNat ^^^ 1
          · simp [hneg] at h1
          · simp only [hneg, ↓reduceIte] at h1; by_cases hpos : l = lit.toNat
            · exact ⟨k.trail_end, by omega, by rw [htrl_get _ (by omega)]; simp [hpos]⟩
            · simp only [hpos, ↓reduceIte] at h1
              obtain ⟨i, hi, heq⟩ := (hw.vals_true_iff l hl).mp h1
              have hne_i : i ≠ k.trail_end := by omega
              exact ⟨i, by omega, by rw [htrl_get i (by omega)]; simp [hne_i, heq]⟩
        · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq
          by_cases hie : i = k.trail_end
          · simp only [hie, ↓reduceIte] at heq; subst heq; simp [hne_lit.symm]
          · simp only [hie, ↓reduceIte] at heq
            have hlv : l / 2 ≠ v := by rw [← heq]; exact hnot_var i (by omega)
            have h1 : l ≠ lit.toNat ^^^ 1 := fun h => hlv (by rw [h, fullInv_var_xor1])
            have h2 : l ≠ lit.toNat := fun h => hlv (by rw [h])
            simp only [h1, h2, ↓reduceIte]; exact (hw.vals_true_iff l hl).mpr ⟨i, by omega, heq⟩
      vals_false_iff := fun l hl => by
        rw [hcv'] at hl; rw [hvals_get l hl, hte']
        constructor
        · intro h1; by_cases hneg : l = lit.toNat ^^^ 1
          · refine ⟨k.trail_end, by omega, ?_⟩
            rw [htrl_get _ (by omega)]; simp [hneg]; exact (litNeg_litNeg _).symm
          · simp only [hneg, ↓reduceIte] at h1; by_cases hpos : l = lit.toNat
            · simp [hpos] at h1
            · simp only [hpos, ↓reduceIte] at h1
              obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l hl).mp h1
              have hne_i : i ≠ k.trail_end := by omega
              exact ⟨i, by omega, by rw [htrl_get i (by omega)]; simp [hne_i, heq]⟩
        · rintro ⟨i, hi, heq⟩; rw [htrl_get i hi] at heq
          by_cases hie : i = k.trail_end
          · simp only [hie, ↓reduceIte] at heq
            have hl_eq : l = lit.toNat ^^^ 1 := by
              have h := congrArg litNeg heq; have h1 : litNeg (l ^^^ 1) = l := litNeg_litNeg l
              rw [h1] at h; exact h.symm
            simp [hl_eq]
          · simp only [hie, ↓reduceIte] at heq
            have hlv : l / 2 ≠ v := by
              have h := hnot_var i (by omega); rw [heq] at h; rwa [fullInv_var_xor1] at h
            have h1 : l ≠ lit.toNat ^^^ 1 := fun h => hlv (by rw [h, fullInv_var_xor1])
            have h2 : l ≠ lit.toNat := fun h => hlv (by rw [h])
            simp only [h1, h2, ↓reduceIte]; exact (hw.vals_false_iff l hl).mpr ⟨i, by omega, heq⟩
      lvl_le := fun i hi => by
        rw [hte'] at hi; rw [hclv', hcl0, htrl_get i hi]
        by_cases hie : i = k.trail_end
        · simp only [hie, ↓reduceIte]; rw [hlvl_get v hv_mv]; simp
        · have hilt : i < k.trail_end := by omega
          simp only [hie, ↓reduceIte]
          rw [hlvl_get _ (by have := hw.trail_lits_lt i hilt; omega)]
          simp only [hnot_var i hilt, ↓reduceIte]
          have := hw.lvl_le i hilt; omega
      dec_earliest := fun i j hi hj _ hdec => by
        rw [hte'] at hi hj
        have hpos : 0 < (k'.lvl[(k'.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat := hdec.1
        have hlv_eq : (k'.lvl[(k'.trl[j]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
          rw [htrl_get j hj]
          by_cases hje : j = k.trail_end
          · simp only [hje, ↓reduceIte]; rw [hlvl_get v hv_mv]; simp
          · have hjlt : j < k.trail_end := by omega
            simp only [hje, ↓reduceIte]
            rw [hlvl_get _ (by have := hw.trail_lits_lt j hjlt; omega)]
            simp only [hnot_var j hjlt, ↓reduceIte]
            have := hw.lvl_le j hjlt; omega
        omega
      levels_inhabited := fun L hL1 hLle => by rw [hclv', hcl0] at hLle; omega
      level0_sound := fun i hi _ => by
        rw [hte'] at hi; rw [htrl_get i hi]
        by_cases hie : i = k.trail_end
        · simp only [hie, ↓reduceIte]; exact hl0
        · have hilt : i < k.trail_end := by omega
          simp only [hie, ↓reduceIte]
          exact hw.level0_sound i hilt (by have := hw.lvl_le i hilt; omega)
      trail_pos_inv := fun i hi => by
        rw [hte'] at hi; rw [htrl_get i hi]
        by_cases hie : i = k.trail_end
        · subst hie; simp only [↓reduceIte]
          change ((k'.trail_pos)[v]?.getD 0#32).toNat = k.trail_end
          rw [List.getElem?_set_self (by rw [hcl.trail_pos_len]; exact hv_mv),
            Option.getD_some, bv32_ofNat_toNat hte_lt32]
        · have hilt : i < k.trail_end := by omega
          simp only [hie, ↓reduceIte]
          change ((k'.trail_pos)[_]?.getD 0#32).toNat = i
          rw [List.getElem?_set_ne (hnot_var i hilt).symm]
          exact hw.trail_pos_inv i hilt
      level0_rsn_none := fun idx hidx _ => by
        rw [hte'] at hidx; rw [htrl_get idx hidx]
        by_cases hie : idx = k.trail_end
        · simp only [hie, ↓reduceIte]; rw [hrsn_get v hv_mv]; simp
        · have hilt : idx < k.trail_end := by omega
          simp only [hie, ↓reduceIte]
          rw [hrsn_get _ (by have := hw.trail_lits_lt idx hilt; omega)]
          simp only [hnot_var idx hilt, ↓reduceIte]
          exact hw.level0_rsn_none idx hilt (by have := hw.lvl_le idx hilt; omega)
      frame_trail_lt := fun L hL => by
        rw [hclv', hcl0] at hL; have hLz : L = 0 := by omega
        subst hLz; change (k.frame_trail[0]?.getD 0#32).toNat ≤ k'.trail_end
        rw [hte']; have := hw.frame_trail_lt 0 (by omega); omega
      frame_trail_mono := fun L1 L2 h1 h2 => by
        rw [hclv', hcl0] at h2; have h1z : L1 = 0 := by omega
        have h2z : L2 = 0 := by omega
        subst h1z h2z; exact Nat.le_refl _
      frame_trail_before_lt := fun L hL1 hLle => by rw [hclv', hcl0] at hLle; omega
      frame_dec_lt := fun L hL1 hLle => by rw [hclv', hcl0] at hLle; omega
      reason_inv := fun idx hidx hne => by
        rw [hte'] at hidx; exfalso; apply hne
        rw [htrl_get idx hidx]
        by_cases hie : idx = k.trail_end
        · simp only [hie, ↓reduceIte]; rw [hrsn_get v hv_mv]; simp
        · have hilt : idx < k.trail_end := by omega
          simp only [hie, ↓reduceIte]
          rw [hrsn_get _ (by have := hw.trail_lits_lt idx hilt; omega)]
          simp only [hnot_var idx hilt, ↓reduceIte]
          exact hw.level0_rsn_none idx hilt (by have := hw.lvl_le idx hilt; omega)
      reason_lit_mem := fun idx hidx hne => by
        rw [hte'] at hidx; exfalso; apply hne
        rw [htrl_get idx hidx]
        by_cases hie : idx = k.trail_end
        · simp only [hie, ↓reduceIte]; rw [hrsn_get v hv_mv]; simp
        · have hilt : idx < k.trail_end := by omega
          simp only [hie, ↓reduceIte]
          rw [hrsn_get _ (by have := hw.trail_lits_lt idx hilt; omega)]
          simp only [hnot_var idx hilt, ↓reduceIte]
          exact hw.level0_rsn_none idx hilt (by have := hw.lvl_le idx hilt; omega) }

/-! ## 2. Tumble Read-Loop & Prune-Loop Invariant Step Lemmas -/

theorem ingestTumReadInv_with_fd {c : FullCfg} {accCnf : CNF Nat} {s : FullState}
    {cnfBytes : List UInt8} {i0 idx tlen elen ev : Nat} {taut : Bool} {revLits : List Nat}
    {mrk' : List (BitVec 8)} {tmp' fd' : List (BitVec 32)}
    (htum : decide (c.mv < c.extend_cap) = true)
    (hc_mv : c.mv ≤ c.max_vars) (hev : ev < c.mv)
    (hun : fd'[ev]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32)
    (hri : IngestTumReadInv c accCnf s cnfBytes i0 idx tlen elen taut revLits mrk' tmp' fd') :
    let fd_n := fd'.set ev (BitVec.ofNat 32 elen)
    elen < c.mv ∧
    IngestTumReadInv c accCnf s cnfBytes i0 idx tlen (elen + 1) taut revLits mrk' tmp' fd_n := by
  intro fd_n
  rcases hri with ⟨hi0, hidx, htl, hmkl, htmpl, hfdl, hel_ge, hel_le, hti, htc, hrel_eq,
    hfd_mono, hvals_lift, hrev_lt, hrev_cov, htmp_lt, htmp_nd, hmrk_zero, hmrk_pos,
    hcov, hsub_rev, hnil_taut, hunit_r⟩
  have hmv_bd := c.hmv; unfold dimacsBound at hmv_bd
  have hlt_ec : c.mv < c.extend_cap := of_decide_eq_true htum
  have hnxt_lt : elen < c.mv := tumbleMapInv_next_lt (hti htum) hev hun
  have hfd_len_ge : c.mv ≤ fd'.length := by omega
  have hmap_eq : ∀ x ∈ revLits, tumbleLit (decide (c.mv < c.extend_cap)) fd_n x =
      tumbleLit (decide (c.mv < c.extend_cap)) fd' x := fun x hx =>
    tumbleLit_set_eq hun (fun ht => hrev_cov ht x hx)
  refine ⟨hnxt_lt, hi0, hidx, htl, hmkl, htmpl, by simp [fd_n, hfdl], by omega, by omega,
    fun ht => tumbleMapInv_set (hti ht) hev hfd_len_ge (by omega) hun,
    tumbleCovers_set htc hun,
    (cnf_relabel_tumble_set htc hun).trans hrel_eq,
    fun e he hne => by
      have hne_ev : ev ≠ e := fun heq => by
        subst heq; exact hne ((hfd_mono ev hev hne).symm.trans hun)
      rw [List.getElem?_set_ne hne_ev]; exact hfd_mono e he hne,
    fun vext hvr hunz =>
      tumbleValsRel_set_unmapped (hvals_lift vext hvr hunz)
        (tumbleUnusedZero_mono hunz hel_ge) hev hfd_len_ge hnxt_lt (by omega) hun,
    hrev_lt,
    fun ht x hx => by
      have hcovx := hrev_cov ht x hx
      have hne : ev ≠ x / 2 := fun heq => by subst heq; exact hcovx hun
      rw [List.getElem?_set_ne hne]; exact hcovx,
    htmp_lt, htmp_nd, hmrk_zero, hmrk_pos,
    fun hnt x hx => by rw [hmap_eq x hx]; exact hcov hnt x hx,
    fun k hk => by
      have hm := hsub_rev k hk
      rw [List.mem_map] at hm ⊢
      obtain ⟨x, hx, hxe⟩ := hm
      exact ⟨x, hx, (hmap_eq x hx).trans hxe⟩,
    hnil_taut,
    fun l hl => by
      obtain ⟨h1, h2, h3⟩ := hunit_r l hl
      exact ⟨h1, h2, h3.trans (hmap_eq l (by rw [hl]; exact List.mem_cons_self)).symm⟩⟩

theorem ingestTumReadInv_push {c : FullCfg} {accCnf : CNF Nat} {s : FullState}
    {cnfBytes : List UInt8} {i0 idx j tlen elen l : Nat} {taut : Bool} {revLits : List Nat}
    {mrk' : List (BitVec 8)} {tmp' fd' : List (BitVec 32)}
    (hc_mv : c.mv ≤ c.max_vars) (hi_j : i0 ≤ j) (hj : j ≤ cnfBytes.length) (htl : tlen < c.mv)
    (hl_mv : l < 2 * c.mv)
    (hl_cov : decide (c.mv < c.extend_cap) = true →
      fd'[l / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hri : IngestTumReadInv c accCnf s cnfBytes i0 idx tlen elen taut revLits mrk' tmp' fd')
    (hmiss_v : ∀ k < tlen,
      (tmp'[k]?.getD 0#32).toNat / 2 ≠ tumbleLit (decide (c.mv < c.extend_cap)) fd' l / 2) :
    let tl := tumbleLit (decide (c.mv < c.extend_cap)) fd' l
    IngestTumReadInv c accCnf s cnfBytes i0 j (tlen + 1) elen taut (l :: revLits)
      (mrk'.set (tl / 2) (BitVec.ofNat 8 (tl % 2 + 1)))
      (tmp'.set tlen (BitVec.ofNat 32 tl)) fd' := by
  intro tl
  rcases hri with ⟨_, _, _, hmkl, htmpl, hfdl, hel_ge, hel_le, hti, htc, hrel_eq,
    hfd_mono, hvals_lift, hrev_lt, hrev_cov, htmp_lt, htmp_nd, hmrk_zero, hmrk_pos,
    hcov, hsub_rev, hnil_taut, _⟩
  have hmv_bd := c.hmv; unfold dimacsBound at hmv_bd
  have htl_mv : tl < 2 * c.mv := tumbleLit_lt hti hl_mv hl_cov
  have htl32 : tl < 2 ^ 32 := by omega
  have hn_lt : tlen < tmp'.length := by rw [htmpl]; omega
  have hm_lt : tl / 2 < mrk'.length := by rw [hmkl]; omega
  refine ⟨hi_j, hj, by omega, by simp [hmkl], by simp [htmpl], hfdl, hel_ge, hel_le,
    hti, htc, hrel_eq, hfd_mono, hvals_lift,
    (fun x hx => (List.mem_cons.mp hx).elim (fun h => h ▸ hl_mv) (hrev_lt x)),
    (fun ht x hx => (List.mem_cons.mp hx).elim (fun h => h ▸ hl_cov ht) (hrev_cov ht x)),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk; by_cases hkt : k = tlen
    · subst k; simp [List.getElem?_set_self hn_lt, bv32_ofNat_toNat htl32, htl_mv]
    · simp [List.getElem?_set_ne (Ne.symm hkt), htmp_lt k (by omega)]
  · intro k1 k2 h1 h2 heq; by_cases hk1 : k1 = tlen <;> by_cases hk2 : k2 = tlen
    · omega
    · subst hk1; simp [List.getElem?_set_self hn_lt, List.getElem?_set_ne (Ne.symm hk2),
        bv32_ofNat_toNat htl32] at heq; exact absurd heq.symm (hmiss_v k2 (by omega))
    · subst hk2; simp [List.getElem?_set_self hn_lt, List.getElem?_set_ne (Ne.symm hk1),
        bv32_ofNat_toNat htl32] at heq; exact absurd heq (hmiss_v k1 (by omega))
    · simp [List.getElem?_set_ne (Ne.symm hk1), List.getElem?_set_ne (Ne.symm hk2)] at heq
      exact htmp_nd k1 k2 (by omega) (by omega) heq
  · intro v hv hmiss
    have hne : v ≠ tl / 2 := by
      have h := hmiss tlen (by omega)
      simp [List.getElem?_set_self hn_lt, bv32_ofNat_toNat htl32] at h; exact Ne.symm h
    rw [List.getElem?_set_ne (Ne.symm hne)]
    exact hmrk_zero v hv fun k hk => by
      have h := hmiss k (by omega); simpa [List.getElem?_set_ne (by omega : tlen ≠ k)] using h
  · intro k hk; by_cases hkt : k = tlen
    · subst k; simp [List.getElem?_set_self hn_lt, List.getElem?_set_self hm_lt,
        bv32_ofNat_toNat htl32]
    · have hne_k : tl / 2 ≠ (tmp'[k]?.getD 0#32).toNat / 2 := Ne.symm (hmiss_v k (by omega))
      rw [List.getElem?_set_ne (Ne.symm hkt), List.getElem?_set_ne hne_k]
      exact hmrk_pos k (by omega)
  · intro ht x hx; rcases List.mem_cons.mp hx with hxl | hx'
    · rw [hxl]
      exact ⟨tlen, by omega, by simp [List.getElem?_set_self hn_lt, bv32_ofNat_toNat htl32, tl]⟩
    · obtain ⟨k, hk, hget⟩ := hcov ht x hx'
      exact ⟨k, by omega, by simpa [List.getElem?_set_ne (by omega : tlen ≠ k)] using hget⟩
  · intro k hk; by_cases hkt : k = tlen
    · subst k
      simp only [List.getElem?_set_self hn_lt, Option.getD_some, bv32_ofNat_toNat htl32,
        List.map_cons]
      exact List.mem_cons_self
    · simp only [List.getElem?_set_ne (Ne.symm hkt), List.map_cons]
      exact List.mem_cons_of_mem tl (hsub_rev k (by omega))
  · intro hc; cases hc
  · intro l' hl'; rcases List.cons.inj hl' with ⟨hl_eq, rfl⟩
    have ht0 : tlen = 0 := by
      cases tlen with | zero => rfl | succ k => exact absurd (hsub_rev 0 (by omega)) (by simp)
    subst ht0
    refine ⟨hnil_taut rfl, rfl, ?_⟩
    rw [← hl_eq]; simp [List.getElem?_set_self hn_lt, bv32_ofNat_toNat htl32, tl]

theorem ingestTum_dup_cov {tum : Bool} {mv tlen : Nat} {tmp' fd' : List (BitVec 32)}
    {mrk' : List (BitVec 8)} {revLits : List Nat} {taut' taut_v : Bool} {l k0 : Nat}
    {mv_b : BitVec 8}
    (hmkl : mv ≤ mrk'.length) (hv_lt : tumbleLit tum fd' l / 2 < mv) (hk0 : k0 < tlen)
    (htaut' : taut' = if mv_b = BitVec.ofNat 8 (tumbleLit tum fd' l % 2 + 1) then taut_v else true)
    (hmv_b : mv_b = mrk'[tumbleLit tum fd' l / 2]'(by omega))
    (hmv_pos : mrk'[tumbleLit tum fd' l / 2]'(by omega) =
      BitVec.ofNat 8 ((tmp'[k0]?.getD 0#32).toNat % 2 + 1))
    (hcov : taut_v = false → ∀ x ∈ revLits,
      ∃ k < tlen, (tmp'[k]?.getD 0#32).toNat = tumbleLit tum fd' x)
    (hk0_v : (tmp'[k0]?.getD 0#32).toNat / 2 = tumbleLit tum fd' l / 2) :
    taut' = false → ∀ x ∈ l :: revLits,
      ∃ k < tlen, (tmp'[k]?.getD 0#32).toNat = tumbleLit tum fd' x := by
  intro hnt' x hx
  by_cases hmeq : mv_b = BitVec.ofNat 8 (tumbleLit tum fd' l % 2 + 1)
  · simp only [hmeq, ↓reduceIte] at htaut'
    rcases List.mem_cons.mp hx with rfl | hx'
    · refine ⟨k0, hk0, ?_⟩
      have h1 := hmv_pos.symm.trans (hmv_b.symm.trans hmeq)
      have hmod := congrArg BitVec.toNat h1
      simp only [BitVec.toNat_ofNat] at hmod; omega
    · exact hcov (htaut' ▸ hnt') x hx'
  · simp only [hmeq, ↓reduceIte] at htaut'; rw [htaut'] at hnt'; cases hnt'

theorem ingestTumPruneInv_push {c : FullCfg} {s : FullState}
    {tmp' tmp'' fd' : List (BitVec 32)} {revLits : List Nat} {tlen keep i : Nat} {li : BitVec 32}
    (hc_mv : c.mv ≤ c.max_vars)
    (hlt : i < tlen) (htlen_le : tlen ≤ c.mv) (htmpl : tmp'.length = c.max_vars)
    (htmp_nd : ∀ k1 k2, k1 < tlen → k2 < tlen →
      (tmp'[k1]?.getD 0#32).toNat / 2 = (tmp'[k2]?.getD 0#32).toNat / 2 → k1 = k2)
    (hli_eq : li = tmp'[i]'(by rw [htmpl]; omega)) (hli_lt : li.toNat < 2 * c.mv)
    (hlv_getD : s.core.vals[li.toNat]?.getD 0#8 = 0#8)
    (hunit0 : ∀ l, revLits = [l] →
      (tmp'[0]?.getD 0#32).toNat = tumbleLit (decide (c.mv < c.extend_cap)) fd' l)
    (hpi : IngestTumPruneInv c s tmp' fd' revLits tlen keep i tmp'') :
    IngestTumPruneInv c s tmp' fd' revLits tlen (keep + 1) (i + 1) (tmp''.set keep li) := by
  rcases hpi with ⟨hk_le, hi_le, htmp'l, htail, hkeep_un, hkeep_src, hkeep_nd, hpruned, _, _⟩
  have htmv : tlen ≤ c.max_vars := Nat.le_trans htlen_le hc_mv
  have hk_bd : keep < tmp''.length := by rw [htmp'l]; omega
  refine ⟨by omega, by omega, by simp [htmp'l], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk1 hk2; rw [List.getElem?_set_ne (by omega)]; exact htail k (by omega) hk2
  · intro k hk; by_cases hkk : k = keep
    · subst k; rw [List.getElem?_set_self hk_bd, Option.getD_some]
      exact ⟨hli_lt, hlv_getD⟩
    · rw [List.getElem?_set_ne (Ne.symm hkk)]; exact hkeep_un k (by omega)
  · intro k hk; by_cases hkk : k = keep
    · subst k; refine ⟨i, by omega, ?_⟩
      rw [List.getElem?_set_self hk_bd, List.getElem?_eq_getElem (by rw [htmpl]; omega), hli_eq]
    · rw [List.getElem?_set_ne (Ne.symm hkk)]
      obtain ⟨m, hm, hmeq⟩ := hkeep_src k (by omega)
      exact ⟨m, by omega, hmeq⟩
  · have hmiss_li : ∀ k < keep, (tmp''[k]?.getD 0#32).toNat / 2 ≠ li.toNat / 2 := by
      intro k hk heq
      obtain ⟨m, hm, hmeq⟩ := hkeep_src k hk
      rw [hmeq] at heq
      have hli_get : li.toNat = (tmp'[i]?.getD 0#32).toNat := by
        rw [List.getElem?_eq_getElem (by rw [htmpl]; omega), Option.getD_some, ← hli_eq]
      rw [hli_get] at heq
      have := htmp_nd m i (by omega) hlt heq; omega
    intro k1 k2 h1 h2 heq
    by_cases hk1 : k1 = keep <;> by_cases hk2 : k2 = keep
    · omega
    · subst hk1; rw [List.getElem?_set_self hk_bd, Option.getD_some,
        List.getElem?_set_ne (Ne.symm hk2)] at heq
      exact absurd heq.symm (hmiss_li k2 (by omega))
    · subst hk2; rw [List.getElem?_set_self hk_bd, Option.getD_some,
        List.getElem?_set_ne (Ne.symm hk1)] at heq
      exact absurd heq (hmiss_li k1 (by omega))
    · rw [List.getElem?_set_ne (Ne.symm hk1), List.getElem?_set_ne (Ne.symm hk2)] at heq
      exact hkeep_nd k1 k2 (by omega) (by omega) heq
  · intro k hk; by_cases hki : k = i
    · subst k; refine Or.inl ⟨keep, by omega, ?_⟩
      rw [List.getElem?_set_self hk_bd, List.getElem?_eq_getElem (by rw [htmpl]; omega), hli_eq]
    · rcases hpruned k (by omega) with ⟨j, hj, hjeq⟩ | hfl
      · exact Or.inl ⟨j, by omega, by rw [List.getElem?_set_ne (by omega)]; exact hjeq⟩
      · exact Or.inr hfl
  · intro l _ hrev _ hi1
    have hi0 : i = 0 := by omega
    have hk0 : keep = 0 := by omega
    subst hi0 hk0; refine ⟨rfl, ?_⟩
    rw [List.getElem?_set_self (by rw [htmp'l]; omega), Option.getD_some, hli_eq]
    simpa [List.getElem?_eq_getElem (l := tmp') (i := 0) (by rw [htmpl]; omega)] using hunit0 l hrev
  · intro l _ hrev hvf hi1
    have hi0 : i = 0 := by omega
    subst hi0; have hl0 := hunit0 l hrev
    rw [List.getElem?_eq_getElem (l := tmp') (i := 0) (by rw [htmpl]; omega), Option.getD_some,
      ← hli_eq] at hl0
    rw [← hl0] at hvf; exact absurd (hlv_getD.symm.trans hvf) (by decide)

theorem ingestTumPruneInv_skip {c : FullCfg} {s : FullState}
    {tmp' tmp'' fd' : List (BitVec 32)} {revLits : List Nat} {tlen keep i : Nat} {li : BitVec 32}
    (hc_mv : c.mv ≤ c.max_vars)
    (hlt : i < tlen) (htlen_le : tlen ≤ c.mv) (htmpl : tmp'.length = c.max_vars)
    (hli_eq : li = tmp'[i]'(by rw [htmpl]; have htmv := Nat.le_trans htlen_le hc_mv; omega))
    (hlv_ff : s.core.vals[li.toNat]?.getD 0#8 = 0xFF#8)
    (hunit0 : ∀ l, revLits = [l] →
      (tmp'[0]?.getD 0#32).toNat = tumbleLit (decide (c.mv < c.extend_cap)) fd' l)
    (hpi : IngestTumPruneInv c s tmp' fd' revLits tlen keep i tmp'') :
    IngestTumPruneInv c s tmp' fd' revLits tlen keep (i + 1) tmp'' := by
  rcases hpi with ⟨hk_le, hi_le, htmp'l, htail, hkeep_un, hkeep_src, hkeep_nd, hpruned, _, _⟩
  have htmv : tlen ≤ c.max_vars := Nat.le_trans htlen_le hc_mv
  refine ⟨by omega, by omega, htmp'l, fun k hk1 hk2 => htail k (by omega) hk2, hkeep_un,
    (fun k hk => let ⟨m, hm, hm_eq⟩ := hkeep_src k hk; ⟨m, by omega, hm_eq⟩), hkeep_nd, ?_, ?_, ?_⟩
  · intro k hk; by_cases hki : k = i
    · subst k; refine Or.inr ?_
      rw [List.getElem?_eq_getElem (i := i) (by rw [htmpl]; omega), Option.getD_some, ← hli_eq]
      exact hlv_ff
    · exact hpruned k (by omega)
  · intro l _ hrev hv0 hi1
    have hi0 : i = 0 := by omega
    subst hi0; have hl0 := hunit0 l hrev
    rw [List.getElem?_eq_getElem (l := tmp') (i := 0) (by rw [htmpl]; omega), Option.getD_some,
      ← hli_eq] at hl0
    rw [← hl0] at hv0; exact absurd (hlv_ff.symm.trans hv0) (by decide)
  · intro _ _ _ _ _; omega

theorem ingestTum_keep_entails {c : FullCfg} {F0 F1_rel : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} {tmp' tmp'' fd' : List (BitVec 32)}
    {revLits : List Nat} {tlen keep : Nat}
    (hcv : s.core.cur_vars = c.mv)
    (hw : FullWitnessInv c F0 F_cur s.core) (hcl0 : s.core.cur_level = 0)
    (htlen_le : tlen ≤ c.mv) (htmpl : tmp'.length = c.max_vars) (hc_mv : c.mv ≤ c.max_vars)
    (htmp_lt : ∀ k < tlen, (tmp'[k]?.getD 0#32).toNat < 2 * c.mv)
    (hF1_ent : F1_rel.Entails (cnfOfClauses F_cur))
    (hF1_cl : F1_rel.EntailsClause (cnfClause ((tmp'.take tlen).map BitVec.toNat)))
    (hpi : IngestTumPruneInv c s tmp' fd' revLits tlen keep tlen tmp'') :
    F1_rel.EntailsClause (cnfClause ((tmp''.take keep).map BitVec.toNat)) := by
  rcases hpi with ⟨hk_le, _, htmp'l, _, _, _, _, hpruned, _, _⟩
  refine entails_of_mem_or_false hF1_cl fun l hl => ?_
  rw [List.mem_map] at hl; obtain ⟨x, hx, rfl⟩ := hl
  rw [List.mem_iff_getElem] at hx; obtain ⟨k, hk, hxk⟩ := hx
  have hklt : k < tlen := by rw [List.length_take] at hk; omega
  rw [List.getElem_take] at hxk
  rcases hpruned k hklt with ⟨j, hj, hjeq⟩ | hfl
  · refine Or.inl (List.mem_map.mpr ⟨x, ?_, rfl⟩)
    rw [List.mem_iff_getElem]; refine ⟨j, by rw [List.length_take]; omega, ?_⟩
    rw [List.getElem_take]; rw [List.getElem?_eq_getElem (by rw [htmp'l]; omega),
      List.getElem?_eq_getElem (by rw [htmpl]; omega)] at hjeq
    exact (Option.some.inj hjeq).trans hxk
  · refine Or.inr ?_
    have hxk_get : (tmp'[k]?.getD 0#32).toNat = x.toNat := by
      rw [List.getElem?_eq_getElem (by rw [htmpl]; omega), Option.getD_some, hxk]
    rw [hxk_get] at hfl
    have hx_lt : x.toNat < 2 * s.core.cur_vars := by
      have := htmp_lt k hklt; rw [hcv, ← hxk_get]; exact this
    obtain ⟨ti, hti, htr_eq⟩ := (hw.vals_false_iff x.toNat hx_lt).mp hfl
    have hlvl0 : (s.core.lvl[(s.core.trl[ti]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = 0 := by
      have := hw.lvl_le ti hti; omega
    have hent0 := hw.level0_sound ti hti hlvl0
    have hent_F1 : F1_rel.EntailsClause
        (cnfClause [(s.core.trl[ti]?.getD 0#32).toNat]) :=
      CNF.entails_clause_trans hF1_ent hent0
    rwa [htr_eq] at hent_F1

theorem ingestTum_st3_inv {c : FullCfg} {F0 F1 : CNF Nat} {F_cur : List (List Nat)}
    {st2 st3 : FullState}
    (hinv : FullSparseInvW c F0 F_cur st2) (hent : F1.Entails (cnfOfClauses F_cur))
    (hlen3 : st3.LengthsOk c) (hmrk : st3.core.mrk = st2.core.mrk)
    (hs1 : st3 = { st2 with core := { st2.core with tmp := st3.core.tmp } }) :
    FullSparseInvW c F1 F_cur st3 := by
  obtain ⟨_, hw0, hltm0, hnd0, hext0, hdm0⟩ := hinv
  have hltm : FullLitMarksClear c st3 := by
    refine ⟨fun v hv => by rw [hmrk]; exact hltm0.1 v hv, ?_⟩
    rw [hs1]; exact hltm0.2
  have hnd : FullArenaVarsNodup st3 := by rw [hs1]; exact hnd0
  have hext_sc : FullExtScratchOk c st3 := by rw [hs1]; exact hext0
  rw [hs1] at hlen3 ⊢
  refine ⟨hlen3,
    { hw0 with
      ext_sound := extUnsatSound_of_entails_tum hw0.ext_sound.1 hent
      arena := { hw0.arena with len_ok := hw0.arena.len_ok }
      watches := hw0.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
    ?_, ?_, ?_, hdm0⟩
  · simpa [← hs1] using hltm
  · simpa [← hs1] using hnd
  · simpa [← hs1] using hext_sc

theorem tumbleValsRel_vals_of_vext_zero {tum : Bool} {mv l : Nat}
    {fd : List (BitVec 32)} {vext vint : List (BitVec 8)}
    (hrel : TumbleValsRel tum mv fd vext vint) (hl : l < 2 * mv)
    (hmap : tum = true → fd[l / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hv0 : vext[l]?.getD 0#8 = 0#8) :
    vint[tumbleLit tum fd l]?.getD 0#8 = 0#8 := by
  have h := hrel l hl
  have hnotun : ¬ (tum = true ∧ fd[l / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) := by
    rintro ⟨ht, hff⟩; exact hmap ht hff
  simp only [hnotun, ↓reduceIte] at h
  exact h.symm.trans hv0

theorem tumbleValsRel_vals_of_vext_ff {tum : Bool} {mv l : Nat}
    {fd0 fd' : List (BitVec 32)} {vext vint : List (BitVec 8)}
    (hrel0 : TumbleValsRel tum mv fd0 vext vint)
    (hmono : ∀ e < mv, fd0[e]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 →
      fd'[e]?.getD 0xFFFFFFFF#32 = fd0[e]?.getD 0xFFFFFFFF#32)
    (hl : l < 2 * mv) (hvf : vext[l]?.getD 0#8 = 0xFF#8) :
    vint[tumbleLit tum fd' l]?.getD 0#8 = 0xFF#8 := by
  have h := hrel0 l hl
  rw [hvf] at h
  have hnotun : ¬ (tum = true ∧ fd0[l / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32) := by
    rintro ⟨ht, hff⟩; simp [ht, hff] at h
  simp only [hnotun, ↓reduceIte] at h
  have hlit_eq : tumbleLit tum fd' l = tumbleLit tum fd0 l := by
    cases tum with
    | false => rfl
    | true =>
      have hne0 : fd0[l / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 :=
        fun hff => hnotun ⟨rfl, hff⟩
      unfold tumbleLit tumblePi
      simp only [↓reduceIte, hmono (l / 2) (by omega) hne0]
  rw [hlit_eq]; exact h.symm

theorem ingestTum_st2_inv {c : FullCfg} {F0 F1 : CNF Nat} {F_cur : List (List Nat)}
    {s st2 : FullState} {accCnf : CNF Nat}
    (hinv : FullSparseInvW c F0 F_cur s) (hcl0 : s.core.cur_level = 0)
    (hrel_eq : CNF.relabel (tumblePi (decide (c.mv < c.extend_cap)) st2.core.frame_dec)
        (shiftDownCnf accCnf) =
      CNF.relabel (tumblePi (decide (c.mv < c.extend_cap)) s.core.frame_dec)
        (shiftDownCnf accCnf))
    (hF0_eq : F0 = CNF.relabel (tumblePi (decide (c.mv < c.extend_cap)) s.core.frame_dec)
      (shiftDownCnf accCnf))
    (hlen2 : st2.LengthsOk c) (hmrk_clr : ∀ v < c.max_vars, st2.core.mrk[v]?.getD 0#8 = 0#8)
    (hel_le : st2.scratch.extend_len ≤ c.extend_cap)
    (hcore : st2 = { s with
      core := { s.core with d_cur := st2.core.d_cur, d_val := st2.core.d_val, mrk := st2.core.mrk,
                            tmp := st2.core.tmp, frame_dec := st2.core.frame_dec }
      scratch := { s.scratch with extend_len := st2.scratch.extend_len } })
    (hent : F1.Entails (cnfOfClauses F_cur)) :
    FullSparseInvW c F1 F_cur st2 := by
  have hinv2 : FullSparseInvW c
      (CNF.relabel (tumblePi (decide (c.mv < c.extend_cap)) st2.core.frame_dec)
        (shiftDownCnf accCnf)) F_cur st2 := by
    rw [hrel_eq, ← hF0_eq, hcore]
    exact ⟨by simpa [← hcore] using hlen2,
      { hinv.2.1 with
        arena := { hinv.2.1.arena with len_ok := hinv.2.1.arena.len_ok }
        watches := hinv.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)
        frame_dec_lt := fun L hL1 hLle => by change L ≤ s.core.cur_level at hLle; omega },
      ⟨fun v hv => by simpa [← hcore] using hmrk_clr v hv, hinv.2.2.1.2⟩,
      hinv.2.2.2.1, ⟨hinv.2.2.2.2.1.1, by simpa [← hcore] using hel_le⟩, hinv.2.2.2.2.2⟩
  exact ingestTum_st3_inv hinv2 hent hlen2 rfl rfl

theorem ingestTum_keep1_step {c : FullCfg} {F1_rel : CNF Nat} {F_cur : List (List Nat)}
    {s st_a sf : FullState} {tmp'' fd' : List (BitVec 32)} {revLits : List Nat}
    {elen : Nat} {l0 : BitVec 32} {flags' : List (BitVec 32)}
    {unass' : BitVec 64} {phases' : List (BitVec 8)}
    (hcv : st_a.core.cur_vars = c.mv) (hcl0 : st_a.core.cur_level = 0)
    (hlen_a : st_a.LengthsOk c) (hinv4 : FullSparseInvW c F1_rel F_cur st_a)
    (hF1_ent : F1_rel.Entails (cnfOfClauses F_cur))
    (htmp'l : tmp''.length = c.max_vars) (h0_lt : 0 < c.max_vars)
    (hl0_eq : l0 = tmp''[0]'(by rw [htmp'l]; exact h0_lt))
    (hl0_lt : l0.toNat < 2 * c.mv) (hl0_un : s.core.vals[l0.toNat]?.getD 0#8 = 0#8)
    (hl0_ent : F1_rel.EntailsClause (cnfClause [l0.toNat]))
    (hs_vals : st_a.core.vals = s.core.vals)
    (hfl' : flags'.length = c.max_vars) (hph' : phases'.length = c.max_vars)
    (hsf : sf = { st_a with
      core := { st_a.core with
        vals := (st_a.core.vals.set l0.toNat 1#8).set (l0.toNat ^^^ 1) 0xFF#8
        flags := flags', lvl := st_a.core.lvl.set (l0.toNat / 2) 0#32
        rsns := st_a.core.rsns.set (l0.toNat / 2) 0xFFFFFFFF#32
        trl := st_a.core.trl.set st_a.core.trail_end l0
        trail_pos := st_a.core.trail_pos.set (l0.toNat / 2) (BitVec.ofNat 32 st_a.core.trail_end)
        trail_end := st_a.core.trail_end + 1
        unassigned := unass', unflushed := st_a.core.unflushed + 1#64 }
      scratch := { st_a.scratch with phases := phases' } })
    (hti_r : TumbleInv (decide (c.mv < c.extend_cap)) c.mv elen fd')
    (hel_ge : s.scratch.extend_len ≤ elen)
    (hrev_cov : decide (c.mv < c.extend_cap) = true →
      ∀ l ∈ revLits, fd'[l / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32)
    (hvals_lift : ∀ vext, TumbleValsRel (decide (c.mv < c.extend_cap)) c.mv
        s.core.frame_dec vext s.core.vals →
      TumbleUnusedZero (decide (c.mv < c.extend_cap)) c.mv s.scratch.extend_len s.core.vals →
      TumbleValsRel (decide (c.mv < c.extend_cap)) c.mv fd' vext s.core.vals)
    (hu0 : ∀ l < 2 * c.mv, revLits = [l] → s.core.vals[tumbleLit (decide (c.mv < c.extend_cap))
        fd' l]?.getD 0#8 = 0#8 →
      1 = 1 ∧ (tmp''[0]?.getD 0#32).toNat = tumbleLit (decide (c.mv < c.extend_cap)) fd' l) :
    let F_next := [l0.toNat] :: F_cur
    sf.LengthsOk c ∧
    FullSparseInvW c F1_rel F_next sf ∧
    F1_rel.Entails (cnfOfClauses F_next) ∧
    (∀ vext l, 2 * c.mv ≤ vext.length → l < 2 * c.mv →
      TumbleValsRel (decide (c.mv < c.extend_cap)) c.mv s.core.frame_dec vext s.core.vals →
      TumbleUnusedZero (decide (c.mv < c.extend_cap)) c.mv s.scratch.extend_len s.core.vals →
      revLits = [l] → vext[l]?.getD 0#8 = 0#8 →
      TumbleValsRel (decide (c.mv < c.extend_cap)) c.mv fd'
        ((vext.set l 1#8).set (l ^^^ 1) 0xFF#8) sf.core.vals ∧
      TumbleUnusedZero (decide (c.mv < c.extend_cap)) c.mv elen sf.core.vals) := by
  subst hsf
  let F_next := [l0.toNat] :: F_cur
  have hFn_ent : F1_rel.Entails (cnfOfClauses F_next) :=
    entails_cnfOfClauses_cons_tum hF1_ent hl0_ent
  have hext_n : ExtUnsatSound F1_rel st_a.core.cur_vars F_next :=
    extUnsatSound_of_entails_tum
      (varsBounded_cons_tum (fun q hq => by
        simp only [List.mem_singleton] at hq; rw [hq, hcv]; exact hl0_lt)
        hinv4.2.1.ext_sound.1) hFn_ent
  have hw4_n : FullWitnessInv c F1_rel F_next st_a.core :=
    hinv4.2.1.replace_extSound hext_n (cnfOfClauses_cons_entails_tum _ _)
  have hte_lt := hw4_n.trail_end_lt_of_unassigned (by rw [hcv]; exact hl0_lt)
    (by rw [hs_vals]; exact hl0_un)
  have hlen_sf : FullState.LengthsOk c
      { st_a with
        core := { st_a.core with
          vals := (st_a.core.vals.set l0.toNat 1#8).set (l0.toNat ^^^ 1) 0xFF#8
          flags := flags', lvl := st_a.core.lvl.set (l0.toNat / 2) 0#32
          rsns := st_a.core.rsns.set (l0.toNat / 2) 0xFFFFFFFF#32
          trl := st_a.core.trl.set st_a.core.trail_end l0
          trail_pos := st_a.core.trail_pos.set (l0.toNat / 2) (BitVec.ofNat 32 st_a.core.trail_end)
          trail_end := st_a.core.trail_end + 1
          unassigned := unass', unflushed := st_a.core.unflushed + 1#64 }
        scratch := { st_a.scratch with phases := phases' } } :=
    ⟨{ hlen_a.core_ok with
        vals_len := by
          change ((st_a.core.vals.set l0.toNat 1#8).set (l0.toNat ^^^ 1) 0xFF#8).length =
            2 * c.max_vars
          rw [List.length_set, List.length_set]; exact hlen_a.core_ok.vals_len
        flags_len := hfl'
        lvl_len := by
          change (st_a.core.lvl.set (l0.toNat / 2) 0#32).length = c.max_vars
          rw [List.length_set]; exact hlen_a.core_ok.lvl_len
        rsns_len := by
          change (st_a.core.rsns.set (l0.toNat / 2) 0xFFFFFFFF#32).length = c.max_vars
          rw [List.length_set]; exact hlen_a.core_ok.rsns_len
        trl_len := by
          change (st_a.core.trl.set st_a.core.trail_end l0).length = c.max_vars
          rw [List.length_set]; exact hlen_a.core_ok.trl_len
        trail_pos_len := by
          change (st_a.core.trail_pos.set (l0.toNat / 2)
            (BitVec.ofNat 32 st_a.core.trail_end)).length = c.max_vars
          rw [List.length_set]; exact hlen_a.core_ok.trail_pos_len
        trail_end_le := by change st_a.core.trail_end + 1 ≤ st_a.core.cur_vars; exact hte_lt
        propagated_le := Nat.le_succ_of_le hlen_a.core_ok.propagated_le },
      { hlen_a.scratch_ok with phases_len := hph' }⟩
  have hw_sf := addUnit_preserves_witness_tum hlen_a.core_ok hw4_n hcl0 hfl'
    (unassigned' := unass') (unflushed' := st_a.core.unflushed + 1#64)
    (by rw [hcv]; exact hl0_lt) (by rw [hs_vals]; exact hl0_un)
    (cnfOfClauses_cons_entails_head_tum _ _)
  have hinv_sf : FullSparseInvW c F1_rel F_next _ :=
    ⟨hlen_sf, hw_sf, hinv4.2.2.1, hinv4.2.2.2.1, hinv4.2.2.2.2.1, hinv4.2.2.2.2.2⟩
  refine ⟨hlen_sf, hinv_sf, hFn_ent, fun vext l hvl hl hvr hunz hrev hv0 => ?_⟩
  have hmap_l : decide (c.mv < c.extend_cap) = true →
      fd'[l / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 :=
    fun ht => hrev_cov ht l (by rw [hrev]; exact List.mem_cons_self)
  have hvr' := hvals_lift vext hvr hunz
  have hs0 := tumbleValsRel_vals_of_vext_zero hvr' hl hmap_l hv0
  have ⟨_, hl0eq⟩ := hu0 l hl hrev hs0
  rw [List.getElem?_eq_getElem (i := 0) (by rw [htmp'l]; exact h0_lt), Option.getD_some, ← hl0_eq]
    at hl0eq
  have hl0eq' : l0.toNat = tumbleLit (decide (c.mv < c.extend_cap)) fd' l := hl0eq
  have htl_lt_el : decide (c.mv < c.extend_cap) = true → l0.toNat < 2 * elen := fun ht => by
    rw [hl0eq']
    have hm := hti_r ht
    rcases hm.2.2.1 (l / 2) (by omega) with hff | hlt
    · exact absurd hff (hmap_l ht)
    · unfold tumbleLit tumblePi; simp only [ht, ↓reduceIte]; omega
  refine ⟨?_, ?_⟩
  · change TumbleValsRel _ c.mv fd' ((vext.set l 1#8).set (l ^^^ 1) 0xFF#8)
      ((st_a.core.vals.set l0.toNat 1#8).set (l0.toNat ^^^ 1) 0xFF#8)
    rw [hs_vals, hl0eq']
    have hc_mv : c.mv ≤ c.max_vars := by rw [← hcv]; exact hlen_a.core_ok.cur_vars_le
    exact tumbleValsRel_assign_unit hti_r hvr' hvl
      (by rw [← hs_vals, hlen_a.core_ok.vals_len]; omega) hl hmap_l
  · change TumbleUnusedZero _ c.mv elen
      ((st_a.core.vals.set l0.toNat 1#8).set (l0.toNat ^^^ 1) 0xFF#8)
    rw [hs_vals]
    exact tumbleUnusedZero_assign (tumbleUnusedZero_mono hunz hel_ge) htl_lt_el

theorem ingestTum_keep_cl_entails {c : FullCfg} {F1_rel : CNF Nat}
    {tmp' fd' : List (BitVec 32)} {revLits : List Nat} {accCnf : CNF Nat} {tlen : Nat}
    (htlen_mv : tlen ≤ c.max_vars) (htmpl : tmp'.length = c.max_vars)
    (hF1_ent : F1_rel = CNF.relabel (tumblePi (decide (c.mv < c.extend_cap)) fd')
      (shiftDownCnf (accCnf.add
        (CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral)))))
    (hcov : ∀ l ∈ revLits, ∃ k < tlen, (tmp'[k]?.getD 0#32).toNat =
      tumbleLit (decide (c.mv < c.extend_cap)) fd' l) :
    F1_rel.EntailsClause (cnfClause ((tmp'.take tlen).map BitVec.toNat)) := by
  subst hF1_ent
  have h1 := relabel_entails_added (tumblePi (decide (c.mv < c.extend_cap)) fd') accCnf
    (CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral))
  rw [cnfClause_relabel_eq] at h1
  refine entails_of_mem_or_false h1 fun tl_x htl_x => Or.inl ?_
  rw [List.mem_map] at htl_x
  obtain ⟨l, hl, rfl⟩ := htl_x
  obtain ⟨k, hk, hget⟩ := hcov l (List.mem_reverse.mp hl)
  rw [List.mem_map]; refine ⟨tmp'[k]'(by rw [htmpl]; omega), ?_, ?_⟩
  · rw [List.mem_iff_getElem]
    exact ⟨k, by rw [List.length_take, htmpl]; omega, by rw [List.getElem_take]⟩
  · rwa [List.getElem?_eq_getElem (by rw [htmpl]; omega), Option.getD_some] at hget

theorem ingestTum_keep2_setup {c : FullCfg} {F1_rel : CNF Nat} {F_cur : List (List Nat)}
    {st_a : FullState} {tmp'' : List (BitVec 32)} {tlen keep : Nat}
    (hcv : st_a.core.cur_vars = c.mv) (hc_mv : c.mv ≤ c.max_vars)
    (hkp_le : keep ≤ tlen) (htlen_le : tlen ≤ c.mv) (htmp'l : tmp''.length = c.max_vars)
    (hkeep_un : ∀ k < keep, (tmp''[k]?.getD 0#32).toNat < 2 * c.mv ∧
      st_a.core.vals[(tmp''[k]?.getD 0#32).toNat]?.getD 0#8 = 0#8)
    (hkeep_nd : ∀ k1 k2, k1 < keep → k2 < keep →
      (tmp''[k1]?.getD 0#32).toNat / 2 = (tmp''[k2]?.getD 0#32).toNat / 2 → k1 = k2)
    (hF1_ent : F1_rel.Entails (cnfOfClauses F_cur))
    (hF1_keep : F1_rel.EntailsClause (cnfClause ((tmp''.take keep).map BitVec.toNat)))
    (hinv4 : FullSparseInvW c F1_rel F_cur st_a) :
    let clLits := (tmp''.take keep).map BitVec.toNat
    let F_next := clLits :: F_cur
    F1_rel.Entails (cnfOfClauses F_next) ∧
    FullWitnessInv c F1_rel F_next st_a.core ∧
    (∀ l ∈ clLits, l < 2 * st_a.core.cur_vars) ∧
    (clLits.map (· / 2)).Nodup ∧
    (cnfOfClauses F_next).EntailsClause (cnfClause clLits) ∧
    (∀ (k1 k2 : FullState → Prop) ( _x : Unit),
      k1 = k1 → k2 = k2 → True) := by
  intro clLits F_next
  have hlits_bd : ∀ l ∈ clLits, l < 2 * c.mv := by
    intro l hl; rw [List.mem_map] at hl; obtain ⟨x, hx, rfl⟩ := hl
    rw [List.mem_iff_getElem] at hx; obtain ⟨k, hk, hxk⟩ := hx
    rw [List.length_take] at hk; rw [List.getElem_take] at hxk
    have hlt := (hkeep_un k (by omega)).1
    rwa [List.getElem?_eq_getElem (by rw [htmp'l]; omega), Option.getD_some, hxk] at hlt
  have hcl_nd : (clLits.map (· / 2)).Nodup := by
    rw [List.map_map]
    exact nodup_of_pairwise_div2_tum
      (by rw [htmp'l]; exact Nat.le_trans hkp_le (Nat.le_trans htlen_le hc_mv)) hkeep_nd
  have hFn_ent : F1_rel.Entails (cnfOfClauses F_next) :=
    entails_cnfOfClauses_cons_tum hF1_ent hF1_keep
  have hext_n : ExtUnsatSound F1_rel st_a.core.cur_vars F_next :=
    extUnsatSound_of_entails_tum
      (varsBounded_cons_tum (fun l hl => by rw [hcv]; exact hlits_bd l hl) hinv4.2.1.ext_sound.1)
      hFn_ent
  exact ⟨hFn_ent, hinv4.2.1.replace_extSound hext_n (cnfOfClauses_cons_entails_tum _ _),
    (fun l hl => by rw [hcv]; exact hlits_bd l hl), hcl_nd,
    cnfOfClauses_cons_entails_head_tum clLits F_cur, fun _ _ _ _ _ => trivial⟩

/-! ## 3. Read-Loop Theorem (`s6a_ingest_read_loop_wp`) -/

theorem s6a_ingest_read_loop_wp (Γ : Env)
    (hLit : ∀ args m Q X, kissatNextLitSpec args m Q X →
      Γ "kissat_next_lit" [i64, i64] [i64] args m Q X)
    {c : FullCfg} {accCnf : CNF Nat} {s : FullState}
    {cnf_ptr : BitVec 64} {cnfBytes : List UInt8} {i0 : Nat} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hfit : cnf_ptr.toNat + cnfBytes.length < 2 ^ 64)
    (hi0 : i0 ≤ cnfBytes.length) (hcv : s.core.cur_vars = c.mv)
    (hdcur : s.core.d_cur = cnf_ptr + BitVec.ofNat 64 i0)
    (hti0 : TumbleInv (decide (c.mv < c.extend_cap)) c.mv s.scratch.extend_len s.core.frame_dec)
    (htc0 : TumbleCovers (decide (c.mv < c.extend_cap)) s.core.frame_dec (shiftDownCnf accCnf))
    (hlen : s.LengthsOk c) (hmrk_zero : ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8)
    (hel_le : s.scratch.extend_len ≤ c.extend_cap)
    (hm : (FullMem c s ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m)
    (hOuter : ∀ (B : Cont [i32, .bool, .bool]) (tlen_v : BitVec 32) (taut_v err_v : Bool)
        (mb : Mem 64),
      (∃ idx tlen elen revLits mrk' tmp' fd' dcur dval,
        let st := ingestTumStR s dcur dval mrk' tmp' fd' elen
        (FullMem c st ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) mb ∧
        tlen_v = BitVec.ofNat 32 tlen ∧
        IngestTumReadInv c accCnf s cnfBytes i0 idx tlen elen taut_v revLits mrk' tmp' fd' ∧
        (err_v = true → parseClause c.mv (cnfBytes.drop i0) = none) ∧
        (err_v = false → i0 < idx ∧ dcur = cnf_ptr + BitVec.ofNat 64 idx ∧
          parseClause c.mv (cnfBytes.drop i0) =
            some (CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral),
              cnfBytes.drop idx))) →
      match ingestGroupFn Val Cont c.hdr (cnf_ptr + BitVec.ofNat 64 cnfBytes.length)
          c.pTmp c.pMark c.pVals c.pFrameDec
          ((BitVec.ofNat 64 c.mv).ult (BitVec.ofNat 64 c.extend_cap)) 0#64 with
      | Expr.group (sig := [[.bits 32, .bool, .bool]]) outerBodies _ =>
        wp Γ Q X ((outerBodies (B, ())).get Member.here (tlen_v, taut_v, err_v, ())) mb
      | _ => True) :
    Func.wp Γ full_ingest_cl_tum_body (c.hdr, cnf_ptr + BitVec.ofNat 64 cnfBytes.length, ())
      m Q X := by
  let tum : Bool := decide (c.mv < c.extend_cap)
  have hmv := c.hmv; have hmaxv := c.hmaxv; have hext_bd := c.hext
  unfold dimacsBound at hmv hmaxv hext_bd
  have hcok := hlen.core_ok
  have hc_mv : c.mv ≤ c.max_vars := by rw [← hcv]; exact hcok.cur_vars_le
  have htum_ult : (BitVec.ofNat 64 c.mv).ult (BitVec.ofNat 64 c.extend_cap) = tum := by
    rw [bv_ult_eq (by omega) (by omega)]
  unfold Func.wp full_ingest_cl_tum_body
  have hm0 : (FullMem c s ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m := sep_ac hm
  c0_hsteps_nogrp
  have hst0 : ingestTumStR s (cnf_ptr + BitVec.ofNat 64 i0) s.core.d_val s.core.mrk s.core.tmp
      s.core.frame_dec s.scratch.extend_len = s := by
    cases s with
    | mk core scratch =>
      dsimp only [ingestTumStR]; dsimp only at hdcur; rw [← hdcur]
  refine wp_loop_break_group (brkTs := [i32, .bool, .bool]) (lpTs := [i32, .bool])
    (fun (tlen_v, taut_v, err_v, ()) mb => ∃ idx tlen elen revLits mrk' tmp' fd' dcur dval,
      let st := ingestTumStR s dcur dval mrk' tmp' fd' elen
      (FullMem c st ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) mb ∧
      tlen_v = BitVec.ofNat 32 tlen ∧
      IngestTumReadInv c accCnf s cnfBytes i0 idx tlen elen taut_v revLits mrk' tmp' fd' ∧
      (err_v = true → parseClause c.mv (cnfBytes.drop i0) = none) ∧
      (err_v = false → i0 < idx ∧ dcur = cnf_ptr + BitVec.ofNat 64 idx ∧
        parseClause c.mv (cnfBytes.drop i0) =
          some (CNF.Clause.ofLiterals (revLits.reverse.map kissatLitToDimacsLiteral),
            cnfBytes.drop idx)))
    (fun r (tlen_v, taut_v, ()) ml => ∃ idx tlen elen revLits mrk' tmp' fd' dval,
      let st := ingestTumStR s (cnf_ptr + BitVec.ofNat 64 idx) dval mrk' tmp' fd' elen
      (FullMem c st ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) ml ∧
      r = cnfBytes.length - idx ∧ tlen_v = BitVec.ofNat 32 tlen ∧
      IngestTumReadInv c accCnf s cnfBytes i0 idx tlen elen taut_v revLits mrk' tmp' fd' ∧
      parseClauseAux ((cnfBytes.drop idx).length + 1) c.mv
        (revLits.map kissatLitToDimacsLiteral) (cnfBytes.drop idx) =
        parseClause c.mv (cnfBytes.drop i0))
    ?_ ?_ ?_
  · rintro B ⟨tlen_v, taut_v, err_v, ⟨⟩⟩ mb hinvB
    exact hOuter B tlen_v taut_v err_v mb hinvB
  · rintro B1 L1 r ⟨tlen_v, taut_v, ⟨⟩⟩ ml hB1 ih1
      ⟨idx, tlen, elen, revLits, mrk', tmp', fd', dval, hml, rfl, rfl, hri, hpc_inv⟩
    let st := ingestTumStR s (cnf_ptr + BitVec.ofNat 64 idx) dval mrk' tmp' fd' elen
    have hri_copy := hri
    obtain ⟨hi_le, hidx, htlen_le, hmkl, htmpl, hfdl, hel_ge, hel_le, hti_r, htc_r, hrel_eq,
      hfd_mono, hvals_lift, hrev_lt, hrev_cov, htmp_lt, htmp_nd,
      hmrk_zero, hmrk_pos, hcov, hsub_rev, hnil_taut, hunit_r⟩ := hri
    p_lets
    refine wp_head_jnz_iff (b := true) (by c0_val_eq) ?_
    refine ⟨fun _ => ?_, fun h => (by cases h)⟩
    p_lets
    have hml_d : (bytes cnf_ptr cnfBytes ⋆
        dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
          (cnf_ptr + BitVec.ofNat 64 idx) dval ⋆ (FullRest c st ⋆ R)) ml :=
      sep_ac (focus_dimacs hml)
    apply wp_call_of_spec; apply hLit
    change kissatNextLitSpec (cnf_ptr + BitVec.ofNat 64 cnfBytes.length, c.hdr, ()) ml _ _
    refine ⟨cnf_ptr, BitVec.ofNat 64 c.nc, dval, c.mv, cnfBytes, idx, FullRest c st ⋆ R,
      rfl, hfit, by omega, hidx, hml_d, ?_⟩
    cases hnl : nextLitPure c.mv (cnfBytes.drop idx) with
    | err =>
      intro cur' val' m' hm'; p_lets; refine wp_head_jnz_iff (by c0_val_eq) ?_
      refine ⟨fun _ => ?_, fun h => (by cases h)⟩
      let st_d := { st with core := { st.core with d_cur := cur', d_val := val' } }
      have hm'_a : (FullMem c st_d ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m' :=
        unfocus_dimacs (R := bytes cnf_ptr cnfBytes ⋆ R) (sep_ac hm')
      p_lets
      exact hB1 (BitVec.ofNat 32 tlen, taut_v, true, ()) m'
        ⟨idx, tlen, elen, revLits, mrk', tmp', fd', cur', val', hm'_a, rfl, hri_copy,
          fun _ => by rw [← hpc_inv, parseClauseAux_eq_nextLitPure, hnl],
          fun hc => by cases hc⟩
    | endClause rest =>
      intro j m' hij hj hdrop hm'; p_lets; refine wp_head_jnz_iff (by c0_val_eq) ?_
      refine ⟨fun h => (by cases h), fun _ => ?_⟩
      p_lets; refine wp_head_jnz_iff (by c0_val_eq) ?_
      refine ⟨fun _ => ?_, fun h => (by cases h)⟩
      let st_d := { st with core := { st.core with d_cur := cnf_ptr + BitVec.ofNat 64 j,
                                                   d_val := 0#64 } }
      have hm'_a : (FullMem c st_d ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m' :=
        unfocus_dimacs (R := bytes cnf_ptr cnfBytes ⋆ R) (sep_ac hm')
      p_lets
      refine hB1 (BitVec.ofNat 32 tlen, taut_v, false, ()) m'
        ⟨j, tlen, elen, revLits, mrk', tmp', fd', cnf_ptr + BitVec.ofNat 64 j, 0#64, hm'_a, rfl,
          ⟨by omega, hj, htlen_le, hmkl, htmpl, hfdl, hel_ge, hel_le, hti_r, htc_r, hrel_eq,
            hfd_mono, hvals_lift, hrev_lt, hrev_cov, htmp_lt, htmp_nd,
            hmrk_zero, hmrk_pos, hcov, hsub_rev, hnil_taut, hunit_r⟩,
          (fun hc => by cases hc),
          fun _ => ⟨by omega, rfl, by
            rw [← hpc_inv, parseClauseAux_eq_nextLitPure, hnl, List.map_reverse, hdrop]⟩⟩
    | lit l rest =>
      intro j m' hl_mv hl_bd hij hj hdrop hm'; p_lets
      refine wp_head_jnz_iff (by c0_val_eq) ?_
      refine ⟨fun h => (by cases h), fun _ => ?_⟩
      p_lets; refine wp_head_jnz_iff (by c0_val_eq) ?_
      refine ⟨fun h => (by cases h), fun _ => ?_⟩
      let st_d := { st with core := { st.core with d_cur := cnf_ptr + BitVec.ofNat 64 j,
                                                   d_val := BitVec.ofNat 64 l } }
      have hm'_a : (FullMem c st_d ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m' :=
        unfocus_dimacs (R := bytes cnf_ptr cnfBytes ⋆ R) (sep_ac hm')
      p_lets
      refine wp_load_of (load_full_val hm'_a) ?_; p_lets
      refine wp_load_of (load_full_mv hm'_a) ?_; p_lets
      have hl32 : l < 2 ^ 32 := by omega
      have hv_lt : l / 2 < c.mv := by omega
      have hmvd : st_d.core.d_val = BitVec.ofNat 64 l := rfl
      rw [hmvd, bv64_trunc32_ofNat hl32, bv32_zext64_eq, bv32_lshr1, bv32_ofNat_toNat hl32]
      have hgd_v : (BitVec.ofNat 64 c.mv).ule (BitVec.ofNat 64 (l / 2)) =
          decide (c.mv ≤ l / 2) := bv_ule_eq (by omega) (by omega)
      refine wp_head_jnz_iff (b := false)
        (by simp only [Arg.val_var, hgd_v]; simp [hv_lt]) ?_
      refine ⟨fun h => (by cases h), fun _ => ?_⟩
      p_lets
      refine wp_join_group
        (fun (_err_t, lit_t, v_t, ()) m_t =>
          ∃ fd_t elen_t,
            let st_t := ingestTumStR s (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 l)
              mrk' tmp' fd_t elen_t
            (FullMem c st_t ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m_t ∧
            lit_t = BitVec.ofNat 32 (tumbleLit tum fd_t l) ∧
            v_t = BitVec.ofNat 32 (tumbleLit tum fd_t l / 2) ∧
            (tum = true → fd_t[l / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32) ∧
            IngestTumReadInv c accCnf s cnfBytes i0 idx tlen elen_t taut_v revLits mrk' tmp' fd_t)
        ?_ ?_
      · rintro _ ⟨_err_t, lit_t, v_t, ⟨⟩⟩ m_t
          ⟨fd_t, elen_t, hm_t, rfl, rfl, hl_cov_t, hri_t⟩
        let tl := tumbleLit tum fd_t l
        let st_t := ingestTumStR s (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 l)
          mrk' tmp' fd_t elen_t
        have hri_t_copy := hri_t
        obtain ⟨_, _, _, _, _, hfdl_t, hel_ge_t, hel_le_t, hti_t, htc_t, hrel_eq_t,
          hfd_mono_t, hvals_lift_t, _, hrev_cov_t, _, _, _, _, hcov_t, hsub_rev_t,
          _, _⟩ := hri_t
        have htl_mv : tl < 2 * c.mv := tumbleLit_lt hti_t hl_mv hl_cov_t
        have htl32 : tl < 2 ^ 32 := by omega
        have htv_lt : tl / 2 < c.mv := by omega
        have htv32 : tl / 2 < 2 ^ 32 := by omega
        p_lets
        rw [bv32_zext64_eq, bv32_ofNat_toNat htv32]
        have hmkl_t : tl / 2 < st_t.core.mrk.length := by
          dsimp [st_t, ingestTumStR]; rw [hmkl]; omega
        refine wp_load_of (load_full_mrk hmkl_t hm_t) ?_; p_lets
        let mv_b := mrk'[tl / 2]'(by rw [hmkl]; omega)
        have hmv_b_eq : st_t.core.mrk[tl / 2]'hmkl_t = mv_b := rfl
        rw [hmv_b_eq]
        have hpc_next : parseClauseAux ((cnfBytes.drop j).length + 1) c.mv
            ((l :: revLits).map kissatLitToDimacsLiteral) (cnfBytes.drop j) =
            parseClause c.mv (cnfBytes.drop i0) := by
          have hstep : parseClauseAux ((cnfBytes.drop idx).length + 1) c.mv
              (revLits.map kissatLitToDimacsLiteral) (cnfBytes.drop idx) =
              parseClauseAux (cnfBytes.drop idx).length c.mv
                ((l :: revLits).map kissatLitToDimacsLiteral) (cnfBytes.drop j) := by
            rw [parseClauseAux_eq_nextLitPure, hnl, ← hdrop]; rfl
          rw [← hpc_inv, hstep]
          exact parseClauseAux_fuel_irrel (by simp only [List.length_drop]; omega)
            (by simp only [List.length_drop]; omega)
        refine wp_join_group
          (fun (tl', taut', _err', ()) m_s =>
            ∃ tlen' mrk_n tmp_n,
              let st_n := ingestTumStR s (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 l)
                mrk_n tmp_n fd_t elen_t
              (FullMem c st_n ⋆ (bytes cnf_ptr cnfBytes ⋆ R)) m_s ∧
              tl' = BitVec.ofNat 32 tlen' ∧
              IngestTumReadInv c accCnf s cnfBytes i0 j tlen' elen_t taut' (l :: revLits)
                mrk_n tmp_n fd_t)
          (fun _ ⟨tl', taut', _err', ⟨⟩⟩ m_s ⟨tlen', mrk_n, tmp_n, hm_n, htl', hinv_n⟩ => by
            subst htl'; p_lets
            exact ih1 (cnfBytes.length - j) _ m_s (by omega)
              ⟨j, tlen', elen_t, l :: revLits, mrk_n, tmp_n, fd_t, BitVec.ofNat 64 l,
                hm_n, rfl, rfl, hinv_n, hpc_next⟩)
          (fun Js hJs => by
            p_lets; rw [wp_jnz]
            simp only [Arg.val_var, beq_iff_eq, beq_eq_false_iff_ne, ne_eq, bv8_zext32_eq_zero]
            refine ⟨fun hm0 => ?_, fun hmne0 => ?_⟩
            · have hm0' : mrk'[tl / 2]'(by rw [hmkl]; omega) = 0#8 := hm0
              have hmiss_v : ∀ k < tlen, (tmp'[k]?.getD 0#32).toNat / 2 ≠ tl / 2 := by
                intro k hk heq
                have hpos := hmrk_pos k hk
                rw [heq, List.getElem?_eq_getElem (by rw [hmkl]; omega),
                  Option.getD_some, hm0'] at hpos
                have h1 := congrArg BitVec.toNat hpos
                simp only [BitVec.toNat_ofNat] at h1; omega
              have htlen_lt : tlen < c.mv :=
                inj_lt_of_missing (fun k => (tmp'[k]?.getD 0#32).toNat / 2)
                  htmp_nd (fun k hk => by have := htmp_lt k hk; omega) htv_lt hmiss_v
              p_lets; refine wp_load_of (load_full_mv hm_t) ?_; p_lets
              rw [bv32_zext64_eq, bv32_ofNat_toNat (by omega)]
              have hgd_t : (BitVec.ofNat 64 c.mv).ule (BitVec.ofNat 64 tlen) =
                  decide (c.mv ≤ tlen) := bv_ule_eq (by omega) (by omega)
              refine wp_head_jnz_iff (b := false)
                (by simp only [Arg.val_var, hgd_t]; simp [htlen_lt]) ?_
              refine ⟨fun h => (by cases h), fun _ => ?_⟩
              p_lets
              rw [bv32_zext64_eq, bv32_ofNat_toNat htv32, bv32_ptag_ofNat htl32]
              obtain ⟨okm, hmm⟩ := store_full_mrk (i := tl / 2) (BitVec.ofNat 8 (tl % 2 + 1))
                hmkl_t hm_t
              refine ⟨okm, ?_⟩; p_lets
              rw [bv32_zext64_eq, bv32_ofNat_toNat (by omega), bv64_mul4_nat]
              have htmpl_t : tlen < ({ st_t with core := { st_t.core with
                  mrk := st_t.core.mrk.set (tl / 2)
                    (BitVec.ofNat 8 (tl % 2 + 1)) } }).core.tmp.length := by
                dsimp [st_t, ingestTumStR]; rw [htmpl]; omega
              obtain ⟨okt, hmt⟩ := store_full_tmp (i := tlen) (BitVec.ofNat 32 tl) htmpl_t hmm
              refine ⟨okt, ?_⟩; p_lets
              rw [bv32_add1_nat (by omega)]
              let mrk_n := mrk'.set (tl / 2) (BitVec.ofNat 8 (tl % 2 + 1))
              let tmp_n := tmp'.set tlen (BitVec.ofNat 32 tl)
              have heq_st : ({ st_t with core := { st_t.core with
                  mrk := st_t.core.mrk.set (tl / 2) (BitVec.ofNat 8 (tl % 2 + 1)),
                  tmp := st_t.core.tmp.set tlen (BitVec.ofNat 32 tl) } } : FullState) =
                  ingestTumStR s (cnf_ptr + BitVec.ofNat 64 j) (BitVec.ofNat 64 l) mrk_n tmp_n
                    fd_t elen_t :=
                rfl
              rw [heq_st] at hmt
              exact hJs _ _ ⟨tlen + 1, mrk_n, tmp_n, hmt, rfl,
                ingestTumReadInv_push hc_mv (by omega) hj htlen_lt hl_mv hl_cov_t hri_t_copy
                  hmiss_v⟩
            · have hex : ∃ k0 < tlen, (tmp'[k0]?.getD 0#32).toNat / 2 = tl / 2 := by
                by_cases h : ∃ k0 < tlen, (tmp'[k0]?.getD 0#32).toNat / 2 = tl / 2
                · exact h
                · exfalso
                  have h0 := hmrk_zero (tl / 2) (by omega) (fun k hk heq => h ⟨k, hk, heq⟩)
                  rw [List.getElem?_eq_getElem (by rw [hmkl]; omega),
                    Option.getD_some] at h0; exact hmne0 h0
              obtain ⟨k0, hk0, hk0_v⟩ := hex
              have hmv_pos := hmrk_pos k0 hk0
              rw [hk0_v, List.getElem?_eq_getElem (by rw [hmkl]; omega),
                Option.getD_some] at hmv_pos
              refine wp_join_group
                (fun (taut', ()) m_j =>
                  (taut' = if mv_b = BitVec.ofNat 8 (tl % 2 + 1) then taut_v else true) ∧
                  m_j = m_t)
                (fun _ ⟨taut', ⟨⟩⟩ m_j ⟨htaut', hm_j⟩ => by
                  subst m_j; p_lets
                  refine hJs _ m_t ⟨tlen, mrk', tmp', hm_t, rfl,
                    ⟨by omega, hj, htlen_le, hmkl, htmpl, hfdl_t, hel_ge_t, hel_le_t, hti_t,
                      htc_t, hrel_eq_t, hfd_mono_t, hvals_lift_t,
                      (fun x hx => (List.mem_cons.mp hx).elim (fun h => h ▸ hl_mv) (hrev_lt x)),
                      (fun ht x hx => (List.mem_cons.mp hx).elim (fun h => h ▸ hl_cov_t ht)
                        (hrev_cov_t ht x)),
                      htmp_lt, htmp_nd, hmrk_zero, hmrk_pos,
                      ingestTum_dup_cov (by rw [hmkl]; exact hc_mv) htv_lt hk0 htaut' rfl hmv_pos
                        hcov_t hk0_v,
                      (fun k hk => by
                        rw [List.map_cons]; exact List.mem_cons_of_mem tl (hsub_rev_t k hk)),
                      (fun hc => by cases hc),
                      fun l' hl' => by
                        rcases List.cons.inj hl' with ⟨_, rfl⟩
                        exact absurd (hsub_rev_t k0 hk0) (by simp)⟩⟩)
                (fun Jt hJt => by
                  p_lets; rw [wp_jnz]
                  have hptag : BitVec.setWidth 8
                      ((BitVec.ofNat 32 (tumbleLit tum fd_t l) &&& (1 : BitVec 32)) +
                        (1 : BitVec 32)) = BitVec.ofNat 8 (tl % 2 + 1) :=
                    bv32_ptag_ofNat htl32
                  simp only [Arg.val_var, hptag, bv8_zext32_bne,
                    decide_eq_true_eq, decide_eq_false_iff_not, Classical.not_not]
                  refine ⟨fun hne => hJt (true, ()) m_t ⟨by simp [hne], rfl⟩,
                    fun heq => hJt (taut_v, ()) m_t ⟨by simp [heq], rfl⟩⟩))
      · intro Jtum hJtum
        p_lets
        refine wp_head_jnz_iff (b := tum) (by simpa [Arg.val_var] using htum_ult) ?_
        refine ⟨fun htum_t => ?_, fun htum_f => ?_⟩
        · p_lets
          rw [bv32_zext64_eq, bv32_lshr1, bv32_ofNat_toNat hl32, bv64_mul4_nat]
          have hfd_bd : l / 2 < st_d.core.frame_dec.length := by
            dsimp [st_d, st, ingestTumStR]; rw [hfdl]; omega
          refine wp_load_of (load_full_frame_dec (i := l / 2) hfd_bd hm'_a) ?_; p_lets
          let iv0 := fd'[l / 2]'(by rw [hfdl]; omega)
          have hiv0_st : st_d.core.frame_dec[l / 2]'hfd_bd = iv0 := rfl
          rw [hiv0_st]
          apply wp_unroll_group
          intro Jiv hJiv
          p_lets
          refine wp_head_jnz_iff (b := decide (iv0 = 0xFFFFFFFF#32))
            (by simp only [Arg.val_var]; by_cases h : iv0 = 0xFFFFFFFF#32 <;> simp [h]) ?_
          rw [decide_eq_true_eq, decide_eq_false_iff_not]
          refine ⟨fun hiv_ff => ?_, fun hiv_ne => ?_⟩
          · have hun_ev : fd'[l / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 := by
              rw [List.getElem?_eq_getElem (by rw [hfdl]; omega), Option.getD_some]; exact hiv_ff
            obtain ⟨hnxt_lt, hri_n⟩ := ingestTumReadInv_with_fd htum_t hc_mv hv_lt hun_ev hri_copy
            p_lets
            refine wp_load_of (load_full_extend_len hm'_a) ?_; p_lets
            have hel_d : st_d.scratch.extend_len = elen := rfl
            rw [hel_d]
            refine wp_load_of (load_full_mv hm'_a) ?_; p_lets
            have hgd_nxt : (BitVec.ofNat 64 c.mv).ule (BitVec.ofNat 64 elen) =
                decide (c.mv ≤ elen) := bv_ule_eq (by omega) (by omega)
            refine wp_head_jnz_iff (b := false)
              (by simp only [Arg.val_var, hgd_nxt]; simp [hnxt_lt]) ?_
            refine ⟨fun h => (by cases h), fun _ => ?_⟩
            p_lets
            rw [bv32_trunc64_ofNat_lt (by omega), bv32_zext64_eq, bv32_lshr1,
              bv32_ofNat_toNat hl32, bv64_mul4_nat]
            obtain ⟨okfd, hmfd⟩ := store_full_frame_dec (i := l / 2) (BitVec.ofNat 32 elen)
              hfd_bd hm'_a
            refine ⟨okfd, ?_⟩; p_lets
            rw [bv64_add1_nat (by omega)]
            obtain ⟨okel, hmel⟩ := store_full_extend_len (v := elen + 1) (by omega) hmfd
            refine ⟨okel, ?_⟩; p_lets
            apply hJiv; p_lets
            let fd_n := fd'.set (l / 2) (BitVec.ofNat 32 elen)
            have hmel' : (FullMem c (ingestTumStR s (cnf_ptr + BitVec.ofNat 64 j)
                (BitVec.ofNat 64 l) mrk' tmp' fd_n (elen + 1)) ⋆
                (bytes cnf_ptr cnfBytes ⋆ R)) _ := hmel
            have htl_eq : tumbleLit tum fd_n l = 2 * elen + l % 2 := by
              unfold tumbleLit tumblePi
              rw [htum_t, List.getElem?_set_self (by rw [hfdl]; omega)]
              simp only [Option.getD_some, ↓reduceIte]
              rw [bv32_ofNat_toNat (by omega)]
            have htl_div : tumbleLit tum fd_n l / 2 = elen := by rw [htl_eq]; omega
            have hne_ff_el : fd_n[l / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
              rw [List.getElem?_set_self (by rw [hfdl]; omega), Option.getD_some]
              intro h; have := congrArg BitVec.toNat h
              rw [bv32_ofNat_toNat (by omega)] at this
              change elen = 2 ^ 32 - 1 at this; omega
            rw [bv32_tumble_lit_eq (by omega) hl32, ← htl_eq]
            exact hJtum (false, BitVec.ofNat 32 (tumbleLit tum fd_n l),
                BitVec.ofNat 32 elen, ()) _
              ⟨fd_n, elen + 1, hmel', rfl, by rw [htl_div], (fun _ => hne_ff_el), hri_n⟩
          · p_lets; apply hJiv; p_lets
            have hmap_ev : fd'[l / 2]?.getD 0xFFFFFFFF#32 ≠ 0xFFFFFFFF#32 := by
              rw [List.getElem?_eq_getElem (by rw [hfdl]; omega), Option.getD_some]; exact hiv_ne
            have hiv0_lt : iv0.toNat < c.mv := by
              have hm := hti_r htum_t
              rcases hm.2.2.1 (l / 2) hv_lt with hff | hlt
              · exact absurd hff hmap_ev
              · rw [List.getElem?_eq_getElem (by rw [hfdl]; omega), Option.getD_some] at hlt
                exact Nat.lt_of_lt_of_le hlt hm.1
            have htl_eq : tumbleLit tum fd' l = 2 * iv0.toNat + l % 2 := by
              unfold tumbleLit tumblePi
              rw [htum_t, List.getElem?_eq_getElem (by rw [hfdl]; omega)]
              simp only [Option.getD_some, ↓reduceIte]; rfl
            have htl_div : tumbleLit tum fd' l / 2 = iv0.toNat := by rw [htl_eq]; omega
            have hiv0_of : BitVec.ofNat 32 iv0.toNat = iv0 :=
              BitVec.eq_of_toNat_eq (bv32_ofNat_toNat iv0.isLt)
            rw [← hiv0_of, bv32_tumble_lit_eq (by omega) hl32, ← htl_eq]
            exact hJtum (false, BitVec.ofNat 32 (tumbleLit tum fd' l),
                BitVec.ofNat 32 iv0.toNat, ()) m'
              ⟨fd', elen, hm'_a, rfl, by rw [htl_div], (fun _ => hmap_ev), hri_copy⟩
        · p_lets
          have htl_eq : tumbleLit tum fd' l = l := by rw [htum_f]; exact tumbleLit_false fd' l
          have hv_eq : BitVec.ofNat 32 l >>> (1 : Nat) = BitVec.ofNat 32 (l / 2) := by
            apply BitVec.eq_of_toNat_eq
            rw [bv32_lshr1, bv32_ofNat_toNat hl32, bv32_ofNat_toNat (by omega)]
          rw [hv_eq]
          exact hJtum (false, BitVec.ofNat 32 l, BitVec.ofNat 32 (l / 2), ()) m'
            ⟨fd', elen, hm'_a, by rw [htl_eq], by rw [htl_eq],
              (fun ht => by rw [htum_f] at ht; cases ht), hri_copy⟩
  · intro B1 L1 _ hL1; p_lets
    exact hL1 (cnfBytes.length - i0) _ m
      ⟨i0, 0, s.scratch.extend_len, [], s.core.mrk, s.core.tmp, s.core.frame_dec, s.core.d_val,
        by rw [hst0]; exact hm0, rfl, rfl,
        ⟨Nat.le_refl _, hi0, Nat.zero_le _, hcok.mrk_len, hcok.tmp_len_arr, hcok.frame_dec_len,
          Nat.le_refl _, hel_le, hti0, htc0, rfl, fun _ _ _ => rfl,
          fun _ hvr _ => hvr,
          (fun _ h => by cases h), (fun _ _ h => by cases h),
          fun _ h => by omega, fun _ _ h => by omega,
          fun v hv _ => hmrk_zero v hv, fun _ h => by omega,
          (fun _ _ h => by cases h), (fun _ h => by omega), (fun _ => rfl),
          (fun _ h => by cases h)⟩,
        by unfold parseClause; simp⟩

end

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S6a
