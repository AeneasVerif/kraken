module

public import LeanQbe.T.Examples.Kissat.FullM5CongFix
public import LeanQbe.T.Examples.Kissat.FullM5CongBinsLemmas

/-!
# Kissat `D-Full` M5 Congruence Closure Fix Proofs — Part 1 (`Specs`, Helpers, `#1–#6`)

Defines widened `arity ≤ 31` (`sz ≤ 32`) congruence invariants (`GateAt32`, `GateSeqOk32`,
`CongHtInv32`, `WorkStepOk32`, `HashGateOk32`), all `7` `FullM5CongFix` `Spec` contracts,
pure bitmask/XOR/ITE/AND soundness lemmas, and parametric `(Γ : Env)` `Func.wp` proofs `#1–#6`:
1. `full_cong_merge` (`m5_cong_merge_wp` against exact `FullCongSpecs.fullCongMergeSpec`)
2. `full_cong_extract_ite` (`m5_cong_extract_ite_wp` against `m5CongExtractIteSpec`)
3. `full_cong_emit_xor` (`m5_cong_emit_xor_wp` against `m5CongEmitXorSpec`)
4. `full_cong_try_xor_ite` (`m5_cong_try_xor_ite_wp` against `m5CongTryXorIteSpec`)
5. `full_cong_extract` (`m5_cong_extract_wp` against `m5CongExtractSpec`)
6. `full_cong_and_match` (`m5_cong_and_match_wp` against `m5CongAndMatchSpec`)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM5CongFix

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open LeanQbe.T.Examples.Kissat.FullM3CongBva hiding
  full_cong_and_match full_cong_and_match_body full_cong_and_match_wf
  full_cong_work_step full_cong_work_step_body full_cong_work_step_wf
open Kraken.Bedrock2.Test

/-! ## 1. Widened `arity ≤ 31` (`sz ≤ 32`) Gate Invariants & `Spec` Contracts -/

section Specs

/-- Valid extracted gate (`tag=0` AND with `2 ≤ arity ≤ 31`, `tag=1` XOR, or `tag=2` ITE)
encoded in `scr` at `g`. -/
def GateAt32 (F_cur : List (List Nat)) (cur_vars : Nat) (scr : List (BitVec 32))
    (g_len g : Nat) : Prop :=
  ∃ (lhs mword : BitVec 32),
    scr[g]? = some lhs ∧ scr[g + 1]? = some mword ∧
    lhs.toNat < 2 * cur_vars ∧
    let tag := (mword >>> 28).toNat
    let arity := (mword &&& 0xFF#32).toNat
    g + 2 + arity ≤ g_len ∧ arity ≤ cur_vars ∧ arity ≤ 31 ∧
    (∀ k < arity, ∃ r : BitVec 32, scr[g + 2 + k]? = some r ∧ r.toNat < 2 * cur_vars) ∧
    ((tag = 0 ∧ 2 ≤ arity ∧
        AndGateDef (cnfOfClauses F_cur) lhs.toNat
          (((scr.drop (g + 2)).take arity).map BitVec.toNat)) ∨
     (tag = 1 ∧ arity = 2 ∧
        XorGateDef (cnfOfClauses F_cur) lhs.toNat
          (scr[g + 2]?.getD 0#32).toNat (scr[g + 3]?.getD 0#32).toNat) ∨
     (tag = 2 ∧ arity = 3 ∧
        IteGateDef (cnfOfClauses F_cur) lhs.toNat
          (scr[g + 2]?.getD 0#32).toNat (scr[g + 3]?.getD 0#32).toNat
          (scr[g + 4]?.getD 0#32).toNat))

/-- Contiguous sequence of valid `GateAt32` gates in `scr[g ..< g_len)`. -/
inductive GateSeqOk32 (F_cur : List (List Nat)) (cur_vars : Nat) (scr : List (BitVec 32))
    (g_len : Nat) : Nat → Prop where
  | done : GateSeqOk32 F_cur cur_vars scr g_len g_len
  | step {g : Nat} (hg : GateAt32 F_cur cur_vars scr g_len g) :
      GateSeqOk32 F_cur cur_vars scr g_len
        (g + 2 + ((scr[g + 1]?.getD 0#32) &&& 0xFF#32).toNat) →
      GateSeqOk32 F_cur cur_vars scr g_len g

/-- Every non-empty slot in `scr[ht_off ..< ht_off + ht_sz)` points to a valid `GateAt32`
offset in `scr0[0 ..< g_len)`. -/
def CongHtInv32 (F_cur : List (List Nat)) (cur_vars : Nat) (scr0 scr : List (BitVec 32))
    (g_len ht_off ht_sz : Nat) : Prop :=
  ∀ k < ht_sz,
    let ent := scr[ht_off + k]?.getD 0xFFFFFFFF#32
    ent = 0xFFFFFFFF#32 ∨ GateAt32 F_cur cur_vars scr0 g_len ent.toNat

/-- Work-step loop invariant for widened `FullM5CongFix.full_cong_work_step`. -/
def WorkStepOk32 (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (fuel0 : BitVec 64) (ar0 : List (BitVec 32)) (alen0 cv0 g_len ht_off ht_sz : Nat)
    (scr0 : List (BitVec 32)) (st : FullState) : Prop :=
  st.LengthsOk c ∧ FullWitnessInv c F0 F_cur st.core ∧
  FullLitMarksClear c st ∧ FullArenaVarsNodup st ∧ FullExtScratchOk c st ∧
  st.core.cur_level = 0 ∧ st.core.dense_mode ≠ 0#64 ∧
  st.core.cur_vars = cv0 ∧ st.core.fuel = fuel0 ∧
  st.core.arena = ar0 ∧ st.core.arena_len = alen0 ∧
  FullCongReprInv F_cur (2 * cv0) st.core.repr ∧
  (∀ idx < g_len, st.scratch.scratch_buf[idx]? = scr0[idx]?) ∧
  CongHtInv32 F_cur cv0 scr0 st.scratch.scratch_buf g_len ht_off ht_sz

/-- Normalized gate invariant passed into the hash-probe loop (`arity ≤ 31`, `lhs < 2 * cv0`). -/
def HashGateOk32 (F_cur : List (List Nat)) (cv0 : Nat) (lhs : BitVec 32)
    (tmps : List (BitVec 32)) (htag harity : BitVec 32) : Prop :=
  lhs.toNat < 2 * cv0 ∧ harity.toNat ≤ cv0 ∧
  (htag = 0#32 → 2 ≤ harity.toNat ∧ harity.toNat ≤ 31 ∧
    ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
      evalLitVal α lhs.toNat =
        (List.range harity.toNat).all (fun k => evalLitVal α (tmps[k]?.getD 0#32).toNat)) ∧
  (htag = 1#32 → harity = 2#32 ∧
    XorGateDef (cnfOfClauses F_cur) lhs.toNat
      (tmps[0]?.getD 0#32).toNat (tmps[1]?.getD 0#32).toNat) ∧
  (htag = 2#32 → harity = 3#32 ∧
    IteGateDef (cnfOfClauses F_cur) lhs.toNat
      (tmps[0]?.getD 0#32).toNat (tmps[1]?.getD 0#32).toNat (tmps[2]?.getD 0#32).toNat)

def m5CongExtractIteSpec : Spec [i64, i32, i32, i32, i64] [i64] :=
  fun (h, c_lit, y, t, g_len, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      FullArenaVarsNodup s ∧ s.core.cur_level = 0 ∧
      c_lit.toNat < 2 * s.core.cur_vars ∧ y.toNat < 2 * s.core.cur_vars ∧
      t.toNat < 2 * s.core.cur_vars ∧
      c_lit.toNat / 2 ≠ y.toNat / 2 ∧ c_lit.toNat / 2 ≠ t.toNat / 2 ∧
      y.toNat / 2 ≠ t.toNat / 2 ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [y.toNat, litNeg c_lit.toNat, litNeg t.toNat]) ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [litNeg y.toNat, litNeg c_lit.toNat, t.toNat]) ∧
      g_len.toNat + 5 ≤ c.scratch_cap ∧
      GateSeqOk32 F_cur s.core.cur_vars s.scratch.scratch_buf g_len.toNat 0 ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ret : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap →
        (ret = g_len ∨ ret = g_len + 5#64) →
        (∀ idx < g_len.toNat, scr'[idx]? = s.scratch.scratch_buf[idx]?) →
        GateSeqOk32 F_cur s.core.cur_vars scr' ret.toNat 0 →
        (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

def m5CongEmitXorSpec : Spec [i64, i64, i32, i32, i32] [i64] :=
  fun (scr_ptr, g_len, x0, x1, x2, ()) m Q _ =>
    ∃ (F_cur : List (List Nat)) (cur_vars : Nat) (scr : List (BitVec 32)) (R : Mem 64 → Prop),
      x0.toNat < 2 * cur_vars ∧ x1.toNat < 2 * cur_vars ∧ x2.toNat < 2 * cur_vars ∧
      2 ≤ cur_vars ∧ g_len.toNat + 4 ≤ scr.length ∧ scr.length < 2 ^ 32 ∧
      XorGateDef (cnfOfClauses F_cur) (litNeg x0.toNat) x1.toNat x2.toNat ∧
      GateSeqOk32 F_cur cur_vars scr g_len.toNat 0 ∧
      (array (t := i32) scr_ptr scr ⋆ R) m ∧
      ∀ (scr' : List (BitVec 32)) (m' : Mem 64),
        scr'.length = scr.length →
        (∀ idx < g_len.toNat, scr'[idx]? = scr[idx]?) →
        GateSeqOk32 F_cur cur_vars scr' (g_len.toNat + 4) 0 →
        (array (t := i32) scr_ptr scr' ⋆ R) m' → Q (g_len + 4#64, ()) m'

def m5CongTryXorIteSpec : Spec [i64, i32, i32, i32, i64, i64] [i64] :=
  fun (h, a, b, cl, g_len, g_cap, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      FullArenaVarsNodup s ∧ s.core.cur_level = 0 ∧
      a.toNat < 2 * s.core.cur_vars ∧ b.toNat < 2 * s.core.cur_vars ∧
      cl.toNat < 2 * s.core.cur_vars ∧
      a.toNat / 2 ≠ b.toNat / 2 ∧ a.toNat / 2 ≠ cl.toNat / 2 ∧ b.toNat / 2 ≠ cl.toNat / 2 ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat, b.toNat, cl.toNat]) ∧
      g_len.toNat + 5 ≤ g_cap.toNat ∧ g_cap.toNat ≤ c.scratch_cap ∧
      GateSeqOk32 F_cur s.core.cur_vars s.scratch.scratch_buf g_len.toNat 0 ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ret : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap →
        g_len.toNat ≤ ret.toNat → ret.toNat ≤ g_cap.toNat →
        (∀ idx < g_len.toNat, scr'[idx]? = s.scratch.scratch_buf[idx]?) →
        GateSeqOk32 F_cur s.core.cur_vars scr' ret.toNat 0 →
        (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

def m5CongExtractSpec : Spec [i64, i64, i64] [i64] :=
  fun (h, g_cap, _tick_lim, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      FullArenaVarsNodup s ∧ s.core.cur_level = 0 ∧ g_cap.toNat ≤ c.scratch_cap ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ret : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap → ret.toNat ≤ g_cap.toNat →
        GateSeqOk32 F_cur s.core.cur_vars scr' ret.toNat 0 →
        (FullMem c s' ⋆ R) m' → Q (ret, ()) m'

def m5CongAndMatchSpec : Spec [i64, i32, i32] [.bool] := fun (h, ent, ua, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (scr0 : List (BitVec 32)) (g_len : Nat) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ s.core.cur_level = 0 ∧
    FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
    g_len ≤ c.scratch_cap ∧
    (∀ idx < g_len, s.scratch.scratch_buf[idx]? = scr0[idx]?) ∧
    GateAt32 F_cur s.core.cur_vars scr0 g_len ent.toNat ∧
    (scr0[ent.toNat + 1]?.getD 0#32 >>> 28) = 0#32 ∧
    ua.toNat ≤ s.core.cur_vars ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) repr' m',
      let s' : FullState := { s with core := { s.core with repr := repr' } }
      repr'.length = 2 * c.max_vars →
      FullCongReprInv F_cur (2 * s.core.cur_vars) repr' →
      (ok = true → 2 ≤ ua.toNat ∧ ua.toNat ≤ 31 ∧
        ∀ α : Nat → Bool, (cnfOfClauses F_cur).Sat α →
          evalLitVal α (scr0[ent.toNat]?.getD 0#32).toNat =
            (List.range ua.toNat).all fun k =>
              evalLitVal α (s.core.tmp[k]?.getD 0#32).toNat) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def m5CongWorkStepSpec : Spec [i64, i64, i64, i64, i32] [i64] :=
  fun (h, g_len, ht_off, ht_sz, _cur_ep, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (scr0 : List (BitVec 32)) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
      FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧
      s.core.cur_level = 0 ∧ s.core.dense_mode ≠ 0#64 ∧
      FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
      0 < ht_sz.toNat ∧ g_len.toNat ≤ ht_off.toNat ∧ ht_off.toNat + ht_sz.toNat ≤ c.scratch_cap ∧
      GateSeqOk32 F_cur s.core.cur_vars scr0 g_len.toNat 0 ∧
      (∀ idx < g_len.toNat, s.scratch.scratch_buf[idx]? = scr0[idx]?) ∧
      CongHtInv32 F_cur s.core.cur_vars scr0 s.scratch.scratch_buf
        g_len.toNat ht_off.toNat ht_sz.toNat ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 64) s' m',
        s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
        FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
        s'.core.cur_level = 0 → s'.core.dense_mode ≠ 0#64 →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
        s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
        FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
        (∀ idx < g_len.toNat, s'.scratch.scratch_buf[idx]? = scr0[idx]?) →
        CongHtInv32 F_cur s'.core.cur_vars scr0 s'.scratch.scratch_buf
          g_len.toNat ht_off.toNat ht_sz.toNat →
        ((r &&& 3#64) = 0#64 ∨ (r &&& 3#64) = 1#64 ∨ (r &&& 3#64) = 2#64) →
        ((r &&& 3#64) = 2#64 → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

end Specs

/-! ## 2. Pure Transport, Bitmask, XOR/ITE/AND Soundness & `WorkStepOk32` Helpers -/

section Helpers

theorem fullWitnessInv_with_oom {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (oom' : BitVec 64) :
    FullWitnessInv c F0 F_cur { k with oom := oom' } :=
  { hw with
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }

theorem gateAt32_congr {F_cur : List (List Nat)} {cur_vars : Nat}
    {scr1 scr2 : List (BitVec 32)} {g_len1 g_len2 g : Nat}
    (hge : g_len1 ≤ g_len2)
    (heq : ∀ idx < g_len1, scr2[idx]? = scr1[idx]?)
    (hg : GateAt32 F_cur cur_vars scr1 g_len1 g) :
    GateAt32 F_cur cur_vars scr2 g_len2 g := by
  obtain ⟨lhs, mword, h0, h1, hlhs, hbd, hac, ha31, hrhs, hsem⟩ := hg
  have hslice : (scr2.drop (g + 2)).take (mword &&& 0xFF#32).toNat =
      (scr1.drop (g + 2)).take (mword &&& 0xFF#32).toNat := by
    have hl1 : g + 2 + (mword &&& 0xFF#32).toNat ≤ scr1.length := by
      rcases Nat.eq_zero_or_pos (mword &&& 0xFF#32).toNat with hz | hpos
      · have := (List.getElem?_eq_some_iff.mp h1).1; omega
      · obtain ⟨_, hr, _⟩ := hrhs ((mword &&& 0xFF#32).toNat - 1) (by omega)
        have := (List.getElem?_eq_some_iff.mp hr).1; omega
    have hl2 : g + 2 + (mword &&& 0xFF#32).toNat ≤ scr2.length := by
      rcases Nat.eq_zero_or_pos (mword &&& 0xFF#32).toNat with hz | hpos
      · have h1' : scr2[g + 1]? = some mword := (heq (g + 1) (by omega)).trans h1
        have := (List.getElem?_eq_some_iff.mp h1').1; omega
      · obtain ⟨r, hr, _⟩ := hrhs ((mword &&& 0xFF#32).toNat - 1) (by omega)
        have hr' : scr2[g + 2 + ((mword &&& 0xFF#32).toNat - 1)]? = some r :=
          (heq _ (by omega)).trans hr
        have := (List.getElem?_eq_some_iff.mp hr').1; omega
    apply List.ext_getElem
    · simp only [List.length_take, List.length_drop]; omega
    · intro k hk1 _
      simp only [List.length_take, List.length_drop] at hk1
      simp only [List.getElem_take, List.getElem_drop]
      have hkeq := heq (g + 2 + k) (by omega)
      rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at hkeq
      exact Option.some.inj hkeq
  refine ⟨lhs, mword, (heq g (by omega)).trans h0, (heq (g + 1) (by omega)).trans h1,
    hlhs, by omega, hac, ha31, ?_, ?_⟩
  · intro k hk; obtain ⟨r, hr, hlt⟩ := hrhs k hk
    exact ⟨r, (heq (g + 2 + k) (by omega)).trans hr, hlt⟩
  · rcases hsem with ⟨ht, ha2, hand⟩ | ⟨ht, ha2, hxor⟩ | ⟨ht, ha3, hite⟩
    · left; exact ⟨ht, ha2, hslice ▸ hand⟩
    · right; left
      rw [heq (g + 2) (by omega), heq (g + 3) (by omega)]; exact ⟨ht, ha2, hxor⟩
    · right; right
      rw [heq (g + 2) (by omega), heq (g + 3) (by omega), heq (g + 4) (by omega)]
      exact ⟨ht, ha3, hite⟩

theorem gateSeqOk32_append {F_cur : List (List Nat)} {cur_vars : Nat}
    {scr1 scr2 : List (BitVec 32)} {g_len1 g_len2 : Nat}
    (hge : g_len1 ≤ g_len2)
    (heq : ∀ idx < g_len1, scr2[idx]? = scr1[idx]?)
    (hnew : GateSeqOk32 F_cur cur_vars scr2 g_len2 g_len1) :
    ∀ {g : Nat}, GateSeqOk32 F_cur cur_vars scr1 g_len1 g →
      GateSeqOk32 F_cur cur_vars scr2 g_len2 g := by
  intro g hs; induction hs with
  | done => exact hnew
  | @step g hg _ ih =>
    have hg' := gateAt32_congr hge heq hg; obtain ⟨_, mword, _, h1, _, hbd, _⟩ := hg
    have h1' : scr2[g + 1]? = scr1[g + 1]? := heq (g + 1) (by omega)
    exact .step hg' (by simpa [h1'] using ih)

theorem gateSeqOk32_congr {F_cur : List (List Nat)} {cur_vars : Nat}
    {scr1 scr2 : List (BitVec 32)} {g_len g : Nat}
    (heq : ∀ idx < g_len, scr2[idx]? = scr1[idx]?)
    (hs : GateSeqOk32 F_cur cur_vars scr1 g_len g) :
    GateSeqOk32 F_cur cur_vars scr2 g_len g :=
  gateSeqOk32_append (Nat.le_refl _) heq .done hs

theorem gateSeqOk32_inv_lt {F_cur : List (List Nat)} {cur_vars : Nat}
    {scr : List (BitVec 32)} {g_len g : Nat}
    (hs : GateSeqOk32 F_cur cur_vars scr g_len g) (hlt : g < g_len) :
    GateAt32 F_cur cur_vars scr g_len g ∧
      GateSeqOk32 F_cur cur_vars scr g_len
        (g + 2 + ((scr[g + 1]?.getD 0#32) &&& 0xFF#32).toNat) := by
  cases hs with
  | done => omega
  | step hg hrest => exact ⟨hg, hrest⟩

private theorem testBit_false_of_lt {a b : Nat} (h : a < 2 ^ b) : a.testBit b = false := by
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt h]; rfl

theorem bv32_and_not1_toNat (x : BitVec 32) :
    (x &&& ~~~1#32).toNat = 2 * (x.toNat / 2) := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [BitVec.toNat_and, Nat.testBit_and]
  cases i with
  | zero => simp
  | succ k =>
    by_cases hk : k + 1 < 32
    · have hall : ∀ j < 32, 0 < j → (~~~1#32 : BitVec 32).toNat.testBit j = true := by decide
      rw [hall (k + 1) hk (by omega), Bool.and_true, Nat.testBit_succ, Nat.testBit_succ]
      congr 1; omega
    · have hx : x.toNat < 2 ^ (k + 1) :=
        Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) (by omega))
      have h2 : 2 * (x.toNat / 2) < 2 ^ (k + 1) := by omega
      rw [testBit_false_of_lt hx, testBit_false_of_lt h2, Bool.false_and]

private theorem bv32_even_or_bit_toNat (y b : BitVec 32) :
    ((y &&& ~~~1#32) ||| (b &&& 1#32)).toNat = 2 * (y.toNat / 2) + b.toNat % 2 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [BitVec.toNat_or, Nat.testBit_or, bv32_and_not1_toNat, BitVec.toNat_and, Nat.testBit_and]
  cases i with
  | zero =>
    have h1 : (1#32 : BitVec 32).toNat.testBit 0 = true := by decide
    rw [h1, Bool.and_true, Nat.testBit_zero, Nat.testBit_zero, Nat.testBit_zero]
    rcases Nat.mod_two_eq_zero_or_one b.toNat with hb | hb <;> simp [hb] <;> omega
  | succ k =>
    have h0 : (1#32 : BitVec 32).toNat.testBit (k + 1) = false := by
      rw [show (1#32 : BitVec 32).toNat = 1 from rfl]
      exact testBit_false_of_lt (Nat.lt_of_lt_of_le (by omega)
        (Nat.pow_le_pow_right (by omega) (by omega : 1 ≤ k + 1)))
    rw [h0, Bool.and_false, Bool.or_false, Nat.testBit_succ, Nat.testBit_succ]
    congr 1; omega

private theorem litSign_of_mod2 (n : Nat) : litSign n = decide (n % 2 = 1) := by
  unfold litSign; rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

private theorem bv32_and1_zero_or_one (x : BitVec 32) :
    (x &&& 1#32) = 0#32 ∨ (x &&& 1#32) = 1#32 := by
  have hlt : (x &&& 1#32).toNat ≤ 1 := by
    rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl]
    exact Nat.and_le_right
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hlt with h0 | h1
  · exact Or.inl (BitVec.eq_of_toNat_eq h0)
  · exact Or.inr (BitVec.eq_of_toNat_eq h1)

/-- Sign-stripping soundness for XOR gates: folding RHS polarity bits `(t0 ^ t1) & 1` onto
`lhs` while masking `t0`, `t1` positive preserves `lhs' < 2 * cur_vars` and `XorGateDef`. -/
theorem xor_sign_strip_sound {f : CNF Nat} {cur_vars : Nat} {lhs t0 t1 : BitVec 32}
    (hlhs : lhs.toNat < 2 * cur_vars) (ht0 : t0.toNat < 2 * cur_vars)
    (ht1 : t1.toNat < 2 * cur_vars)
    (hxor : XorGateDef f lhs.toNat t0.toNat t1.toNat) :
    let lhs' := lhs ^^^ ((t0 ^^^ t1) &&& 1#32)
    let r0 := t0 &&& ~~~1#32
    let r1 := t1 &&& ~~~1#32
    lhs'.toNat < 2 * cur_vars ∧ r0.toNat < 2 * cur_vars ∧ r1.toNat < 2 * cur_vars ∧
    XorGateDef f lhs'.toNat r0.toNat r1.toNat ∧ XorGateDef f lhs'.toNat r1.toNat r0.toNat := by
  intro lhs' r0 r1
  have hr0_n : r0.toNat = 2 * (t0.toNat / 2) := bv32_and_not1_toNat t0
  have hr1_n : r1.toNat = 2 * (t1.toNat / 2) := bv32_and_not1_toNat t1
  have hlt_r0 : r0.toNat < 2 * cur_vars := by omega
  have hlt_r1 : r1.toNat < 2 * cur_vars := by omega
  have hlt_lhs' : lhs'.toNat < 2 * cur_vars := by
    dsimp only [lhs']
    rcases bv32_and1_zero_or_one (t0 ^^^ t1) with h0 | h1
    · rw [h0, BitVec.xor_zero]; exact hlhs
    · rw [h1, bv32_xor1_eq_litNeg]; exact bv32_xor1_lt_even hlhs
  have hbit_eq : ((t0 ^^^ t1) &&& 1#32).toNat = (t0.toNat % 2 ^^^ t1.toNat % 2) := by
    rw [BitVec.toNat_and, BitVec.toNat_xor, show (1#32 : BitVec 32).toNat = 1 from rfl,
      show (1 : Nat) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.xor_mod_two_pow (a := t0.toNat) (b := t1.toNat) (n := 1)
  have heval_eq : ∀ α : Nat → Bool, f.Sat α →
      evalLitVal α lhs'.toNat = (evalLitVal α r0.toNat != evalLitVal α r1.toNat) := by
    intro α hα
    have hv := xorGateDef_eval hα hxor
    have ht0_e : evalLitVal α t0.toNat = (α (t0.toNat / 2) != litSign t0.toNat) := rfl
    have ht1_e : evalLitVal α t1.toNat = (α (t1.toNat / 2) != litSign t1.toNat) := rfl
    have hr0_e : evalLitVal α r0.toNat = α (t0.toNat / 2) := by
      simp [evalLitVal, litVar, litSign, hr0_n]
    have hr1_e : evalLitVal α r1.toNat = α (t1.toNat / 2) := by
      simp [evalLitVal, litVar, litSign, hr1_n]
    have hflip_e : evalLitVal α lhs'.toNat =
        (evalLitVal α lhs.toNat != (litSign t0.toNat != litSign t1.toNat)) := by
      dsimp only [lhs']
      rw [litSign_of_mod2, litSign_of_mod2]
      rcases bv32_and1_zero_or_one (t0 ^^^ t1) with h0 | h1
      · have hmod := congrArg BitVec.toNat h0
        rw [hbit_eq] at hmod
        rw [h0, BitVec.xor_zero]
        rcases Nat.mod_two_eq_zero_or_one t0.toNat with hm0 | hm0 <;>
          rcases Nat.mod_two_eq_zero_or_one t1.toNat with hm1 | hm1 <;>
          simp_all
      · have hmod := congrArg BitVec.toNat h1
        rw [hbit_eq] at hmod
        rw [h1, bv32_xor1_eq_litNeg, evalLitVal_litNeg]
        rcases Nat.mod_two_eq_zero_or_one t0.toNat with hm0 | hm0 <;>
          rcases Nat.mod_two_eq_zero_or_one t1.toNat with hm1 | hm1 <;>
          simp_all
    rw [hflip_e, hr0_e, hr1_e, hv, ht0_e, ht1_e]
    cases α (t0.toNat / 2) <;> cases α (t1.toNat / 2) <;>
      cases litSign t0.toNat <;> cases litSign t1.toNat <;> rfl
  refine ⟨hlt_lhs', hlt_r0, hlt_r1, xorGateDef_of_eval_eq heval_eq,
    xorGateDef_of_eval_eq fun α hα => by
      rw [heval_eq α hα]; cases evalLitVal α r0.toNat <;> cases evalLitVal α r1.toNat <;> rfl⟩

/-- `((y & ~1) | ((y ^ x1 ^ x2) & 1)) = y ^ ((x1 ^ x2) & 1)`. -/
private theorem bv32_emit_xor_lhs_eq (y x1 x2 : BitVec 32) :
    ((y &&& ~~~1#32) ||| (((y ^^^ x1) ^^^ x2) &&& 1#32)) =
      y ^^^ ((x1 ^^^ x2) &&& 1#32) := by
  apply BitVec.eq_of_getElem_eq; intro i hi
  simp only [BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_xor, BitVec.getElem_not]
  cases i with
  | zero =>
    have h1 : (1#32 : BitVec 32)[0] = true := by simp [BitVec.getElem_eq_testBit_toNat]
    rw [h1]
    cases y[0] <;> cases x1[0] <;> cases x2[0] <;> rfl
  | succ k =>
    have h0 : (1#32 : BitVec 32)[k + 1] = false := by
      simp only [BitVec.getElem_eq_testBit_toNat, show (1#32 : BitVec 32).toNat = 1 from rfl]
      exact testBit_false_of_lt (Nat.lt_of_lt_of_le (by omega)
        (Nat.pow_le_pow_right (by omega) (by omega : 1 ≤ k + 1)))
    rw [h0]; simp

/-- Arithmetic 32-bit bitmask testBit lemma (`2 ≤ ua ≤ 31`, zero `decide` table). -/
theorem testBit_full_mask_iff32 {ua : BitVec 32} (hlo : 2 ≤ ua.toNat) (hhi : ua.toNat ≤ 31)
    {k : Nat} (hk : k < ua.toNat) :
    (((1#32 <<< ua) - 1#32).toNat.testBit k) = true := by
  have hshl_n : (1#32 <<< ua).toNat = 2 ^ ua.toNat := by
    rw [show (1#32 <<< ua) = (1#32 <<< ua.toNat) from rfl, BitVec.toNat_shiftLeft,
      show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.shiftLeft_eq, Nat.one_mul]
    have hlt : 2 ^ ua.toNat < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) (by omega)
    exact Nat.mod_eq_of_lt hlt
  have hpos : (1#32 : BitVec 32).toNat ≤ (1#32 <<< ua).toNat := by
    rw [hshl_n]; exact Nat.one_le_two_pow
  have hsub_n : ((1#32 <<< ua) - 1#32).toNat = 2 ^ ua.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hpos), hshl_n]; rfl
  rw [hsub_n, Nat.testBit_two_pow_sub_one]; exact decide_eq_true hk

/-- Arithmetic 32-bit `mask ||| (1 <<< k)` testBit lemma (`k < 31`, zero `decide` table). -/
theorem testBit_or_shl_eq32 {mask : BitVec 32} {k : BitVec 32} (hk : k.toNat < 31)
    {b : Nat} (_hb : b < 32) :
    ((mask ||| (1#32 <<< k)).toNat.testBit b) =
      (mask.toNat.testBit b || decide (b = k.toNat)) := by
  have hshl_n : (1#32 <<< k).toNat = 2 ^ k.toNat := by
    rw [show (1#32 <<< k) = (1#32 <<< k.toNat) from rfl, BitVec.toNat_shiftLeft,
      show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))
  rw [BitVec.toNat_or, Nat.testBit_or, hshl_n, Nat.testBit_two_pow]
  congr 1; by_cases h : k.toNat = b
  · subst h; simp
  · simp [h, Ne.symm h]

/-- If an AND gate's RHS contains a literal equivalent to `¬lhs`, then `F_cur ⊨ (¬lhs)`. -/
theorem andFold_neg_lhs_entails {F_cur : List (List Nat)} {lhs0 lhs : BitVec 32}
    {rhs : List Nat} (hand : AndGateDef (cnfOfClauses F_cur) lhs0.toNat rhs)
    (hlhs_eqv : LitEquiv (cnfOfClauses F_cur) lhs0.toNat lhs.toNat)
    (hex : ∃ x ∈ rhs, LitEquiv (cnfOfClauses F_cur) x (litNeg lhs.toNat)) :
    (cnfOfClauses F_cur).EntailsClause (cnfClause [litNeg lhs.toNat]) := by
  refine entails_of_eval_mem fun α hα => ?_
  obtain ⟨x, hx, heqv⟩ := hex
  have hl0 := andGateDef_eval hα hand
  rw [litEquiv_eval hα hlhs_eqv] at hl0
  refine ⟨litNeg lhs.toNat, List.mem_cons_self .., ?_⟩
  cases hv : evalLitVal α lhs.toNat
  · rw [evalLitVal_litNeg, hv]; rfl
  · exfalso
    rw [hv] at hl0
    have hxt := List.all_eq_true.mp hl0.symm x hx
    rw [litEquiv_eval hα heqv, evalLitVal_litNeg, hv] at hxt
    cases hxt

/-- When `lhs` is assigned at level 0 in `XorGateDef F lhs t0 t1`, then `t0` and `t1` are
equivalent (if `lhs = false`) or opposite (if `lhs = true`). -/
theorem xor_lhs_const_equiv {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hcl0 : k.cur_level = 0)
    {lhs a b : Nat} (hx : XorGateDef (cnfOfClauses F_cur) lhs a b)
    (hl_lt : lhs < 2 * k.cur_vars)
    (hdom : k.vals[lhs]?.getD 0#8 = 1#8 ∨ k.vals[lhs]?.getD 0#8 = 0xFF#8) :
    LitEquiv (cnfOfClauses F_cur)
      (if k.vals[lhs]?.getD 0#8 = 1#8 then litNeg a else a) b := by
  refine litEquiv_of_eval_eq fun α hα => ?_
  have hv := xorGateDef_eval hα hx
  rcases hdom with h1 | hff
  · rw [h1, ite_eq_left rfl, evalLitVal_litNeg]
    rw [entails_eval_true (vals1_entails hw hcl0 hl_lt h1) hα] at hv
    cases ha : evalLitVal α a <;> cases hb : evalLitVal α b <;> simp_all
  · have hne : (0xFF#8 : BitVec 8) ≠ 1#8 := by decide
    rw [hff, ite_eq_right hne]
    rw [entails_neg_eval_false (valsff_entails_neg hw hcl0 hl_lt hff) hα] at hv
    cases ha : evalLitVal α a <;> cases hb : evalLitVal α b <;> simp_all

theorem workStepOk32_of_fold {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)} {alen0 cv0 g_len ht_off ht_sz : Nat}
    {scr0 : List (BitVec 32)} {st s' : FullState}
    (hok : WorkStepOk32 c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0 st)
    (hl' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hmk' : FullLitMarksClear c s') (hnd' : FullArenaVarsNodup s')
    (hext' : FullExtScratchOk c s') (hcl' : s'.core.cur_level = 0)
    (hdm' : s'.core.dense_mode ≠ 0#64) (hcv' : s'.core.cur_vars = st.core.cur_vars)
    (hfl' : s'.core.fuel = st.core.fuel) (har' : s'.core.arena = st.core.arena)
    (hal' : s'.core.arena_len = st.core.arena_len)
    (hscr' : s'.scratch.scratch_buf = st.scratch.scratch_buf)
    (hrepr' : FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr) :
    WorkStepOk32 c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0 s' :=
  ⟨hl', hw', hmk', hnd', hext', hcl', hdm', hcv'.trans hok.2.2.2.2.2.2.2.1,
   hfl'.trans hok.2.2.2.2.2.2.2.2.1, har'.trans hok.2.2.2.2.2.2.2.2.2.1,
   hal'.trans hok.2.2.2.2.2.2.2.2.2.2.1,
   by rw [hcv'.trans hok.2.2.2.2.2.2.2.1] at hrepr'; exact hrepr',
   fun idx hi => by rw [hscr']; exact hok.2.2.2.2.2.2.2.2.2.2.2.2.1 idx hi,
   by unfold CongHtInv32; rw [hscr']; exact hok.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

theorem workStepOk32_wsState {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)} {alen0 cv0 g_len ht_off ht_sz : Nat}
    {scr0 : List (BitVec 32)} {st : FullState}
    (hok : WorkStepOk32 c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0 st)
    {repr' tmp' : List (BitVec 32)}
    (hrl' : repr'.length = 2 * c.max_vars) (htl' : tmp'.length = c.max_vars)
    (hrepr' : FullCongReprInv F_cur (2 * cv0) repr') :
    WorkStepOk32 c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0
      (wsState st repr' tmp') :=
  ⟨⟨{ hok.1.core_ok with repr_len := hrl', tmp_len_arr := htl' }, hok.1.scratch_ok⟩,
   fullWitnessInv_with_tmp (fullWitnessInv_with_repr hok.2.1 repr') tmp',
   hok.2.2.1, hok.2.2.2.1, hok.2.2.2.2.1, hok.2.2.2.2.2.1, hok.2.2.2.2.2.2.1,
   hok.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.2.1,
   hok.2.2.2.2.2.2.2.2.2.2.1, hrepr',
   hok.2.2.2.2.2.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

theorem workStepOk32_with_repr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)} {alen0 cv0 g_len ht_off ht_sz : Nat}
    {scr0 : List (BitVec 32)} {st : FullState}
    (hok : WorkStepOk32 c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0 st)
    {repr' : List (BitVec 32)} (hrl' : repr'.length = 2 * c.max_vars)
    (hrepr' : FullCongReprInv F_cur (2 * cv0) repr') :
    WorkStepOk32 c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0
      { st with core := { st.core with repr := repr' } } :=
  ⟨⟨{ hok.1.core_ok with repr_len := hrl' }, hok.1.scratch_ok⟩,
   fullWitnessInv_with_repr hok.2.1 repr', hok.2.2.1, hok.2.2.2.1, hok.2.2.2.2.1,
   hok.2.2.2.2.2.1, hok.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.1,
   hok.2.2.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.2.2.1, hrepr',
   hok.2.2.2.2.2.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.2.2.2.2.2⟩

theorem ws32_ret2_q {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)} {alen0 cv0 g_len ht_off ht_sz : Nat}
    {scr0 : List (BitVec 32)} {su : FullState} {R : Mem 64 → Prop} {mu : Mem 64}
    {Q : Post [i64]} {s0 : FullState}
    (hQ : ∀ (r : BitVec 64) s' m',
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
      s'.core.cur_level = 0 → s'.core.dense_mode ≠ 0#64 →
      s'.core.cur_vars = s0.core.cur_vars → s'.core.fuel = s0.core.fuel →
      s'.core.arena = s0.core.arena → s'.core.arena_len = s0.core.arena_len →
      FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
      (∀ idx < g_len, s'.scratch.scratch_buf[idx]? = scr0[idx]?) →
      CongHtInv32 F_cur s'.core.cur_vars scr0 s'.scratch.scratch_buf g_len ht_off ht_sz →
      ((r &&& 3#64) = 0#64 ∨ (r &&& 3#64) = 1#64 ∨ (r &&& 3#64) = 2#64) →
      ((r &&& 3#64) = 2#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hcv0 : cv0 = s0.core.cur_vars) (hf0 : fuel0 = s0.core.fuel)
    (ha0 : ar0 = s0.core.arena) (hal0 : alen0 = s0.core.arena_len)
    (hoku : WorkStepOk32 c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0 su)
    (huns : F0.Unsat) (hmu : (FullMem c su ⋆ R) mu) (wk : BitVec 64) :
    Q ((wk <<< (2 : Nat)) ||| 2#64, ()) mu := by
  have hand3 := bv64_shl2_or_low2_and3 (w := wk) (by decide : (2#64 : BitVec 64).toNat < 4)
  exact hQ ((wk <<< (2 : Nat)) ||| 2#64) su mu hoku.1 hoku.2.1 hoku.2.2.1 hoku.2.2.2.1
    hoku.2.2.2.2.1 hoku.2.2.2.2.2.1 hoku.2.2.2.2.2.2.1
    (hoku.2.2.2.2.2.2.2.1.trans hcv0) (hoku.2.2.2.2.2.2.2.2.1.trans hf0)
    (hoku.2.2.2.2.2.2.2.2.2.1.trans ha0) (hoku.2.2.2.2.2.2.2.2.2.2.1.trans hal0)
    (by rw [hoku.2.2.2.2.2.2.2.1]; exact hoku.2.2.2.2.2.2.2.2.2.2.2.1)
    hoku.2.2.2.2.2.2.2.2.2.2.2.2.1
    (by rw [hoku.2.2.2.2.2.2.2.1]; exact hoku.2.2.2.2.2.2.2.2.2.2.2.2.2)
    (Or.inr (Or.inr hand3)) (fun _ => huns) hmu

theorem ws32_exit_q {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)} {alen0 cv0 g_len ht_off ht_sz : Nat}
    {scr0 : List (BitVec 32)} {ste : FullState} {R : Mem 64 → Prop} {me : Mem 64}
    {Q : Post [i64]} {s0 : FullState}
    (hQ : ∀ (r : BitVec 64) s' m',
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullLitMarksClear c s' → FullArenaVarsNodup s' → FullExtScratchOk c s' →
      s'.core.cur_level = 0 → s'.core.dense_mode ≠ 0#64 →
      s'.core.cur_vars = s0.core.cur_vars → s'.core.fuel = s0.core.fuel →
      s'.core.arena = s0.core.arena → s'.core.arena_len = s0.core.arena_len →
      FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
      (∀ idx < g_len, s'.scratch.scratch_buf[idx]? = scr0[idx]?) →
      CongHtInv32 F_cur s'.core.cur_vars scr0 s'.scratch.scratch_buf g_len ht_off ht_sz →
      ((r &&& 3#64) = 0#64 ∨ (r &&& 3#64) = 1#64 ∨ (r &&& 3#64) = 2#64) →
      ((r &&& 3#64) = 2#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hcv0 : cv0 = s0.core.cur_vars) (hf0 : fuel0 = s0.core.fuel)
    (ha0 : ar0 = s0.core.arena) (hal0 : alen0 = s0.core.arena_len)
    (hoke : WorkStepOk32 c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0 ste)
    (hme : (FullMem c ste ⋆ R) me) (ch_e : Bool) (wk_e : BitVec 64) :
    let st_v : BitVec 64 :=
      if ste.core.inconsistent ≠ 0#64 then 2#64 else if ch_e then 1#64 else 0#64
    Q ((wk_e <<< (2 : Nat)) ||| st_v, ()) me := by
  intro st_v
  have hstv_lt : st_v.toNat < 4 := by
    dsimp only [st_v]
    by_cases h1 : ste.core.inconsistent ≠ 0#64
    · simp [h1]
    · by_cases h2 : ch_e <;> simp [h1, h2]
  have hand3 := bv64_shl2_or_low2_and3 (w := wk_e) hstv_lt
  refine hQ ((wk_e <<< (2 : Nat)) ||| st_v) ste me hoke.1 hoke.2.1 hoke.2.2.1 hoke.2.2.2.1
    hoke.2.2.2.2.1 hoke.2.2.2.2.2.1 hoke.2.2.2.2.2.2.1
    (hoke.2.2.2.2.2.2.2.1.trans hcv0) (hoke.2.2.2.2.2.2.2.2.1.trans hf0)
    (hoke.2.2.2.2.2.2.2.2.2.1.trans ha0) (hoke.2.2.2.2.2.2.2.2.2.2.1.trans hal0)
    (by rw [hoke.2.2.2.2.2.2.2.1]; exact hoke.2.2.2.2.2.2.2.2.2.2.2.1)
    hoke.2.2.2.2.2.2.2.2.2.2.2.2.1
    (by rw [hoke.2.2.2.2.2.2.2.1]; exact hoke.2.2.2.2.2.2.2.2.2.2.2.2.2)
    ?_ (fun h2 => ?_) hme
  · rw [hand3]; dsimp only [st_v]
    by_cases h1 : ste.core.inconsistent ≠ 0#64
    · simp [h1]
    · by_cases h2 : ch_e <;> simp [h1, h2]
  · rw [hand3] at h2
    have hinc : ste.core.inconsistent ≠ 0#64 := by
      dsimp only [st_v] at h2
      by_cases h1 : ste.core.inconsistent ≠ 0#64
      · exact h1
      · exfalso; by_cases h3 : ch_e <;> simp [h1, h3] at h2
    exact unsat_of_inconsistent_w hoke.2.1 hinc

theorem ws32_unit_call {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)} {alen0 cv0 g_len ht_off ht_sz : Nat}
    {scr0 : List (BitVec 32)} {st : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} {lit next_ep : BitVec 32}
    (hok : WorkStepOk32 c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0 st)
    (hl : lit.toNat < 2 * cv0) (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat]))
    (hm : (FullMem c st ⋆ R) m)
    (k : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      WorkStepOk32 c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0 s' →
      s'.core.tmp = st.core.tmp → (r = 2#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    m3CongUnitFoldSpec (c.hdr, lit, next_ep, ()) m Q X :=
  ⟨c, F0, F_cur, st, R, rfl, hok.1, hok.2.1, hok.2.2.1, hok.2.2.2.1, hok.2.2.2.2.1,
   hok.2.2.2.2.2.1, hok.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.1 ▸ hok.2.2.2.2.2.2.2.2.2.2.2.1,
   hok.2.2.2.2.2.2.2.1 ▸ hl, hent, hm,
   fun r s' m' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 htmp h12 h13 _ h2u hm' =>
     k r s' m' (workStepOk32_of_fold hok h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13)
       htmp (fun h => (h2u h).2) hm'⟩

theorem ws32_unit_xor1 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)} {alen0 cv0 g_len ht_off ht_sz : Nat}
    {scr0 : List (BitVec 32)} {st : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} {lit next_ep : BitVec 32}
    (hok : WorkStepOk32 c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0 st)
    (hl : lit.toNat < 2 * cv0)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [litNeg lit.toNat]))
    (hm : (FullMem c st ⋆ R) m)
    (k : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      WorkStepOk32 c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0 s' →
      s'.core.tmp = st.core.tmp → (r = 2#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    m3CongUnitFoldSpec (c.hdr, lit ^^^ 1#32, next_ep, ()) m Q X :=
  ws32_unit_call hok (by rw [bv32_xor1_eq_litNeg]; exact bv32_xor1_lt_even hl)
    (by rw [bv32_xor1_eq_litNeg]; exact hent) hm k

theorem ws32_equiv_call {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)} {alen0 cv0 g_len ht_off ht_sz : Nat}
    {scr0 : List (BitVec 32)} {st : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} {a b next_ep : BitVec 32}
    (hok : WorkStepOk32 c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0 st)
    (ha : a.toNat < 2 * cv0) (hb : b.toNat < 2 * cv0)
    (heqv : LitEquiv (cnfOfClauses F_cur) a.toNat b.toNat) (hm : (FullMem c st ⋆ R) m)
    (k : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      WorkStepOk32 c F0 F_cur fuel0 ar0 alen0 cv0 g_len ht_off ht_sz scr0 s' →
      s'.core.tmp = st.core.tmp → (r = 2#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    m3CongEquivFoldSpec (c.hdr, a, b, next_ep, ()) m Q X :=
  ⟨c, F0, F_cur, st, R, rfl, hok.1, hok.2.1, hok.2.2.1, hok.2.2.2.1, hok.2.2.2.2.1,
   hok.2.2.2.2.2.1, hok.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.1 ▸ hok.2.2.2.2.2.2.2.2.2.2.2.1,
   hok.2.2.2.2.2.2.2.1 ▸ ha, hok.2.2.2.2.2.2.2.1 ▸ hb, heqv, hm,
   fun r s' m' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 htmp h12 h13 _ h2u hm' =>
     k r s' m' (workStepOk32_of_fold hok h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13)
       htmp h2u hm'⟩

theorem ws32_probe_insert_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {fuel0 : BitVec 64} {ar0 : List (BitVec 32)} {alen0 cv0 : Nat}
    {g_len ht_off ht_sz g : BitVec 64}
    {scr0 : List (BitVec 32)} {stp : FullState} {slot : BitVec 64}
    (hok : WorkStepOk32 c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat ht_off.toNat ht_sz.toNat
      scr0 stp)
    (hg_lt : g.toNat < g_len.toNat) (hg_le_ht : g_len.toNat ≤ ht_off.toNat)
    (hht_le : ht_off.toNat + ht_sz.toNat ≤ c.scratch_cap)
    (hslot_lt : slot.toNat < ht_sz.toNat)
    (hgat : GateAt32 F_cur cv0 scr0 g_len.toNat g.toNat) :
    let scr_ins := stp.scratch.scratch_buf.set (ht_off.toNat + slot.toNat) (g.setWidth 32)
    let stp' : FullState :=
      { stp with scratch := { stp.scratch with
        scratch_buf := scr_ins, res_sz := stp.scratch.res_sz + 1#64 } }
    WorkStepOk32 c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat ht_off.toNat ht_sz.toNat scr0 stp' := by
  intro scr_ins stp'
  have hscrl_p := hok.1.scratch_ok.scratch_buf_len
  have hlen_p' : stp'.LengthsOk c :=
    ⟨hok.1.core_ok,
     { hok.1.scratch_ok with scratch_buf_len := by rw [List.length_set]; exact hscrl_p }⟩
  have hext_p' : FullExtScratchOk c stp' := fullExtScratchOk_of_eq hok.2.2.2.2.1 rfl rfl rfl rfl
  have hpref_p := hok.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hht_p := hok.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hg_tr : (g.setWidth 32).toNat = g.toNat := by
    have hsc := c.hscr; unfold dimacsBound at hsc
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  have hpref_p' : ∀ idx < g_len.toNat, scr_ins[idx]? = scr0[idx]? := fun idx hi => by
    rw [List.getElem?_set_ne (by omega)]; exact hpref_p idx hi
  have hht_p' : CongHtInv32 F_cur cv0 scr0 scr_ins g_len.toNat ht_off.toNat ht_sz.toNat :=
    fun k' hk' => by
      by_cases hks : k' = slot.toNat
      · subst hks; right; rw [List.getElem?_set_self (by omega), Option.getD_some, hg_tr]
        exact hgat
      · rw [List.getElem?_set_ne (by omega)]; exact hht_p k' hk'
  exact ⟨hlen_p', hok.2.1, hok.2.2.1, hok.2.2.2.1, hext_p', hok.2.2.2.2.2.1, hok.2.2.2.2.2.2.1,
    hok.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.2.1,
    hok.2.2.2.2.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.2.2.2.2.1, hpref_p', hht_p'⟩

private theorem slice_pop_step {F_cur : List (List Nat)} {k : FullCoreState} {a p rem : Nat}
    (hslice : if k.dense_mode = 0#64 then WatchSliceOk F_cur k a p rem
      else DenseWatchSliceOk F_cur k a p rem) (hpos : 0 < rem) :
    ∃ w0 : BitVec 32, k.wstk[p]? = some w0 ∧
      ((w0 &&& 0x80000000#32) ≠ 0#32 ∧
        (if k.dense_mode = 0#64 then WatchSliceOk F_cur k a (p + 1) (rem - 1)
         else DenseWatchSliceOk F_cur k a (p + 1) (rem - 1)) ∨
       (w0 &&& 0x80000000#32) = 0#32 ∧ 2 ≤ rem ∧
        ∃ cr : BitVec 32, k.wstk[p + 1]? = some cr ∧ cr.toNat ∈ fullArenaClauseRefsCore k ∧
        (if k.dense_mode = 0#64 then WatchSliceOk F_cur k a (p + 2) (rem - 2)
         else DenseWatchSliceOk F_cur k a (p + 2) (rem - 2))) := by
  by_cases hdm : k.dense_mode = 0#64 <;> simp only [hdm, ↓reduceIte] at hslice ⊢
  · cases hslice with
    | empty => omega
    | bin hp hf _ _ _ hrest => exact ⟨_, hp, Or.inl ⟨hf, hrest⟩⟩
    | large hp hp1 hf _ href hrest => exact ⟨_, hp, Or.inr ⟨hf, by omega, _, hp1, href, hrest⟩⟩
  · cases hslice with
    | empty => omega
    | bin hp hf _ _ _ hrest => exact ⟨_, hp, Or.inl ⟨hf, hrest⟩⟩
    | occ hp hp1 hf _ _ href hrest => exact ⟨_, hp, Or.inr ⟨hf, by omega, _, hp1, href, hrest⟩⟩

private theorem litNeg_div2 (n : Nat) : litNeg n / 2 = n / 2 := litVar_litNeg n

private theorem bv32_ne_of_div2_ne {x y : BitVec 32} (h : x.toNat / 2 ≠ y.toNat / 2) : x ≠ y := by
  intro heq; subst heq; exact h rfl

private theorem div2_ne_of_xor1 {x y : BitVec 32} (h : x.toNat / 2 ≠ y.toNat / 2) :
    x.toNat / 2 ≠ (y ^^^ 1).toNat / 2 := by rw [bv32_xor1_litNeg, litNeg_div2]; exact h

private theorem div2_ne_of_xor1_l {x y : BitVec 32} (h : x.toNat / 2 ≠ y.toNat / 2) :
    (x ^^^ 1).toNat / 2 ≠ y.toNat / 2 := by rw [bv32_xor1_litNeg, litNeg_div2]; exact h

private theorem div2_ne_of_xor1_both {x y : BitVec 32} (h : x.toNat / 2 ≠ y.toNat / 2) :
    (x ^^^ 1).toNat / 2 ≠ (y ^^^ 1).toNat / 2 := by
  rw [bv32_xor1_litNeg, bv32_xor1_litNeg, litNeg_div2, litNeg_div2]; exact h

private theorem cur_vars_ge3_of_distinct {v0 v1 v2 n : Nat}
    (h0 : v0 < n) (h1 : v1 < n) (h2 : v2 < n)
    (h01 : v0 ≠ v1) (h02 : v0 ≠ v2) (h12 : v1 ≠ v2) : 3 ≤ n := by
  have hle := nodup_lt_length_le (n := n) (xs := [v0, v1, v2])
    (by simp [h01, h02, h12])
    (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption)
  simpa using hle

private theorem closed_cons_get {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {ts : List Ty} {b : Tup Val ts → Expr Val Cont rs} {Js : Tup Cont [ts]}
    (h : Closed Γ Q X (.cons b .nil) Js) (xs : Tup Val ts) (m : Mem 64)
    (hwp : wp Γ Q X (b xs) m) : Js.1 xs m := h.1 xs m hwp

private theorem bv64_add_n {x y : BitVec 64} (h : x.toNat + y.toNat < 2 ^ 64) :
    (x + y).toNat = x.toNat + y.toNat := Nat.mod_eq_of_lt h

private theorem ite_pick_e_ok {F_cur : List (List Nat)} {cv : Nat}
    {c_lit y l0 l1 l2 la lb lc : BitVec 32}
    (hcl : (cnfOfClauses F_cur).EntailsClause (cnfClause [l0.toNat, l1.toNat, l2.toNat]))
    (hnd : l0.toNat / 2 ≠ l1.toNat / 2 ∧ l0.toNat / 2 ≠ l2.toNat / 2 ∧
      l1.toNat / 2 ≠ l2.toNat / 2)
    (hlt : ∀ x ∈ [l0.toNat, l1.toNat, l2.toNat], x < 2 * cv)
    (h1 : la = c_lit) (h2 : lb = y ^^^ 1)
    (hcase : (la = l0 ∧ lb = l1 ∧ lc = l2) ∨ (la = l0 ∧ lb = l2 ∧ lc = l1) ∨
             (la = l1 ∧ lb = l0 ∧ lc = l2) ∨ (la = l1 ∧ lb = l2 ∧ lc = l0) ∨
             (la = l2 ∧ lb = l0 ∧ lc = l1) ∨ (la = l2 ∧ lb = l1 ∧ lc = l0)) :
    lc.toNat < 2 * cv ∧ lc.toNat / 2 ≠ c_lit.toNat / 2 ∧ lc.toNat / 2 ≠ y.toNat / 2 ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [litNeg y.toNat, c_lit.toNat, lc.toNat]) := by
  have hny : (y ^^^ 1 : BitVec 32).toNat = litNeg y.toNat := bv32_xor1_litNeg y
  have hdiv_ny : (y ^^^ 1 : BitVec 32).toNat / 2 = y.toNat / 2 := by rw [hny, litNeg_div2]
  rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    (subst h1 h2; refine ⟨hlt _ (by simp), by omega, by rw [← hdiv_ny]; omega,
      entails_perm_clause (fun x hx => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
        rw [← hny]; rcases hx with rfl | rfl | rfl <;> simp) hcl⟩)

private theorem ite_emit_gateSeq32 {F_cur : List (List Nat)} {cur_vars cap g_len : Nat}
    {scr : List (BitVec 32)} {y2 c1 t2 e2 : BitVec 32}
    (hscrl : scr.length = cap) (hg5_le : g_len + 5 ≤ cap) (hcv3 : 3 ≤ cur_vars)
    (hy2_lt : y2.toNat < 2 * cur_vars) (hc1_lt : c1.toNat < 2 * cur_vars)
    (ht2_lt : t2.toNat < 2 * cur_vars) (he2_lt : e2.toNat < 2 * cur_vars)
    (hite2 : IteGateDef (cnfOfClauses F_cur) y2.toNat c1.toNat t2.toNat e2.toNat)
    (hseq0 : GateSeqOk32 F_cur cur_vars scr g_len 0) :
    let scr5 := ((((scr.set g_len y2).set (g_len + 1) ((2#32 <<< 28) ||| 3#32)).set
      (g_len + 2) c1).set (g_len + 3) t2).set (g_len + 4) e2
    scr5.length = cap ∧ (∀ idx < g_len, scr5[idx]? = scr[idx]?) ∧
      GateSeqOk32 F_cur cur_vars scr5 (g_len + 5) 0 := by
  intro scr5
  have hlen5 : scr5.length = cap := by simp [scr5, hscrl]
  have hpref : ∀ idx < g_len, scr5[idx]? = scr[idx]? := fun idx hi => by
    simp only [scr5]; repeat rw [List.getElem?_set_ne (by omega)]
  have h0 : scr5[g_len]? = some y2 := by
    simp only [scr5]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by omega)]
  have h1 : scr5[g_len + 1]? = some ((2#32 <<< 28) ||| 3#32) := by
    simp only [scr5]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp [hscrl]; omega)]
  have h2 : scr5[g_len + 2]? = some c1 := by
    simp only [scr5]; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by simp [hscrl]; omega)]
  have h3 : scr5[g_len + 3]? = some t2 := by
    simp only [scr5]; rw [List.getElem?_set_ne (by omega),
      List.getElem?_set_self (by simp [hscrl]; omega)]
  have h4 : scr5[g_len + 4]? = some e2 := by
    simp only [scr5]; rw [List.getElem?_set_self (by simp [hscrl]; omega)]
  have hg_at : GateAt32 F_cur cur_vars scr5 (g_len + 5) g_len := by
    refine ⟨y2, (2#32 <<< 28) ||| 3#32, h0, h1, hy2_lt, by show g_len + 2 + 3 ≤ g_len + 5; omega,
      hcv3, by decide, fun k hk => ?_,
      Or.inr (Or.inr ⟨rfl, rfl, by rw [h2, h3, h4]; simpa using hite2⟩)⟩
    have hk3 : k < 3 := hk
    match k with
    | 0 => exact ⟨c1, h2, hc1_lt⟩
    | 1 => exact ⟨t2, h3, ht2_lt⟩
    | 2 => exact ⟨e2, h4, he2_lt⟩
    | _ + 3 => omega
  refine ⟨hlen5, hpref, gateSeqOk32_append (by omega) hpref (.step hg_at ?_) hseq0⟩
  simpa [h1] using GateSeqOk32.done

private theorem xorGateDef_of_four {f : CNF Nat} {a b c : Nat}
    (h1 : f.EntailsClause (cnfClause [a, b, c]))
    (h2 : f.EntailsClause (cnfClause [a, litNeg b, litNeg c]))
    (h3 : f.EntailsClause (cnfClause [litNeg a, b, litNeg c]))
    (h4 : f.EntailsClause (cnfClause [litNeg a, litNeg b, c])) :
    XorGateDef f (litNeg a) b c ∧ XorGateDef f (litNeg b) a c ∧ XorGateDef f (litNeg c) a b := by
  have h1' : XorGateDef f (litNeg a) b c :=
    ⟨entails_perm_clause (fun x hx => by
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
       rcases hx with rfl | rfl | rfl <;> simp) h4,
     entails_perm_clause (fun x hx => by
       simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
       rcases hx with rfl | rfl | rfl <;> simp) h3,
     by simpa [litNeg_litNeg] using h1,
     by simpa [litNeg_litNeg] using h2⟩
  refine ⟨h1', xorGateDef_of_eval_eq fun α hα => ?_, xorGateDef_of_eval_eq fun α hα => ?_⟩
  · have hv := xorGateDef_eval hα h1'; rw [evalLitVal_litNeg] at hv ⊢
    cases ha : evalLitVal α a <;> cases hb : evalLitVal α b <;> cases hc : evalLitVal α c <;>
      simp_all
  · have hv := xorGateDef_eval hα h1'; rw [evalLitVal_litNeg] at hv ⊢
    cases ha : evalLitVal α a <;> cases hb : evalLitVal α b <;> cases hc : evalLitVal α c <;>
      simp_all

/-- Emitting an AND gate from an arena clause (`3 ≤ sz ≤ 32`) gives `GateAt32`. -/
theorem andGate32_of_emitted {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hnd : FullArenaVarsNodup s) {p i sz g_len : Nat}
    (hp : p ∈ fullArenaClauseRefs s) (hng : fullArenaClauseGarb s p = false)
    (hsz_eq : fullArenaClauseSizeCore s.core p = sz) (hsz3 : 3 ≤ sz) (hsz32 : sz ≤ 32) (hi : i < sz)
    (hbins : ∀ k < sz, k ≠ i →
      (cnfOfClauses F_cur).EntailsClause
        (cnfClause [litNeg (s.core.arena[p + 3 + i]?.getD 0#32).toNat,
                    litNeg (s.core.arena[p + 3 + k]?.getD 0#32).toNat]))
    {scr : List (BitVec 32)} (hscrl : scr.length = c.scratch_cap)
    (hbd_g : g_len + 2 + (sz - 1) ≤ c.scratch_cap)
    (h0 : scr[g_len]? = some (s.core.arena[p + 3 + i]?.getD 0#32))
    (h1 : scr[g_len + 1]? = some (BitVec.ofNat 32 (sz - 1)))
    (hrhs : ∀ k < sz, k ≠ i →
      scr[g_len + 2 + (if k < i then k else k - 1)]? =
        some ((s.core.arena[p + 3 + k]?.getD 0#32) ^^^ 1#32)) :
    GateAt32 F_cur s.core.cur_vars scr (g_len + 2 + (sz - 1)) g_len := by
  have hwf := hw.arena.refs_wf p hp
  have har_bd : p + 3 + sz ≤ s.core.arena.length := by
    have := hlen.core_ok.arena_len_le; have := hlen.core_ok.arena_len_arr; omega
  have hsz_cv : sz ≤ s.core.cur_vars :=
    hsz_eq ▸ fullArenaClauseSize_le_cur_vars hlen hw hnd hp hng
  have hlit_lt : ∀ k < sz, (s.core.arena[p + 3 + k]?.getD 0#32).toNat < 2 * s.core.cur_vars :=
    fun k hk => hw.arena.lits_lt p hp hng _ <| (mem_fullArenaClauseLitsCore_iff (by omega)).mpr
      ⟨k, by omega, by rw [List.getElem?_eq_getElem (by omega), Option.getD_some]⟩
  have hmword_tag : ((BitVec.ofNat 32 (sz - 1) >>> 28)).toNat = 0 := by
    rw [BitVec.toNat_ushiftRight, bv32_ofNat_toNat (by omega), Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt (by omega)
  have hmword_ar : ((BitVec.ofNat 32 (sz - 1) &&& 0xFF#32)).toNat = sz - 1 := by
    rw [BitVec.toNat_and, bv32_ofNat_toNat (by omega),
      show (0xFF#32 : BitVec 32).toNat = 255 from rfl]
    simpa [Nat.mod_eq_of_lt (show sz - 1 < 256 by omega)] using
      Nat.and_two_pow_sub_one_eq_mod (sz - 1) 8
  have hrhs_at : ∀ r < sz - 1,
      ∃ v : BitVec 32, scr[g_len + 2 + r]? = some v ∧ v.toNat < 2 * s.core.cur_vars ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause [litNeg (s.core.arena[p + 3 + i]?.getD 0#32).toNat, v.toNat]) := by
    intro r hr
    let k := if r < i then r else r + 1
    have hk_lt : k < sz := by dsimp only [k]; split <;> omega
    have hk_ne : k ≠ i := by dsimp only [k]; split <;> omega
    have hk_eq : (if k < i then k else k - 1) = r := by
      dsimp only [k]; split <;> (try split) <;> omega
    have hget := hrhs k hk_lt hk_ne; rw [hk_eq] at hget
    exact ⟨_, hget, by rw [bv32_xor1_eq_litNeg]; exact bv32_xor1_lt_even (hlit_lt k hk_lt),
      by rw [bv32_xor1_eq_litNeg]; exact hbins k hk_lt hk_ne⟩
  refine ⟨s.core.arena[p + 3 + i]?.getD 0#32, BitVec.ofNat 32 (sz - 1), h0, h1, hlit_lt i hi,
    by omega, by omega, by omega,
    fun r hr => let ⟨v, hv, hlt, _⟩ := hrhs_at r (by omega); ⟨v, hv, hlt⟩, Or.inl ⟨hmword_tag,
    by omega, ?_, ?_⟩⟩
  · refine entails_perm_clause (fun x hx => ?_) (hw.arena.entails p hp hng)
    obtain ⟨k, hk, hget⟩ := (mem_fullArenaClauseLitsCore_iff (by omega)).mp hx
    rw [hsz_eq] at hk; rw [List.mem_cons]
    by_cases hki : k = i
    · subst hki; left; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact hget.symm
    · right; rw [List.mem_map]
      let r := if k < i then k else k - 1
      have hr_lt : r < sz - 1 := by dsimp only [r]; split <;> omega
      have hscr_r := hrhs k hk hki; have hr_scr : g_len + 2 + r < scr.length := by omega
      have hval_r : scr[g_len + 2 + r]'hr_scr = (s.core.arena[p + 3 + k]?.getD 0#32) ^^^ 1#32 := by
        rw [List.getElem?_eq_getElem hr_scr] at hscr_r; exact Option.some.inj hscr_r
      refine ⟨(scr[g_len + 2 + r]'hr_scr).toNat, List.mem_map.mpr ⟨_, ?_, rfl⟩, ?_⟩
      · have hlt_t : r < ((scr.drop (g_len + 2)).take
            ((BitVec.ofNat 32 (sz - 1) &&& 0xFF#32).toNat)).length := by
          rw [List.length_take, List.length_drop, hmword_ar]; omega
        simpa [List.getElem_take, List.getElem_drop] using List.getElem_mem hlt_t
      · rw [hval_r, bv32_xor1_eq_litNeg, litNeg_litNeg, List.getElem?_eq_getElem (by omega),
          Option.getD_some]
        exact hget
  · intro l hl
    rw [List.mem_map] at hl; obtain ⟨b, hb, rfl⟩ := hl
    obtain ⟨r, hr, hget⟩ := List.mem_iff_getElem.mp hb
    rw [List.length_take, List.length_drop, hmword_ar] at hr
    obtain ⟨v, hv, _, hent⟩ := hrhs_at r (by omega)
    rw [List.getElem_take, List.getElem_drop] at hget
    rw [List.getElem?_eq_getElem (by omega)] at hv
    rw [← Option.some.inj hv, hget] at hent; exact hent

end Helpers

/-! ## 3. `Func.wp` Proofs `#1–#6` -/

section Proofs1To6

open scoped FullArenaTactics FullCongTactics M3HeadTactics

/-- **#1 (`full_cong_merge`)**: merges two semantically equivalent literals in `repr`, checks
`full_add_bin` `2ULL` (OOM) return resetting `h->oom = 0ULL` cleanly, and satisfies exact canonical
`FullCongSpecs.fullCongMergeSpec`. -/
theorem m5_cong_merge_wp (Γ : Env)
    (hFind : ∀ args m Q X, fullCongFindSpec args m Q X →
      Γ "full_cong_find" [i64, i32] [i32] args m Q X)
    (hAddBin : ∀ args m Q X, FullCongSpecs.fullAddBinSpec args m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] args m Q X) :
    ∀ args m Q X, fullCongMergeSpec args m Q X →
      Func.wp Γ full_cong_merge_body args m Q X := by
  rintro ⟨h, a, b, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hmk, hnd, hext, hcl0, hdm, hrepr, ha, hb, heqv, hm0, hQ⟩
  have hmx := c.hmaxv; unfold dimacsBound at hmx; have hcv_le := hlen.core_ok.cur_vars_le
  have hrl := hlen.core_ok.repr_len; fc_steps; c0_call hFind
  refine ⟨F_cur, 2 * s.core.cur_vars, s.core.repr, FullReprRest c s ⋆ R, hrepr, ha,
    focus_full_repr hm0, fun ra repr1 m1 hrl1 hrepr1 _ hra_lt ha_ra hm1 => ?_⟩
  let s1 : FullState := { s with core := { s.core with repr := repr1 } }
  have hlen1 : s1.LengthsOk c := ⟨{ hlen.core_ok with repr_len := by simp [s1, hrl1, hrl] },
    hlen.scratch_ok⟩
  have hw1 : FullWitnessInv c F0 F_cur s1.core := fullWitnessInv_with_repr hw repr1
  have hm1' : (FullMem c s1 ⋆ R) m1 := unfocus_full_repr hm1; c0_call hFind
  refine ⟨F_cur, 2 * s.core.cur_vars, repr1, FullReprRest c s1 ⋆ R, hrepr1, hb,
    focus_full_repr hm1', fun rb repr2 m2 hrl2 hrepr2 _ hrb_lt hb_rb hm2 => ?_⟩
  let s2 : FullState := { s1 with core := { s1.core with repr := repr2 } }
  have hlen2 : s2.LengthsOk c := ⟨{ hlen1.core_ok with repr_len := by simp [s2, hrl2, hrl1, hrl] },
    hlen.scratch_ok⟩
  have hw2 : FullWitnessInv c F0 F_cur s2.core := fullWitnessInv_with_repr hw1 repr2
  have hm2' : (FullMem c s2 ⋆ R) m2 := unfocus_full_repr hm2; clear hm0 hm1 hm1' hm2
  have hrab_eqv : LitEquiv (cnfOfClauses F_cur) ra.toNat rb.toNat :=
    ha_ra.symm.trans (heqv.trans hb_rb)
  fc_split
  · fc_steps
    exact hQ false s2 m2 hlen2 hw2 hmk hnd hext hcl0 hdm rfl rfl rfl rfl rfl rfl hrepr2 hm2'
  · have hne_eq := hc; clear hc; fc_split
    · have heq_neg : ra = rb ^^^ 1#32 := by grind
      have hunsat : (cnfOfClauses F_cur).Unsat := by
        have hneg : LitEquiv (cnfOfClauses F_cur) rb.toNat (litNeg rb.toNat) := by
          rw [← bv32_xor1_eq_litNeg rb, ← heq_neg]; exact hrab_eqv.symm
        exact unsat_of_litEquiv_neg hneg
      fc_steps; let s3 : FullState := { s2 with core := { s2.core with inconsistent := 1#64 } }
      have hlen3 : s3.LengthsOk c := ⟨{ hlen2.core_ok with vals_len := hlen2.core_ok.vals_len },
        hlen2.scratch_ok⟩
      have hw3 : FullWitnessInv c F0 F_cur s3.core :=
        fullWitnessInv_with_inconsistent hw2 1#64 (fun _ => hunsat)
      exact hQ true s3 m hlen3 hw3 hmk hnd hext hcl0 hdm rfl rfl rfl rfl rfl rfl hrepr2 hm
    · have hne_neg := hc; clear hc; fc_to_group
      refine wp_join_group (ts := [i32, i32])
        (fun (ra', rb', ()) mj =>
          mj = m2 ∧ ra'.toNat < rb'.toNat ∧ rb'.toNat < 2 * s.core.cur_vars ∧
          ra' ≠ rb' ^^^ 1#32 ∧ LitEquiv (cnfOfClauses F_cur) ra'.toNat rb'.toNat)
        ?_ ?_
      · rintro _ ⟨ra', rb', ⟨⟩⟩ mj ⟨rfl, hlt_ab, hrb'_lt, hne_n', heqv'⟩
        have hra'_lt : ra'.toNat < 2 * s.core.cur_vars := by omega
        have hdiv := bv32_lt_and_ne_xor1_div_lt hlt_ab hne_n'
        have hnrb_lt : (rb' ^^^ 1#32).toNat < 2 * s.core.cur_vars := by
          rw [bv32_xor1_eq_litNeg]; exact bv32_xor1_lt_even hrb'_lt
        have hnra_lt : (ra' ^^^ 1#32).toNat < 2 * s.core.cur_vars := by
          rw [bv32_xor1_eq_litNeg]; exact bv32_xor1_lt_even hra'_lt
        have hrb_arr : rb'.toNat < s2.core.repr.length := by
          have := hlen2.core_ok.repr_len; omega
        have hnrb_arr : (rb' ^^^ 1#32).toNat < s2.core.repr.length := by
          have := hlen2.core_ok.repr_len; omega
        have hrb_z : (rb'.setWidth 64).toNat < s2.core.repr.length := by
          rw [bv_zext32_toNat]; exact hrb_arr
        have hnrb_z : ((rb' ^^^ 1).setWidth 64).toNat <
            (s2.core.repr.set (rb'.setWidth 64).toNat ra').length := by
          rw [List.length_set, bv_zext32_toNat]; exact hnrb_arr
        fc_steps; let repr3 := (repr2.set rb'.toNat ra').set (rb' ^^^ 1#32).toNat (ra' ^^^ 1#32)
        let s3 : FullState := { s2 with core := { s2.core with repr := repr3 } }
        have hlen3 : s3.LengthsOk c :=
          ⟨{ hlen2.core_ok with repr_len := by simpa [s3, repr3] using hlen2.core_ok.repr_len },
           hlen2.scratch_ok⟩
        have hw3 : FullWitnessInv c F0 F_cur s3.core := fullWitnessInv_with_repr hw2 repr3
        have hrepr3 : FullCongReprInv F_cur (2 * s.core.cur_vars) repr3 := by
          have hlen3_r : repr3.length = repr2.length := by simp [repr3]
          refine ⟨⟨by omega, fun x hx => ?_⟩, fun x hx => ?_⟩
          · by_cases hx1 : x = (rb' ^^^ 1#32).toNat
            · subst hx1; dsimp only [repr3]
              rw [List.getElem?_set_self (by simpa using hnrb_arr), Option.getD_some]; omega
            · dsimp only [repr3]; rw [List.getElem?_set_ne (Ne.symm hx1)]
              by_cases hx2 : x = rb'.toNat
              · subst hx2; rw [List.getElem?_set_self hrb_arr, Option.getD_some]; omega
              · rw [List.getElem?_set_ne (Ne.symm hx2)]; exact hrepr2.1.2 x hx
          · by_cases hx1 : x = (rb' ^^^ 1#32).toNat
            · subst hx1; dsimp only [repr3]
              rw [List.getElem?_set_self (by simpa using hnrb_arr), Option.getD_some,
                bv32_xor1_eq_litNeg, bv32_xor1_eq_litNeg]
              exact heqv'.symm.neg
            · dsimp only [repr3]; rw [List.getElem?_set_ne (Ne.symm hx1)]
              by_cases hx2 : x = rb'.toNat
              · subst hx2; rw [List.getElem?_set_self hrb_arr, Option.getD_some]; exact heqv'.symm
              · rw [List.getElem?_set_ne (Ne.symm hx2)]; exact hrepr2.2 x hx
        have hm3 : (FullMem c s3 ⋆ R) m := by
          rw [bv_zext32_toNat, bv_zext32_toNat] at hm; exact hm
        c0_call hAddBin
        refine ⟨c, F0, F_cur, s3, R, rfl, hlen3, hw3, hcl0, hnra_lt, hrb'_lt,
          by rw [bv32_xor1_litNeg]; exact heqv'.1, hm3,
          fun r1 s4 m4 hlen4 hw4 hcl4 hdm4 hcv4 hfl4 hmrk4 hlm4 har4 hal4 hrep4 htmp4 hscr4
            hll4 hel4 hr1_20 hm4 => ?_⟩
        have hmk4 : FullLitMarksClear c s4 := fullLitMarksClear_of_eq hmk hmrk4 hlm4
        have hnd4 : FullArenaVarsNodup s4 := fullArenaVarsNodup_of_eq hnd har4 hal4
        have hext4 : FullExtScratchOk c s4 := fullExtScratchOk_of_eq hext har4 hal4 hll4 hel4
        fc_split
        · have hunsat4 : (cnfOfClauses F_cur).Unsat := hw4.inconsistent_sound (hr1_20 (by grind))
          fc_steps
          let s5 : FullState := { s4 with core := { s4.core with inconsistent := 1#64 } }
          have hlen5 : s5.LengthsOk c := ⟨{ hlen4.core_ok with vals_len := hlen4.core_ok.vals_len },
            hlen4.scratch_ok⟩
          have hw5 : FullWitnessInv c F0 F_cur s5.core :=
            fullWitnessInv_with_inconsistent hw4 1#64 (fun _ => hunsat4)
          exact hQ true s5 m hlen5 hw5 hmk4 hnd4 hext4 hcl4 (hdm4 ▸ hdm) hcv4 hfl4 har4 hal4 htmp4
            hscr4 (by rw [show s5.core.cur_vars = s.core.cur_vars from hcv4,
              show s5.core.repr = repr3 from hrep4]; exact hrepr3) hm
        · fc_to_group
          refine wp_join_group (ts := [])
            (fun () mf => ∃ sf : FullState,
              sf.LengthsOk c ∧ FullWitnessInv c F0 F_cur sf.core ∧
              FullLitMarksClear c sf ∧ FullArenaVarsNodup sf ∧ FullExtScratchOk c sf ∧
              sf.core.cur_level = 0 ∧ sf.core.dense_mode ≠ 0#64 ∧
              sf.core.cur_vars = s.core.cur_vars ∧ sf.core.fuel = s.core.fuel ∧
              sf.core.arena = s.core.arena ∧ sf.core.arena_len = s.core.arena_len ∧
              sf.core.tmp = s.core.tmp ∧ sf.scratch.scratch_buf = s.scratch.scratch_buf ∧
              FullCongReprInv F_cur (2 * sf.core.cur_vars) sf.core.repr ∧
              (FullMem c sf ⋆ R) mf)
            (fun _ ⟨⟩ mf ⟨sf, hlenf, hwf, hmkf, hndf, hextf, hclf, hdmf, hcvf, hflf, harf, half,
                htmpf, hscrf, hreprf, hmf⟩ => by
              fc_steps
              let sf' : FullState := { sf with scratch :=
                { sf.scratch with cong_cnt := sf.scratch.cong_cnt + 1#64 } }
              have hlenf' : sf'.LengthsOk c := ⟨hlenf.core_ok,
                { hlenf.scratch_ok with walk_vals_len := hlenf.scratch_ok.walk_vals_len }⟩
              exact hQ true sf' m hlenf' hwf hmkf hndf hextf hclf hdmf hcvf hflf harf half htmpf
                hscrf hreprf hm)
            ?_
          intro Jend hJend
          fc_split
          · -- st1 == 2ULL -> h->oom = 0ULL; skip st2
            fc_steps
            let s4z : FullState := { s4 with core := { s4.core with oom := 0#64 } }
            have hlen4z : s4z.LengthsOk c :=
              ⟨{ hlen4.core_ok with vals_len := hlen4.core_ok.vals_len }, hlen4.scratch_ok⟩
            exact hJend () m ⟨s4z, hlen4z, fullWitnessInv_with_oom hw4 0#64, hmk4, hnd4, hext4,
              hcl4, hdm4 ▸ hdm, hcv4, hfl4, har4, hal4, htmp4, hscr4,
              by rw [show s4z.core.cur_vars = s.core.cur_vars from hcv4,
                show s4z.core.repr = repr3 from hrep4]; exact hrepr3, hm⟩
          · -- st1 != 2ULL -> call second full_add_bin
            fc_steps; c0_call hAddBin
            refine ⟨c, F0, F_cur, s4, R, rfl, hlen4, hw4, hcl4,
              hcv4 ▸ hra'_lt, hcv4 ▸ hnrb_lt,
              by rw [bv32_xor1_litNeg]; exact heqv'.2, hm4,
              fun r2 s5 m5 hlen5 hw5 hcl5 hdm5 hcv5 hfl5 hmrk5 hlm5 har5 hal5 hrep5 htmp5 hscr5
                hll5 hel5 hr2_20 hm5 => ?_⟩
            have hmk5 : FullLitMarksClear c s5 := fullLitMarksClear_of_eq hmk4 hmrk5 hlm5
            have hnd5 : FullArenaVarsNodup s5 := fullArenaVarsNodup_of_eq hnd4 har5 hal5
            have hext5 : FullExtScratchOk c s5 := fullExtScratchOk_of_eq hext4 har5 hal5 hll5 hel5
            have hrepr5 : FullCongReprInv F_cur (2 * s5.core.cur_vars) s5.core.repr := by
              rw [hcv5.trans hcv4, hrep5.trans hrep4]; exact hrepr3
            fc_split
            · have hunsat5 : (cnfOfClauses F_cur).Unsat :=
                hw5.inconsistent_sound (hr2_20 (by grind))
              fc_steps
              let s6 : FullState := { s5 with core := { s5.core with inconsistent := 1#64 } }
              have hlen6 : s6.LengthsOk c :=
                ⟨{ hlen5.core_ok with vals_len := hlen5.core_ok.vals_len }, hlen5.scratch_ok⟩
              have hw6 : FullWitnessInv c F0 F_cur s6.core :=
                fullWitnessInv_with_inconsistent hw5 1#64 (fun _ => hunsat5)
              exact hQ true s6 m hlen6 hw6 hmk5 hnd5 hext5 hcl5 (hdm5.trans hdm4 ▸ hdm)
                (hcv5.trans hcv4) (hfl5.trans hfl4) (har5.trans har4) (hal5.trans hal4)
                (htmp5.trans htmp4) (hscr5.trans hscr4) hrepr5 hm
            · fc_split
              · fc_steps
                let s5z : FullState := { s5 with core := { s5.core with oom := 0#64 } }
                have hlen5z : s5z.LengthsOk c :=
                  ⟨{ hlen5.core_ok with vals_len := hlen5.core_ok.vals_len }, hlen5.scratch_ok⟩
                exact hJend () m ⟨s5z, hlen5z, fullWitnessInv_with_oom hw5 0#64, hmk5, hnd5, hext5,
                  hcl5, hdm5.trans hdm4 ▸ hdm, hcv5.trans hcv4, hfl5.trans hfl4, har5.trans har4,
                  hal5.trans hal4, htmp5.trans htmp4, hscr5.trans hscr4, hrepr5, hm⟩
              · fc_steps
                exact hJend () m5 ⟨s5, hlen5, hw5, hmk5, hnd5, hext5, hcl5,
                  hdm5.trans hdm4 ▸ hdm, hcv5.trans hcv4, hfl5.trans hfl4, har5.trans har4,
                  hal5.trans hal4, htmp5.trans htmp4, hscr5.trans hscr4, hrepr5, hm5⟩
      · intro J hJ; fc_steps
        · exact hJ (rb, ra, ()) m2 ⟨rfl, by c0_bound, hra_lt, bv32_xor1_symm hne_neg, hrab_eqv.symm⟩
        · have hne_n : ra.toNat ≠ rb.toNat := fun h => hne_eq (BitVec.eq_of_toNat_eq h)
          exact hJ (ra, rb, ()) m2 ⟨rfl, by c0_bound, hrb_lt, hne_neg, hrab_eqv⟩

private theorem ite_scr5_bounds {g_len : BitVec 64} {cap len : Nat}
    (hcap : cap < 2 ^ 28) (hlen : len = cap) (h5 : g_len.toNat + 5 ≤ cap) :
    (g_len + 1).toNat = g_len.toNat + 1 ∧ (g_len + 2).toNat = g_len.toNat + 2 ∧
    (g_len + 3).toNat = g_len.toNat + 3 ∧ (g_len + 4).toNat = g_len.toNat + 4 ∧
    (g_len + 5).toNat = g_len.toNat + 5 ∧
    g_len.toNat < len ∧ (g_len + 1).toNat < len ∧ (g_len + 2).toNat < len ∧
    (g_len + 3).toNat < len ∧ (g_len + 4).toNat < len := by
  have h1 : (g_len + 1).toNat = g_len.toNat + 1 :=
    bv64_add_n (by change g_len.toNat + 1 < 2 ^ 64; omega)
  have h2 : (g_len + 2).toNat = g_len.toNat + 2 :=
    bv64_add_n (by change g_len.toNat + 2 < 2 ^ 64; omega)
  have h3 : (g_len + 3).toNat = g_len.toNat + 3 :=
    bv64_add_n (by change g_len.toNat + 3 < 2 ^ 64; omega)
  have h4 : (g_len + 4).toNat = g_len.toNat + 4 :=
    bv64_add_n (by change g_len.toNat + 4 < 2 ^ 64; omega)
  have h5n : (g_len + 5).toNat = g_len.toNat + 5 :=
    bv64_add_n (by change g_len.toNat + 5 < 2 ^ 64; omega)
  exact ⟨h1, h2, h3, h4, h5n, by omega, by omega, by omega, by omega, by omega⟩

/-- **#2 (`full_cong_extract_ite`)**: skips XOR-like `e == (t ^ 1u)`, normalizes both `c` and `t`
positive, and emits a 5-word `tag=2, arity=3` `GateAt32` entry. -/
theorem m5_cong_extract_ite_wp (Γ : Env)
    (hHasTern : ∀ args m Q X, fullHasTernarySpec args m Q X →
      Γ "full_has_ternary" [i64, i32, i32, i32] [.bool] args m Q X) :
    ∀ args m Q X, m5CongExtractIteSpec args m Q X →
      Func.wp Γ full_cong_extract_ite_body args m Q X := by
  rintro ⟨h, c_lit, y, t, g_len, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hcl0, hc_lt, hy_lt, ht_lt,
     hcy, hct, hyt, hcl1, hcl2, hglen_le, hseq0, hm0, hQ⟩
  have hmx := c.hmaxv; have hwc := c.hwcap; have hac := c.harena; have hsc := c.hscr
  unfold dimacsBound at hmx hwc hac hsc; have hcl := hlen.core_ok; have hsl := hlen.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hwvl := hcl.wvec_len
  have hwsl := hcl.wstk_len_arr; have hwle := hcl.wlen_le
  have harl := hcl.arena_len_arr; have hale := hcl.arena_len_le
  have hscrl := hsl.scratch_buf_len
  have hcv3 : 3 ≤ s.core.cur_vars :=
    cur_vars_ge3_of_distinct (by omega) (by omega) (by omega) hcy hct hyt
  have hw_bd := hw.watches.bounds c_lit.toNat hc_lt
  have hshl : (c_lit.setWidth 64 <<< (1 : Nat)).toNat = 2 * c_lit.toNat := by
    rw [bv64_shl1_toNat, bv_zext32_toNat]; omega
  have hshl1 : (c_lit.setWidth 64 <<< (1 : Nat) + 1#64).toNat = 2 * c_lit.toNat + 1 := by
    rw [BitVec.toNat_add, hshl]; show (2 * c_lit.toNat + 1) % 2 ^ 64 = 2 * c_lit.toNat + 1; omega
  have hslice0 : if s.core.dense_mode = 0#64 then
        WatchSliceOk F_cur s.core c_lit.toNat (fullWatchOffCore s.core c_lit.toNat)
          (fullWatchSizeCore s.core c_lit.toNat)
      else DenseWatchSliceOk F_cur s.core c_lit.toNat (fullWatchOffCore s.core c_lit.toNat)
          (fullWatchSizeCore s.core c_lit.toNat) := by
    have hwat := hw.watches; unfold ModeWatchesInv at hwat
    by_cases hdm : s.core.dense_mode = 0#64 <;> simp only [hdm, ↓reduceIte] at hwat ⊢
    · exact hwat.slices c_lit.toNat hc_lt
    · exact hwat.slices c_lit.toNat hc_lt
  fc_to_group
  generalize hoff_v :
    (s.core.wvec[(c_lit.setWidth 64 <<< (1 : Nat)).toNat]'(by omega)).setWidth 64 = off
  generalize hwsz_v :
    (s.core.wvec[(c_lit.setWidth 64 <<< (1 : Nat) + 1#64).toNat]'(by omega)).setWidth 64 = wsz
  have hoff_n : off.toNat = fullWatchOffCore s.core c_lit.toNat := by
    rw [← hoff_v, bv_zext32_toNat]; unfold fullWatchOffCore
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact congrArg BitVec.toNat (list_getElem_congr hshl (by omega) (by omega))
  have hwsz_n : wsz.toNat = fullWatchSizeCore s.core c_lit.toNat := by
    rw [← hwsz_v, bv_zext32_toNat]; unfold fullWatchSizeCore
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact congrArg BitVec.toNat (list_getElem_congr hshl1 (by omega) (by omega))
  have hend_n : (off + wsz).toNat = off.toNat + wsz.toNat := by bv_omega
  refine wp_loop_break_group (brkTs := [i32, i32, i32, i64]) (lpTs := [i64])
    (fun _ mb => mb = m0)
    (fun rem (p, ()) ml =>
      ml = m0 ∧ p.toNat ≤ (off + wsz).toNat ∧ rem = (off + wsz).toNat - p.toNat ∧
      (if s.core.dense_mode = 0#64 then
         WatchSliceOk F_cur s.core c_lit.toNat p.toNat ((off + wsz).toNat - p.toNat)
       else DenseWatchSliceOk F_cur s.core c_lit.toNat p.toNat ((off + wsz).toNat - p.toNat)))
    ?_ ?_ ?_
  · rintro _ ⟨_, _, _, _, ⟨⟩⟩ mb hmb; subst mb
    fc_steps
    exact hQ g_len s.scratch.scratch_buf m0 hscrl (Or.inl rfl) (fun _ _ => rfl) hseq0 hm0
  · rintro B L rem ⟨p, ⟨⟩⟩ ml hB hL ⟨hml, hp_le, rfl, hslice⟩
    subst ml; fc_split
    · have hp_lt : p.toNat < (off + wsz).toNat := by bv_omega
      have hp_w : p.toNat < s.core.wstk.length := by omega
      obtain ⟨w0, hw0_get, hcase⟩ := slice_pop_step hslice (by omega)
      have hw0_eq : s.core.wstk[p.toNat]'hp_w = w0 := by
        rw [List.getElem?_eq_getElem hp_w] at hw0_get; exact Option.some.inj hw0_get
      have hp1_n : (p + 1#64).toNat = p.toNat + 1 := by bv_omega
      fc_split
      · rcases hcase with ⟨_, hrest⟩ | ⟨hf0, _⟩
        · exact hL ((off + wsz).toNat - (p + 1#64).toNat) (p + 1#64, ()) m0 (by omega)
            ⟨rfl, by omega, rfl, by simpa [hp1_n, Nat.sub_sub] using hrest⟩
        · exfalso; rw [hw0_eq] at hc; exact hc hf0
      · rcases hcase with ⟨hf1, _⟩ | ⟨_, hrem2, cr, hcr_get, hcr_ref, hrest2⟩
        · exfalso; rw [hw0_eq] at hc; exact hf1 (by grind)
        · have hp1_n' : (p + 1).toNat = p.toNat + 1 := hp1_n
          have hp1_w : (p + 1).toNat < s.core.wstk.length := by omega
          have hcr_eq : s.core.wstk[(p + 1).toNat]'hp1_w = cr := by
            rw [list_getElem_congr hp1_n' hp1_w (by omega)]
            rw [List.getElem?_eq_getElem (by omega)] at hcr_get
            exact Option.some.inj hcr_get
          have hp1_m : (p.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 = p.toNat + 1 :=
            show (p.toNat + 1) % 2 ^ 64 = p.toNat + 1 from Nat.mod_eq_of_lt (by omega)
          have hcr_m : s.core.wstk[(p.toNat + (1 : BitVec 64).toNat) % 2 ^ 64]'(by omega) = cr := by
            rw [list_getElem_congr hp1_m _ (by omega)]
            rw [List.getElem?_eq_getElem (by omega)] at hcr_get
            exact Option.some.inj hcr_get
          have hcr_wf := hw.arena.refs_wf cr.toNat hcr_ref
          have hp2_n : (p + 1#64 + 1#64).toNat = p.toNat + 2 := by bv_omega
          have hcont2 : L (p + 1 + 1, ()) m0 :=
            hL ((off + wsz).toNat - (p + 1#64 + 1#64).toNat) (p + 1#64 + 1#64, ()) m0
              (by omega) ⟨rfl, by omega, rfl, by simpa [hp2_n, Nat.sub_sub] using hrest2⟩
          have hcr_arr : cr.toNat < s.core.arena.length := by omega
          have hcr2_m : (cr.toNat + (2 : BitVec 64).toNat) % 2 ^ 64 = cr.toNat + 2 :=
            show (cr.toNat + 2) % 2 ^ 64 = cr.toNat + 2 from Nat.mod_eq_of_lt (by omega)
          have hcr_w : ((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64).toNat <
              s.core.arena.length := by rw [hcr_eq, bv_zext32_toNat]; exact hcr_arr
          have hcr2_w : ((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64 + 2).toNat <
              s.core.arena.length := by
            rw [hcr_eq, BitVec.toNat_add, bv_zext32_toNat, hcr2_m]; omega
          fc_split
          · fc_split
            · exact hcont2
            · have hng_red := hc; clear hc
              fc_split
              · exact hcont2
              · have hsz3_bv := hc; clear hc
                simp only [hcr_m, hcr2_m] at hng_red hsz3_bv
                have hng : fullArenaClauseGarb s cr.toNat = false := by
                  unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
                  rw [List.getElem?_eq_getElem hcr_arr, Option.getD_some]
                  exact garb_false_of_and_480000 hng_red
                have hsz3 : fullArenaClauseSizeCore s.core cr.toNat = 3 := by
                  unfold fullArenaClauseSizeCore
                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                  exact congrArg BitVec.toNat hsz3_bv
                have hbd6 : cr.toNat + 6 ≤ s.core.arena.length := by omega
                have hlits3 := arena_clause3_lits (k := s.core) (cr := cr.toNat) hsz3 hbd6
                have hcl3 := hw.arena.entails cr.toNat hcr_ref hng
                have hnd3 := hnd cr.toNat hcr_ref hng
                have hlt3 := hw.arena.lits_lt cr.toNat hcr_ref hng
                unfold fullArenaClauseLits at hnd3
                rw [hlits3] at hcl3 hnd3 hlt3
                simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
                  List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hnd3
                have hcr3_m : (cr.toNat + (3 : BitVec 64).toNat) % 2 ^ 64 = cr.toNat + 3 :=
                  show (cr.toNat + 3) % 2 ^ 64 = cr.toNat + 3 from Nat.mod_eq_of_lt (by omega)
                have hcr4_m : (cr.toNat + (4 : BitVec 64).toNat) % 2 ^ 64 = cr.toNat + 4 :=
                  show (cr.toNat + 4) % 2 ^ 64 = cr.toNat + 4 from Nat.mod_eq_of_lt (by omega)
                have hcr5_m : (cr.toNat + (5 : BitVec 64).toNat) % 2 ^ 64 = cr.toNat + 5 :=
                  show (cr.toNat + 5) % 2 ^ 64 = cr.toNat + 5 from Nat.mod_eq_of_lt (by omega)
                have hcr3_w : ((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64 + 3).toNat <
                    s.core.arena.length := by
                  rw [hcr_eq, BitVec.toNat_add, bv_zext32_toNat, hcr3_m]; omega
                have hcr4_w : ((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64 + 4).toNat <
                    s.core.arena.length := by
                  rw [hcr_eq, BitVec.toNat_add, bv_zext32_toNat, hcr4_m]; omega
                have hcr5_w : ((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64 + 5).toNat <
                    s.core.arena.length := by
                  rw [hcr_eq, BitVec.toNat_add, bv_zext32_toNat, hcr5_m]; omega
                have hl0_eq : s.core.arena[((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64 +
                    3).toNat]'hcr3_w = s.core.arena[cr.toNat + 3]'(by omega) :=
                  list_getElem_congr (by rw [hcr_eq, BitVec.toNat_add, bv_zext32_toNat, hcr3_m]) _ _
                have hl1_eq : s.core.arena[((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64 +
                    4).toNat]'hcr4_w = s.core.arena[cr.toNat + 4]'(by omega) :=
                  list_getElem_congr (by rw [hcr_eq, BitVec.toNat_add, bv_zext32_toNat, hcr4_m]) _ _
                have hl2_eq : s.core.arena[((s.core.wstk[(p + 1).toNat]'hp1_w).setWidth 64 +
                    5).toNat]'hcr5_w = s.core.arena[cr.toNat + 5]'(by omega) :=
                  list_getElem_congr (by rw [hcr_eq, BitVec.toNat_add, bv_zext32_toNat, hcr5_m]) _ _
                fc_to_group
                refine wp_join_group (ts := [i32])
                  (fun (e, ()) mj => mj = m0 ∧
                    (e ≠ 0xFFFFFFFF#32 →
                      e.toNat < 2 * s.core.cur_vars ∧
                      e.toNat / 2 ≠ c_lit.toNat / 2 ∧ e.toNat / 2 ≠ y.toNat / 2 ∧
                      (cnfOfClauses F_cur).EntailsClause
                        (cnfClause [litNeg y.toNat, c_lit.toNat, e.toNat])))
                  ?_ ?_
                · rintro _ ⟨e, ⟨⟩⟩ mj ⟨hmj, he_ok⟩
                  subst mj
                  fc_split
                  · have he_ne : e ≠ 0xFFFFFFFF#32 := hc
                    obtain ⟨he_lt, hec, hey, hcl3_ite⟩ := he_ok he_ne
                    fc_split_fast
                    · fc_steps
                      c0_call hHasTern
                      refine ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hcl0, hc_lt, hm0,
                        fun ok hok => ?_⟩
                      fc_split_fast
                      · have hne_ce : c_lit ≠ e ^^^ 1 :=
                          bv32_ne_of_div2_ne (div2_ne_of_xor1 (Ne.symm hec))
                        have hne_cy : c_lit ≠ y := bv32_ne_of_div2_ne hcy
                        have hne_ey : e ^^^ 1 ≠ y :=
                          bv32_ne_of_div2_ne (div2_ne_of_xor1_l hey)
                        have hcl4 := hok hc hne_ce hne_cy hne_ey
                        have hcl4' : (cnfOfClauses F_cur).EntailsClause
                            (cnfClause [y.toNat, c_lit.toNat, litNeg e.toNat]) := by
                          rw [bv32_xor1_litNeg] at hcl4
                          exact entails_perm_clause (fun x hx => by
                            simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
                            rcases hx with rfl | rfl | rfl <;> simp) hcl4
                        have hite0 : IteGateDef (cnfOfClauses F_cur)
                            y.toNat c_lit.toNat t.toNat e.toNat :=
                          ⟨hcl1, hcl4', hcl2, hcl3_ite⟩
                        clear hl0_eq hl1_eq hl2_eq hcl1 hcl2 hcl3_ite hcl4 hcl4' hok hne_ce hne_cy
                          hne_ey hec hey he_ne he_ok hcy hct hyt hHasTern hlt3 hnd3 hcl3 hlits3
                          hbd6 hsz3 hng hcr_wf hrest2 hL hslice hB hslice0 hw_bd hcl0 hnd hw hlen
                          hcr_m hcr2_m hcr3_m hcr4_m hcr5_m hp1_n hp1_n' hp1_m hp2_n hcr_eq
                          hw0_eq hw0_get hcr_get hcr_ref hcont2 hng_red hsz3_bv hoff_v hwsz_v
                          hoff_n hwsz_n hend_n hwvl hwsl hwle harl hale hshl hshl1 hp_lt hmx
                          hwc hac hcv_le hcl hsl hc hrem2 hp_le
                        fc_to_group
                        refine wp_join_group (ts := [i32, i32, i32])
                          (fun (c1, t1, e1, ()) m1 => m1 = m0 ∧
                            c1.toNat < 2 * s.core.cur_vars ∧ t1.toNat < 2 * s.core.cur_vars ∧
                            e1.toNat < 2 * s.core.cur_vars ∧
                            IteGateDef (cnfOfClauses F_cur) y.toNat c1.toNat t1.toNat e1.toNat)
                          ?_ ?_
                        · rintro _ ⟨c1, t1, e1, ⟨⟩⟩ m1 ⟨hm1, hc1_lt, ht1_lt, he1_lt, hite1⟩
                          subst m1
                          fc_to_group
                          refine wp_join_group (ts := [i32, i32, i32])
                            (fun (y2, t2, e2, ()) m2 => m2 = m0 ∧
                              y2.toNat < 2 * s.core.cur_vars ∧ t2.toNat < 2 * s.core.cur_vars ∧
                              e2.toNat < 2 * s.core.cur_vars ∧
                              IteGateDef (cnfOfClauses F_cur) y2.toNat c1.toNat t2.toNat e2.toNat)
                            ?_ ?_
                          · rintro _ ⟨y2, t2, e2, ⟨⟩⟩ m2 ⟨hm2, hy2_lt, ht2_lt, he2_lt, hite2⟩
                            subst m2
                            have hi32 : i32.bytes = 4 := rfl
                            obtain ⟨hg1, hg2, hg3, hg4, hg5, hg0_lt, hg1_lt, hg2_lt, hg3_lt,
                              hg4_lt⟩ := ite_scr5_bounds hsc hscrl hglen_le
                            have hfs := focus_full_scratch_buf hm0; clear hm0
                            generalize hR_scr : FullScrBufRest c s ⋆ R = R_scr at hfs
                            fc_steps; subst hR_scr
                            obtain ⟨hlen5, hpref, hseq5⟩ := ite_emit_gateSeq32 hscrl hglen_le hcv3
                              hy2_lt hc1_lt ht2_lt he2_lt hite2 hseq0
                            rw [hg1, hg2, hg3, hg4] at hm
                            exact hQ (g_len + 5) _ m hlen5 (Or.inr rfl) hpref (hg5 ▸ hseq5)
                              (unfocus_full_scratch_buf hm)
                          · intro Jy hJy; c0_let_simp; refine ⟨fun _ => ?_, fun _ => ?_⟩
                            · c0_let_simp
                              exact hJy (y ^^^ 1#32, t1 ^^^ 1#32, e1 ^^^ 1#32, ()) m0
                                ⟨rfl, by rw [bv32_xor1_eq_litNeg]; exact bv32_xor1_lt_even hy_lt,
                                 by rw [bv32_xor1_eq_litNeg]; exact bv32_xor1_lt_even ht1_lt,
                                 by rw [bv32_xor1_eq_litNeg]; exact bv32_xor1_lt_even he1_lt,
                                 by simp only [bv32_xor1_eq_litNeg]
                                    exact iteGateDef_flip_out hite1⟩
                            · c0_let_simp
                              exact hJy (y, t1, e1, ()) m0 ⟨rfl, hy_lt, ht1_lt, he1_lt, hite1⟩
                        · intro Jc hJc; c0_let_simp; refine ⟨fun _ => ?_, fun _ => ?_⟩
                          · c0_let_simp
                            exact hJc (c_lit ^^^ 1#32, e, t, ()) m0
                              ⟨rfl, by rw [bv32_xor1_eq_litNeg]; exact bv32_xor1_lt_even hc_lt,
                               he_lt, ht_lt,
                               by rw [bv32_xor1_eq_litNeg]; exact iteGateDef_flip_cond hite0⟩
                          · c0_let_simp
                            exact hJc (c_lit, t, e, ()) m0 ⟨rfl, hc_lt, ht_lt, he_lt, hite0⟩
                      · exact hcont2
                    · exact hcont2
                  · exact hcont2
                · intro Je hJe
                  have hJe' : ∀ (v : Val i32) (m : Mem 64), (m = m0 ∧ (v ≠ 0xFFFFFFFF#32 →
                      v.toNat < 2 * s.core.cur_vars ∧ v.toNat / 2 ≠ c_lit.toNat / 2 ∧
                      v.toNat / 2 ≠ y.toNat / 2 ∧ (cnfOfClauses F_cur).EntailsClause
                        (cnfClause [litNeg y.toNat, c_lit.toNat, v.toNat]))) →
                      Je (v, ()) m := fun v m h => hJe (v, ()) m h
                  clear hJe hHasTern hQ hseq0 hglen_le hcl1 hcl2 hcy hct hyt hcv3 hw_bd hslice0
                  clear hoff_n hwsz_n hend_n hB hL hslice hrest2 hcr_wf hcont2 hlits3 hng hsz3
                  clear hng_red hsz3_bv hw0_eq hw0_get hcr_get hcr_ref hcl0 hnd hw hlen hm0
                  repeat (
                    intro Js hJs
                    suffices hnext : Js.1 () m0 by
                      c0_let_simp; refine ⟨fun h1 => ?_, fun _ => hnext⟩
                      c0_let_simp; refine ⟨fun h2 => ?_, fun _ => hnext⟩
                      c0_let_simp
                      refine hJe' _ m0 ⟨rfl, fun _ => ite_pick_e_ok hcl3
                        ⟨hnd3.1.1, hnd3.1.2, hnd3.2.1⟩ hlt3
                        (beq_iff_eq.mp h1) (beq_iff_eq.mp h2) ?_⟩
                      rw [hl0_eq, hl1_eq, hl2_eq]
                      simp only [and_self, true_or, or_true]
                    refine closed_cons_get hJs () m0 fun Jf hJf => ?_
                    have hJe' := fun v m h => closed_cons_get hJf (v, ()) m (hJe' v m h))
                  c0_let_simp; refine ⟨fun h1 => ?_, fun _ => hJe' 0xFFFFFFFF#32 m0
                    ⟨rfl, fun h => absurd rfl h⟩⟩
                  c0_let_simp; refine ⟨fun h2 => ?_, fun _ => hJe' 0xFFFFFFFF#32 m0
                    ⟨rfl, fun h => absurd rfl h⟩⟩
                  c0_let_simp; refine hJe' _ m0 ⟨rfl, fun _ => ite_pick_e_ok hcl3
                    ⟨hnd3.1.1, hnd3.1.2, hnd3.2.1⟩ hlt3
                    (beq_iff_eq.mp h1) (beq_iff_eq.mp h2) ?_⟩
                  rw [hl0_eq, hl1_eq, hl2_eq]
                  simp only [and_self, or_true]
    · exact hB (c_lit, y, t, p, ()) m0 rfl
  · intro _ L _ hL; c0_let_simp
    refine hL ((off + wsz).toNat - off.toNat) (off, ()) m0 ⟨rfl, by omega, rfl, ?_⟩
    simpa [hend_n, hoff_n, hwsz_n] using hslice0

/-- **#3 (`full_cong_emit_xor`)**: emits one polarity-normalized 4-word `tag=1, arity=2` XOR
`GateAt32` record into `scr[g_len ..< g_len + 4)`. -/
theorem m5_cong_emit_xor_wp (Γ : Env) :
    ∀ args m Q X, m5CongEmitXorSpec args m Q X →
      Func.wp Γ full_cong_emit_xor_body args m Q X := by
  rintro ⟨scr_ptr, g_len, x0, x1, x2, ⟨⟩⟩ m0 Q X
    ⟨F_cur, cur_vars, scr, R, hx0, hx1, hx2, hcv2, hg_le, hscr_lt, hxor, hseq0, hm0, hQ⟩
  have hnx0 : (x0 ^^^ 1#32).toNat < 2 * cur_vars := by
    rw [bv32_xor1_eq_litNeg]; exact bv32_xor1_lt_even hx0
  have hxs0 := xor_sign_strip_sound hnx0 hx1 hx2 (by rw [bv32_xor1_eq_litNeg]; exact hxor)
  have hlhs_eq : (((x0 ^^^ 1#32) &&& ~~~1#32) ||| ((((x0 ^^^ 1#32) ^^^ x1) ^^^ x2) &&& 1#32)) =
      (x0 ^^^ 1#32) ^^^ ((x1 ^^^ x2) &&& 1#32) :=
    bv32_emit_xor_lhs_eq (x0 ^^^ 1#32) x1 x2
  have hi32 : i32.bytes = 4 := rfl
  have hg1 : (g_len + 1).toNat = g_len.toNat + 1 := by bv_omega
  have hg2 : (g_len + 2).toNat = g_len.toNat + 2 := by bv_omega
  have hg3 : (g_len + 3).toNat = g_len.toNat + 3 := by bv_omega
  let lhs := ((x0 ^^^ 1#32) &&& ~~~1#32) ||| ((((x0 ^^^ 1#32) ^^^ x1) ^^^ x2) &&& 1#32)
  let r0 := x1 &&& ~~~1#32
  let r1 := x2 &&& ~~~1#32
  have hxs : lhs.toNat < 2 * cur_vars ∧ r0.toNat < 2 * cur_vars ∧ r1.toNat < 2 * cur_vars ∧
      XorGateDef (cnfOfClauses F_cur) lhs.toNat r0.toNat r1.toNat ∧
      XorGateDef (cnfOfClauses F_cur) lhs.toNat r1.toNat r0.toNat := by
    dsimp only [lhs, r0, r1]; rw [hlhs_eq]; exact hxs0
  have hfinish : ∀ (a0 a1 : BitVec 32) (m : Mem 64),
      ((a0 = r0 ∧ a1 = r1) ∨ (a0 = r1 ∧ a1 = r0)) →
      let scr1 := scr.set g_len.toNat lhs
      let scr2 := scr1.set (g_len.toNat + 1) ((1#32 <<< 28) ||| 2#32)
      let scr3 := scr2.set (g_len.toNat + 2) a0
      let scr4 := scr3.set (g_len.toNat + 3) a1
      (array (t := i32) scr_ptr scr4 ⋆ R) m → Q (g_len + 4#64, ()) m := by
    intro a0 a1 m hpair scr1 scr2 scr3 scr4 hm4
    have hlen4 : scr4.length = scr.length := by simp [scr4, scr3, scr2, scr1]
    have hpref : ∀ idx < g_len.toNat, scr4[idx]? = scr[idx]? := fun idx hi => by
      simp only [scr4, scr3, scr2, scr1]
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
        List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    have hg_at : GateAt32 F_cur cur_vars scr4 (g_len.toNat + 4) g_len.toNat := by
      have h0 : scr4[g_len.toNat]? = some lhs := by
        simp only [scr4, scr3, scr2, scr1]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega)]
      have h1 : scr4[g_len.toNat + 1]? = some ((1#32 <<< 28) ||| 2#32) := by
        simp only [scr4, scr3, scr2, scr1]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_self (by simp; omega)]
      have h2 : scr4[g_len.toNat + 2]? = some a0 := by
        simp only [scr4, scr3, scr2, scr1]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp; omega)]
      have h3 : scr4[g_len.toNat + 3]? = some a1 := by
        simp only [scr4, scr3, scr2, scr1]
        rw [List.getElem?_set_self (by simp; omega)]
      refine ⟨lhs, (1#32 <<< 28) ||| 2#32, h0, h1, hxs.1,
        by show g_len.toNat + 2 + 2 ≤ g_len.toNat + 4; omega, hcv2, by decide, ?_, ?_⟩
      · intro k hk; have hk2 : k < 2 := hk
        match k with
        | 0 => exact ⟨a0, h2, by
            rcases hpair with ⟨rfl, _⟩ | ⟨rfl, _⟩; exact hxs.2.1; exact hxs.2.2.1⟩
        | 1 => exact ⟨a1, h3, by
            rcases hpair with ⟨_, rfl⟩ | ⟨_, rfl⟩; exact hxs.2.2.1; exact hxs.2.1⟩
        | _ + 2 => omega
      · right; left; refine ⟨rfl, rfl, ?_⟩
        rw [h2, h3]; dsimp only [Option.getD_some]
        rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hxs.2.2.2.1
        · exact hxs.2.2.2.2
    have hseq4 : GateSeqOk32 F_cur cur_vars scr4 (g_len.toNat + 4) 0 := by
      refine gateSeqOk32_append (by omega) hpref ?_ hseq0
      refine .step hg_at ?_
      have h1 : scr4[g_len.toNat + 1]? = some ((1#32 <<< 28) ||| 2#32) := by
        simp only [scr4, scr3, scr2, scr1]
        rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
          List.getElem?_set_self (by simp; omega)]
      simpa [h1] using GateSeqOk32.done
    exact hQ scr4 m hlen4 hpref hseq4 hm4
  fc_steps
  · exact hfinish r0 r1 m (Or.inl ⟨rfl, rfl⟩) (by rw [hg1, hg2, hg3] at hm; exact hm)
  · exact hfinish r1 r0 m (Or.inr ⟨rfl, rfl⟩) (by rw [hg1, hg2, hg3] at hm; exact hm)

/-- **#4 (`full_cong_try_xor_ite`)**: canonical XOR base-clause filter (eliminating `4x` duplicate
bloat) + non-blocking ITE selector fallback across `a`, `b`, `c`. -/
theorem m5_cong_try_xor_ite_wp (Γ : Env)
    (hHasTern : ∀ args m Q X, fullHasTernarySpec args m Q X →
      Γ "full_has_ternary" [i64, i32, i32, i32] [.bool] args m Q X)
    (hEmitXor : ∀ args m Q X, m5CongEmitXorSpec args m Q X →
      Γ "full_cong_emit_xor" [i64, i64, i32, i32, i32] [i64] args m Q X)
    (hExtIte : ∀ args m Q X, m5CongExtractIteSpec args m Q X →
      Γ "full_cong_extract_ite" [i64, i32, i32, i32, i64] [i64] args m Q X) :
    ∀ args m Q X, m5CongTryXorIteSpec args m Q X →
      Func.wp Γ full_cong_try_xor_ite_body args m Q X := by
  rintro ⟨h, a, b, cl, g_len, g_cap, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hcl0, ha_lt, hb_lt, hc_lt,
     hab_v, hac_v, hbc_v, hcl0_ent, hg_le, hgc_le, hseq0, hm0, hQ⟩
  have hsc := c.hscr; unfold dimacsBound at hsc
  have hscrl := hlen.scratch_ok.scratch_buf_len
  have hcv3 : 3 ≤ s.core.cur_vars :=
    cur_vars_ge3_of_distinct (by omega) (by omega) (by omega) hab_v hac_v hbc_v
  have hna_lt : (a ^^^ 1).toNat < 2 * s.core.cur_vars := by
    rw [bv32_xor1_litNeg]; exact bv32_xor1_lt_even ha_lt
  have hnb_lt : (b ^^^ 1).toNat < 2 * s.core.cur_vars := by
    rw [bv32_xor1_litNeg]; exact bv32_xor1_lt_even hb_lt
  have hnc_lt : (cl ^^^ 1).toNat < 2 * s.core.cur_vars := by
    rw [bv32_xor1_litNeg]; exact bv32_xor1_lt_even hc_lt
  have hdis_lit : ∀ x y : BitVec 32, x.toNat / 2 ≠ y.toNat / 2 → x ≠ y :=
    fun _ _ => bv32_ne_of_div2_ne
  have hperm3 : ∀ {u v w u' v' w' : Nat},
      (u = u' ∨ u = v' ∨ u = w') → (v = u' ∨ v = v' ∨ v = w') → (w = u' ∨ w = v' ∨ w = w') →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [u, v, w]) →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [u', v', w']) :=
    fun hu hv hw_p hcl => entails_perm_clause (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl | rfl <;> assumption) hcl
  -- Reusable helper: call `full_cong_extract_ite` from any `scr_cur` matching `s` on `[0..g_len)`
  have hite_call : ∀ (x y z : BitVec 32) (scr_cur : List (BitVec 32)) (m_cur : Mem 64),
      scr_cur.length = c.scratch_cap →
      (∀ idx < g_len.toNat, scr_cur[idx]? = s.scratch.scratch_buf[idx]?) →
      GateSeqOk32 F_cur s.core.cur_vars scr_cur g_len.toNat 0 →
      x.toNat < 2 * s.core.cur_vars → y.toNat < 2 * s.core.cur_vars →
      z.toNat < 2 * s.core.cur_vars →
      x.toNat / 2 ≠ y.toNat / 2 → x.toNat / 2 ≠ z.toNat / 2 → y.toNat / 2 ≠ z.toNat / 2 →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [x.toNat, y.toNat, z.toNat]) →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [x.toNat, litNeg y.toNat, litNeg z.toNat]) →
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr_cur } } ⋆ R) m_cur →
      ∀ (P : Post [i64]),
      (∀ (ng : BitVec 64) (scr1 : List (BitVec 32)) (m1 : Mem 64),
        scr1.length = c.scratch_cap → (ng = g_len ∨ ng = g_len + 5#64) →
        (∀ idx < g_len.toNat, scr1[idx]? = s.scratch.scratch_buf[idx]?) →
        GateSeqOk32 F_cur s.core.cur_vars scr1 ng.toNat 0 →
        (FullMem c { s with scratch := { s.scratch with scratch_buf := scr1 } } ⋆ R) m1 →
        P (ng, ()) m1) →
      m5CongExtractIteSpec (c.hdr, x ^^^ 1, y ^^^ 1, z, g_len, ()) m_cur P X := by
    intro x y z scr_cur m_cur hlen_c hpref_c hgate_c hx hy hz hxy hxz hyz he1 he2 hm_c P hP
    let sc : FullState := { s with scratch := { s.scratch with scratch_buf := scr_cur } }
    refine ⟨c, F0, F_cur, sc, R, rfl,
      ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hlen_c }⟩,
      hw, hnd, hcl0,
      by rw [bv32_xor1_litNeg]; exact bv32_xor1_lt_even hx,
      by rw [bv32_xor1_litNeg]; exact bv32_xor1_lt_even hy, hz,
      div2_ne_of_xor1_both hxy, div2_ne_of_xor1_l hxz, div2_ne_of_xor1_l hyz,
      by simp only [bv32_xor1_litNeg, litNeg_litNeg]
         exact hperm3 (Or.inr (Or.inl rfl)) (Or.inl rfl) (Or.inr (Or.inr rfl)) he2,
      by simp only [bv32_xor1_litNeg, litNeg_litNeg]
         exact hperm3 (Or.inr (Or.inl rfl)) (Or.inl rfl) (Or.inr (Or.inr rfl)) he1,
      by omega, hgate_c, hm_c, fun ng scr1 m1 hlen1 hng hpref1 hseq1 hm1 =>
        hP ng scr1 m1 hlen1 hng (fun idx hi => (hpref1 idx hi).trans (hpref_c idx hi)) hseq1 hm1⟩
  have hret_gt : ∀ (ng : BitVec 64) (scr1 : List (BitVec 32)) (m1 : Mem 64),
      scr1.length = c.scratch_cap → (ng = g_len ∨ ng = g_len + 5#64) →
      (∀ idx < g_len.toNat, scr1[idx]? = s.scratch.scratch_buf[idx]?) →
      GateSeqOk32 F_cur s.core.cur_vars scr1 ng.toNat 0 →
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr1 } } ⋆ R) m1 →
      Q (ng, ()) m1 := by
    intro ng scr1 m1 hlen1 hng hpref1 hseq1 hm1
    have hbounds : g_len.toNat ≤ ng.toNat ∧ ng.toNat ≤ g_cap.toNat := by
      rcases hng with rfl | rfl
      · exact ⟨Nat.le_refl _, by omega⟩
      · have : (g_len + 5#64).toNat = g_len.toNat + 5 := by bv_omega
        omega
    exact hQ ng scr1 m1 hlen1 hbounds.1 hbounds.2 hpref1 hseq1 hm1
  have hng_eq_of_not_gt : ∀ (ng : BitVec 64), (ng = g_len ∨ ng = g_len + 5#64) →
      g_len.ult ng = false → ng = g_len := by
    intro ng hng hnot
    rcases hng with rfl | rfl
    · rfl
    · exfalso
      have h5 : (g_len + 5#64).toNat = g_len.toNat + 5 := by bv_omega
      have hnl := bv64_ult_not_lt hnot; omega
  let ScrKeep (m_cur : Mem 64) : Prop :=
    ∃ scr_c : List (BitVec 32), scr_c.length = c.scratch_cap ∧
      (∀ idx < g_len.toNat, scr_c[idx]? = s.scratch.scratch_buf[idx]?) ∧
      GateSeqOk32 F_cur s.core.cur_vars scr_c g_len.toNat 0 ∧
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr_c } } ⋆ R) m_cur
  -- Step `mx = max(a, b, c)` cleanly via two joins
  fc_to_group
  refine wp_join_group (ts := [i32]) (fun (_, ()) m1 => m1 = m0) ?_ ?_
  · rintro _ ⟨mx0, ⟨⟩⟩ m1 hm1; subst m1
    fc_to_group
    refine wp_join_group (ts := [i32]) (fun (_, ()) m2 => m2 = m0) ?_ ?_
    · rintro _ ⟨mx, ⟨⟩⟩ m2 hm2; subst m2
      fc_to_group
      refine wp_join_group (ts := []) (fun () mj => mj = m0) ?_ ?_
      · -- Non-blocking ITE fallback across `a`, `b`, `c`
        rintro _ ⟨⟩ mj hmj; subst mj
        have hkeep0 : ScrKeep m0 := ⟨s.scratch.scratch_buf, hscrl, fun _ _ => rfl, hseq0, hm0⟩
        fc_to_group
        refine wp_join_group (ts := []) (fun () m1 => ScrKeep m1) ?_ ?_
        · rintro _ ⟨⟩ m1 hk1
          fc_to_group
          refine wp_join_group (ts := []) (fun () m2 => ScrKeep m2) ?_ ?_
          · rintro _ ⟨⟩ m2 hk2
            fc_to_group
            refine wp_join_group (ts := []) (fun () m3 => ScrKeep m3) ?_ ?_
            · rintro _ ⟨⟩ m3 ⟨scr3, hlen3, hpref3, hseq3, hm3⟩
              fc_steps
              exact hQ g_len scr3 m3 hlen3 (Nat.le_refl _) (by omega) hpref3 hseq3 hm3
            · intro Jc hJc
              obtain ⟨scr_c, hlen_c, hpref_c, hseq_c, hm_c⟩ := hk2
              let sc : FullState := { s with scratch := { s.scratch with scratch_buf := scr_c } }
              have hlen_sc : sc.LengthsOk c :=
                ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hlen_c }⟩
              have hcl_cab := hperm3 (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) (Or.inl rfl)
                hcl0_ent
              fc_steps; c0_call hHasTern
              refine ⟨c, F0, F_cur, sc, R, rfl, hlen_sc, hw, hnd, hcl0, hc_lt, hm_c,
                fun ok hok => ?_⟩
              fc_split_fast
              · have hti : (cnfOfClauses F_cur).EntailsClause
                    (cnfClause [cl.toNat, litNeg a.toNat, litNeg b.toNat]) := by
                  simpa only [bv32_xor1_litNeg] using hok hc
                    (hdis_lit _ _ (div2_ne_of_xor1 (Ne.symm hac_v)))
                    (hdis_lit _ _ (div2_ne_of_xor1 (Ne.symm hbc_v)))
                    (hdis_lit _ _ (div2_ne_of_xor1_both hab_v))
                fc_steps; c0_call hExtIte
                refine hite_call cl a b scr_c m2 hlen_c hpref_c hseq_c hc_lt ha_lt hb_lt
                  (Ne.symm hac_v) (Ne.symm hbc_v) hab_v hcl_cab hti hm_c _
                  fun ng1 scr1 m1 hlen1 hng1 hpref1 hseq1 hm1 => ?_
                fc_split_fast
                · fc_steps; exact hret_gt ng1 scr1 m1 hlen1 hng1 hpref1 hseq1 hm1
                · have heq1 := hng_eq_of_not_gt ng1 hng1 hc; subst heq1
                  fc_steps; c0_call hExtIte
                  refine hite_call cl b a scr1 m1 hlen1 hpref1 hseq1 hc_lt hb_lt ha_lt
                    (Ne.symm hbc_v) (Ne.symm hac_v) (Ne.symm hab_v)
                    (hperm3 (Or.inl rfl) (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)) hcl_cab)
                    (hperm3 (Or.inl rfl) (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)) hti) hm1 _
                    fun ng2 scr2 m2' hlen2 hng2 hpref2 hseq2 hm2' => ?_
                  fc_split_fast
                  · fc_steps; exact hret_gt ng2 scr2 m2' hlen2 hng2 hpref2 hseq2 hm2'
                  · have heq2 := hng_eq_of_not_gt ng2 hng2 hc; subst heq2
                    fc_let; exact hJc () m2' ⟨scr2, hlen2, hpref2, hseq2, hm2'⟩
              · fc_let; exact hJc () m2 ⟨scr_c, hlen_c, hpref_c, hseq_c, hm_c⟩
          · intro Jb hJb
            obtain ⟨scr_c, hlen_c, hpref_c, hseq_c, hm_c⟩ := hk1
            let sc : FullState := { s with scratch := { s.scratch with scratch_buf := scr_c } }
            have hlen_sc : sc.LengthsOk c :=
              ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hlen_c }⟩
            have hcl_bac := hperm3 (Or.inr (Or.inl rfl)) (Or.inl rfl) (Or.inr (Or.inr rfl))
              hcl0_ent
            fc_steps; c0_call hHasTern
            refine ⟨c, F0, F_cur, sc, R, rfl, hlen_sc, hw, hnd, hcl0, hb_lt, hm_c,
              fun ok hok => ?_⟩
            fc_split_fast
            · have hti : (cnfOfClauses F_cur).EntailsClause
                  (cnfClause [b.toNat, litNeg a.toNat, litNeg cl.toNat]) := by
                simpa only [bv32_xor1_litNeg] using hok hc
                  (hdis_lit _ _ (div2_ne_of_xor1 (Ne.symm hab_v)))
                  (hdis_lit _ _ (div2_ne_of_xor1 hbc_v))
                  (hdis_lit _ _ (div2_ne_of_xor1_both hac_v))
              fc_steps; c0_call hExtIte
              refine hite_call b a cl scr_c m1 hlen_c hpref_c hseq_c hb_lt ha_lt hc_lt
                (Ne.symm hab_v) hbc_v hac_v hcl_bac hti hm_c _
                fun ng1 scr1 m1' hlen1 hng1 hpref1 hseq1 hm1' => ?_
              fc_split_fast
              · fc_steps; exact hret_gt ng1 scr1 m1' hlen1 hng1 hpref1 hseq1 hm1'
              · have heq1 := hng_eq_of_not_gt ng1 hng1 hc; subst heq1
                fc_steps; c0_call hExtIte
                refine hite_call b cl a scr1 m1' hlen1 hpref1 hseq1 hb_lt hc_lt ha_lt
                  hbc_v (Ne.symm hab_v) (Ne.symm hac_v)
                  (hperm3 (Or.inl rfl) (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)) hcl_bac)
                  (hperm3 (Or.inl rfl) (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)) hti) hm1' _
                  fun ng2 scr2 m2' hlen2 hng2 hpref2 hseq2 hm2' => ?_
                fc_split_fast
                · fc_steps; exact hret_gt ng2 scr2 m2' hlen2 hng2 hpref2 hseq2 hm2'
                · have heq2 := hng_eq_of_not_gt ng2 hng2 hc; subst heq2
                  fc_let; exact hJb () m2' ⟨scr2, hlen2, hpref2, hseq2, hm2'⟩
            · fc_let; exact hJb () m1 ⟨scr_c, hlen_c, hpref_c, hseq_c, hm_c⟩
        · intro Ja hJa
          obtain ⟨scr_c, hlen_c, hpref_c, hseq_c, hm_c⟩ := hkeep0
          let sc : FullState := { s with scratch := { s.scratch with scratch_buf := scr_c } }
          have hlen_sc : sc.LengthsOk c :=
            ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hlen_c }⟩
          fc_steps; c0_call hHasTern
          refine ⟨c, F0, F_cur, sc, R, rfl, hlen_sc, hw, hnd, hcl0, ha_lt, hm_c,
            fun ok hok => ?_⟩
          fc_split_fast
          · have hti : (cnfOfClauses F_cur).EntailsClause
                (cnfClause [a.toNat, litNeg b.toNat, litNeg cl.toNat]) := by
              simpa only [bv32_xor1_litNeg] using hok hc
                (hdis_lit _ _ (div2_ne_of_xor1 hab_v))
                (hdis_lit _ _ (div2_ne_of_xor1 hac_v))
                (hdis_lit _ _ (div2_ne_of_xor1_both hbc_v))
            fc_steps; c0_call hExtIte
            refine hite_call a b cl scr_c m0 hlen_c hpref_c hseq_c ha_lt hb_lt hc_lt
              hab_v hac_v hbc_v hcl0_ent hti hm_c _
              fun ng1 scr1 m1' hlen1 hng1 hpref1 hseq1 hm1' => ?_
            fc_split_fast
            · fc_steps; exact hret_gt ng1 scr1 m1' hlen1 hng1 hpref1 hseq1 hm1'
            · have heq1 := hng_eq_of_not_gt ng1 hng1 hc; subst heq1
              fc_steps; c0_call hExtIte
              refine hite_call a cl b scr1 m1' hlen1 hpref1 hseq1 ha_lt hc_lt hb_lt
                hac_v hab_v (Ne.symm hbc_v)
                (hperm3 (Or.inl rfl) (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)) hcl0_ent)
                (hperm3 (Or.inl rfl) (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)) hti) hm1' _
                fun ng2 scr2 m2' hlen2 hng2 hpref2 hseq2 hm2' => ?_
              fc_split_fast
              · fc_steps; exact hret_gt ng2 scr2 m2' hlen2 hng2 hpref2 hseq2 hm2'
              · have heq2 := hng_eq_of_not_gt ng2 hng2 hc; subst heq2
                fc_let; exact hJa () m2' ⟨scr2, hlen2, hpref2, hseq2, hm2'⟩
          · fc_let; exact hJa () m0 ⟨scr_c, hlen_c, hpref_c, hseq_c, hm_c⟩
      · -- Entry: canonical XOR filter + 3-way `full_has_ternary` check
        intro J hJ
        have hj0 : J () m0 := hJ () m0 rfl
        -- `((a & 1) == 0 || a == mx) && ((b & 1) == 0 || b == mx) && ((c & 1) == 0 || c == mx)`
        fc_to_group
        refine wp_join_group (ts := []) (fun () m_a => m_a = m0) ?_ ?_
        · rintro _ ⟨⟩ m_a hma; subst m_a
          fc_to_group
          refine wp_join_group (ts := []) (fun () m_b => m_b = m0) ?_ ?_
          · rintro _ ⟨⟩ m_b hmb; subst m_b
            fc_to_group
            refine wp_join_group (ts := []) (fun () m_c => m_c = m0) ?_ ?_
            · rintro _ ⟨⟩ m_c hmc; subst m_c
              fc_steps; c0_call hHasTern
              refine ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hcl0, ha_lt, hm0, fun ok1 hok1 => ?_⟩
              fc_split
              · have ht1 : (cnfOfClauses F_cur).EntailsClause
                    (cnfClause [a.toNat, litNeg b.toNat, litNeg cl.toNat]) := by
                  simpa only [bv32_xor1_litNeg] using hok1 (by grind)
                    (hdis_lit _ _ (div2_ne_of_xor1 hab_v)) (hdis_lit _ _ (div2_ne_of_xor1 hac_v))
                    (hdis_lit _ _ (div2_ne_of_xor1_both hbc_v))
                fc_steps; c0_call hHasTern
                refine ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hcl0, hna_lt, hm0,
                  fun ok2 hok2 => ?_⟩
                fc_split
                · have ht2 : (cnfOfClauses F_cur).EntailsClause
                      (cnfClause [litNeg a.toNat, b.toNat, litNeg cl.toNat]) := by
                    simpa only [bv32_xor1_litNeg] using hok2 (by grind)
                      (hdis_lit _ _ (div2_ne_of_xor1_l hab_v))
                      (hdis_lit _ _ (div2_ne_of_xor1_both hac_v))
                      (hdis_lit _ _ (div2_ne_of_xor1 hbc_v))
                  fc_steps; c0_call hHasTern
                  refine ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hcl0, hna_lt, hm0,
                    fun ok3 hok3 => ?_⟩
                  fc_split
                  · have ht3 : (cnfOfClauses F_cur).EntailsClause
                        (cnfClause [litNeg a.toNat, litNeg b.toNat, cl.toNat]) := by
                      simpa only [bv32_xor1_litNeg] using hok3 (by grind)
                        (hdis_lit _ _ (div2_ne_of_xor1_both hab_v))
                        (hdis_lit _ _ (div2_ne_of_xor1_l hac_v))
                        (hdis_lit _ _ (div2_ne_of_xor1_l hbc_v))
                    obtain ⟨hx1, hx2, hx3⟩ := xorGateDef_of_four hcl0_ent ht1 ht2 ht3
                    fc_split
                    · have h12 : g_len.toNat + 12 ≤ g_cap.toNat := by bv_omega
                      have hg4 : (g_len + 4#64).toNat = g_len.toNat + 4 := by bv_omega
                      have hg8 : (g_len + 4#64 + 4#64).toNat = g_len.toNat + 8 := by bv_omega
                      have hg12 : (g_len + 4#64 + 4#64 + 4#64).toNat = g_len.toNat + 12 := by
                        bv_omega
                      fc_steps; c0_call hEmitXor
                      refine ⟨F_cur, s.core.cur_vars, s.scratch.scratch_buf, FullScrBufRest c s ⋆ R,
                        ha_lt, hb_lt, hc_lt, by omega, by omega, by omega, hx1, hseq0,
                        focus_full_scratch_buf hm0, fun scr1 m1 hlen1 hpref1 hseq1 hm1 => ?_⟩
                      fc_steps; c0_call hEmitXor
                      refine ⟨F_cur, s.core.cur_vars, scr1, FullScrBufRest c s ⋆ R,
                        hb_lt, ha_lt, hc_lt, by omega, by omega, by omega, hx2, hg4 ▸ hseq1, hm1,
                        fun scr2 m2 hlen2 hpref2 hseq2 hm2 => ?_⟩
                      fc_steps; c0_call hEmitXor
                      refine ⟨F_cur, s.core.cur_vars, scr2, FullScrBufRest c s ⋆ R,
                        hc_lt, ha_lt, hb_lt, by omega, by omega, by omega, hx3,
                        by rw [hg8]; simpa [hg4, Nat.add_assoc] using hseq2, hm2,
                        fun scr3 m3 hlen3 hpref3 hseq3 hm3 => ?_⟩
                      fc_steps
                      exact hQ (g_len + 4#64 + 4#64 + 4#64) scr3 m3 (by omega) (by omega) (by omega)
                        (fun idx hi => (hpref3 idx (by omega)).trans
                          ((hpref2 idx (by omega)).trans (hpref1 idx hi)))
                        (by rw [hg12]; simpa [hg8, Nat.add_assoc] using hseq3)
                        (unfocus_full_scratch_buf hm3)
                    · fc_steps
                      exact hQ g_len s.scratch.scratch_buf m0 hscrl (Nat.le_refl _) (by omega)
                        (fun _ _ => rfl) hseq0 hm0
                  · fc_steps; exact hj0
                · fc_steps; exact hj0
              · fc_steps; exact hj0
            · intro Jc hJc; fc_split_fast
              · fc_let; exact hJc () m0 rfl
              · fc_split_fast
                · fc_let; exact hJc () m0 rfl
                · fc_let; exact hj0
          · intro Jb hJb; fc_split_fast
            · fc_let; exact hJb () m0 rfl
            · fc_split_fast
              · fc_let; exact hJb () m0 rfl
              · fc_let; exact hj0
        · intro Ja hJa; fc_split_fast
          · fc_let; exact hJa () m0 rfl
          · fc_split_fast
            · fc_let; exact hJa () m0 rfl
            · fc_let; exact hj0
    · intro Jmx hJmx; fc_split_fast <;> (fc_let; exact hJmx (_, ()) m0 rfl)
  · intro Jmx0 hJmx0; fc_split_fast <;> (fc_let; exact hJmx0 (_, ()) m0 rfl)

/-- **#5 (`full_cong_extract`)**: widens AND extraction to `sz <= 32` (`arity <= 31`) and removes
early `break`, extracting all valid AND LHSs + ternary XOR/ITE gates into `GateSeqOk32`. -/
theorem m5_cong_extract_wp (Γ : Env)
    (hNext : ∀ args m Q X, fullArenaNextSpec args m Q X →
      Γ "full_arena_next" [i64, i32] [i32] args m Q X)
    (hHasBin : ∀ args m Q X, fullHasBinSpec args m Q X →
      Γ "full_has_bin" [i64, i32, i32] [.bool] args m Q X)
    (hTryXorIte : ∀ args m Q X, m5CongTryXorIteSpec args m Q X →
      Γ "full_cong_try_xor_ite" [i64, i32, i32, i32, i64, i64] [i64] args m Q X) :
    ∀ args m Q X, m5CongExtractSpec args m Q X →
      Func.wp Γ full_cong_extract_body args m Q X := by
  rintro ⟨h, g_cap, _tick_lim, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hnd, hcl0, hgc_le, hm0, hQ⟩
  have hac := c.harena; have hsc := c.hscr; have hmx := c.hmaxv
  unfold dimacsBound at hac hsc hmx; have hcl := hlen.core_ok; have hsl := hlen.scratch_ok
  have harl := hcl.arena_len_arr; have hale := hcl.arena_len_le; have hscrl := hsl.scratch_buf_len
  fc_steps; refine wp_loop_inv
    (fun (p, g_len, _ticks, ()) ml => ∃ scr : List (BitVec 32),
      scr.length = c.scratch_cap ∧
      p.toNat ≤ s.core.arena_len ∧
      (p.toNat = s.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs s) ∧
      g_len.toNat ≤ g_cap.toNat ∧
      GateSeqOk32 F_cur s.core.cur_vars scr g_len.toNat 0 ∧
      (FullMem c { s with scratch := { s.scratch with scratch_buf := scr } } ⋆ R) ml)
    (fun (p, _, _, ()) _ => s.core.arena_len - p.toNat)
    (fun J hJ => by
      fc_let
      refine hJ (0#64, 0#64, 0#64, ()) m0 ⟨s.scratch.scratch_buf, hscrl, Nat.zero_le _, ?_,
        Nat.zero_le _, .done, hm0⟩
      rcases Nat.eq_zero_or_pos s.core.arena_len with hz | hpos
      · exact Or.inl hz.symm
      · exact Or.inr (fullArenaClauseRefs_zero_mem hw hpos))
    (fun J (p, g_len, ticks, ()) ml ⟨scr, hscrl_c, hp_le, hp_mem, hgl_le, hseq_c, hml⟩ ih => ?_)
  let sc : FullState := { s with scratch := { s.scratch with scratch_buf := scr } }
  have hlen_c : sc.LengthsOk c :=
    ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hscrl_c }⟩
  have hq_out : Q (g_len, ()) ml := hQ g_len scr ml hscrl_c hgl_le hseq_c hml; fc_split_fast
  · have hp_lt : p.toNat < s.core.arena_len := by
      simp only [BitVec.ult, decide_eq_true_eq] at hc; bv_omega
    fc_split_fast
    · have hgl34 : g_len.toNat + 34 ≤ g_cap.toNat := by
        simp only [BitVec.ule, decide_eq_true_eq] at hc; bv_omega
      fc_split_fast
      · have hp_ref : p.toNat ∈ fullArenaClauseRefs s := hp_mem.resolve_left (by omega)
        have hp_wf := hw.arena.refs_wf p.toNat hp_ref
        have hp2_n : (p + 2).toNat = p.toNat + 2 :=
          show (p.toNat + 2) % 2 ^ 64 = p.toNat + 2 from Nat.mod_eq_of_lt (by omega)
        have hp_arr : p.toNat < s.core.arena.length := by omega
        have hp2_arr : (p + 2).toNat < s.core.arena.length := by omega
        fc_steps; c0_call hNext; refine ⟨c, sc, R, rfl, hlen_c, hml, ?_⟩
        have hp_tr : (p.setWidth 32).toNat = p.toNat := by
          rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
        have hnp_bd := fullArenaNextOff_bounds (ar := s.core.arena) (alen := s.core.arena_len)
          (cref := p.toNat) hp_wf.1
        let np_bv := (BitVec.ofNat 32 (fullArenaNextOff s.core.arena s.core.arena_len
          (p.setWidth 32).toNat)).setWidth 64
        have hnp_n : np_bv.toNat = fullArenaNextOff s.core.arena s.core.arena_len p.toNat := by
          dsimp only [np_bv]; rw [hp_tr, bv_zext32_toNat, bv32_ofNat_toNat (by omega)]
        have hnp_mem : np_bv.toNat = s.core.arena_len ∨
            np_bv.toNat ∈ fullArenaClauseRefs s := by
          rw [hnp_n]; exact fullArenaClauseRefs_next_or_end hw hp_ref
        fc_to_group; refine wp_join_group (ts := [i64, i64])
          (fun (g_len_n, _ticks_n, ()) mn => ∃ scr_n : List (BitVec 32),
            scr_n.length = c.scratch_cap ∧ g_len_n.toNat ≤ g_cap.toNat ∧
            GateSeqOk32 F_cur s.core.cur_vars scr_n g_len_n.toNat 0 ∧
            (FullMem c { s with scratch := { s.scratch with scratch_buf := scr_n } } ⋆ R) mn)
          ?_ ?_
        · rintro _ ⟨g_len_n, ticks_n, ⟨⟩⟩ mn ⟨scr_n, hscrl_n, hgl_n, hseq_n, hmn⟩
          fc_let; exact ih (np_bv, g_len_n, ticks_n, ()) mn (by dsimp only; omega)
            ⟨scr_n, hscrl_n, by omega, hnp_mem, hgl_n, hseq_n, hmn⟩
        · intro Jnp hJnp
          have hjnp0 : Jnp (g_len, ticks + 1#64, ()) ml :=
            hJnp (g_len, ticks + 1#64, ()) ml ⟨scr, hscrl_c, hgl_le, hseq_c, hml⟩
          fc_split_fast
          · have hng_red := beq_iff_eq.mp hc; clear hc; fc_split_fast
            · have hsz3_bv : 3 ≤ (s.core.arena[(p + 2).toNat]'hp2_arr).toNat := by
                simp only [BitVec.ule, decide_eq_true_eq] at hc; exact hc
              clear hc; fc_split_fast
              · have hsz32_bv : (s.core.arena[(p + 2).toNat]'hp2_arr).toNat ≤ 32 := by
                  simp only [BitVec.ule, decide_eq_true_eq] at hc; exact hc
                clear hc
                have hng : fullArenaClauseGarb s p.toNat = false := by
                  unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
                  rw [List.getElem?_eq_getElem hp_arr, Option.getD_some]
                  exact garb_false_of_and_480000 hng_red
                let sz_bv := s.core.arena[(p + 2).toNat]'hp2_arr
                have hsz_bv_p2 : sz_bv = s.core.arena[p.toNat + 2]'(by omega) :=
                  list_getElem_congr hp2_n hp2_arr (by omega)
                have hsz_eq : sz_bv.toNat = fullArenaClauseSizeCore s.core p.toNat := by
                  unfold fullArenaClauseSizeCore
                  rw [hsz_bv_p2, List.getElem?_eq_getElem (by omega), Option.getD_some]
                have hsz3 : 3 ≤ sz_bv.toNat := hsz3_bv; have hsz32 : sz_bv.toNat ≤ 32 := hsz32_bv
                have har_bd : p.toNat + 3 + sz_bv.toNat ≤ s.core.arena.length := by omega
                have hszm1 : (sz_bv - 1#32).toNat = sz_bv.toNat - 1 := by bv_omega
                fc_to_group
                refine wp_loop_inv
                  (fun (g_li, i, ()) mi => ∃ scri : List (BitVec 32),
                    i.toNat ≤ sz_bv.toNat ∧
                    scri.length = c.scratch_cap ∧ g_li.toNat ≤ g_cap.toNat ∧
                    GateSeqOk32 F_cur s.core.cur_vars scri g_li.toNat 0 ∧
                    (FullMem c { s with scratch := { s.scratch with scratch_buf := scri } } ⋆ R) mi)
                  (fun (_, i, ()) _ => sz_bv.toNat - i.toNat)
                  (fun Ji hJi => by
                    fc_let
                    exact hJi (g_len, 0#32, ()) ml ⟨scr, Nat.zero_le _, hscrl_c, hgl_le, hseq_c,
                      hml⟩)
                  (fun Ji (g_li, i, ()) mi ⟨scri, hi_le, hscrli, hgli_le, hseqi, hmi⟩ ihi => ?_)
                let sci : FullState :=
                  { s with scratch := { s.scratch with scratch_buf := scri } }
                have hleni : sci.LengthsOk c :=
                  ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hscrli }⟩
                fc_to_group
                refine wp_join_group (ts := [])
                  (fun () mb => mb = mi)
                  (fun _ ⟨⟩ mb hmb => by
                    subst mb
                    have hjnp1 : Jnp (g_li, ticks + 1#64, ()) mi :=
                      hJnp (g_li, ticks + 1#64, ()) mi ⟨scri, hscrli, hgli_le, hseqi, hmi⟩
                    fc_to_group
                    refine wp_join_group (ts := [i64, i64]) (fun args mj => Jnp args mj)
                      (fun _ args mj h => by fc_let; exact h) ?_
                    intro J3 hJ3
                    have hj3_keep : J3 (g_li, ticks + 1#64, ()) mi :=
                      hJ3 (g_li, ticks + 1#64, ()) mi hjnp1
                    fc_split_fast
                    · have hsz_eq3 := beq_iff_eq.mp hc; clear hc; fc_split_fast
                      · have h14_le : g_li.toNat + 14 ≤ g_cap.toNat := by
                          simp only [BitVec.ule, decide_eq_true_eq] at hc; bv_omega
                        have hsz3_n : fullArenaClauseSizeCore s.core p.toNat = 3 := by
                          rw [← hsz_eq]; exact congrArg BitVec.toNat hsz_eq3
                        have hp3_n : (p + 3).toNat = p.toNat + 3 :=
                          show (p.toNat + 3) % 2 ^ 64 = p.toNat + 3 from Nat.mod_eq_of_lt (by omega)
                        have hp4_n : (p + 4).toNat = p.toNat + 4 :=
                          show (p.toNat + 4) % 2 ^ 64 = p.toNat + 4 from Nat.mod_eq_of_lt (by omega)
                        have hp5_n : (p + 5).toNat = p.toNat + 5 :=
                          show (p.toNat + 5) % 2 ^ 64 = p.toNat + 5 from Nat.mod_eq_of_lt (by omega)
                        have hlits3 := arena_clause3_lits (k := s.core) (cr := p.toNat) hsz3_n
                          (by omega)
                        have hcl3 := hw.arena.entails p.toNat hp_ref hng
                        have hnd3 := hnd p.toNat hp_ref hng
                        have hlt3 := hw.arena.lits_lt p.toNat hp_ref hng
                        unfold fullArenaClauseLits at hnd3; rw [hlits3] at hcl3 hnd3 hlt3
                        simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
                          List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hnd3
                        have hl3 : s.core.arena[(p + 3).toNat]'(by omega) =
                            s.core.arena[p.toNat + 3]'(by omega) :=
                          list_getElem_congr hp3_n (by omega) (by omega)
                        have hl4 : s.core.arena[(p + 4).toNat]'(by omega) =
                            s.core.arena[p.toNat + 4]'(by omega) :=
                          list_getElem_congr hp4_n (by omega) (by omega)
                        have hl5 : s.core.arena[(p + 5).toNat]'(by omega) =
                            s.core.arena[p.toNat + 5]'(by omega) :=
                          list_getElem_congr hp5_n (by omega) (by omega)
                        fc_steps; c0_call hTryXorIte
                        refine ⟨c, F0, F_cur, sci, R, rfl, hleni, hw, hnd, hcl0,
                          by rw [hl3]; exact hlt3 _ (by simp),
                          by rw [hl4]; exact hlt3 _ (by simp),
                          by rw [hl5]; exact hlt3 _ (by simp),
                          by rw [hl3, hl4]; exact hnd3.1.1,
                          by rw [hl3, hl5]; exact hnd3.1.2,
                          by rw [hl4, hl5]; exact hnd3.2.1,
                          by rw [hl3, hl4, hl5]; exact hcl3,
                          by omega, hgc_le, hseqi, hmi,
                          fun ret scr2 m2 hlen2 _ hret_le _ hseq2 hm2 => ?_⟩
                        fc_let
                        exact hJ3 (ret, ticks + 1#64 + 4#64, ()) m2
                          (hJnp (ret, ticks + 1#64 + 4#64, ()) m2
                            ⟨scr2, hlen2, hret_le, hseq2, hm2⟩)
                      · fc_let; exact hj3_keep
                    · fc_let; exact hj3_keep)
                  ?_
                intro Jexit hJexit
                fc_split_fast
                · have hi_lt : i.toNat < sz_bv.toNat := by
                    simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                  clear hc; fc_split_fast
                  · have hgl_fit : g_li.toNat + 2 + (sz_bv.toNat - 1) ≤ g_cap.toNat := by
                      have hgl_add : (g_li + 2#64 + (sz_bv - 1#32).setWidth 64).toNat =
                          g_li.toNat + 2 + (sz_bv.toNat - 1) := by
                        rw [bv64_add_zext32 (k := 2) (by omega), hszm1]
                      have hle : (g_li + 2#64 + (sz_bv - 1#32).setWidth 64).toNat ≤
                          g_cap.toNat := by
                        simp only [BitVec.ule, decide_eq_true_eq] at hc; exact hc
                      omega
                    have hp3i_n : (p + 3 + i.setWidth 64).toNat = p.toNat + 3 + i.toNat :=
                      bv64_add_zext32 (k := 3) (by omega)
                    have hp3i_arr : (p + 3 + i.setWidth 64).toNat < s.core.arena.length := by omega
                    let lhs := s.core.arena[(p + 3 + i.setWidth 64).toNat]'hp3i_arr
                    have hlhs_eq : s.core.arena[(p + 3 + i.setWidth 64).toNat]'hp3i_arr =
                        s.core.arena[p.toNat + 3 + i.toNat]?.getD 0#32 := by
                      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                      exact list_getElem_congr hp3i_n hp3i_arr (by omega)
                    have hi1 : (i + 1#32).toNat = i.toNat + 1 :=
                      show (i.toNat + 1) % 2 ^ 32 = i.toNat + 1 from Nat.mod_eq_of_lt (by omega)
                    fc_to_group
                    refine wp_loop_break_group (brkTs := [.bool, i32]) (lpTs := [i32])
                      (fun (ok, _, ()) mb2 => mb2 = mi ∧
                        (ok = true → ∀ k < sz_bv.toNat, k ≠ i.toNat →
                          (cnfOfClauses F_cur).EntailsClause (cnfClause
                            [litNeg (s.core.arena[p.toNat + 3 + i.toNat]?.getD 0#32).toNat,
                             litNeg (s.core.arena[p.toNat + 3 + k]?.getD 0#32).toNat])))
                      (fun rem2 (j, ()) mj => mj = mi ∧ j.toNat ≤ sz_bv.toNat ∧
                        rem2 = sz_bv.toNat - j.toNat ∧
                        ∀ k < j.toNat, k ≠ i.toNat →
                          (cnfOfClauses F_cur).EntailsClause (cnfClause
                            [litNeg (s.core.arena[p.toNat + 3 + i.toNat]?.getD 0#32).toNat,
                             litNeg (s.core.arena[p.toNat + 3 + k]?.getD 0#32).toNat]))
                      ?_ ?_ ?_
                    · rintro _ ⟨ok, j_brk, ⟨⟩⟩ mb2 ⟨hmb2, hok⟩
                      subst mb2
                      fc_to_group
                      refine wp_join_group (ts := [i64, i32])
                        (fun (g_li', _, ()) mn => ∃ scri' : List (BitVec 32),
                          scri'.length = c.scratch_cap ∧ g_li'.toNat ≤ g_cap.toNat ∧
                          GateSeqOk32 F_cur s.core.cur_vars scri' g_li'.toNat 0 ∧
                          (FullMem c { s with scratch :=
                            { s.scratch with scratch_buf := scri' } } ⋆ R) mn)
                        ?_ ?_
                      · rintro _ ⟨g_li', _, ⟨⟩⟩ mn ⟨scri', hscrl', hgli', hseq', hmn⟩
                        fc_let; exact ihi (g_li', i + 1#32, ()) mn (by dsimp only; omega)
                          ⟨scri', by omega, hscrl', hgli', hseq', hmn⟩
                      · intro Jok hJok
                        fc_split_fast
                        · have hbins := hok hc
                          clear hc hok hNext hHasBin hTryXorIte hQ ih hJnp hjnp0 hq_out hJexit
                          have hi32 : i32.bytes = 4 := rfl
                          have hg1 : (g_li + 1).toNat = g_li.toNat + 1 :=
                            show (g_li.toNat + 1) % 2 ^ 64 = g_li.toNat + 1 from
                              Nat.mod_eq_of_lt (by omega)
                          have hgl_next : (g_li + 2#64 + (sz_bv - 1#32).setWidth 64).toNat =
                              g_li.toNat + 2 + (sz_bv.toNat - 1) := by
                            rw [bv64_add_zext32 (k := 2) (by omega), hszm1]
                          have hfs := focus_full_scratch_buf hmi; clear hmi
                          generalize hR_scr : FullScrBufRest c sci ⋆ R = R_scr at hfs
                          have hg0_lt : g_li.toNat < scri.length := by omega
                          have hg1_lt : (g_li + 1).toNat < scri.length := by omega
                          fc_steps; let scr_h0 := scri.set g_li.toNat lhs
                          let scr_h1 := scr_h0.set (g_li.toNat + 1) (sz_bv - 1#32)
                          have hm_h1 : (array (t := i32) c.pScratchBuf scr_h1 ⋆ R_scr) m := by
                            rw [hg1] at hm; exact hm
                          have hm_h1_full : (FullMem c { s with scratch :=
                              { s.scratch with scratch_buf := scr_h1 } } ⋆ R) m := by
                            subst hR_scr; exact unfocus_full_scratch_buf hm_h1
                          let ScrWOk (n : Nat) (scrw : List (BitVec 32)) (mj : Mem 64) : Prop :=
                            scrw.length = c.scratch_cap ∧
                            (∀ idx < g_li.toNat, scrw[idx]? = scri[idx]?) ∧
                            scrw[g_li.toNat]? = some lhs ∧
                            scrw[g_li.toNat + 1]? = some (sz_bv - 1#32) ∧
                            (∀ k < n, k ≠ i.toNat →
                              scrw[g_li.toNat + 2 + (if k < i.toNat then k else k - 1)]? =
                                some ((s.core.arena[p.toNat + 3 + k]?.getD 0#32) ^^^ 1#32)) ∧
                            (FullMem c { s with scratch :=
                              { s.scratch with scratch_buf := scrw } } ⋆ R) mj
                          clear hm hm_h1; refine wp_loop_inv
                            (fun (j2, rk, ()) mj2 => ∃ scrw : List (BitVec 32),
                              j2.toNat ≤ sz_bv.toNat ∧
                              rk.toNat = (if j2.toNat ≤ i.toNat then j2.toNat else j2.toNat - 1) ∧
                              ScrWOk j2.toNat scrw mj2)
                            (fun (j2, _, ()) _ => sz_bv.toNat - j2.toNat)
                            (fun Jw hJw => by
                              fc_let; refine hJw (0#32, 0#32, ()) m
                                ⟨scr_h1, Nat.zero_le _, by simp,
                                 by simp [scr_h1, scr_h0, hscrli],
                                 fun idx hi => by
                                   simp only [scr_h1, scr_h0]
                                   repeat rw [List.getElem?_set_ne (by omega)],
                                 by simp only [scr_h1, scr_h0]
                                    rw [List.getElem?_set_ne (by omega),
                                      List.getElem?_set_self (by omega)],
                                 by simp only [scr_h1, scr_h0]
                                    rw [List.getElem?_set_self (by simp [hscrli]; omega)],
                                 fun _ hk => by simp at hk, hm_h1_full⟩)
                            (fun Jw (j2, rk, ()) mj2
                              ⟨scrw, hj2_le, hrk_eq, hscrlw, hprefw, hw0, hw1, hwrhs, hmj2⟩ ihw =>
                              ?_)
                          fc_split_fast
                          · have hj2_lt : j2.toNat < sz_bv.toNat := by
                              simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                            have hj21 : (j2 + 1#32).toNat = j2.toNat + 1 :=
                              show (j2.toNat + 1) % 2 ^ 32 = j2.toNat + 1 from
                                Nat.mod_eq_of_lt (by omega)
                            fc_to_group; refine wp_join_group (ts := [i32])
                              (fun (rk', ()) mj2' => ∃ scrw' : List (BitVec 32),
                                rk'.toNat = (if j2.toNat + 1 ≤ i.toNat then j2.toNat + 1
                                  else j2.toNat) ∧ ScrWOk (j2.toNat + 1) scrw' mj2')
                              ?_ ?_
                            · rintro _ ⟨rk', ⟨⟩⟩ mj2' ⟨scrw', h2, h1, h3, h4, h5, h6, h7⟩
                              fc_let; exact ihw (j2 + 1#32, rk', ()) mj2' (by dsimp only; omega)
                                ⟨scrw', by omega, by rw [hj21]; exact h2, h1, h3, h4, h5,
                                 by rw [hj21]; exact h6, h7⟩
                            · intro Jif hJif; fc_split_fast
                              · have hj2i : j2.toNat ≠ i.toNat := fun h =>
                                  (bne_iff_ne.mp hc) (BitVec.eq_of_toNat_eq h)
                                have hrk_pos_eq : rk.toNat =
                                    (if j2.toNat < i.toNat then j2.toNat else j2.toNat - 1) := by
                                  rw [hrk_eq]; split <;> split <;> omega
                                have hrk_lt31 : rk.toNat < sz_bv.toNat - 1 := by
                                  rw [hrk_pos_eq]; split <;> omega
                                have hp3j_n : (p + 3 + j2.setWidth 64).toNat =
                                    p.toNat + 3 + j2.toNat :=
                                  bv64_add_zext32 (k := 3) (by omega)
                                have hp3j_arr : (p + 3 + j2.setWidth 64).toNat <
                                    s.core.arena.length := by omega
                                have hdst_n : (g_li + 2 + rk.setWidth 64).toNat =
                                    g_li.toNat + 2 + rk.toNat := bv64_add_zext32 (k := 2) (by omega)
                                have hdst_lt : (g_li + 2 + rk.setWidth 64).toNat < scrw.length := by
                                  omega
                                have hrk1 : (rk + 1#32).toNat = rk.toNat + 1 :=
                                  show (rk.toNat + 1) % 2 ^ 32 = rk.toNat + 1 from
                                    Nat.mod_eq_of_lt (by omega)
                                fc_let; fc_step; have hfs_w := focus_full_scratch_buf hmj2
                                clear hmj2
                                generalize hR_w : FullScrBufRest c { s with scratch :=
                                  { s.scratch with scratch_buf := scrw } } ⋆ R = R_w at hfs_w
                                fc_steps; subst hR_w
                                let val_j :=
                                  (s.core.arena[(p + 3 + j2.setWidth 64).toNat]'hp3j_arr) ^^^ 1#32
                                have hval_j : val_j =
                                    (s.core.arena[p.toNat + 3 + j2.toNat]?.getD 0#32) ^^^ 1#32 := by
                                  dsimp only [val_j]; congr 1
                                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                                  exact list_getElem_congr hp3j_n hp3j_arr (by omega)
                                let scrw' := scrw.set (g_li.toNat + 2 + rk.toNat) val_j
                                have hm_w' : (FullMem c { s with scratch :=
                                    { s.scratch with scratch_buf := scrw' } } ⋆ R) m := by
                                  rw [hdst_n] at hm; exact unfocus_full_scratch_buf hm
                                refine hJif (rk + 1#32, ()) m
                                  ⟨scrw', by rw [hrk1, hrk_eq]; split <;> split <;> omega,
                                   by rw [List.length_set]; exact hscrlw,
                                   fun idx hi => by
                                     rw [List.getElem?_set_ne (by omega)]; exact hprefw idx hi,
                                   by rw [List.getElem?_set_ne (by omega)]; exact hw0,
                                   by rw [List.getElem?_set_ne (by omega)]; exact hw1,
                                   fun k hk hkne => ?_, hm_w'⟩
                                by_cases hkj : k = j2.toNat
                                · subst hkj; rw [← hrk_pos_eq]
                                  simp only [scrw']; rw [List.getElem?_set_self (by omega), hval_j]
                                · have hne_slot : (if k < i.toNat then k else k - 1) ≠ rk.toNat :=
                                      by
                                    rw [hrk_pos_eq]; split <;> split <;> omega
                                  simp only [scrw']; rw [List.getElem?_set_ne (by omega)]
                                  exact hwrhs k (by omega) hkne
                              · have hj2i : j2.toNat = i.toNat :=
                                  congrArg BitVec.toNat (by simpa using hc : j2 = i)
                                fc_let; exact hJif (rk, ()) mj2
                                  ⟨scrw, by rw [hrk_eq]; split <;> split <;> omega,
                                   hscrlw, hprefw, hw0, hw1,
                                   fun k hk hkne => hwrhs k (by omega) hkne, hmj2⟩
                          · have hj2_e : j2.toNat = sz_bv.toNat := by
                              simp only [BitVec.ult, decide_eq_false_iff_not] at hc
                              change ¬j2.toNat < sz_bv.toNat at hc; omega
                            rw [hj2_e] at hwrhs
                            have hsz_bv_eq : sz_bv - 1#32 = BitVec.ofNat 32 (sz_bv.toNat - 1) := by
                              apply BitVec.eq_of_toNat_eq; rw [hszm1, bv32_ofNat_toNat (by omega)]
                            have hgat := andGate32_of_emitted hlen hw hnd hp_ref hng hsz_eq.symm
                              hsz3 hsz32 hi_lt hbins hscrlw (by omega) (hlhs_eq ▸ hw0)
                              (hsz_bv_eq ▸ hw1) hwrhs
                            have hseq_new : GateSeqOk32 F_cur s.core.cur_vars scrw
                                (g_li + 2#64 + (sz_bv - 1#32).setWidth 64).toNat 0 := by
                              rw [hgl_next]; refine gateSeqOk32_append (by omega) hprefw ?_ hseqi
                              refine .step hgat ?_
                              have hmword_ar : ((sz_bv - 1#32) &&& 0xFF#32).toNat =
                                  sz_bv.toNat - 1 := by
                                rw [BitVec.toNat_and, hszm1,
                                  show (0xFF#32 : BitVec 32).toNat = 255 from rfl]
                                simpa [Nat.mod_eq_of_lt (show sz_bv.toNat - 1 < 256 by omega)] using
                                  Nat.and_two_pow_sub_one_eq_mod (sz_bv.toNat - 1) 8
                              simpa [hw1, hmword_ar] using GateSeqOk32.done
                            fc_let
                            exact hJok (g_li + 2#64 + (sz_bv - 1#32).setWidth 64, j2, ()) mj2
                              ⟨scrw, hscrlw, by omega, hseq_new, hmj2⟩
                        · fc_let
                          exact hJok (g_li, j_brk, ()) mi ⟨scri, hscrli, hgli_le, hseqi, hmi⟩
                    · rintro B2 L2 rem2 ⟨j, ⟨⟩⟩ mj hB2 hL2 ⟨hmj, hj_le, rfl, hseen⟩
                      subst mj; fc_split_fast
                      · have hj_lt : j.toNat < sz_bv.toNat := by
                          simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                        have hj1 : (j + 1#32).toNat = j.toNat + 1 :=
                          show (j.toNat + 1) % 2 ^ 32 = j.toNat + 1 from Nat.mod_eq_of_lt (by omega)
                        fc_to_group; refine wp_join_group (ts := [])
                          (fun () m_j => m_j = mi ∧
                            ∀ k < (j + 1#32).toNat, k ≠ i.toNat →
                              (cnfOfClauses F_cur).EntailsClause (cnfClause
                                [litNeg (s.core.arena[p.toNat + 3 + i.toNat]?.getD 0#32).toNat,
                                 litNeg (s.core.arena[p.toNat + 3 + k]?.getD 0#32).toNat]))
                          ?_ ?_
                        · rintro _ ⟨⟩ m_j ⟨hmj', hseen'⟩; subst m_j; fc_let
                          exact hL2 (sz_bv.toNat - (j + 1#32).toNat) (j + 1#32, ()) mi (by omega)
                            ⟨rfl, by omega, rfl, hseen'⟩
                        · intro Jj hJj
                          fc_let; refine ⟨fun hne => ?_, fun heq => ?_⟩
                          · have hji : j.toNat ≠ i.toNat := fun h =>
                              (bne_iff_ne.mp hne) (BitVec.eq_of_toNat_eq h)
                            have hp3j_n : (p + 3 + j.setWidth 64).toNat = p.toNat + 3 + j.toNat :=
                              bv64_add_zext32 (k := 3) (by omega)
                            have hp3j_arr : (p + 3 + j.setWidth 64).toNat <
                                s.core.arena.length := by omega
                            fc_steps; c0_call hHasBin
                            refine ⟨c, F0, F_cur, sci, R, rfl, hleni, hw, hmi, fun hb hhb => ?_⟩
                            fc_let; refine ⟨fun hbt => ?_, fun _ => ?_⟩
                            · have hnew : (cnfOfClauses F_cur).EntailsClause (cnfClause
                                  [litNeg (s.core.arena[p.toNat + 3 + i.toNat]?.getD 0#32).toNat,
                                   litNeg (s.core.arena[p.toNat + 3 + j.toNat]?.getD
                                     0#32).toNat]) :=
                                by
                                have h := (hhb hbt).2.2.2.2
                                have hget_j :
                                    s.core.arena[(p + 3 + j.setWidth 64).toNat]'hp3j_arr =
                                      s.core.arena[p.toNat + 3 + j.toNat]?.getD 0#32 := by
                                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
                                  exact list_getElem_congr hp3j_n hp3j_arr (by omega)
                                simpa only [bv32_xor1_litNeg, hlhs_eq, hget_j] using h
                              fc_let
                              exact hJj () mi ⟨rfl, fun k hk hkne => by
                                rw [hj1] at hk
                                by_cases hkj : k = j.toNat
                                · subst hkj; exact hnew
                                · exact hseen k (by omega) hkne⟩
                            · fc_let; exact hB2 (false, j, ()) mi ⟨rfl, fun h => by cases h⟩
                          · have hji : j.toNat = i.toNat := by
                              have : j = i := by simpa using heq
                              exact congrArg BitVec.toNat this
                            fc_let; exact hJj () mi ⟨rfl, fun k hk hkne => hseen k (by omega) hkne⟩
                      · have hj_e : j.toNat = sz_bv.toNat := by
                          simp only [BitVec.ult, decide_eq_false_iff_not] at hc
                          change ¬j.toNat < sz_bv.toNat at hc; omega
                        rw [hj_e] at hseen; fc_let; exact hB2 (true, j, ()) mi ⟨rfl, fun _ => hseen⟩
                    · intro _ L2 _ hL2; fc_let
                      exact hL2 (sz_bv.toNat - 0) (0#32, ()) mi
                        ⟨rfl, Nat.zero_le _, rfl, fun _ h => by simp at h⟩
                  · fc_let; exact hJexit () mi rfl
                · fc_let; exact hJexit () mi rfl
              · fc_let; exact hjnp0
            · fc_let; exact hjnp0
          · fc_let; exact hjnp0
      · fc_let; exact hq_out
    · fc_let; exact hq_out
  · fc_let; exact hq_out

/-- **#6 (`full_cong_and_match`)**: widened `u32` bitmask matching (`2 ≤ ua ≤ 31`) against
`GateAt32`. -/
theorem m5_cong_and_match_wp (Γ : Env)
    (hFind : ∀ a m Q X, fullCongFindSpec a m Q X →
      Γ "full_cong_find" [i64, i32] [i32] a m Q X) :
    ∀ a m Q X, m5CongAndMatchSpec a m Q X →
      Func.wp Γ full_cong_and_match_body a m Q X := by
  rintro ⟨h, ent, ua, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, scr0, g_len, R, rfl, hlen, hw, hcl0, hrepr0, hg_cap, hpref,
     hgat, htag0, hua_cv, hm0, hQ⟩
  have hsc := c.hscr; have hmx := c.hmaxv; unfold dimacsBound at hsc hmx
  have hcv_le := hlen.core_ok.cur_vars_le
  have hrl0 := hlen.core_ok.repr_len
  have htmpl0 := hlen.core_ok.tmp_len_arr
  have hscrl0 := hlen.scratch_ok.scratch_buf_len
  obtain ⟨lhs_ent, mword, he0, he1, _, hbd_e, _, _, hrhs_e, hsem_e⟩ := hgat
  have htag0' : (mword >>> 28).toNat = 0 := by
    rw [he1, Option.getD_some] at htag0; simpa using congrArg BitVec.toNat htag0
  obtain ⟨_, ha2_e, hand_e⟩ | ⟨ht_ne, _⟩ | ⟨ht_ne, _⟩ := hsem_e <;> (try omega)
  let ea := mword &&& 0xFF#32
  have hea_eq : ea.toNat = (mword &&& 0xFF#32).toNat := rfl
  let rhs := ((scr0.drop (ent.toNat + 2)).take ea.toNat).map BitVec.toNat
  have hrl_rhs : rhs.length = ea.toNat := by
    simp only [rhs, List.length_map, List.length_take, List.length_drop]
    rcases Nat.eq_zero_or_pos ea.toNat with hz | hpos
    · exact Nat.min_eq_left (by omega)
    · obtain ⟨_, hr, _⟩ := hrhs_e (ea.toNat - 1) (by omega)
      have := (List.getElem?_eq_some_iff.mp hr).1; omega
  have he1_n : (ent.setWidth 64 + 1).toNat = ent.toNat + 1 := by
    rw [BitVec.toNat_add, bv_zext32_toNat]
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [h1]; exact Nat.mod_eq_of_lt (by omega)
  have he1_arr : (ent.setWidth 64 + 1).toNat < s.scratch.scratch_buf.length := by omega
  have hst_e1 : s.scratch.scratch_buf[(ent.setWidth 64 + 1).toNat]'he1_arr = mword := by
    have h := (hpref (ent.toNat + 1) (by omega)).trans he1
    rw [← he1_n, List.getElem?_eq_getElem he1_arr] at h; exact Option.some.inj h
  fc_split_fast
  · fc_steps; exact hQ false s.core.repr m0 hrl0 hrepr0 (fun h => by cases h) hm0
  · have h2_le_ua : 2 ≤ ua.toNat := by
      have h2_val : ((2 : BitVec 32).toNat) = 2 := rfl
      simp only [BitVec.ult, h2_val, decide_eq_false_iff_not] at hc; omega
    fc_split_fast
    · fc_steps; exact hQ false s.core.repr m0 hrl0 hrepr0 (fun h => by cases h) hm0
    · have hua_le_31 : ua.toNat ≤ 31 := by
        have h31_val : ((31 : BitVec 32).toNat) = 31 := rfl
        simp only [BitVec.ult, h31_val, decide_eq_false_iff_not] at hc; omega
      fc_steps
      refine wp_loop_inv
        (fun (mask, j, ()) mj => ∃ reprj : List (BitVec 32),
          reprj.length = 2 * c.max_vars ∧ j.toNat ≤ ea.toNat ∧
          FullCongReprInv F_cur (2 * s.core.cur_vars) reprj ∧
          (∀ p (hp : p < j.toNat), ∃ er < 2 * s.core.cur_vars,
            LitEquiv (cnfOfClauses F_cur) (rhs[p]?.getD 0) er ∧
            (s.core.vals[er]?.getD 0#8 = 1#8 ∨
              ∃ k < ua.toNat, er = (s.core.tmp[k]?.getD 0#32).toNat)) ∧
          (∀ b < 32, mask.toNat.testBit b = true → b < ua.toNat ∧
            ∃ p < j.toNat, LitEquiv (cnfOfClauses F_cur)
              (rhs[p]?.getD 0) (s.core.tmp[b]?.getD 0#32).toNat) ∧
          (FullMem c { s with core := { s.core with repr := reprj } } ⋆ R) mj)
        (fun (_, j, ()) _ => ea.toNat - j.toNat)
        (fun J hJ => by
          fc_let
          exact hJ (0#32, 0#32, ()) m0 ⟨s.core.repr, hrl0, Nat.zero_le _, hrepr0,
            fun _ h => absurd h (by simp), fun _ _ h => by simp at h, hm0⟩)
        (fun J (mask, j, ()) mj ⟨reprj, hrlj, hj_le, hreprj, hfwdj, hbwdj, hmj⟩ ihj => ?_)
      let stj : FullState := { s with core := { s.core with repr := reprj } }
      have hlenj : stj.LengthsOk c := ⟨{ hlen.core_ok with repr_len := hrlj }, hlen.scratch_ok⟩
      have hwj : FullWitnessInv c F0 F_cur stj.core := fullWitnessInv_with_repr hw reprj
      fc_split_fast
      · have hj_lt : j.toNat < ea.toNat := by
          simp only [BitVec.ult, decide_eq_true_eq] at hc; rw [hst_e1] at hc; exact hc
        obtain ⟨rv, hrv_get, hrv_lt⟩ := hrhs_e j.toNat hj_lt
        have hrhs_j : rhs[j.toNat]?.getD 0 = rv.toNat := by
          simp only [rhs, List.getElem?_map, List.getElem?_take,
            ite_eq_left (by omega : j.toNat < ea.toNat), List.getElem?_drop, hrv_get]
          rfl
        have he2j_n : (ent.setWidth 64 + 2 + j.setWidth 64).toNat = ent.toNat + 2 + j.toNat :=
          bv64_add_zext32 (k := 2) (by rw [bv_zext32_toNat]; omega)
        have he2j_arr : (ent.setWidth 64 + 2 + j.setWidth 64).toNat <
            stj.scratch.scratch_buf.length := by
          rw [he2j_n]; dsimp [stj]; omega
        have hst_e2j : stj.scratch.scratch_buf[(ent.setWidth 64 + 2 + j.setWidth 64).toNat]'
            he2j_arr = rv := by
          have h := (hpref (ent.toNat + 2 + j.toNat) (by omega)).trans hrv_get
          rw [← he2j_n, List.getElem?_eq_getElem he2j_arr] at h; exact Option.some.inj h
        have hj1_n : (j + 1#32).toNat = j.toNat + 1 := by bv_omega
        fc_steps; c0_call hFind
        refine ⟨F_cur, 2 * s.core.cur_vars, reprj, FullReprRest c stj ⋆ R, hreprj,
          by rw [hst_e2j]; exact hrv_lt, focus_full_repr hmj,
          fun er repr_e me hrl_e hrepr_e _ her_lt her_eqv hme => ?_⟩
        let ste : FullState := { stj with core := { stj.core with repr := repr_e } }
        have hme' : (FullMem c ste ⋆ R) me := unfocus_full_repr hme; clear hme
        have hw_e : FullWitnessInv c F0 F_cur ste.core := fullWitnessInv_with_repr hwj repr_e
        have her_vals : (er.setWidth 64).toNat < ste.core.vals.length := by
          rw [bv_zext32_toNat]; dsimp [ste, stj]; rw [hlen.core_ok.vals_len]; omega
        have her_vals' : er.toNat < ste.core.vals.length := by
          rw [bv_zext32_toNat] at her_vals; exact her_vals
        have hrv_er_eqv : LitEquiv (cnfOfClauses F_cur) (rhs[j.toNat]?.getD 0) er.toNat := by
          rw [hrhs_j]; rwa [hst_e2j] at her_eqv
        have hev_dom : ste.core.vals[er.toNat]'her_vals' = 0#8 ∨
            ste.core.vals[er.toNat]'her_vals' = 1#8 ∨
            ste.core.vals[er.toNat]'her_vals' = 0xFF#8 := by
          have hd := hw_e.vals_domain er.toNat her_lt
          rwa [List.getElem?_eq_getElem her_vals', Option.getD_some] at hd
        fc_split_fast
        · fc_steps
          exact hQ false repr_e me (by omega) hrepr_e (fun h => by cases h) hme'
        · have hev_nslt : ¬ (ste.core.vals[er.toNat]'her_vals').slt 0#8 = true :=
            bv8_not_slt0_of_signExtend32_nslt0 hev_dom (by
              rw [list_getElem_congr (bv_zext32_toNat er) her_vals her_vals'] at hc; exact hc)
          fc_split_fast
          · have hev_eq0 : s.core.vals[er.toNat]?.getD 0#8 = 0#8 := by
              have hv0 : ste.core.vals[er.toNat]'her_vals' = 0#8 :=
                bv8_eq0_of_signExtend32 hev_dom (by
                  have hc' := beq_iff_eq.mp hc
                  rw [list_getElem_congr (bv_zext32_toNat er) her_vals her_vals'] at hc'; exact hc')
              rw [List.getElem?_eq_getElem (by rw [hlen.core_ok.vals_len]; omega), Option.getD_some]
              exact hv0
            fc_to_group
            refine wp_loop_break_group (brkTs := [i32, .bool, i32]) (lpTs := [i32])
              (fun (mask_b, found, _, ()) mb => mb = me ∧
                (found = true → ∃ k < ua.toNat, er = (s.core.tmp[k]?.getD 0#32) ∧
                  ∀ b < 32, mask_b.toNat.testBit b = true → b < ua.toNat ∧
                    (b = k ∨ ∃ p < j.toNat, LitEquiv (cnfOfClauses F_cur)
                      (rhs[p]?.getD 0) (s.core.tmp[b]?.getD 0#32).toNat)))
              (fun rem (k, ()) mk => mk = me ∧ k.toNat ≤ ua.toNat ∧ rem = ua.toNat - k.toNat)
              ?_ ?_ ?_
            · rintro _ ⟨mask_b, found, _, ⟨⟩⟩ mb ⟨hmb_eq, hfb⟩
              subst mb
              fc_split_fast
              · obtain ⟨k, hk_lt, htmp_k, hmask_b⟩ := hfb hc
                fc_steps
                refine ihj (mask_b, j + 1#32, ()) me (by dsimp only; omega)
                  ⟨repr_e, by omega, by omega, hrepr_e, ?_, ?_, hme'⟩
                · intro p hp; rw [hj1_n] at hp
                  by_cases hpj : p = j.toNat
                  · subst hpj
                    refine ⟨er.toNat, her_lt, hrv_er_eqv, Or.inr ⟨k, hk_lt, ?_⟩⟩; rw [htmp_k]
                  · exact hfwdj p (by omega)
                · intro b hb htb
                  obtain ⟨hb_ua, hbk | ⟨p, hp, heq⟩⟩ := hmask_b b hb htb
                  · refine ⟨hb_ua, j.toNat, by omega, ?_⟩; subst hbk; rwa [← htmp_k]
                  · exact ⟨hb_ua, p, by omega, heq⟩
              · fc_steps; exact hQ false repr_e me (by omega) hrepr_e (fun h => by cases h) hme'
            · rintro Bk Lk rem ⟨k, ⟨⟩⟩ mk hBk hLk ⟨hmk_eq, hk_le, rfl⟩
              subst mk; fc_split_fast
              · have hk_lt : k.toNat < ua.toNat := by
                  simp only [BitVec.ult, decide_eq_true_eq] at hc; exact hc
                have hk_tmp : (k.setWidth 64).toNat < ste.core.tmp.length := by
                  rw [bv_zext32_toNat]; dsimp [ste, stj]; omega
                have hk_tmp' : k.toNat < ste.core.tmp.length := by
                  rw [bv_zext32_toNat] at hk_tmp; exact hk_tmp
                have hk1_n : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
                fc_split_fast
                · have htmp_eq : s.core.tmp[k.toNat]?.getD 0#32 = er := by
                    have h1 : ste.core.tmp[k.toNat]'hk_tmp' = er := by
                      have hc' := beq_iff_eq.mp hc
                      rw [list_getElem_congr (bv_zext32_toNat k) hk_tmp hk_tmp'] at hc'; exact hc'
                    change s.core.tmp[k.toNat]'_ = er at h1
                    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; exact h1
                  have hk_31 : k.toNat < 31 := by omega
                  fc_steps
                  have hkm : ((1 : BitVec 32) <<< (k.toNat % 32)) = 1#32 <<< k := by
                    rw [Nat.mod_eq_of_lt (by omega)]; rfl
                  rw [hkm]
                  refine hBk (mask ||| (1#32 <<< k), true, k, ()) me ⟨rfl, fun _ =>
                    ⟨k.toNat, hk_lt, htmp_eq.symm, fun b hb htb => ?_⟩⟩
                  rw [testBit_or_shl_eq32 hk_31 hb, Bool.or_eq_true, decide_eq_true_eq] at htb
                  rcases htb with htb | rfl
                  · obtain ⟨hb_ua, p, hp, heq⟩ := hbwdj b hb htb
                    exact ⟨hb_ua, Or.inr ⟨p, hp, heq⟩⟩
                  · exact ⟨hk_lt, Or.inl rfl⟩
                · fc_steps
                  exact hLk (ua.toNat - (k + 1#32).toNat) (k + 1#32, ()) me (by omega)
                    ⟨rfl, by omega, rfl⟩
              · fc_steps; exact hBk (mask, false, k, ()) me ⟨rfl, fun h => by cases h⟩
            · intro _ Lk _ hLk; fc_let; exact hLk ua.toNat (0#32, ()) me ⟨rfl, Nat.zero_le _, rfl⟩
          · have hev_eq1 : s.core.vals[er.toNat]?.getD 0#8 = 1#8 := by
              have hne0 : (ste.core.vals[er.toNat]'her_vals').signExtend 32 ≠ 0#32 := by
                have hc' := beq_eq_false_iff_ne.mp hc
                rw [list_getElem_congr (bv_zext32_toNat er) her_vals her_vals'] at hc'; exact hc'
              have h1 := bv8_eq1_of_signExtend32_ne0_nslt0 hev_dom hne0 hev_nslt
              rw [List.getElem?_eq_getElem (by rw [hlen.core_ok.vals_len]; omega), Option.getD_some]
              exact h1
            fc_steps
            refine ihj (mask, j + 1#32, ()) me (by dsimp only; omega)
              ⟨repr_e, by omega, by omega, hrepr_e, ?_, ?_, hme'⟩
            · intro p hp; rw [hj1_n] at hp
              by_cases hpj : p = j.toNat
              · subst hpj; exact ⟨er.toNat, her_lt, hrv_er_eqv, Or.inl hev_eq1⟩
              · exact hfwdj p (by omega)
            · intro b hb htb
              obtain ⟨hb_ua, p, hp, heq⟩ := hbwdj b hb htb
              exact ⟨hb_ua, p, by omega, heq⟩
      · have hj_eq : j.toNat = ea.toNat := by
          simp only [BitVec.ult, decide_eq_false_iff_not] at hc; rw [hst_e1] at hc
          change ¬ j.toNat < ea.toNat at hc; omega
        rw [hj_eq] at hfwdj hbwdj
        fc_steps
        have hm_mod : ((1 : BitVec 32) <<< (ua.toNat % 32)) = 1#32 <<< ua := by
          rw [Nat.mod_eq_of_lt (by omega)]; rfl
        rw [hm_mod]
        refine hQ (mask == (1#32 <<< ua) - 1#32) reprj mj hrlj hreprj ?_ hmj
        intro htrue
        have hm_eq : mask = (1#32 <<< ua) - 1#32 := beq_iff_eq.mp htrue
        refine ⟨h2_le_ua, hua_le_31, ?_⟩
        rw [he0, Option.getD_some]
        refine andMatch_sound_equiv hwj hcl0 hand_e ?_ ?_
        · intro p hp
          have hp' : p < ea.toNat := by rw [← hrl_rhs]; exact hp
          have h1 := hfwdj p hp'
          dsimp only [rhs] at h1
          rw [List.getElem?_eq_getElem hp, Option.getD_some] at h1
          exact h1
        · intro k hk
          have htb : mask.toNat.testBit k = true := by
            rw [hm_eq]; exact testBit_full_mask_iff32 h2_le_ua hua_le_31 hk
          have ⟨_, p, hp, heq⟩ := hbwdj k (by omega) htb
          rw [← hrl_rhs] at hp
          exact ⟨p, hp, heq⟩

end Proofs1To6

end LeanQbe.T.Examples.Kissat.FullM5CongFix
