module

public import LeanQbe.T.Examples.Kissat.FullM6Orch
public import LeanQbe.T.Examples.Kissat.FullM6OrchProof2
public import LeanQbe.T.Examples.Kissat.FullM6OrchAdaptersProof0
public import LeanQbe.T.Examples.Kissat.FullM6ProofUtil
public import LeanQbe.T.Examples.Kissat.FullM6HdrProof0
public import LeanQbe.T.Examples.Kissat.FullSpec1
public import LeanQbe.T.Examples.Kissat.FullSpec2
public import LeanQbe.T.Examples.Kissat.FullSpec3
public import LeanQbe.T.Examples.Kissat.FullM4Proof1
public import LeanQbe.T.Examples.Kissat.FullM4TernaryProof
public import LeanQbe.T.Examples.Kissat.FullM5SchedLemmas
public import LeanQbe.T.Examples.Kissat.FullM6BcpS15Proof1
public import LeanQbe.T.Examples.Kissat.FullDefSweepLemmas1
public import LeanQbe.T.Examples.Kissat.FullWalkExtLemmas1

import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas1
import LeanQbe.T.Examples.Kissat.FullAnalyzeLemmas2
import LeanQbe.T.Examples.Kissat.FullDeduce1UipLemmas1
import LeanQbe.T.Examples.Kissat.FullDenseWatchLemmas1
import LeanQbe.T.Examples.Kissat.FullLearnAnaLemmas
import LeanQbe.T.Examples.Kissat.FullPropDecLemmas
import LeanQbe.T.Examples.Kissat.FullM6MinShrinkProof3a
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullSpec
import LeanQbe.T.Flat
import LeanQbe.T.FlatLemmas
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import LeanQbe.T.WPLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M6 Orchestration Proofs Part 0 (`FullM6OrchProof0`)

M1-clean proof module (plain public section, opaque specs):
Proves parametric `(Γ : Env)` `Func.wp` contracts for the `19` Group-0 `FullM6Orch` functions:
- `13` inner forwarding shims (`full_wstack_defrag` .. `full_sweep_dense_m6`)
- `full_reorder_m6` (`stable == 0` guard over `full_reorder_queue_m7`)
- `full_ema_swap_m6` (`glue_used[36..55]`) and `full_switch_mode_m6`
- `full_analyze_rsn_m6_hdr`, `full_deduce_1uip_m6_hdr`, `full_analyze_core_m6`
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6Orch

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.C0HeadStep
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6ProofUtil
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6ProofUtil.M6ProofUtilTactics

/-! ### Exported Orchestrator & Adapter Specs (`_of` / `_elim` / `_monoX`) -/

def m6ReorderSpec : Spec [i64, i64] [i64] :=
  fun (h, _budget, ()) m Q _ =>
    ∃ c F0 ext s R,
      h = c.hdr ∧
      FullM6HdrInv c F0 ext s ∧
      (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
        FullM6HdrInv c F0 ext s' →
        FullArenaPermEq s.core s'.core →
        s'.core.cur_level = s.core.cur_level →
        s'.core.fuel = s.core.fuel →
        FullExtScratchPres s s' →
        (FullM6HdrMem c ext s' ⋆ R) m' → Q (r, ()) m'

theorem m6ReorderSpec_of {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} {budget : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hinv : FullM6HdrInv c F0 ext s) (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullM6HdrInv c F0 ext s' →
      FullArenaPermEq s.core s'.core →
      s'.core.cur_level = s.core.cur_level →
      s'.core.fuel = s.core.fuel →
      FullExtScratchPres s s' →
      (FullM6HdrMem c ext s' ⋆ R) m' → Q (r, ()) m') :
    m6ReorderSpec (c.hdr, budget, ()) m Q X :=
  ⟨c, F0, ext, s, R, rfl, hinv, hm, hQ⟩

theorem m6ReorderSpec_elim {h budget : BitVec 64} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hs : m6ReorderSpec (h, budget, ()) m Q X) :
    ∃ c F0 ext s R, h = c.hdr ∧ FullM6HdrInv c F0 ext s ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
        FullM6HdrInv c F0 ext s' →
        FullArenaPermEq s.core s'.core →
        s'.core.cur_level = s.core.cur_level →
        s'.core.fuel = s.core.fuel →
        FullExtScratchPres s s' →
        (FullM6HdrMem c ext s' ⋆ R) m' → Q (r, ()) m' := hs

theorem m6ReorderSpec_monoX {xs : Tup Val [i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X X' : XPost} (h : m6ReorderSpec xs m Q X) :
    m6ReorderSpec xs m Q X' := by
  rcases xs with ⟨h0, budget, ⟨⟩⟩; exact h

def m6EmaSwapSpec : Spec [i64, i64, i64] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _old, _new, ()) _ => h = c.hdr)
    (fun _ _ _ s s' =>
      FullProbeScratchPres s s' ∧
      s'.scratch.delayed_len = s.scratch.delayed_len ∧
      s'.scratch.delayed = s.scratch.delayed)

theorem m6EmaSwapSpec_of {c : FullCfg} {oldM newM : BitVec 64} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post []} {X : XPost}
    (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ (s' : FullState) (m' : Mem 64),
      s'.core = s.core → s'.LengthsOk c →
      (FullProbeScratchPres s s' ∧
        s'.scratch.delayed_len = s.scratch.delayed_len ∧
        s'.scratch.delayed = s.scratch.delayed) →
      (FullMem c s' ⋆ R) m' → Q () m') :
    m6EmaSwapSpec (c.hdr, oldM, newM, ()) m Q X :=
  ⟨c, s, R, rfl, hlen, hm, fun ⟨⟩ s' m' hc hl hp hm' => hQ s' m' hc hl hp hm'⟩

theorem m6EmaSwapSpec_elim {h oldM newM : BitVec 64} {m : Mem 64}
    {Q : Post []} {X : XPost}
    (hs : m6EmaSwapSpec (h, oldM, newM, ()) m Q X) :
    ∃ c s R, h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
      ∀ (s' : FullState) (m' : Mem 64),
        s'.core = s.core → s'.LengthsOk c →
        (FullProbeScratchPres s s' ∧
          s'.scratch.delayed_len = s.scratch.delayed_len ∧
          s'.scratch.delayed = s.scratch.delayed) →
        (FullMem c s' ⋆ R) m' → Q () m' := by
  rcases hs with ⟨c, s, R, rfl, hlen, hm, hQ⟩
  exact ⟨c, s, R, rfl, hlen, hm, fun s' m' hc hl hp hm' => hQ () s' m' hc hl hp hm'⟩

theorem m6EmaSwapSpec_monoX {xs : Tup Val [i64, i64, i64]} {m : Mem 64}
    {Q : Post []} {X X' : XPost} (h : m6EmaSwapSpec xs m Q X) :
    m6EmaSwapSpec xs m Q X' := by
  rcases xs with ⟨h0, oldM, newM, ⟨⟩⟩; exact h

def m6AnalyzeRsnHdrSpec : Spec [i64, i32, i32] [.bool] := fun (h, rsn, skip_var, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut : Nat)
    (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
    FullWitnessCutInv c F0 F_cur cut s.core ∧ FullAnaMarksCov c s ∧
    s.core.tmp_len ≤ s.core.cur_vars ∧ s.core.tmp_cnt + s.core.cur_vars + 1 < 2 ^ 64 ∧
    (rsn ≠ 0xFFFFFFFF#32 → (rsn &&& 0x80000000#32) = 0#32 → rsn.toNat ∈ fullArenaClauseRefs s) ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ (ok : Bool) mrk' tmp' tc' tl' mcl' arena' sc' ext' m',
      let s' : FullState := { s with
        core := { s.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                              min_clr_len := mcl', arena := arena' }
        scratch := sc' }
      M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6ExtW2bPres ext ext') →
      s'.LengthsOk c → FullWitnessCutInv c F0 F_cur cut s'.core → FullAnaMarksCov c s' →
      FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
      s.core.tmp_len ≤ tl' → tl' ≤ s.core.cur_vars → s.core.tmp_cnt ≤ tc' →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
        fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
        fullArenaClauseLits s' r = fullArenaClauseLits s r) →
      (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 ≠ 0#8 →
        mrk'[v]?.getD 0#8 = s.core.mrk[v]?.getD 0#8) →
      (∀ k < s.core.tmp_len, tmp'[k]? = s.core.tmp[k]?) →
      (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
        ∃ l ∈ fullRsnLits s rsn, l / 2 = v ∧ v < s.core.cur_vars ∧ v ≠ skip_var.toNat ∧
          0 < (s.core.lvl[v]?.getD 0#32).toNat ∧
          (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level) →
      (∀ j, s.core.tmp_len ≤ j → j < tl' → let l := (tmp'[j]?.getD 0#32).toNat
        l ∈ fullRsnLits s rsn ∧ l < 2 * s.core.cur_vars ∧ l / 2 ≠ skip_var.toNat ∧
        s.core.mrk[l / 2]?.getD 0#8 = 0#8 ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
        (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level ∧ mrk'[l / 2]?.getD 0#8 ≠ 0#8) →
      (∀ j1 j2, s.core.tmp_len ≤ j1 → j1 < j2 → j2 < tl' →
        (tmp'[j1]?.getD 0#32).toNat / 2 ≠ (tmp'[j2]?.getD 0#32).toNat / 2) →
      (tc' - s.core.tmp_cnt = ((List.range s.core.cur_vars).filter fun w =>
        decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8) &&
        decide ((s.core.lvl[w]?.getD 0#32).toNat = s.core.cur_level)).length) →
      (sc'.res_sz = s.scratch.res_sz + BitVec.ofNat 64 ((List.range s.core.cur_vars).filter fun w =>
        decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8)).length) →
      (ok = true → rsn ≠ 0xFFFFFFFF#32 ∧
        sc'.ant_sz = s.scratch.ant_sz + BitVec.ofNat 64 ((fullRsnLits s rsn).countP fun l =>
          decide (l / 2 < s.core.cur_vars ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
            (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level)) ∧
        ∀ l ∈ fullRsnLits s rsn, l / 2 < s.core.cur_vars ∧ (l / 2 ≠ skip_var.toNat →
          (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
          (s.core.mrk[l / 2]?.getD 0#8 = 0#8 →
            (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level ∧
            (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat →
              (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level →
              ∃ j, s.core.tmp_len ≤ j ∧ j < tl' ∧ (tmp'[j]?.getD 0#32).toNat / 2 = l / 2)))) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (ok, ()) m'

theorem m6AnalyzeRsnHdrSpec_monoX {xs : Tup Val [i64, i32, i32]} {m : Mem 64}
    {Q : Post [.bool]} {X X' : XPost} (h : m6AnalyzeRsnHdrSpec xs m Q X) :
    m6AnalyzeRsnHdrSpec xs m Q X' := by rcases xs with ⟨_, _, _, ⟨⟩⟩; exact h

def m6Deduce1uipHdrSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ c F0 F_cur cut ext s R, h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧
    FullCutInvW c F0 F_cur cut s ∧ 0 < s.core.cur_level ∧ FullConflictOkCut F_cur cut s ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ (r : BitVec 64) (ext' : List (BitVec 64)) (s' : FullState) (m' : Mem 64),
      M6HdrExtOk ext' → s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
      s'.scratch.work_stk2 = s.scratch.work_stk2 →
      (r = 20#64 → F0.Unsat ∧ FullOtfsInvW c F0 F_cur s' ∧
        s'.core.cur_level ≤ s.core.cur_level ∧ s'.core.dense_mode = s.core.dense_mode) →
      (r = 0#64 → FullOtfsInvW c F0 F_cur s') →
      (r = 1#64 → FullOtfsInvW c F0 F_cur s' ∧ s'.core.cur_level = s.core.cur_level ∧
        1 ≤ s'.core.tmp_len ∧ s'.core.tmp_len ≤ s'.core.cur_vars ∧
        (List.map (fun x => x.toNat / 2) (List.take s'.core.tmp_len s'.core.tmp)).Nodup ∧
        (∀ k, k < s'.core.tmp_len → let l := (s'.core.tmp[k]?.getD 0#32).toNat
          l < 2 * s'.core.cur_vars ∧ s'.core.vals[l]?.getD 0#8 = 255#8) ∧
        (∀ k, 1 ≤ k → k < s'.core.tmp_len →
          let lv := (s'.core.lvl[(s'.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
          0 < lv ∧ lv < s'.core.cur_level) ∧
        (s'.core.lvl[(s'.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s'.core.cur_level ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause (List.map BitVec.toNat (List.take s'.core.tmp_len s'.core.tmp)))) →
      (r = 2#64 → ∃ cut', cut' ≤ s'.core.trail_end ∧ FullCutInvW c F0 F_cur cut' s' ∧
        s'.core.cur_level = s.core.cur_level ∧ FullConflictOkCut F_cur cut' s') →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

theorem m6Deduce1uipHdrSpec_monoX {xs : Tup Val [i64]} {m : Mem 64}
    {Q : Post [i64]} {X X' : XPost} (h : m6Deduce1uipHdrSpec xs m Q X) :
    m6Deduce1uipHdrSpec xs m Q X' := by rcases xs with ⟨h0, ⟨⟩⟩; exact h

/-! ### Private Helpers -/

private theorem m6o_arenaPermEq_refl (k : FullCoreState) : FullArenaPermEq k k :=
  ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl, List.Perm.refl _⟩⟩

private theorem fullSparseInv_of_extScratch {c : FullCfg} {F0 : CNF Nat} {s s' : FullState}
    (hsp : FullSparseInv c F0 s) (hlen : s'.LengthsOk c) (hcore : s'.core = s.core)
    (hpres : FullExtScratchPres s s') : FullSparseInv c F0 s' :=
  hsp.of_safetySlice hlen hcore hpres

private def m6oUpdGu (s : FullState) (gu' : List (BitVec 32)) : FullState :=
  { s with scratch := { s.scratch with glue_used := gu' } }

private def M6oProbeStep (s0 s : FullState) : Prop :=
  FullProbeScratchPres s0 s ∧
  s.scratch.delayed_len = s0.scratch.delayed_len ∧
  s.scratch.delayed = s0.scratch.delayed

private theorem m6oProbeStep_refl (s : FullState) : M6oProbeStep s s :=
  ⟨⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩

private theorem m6oProbeStep_trans {s0 s1 s2 : FullState}
    (h1 : M6oProbeStep s0 s1) (h2 : M6oProbeStep s1 s2) : M6oProbeStep s0 s2 :=
  ⟨⟨⟨h2.1.1.1.trans h1.1.1.1, h2.1.1.2.trans h1.1.1.2⟩,
    h2.1.2.1.trans h1.1.2.1, h2.1.2.2.1.trans h1.1.2.2.1,
    h2.1.2.2.2.1.trans h1.1.2.2.2.1, h2.1.2.2.2.2.1.trans h1.1.2.2.2.2.1,
    h2.1.2.2.2.2.2.1.trans h1.1.2.2.2.2.2.1, h2.1.2.2.2.2.2.2.1.trans h1.1.2.2.2.2.2.2.1,
    h2.1.2.2.2.2.2.2.2.trans h1.1.2.2.2.2.2.2.2⟩,
    h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

private theorem m6oUpdGu_step {c : FullCfg} {s s0 : FullState} (hs : s.LengthsOk c)
    (hcore : s.core = s0.core) (hp : M6oProbeStep s0 s)
    {gu' : List (BitVec 32)} (hgu : gu'.length = s.scratch.glue_used.length) :
    (m6oUpdGu s gu').LengthsOk c ∧ (m6oUpdGu s gu').core = s0.core ∧
      M6oProbeStep s0 (m6oUpdGu s gu') := by
  have hst := fullState_upd_glue_used_step hs hgu
  exact ⟨hst.1, hst.2.1.trans hcore, m6oProbeStep_trans hp hst.2.2⟩

private theorem m6o_wp_load_gu_bv {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {i : BitVec 64} {a : Arg Val i64} {k : Val i32 → Expr Val Cont rs}
    (ha : a.val = c.pGlueUsed + i * 4)
    (hi : i.toNat < 64) (hm : (FullMem c s ⋆ R) m) (hgu : s.scratch.glue_used.length = 64)
    (hk : wp Γ Q X (k (s.scratch.glue_used[i.toNat]'(by rw [hgu]; exact hi))) m) :
    wp Γ Q X (.load i32 a k) m :=
  head_wp_load ha (c0_load_full_glue_used (by rw [hgu]; exact hi) hm) hk

private theorem m6o_wp_load_gu_imm {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {n : Nat} {a : Arg Val i64} {k : Val i32 → Expr Val Cont rs}
    (ha : a.val = c.pGlueUsed + BitVec.ofNat (OfNat.ofNat 64) n * 4)
    (hn : n < 64) (hgu : s.scratch.glue_used.length = 64) (hm : (FullMem c s ⋆ R) m)
    (hk : wp Γ Q X (k (s.scratch.glue_used[n]'(by rw [hgu]; exact hn))) m) :
    wp Γ Q X (.load i32 a k) m := by
  have hi : (BitVec.ofNat 64 n).toNat < 64 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hn
  refine m6o_wp_load_gu_bv ha hi hm hgu ?_
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : n < 2 ^ 64)] using hk

private theorem m6o_wp_store_gu_bv {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {s0 : FullState} {gu : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    {i : BitVec 64} {a : Arg Val i64} {v : Arg Val i32} {vv : BitVec 32} {k : Expr Val Cont rs}
    (hv : v.val = vv) (ha : a.val = c.pGlueUsed + i * 4)
    (hi : i.toNat < 64) (hgu : gu.length = 64) (hm : (FullMem c (m6oUpdGu s0 gu) ⋆ R) m)
    (hk : ∀ gu' m', gu'.length = 64 → (FullMem c (m6oUpdGu s0 gu') ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X (.store v a k) m := by
  have hst := c0_store_full_glue_used vv (show i.toNat < (m6oUpdGu s0 gu).scratch.glue_used.length
    from by change i.toNat < gu.length; rw [hgu]; exact hi) hm
  exact @head_wp_store Γ rs Q X m i32 v a vv _ k (FullMem c (m6oUpdGu s0 (gu.set i.toNat vv))) R
    hv ha (by simpa [m6oUpdGu] using hst) fun _ hm' => hk _ _ (by simpa using hgu) hm'

private theorem m6o_wp_store_gu_imm {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {s0 : FullState} {gu : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    {n : Nat} {a : Arg Val i64} {v : Arg Val i32} {vv : BitVec 32} {k : Expr Val Cont rs}
    (hv : v.val = vv) (ha : a.val = c.pGlueUsed + BitVec.ofNat (OfNat.ofNat 64) n * 4)
    (hn : n < 64) (hgu : gu.length = 64) (hm : (FullMem c (m6oUpdGu s0 gu) ⋆ R) m)
    (hk : ∀ gu' m', gu'.length = 64 → (FullMem c (m6oUpdGu s0 gu') ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X (.store v a k) m :=
  m6o_wp_store_gu_bv hv ha (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hn)
    hgu hm hk

private theorem m6o_gu_bv_step {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {s0 : FullState} {gu : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    {i : BitVec 64} {a : Arg Val i64} {v : Arg Val i32} {vv : BitVec 32} {k : Expr Val Cont rs}
    (hm : (FullMem c (m6oUpdGu s0 gu) ⋆ R) m) (hgu : gu.length = 64)
    (hv : v.val = vv) (ha : a.val = c.pGlueUsed + i * 4) (hi : i.toNat < 64)
    (hk : ∀ gu' m', gu'.length = 64 → (FullMem c (m6oUpdGu s0 gu') ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X (.store v a k) m := m6o_wp_store_gu_bv hv ha hi hgu hm hk

private theorem m6o_gu_step {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {s0 : FullState} {gu : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64}
    {n : Nat} {a : Arg Val i64} {v : Arg Val i32} {vv : BitVec 32} {k : Expr Val Cont rs}
    (hm : (FullMem c (m6oUpdGu s0 gu) ⋆ R) m) (hgu : gu.length = 64)
    (hv : v.val = vv) (ha : a.val = c.pGlueUsed + BitVec.ofNat (OfNat.ofNat 64) n * 4)
    (hn : n < 64)
    (hk : ∀ gu' m', gu'.length = 64 → (FullMem c (m6oUpdGu s0 gu') ⋆ R) m' → wp Γ Q X k m') :
    wp Γ Q X (.store v a k) m := m6o_wp_store_gu_imm hv ha hn hgu hm hk

private theorem m6o_gu_finish {c : FullCfg} {s : FullState} {gu : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hlen : s.LengthsOk c) (hgu0 : s.scratch.glue_used.length = 64)
    (hm : (FullMem c (m6oUpdGu s gu) ⋆ R) m) (hgu : gu.length = 64) :
    (m6oUpdGu s gu).LengthsOk c ∧ (m6oUpdGu s gu).core = s.core ∧
      M6oProbeStep s (m6oUpdGu s gu) ∧ (FullMem c (m6oUpdGu s gu) ⋆ R) m :=
  let h := m6oUpdGu_step hlen rfl (m6oProbeStep_refl s) (hgu.trans hgu0.symm)
  ⟨h.1, h.2.1, h.2.2, hm⟩

private theorem m6oProbeStep_upd_ema {c : FullCfg} {s s0 : FullState}
    (hlen : s.LengthsOk c) (hcore : s.core = s0.core) (hp : M6oProbeStep s0 s)
    (efb efe esb ese : BitVec 64) :
    let s' : FullState := { core := s.core, scratch := { s.scratch with
      ema_fast_biased := efb, ema_fast_exp := efe,
      ema_slow_biased := esb, ema_slow_exp := ese } }
    s'.LengthsOk c ∧ s'.core = s0.core ∧ M6oProbeStep s0 s' :=
  let hst := fullState_upd_ema_step hlen efb efe esb ese
  ⟨hst.1, hst.2.1.trans hcore, m6oProbeStep_trans hp hst.2.2⟩

private theorem m6oProbeStep_upd_ema_pack {c : FullCfg} {s s0 : FullState}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hlen : s.LengthsOk c) (hcore : s.core = s0.core) (hp : M6oProbeStep s0 s)
    {efb efe esb ese : BitVec 64}
    (hm : (FullMem c { core := s.core, scratch := { s.scratch with
      ema_fast_biased := efb, ema_fast_exp := efe,
      ema_slow_biased := esb, ema_slow_exp := ese } } ⋆ R) m) :
    let s' : FullState := { core := s.core, scratch := { s.scratch with
      ema_fast_biased := efb, ema_fast_exp := efe,
      ema_slow_biased := esb, ema_slow_exp := ese } }
    s'.LengthsOk c ∧ s'.core = s0.core ∧ M6oProbeStep s0 s' ∧ (FullMem c s' ⋆ R) m :=
  let hst := m6oProbeStep_upd_ema hlen hcore hp efb efe esb ese
  ⟨hst.1, hst.2.1, hst.2.2, hm⟩

/-! ### 13 Inner Forwarding Shims -/

private theorem m6o_fwd0 {Q : Post []} : (fun (_ : Tup Val []) m' => Q () m') = Q :=
  funext fun r => by cases r; rfl

private theorem m6o_fwd1 {t : Ty} {Q : Post [t]} :
    (fun (r : Tup Val [t]) m' => Q (r.fst, ()) m') = Q := funext fun ⟨_, ⟨⟩⟩ => rfl

theorem full_wstack_defrag_wp (Γ : Env) (hSub : ∀ a m Q X, fullWstackDefragSpec a m Q X →
    Γ "full_wstack_defrag_m6" [i64] [] a m Q X) : ∀ a m Q X, fullWstackDefragSpec a m Q X →
    Func.wp Γ FullM6Orch.full_wstack_defrag_body a m Q X := by
  intro ⟨_, ⟨⟩⟩ _ _ _ hs; unfold Func.wp FullM6Orch.full_wstack_defrag_body
  c0_hsteps; c0_call hSub; rwa [m6o_fwd0]

theorem full_watch_push_wp (Γ : Env) (hSub : ∀ a m Q X, fullWatchPushSpec a m Q X →
    Γ "full_watch_push_m6" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullWatchPushSpec a m Q X → Func.wp Γ FullM6Orch.full_watch_push_body a m Q X := by
  intro ⟨_, _, _, _, _, ⟨⟩⟩ _ _ _ hs; unfold Func.wp FullM6Orch.full_watch_push_body
  c0_hsteps; c0_call hSub; rwa [m6o_fwd1]

theorem full_rescale_wp (Γ : Env) (hSub : ∀ a m Q X, fullRescaleSpec a m Q X →
    Γ "full_rescale_m6" [i64] [] a m Q X) : ∀ a m Q X, fullRescaleSpec a m Q X →
    Func.wp Γ FullM6Orch.full_rescale_body a m Q X := by
  intro ⟨_, ⟨⟩⟩ _ _ _ hs; unfold Func.wp FullM6Orch.full_rescale_body
  c0_hsteps; c0_call hSub; rwa [m6o_fwd0]

theorem full_parse_body_wp (Γ : Env) (hSub : ∀ a m Q X, fullParseBodySpec a m Q X →
    Γ "full_parse_body_m6" [i64, i64] [i64] a m Q X) : ∀ a m Q X, fullParseBodySpec a m Q X →
    Func.wp Γ FullM6Orch.full_parse_body_body a m Q X := by
  intro ⟨_, _, ⟨⟩⟩ _ _ _ hs; unfold Func.wp FullM6Orch.full_parse_body_body
  c0_hsteps; c0_call hSub; rwa [m6o_fwd1]

theorem full_lit_rank_wp (Γ : Env) (hSub : ∀ a m Q X, fullLitRankSpec a m Q X →
    Γ "full_lit_rank_m6" [i64, i64, i32] [i64] a m Q X) : ∀ a m Q X, fullLitRankSpec a m Q X →
    Func.wp Γ FullM6Orch.full_lit_rank_body a m Q X := by
  intro ⟨_, _, _, ⟨⟩⟩ _ _ _ hs; unfold Func.wp FullM6Orch.full_lit_rank_body
  c0_hsteps; c0_call hSub; rwa [m6o_fwd1]

theorem full_sweep_bins_wp (Γ : Env) (hSub : ∀ a m Q X, fullSweepBinsSpec a m Q X →
    Γ "full_sweep_bins_m6cf" [i64] [] a m Q X) : ∀ a m Q X, fullSweepBinsSpec a m Q X →
    Func.wp Γ FullM6Orch.full_sweep_bins_body a m Q X := by
  intro ⟨_, ⟨⟩⟩ _ _ _ hs; unfold Func.wp FullM6Orch.full_sweep_bins_body
  c0_hsteps; c0_call hSub; rwa [m6o_fwd0]

theorem full_rewatch_arena_wp (Γ : Env) (hSub : ∀ a m Q X, fullRewatchArenaSpec a m Q X →
    Γ "full_rewatch_arena_m6" [i64, i64] [.bool] a m Q X) :
    ∀ a m Q X, fullRewatchArenaSpec a m Q X →
      Func.wp Γ FullM6Orch.full_rewatch_arena_body a m Q X := by
  intro ⟨_, _, ⟨⟩⟩ _ _ _ hs; unfold Func.wp FullM6Orch.full_rewatch_arena_body
  c0_hsteps; c0_call hSub; rwa [m6o_fwd1]

theorem full_arena_sweep_wp (Γ : Env) (hSub : ∀ a m Q X, fullArenaSweepSpec a m Q X →
    Γ "full_arena_sweep_m6" [i64] [i64] a m Q X) : ∀ a m Q X, fullArenaSweepSpec a m Q X →
    Func.wp Γ FullM6Orch.full_arena_sweep_body a m Q X := by
  intro ⟨_, ⟨⟩⟩ _ _ _ hs; unfold Func.wp FullM6Orch.full_arena_sweep_body
  c0_hsteps; c0_call hSub; rwa [m6o_fwd1]

theorem full_mark_reasons_wp (Γ : Env) (hSub : ∀ a m Q X, fullMarkReasonsSpec a m Q X →
    Γ "full_mark_reasons_m6" [i64, .bool] [] a m Q X) : ∀ a m Q X, fullMarkReasonsSpec a m Q X →
    Func.wp Γ FullM6Orch.full_mark_reasons_body a m Q X := by
  intro ⟨_, _, ⟨⟩⟩ _ _ _ hs; unfold Func.wp FullM6Orch.full_mark_reasons_body
  c0_hsteps; c0_call hSub; rwa [m6o_fwd0]

theorem full_min_shrink_any_wp {msSpec : Spec [i64] []} (Γ : Env)
    (hSub : ∀ a m Q X, msSpec a m Q X → Γ "full_min_shrink_m6" [i64] [] a m Q X) :
    ∀ a m Q X, msSpec a m Q X → Func.wp Γ FullM6Orch.full_min_shrink_body a m Q X := by
  intro ⟨_, ⟨⟩⟩ _ _ _ hs; unfold Func.wp FullM6Orch.full_min_shrink_body
  c0_hsteps; c0_call hSub; rwa [m6o_fwd0]

theorem full_min_shrink_wp (Γ : Env) (hSub : ∀ a m Q X, fullMinShrinkSpec a m Q X →
    Γ "full_min_shrink_m6" [i64] [] a m Q X) : ∀ a m Q X, fullMinShrinkSpec a m Q X →
    Func.wp Γ FullM6Orch.full_min_shrink_body a m Q X :=
  full_min_shrink_any_wp Γ hSub

theorem full_deduce_1uip_wp (Γ : Env) (hSub : ∀ a m Q X, fullDeduce1uipSpec a m Q X →
    Γ "full_deduce_1uip_m6" [i64] [i64] a m Q X) : ∀ a m Q X, fullDeduce1uipSpec a m Q X →
    Func.wp Γ FullM6Orch.full_deduce_1uip_body a m Q X := by
  intro ⟨_, ⟨⟩⟩ _ _ _ hs; unfold Func.wp FullM6Orch.full_deduce_1uip_body
  c0_hsteps; c0_call hSub; rwa [m6o_fwd1]

theorem full_walk_wp (Γ : Env) (hSub : ∀ a m Q X, fullWarmupSpec a m Q X →
    Γ "full_walk_m6" [i64] [] a m Q X) : ∀ a m Q X, fullWarmupSpec a m Q X →
    Func.wp Γ FullM6Orch.full_walk_body a m Q X := by
  intro ⟨_, ⟨⟩⟩ _ _ _ hs; unfold Func.wp FullM6Orch.full_walk_body
  c0_hsteps; c0_call hSub; rwa [m6o_fwd0]

theorem full_sweep_dense_m6_wp (Γ : Env)
    (hSub : ∀ a m Q X, FullDefSweep.fullSweepDenseSpec a m Q X →
      Γ "full_sweep_dense_m5" [i64, i64, i64] [i64] a m Q X) :
    ∀ a m Q X, FullDefSweep.fullSweepDenseSpec a m Q X →
      Func.wp Γ full_sweep_dense_m6_body a m Q X := by
  intro ⟨_, _, _, ⟨⟩⟩ _ _ _ hs; unfold Func.wp full_sweep_dense_m6_body
  c0_hsteps; c0_call hSub; rwa [m6o_fwd1]

/-! ### `full_reorder_m6` (Stable Guard -> `full_reorder_queue_m7`) -/

private theorem full_reorder_m6_aux (Γ : Env)
    (hQueue : ∀ a m Q X, FullM4Ternary.fullReorderQueueSpec a m Q X →
      Γ "full_reorder_queue_m7" [i64] [i64] a m Q X)
    {c : FullCfg} {budget : BitVec 64} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ r s' m', s'.core = s.core → s'.LengthsOk c → FullExtScratchPres s s' →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    Func.wp Γ full_reorder_m6_body (c.hdr, budget, ()) m Q X := by
  unfold Func.wp full_reorder_m6_body; c0_hsteps
  · exact hQ 0#64 s m rfl hlen ⟨rfl, rfl⟩ hm
  · c0_call hQueue; refine ⟨c, s, R, rfl, hlen, hm, ?_⟩
    rintro ⟨r, ⟨⟩⟩ s1 m1 hc1 hlen1 hpres1 hm1; c0_hsteps
    exact hQ r s1 m1 (fullCoreState_agrees_with_scratch hc1) hlen1 hpres1 hm1

theorem full_reorder_m6_wp (Γ : Env)
    (hQueue : ∀ a m Q X, FullM4Ternary.fullReorderQueueSpec a m Q X →
      Γ "full_reorder_queue_m7" [i64] [i64] a m Q X) :
    ∀ a m Q X, FullM4.m4ReorderSpec a m Q X →
      Func.wp Γ full_reorder_m6_body a m Q X := by
  rintro ⟨h, budget, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp, hm, hQ⟩
  refine full_reorder_m6_aux Γ hQueue hsp.lengths hm fun r s1 m1 hce1 hlen1 hpres1 hm1 => ?_
  exact hQ r s1 m1 (fullSparseInv_of_extScratch hsp hlen1 hce1 hpres1)
    (hce1 ▸ m6o_arenaPermEq_refl s.core) (by rw [hce1]) (by rw [hce1]) hm1

theorem full_reorder_m6_hdr_wp (Γ : Env)
    (hQueue : ∀ a m Q X, FullM4Ternary.fullReorderQueueSpec a m Q X →
      Γ "full_reorder_queue_m7" [i64] [i64] a m Q X) :
    ∀ a m Q X, m6ReorderSpec a m Q X →
      Func.wp Γ full_reorder_m6_body a m Q X := by
  rintro ⟨h, budget, ⟨⟩⟩ m Q X ⟨c, F0, ext, s, R, rfl, hinv, hm, hQ⟩
  refine wp_m6Hdr_focus_frame hm fun hm' =>
    full_reorder_m6_aux Γ hQueue hinv.sparse.lengths hm' fun r s1 m1 hce1 hlen1 hpres1 hm1 =>
      hQ r s1 m1 (fullM6HdrInv_of_core_eq hinv hlen1 hce1 hpres1)
        (hce1 ▸ m6o_arenaPermEq_refl s.core) (by rw [hce1]) (by rw [hce1])
        hpres1 (fullM6HdrMem_unfocus hm1)

/-! ### `full_ema_swap_m6` (`glue_used[36..55]`) -/

theorem full_ema_swap_m6_wp (Γ : Env) :
    ∀ a m Q X, m6EmaSwapSpec a m Q X →
      Func.wp Γ full_ema_swap_m6_body a m Q X := by
  rintro ⟨h, oldM, newM, ⟨⟩⟩ m Q X hs
  rcases m6EmaSwapSpec_elim hs with ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hgu := hlen.scratch_ok.glue_used_len
  unfold Func.wp full_ema_swap_m6_body
  c0_hsteps_nogrp
  apply m6o_wp_load_gu_imm rfl (by decide) hgu hm; c0_hsteps_nogrp
  apply m6o_wp_load_gu_imm rfl (by decide) hgu hm; c0_hsteps_nogrp
  refine wp_join_state0 (α := FullState) (fun st m' =>
    st.LengthsOk c ∧ st.core = s.core ∧ M6oProbeStep s st ∧ (FullMem c st ⋆ R) m') ?_ ?_
  · rintro J s1 m1 ⟨hlen1, hce1, hpres1, hm1⟩
    have hgu1 := hlen1.scratch_ok.glue_used_len
    c0_hsteps_nogrp
    refine wp_join_state1 (α := FullState × BitVec 64) (fun p => p.2) (fun p m' =>
      p.1.LengthsOk c ∧ p.1.core = s.core ∧ M6oProbeStep s p.1 ∧
      (p.2 = 40#64 ∨ p.2 = 48#64) ∧ (FullMem c p.1 ⋆ R) m') ?_ ?_
    · rintro J2 ⟨s2, ob⟩ m2 ⟨hlen2, hce2, hpres2, hob, hm2⟩
      have hgu2 := hlen2.scratch_ok.glue_used_len
      have hob_hi : ∀ k : Nat, k ≤ 7 → (ob + BitVec.ofNat 64 k).toNat < 64 := by
        intro k hk
        rcases hob with rfl | rfl <;> (simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
      have hob0 : ob.toNat < 64 := by rcases hob with rfl | rfl <;> decide
      change (FullMem c (m6oUpdGu s2 s2.scratch.glue_used) ⋆ R) m2 at hm2
      c0_hsteps_nogrp
      apply m6o_wp_store_gu_bv rfl rfl hob0 hgu2 hm2
      intro gu1 m1 hgu1 hm1; c0_hsteps_nogrp
      repeat (apply m6o_gu_bv_step (by assumption) (by assumption) rfl rfl (hob_hi _ (by decide))
              intro _ _ _ _; c0_hsteps_nogrp)
      rename_i gu8 m8 hgu8 hm8
      have ⟨hlen28, hce28, hp28⟩ :=
        m6oUpdGu_step hlen2 hce2 hpres2 (hgu8.trans hlen2.scratch_ok.glue_used_len.symm)
      generalize m6oUpdGu s2 gu8 = s28 at *
      have hgu28 := hlen28.scratch_ok.glue_used_len
      apply m6o_wp_load_gu_imm rfl (by decide) hgu28 hm8; c0_hsteps_nogrp
      apply m6o_wp_load_gu_imm rfl (by decide) hgu28 hm8; c0_hsteps_nogrp
      refine wp_join_state1 (α := FullState × BitVec 64) (fun p => p.2) (fun p m' =>
        p.1.LengthsOk c ∧ p.1.core = s.core ∧ M6oProbeStep s p.1 ∧
        (p.2 = 40#64 ∨ p.2 = 48#64) ∧ (FullMem c p.1 ⋆ R) m') ?_ ?_
      · rintro J3 ⟨s3b, nb⟩ m3b ⟨hlen3, hce3, hp3, hnb, hm3b⟩
        dsimp only at hlen3 hce3 hp3 hnb hm3b
        have hgu3b := hlen3.scratch_ok.glue_used_len
        have hnb_hi : ∀ k : Nat, k ≤ 7 → (nb + BitVec.ofNat 64 k).toNat < 64 := by
          intro k hk
          rcases hnb with rfl | rfl <;> (simp [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
        c0_hsteps_nogrp
        refine wp_join_state1 (α := FullState × BitVec 64) (fun p => p.2) (fun p m' =>
          p.1.LengthsOk c ∧ p.1.core = s.core ∧ M6oProbeStep s p.1 ∧
          (FullMem c p.1 ⋆ R) m') ?_ ?_
        · rintro J4 ⟨s4, msk⟩ m4 ⟨hlen4, hce4, hp4, hm4⟩
          dsimp only at hlen4 hce4 hp4 hm4
          have hgu4 := hlen4.scratch_ok.glue_used_len
          change (FullMem c (m6oUpdGu s4 s4.scratch.glue_used) ⋆ R) m4 at hm4
          c0_hsteps_nogrp
          apply m6o_gu_step hm4 hgu4 rfl rfl (by decide)
          intro gu41 m41 hgu41 hm41; c0_hsteps_nogrp
          apply m6o_gu_step hm41 hgu41 rfl rfl (by decide)
          intro gu42 m42 hgu42 hm42; c0_hsteps_nogrp
          have ⟨hlen5, hce5, hp5⟩ := m6oUpdGu_step hlen4 hce4 hp4 (hgu42.trans hgu4.symm)
          exact hQ _ m42 hce5 hlen5 hp5 hm42
        · intro J4 hJ4
          c0_hsteps_nogrp
          · apply m6o_wp_load_gu_bv rfl (hnb_hi 2 (by omega)) hm hgu3b; c0_hsteps_nogrp
            apply m6o_wp_load_gu_bv rfl (hnb_hi 3 (by omega)) hm hgu3b; c0_hsteps_nogrp
            apply m6o_wp_load_gu_bv rfl (hnb_hi 4 (by omega)) hm hgu3b; c0_hsteps_nogrp
            apply m6o_wp_load_gu_bv rfl (hnb_hi 5 (by omega)) hm hgu3b; c0_hsteps_nogrp
            apply m6o_wp_load_gu_bv rfl (hnb_hi 6 (by omega)) hm hgu3b; c0_hsteps_nogrp
            apply m6o_wp_load_gu_bv rfl (hnb_hi 7 (by omega)) hm hgu3b; c0_hsteps_nogrp
            dsimp only at hm
            exact hJ4 (_, _) _ (m6oProbeStep_upd_ema_pack hlen3 hce3 hp3 hm)
          · dsimp only at hm
            exact hJ4 (_, _) _ (m6oProbeStep_upd_ema_pack hlen3 hce3 hp3 hm)
      · intro J3 hJ3
        c0_hsteps_nogrp
        · exact hJ3 (s28, 40#64) m8 ⟨hlen28, hce28, hp28, Or.inl rfl, hm8⟩
        · exact hJ3 (s28, 48#64) m8 ⟨hlen28, hce28, hp28, Or.inr rfl, hm8⟩
    · intro J2 hJ2
      c0_hsteps_nogrp
      · exact hJ2 (s1, 40#64) m1 ⟨hlen1, hce1, hpres1, Or.inl rfl, hm1⟩
      · exact hJ2 (s1, 48#64) m1 ⟨hlen1, hce1, hpres1, Or.inr rfl, hm1⟩
  · intro J hJ; c0_hsteps_nogrp
    · change (FullMem c (m6oUpdGu s s.scratch.glue_used) ⋆ R) m at hm
      repeat (apply m6o_gu_step (by assumption) (by assumption) rfl rfl (by decide)
              intro _ _ _ _; c0_hsteps_nogrp)
      exact hJ _ _ (m6o_gu_finish hlen hgu (by assumption) (by assumption))
    · exact hJ s m ⟨hlen, rfl, m6oProbeStep_refl s, hm⟩

/-! ### Additional Local Helpers (`switch_mode`, `reduce`, `TFlat` Lifting) -/

private theorem m6o_call_emaSwap {Γ : Env} {ret : List Ty}
    {oldM newM : BitVec 64} {args : Tup (Arg Val) [i64, i64, i64]}
    {k : Tup Val [] → Expr Val Cont ret}
    {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, oldM, newM, ()))
    (hΓ : ∀ a m' Q' X', m6EmaSwapSpec a m' Q' X' →
      Γ "full_ema_swap_m6" [i64, i64, i64] [] a m' Q' X')
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ s' m', s'.core = s.core → s'.LengthsOk c →
      FullProbeScratchPres s s' → (FullM6HdrMem c ext s' ⋆ R) m' →
      wp Γ Q X (k ()) m') :
    wp Γ Q X (.call "full_ema_swap_m6" (as := [i64, i64, i64]) (bs := []) args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  exact hΓ _ _ _ X (fullM6Hdr_frame_safetySlice hcfg hext hlen (by exact rfl) hm
    (fun () s' m' hs' hc hp _ _ hm' =>
      hk s' m' (fullCoreState_agrees_with_scratch hc) hs' hp.1 hm'))

private theorem m6o_call_heapDown {Γ : Env} {ret : List Ty}
    {idx : BitVec 32} {args : Tup (Arg Val) [i64, i32]}
    {k : Tup Val [] → Expr Val Cont ret}
    {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post ret} {X : XPost}
    (hargs : vals args = (c.hdr, idx, ()))
    (hΓ : ∀ a m' Q' X', Full.fullHeapDownSpec a m' Q' X' →
      Γ "full_heap_down" [i64, i32] [] a m' Q' X')
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hk : ∀ s' m', s'.core = s.core → s'.LengthsOk c →
      s'.scratch.heap_len = s.scratch.heap_len → FullProbeScratchPres s s' →
      (FullM6HdrMem c ext s' ⋆ R) m' → wp Γ Q X (k ()) m') :
    wp Γ Q X (.call "full_heap_down" (as := [i64, i32]) (bs := []) args k) m := by
  refine wp_call_of_spec args k ?_; rw [hargs]
  exact hΓ _ _ _ X (fullM6Hdr_frame_safetySlice hcfg hext hlen (by exact rfl) hm
    (fun () s' m' hs' hc hp _ _ hm' =>
      hk s' m' (fullCoreState_agrees_with_scratch hc) hs' hp.1 hp.2 hm'))

/-! ### `TFlat` `"full_analyze_rsn"` -> `"full_analyze_rsn_m6_hdr"` Frame Lifter
  and `full_deduce_1uip_m6_hdr` -/

private def arsnLiftEnv : Env := fun f as bs xs m Q X =>
  match f, as, bs, xs, Q with
  | "full_analyze_rsn", [.bits 64, .bits 32, .bits 32], [.bool], xs, Q =>
    Full.fullAnalyzeRsnSpec xs m Q X
  | "full_analyze_lit", [.bits 64, .bits 32, .bits 32], [.bool], xs, Q =>
    Full.fullAnalyzeLitSpec xs m Q X
  | "full_clear_ana", [.bits 64], [], xs, Q =>
    Full.fullClearAnaSpec xs m Q X
  | "full_otfs_large", [.bits 64, .bits 32, .bits 32], [.bool], xs, Q =>
    Full.fullOtfsLargeSpec xs m Q X
  | "full_otfs_bin", [.bits 64, .bits 32, .bits 32], [.bool], xs, Q =>
    Full.fullOtfsBinSpec xs m Q X
  | "full_otfs_subsume", [.bits 64, .bits 32, .bits 64, .bits 64, .bool], [], xs, Q =>
    Full.fullOtfsSubsumeSpec xs m Q X
  | _, _, _, _, _ => False

private def tflatMapArsnCall {as : List Ty} (bs : List Ty) (args : Tup (Arg K) as) (nv : Nat) :
    Option (Arg K i64) :=
  match as, bs, args with
  | [.bits 64, .bits 32, .bits 32], [.bool], (a0, _, _, ()) =>
    match a0 with
    | .var i => if decide (0 < nv ∧ i = nv - 1) then some a0 else none
    | _ => none
  | _, _, _ => none

mutual
private def tflatMapArsn {rs : List Ty} (nv : Nat) : TFlat rs → Option (TFlat rs)
  | .let_ (ts := ts) op k => (tflatMapArsn (nv + ts.length) k).map (.let_ op)
  | .load t a k => (tflatMapArsn (nv + 1) k).map (.load t a)
  | .store v a k => (tflatMapArsn nv k).map (.store v a)
  | .call f bs args k =>
    if f = "full_analyze_rsn" then
      match tflatMapArsnCall bs args nv with
      | some _ => (tflatMapArsn (nv + bs.length) k).map (.call "full_analyze_rsn_m6_hdr" bs args)
      | none => none
    else (tflatMapArsn (nv + bs.length) k).map (.call f bs args)
  | .jnz c t e =>
    match tflatMapArsn nv t, tflatMapArsn nv e with
    | some t', some e' => some (.jnz c t' e')
    | _, _ => none
  | .jump j args => some (.jump j args)
  | .ret vs => some (.ret vs)
  | .exit f args => some (.exit f args)
  | .hlt => some .hlt
  | .group bodies k =>
    match tblocksMapArsn nv bodies, tflatMapArsn nv k with
    | some bodies', some k' => some (.group bodies' k')
    | _, _ => none

private def tblocksMapArsn {rs : List Ty} (nv : Nat) :
    {sig : List (List Ty)} → TBlocks rs sig → Option (TBlocks rs sig)
  | _, .nil => some .nil
  | _, .cons (ts := ts) b bs =>
    match tflatMapArsn (nv + ts.length) b, tblocksMapArsn nv bs with
    | some b', some bs' => some (.cons b' bs')
    | _, _ => none
end

private theorem listGet?_cons_last {α : Type _} (x : α) (xs : List α) (hle : 0 < xs.length) :
    listGet? (x :: xs) ((x :: xs).length - 1) = listGet? xs (xs.length - 1) := by
  rw [show (x :: xs).length - 1 = (xs.length - 1) + 1 from by simp; omega]; rfl

private theorem listGet?_pushTup_last {ts : List Ty} (xs : Tup Val ts)
    (vs : List ((t : Ty) × Val t)) (hle : 0 < vs.length) :
    listGet? (pushTup xs vs) ((pushTup xs vs).length - 1) = listGet? vs (vs.length - 1) := by
  induction ts generalizing vs with
  | nil => cases xs; rfl
  | cons t ts ih =>
    rcases xs with ⟨x, xs⟩
    exact (ih xs (⟨t, x⟩ :: vs) (by simp)).trans (listGet?_cons_last ⟨t, x⟩ vs hle)

private def liftContHdr {ts : List Ty} (c : FullCfg) (J₂ : Cont ts) : Cont ts :=
  fun xs m_s => ∀ ext m_f, M6HdrExtOk ext →
    (Eq m_s ⋆ array64 (c.hdr - 2304) ext) m_f → J₂ xs m_f

private def liftTupContHdr (c : FullCfg) :
    {sig : List (List Ty)} → Tup Cont sig → Tup Cont sig
  | [], () => ()
  | _ :: _, (J, Js) => (liftContHdr c J, liftTupContHdr c Js)

private def LabelsLiftRel (c : FullCfg)
    (ls₁ ls₂ : List ((ts : List Ty) × Cont ts)) : Prop :=
  (∀ (ts : List Ty) (idx : Nat), (lookupL ls₁ ts idx).isSome = (lookupL ls₂ ts idx).isSome) ∧
  ∀ (ts : List Ty) (idx : Nat) (j₁ j₂ : Cont ts),
    lookupL ls₁ ts idx = some j₁ → lookupL ls₂ ts idx = some j₂ →
    ∀ xs m_s m_f ext, M6HdrExtOk ext →
      (Eq m_s ⋆ array64 (c.hdr - 2304) ext) m_f → j₁ xs m_s → j₂ xs m_f

private theorem labelsLiftRel_cons {c : FullCfg} {ts : List Ty}
    {ls₁ ls₂ : List ((us : List Ty) × Cont us)} {J₂ : Cont ts}
    (h : LabelsLiftRel c ls₁ ls₂) :
    LabelsLiftRel c (⟨ts, liftContHdr c J₂⟩ :: ls₁) (⟨ts, J₂⟩ :: ls₂) := by
  refine ⟨fun ts' idx => ?_, fun ts' idx j₁ j₂ hj₁ hj₂ => ?_⟩
  · cases idx with
    | zero => dsimp only [lookupL, listGet?, castListTy]; cases listTyDecEq ts ts' <;> rfl
    | succ k => exact h.1 ts' k
  · cases idx with
    | succ k => exact h.2 ts' k j₁ j₂ hj₁ hj₂
    | zero =>
      dsimp only [lookupL, listGet?, castListTy] at hj₁ hj₂
      cases hdec : listTyDecEq ts ts' with
      | isFalse _ => simp [hdec] at hj₁
      | isTrue heq =>
        subst heq; simp only [hdec, Option.some.injEq] at hj₁ hj₂; subst hj₁ hj₂
        exact fun _ _ _ _ hext hsep hJ => hJ _ _ hext hsep

private theorem labelsLiftRel_pushTup {c : FullCfg} :
    {sig : List (List Ty)} → (Js₂ : Tup Cont sig) →
    {ls₁ ls₂ : List ((ts : List Ty) × Cont ts)} → LabelsLiftRel c ls₁ ls₂ →
    LabelsLiftRel c (pushTup (liftTupContHdr c Js₂) ls₁) (pushTup Js₂ ls₂)
  | [], (), _, _, h => h
  | _ :: _, (_J, Js), _, _, h => labelsLiftRel_pushTup Js (labelsLiftRel_cons h)

private theorem sep_extract_eq {A B : Mem 64 → Prop} {m : Mem 64} (h : (A ⋆ B) m) :
    ∃ m_b, B m_b ∧ (Eq m_b ⋆ A) m := by
  have hB : B = (fun m' => ∃ m_b, B m_b ∧ Eq m_b m') :=
    funext fun m' => propext ⟨fun hb => ⟨m', hb, rfl⟩, fun ⟨_, hb, heq⟩ => heq ▸ hb⟩
  have h1 : (A ⋆ (fun m' => ∃ m_b, B m_b ∧ Eq m_b m')) m := hB ▸ h
  rw [sep_ex_r] at h1; rcases h1 with ⟨m_b, h2⟩; rw [sep_pure_r, sep_comm] at h2; exact ⟨m_b, h2⟩

private theorem sep_join_eq {A P : Mem 64 → Prop} {m_b m : Mem 64}
    (hp : P m_b) (h : (Eq m_b ⋆ A) m) : (A ⋆ P) m := by
  rw [sep_comm]; exact sep_mono (fun _ heq => heq ▸ hp) h

private theorem sep_frame_enter {E M R : Mem 64 → Prop} {m_s m_f : Mem 64}
    (hm : (M ⋆ R) m_s) (hsep : (Eq m_s ⋆ E) m_f) : (M ⋆ (E ⋆ R)) m_f := by
  have h1 : (E ⋆ (M ⋆ R)) m_f := sep_join_eq hm hsep
  rwa [← sep_assoc, sep_comm E M, sep_assoc] at h1

private theorem sep_frame_exit {E M R : Mem 64 → Prop} {m_f : Mem 64}
    (hm : (M ⋆ (E ⋆ R)) m_f) : ∃ m_s, (M ⋆ R) m_s ∧ (Eq m_s ⋆ E) m_f := by
  rw [← sep_assoc, sep_comm M E, sep_assoc] at hm; exact sep_extract_eq hm

private theorem m6o_sep_split_ext {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hm : (FullM6HdrMem c ext s ⋆ R) m) :
    ∃ m_s, (FullMem c s ⋆ R) m_s ∧ (Eq m_s ⋆ array64 (c.hdr - 2304) ext) m :=
  sep_extract_eq (fullM6HdrMem_ext_focus hm)

private theorem m6o_sep_join_fullM6Hdr {c : FullCfg} {ext : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {m_s m_f : Mem 64}
    (hs : (FullMem c s ⋆ R) m_s) (hsep : (Eq m_s ⋆ array64 (c.hdr - 2304) ext) m_f) :
    (FullM6HdrMem c ext s ⋆ R) m_f := fullM6HdrMem_ext_unfocus (sep_join_eq hs hsep)

private structure ArsnLiftHyps (Γ : Env) : Prop where
  alit : ∀ a m Q X, Full.fullAnalyzeLitSpec a m Q X →
    Γ "full_analyze_lit" [i64, i32, i32] [.bool] a m Q X
  arsn : ∀ a m Q X, m6AnalyzeRsnHdrSpec a m Q X →
    Γ "full_analyze_rsn_m6_hdr" [i64, i32, i32] [.bool] a m Q X
  clear : ∀ a m Q X, Full.fullClearAnaSpec a m Q X → Γ "full_clear_ana" [i64] [] a m Q X
  otfsLarge : ∀ a m Q X, Full.fullOtfsLargeSpec a m Q X →
    Γ "full_otfs_large" [i64, i32, i32] [.bool] a m Q X
  otfsBin : ∀ a m Q X, Full.fullOtfsBinSpec a m Q X →
    Γ "full_otfs_bin" [i64, i32, i32] [.bool] a m Q X
  otfsSub : ∀ a m Q X, Full.fullOtfsSubsumeSpec a m Q X →
    Γ "full_otfs_subsume" [i64, i32, i64, i64, .bool] [] a m Q X

private theorem m6o_frame_unchanged_call {Γ : Env} (hΓ : ArsnLiftHyps Γ)
    {c : FullCfg} {ext : List (BitVec 64)} {rs : List Ty}
    {f : String} {as bs : List Ty} (hf_ne : f ≠ "full_analyze_rsn")
    (args' : Tup (Arg Val) as) (k₂ : Tup Val bs → Expr Val Cont rs)
    {m_s m_f : Mem 64} {P : Post bs} {Q₂ : Post rs}
    (hG : arsnLiftEnv f as bs (vals args') m_s P (fun _ _ _ _ => False))
    (hk : ∀ rv m_s' m_f', P rv m_s' → (Eq m_s' ⋆ array64 (c.hdr - 2304) ext) m_f' →
      wp Γ Q₂ (fun _ _ _ _ => False) (k₂ rv) m_f')
    (hsep : (Eq m_s ⋆ array64 (c.hdr - 2304) ext) m_f) :
    wp Γ Q₂ (fun _ _ _ _ => False) (.call f (as := as) (bs := bs) args' k₂) m_f := by
  let E := array64 (c.hdr - 2304) ext
  dsimp only [arsnLiftEnv] at hG
  split at hG
  · exact absurd rfl hf_ne
  · rcases hG with ⟨c', s', R', hc, h1, h2, h3, h4, h5, hm_s, hP'⟩
    rcases args' with ⟨a0, a1, a2, ⟨⟩⟩; dsimp only [vals] at hc
    refine wp_call_of_spec (as := [i64, i32, i32]) (bs := [.bool]) (a0, a1, a2, ()) k₂ ?_
    dsimp only [vals]; rw [hc]
    refine hΓ.alit (c'.hdr, a1.val, a2.val, ()) m_f _ _
      ⟨c', s', E ⋆ R', rfl, h1, h2, h3, h4, h5, sep_frame_enter hm_s hsep,
        fun ok mrk' tmp' tc' tl' mcl' ws1' ant' res' m_f' a b d e f g h i j k l n o p hm' => ?_⟩
    rcases sep_frame_exit hm' with ⟨m_s', hm_s', hsep'⟩
    exact hk (ok, ()) m_s' m_f'
      (hP' ok mrk' tmp' tc' tl' mcl' ws1' ant' res' m_s' a b d e f g h i j k l n o p hm_s') hsep'
  · rcases hG with ⟨c', s', R', hc, hlen', hm_s, hP'⟩
    rcases args' with ⟨a0, ⟨⟩⟩; dsimp only [vals] at hc
    refine wp_call_of_spec (as := [i64]) (bs := []) (a0, ()) k₂ ?_
    dsimp only [vals]; rw [hc]
    refine hΓ.clear (c'.hdr, ()) m_f _ _
      ⟨c', s', E ⋆ R', rfl, hlen', sep_frame_enter hm_s hsep, fun mrk' m_f' a b d e hm' => ?_⟩
    rcases sep_frame_exit hm' with ⟨m_s', hm_s', hsep'⟩
    exact hk () m_s' m_f' (hP' mrk' m_s' a b d e hm_s') hsep'
  · rcases hG with ⟨c', F0', F_cur', cut', idx_u', s', R', hc, a, b, d, e, f, g, h, i, j, k, l, n,
      hm_s, hP'⟩
    rcases args' with ⟨a0, a1, a2, ⟨⟩⟩; dsimp only [vals] at hc
    refine wp_call_of_spec (as := [i64, i32, i32]) (bs := [.bool]) (a0, a1, a2, ()) k₂ ?_
    dsimp only [vals]; rw [hc]
    refine hΓ.otfsLarge (c'.hdr, a1.val, a2.val, ()) m_f _ _
      ⟨c', F0', F_cur', cut', idx_u', s', E ⋆ R', rfl, a, b, d, e, f, g, h, i, j, k, l, n,
        sep_frame_enter hm_s hsep,
        fun ok ar' wv' ws' wl' wu' oom' sc' m_f' p1 p2 p3 p4 p5 p6 p7 p8 p9 hm' => ?_⟩
    rcases sep_frame_exit hm' with ⟨m_s', hm_s', hsep'⟩
    exact hk (ok, ()) m_s' m_f'
      (hP' ok ar' wv' ws' wl' wu' oom' sc' m_s' p1 p2 p3 p4 p5 p6 p7 p8 p9 hm_s') hsep'
  · rcases hG with ⟨c', F0', F_cur', cut', idx_u', s', R', hc, a, b, d, e, f, g, h, i, j, k, l, n,
      hm_s, hP'⟩
    rcases args' with ⟨a0, a1, a2, ⟨⟩⟩; dsimp only [vals] at hc
    refine wp_call_of_spec (as := [i64, i32, i32]) (bs := [.bool]) (a0, a1, a2, ()) k₂ ?_
    dsimp only [vals]; rw [hc]
    refine hΓ.otfsBin (c'.hdr, a1.val, a2.val, ()) m_f _ _
      ⟨c', F0', F_cur', cut', idx_u', s', E ⋆ R', rfl, a, b, d, e, f, g, h, i, j, k, l, n,
        sep_frame_enter hm_s hsep,
        fun ok ar' ag' wv' ws' wl' wu' nb' ct' cr' c0' c1' oom' sc' m_f'
          p1 p2 p3 p4 p5 p6 p7 p8 p9 hm' => ?_⟩
    rcases sep_frame_exit hm' with ⟨m_s', hm_s', hsep'⟩
    exact hk (ok, ()) m_s' m_f' (hP' ok ar' ag' wv' ws' wl' wu' nb' ct' cr' c0' c1'
      oom' sc' m_s' p1 p2 p3 p4 p5 p6 p7 p8 p9 hm_s') hsep'
  · rcases hG with ⟨c', F0', F_cur', cut', s', R', hc, a, b, d, e, hm_s, hP'⟩
    rcases args' with ⟨a0, a1, a2, a3, a4, ⟨⟩⟩; dsimp only [vals] at hc
    refine wp_call_of_spec (as := [i64, i32, i64, i64, .bool]) (bs := [])
      (a0, a1, a2, a3, a4, ()) k₂ ?_
    dsimp only [vals]; rw [hc]
    refine hΓ.otfsSub (c'.hdr, a1.val, a2.val, a3.val, a4.val, ()) m_f _ _
      ⟨c', F0', F_cur', cut', s', E ⋆ R', rfl, a, b, d, e, sep_frame_enter hm_s hsep,
        fun ar' ag' ni' nr' m_f' p1 p2 p3 p4 p5 hm' => ?_⟩
    rcases sep_frame_exit hm' with ⟨m_s', hm_s', hsep'⟩
    exact hk () m_s' m_f' (hP' ar' ag' ni' nr' m_s' p1 p2 p3 p4 p5 hm_s') hsep'
  · exact False.elim hG

private theorem denoteArgs3_inv {t0 t1 t2 : Ty} {vs : List ((t : Ty) × Val t)}
    {a0 : Arg K t0} {a1 : Arg K t1} {a2 : Arg K t2} {args' : Tup (Arg Val) [t0, t1, t2]}
    (hd : denoteArgs (ts := [t0, t1, t2]) vs (a0, a1, a2, ()) = some args') :
    ∃ a0' a1' a2', denoteArg vs a0 = some a0' ∧ denoteArg vs a1 = some a1' ∧
      denoteArg vs a2 = some a2' ∧ args' = (a0', a1', a2', ()) := by
  dsimp only [denoteArgs] at hd
  cases h0 : denoteArg vs a0 with | none => simp [h0] at hd | some x0 =>
  cases h1 : denoteArg vs a1 with | none => simp [h0, h1] at hd | some x1 =>
  cases h2 : denoteArg vs a2 with | none => simp [h0, h1, h2] at hd | some x2 =>
  simp [h0, h1, h2] at hd; subst hd; exact ⟨x0, x1, x2, rfl, rfl, rfl, rfl⟩

mutual
private theorem denote_wp_arsn_lift {Γ : Env} (hΓ : ArsnLiftHyps Γ)
    {c : FullCfg} (hcfg : FullM6HdrCfgOk c) {rs : List Ty} :
    ∀ (tf₁ tf₂ : TFlat rs)
      (vs : List ((t : Ty) × Val t)) (ls₁ ls₂ : List ((ts : List Ty) × Cont ts)),
      0 < vs.length → listGet? vs (vs.length - 1) = some ⟨i64, c.hdr⟩ →
      LabelsLiftRel c ls₁ ls₂ → tflatMapArsn vs.length tf₁ = some tf₂ →
      ∀ (Q₁ Q₂ : Post rs),
        (∀ rv m_s ext m_f, M6HdrExtOk ext →
          (Eq m_s ⋆ array64 (c.hdr - 2304) ext) m_f → Q₁ rv m_s → Q₂ rv m_f) →
        ∀ m_s ext m_f, M6HdrExtOk ext → (Eq m_s ⋆ array64 (c.hdr - 2304) ext) m_f →
          wp arsnLiftEnv Q₁ (fun _ _ _ _ => False) (denote Val Cont tf₁ vs ls₁) m_s →
          wp Γ Q₂ (fun _ _ _ _ => False) (denote Val Cont tf₂ vs ls₂) m_f
  | .let_ (ts := ts) op k, tf₂, vs, ls₁, ls₂, hv_pos, hlast, hls, hmap, Q₁, Q₂, hQ,
      m_s, ext, m_f, hext, hsep, hwp => by
    dsimp only [tflatMapArsn] at hmap
    cases hk_eq : tflatMapArsn (vs.length + ts.length) k with
    | none => simp [hk_eq] at hmap | some k' =>
    simp only [hk_eq, Option.map_some, Option.some.injEq] at hmap; subst tf₂
    dsimp only [denote] at hwp ⊢
    cases hd : denoteArgs vs op.args with | none => rw [hd] at hwp; cases hwp | some args' =>
    rw [hd] at hwp; dsimp only at hwp ⊢; dsimp only [wp] at hwp ⊢
    refine OpCode.wp_mono op.code _ (fun r h => ?_) hwp
    have hp := pushTup_length r vs
    exact denote_wp_arsn_lift hΓ hcfg k k' (pushTup r vs) ls₁ ls₂ (by rw [hp]; omega)
      (by simpa using (listGet?_pushTup_last r vs hv_pos).trans hlast) hls
      (by rw [hp]; exact hk_eq) Q₁ Q₂ hQ m_s ext m_f hext hsep h
  | .load t a k, tf₂, vs, ls₁, ls₂, hv_pos, hlast, hls, hmap, Q₁, Q₂, hQ,
      m_s, ext, m_f, hext, hsep, hwp => by
    dsimp only [tflatMapArsn] at hmap
    cases hk_eq : tflatMapArsn (vs.length + 1) k with | none => simp [hk_eq] at hmap | some k' =>
    simp only [hk_eq, Option.map_some, Option.some.injEq] at hmap; subst tf₂
    dsimp only [denote] at hwp ⊢
    cases hd : denoteArg vs a with | none => rw [hd] at hwp; cases hwp | some a' =>
    rw [hd] at hwp; dsimp only at hwp ⊢; rcases hwp with ⟨v, hld, hwp⟩
    exact ⟨v, loadVal_frame hsep hld, denote_wp_arsn_lift hΓ hcfg k k' (⟨t, v⟩ :: vs) ls₁ ls₂
      (by simp) ((listGet?_cons_last ⟨t, v⟩ vs hv_pos).trans hlast) hls hk_eq Q₁ Q₂ hQ m_s ext m_f
      hext hsep hwp⟩
  | .store v a k, tf₂, vs, ls₁, ls₂, hv_pos, hlast, hls, hmap, Q₁, Q₂, hQ,
      m_s, ext, m_f, hext, hsep, hwp => by
    dsimp only [tflatMapArsn] at hmap
    cases hk_eq : tflatMapArsn vs.length k with | none => simp [hk_eq] at hmap | some k' =>
    simp only [hk_eq, Option.map_some, Option.some.injEq] at hmap; subst tf₂
    dsimp only [denote] at hwp ⊢
    cases hv : denoteArg vs v with | none => rw [hv] at hwp; cases hwp | some v' =>
    cases ha : denoteArg vs a with | none => rw [hv, ha] at hwp; cases hwp | some a' =>
    rw [hv, ha] at hwp; dsimp only at hwp ⊢; rcases hwp with ⟨hok, hwp⟩
    exact ⟨storeOk_frame hsep hok, denote_wp_arsn_lift hΓ hcfg k k' vs ls₁ ls₂
      hv_pos hlast hls hk_eq Q₁ Q₂ hQ _ ext _ hext (storeMem_frame hsep hok v'.val) hwp⟩
  | .call f bs args k, tf₂, vs, ls₁, ls₂, hv_pos, hlast, hls, hmap, Q₁, Q₂, hQ,
      m_s, ext, m_f, hext, hsep, hwp => by
    dsimp only [tflatMapArsn] at hmap
    by_cases hf_arsn : f = "full_analyze_rsn"
    · subst hf_arsn; simp only [↓reduceIte] at hmap
      cases ht_eq : tflatMapArsnCall bs args vs.length with
      | none => simp [ht_eq] at hmap | some a0 =>
      cases hk_eq : tflatMapArsn (vs.length + bs.length) k with
      | none => simp [ht_eq, hk_eq] at hmap
      | some k' =>
        simp only [ht_eq, hk_eq, Option.map_some, Option.some.injEq] at hmap; subst tf₂
        dsimp only [tflatMapArsnCall] at ht_eq
        split at ht_eq <;> try cases ht_eq
        rename_i _i a1 a2; split at ht_eq <;> try cases ht_eq
        rename_i _iv idx; split at ht_eq <;> try cases ht_eq
        rename_i hdec
        have hiv : idx = vs.length - 1 := by rw [decide_eq_true_eq] at hdec; exact hdec.2
        subst hiv; dsimp only [denote] at hwp ⊢
        cases hd : denoteArgs (ts := [i64, i32, i32]) vs
            (Arg.var (vs.length - 1), a1, a2, ()) with
        | none => rw [hd] at hwp; cases hwp
        | some args' =>
          rw [hd] at hwp; dsimp only at hwp ⊢; rcases hwp with ⟨P, _E, hG, hP, _hE⟩
          have hspec : Full.fullAnalyzeRsnSpec (vals args') m_s P (fun _ _ _ _ => False) := hG
          rcases denoteArgs3_inv hd with ⟨a0', a1', a2', ha0, _ha1, _ha2, h_eq⟩
          have ha0_eq : a0' = .var c.hdr := by
            simpa only [denoteArg, lookupV, hlast, castTy, ↓reduceDIte,
              Option.some.injEq] using ha0.symm
          have hargs_v : vals args' = (c.hdr, a1'.val, a2'.val, ()) := by rw [h_eq, ha0_eq]; rfl
          rw [hargs_v] at hspec
          rcases hspec with ⟨c', F0', F_cur', cut', s', R', hc'_eq, hlen', hcut', hcov',
            htl', htc', href', hm_s, hP'⟩
          have hcfg' := M6HdrCfgOk_of_le (hc'_eq ▸ M6HdrCfgOk_le hcfg)
          rw [hc'_eq] at hargs_v; refine wp_call_of_spec args' _ ?_; rw [hargs_v]
          refine hΓ.arsn (c'.hdr, a1'.val, a2'.val, ()) m_f _ _
            ⟨c', F0', F_cur', cut', ext, s', R', rfl, hcfg', hext, hlen', hcut', hcov', htl',
              htc', href', m6o_sep_join_fullM6Hdr hm_s (by rwa [← hc'_eq]),
              fun ok mrk' tmp' tc' tl' mcl' arena' sc' ext' m_f' hext' _ hlen2 hcut2 hcov2 hpre2
                hws2 htl2 htl_cv htc2 hrefs2 har2 hmrk2 htmp2 hnew2 hjok2 hjnodup2 hdiff2 hres2 hok2
                hm_f' => ?_⟩
          rcases m6o_sep_split_ext hm_f' with ⟨m_s', hm_s', hsep'⟩
          have hp_ok := hP' ok mrk' tmp' tc' tl' mcl' arena' sc' m_s' hlen2 hcut2 hcov2 hpre2 hws2
            htl2 htl_cv htc2 hrefs2 har2 hmrk2 htmp2 hnew2 hjok2 hjnodup2 hdiff2 hres2 hok2 hm_s'
          have hlen_p := pushTup_length (as := [.bool]) (ok, ()) vs
          exact denote_wp_arsn_lift hΓ hcfg k k'
            (pushTup (as := [.bool]) (f := Val) (ok, ()) vs) ls₁ ls₂ (by rw [hlen_p]; omega)
            ((listGet?_pushTup_last (ts := [.bool]) (ok, ()) vs hv_pos).trans hlast) hls
            (by simpa [hlen_p] using hk_eq) Q₁ Q₂ hQ m_s' ext' m_f' hext' (by rwa [hc'_eq])
            (hP ((ok, ()) : Tup Val [.bool]) m_s' hp_ok)
    · simp only [hf_arsn, ↓reduceIte] at hmap
      cases hk_eq : tflatMapArsn (vs.length + bs.length) k with
      | none => simp [hk_eq] at hmap
      | some k' =>
        simp only [hk_eq, Option.map_some, Option.some.injEq] at hmap; subst tf₂
        dsimp only [denote] at hwp ⊢
        cases hd : denoteArgs vs args with | none => rw [hd] at hwp; cases hwp | some args' =>
        rw [hd] at hwp; dsimp only at hwp ⊢; rcases hwp with ⟨P, _E, hG, hP, _hE⟩
        refine m6o_frame_unchanged_call hΓ hf_arsn args'
          (fun rv => denote Val Cont k' (pushTup rv vs) ls₂) hG
          (fun rv m_s' m_f' hp hsep' => ?_) hsep
        have hlen_p := pushTup_length rv vs
        exact denote_wp_arsn_lift hΓ hcfg k k' (pushTup rv vs) ls₁ ls₂ (by rw [hlen_p]; omega)
          ((listGet?_pushTup_last rv vs hv_pos).trans hlast) hls (by rw [hlen_p]; exact hk_eq)
          Q₁ Q₂ hQ m_s' ext m_f' hext hsep' (hP rv m_s' hp)
  | .jnz cd t e, tf₂, vs, ls₁, ls₂, hv_pos, hlast, hls, hmap, Q₁, Q₂, hQ,
      m_s, ext, m_f, hext, hsep, hwp => by
    dsimp only [tflatMapArsn] at hmap
    cases ht_eq : tflatMapArsn vs.length t with | none => simp [ht_eq] at hmap | some t' =>
    cases he_eq : tflatMapArsn vs.length e with | none => simp [ht_eq, he_eq] at hmap | some e' =>
    simp only [ht_eq, he_eq, Option.some.injEq] at hmap; subst tf₂; dsimp only [denote] at hwp ⊢
    cases hd : denoteArg vs cd with | none => rw [hd] at hwp; cases hwp | some c' =>
    rw [hd] at hwp; dsimp only at hwp ⊢
    exact ⟨fun hc => denote_wp_arsn_lift hΓ hcfg t t' vs ls₁ ls₂ hv_pos hlast hls ht_eq
        Q₁ Q₂ hQ m_s ext m_f hext hsep (hwp.1 hc),
      fun hc => denote_wp_arsn_lift hΓ hcfg e e' vs ls₁ ls₂ hv_pos hlast hls he_eq
        Q₁ Q₂ hQ m_s ext m_f hext hsep (hwp.2 hc)⟩
  | .jump (ts := ts) j args, tf₂, vs, ls₁, ls₂, _, _, hls, hmap, _, _, _,
      m_s, ext, m_f, hext, hsep, hwp => by
    dsimp only [tflatMapArsn] at hmap; injection hmap with hmap'; subst tf₂
    dsimp only [denote] at hwp ⊢
    cases hj1 : lookupL ls₁ ts j with | none => rw [hj1] at hwp; cases hwp | some j₁ =>
    cases hj2 : lookupL ls₂ ts j with
    | none => have hs := hls.1 ts j; rw [hj1, hj2] at hs; simp at hs
    | some j₂ =>
      cases ha : denoteArgs vs args with | none => rw [hj1, ha] at hwp; cases hwp | some args' =>
      rw [hj1, ha] at hwp; dsimp only at hwp ⊢
      exact hls.2 ts j j₁ j₂ hj1 hj2 (vals args') m_s m_f ext hext hsep hwp
  | .ret vs', tf₂, vs, _, _, _, _, _, hmap, Q₁, Q₂, hQ, m_s, ext, m_f, hext, hsep, hwp => by
    dsimp only [tflatMapArsn] at hmap; injection hmap with hmap'; subst tf₂
    dsimp only [denote] at hwp ⊢
    cases ha : denoteArgs vs vs' with | none => rw [ha] at hwp; cases hwp | some vs'' =>
    rw [ha] at hwp; dsimp only at hwp ⊢; exact hQ (vals vs'') m_s ext m_f hext hsep hwp
  | .exit _ args, tf₂, vs, _, _, _, _, _, hmap, _, _, _, _, _, _, _, _, hwp => by
    dsimp only [tflatMapArsn] at hmap; injection hmap with hmap'; subst tf₂
    dsimp only [denote] at hwp ⊢
    cases ha : denoteArgs vs args <;> (rw [ha] at hwp; cases hwp)
  | .hlt, tf₂, _, _, _, _, _, _, hmap, _, _, _, _, _, _, _, _, hwp => by
    dsimp only [tflatMapArsn] at hmap; injection hmap with hmap'; subst tf₂; exact hwp
  | .group bodies k, tf₂, vs, ls₁, ls₂, hv_pos, hlast, hls, hmap, Q₁, Q₂, hQ,
      m_s, ext, m_f, hext, hsep, hwp => by
    dsimp only [tflatMapArsn] at hmap
    cases hb_eq : tblocksMapArsn vs.length bodies with
    | none => simp [hb_eq] at hmap | some bodies' =>
    cases hk_eq : tflatMapArsn vs.length k with
    | none => simp [hb_eq, hk_eq] at hmap
    | some k' =>
      simp only [hb_eq, hk_eq, Option.some.injEq] at hmap; subst tf₂
      dsimp only [denote, wp] at hwp ⊢
      intro Js₂ hc₂; let Js₁ := liftTupContHdr c Js₂; have hls' := labelsLiftRel_pushTup Js₂ hls
      exact denote_wp_arsn_lift hΓ hcfg k k' vs (pushTup Js₁ ls₁) (pushTup Js₂ ls₂)
        hv_pos hlast hls' hk_eq Q₁ Q₂ hQ m_s ext m_f hext hsep (hwp Js₁ (denoteB_wp_arsn_lift
          hΓ hcfg bodies bodies' vs (pushTup Js₁ ls₁) (pushTup Js₂ ls₂)
          hv_pos hlast hls' hb_eq Q₁ Q₂ hQ Js₂ hc₂))

private theorem denoteB_wp_arsn_lift {Γ : Env} (hΓ : ArsnLiftHyps Γ)
    {c : FullCfg} (hcfg : FullM6HdrCfgOk c) {rs : List Ty} :
    {sig : List (List Ty)} → (tb₁ tb₂ : TBlocks rs sig) →
      (vs : List ((t : Ty) × Val t)) → (ls₁ ls₂ : List ((ts : List Ty) × Cont ts)) →
      0 < vs.length → listGet? vs (vs.length - 1) = some ⟨i64, c.hdr⟩ →
      LabelsLiftRel c ls₁ ls₂ → tblocksMapArsn vs.length tb₁ = some tb₂ →
      ∀ (Q₁ Q₂ : Post rs),
        (∀ rv m_s ext m_f, M6HdrExtOk ext →
          (Eq m_s ⋆ array64 (c.hdr - 2304) ext) m_f → Q₁ rv m_s → Q₂ rv m_f) →
        ∀ (Js₂ : Tup Cont sig),
          Closed Γ Q₂ (fun _ _ _ _ => False) (denoteB Val Cont tb₂ vs ls₂) Js₂ →
          Closed arsnLiftEnv Q₁ (fun _ _ _ _ => False) (denoteB Val Cont tb₁ vs ls₁)
            (liftTupContHdr c Js₂)
  | [], .nil, tb₂, _, _, _, _, _, _, hmap, _, _, _, (), _ => by
    dsimp only [tblocksMapArsn] at hmap; injection hmap with hmap'; subst tb₂; trivial
  | _, .cons (ts := ts) b bs, tb₂, vs, ls₁, ls₂, hv_pos, hlast, hls, hmap, Q₁, Q₂, hQ,
      (J, Js), hc => by
    dsimp only [tblocksMapArsn] at hmap
    cases hb_eq : tflatMapArsn (vs.length + ts.length) b with
    | none => simp [hb_eq] at hmap
    | some b' =>
      cases hbs_eq : tblocksMapArsn vs.length bs with
      | none => simp [hb_eq, hbs_eq] at hmap
      | some bs' =>
        simp only [hb_eq, hbs_eq, Option.some.injEq] at hmap; subst tb₂
        dsimp only [denoteB, Closed] at hc ⊢
        refine ⟨fun xs m_s hb ext m_f hext hsep => ?_,
          denoteB_wp_arsn_lift hΓ hcfg bs bs' vs ls₁ ls₂ hv_pos hlast hls hbs_eq Q₁ Q₂ hQ Js hc.2⟩
        have hp := pushTup_length xs vs
        exact hc.1 xs m_f (denote_wp_arsn_lift hΓ hcfg b b' (pushTup xs vs) ls₁ ls₂
          (by rw [hp]; omega) ((listGet?_pushTup_last xs vs hv_pos).trans hlast) hls
          (by rw [hp]; exact hb_eq) Q₁ Q₂ hQ m_s ext m_f hext hsep hb)
end

theorem full_deduce_1uip_m6_hdr_wp (Γ : Env)
    (hAlit : ∀ a m Q X, Full.fullAnalyzeLitSpec a m Q X →
      Γ "full_analyze_lit" [i64, i32, i32] [.bool] a m Q X)
    (hArsn : ∀ a m Q X, m6AnalyzeRsnHdrSpec a m Q X →
      Γ "full_analyze_rsn_m6_hdr" [i64, i32, i32] [.bool] a m Q X)
    (hClear : ∀ a m Q X, Full.fullClearAnaSpec a m Q X →
      Γ "full_clear_ana" [i64] [] a m Q X)
    (hOtfsLarge : ∀ a m Q X, Full.fullOtfsLargeSpec a m Q X →
      Γ "full_otfs_large" [i64, i32, i32] [.bool] a m Q X)
    (hOtfsBin : ∀ a m Q X, Full.fullOtfsBinSpec a m Q X →
      Γ "full_otfs_bin" [i64, i32, i32] [.bool] a m Q X)
    (hOtfsSub : ∀ a m Q X, Full.fullOtfsSubsumeSpec a m Q X →
      Γ "full_otfs_subsume" [i64, i32, i64, i64, .bool] [] a m Q X) :
    ∀ a m Q X, m6Deduce1uipHdrSpec a m Q X →
      Func.wp Γ full_deduce_1uip_m6_hdr_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  rcases hs with ⟨c, F0, F_cur, cut, ext, s, R, rfl, hcfg, hext, hcut, hlvl, hcf, hm, hQ⟩
  have hmap : tflatMapArsn 1 (reifyFunc FullM6MinShrink.full_deduce_1uip_m6_body) =
      some (reifyFunc full_deduce_1uip_m6_hdr_body) := by t_kernel_rfl
  rcases m6o_sep_split_ext hm with ⟨m_s, hm_s, hsep⟩
  let Q_s : Post [i64] := fun (r, ()) m_s' => ∀ ext' m_f', M6HdrExtOk ext' →
    (Eq m_s' ⋆ array64 (c.hdr - 2304) ext') m_f' → Q (r, ()) m_f'
  have hwp_old : Func.wp arsnLiftEnv FullM6MinShrink.full_deduce_1uip_m6_body
      (c.hdr, ()) m_s Q_s (fun _ _ _ _ => False) :=
    FullM6MinShrink.full_deduce_1uip_m6_wp arsnLiftEnv (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
      (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
      (c.hdr, ()) m_s Q_s (fun _ _ _ _ => False) ⟨c, F0, F_cur, cut, s, R, rfl, hcut, hlvl, hcf,
        hm_s, fun r s' m_s' h1 h2 h3 h4 h5 h6 h7 h8 h9 hm_s' ext' m_f' hext' hsep' =>
          hQ r ext' s' m_f' hext' h1 h2 h3 h4 h5 h6 h7 h8 h9 (m6o_sep_join_fullM6Hdr hm_s' hsep')⟩
  have hden_old : wp arsnLiftEnv Q_s (fun _ _ _ _ => False)
      (denote Val Cont (reifyFunc FullM6MinShrink.full_deduce_1uip_m6_body)
        [⟨i64, c.hdr⟩] []) m_s :=
    Func.renorm_spec FullM6MinShrink.full_deduce_1uip_m6_wf hwp_old
  have hden_new : wp Γ Q (fun _ _ _ _ => False)
      (denote Val Cont (reifyFunc full_deduce_1uip_m6_hdr_body) [⟨i64, c.hdr⟩] []) m :=
    denote_wp_arsn_lift ⟨hAlit, hArsn, hClear, hOtfsLarge, hOtfsBin, hOtfsSub⟩ hcfg
      (reifyFunc FullM6MinShrink.full_deduce_1uip_m6_body)
      (reifyFunc full_deduce_1uip_m6_hdr_body)
      [⟨i64, c.hdr⟩] [] [] (by simp) rfl ⟨fun _ _ => rfl, fun _ _ _ _ hj => by cases hj⟩ hmap
      Q_s Q (fun (r, ()) m_s' ext' m_f' hext' hsep' hq => hq ext' m_f' hext' hsep')
      m_s ext m hext hsep hden_old
  have hren_hdr : Func.renorm full_deduce_1uip_m6_hdr_body = full_deduce_1uip_m6_hdr_body := by
    t_kernel_rfl
  exact wp_mono (fun _ _ h => h) (fun _ _ _ _ h => False.elim h) _ _
    (by rw [← hren_hdr]; exact hden_new)

section AnalyzeCoreAndSwitchMode

open LeanQbe.T.Examples.LratBytes
open scoped FullArenaTactics

/-! ### Unused `m6o_upd_heap_pos` removed; `AnalyzeCore` helpers -/

private theorem m6o_cut_with_conflicts {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s : FullState} (h : FullCutInvW c F0 F_cur cut s)
    (hcf : FullConflictOkCut F_cur cut s) (k' : BitVec 64) :
    let s' : FullState := { s with scratch := { s.scratch with conflicts := k' } }
    FullCutInvW c F0 F_cur cut s' ∧ FullConflictOkCut F_cur cut s' :=
  ⟨⟨⟨h.1.core_ok, fullScratch_lengthsOk_of_arr_len h.1.scratch_ok rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩,
    h.2.1, h.2.2.1, h.2.2.2.1,
    FullExtScratchOk.of_pres h.2.2.2.2.1 ⟨rfl, rfl⟩ (fun _ hr => hr), h.2.2.2.2.2⟩, hcf⟩

private theorem m6o_cut_with_tmp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s : FullState} (h : FullCutInvW c F0 F_cur cut s)
    (hcf : FullConflictOkCut F_cur cut s) {tmp' : List (BitVec 32)} {tl' : Nat}
    (htarr : tmp'.length = c.max_vars) (htle : tl' ≤ c.max_vars) :
    let s' : FullState := { s with core := { s.core with tmp := tmp', tmp_len := tl' } }
    FullCutInvW c F0 F_cur cut s' ∧ FullConflictOkCut F_cur cut s' :=
  ⟨⟨⟨{ h.1.core_ok with tmp_len_arr := htarr, tmp_len_le := htle }, h.1.scratch_ok⟩,
    deduce_same_core_cut h.2.1 s.core.mrk tmp' s.core.tmp_cnt tl' s.core.min_clr_len,
    h.2.2.1, h.2.2.2.1,
    FullExtScratchOk.of_pres h.2.2.2.2.1 ⟨rfl, rfl⟩ (fun _ hr => hr), h.2.2.2.2.2⟩, hcf⟩

private theorem m6o_cut_of_restoreBump {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {s : FullState} (h : FullCutInvW c F0 F_cur cut s)
    (hcf : FullConflictOkCut F_cur cut s) {mrk' : List (BitVec 8)} {mcl' : Nat} {sc' : FullScratch}
    (hlen' : ({ core := { s.core with mrk := mrk', min_clr_len := mcl' },
                 scratch := sc' } : FullState).LengthsOk c)
    (hmrk0' : ∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8)
    (hpres : FullExtScratchPres s
      { core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' }) :
    let s' : FullState :=
      { core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' }
    FullCutInvW c F0 F_cur cut s' ∧ FullConflictOkCut F_cur cut s' :=
  ⟨⟨hlen', deduce_same_core_cut h.2.1 mrk' s.core.tmp s.core.tmp_cnt s.core.tmp_len mcl',
    ⟨hmrk0', h.2.2.1.2⟩, h.2.2.2.1,
    FullExtScratchOk.of_pres h.2.2.2.2.1 hpres (fun _ hr => hr), h.2.2.2.2.2⟩, hcf⟩

private theorem m6o_otfs_of_restoreBump {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullOtfsInvW c F0 F_cur s)
    {mrk' : List (BitVec 8)} {mcl' : Nat} {sc' : FullScratch}
    (hlen' : ({ core := { s.core with mrk := mrk', min_clr_len := mcl' },
                 scratch := sc' } : FullState).LengthsOk c)
    (hmrk0' : ∀ v < c.max_vars, mrk'[v]?.getD 0#8 = 0#8)
    (hpres : FullExtScratchPres s
      { core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' }) :
    FullOtfsInvW c F0 F_cur
      { core := { s.core with mrk := mrk', min_clr_len := mcl' }, scratch := sc' } :=
  ⟨hlen', { h.2.1 with
      arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
      watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
    ⟨hmrk0', h.2.2.1.2⟩, h.2.2.2.1,
    FullExtScratchOk.of_pres h.2.2.2.2.1 hpres (fun _ hr => hr), h.2.2.2.2.2⟩

private theorem m6o_otfs_of_safetySlice {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (h : FullOtfsInvW c F0 F_cur s) (hlen' : s'.LengthsOk c)
    (hcore : s'.core = s.core) (hpres : FullExtScratchPres s s') :
    FullOtfsInvW c F0 F_cur s' :=
  ⟨hlen', hcore ▸ h.2.1, by unfold FullLitMarksClear FullMrkZero; rw [hcore]; exact h.2.2.1,
    by unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
       rw [hcore]; exact h.2.2.2.1,
    fullExtScratchOk_of_core_eq h.2.2.2.2.1 hpres hcore, hcore ▸ h.2.2.2.2.2⟩

private def CoreLoopInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (R : Mem 64 → Prop) (iter_lim : BitVec 64)
    (st : BitVec 64 × FullState × List (BitVec 64)) (m' : Mem 64) : Prop :=
  ∃ cut', cut' ≤ st.2.1.core.trail_end ∧ FullCutInvW c F0 F_cur cut' st.2.1 ∧
    FullConflictOkCut F_cur cut' st.2.1 ∧ M6HdrExtOk st.2.2 ∧
    st.2.1.core.cur_vars = s.core.cur_vars ∧ st.2.1.core.fuel = s.core.fuel ∧
    st.2.1.core.cur_level ≤ s.core.cur_level ∧ st.2.1.scratch.work_stk2 = s.scratch.work_stk2 ∧
    st.1.toNat ≤ iter_lim.toNat ∧
    (FullMem c st.2.1 ⋆ (m6ExtMem (m6ExtAddr c.hdr) st.2.2 ⋆ R)) m'

private def CoreShrinkPost (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s : FullState) (s' : FullState) : Prop :=
  FullOtfsInvW c F0 F_cur s' ∧ 0 < s'.core.cur_level ∧
  1 ≤ s'.core.tmp_len ∧ s'.core.tmp_len ≤ s'.core.cur_vars ∧
  (List.map (fun x => x.toNat / 2) (List.take s'.core.tmp_len s'.core.tmp)).Nodup ∧
  (∀ k < s'.core.tmp_len, let l := (s'.core.tmp[k]?.getD 0#32).toNat
    l < 2 * s'.core.cur_vars ∧ s'.core.vals[l]?.getD 0#8 = 255#8) ∧
  (∀ k, 1 ≤ k → k < s'.core.tmp_len →
    let lv := (s'.core.lvl[(s'.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
    0 < lv ∧ lv < s'.core.cur_level ∧
    lv ≤ (s'.core.lvl[(s'.core.tmp[s'.core.tmp_len - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) ∧
  (cnfOfClauses F_cur).EntailsClause
    (cnfClause (List.map BitVec.toNat (List.take s'.core.tmp_len s'.core.tmp))) ∧
  s'.core.cur_vars = s.core.cur_vars ∧ s'.core.fuel = s.core.fuel ∧
  s'.core.cur_level ≤ s.core.cur_level ∧ s'.scratch.work_stk2 = s.scratch.work_stk2

private def CoreCutJoin (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (cut : Nat) (s : FullState) (st : FullState) : Prop :=
  cut ≤ st.core.trail_end ∧ FullCutInvW c F0 F_cur cut st ∧ FullConflictOkCut F_cur cut st ∧
  st.core.cur_vars = s.core.cur_vars ∧ st.core.fuel = s.core.fuel ∧
  st.core.cur_level ≤ s.core.cur_level ∧ st.scratch.work_stk2 = s.scratch.work_stk2

def m6MinShrinkWsortSpec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullOtfsWitnessInv c F0 F_cur s.core ∧ FullLitMarksClear c s ∧
    1 ≤ s.core.tmp_len ∧ s.core.tmp_len ≤ s.core.cur_vars ∧
    ((s.core.tmp.take s.core.tmp_len).map fun x => x.toNat / 2).Nodup ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s.core.tmp.take s.core.tmp_len).map BitVec.toNat)) ∧
    (∀ k < s.core.tmp_len, let l := (s.core.tmp[k]?.getD 0#32).toNat
      l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
    (∀ k, 1 ≤ k → k < s.core.tmp_len →
      let lv := (s.core.lvl[(s.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
      0 < lv ∧ lv < s.core.cur_level) ∧
    (s.core.lvl[(s.core.tmp[0]?.getD 0#32).toNat / 2]?.getD 0#32).toNat = s.core.cur_level ∧
    (FullMem c s ⋆ R) m ∧
    ∀ tmp' tl' mrk' mstk' mclr' mcl' mcf' conf' llits' mrem' sstk' wsort' m',
      let s' : FullState :=
        { s with
          core := { s.core with tmp := tmp', tmp_len := tl', mrk := mrk', min_stk := mstk',
                                min_clr := mclr', min_clr_len := mcl', min_clr_full := mcf' }
          scratch := { s.scratch with conflicts := conf', learned_lits := llits',
                                      min_removed := mrem', shrink_stk := sstk',
                                      wsort := wsort' } }
      s'.LengthsOk c → FullOtfsWitnessInv c F0 F_cur s'.core → FullLitMarksClear c s' →
      1 ≤ tl' → tl' ≤ s.core.tmp_len → tmp'[0]? = s.core.tmp[0]? →
      ((tmp'.take tl').map fun x => x.toNat / 2).Nodup →
      (∀ j, 1 ≤ j → j < tl' →
        let l := (tmp'[j]?.getD 0#32).toNat
        let lv := (s.core.lvl[l / 2]?.getD 0#32).toNat
        l < 2 * s.core.cur_vars ∧ s.core.vals[l]?.getD 0#8 = 0xFF#8 ∧
        0 < lv ∧ lv < s.core.cur_level ∧
        lv ≤ (s.core.lvl[(tmp'[tl' - 1]?.getD 0#32).toNat / 2]?.getD 0#32).toNat) →
      (cnfOfClauses F_cur).EntailsClause (cnfClause ((tmp'.take tl').map BitVec.toNat)) →
      (FullMem c s' ⋆ R) m' → Q () m'

theorem full_analyze_core_m6_any_wp (Γ : Env)
    (hOneLit : ∀ a m Q X, Full.fullOneLitConflSpec a m Q X →
      Γ "full_one_lit_confl" [i64] [i64] a m Q X)
    (hFailed : ∀ a m Q X, FullM6OrchAdapters.m6aAnaFailedLitSpec a m Q X →
      Γ "full_ana_failed_lit_m6_hdr" [i64] [i64] a m Q X)
    (hDeduce : ∀ a m Q X, m6Deduce1uipHdrSpec a m Q X →
      Γ "full_deduce_1uip_m6_hdr" [i64] [i64] a m Q X)
    (hRestore : ∀ a m Q X, FullM6OrchAdapters.m6aRestoreBumpAnaSpec a m Q X →
      Γ "full_restore_bump_ana_m6_hdr" [i64] [] a m Q X)
    (hMinShrink : ∀ a m Q X, m6MinShrinkWsortSpec a m Q X →
      Γ "full_min_shrink_m6" [i64] [] a m Q X)
    (hTick : ∀ a m Q X, Full.fullTickRelSpec a m Q X → Γ "full_tick_rel" [i64] [] a m Q X)
    (hEma : ∀ a m Q X, Full.fullEmaUpdateSpec a m Q X →
      Γ "full_ema_update" [i64, i64] [] a m Q X)
    (hLearn : ∀ a m Q X, Full.fullLearnClauseSpec a m Q X →
      Γ "full_learn_clause" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, FullM6Hdr.m6HdrAnalyzeSpec a m Q X →
      Func.wp Γ full_analyze_core_m6_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  rcases m6HdrAnalyzeSpec_elim hs with ⟨c, F0, F_cur, ext, s, R, rfl, hinv, hcf, hm, hQ⟩
  have hmaxv := c.hmaxv; have har_cap := c.harena; unfold dimacsBound at hmaxv har_cap
  have hcv_le := hinv.sparseW.1.core_ok.cur_vars_le
  let iter_lim : BitVec 64 := BitVec.ofNat 64 s.core.cur_vars + 64#64
  have hil_val : iter_lim.toNat = s.core.cur_vars + 64 := by
    change (BitVec.ofNat 64 s.core.cur_vars + 64#64).toNat = _
    rw [bv64_add_small_eq] <;> simp [BitVec.toNat_ofNat] <;> omega
  unfold Func.wp full_analyze_core_m6_body
  refine wp_m6Hdr_focus_frame hm fun hm' => ?_; c0_hsteps_nogrp
  refine wp_while_state1 (α := BitVec 64 × FullState × List (BitVec 64)) (fun st => st.1)
    (fun st => iter_lim.toNat - st.1.toNat) (CoreLoopInv c F0 F_cur s R iter_lim) ?_ ?_
  · intro J hJ; refine hJ (0#64, s, ext) m ⟨s.core.trail_end, Nat.le_refl _, hinv.sparseW.toCut,
      hcf.toCut hinv.sparseW.2.1, hinv.extOk, rfl, rfl, Nat.le_refl _, rfl, by simp, hm'⟩
  · intro J ⟨iter, s1, ext1⟩ m1
      ⟨cut1, hcut1_le, hcut1, hcf1, hext1, hcv1, hfu1, hcl1, hws1, hil1, hm1⟩ ih
    dsimp only at hcut1_le hcut1 hcf1 hext1 hcv1 hfu1 hcl1 hws1 hil1 hm1 ⊢
    c0_hsteps_nogrp
    · have hlt : iter.toNat < iter_lim.toNat := by
        simpa [iter_lim, BitVec.toNat_add, BitVec.toNat_ofNat] using hc
      have hcv_fit : (BitVec.ofNat 64 s1.core.cur_vars + 64#64).toNat = s1.core.cur_vars + 64 := by
        rw [hcv1]; exact hil_val
      c0_hsteps_nogrp; c0_call hOneLit
      refine ⟨c, F0, F_cur, cut1, s1, m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R,
        rfl, hcut1, hcf1, hm1, ?_⟩
      intro ol s2 m2 hlen2 hol hcv2 hfu2 hws2 h20 h1 h2 h0 hm2
      have hm2' := fullM6HdrMem_unfocus hm2
      rcases hol with rfl | rfl | rfl | rfl
      · rcases h0 rfl with ⟨cut2, hcut2_le, hcut2, hlvl2, hlle2, hcf2⟩
        c0_hsteps_nogrp
        · c0_call hFailed
          refine FullM6OrchAdapters.m6aAnaFailedLitSpec_of hinv.cfgOk hext1 hcut2 hlvl2 hcf2 hm2'
            ?_
          intro r ext3 s3 m3 hext3 _ hlen3 hr hcv3 hfu3 hws3 hr20 hr0 hr1 hm3
          exact hQ r ext3 s3 m3 hext3 hlen3 hr (hcv3.trans (hcv2.trans hcv1))
            (by rw [hfu3, hfu2, hfu1]; exact Nat.le_refl _) ⟨hws3.trans (hws2.trans hws1),
              fun heq => by
                have ⟨_, ho, hcl, _hdm⟩ := hr20 heq
                exact ⟨ho, Nat.le_trans hcl (Nat.le_trans hlle2 hcl1),
                  ho.2.2.2.2.2.trans hinv.sparseW.2.2.2.2.2.symm⟩⟩
            (fun heq => (hr20 heq).1) hr0
            (fun heq => ⟨FullM6HdrInvW.mk_inv hinv.cfgOk hext3 (hr1 heq).1,
              Nat.lt_of_lt_of_le (hr1 heq).2 (Nat.le_trans hlle2 hcl1)⟩) hm3
        · c0_call hDeduce
          refine ⟨c, F0, F_cur, cut2, ext1, s2, R, rfl, hinv.cfgOk, hext1, hcut2, hlvl2, hcf2,
            hm2', ?_⟩
          intro dst ext3 s3 m3 hext3 hlen3 hdst hcv3 hfu3 hws3 hr20 hr0 hr1 hr2 hm3
          rcases hdst with rfl | rfl | rfl | rfl
          · c0_hsteps_nogrp
            exact hQ 0#64 ext3 s3 m3 hext3 hlen3 (Or.inl rfl) (hcv3.trans (hcv2.trans hcv1))
              (by rw [hfu3, hfu2, hfu1]; exact Nat.le_refl _) ⟨hws3.trans (hws2.trans hws1),
                fun h => by cases h⟩
              (fun h => by cases h) hr0 (fun h => by cases h) hm3
          · rcases hr1 rfl with ⟨ho3, hcl3, htl_ge, htl_le, hnd3, hvals3, hlvl3, _hlvl0, hent3⟩
            refine wp_m6Hdr_focus_frame hm3 fun hm3f => ?_; c0_hsteps_nogrp; c0_call hMinShrink
            refine ⟨c, F0, F_cur, s3, m6ExtMem (m6ExtAddr c.hdr) ext3 ⋆ R, rfl, hlen3,
              ho3.2.1, ho3.2.2.1, htl_ge, htl_le, hnd3, hent3, hvals3, hlvl3, _hlvl0, hm3f, ?_⟩
            intro tmp4 tl4 mrk4 mstk4 mclr4 mcl4 mcf4 conf4 llits4 mrem4 sstk4 wsort4 m4 _s4
              hlen4 ho4 hmc4 htl4_ge htl4_le htmp04 hnd4 h4lits hent4 hm4
            let s4 : FullState := { s3 with
              core := { s3.core with tmp := tmp4, tmp_len := tl4, mrk := mrk4, min_stk := mstk4,
                                     min_clr := mclr4, min_clr_len := mcl4, min_clr_full := mcf4 }
              scratch := { s3.scratch with conflicts := conf4, learned_lits := llits4,
                                           min_removed := mrem4, shrink_stk := sstk4,
                                           wsort := wsort4 } }
            have hotfs4 : FullOtfsInvW c F0 F_cur s4 :=
              ⟨hlen4, ho4, hmc4, ho3.2.2.2.1,
                FullExtScratchOk.of_pres ho3.2.2.2.2.1 ⟨rfl, rfl⟩ (fun _ hr => hr),
                ho3.2.2.2.2.2⟩
            have h4v : ∀ k < tl4, let l := (tmp4[k]?.getD 0#32).toNat
                l < 2 * s4.core.cur_vars ∧ s4.core.vals[l]?.getD 0#8 = 255#8 := fun k hk => by
              by_cases hk0 : k = 0
              · subst hk0
                simpa [s4, htmp04] using hvals3 0 (Nat.lt_of_lt_of_le Nat.zero_lt_one htl_ge)
              · exact ⟨(h4lits k (Nat.pos_of_ne_zero hk0) hk).1,
                  (h4lits k (Nat.pos_of_ne_zero hk0) hk).2.1⟩
            have hm4' := fullM6HdrMem_unfocus hm4
            c0_hsteps_nogrp
            refine wp_join_state0 (α := FullState × List (BitVec 64))
              (fun st m' => CoreShrinkPost c F0 F_cur s st.1 ∧ M6HdrExtOk st.2 ∧
                (FullM6HdrMem c st.2 st.1 ⋆ R) m') ?_ ?_
            · rintro J4 ⟨s5, ext5⟩ m5 ⟨⟨ho5, hpos5, htl5_ge, htl5_le, hnd5, hvals5, hlvl5,
                hent5, hcv5, hfu5, hcl5, hws5⟩, hext5, hm5⟩
              dsimp only at ho5 hpos5 htl5_ge htl5_le hnd5 hvals5 hlvl5
              dsimp only at hent5 hcv5 hfu5 hcl5 hws5 hext5 hm5 ⊢
              refine wp_m6Hdr_focus_frame hm5 fun hm5f => ?_
              have htl5_arr := ho5.1.core_ok.tmp_len_arr; have hcv5_le := ho5.1.core_ok.cur_vars_le
              have hcv5_b : s5.core.cur_vars < 2 * 2 ^ 28 := Nat.lt_of_le_of_lt hcv5_le hmaxv
              have htl5_max : s5.core.tmp_len < 2 * 2 ^ 28 := Nat.lt_of_le_of_lt htl5_le hcv5_b
              have htl5_fit : s5.core.tmp_len < 2 ^ 64 := by omega
              c0_hsteps_nogrp
              refine wp_while_state_pure (α := BitVec 64 × BitVec 64 × BitVec 32)
                (fun st => (st.2.1, st.2.2, st.1, ())) (fun st => s5.core.tmp_len - st.1.toNat)
                (fun st => 1 ≤ st.1.toNat ∧ st.1.toNat ≤ s5.core.tmp_len) ?_ ?_
              · intro J5 hJ5; exact hJ5 (1#64, 1#64, 0#32) ⟨by decide, htl5_ge⟩
              · intro J5 ⟨gi, glue, llvl⟩ ⟨hgi_lo, hgi_hi⟩ ih5
                dsimp only at hgi_lo hgi_hi ⊢; c0_hsteps_nogrp
                · have hgi_lt : gi.toNat < s5.core.tmp_len := by
                    simpa [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt htl5_fit] using hc
                  have hlt_arr : gi.toNat < s5.core.tmp.length := by rw [htl5_arr]; omega
                  have hl_lt : (s5.core.tmp[gi.toNat]'hlt_arr).toNat < 2 * s5.core.cur_vars := by
                    simpa [List.getElem?_eq_getElem hlt_arr] using (hvals5 gi.toNat hgi_lt).1
                  have hv_lt : (BitVec.setWidth 64
                      ((s5.core.tmp[gi.toNat]'hlt_arr) >>> 1#32)).toNat < s5.core.lvl.length := by
                    have hb : ((s5.core.tmp[gi.toNat]'hlt_arr) >>> 1#32).toNat =
                        (s5.core.tmp[gi.toNat]'hlt_arr).toNat / 2 := by
                      simpa using bv32_lshr_1 (s5.core.tmp[gi.toNat]'hlt_arr)
                    rw [ho5.1.core_ok.lvl_len, BitVec.toNat_setWidth, hb]
                    have hdiv : (s5.core.tmp[gi.toNat]'hlt_arr).toNat / 2 < s5.core.cur_vars := by
                      omega
                    rw [Nat.mod_eq_of_lt (by omega : (s5.core.tmp[gi.toNat]'hlt_arr).toNat / 2 <
                      2 ^ 64)]
                    exact Nat.lt_of_lt_of_le hdiv hcv5_le
                  have hgi_add1 : (gi + 1#64).toNat = gi.toNat + 1 :=
                    bv64_add_small_eq (by rw [show (1#64 : BitVec 64).toNat = 1 from rfl]; omega)
                  c0_hsteps
                  · exact ih5 (gi + 1#64, glue + 1#64, s5.core.lvl[(BitVec.setWidth 64
                        ((s5.core.tmp[gi.toNat]'hlt_arr) >>> 1#32)).toNat]'hv_lt)
                      (by dsimp only; rw [hgi_add1]; omega)
                      ⟨by dsimp only; rw [hgi_add1]; omega, by dsimp only; rw [hgi_add1]; omega⟩
                  · exact ih5 (gi + 1#64, glue, llvl) (by dsimp only; rw [hgi_add1]; omega)
                      ⟨by dsimp only; rw [hgi_add1]; omega, by dsimp only; rw [hgi_add1]; omega⟩
                · refine wp_join_state0 (α := FullState)
                    (fun s6 m' => CoreShrinkPost c F0 F_cur s s6 ∧
                      (FullMem c s6 ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext5 ⋆ R)) m') ?_ ?_
                  · rintro J6 s6 m6 ⟨⟨ho6, hpos6, htl6_ge, htl6_le, hnd6, hvals6, hlvl6,
                      hent6, hcv6, hfu6, hcl6, hws6⟩, hm6⟩
                    c0_hsteps_nogrp; c0_call hLearn
                    refine ⟨c, F0, F_cur, s6, m6ExtMem (m6ExtAddr c.hdr) ext5 ⋆ R, rfl,
                      ho6, hpos6, htl6_ge, htl6_le, hnd6, hvals6, hlvl6, hent6, hm6, ?_⟩
                    intro r s7 m7 hlen7 hr hcv7 hfu7 hws7 h20_7 h0_7 h1_7 hm7
                    exact hQ r ext5 s7 m7 hext5 hlen7 hr (hcv7.trans hcv6)
                      (Nat.le_trans hfu7 (by rw [hfu6]; exact Nat.le_refl _))
                      ⟨hws7.trans hws6, fun h => let ⟨_, hsp, hcl⟩ := h20_7 h
                        ⟨hsp.toOtfs, Nat.le_trans (Nat.le_of_lt hcl) hcl6,
                          hsp.2.2.2.2.2.trans hinv.sparseW.2.2.2.2.2.symm⟩⟩
                      (fun h => (h20_7 h).1) (fun h => (h0_7 h).toOtfs)
                      (fun h => ⟨FullM6HdrInvW.mk_inv hinv.cfgOk hext5 (h1_7 h).1,
                        Nat.lt_of_lt_of_le (h1_7 h).2 hcl6⟩)
                      (fullM6HdrMem_unfocus hm7)
                  · intro J6 hJ6; c0_hsteps_nogrp
                    · c0_call hEma
                      refine ⟨c, s5, m6ExtMem (m6ExtAddr c.hdr) ext5 ⋆ R, rfl, ho5.1, hm5f, ?_⟩
                      rintro ⟨⟩ s6 m6 hcore6 hlen6 hpres6 hm6
                      have heq6 := fullCoreState_agrees_with_scratch hcore6
                      exact hJ6 s6 m6 ⟨⟨m6o_otfs_of_safetySlice ho5 hlen6 heq6 hpres6.1,
                        by change 0 < s6.core.cur_level; rw [heq6]; exact hpos5,
                        by rw [heq6]; exact htl5_ge, by rw [heq6]; exact htl5_le,
                        by rw [heq6]; exact hnd5, by rw [heq6]; exact hvals5,
                        by rw [heq6]; exact hlvl5, by rw [heq6]; exact hent5,
                        by rw [heq6]; exact hcv5, by rw [heq6]; exact hfu5,
                        by change s6.core.cur_level ≤ _; rw [heq6]; exact hcl5,
                        hpres6.2.2.1.trans hws5⟩, hm6⟩
                    · exact hJ6 s5 m5 ⟨⟨ho5, hpos5, htl5_ge, htl5_le, hnd5, hvals5, hlvl5,
                        hent5, hcv5, hfu5, hcl5, hws5⟩, hm5f⟩
            · intro J4 hJ4
              let mkShk : ∀ {s' : FullState}, FullOtfsInvW c F0 F_cur s' → 0 < s'.core.cur_level →
                  1 ≤ s'.core.tmp_len → s'.core.tmp_len ≤ s'.core.cur_vars →
                  (List.map (fun x => x.toNat / 2)
                    (List.take s'.core.tmp_len s'.core.tmp)).Nodup →
                  (∀ k < s'.core.tmp_len, let l := (s'.core.tmp[k]?.getD 0#32).toNat
                    l < 2 * s'.core.cur_vars ∧ s'.core.vals[l]?.getD 0#8 = 255#8) →
                  (∀ k, 1 ≤ k → k < s'.core.tmp_len →
                    let lv := (s'.core.lvl[(s'.core.tmp[k]?.getD 0#32).toNat / 2]?.getD 0#32).toNat
                    0 < lv ∧ lv < s'.core.cur_level ∧
                    lv ≤ (s'.core.lvl[(s'.core.tmp[s'.core.tmp_len - 1]?.getD 0#32).toNat / 2]?.getD
                      0#32).toNat) →
                  (cnfOfClauses F_cur).EntailsClause
                    (cnfClause (List.map BitVec.toNat (List.take s'.core.tmp_len s'.core.tmp))) →
                  s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
                  s'.core.cur_level ≤ s.core.cur_level →
                  s'.scratch.work_stk2 = s.scratch.work_stk2 → CoreShrinkPost c F0 F_cur s s' :=
                fun ho hp h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
                  ⟨ho, hp, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
              c0_hsteps_nogrp
              · c0_call hRestore
                refine FullM6OrchAdapters.m6aRestoreBumpAnaSpec_of hinv.cfgOk hext3 hlen4 hmc4.1
                  hm4' ?_
                intro mrk5 mcl5 sc5 ext5 m5 _s5 hlen5 hmz5 _ _ hpres5 hws5 hext5 _ hm5
                let s5 : FullState :=
                  { core := { s4.core with mrk := mrk5, min_clr_len := mcl5 }, scratch := sc5 }
                have ho5 := m6o_otfs_of_restoreBump hotfs4 hlen5 hmz5 hpres5
                refine wp_m6Hdr_focus_frame hm5 fun hm5f => ?_; c0_hsteps_nogrp; c0_call hTick
                refine ⟨c, s5, m6ExtMem (m6ExtAddr c.hdr) ext5 ⋆ R, rfl, hlen5, hm5f, ?_⟩
                rintro ⟨⟩ s6 m6 hcore6 hlen6 hpres6 hm6
                have heq6 := fullCoreState_agrees_with_scratch hcore6
                exact hJ4 (s6, ext5) m6 ⟨mkShk (m6o_otfs_of_safetySlice ho5 hlen6 heq6 hpres6.1)
                  (by change 0 < s6.core.cur_level; rw [heq6]; change 0 < s3.core.cur_level; omega)
                  (by rw [heq6]; exact htl4_ge) (by rw [heq6]; exact Nat.le_trans htl4_le htl_le)
                  (by rw [heq6]; exact hnd4) (by rw [heq6]; exact h4v)
                  (fun k hk1 hk2 => by rw [heq6] at hk2 ⊢; exact (h4lits k hk1 hk2).2.2)
                  (by rw [heq6]; exact hent4)
                  (by change s6.core.cur_vars = _; rw [heq6]; exact hcv3.trans (hcv2.trans hcv1))
                  (by change s6.core.fuel = _; rw [heq6]; rw [hfu3, hfu2, hfu1])
                  (by change s6.core.cur_level ≤ _; rw [heq6, hcl3]; exact Nat.le_trans hlle2 hcl1)
                  (hpres6.2.2.1.trans (hws5.trans (hws3.trans (hws2.trans hws1)))),
                  hext5, fullM6HdrMem_unfocus hm6⟩
              · exact hJ4 (s4, ext3) m4 ⟨mkShk hotfs4 (by change 0 < s3.core.cur_level; omega)
                  htl4_ge (Nat.le_trans htl4_le htl_le) hnd4 h4v
                    (fun k hk1 hk2 => (h4lits k hk1 hk2).2.2)
                  hent4 (hcv3.trans (hcv2.trans hcv1)) (by rw [hfu3, hfu2, hfu1])
                  (by rw [hcl3]; exact Nat.le_trans hlle2 hcl1)
                  (hws3.trans (hws2.trans hws1)), hext3, hm4'⟩
          · rcases hr2 rfl with ⟨cut3, hcut3_le, hcut3, hcl3, hcf3⟩
            refine wp_m6Hdr_focus_frame hm3 fun hm3f => ?_; c0_hsteps_nogrp
            have ⟨hcut3k, hcf3k⟩ := m6o_cut_with_conflicts hcut3 hcf3 (s3.scratch.conflicts + 1#64)
            let s3k : FullState :=
              { s3 with scratch := { s3.scratch with conflicts := s3.scratch.conflicts + 1#64 } }
            refine wp_join_state0 (α := FullState × List (BitVec 64))
              (fun st m' => CoreCutJoin c F0 F_cur cut3 s st.1 ∧ M6HdrExtOk st.2 ∧
                (FullM6HdrMem c st.2 st.1 ⋆ R) m') ?_ ?_
            · rintro J4 ⟨s5, ext5⟩ m5 ⟨⟨hcut5_le, hcut5, hcf5, hcv5, hfu5, hcl5, hws5⟩, hext5, hm5⟩
              dsimp only at hcut5_le hcut5 hcf5 hcv5 hfu5 hcl5 hws5 hext5 hm5 ⊢
              refine wp_m6Hdr_focus_frame hm5 fun hm5f => ?_
              c0_hsteps_nogrp
              exact ih (iter + 1#64, s5, ext5) m5 (bv64_measure_sub_lt hlt)
                ⟨cut3, hcut5_le, hcut5, hcf5, hext5, hcv5, hfu5, hcl5, hws5,
                 by rw [bv64_add1_toNat hlt]; exact hlt, hm5f⟩
            · intro J4 hJ4; c0_hsteps_nogrp
              · refine wp_join_state0 (α := FullState)
                  (fun st m' => CoreCutJoin c F0 F_cur cut3 s st ∧
                    (FullMem c st ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext3 ⋆ R)) m') ?_ ?_
                · rintro J5 s4 m4 ⟨⟨hcut4_le, hcut4, hcf4, hcv4, hfu4, hcl4, hws4⟩, hm4⟩
                  c0_hsteps_nogrp; c0_call hRestore
                  refine FullM6OrchAdapters.m6aRestoreBumpAnaSpec_of hinv.cfgOk hext3 hcut4.1
                    hcut4.2.2.1.1 (fullM6HdrMem_unfocus hm4) ?_
                  intro mrk5 mcl5 sc5 ext5 m5 _s5 hlen5 hmz5 _ _ hpres5 hws5 hext5 _ hm5
                  let s5 : FullState :=
                    { core := { s4.core with mrk := mrk5, min_clr_len := mcl5 }, scratch := sc5 }
                  have ⟨hcut5, hcf5⟩ := m6o_cut_of_restoreBump hcut4 hcf4 hlen5 hmz5 hpres5
                  exact hJ4 (s5, ext5) m5
                    ⟨⟨hcut4_le, hcut5, hcf5, hcv4, hfu4, hcl4, hws5.trans hws4⟩, hext5, hm5⟩
                · intro J5 hJ5
                  have hJ_s3k : ∀ m',
                      (FullMem c s3k ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext3 ⋆ R)) m' →
                      J5 () m' := fun m' hm' =>
                    hJ5 s3k m' ⟨⟨hcut3_le, hcut3k, hcf3k, hcv3.trans (hcv2.trans hcv1),
                      by rw [hfu3, hfu2, hfu1], by rw [hcl3]; exact Nat.le_trans hlle2 hcl1,
                      hws3.trans (hws2.trans hws1)⟩, hm'⟩
                  c0_hsteps_nogrp
                  · have hpos3 : 0 < s3k.core.cur_vars := by
                      change 0 < s3.core.cur_vars
                      have : s3.core.cur_vars < 2 ^ 64 := by omega
                      simpa [BitVec.lt_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt this] using hc
                    have htl0 : (0#64 : BitVec 64).toNat < s3k.core.tmp.length := by
                      rw [hcut3k.1.core_ok.tmp_len_arr]
                      exact Nat.lt_of_lt_of_le hpos3 (by
                        change s3.core.cur_vars ≤ c.max_vars; rw [hcv3, hcv2, hcv1]; exact hcv_le)
                    have hJ_tmp : ∀ {tp' : List (BitVec 32)} {m'} (htp' : tp'.length = c.max_vars),
                        (FullMem c { s3k with core := { s3k.core with
                          tmp := tp', tmp_len := (1#64 : BitVec 64).toNat } } ⋆
                          (m6ExtMem (m6ExtAddr c.hdr) ext3 ⋆ R)) m' → J5 () m' := by
                      intro tp' m' htp' hm'
                      have htw := m6o_cut_with_tmp hcut3k hcf3k htp'
                        (tl' := (1#64 : BitVec 64).toNat)
                        (by rw [show (1#64 : BitVec 64).toNat = 1 from rfl]; omega)
                      refine hJ5 _ m' ⟨?_, hm'⟩
                      exact ⟨hcut3_le, htw.1, htw.2, hcv3.trans (hcv2.trans hcv1),
                        by rw [hfu3, hfu2, hfu1], by rw [hcl3]; exact Nat.le_trans hlle2 hcl1,
                        hws3.trans (hws2.trans hws1)⟩
                    refine wp_unroll_group fun Jlit hJlit => ?_; c0_hsteps_nogrp
                    · exact hJ_tmp
                        (by simpa [List.length_set] using hcut3k.1.core_ok.tmp_len_arr) hm
                    · refine wp_unroll_group fun Js hJs => ?_
                      have har_len := hcut3k.1.core_ok.arena_len_arr
                      have har_le := hcut3k.1.core_ok.arena_len_le
                      c0_hsteps_nogrp
                      · rename_i hlt_ar; dsimp only [s3k] at har_len har_le
                        have href_lt : s3.core.confl_ref.toNat < s3.core.arena_len := by
                          simpa [BitVec.lt_def, BitVec.toNat_ofNat,
                            Nat.mod_eq_of_lt (by omega : s3.core.arena_len < 2 ^ 64)] using hlt_ar
                        have hsub_lt : 3 < s3.core.arena_len - s3.core.confl_ref.toNat := by
                          have hc' : 3 < (2 ^ 64 - s3.core.confl_ref.toNat +
                              s3.core.arena_len) % 2 ^ 64 := hc
                          omega
                        have har_lt : (s3k.core.confl_ref + 3#64).toNat <
                            s3k.core.arena.length := by
                          dsimp only [s3k]; rw [bv64_add_small_eq (by simp; omega)]; simp; omega
                        c0_hsteps_nogrp
                        exact hJ_tmp
                            (by simpa [List.length_set] using hcut3k.1.core_ok.tmp_len_arr) hm
                      · exact hJ_s3k _ (by assumption)
                      · exact hJ_s3k _ (by assumption)
                      · exact hJ_s3k _ (by assumption)
                  · exact hJ_s3k _ (by assumption)
              · exact hJ4 (s3k, ext3) _ ⟨⟨hcut3_le, hcut3k, hcf3k,
                  hcv3.trans (hcv2.trans hcv1), by rw [hfu3, hfu2, hfu1],
                  by rw [hcl3]; exact Nat.le_trans hlle2 hcl1,
                  hws3.trans (hws2.trans hws1)⟩, hext3, fullM6HdrMem_unfocus (by assumption)⟩
          · rcases hr20 rfl with ⟨hu3, ho3, hcl3, _hdm3⟩
            c0_hsteps_nogrp
            exact hQ 20#64 ext3 s3 m3 hext3 hlen3 (Or.inr (Or.inr rfl))
              (hcv3.trans (hcv2.trans hcv1)) (by rw [hfu3, hfu2, hfu1]; exact Nat.le_refl _)
              ⟨hws3.trans (hws2.trans hws1),
                fun _ => ⟨ho3, Nat.le_trans hcl3 (Nat.le_trans hlle2 hcl1),
                  ho3.2.2.2.2.2.trans hinv.sparseW.2.2.2.2.2.symm⟩⟩
              (fun _ => hu3) (fun h => by cases h) (fun h => by cases h) hm3
      · c0_hsteps_nogrp
        exact hQ 1#64 ext1 s2 m2 hext1 hlen2 (Or.inr (Or.inl rfl)) (hcv2.trans hcv1)
          (by rw [hfu2, hfu1]; exact Nat.le_refl _) ⟨hws2.trans hws1, fun h => by cases h⟩
          (fun h => by cases h) (fun h => by cases h)
          (fun _ => ⟨FullM6HdrInvW.mk_inv hinv.cfgOk hext1 (h1 rfl).1,
            Nat.lt_of_lt_of_le (h1 rfl).2 hcl1⟩) hm2'
      · c0_hsteps_nogrp
        exact hQ 0#64 ext1 s2 m2 hext1 hlen2 (Or.inl rfl) (hcv2.trans hcv1)
          (by rw [hfu2, hfu1]; exact Nat.le_refl _) ⟨hws2.trans hws1, fun h => by cases h⟩
          (fun h => by cases h) (fun _ => h2 rfl) (fun h => by cases h) hm2'
      · c0_hsteps_nogrp
        have ⟨hu2, ho2, hcl2, _hdm2⟩ := h20 rfl
        exact hQ 20#64 ext1 s2 m2 hext1 hlen2 (Or.inr (Or.inr rfl)) (hcv2.trans hcv1)
          (by rw [hfu2, hfu1]; exact Nat.le_refl _) ⟨hws2.trans hws1,
            fun _ => ⟨ho2, Nat.le_trans hcl2 hcl1,
              ho2.2.2.2.2.2.trans hinv.sparseW.2.2.2.2.2.symm⟩⟩
          (fun _ => hu2) (fun h => by cases h) (fun h => by cases h) hm2'
    · c0_hsteps_nogrp
      exact hQ 0#64 ext1 s1 m1 hext1 hcut1.1 (Or.inl rfl) hcv1
        (by rw [hfu1]; exact Nat.le_refl _)
        ⟨hws1, fun h => by cases h⟩ (fun h => by cases h)
        (fun _ => hcut1.toOtfs) (fun h => by cases h) (fullM6HdrMem_unfocus hm1)

theorem full_analyze_core_m6_wp (Γ : Env)
    (hOneLit : ∀ a m Q X, Full.fullOneLitConflSpec a m Q X →
      Γ "full_one_lit_confl" [i64] [i64] a m Q X)
    (hFailed : ∀ a m Q X, FullM6OrchAdapters.m6aAnaFailedLitSpec a m Q X →
      Γ "full_ana_failed_lit_m6_hdr" [i64] [i64] a m Q X)
    (hDeduce : ∀ a m Q X, m6Deduce1uipHdrSpec a m Q X →
      Γ "full_deduce_1uip_m6_hdr" [i64] [i64] a m Q X)
    (hRestore : ∀ a m Q X, FullM6OrchAdapters.m6aRestoreBumpAnaSpec a m Q X →
      Γ "full_restore_bump_ana_m6_hdr" [i64] [] a m Q X)
    (hMinShrink : ∀ a m Q X, Full.fullMinShrinkSpec a m Q X →
      Γ "full_min_shrink_m6" [i64] [] a m Q X)
    (hTick : ∀ a m Q X, Full.fullTickRelSpec a m Q X → Γ "full_tick_rel" [i64] [] a m Q X)
    (hEma : ∀ a m Q X, Full.fullEmaUpdateSpec a m Q X →
      Γ "full_ema_update" [i64, i64] [] a m Q X)
    (hLearn : ∀ a m Q X, Full.fullLearnClauseSpec a m Q X →
      Γ "full_learn_clause" [i64, i64] [i64] a m Q X) :
    ∀ a m Q X, FullM6Hdr.m6HdrAnalyzeSpec a m Q X →
      Func.wp Γ full_analyze_core_m6_body a m Q X :=
  full_analyze_core_m6_any_wp Γ hOneLit hFailed hDeduce hRestore
    (fun a m Q X hs => hMinShrink a m Q X (by
      rcases hs with ⟨c, F0, F_cur, s, R, hh, hl, hw, hm, h1, h2, h3, h4, h5, h6, h7, hmem, hcb⟩
      exact ⟨c, F0, F_cur, s, R, hh, hl, hw, hm, h1, h2, h3, h4, h5, h6, h7, hmem,
        fun tmp' tl' mrk' mstk' mclr' mcl' mcf' conf' llits' mrem' sstk' m' =>
          hcb tmp' tl' mrk' mstk' mclr' mcl' mcf' conf' llits' mrem' sstk' s.scratch.wsort m'⟩))
    hTick hEma hLearn

/-! ### `full_analyze_rsn_m6_hdr` -/

private theorem m6o_bv64_ite_iff {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) :
    (if P then (1#64 : BitVec 64) else 0#64) = BitVec.ofNat 64 (if Q then 1 else 0) := by
  by_cases hp : P
  · simp [hp, h.mp hp]
  · simp [hp, mt h.mpr hp]

private theorem m6o_bv32_glue_bit (x g mask : BitVec 32) {b : Nat} (h19 : 19 ≤ b)
    (hmask_hi : (0xFFF80000#32 &&& mask) = mask)
    (hmask_eq : mask.toNat = 2 ^ b) (hg : g.toNat < 2 ^ 19) :
    (((x &&& 0xFFF80000#32) ||| g) &&& mask) = (x &&& mask) := by
  have hg_zero : (g &&& mask) = 0#32 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat]
    apply Nat.eq_of_testBit_eq; intro k
    rw [Nat.testBit_and, Nat.zero_mod, Nat.zero_testBit, hmask_eq, Nat.testBit_two_pow]
    by_cases hkb : b = k
    · subst k
      have hdiv : g.toNat / 2 ^ b = 0 :=
        Nat.div_eq_of_lt (lt_of_lt_of_le hg (Nat.pow_le_pow_right (by decide) h19))
      simp [Nat.testBit, Nat.shiftRight_eq_div_pow, hdiv]
    · simp [hkb]
  rw [BitVec.and_or_distrib_right, hg_zero, BitVec.or_zero, BitVec.and_assoc, hmask_hi]

private theorem m6o_filter_zero {α : Type} {p : α → Bool} {xs : List α}
    (h : ∀ x ∈ xs, p x = false) : (xs.filter p).length = 0 := by
  rw [List.filter_eq_nil_iff.mpr (fun x hx => by simp [h x hx])]; rfl

private theorem m6o_res_step_of_lit {s_mrk mrk1 mrk2 : List (BitVec 8)} {mv v : Nat}
    {r0 r1 r2 : BitVec 64}
    (hmp0 : ∀ w < mv, s_mrk[w]?.getD 0#8 ≠ 0#8 → mrk1[w]?.getD 0#8 = s_mrk[w]?.getD 0#8)
    (hmp1 : ∀ w < mv, mrk1[w]?.getD 0#8 ≠ 0#8 → mrk2[w]?.getD 0#8 = mrk1[w]?.getD 0#8)
    (hnew1 : ∀ w < mv, mrk1[w]?.getD 0#8 = 0#8 → mrk2[w]?.getD 0#8 ≠ 0#8 → v = w)
    (hr1 : r1 = r0 + BitVec.ofNat 64 ((List.range mv).filter fun w =>
      decide (s_mrk[w]?.getD 0#8 = 0#8) && decide (mrk1[w]?.getD 0#8 ≠ 0#8)).length)
    (hr2 : r2 = r1 + if v < mv ∧ mrk1[v]?.getD 0#8 = 0#8 ∧ mrk2[v]?.getD 0#8 ≠ 0#8
      then 1#64 else 0#64) : r2 = r0 + BitVec.ofNat 64 ((List.range mv).filter fun w =>
      decide (s_mrk[w]?.getD 0#8 = 0#8) && decide (mrk2[w]?.getD 0#8 ≠ 0#8)).length := by
  let c1 := ((List.range mv).filter fun w =>
    decide (s_mrk[w]?.getD 0#8 = 0#8) && decide (mrk1[w]?.getD 0#8 ≠ 0#8)).length
  have hf := FullAnalyzeHelpers.filter_step_of_lit (fun _ => true) (tc0 := 0) (tc1 := c1)
    (tc2 := c1 + if v < mv ∧ mrk1[v]?.getD 0#8 = 0#8 ∧ mrk2[v]?.getD 0#8 ≠ 0#8 ∧
      (true : Bool) = true then 1 else 0) hmp0 hmp1 hnew1 (Nat.zero_le _) (by simp [c1]) rfl
  simp only [Nat.sub_zero, Bool.and_true, and_true] at hf
  rw [hr2, hr1, BitVec.add_assoc]; congr 1; dsimp only [c1] at hf; rw [← hf]
  split <;> simp [BitVec.ofNat_add]

private abbrev M6oRsnStepPre (s : FullState) (rsn_lits : List Nat) (skip_var : BitVec 32)
    (mrk' : List (BitVec 8)) (tmp' : List (BitVec 32)) (tc' tl' : Nat) (res' : BitVec 64) : Prop :=
  (∀ w < s.core.cur_vars, s.core.mrk[w]?.getD 0#8 ≠ 0#8 →
    mrk'[w]?.getD 0#8 = s.core.mrk[w]?.getD 0#8) ∧
  (∀ k < s.core.tmp_len, tmp'[k]? = s.core.tmp[k]?) ∧
  (∀ w < s.core.cur_vars, s.core.mrk[w]?.getD 0#8 = 0#8 → mrk'[w]?.getD 0#8 ≠ 0#8 →
    ∃ l ∈ rsn_lits, l / 2 = w ∧ w ≠ skip_var.toNat ∧
      0 < (s.core.lvl[w]?.getD 0#32).toNat ∧ (s.core.lvl[w]?.getD 0#32).toNat ≤ s.core.cur_level) ∧
  (∀ j, s.core.tmp_len ≤ j → j < tl' → let l := (tmp'[j]?.getD 0#32).toNat
    l ∈ rsn_lits ∧ l < 2 * s.core.cur_vars ∧ l / 2 ≠ skip_var.toNat ∧
    s.core.mrk[l / 2]?.getD 0#8 = 0#8 ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
    (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level ∧ mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
  (∀ j1 j2, s.core.tmp_len ≤ j1 → j1 < j2 → j2 < tl' →
    (tmp'[j1]?.getD 0#32).toNat / 2 ≠ (tmp'[j2]?.getD 0#32).toNat / 2) ∧
  (tc' - s.core.tmp_cnt = ((List.range s.core.cur_vars).filter fun w =>
    decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8) &&
    decide ((s.core.lvl[w]?.getD 0#32).toNat = s.core.cur_level)).length) ∧
  (res' = s.scratch.res_sz + BitVec.ofNat 64 ((List.range s.core.cur_vars).filter fun w =>
    decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8)).length)

private theorem m6o_rsn_comb_step {s : FullState} {l_bv skip_var : BitVec 32}
    {rsn_lits : List Nat} {mrk' mrk2 : List (BitVec 8)} {tmp' tmp2 : List (BitVec 32)}
    {tc' tl' tc2 tl2 : Nat} {res' res2 : BitVec 64}
    (htl_ge : s.core.tmp_len ≤ tl') (htl2_ge : tl' ≤ tl2) (htl2_inc : tl2 ≤ tl' + 1)
    (htc_ge : s.core.tmp_cnt ≤ tc') (hl_mem : l_bv.toNat ∈ rsn_lits)
    (hpre : M6oRsnStepPre s rsn_lits skip_var mrk' tmp' tc' tl' res')
    (hmp2 : ∀ w < s.core.cur_vars, mrk'[w]?.getD 0#8 ≠ 0#8 →
      mrk2[w]?.getD 0#8 = mrk'[w]?.getD 0#8) (htp2 : ∀ k < tl', tmp2[k]? = tmp'[k]?)
    (hnm2 : ∀ w < s.core.cur_vars, mrk'[w]?.getD 0#8 = 0#8 → mrk2[w]?.getD 0#8 ≠ 0#8 →
      l_bv.toNat / 2 = w ∧ w ≠ skip_var.toNat ∧ 0 < (s.core.lvl[w]?.getD 0#32).toNat ∧
      (s.core.lvl[w]?.getD 0#32).toNat ≤ s.core.cur_level)
    (hnt2 : ∀ j, tl' ≤ j → j < tl2 → (tmp2[j]?.getD 0#32).toNat = l_bv.toNat ∧
      l_bv.toNat / 2 < s.core.cur_vars ∧ l_bv.toNat / 2 ≠ skip_var.toNat ∧
      mrk'[l_bv.toNat / 2]?.getD 0#8 = 0#8 ∧ 0 < (s.core.lvl[l_bv.toNat / 2]?.getD 0#32).toNat ∧
      (s.core.lvl[l_bv.toNat / 2]?.getD 0#32).toNat < s.core.cur_level ∧
      mrk2[l_bv.toNat / 2]?.getD 0#8 ≠ 0#8)
    (hres2 : res2 = res' + if l_bv.toNat / 2 < s.core.cur_vars ∧
      mrk'[l_bv.toNat / 2]?.getD 0#8 = 0#8 ∧ mrk2[l_bv.toNat / 2]?.getD 0#8 ≠ 0#8
      then 1#64 else 0#64)
    (htc2_eq : tc2 = tc' + if l_bv.toNat / 2 < s.core.cur_vars ∧
      mrk'[l_bv.toNat / 2]?.getD 0#8 = 0#8 ∧ mrk2[l_bv.toNat / 2]?.getD 0#8 ≠ 0#8 ∧
      (s.core.lvl[l_bv.toNat / 2]?.getD 0#32).toNat = s.core.cur_level then 1 else 0) :
    M6oRsnStepPre s rsn_lits skip_var mrk2 tmp2 tc2 tl2 res2 := by
  obtain ⟨hmp, htp, hnm, hnt, hnd, hcnt, hres_l⟩ := hpre
  refine ⟨fun w hw hnz => by have h1 := hmp w hw hnz; rw [hmp2 w hw (by rwa [h1]), h1],
    fun k hk => by rw [htp2 k (by omega), htp k hk], fun w hw hs0 hmnz => ?_, fun j hj1 hj2 => ?_,
    fun j1 j2 hj1 hj12 hj2 => ?_, ?_, ?_⟩
  · by_cases hm1 : mrk'[w]?.getD 0#8 = 0#8
    · obtain ⟨rfl, hne', hpos, hle⟩ := hnm2 w hw hm1 hmnz
      exact ⟨l_bv.toNat, hl_mem, rfl, hne', hpos, hle⟩
    · exact hnm w hw hs0 hm1
  · by_cases hjold : j < tl'
    · rw [htp2 j hjold]; obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hnt j hj1 hjold
      exact ⟨h1, h2, h3, h4, h5, h6, by rw [hmp2 _ (by omega) h7]; exact h7⟩
    · obtain ⟨heq, hlt, hne', hm1_0, hpos, hcl, _⟩ := hnt2 j (by omega) hj2
      have hs0 : s.core.mrk[l_bv.toNat / 2]?.getD 0#8 = 0#8 :=
        Classical.byContradiction fun hnz => by rw [hmp _ hlt hnz] at hm1_0; exact hnz hm1_0
      exact ⟨by rwa [heq], by omega, by omega, by rwa [heq], by rwa [heq], by rwa [heq],
        by rwa [heq]⟩
  · by_cases hj2_old : j2 < tl'
    · rw [htp2 j1 (by omega), htp2 j2 hj2_old]; exact hnd j1 j2 hj1 hj12 hj2_old
    · have hj1_old : j1 < tl' := by omega
      rw [htp2 j1 hj1_old]; have h1 := (hnt j1 hj1 hj1_old).2.2.2.2.2.2
      obtain ⟨heq, _, _, hm1_0, _⟩ := hnt2 j2 (by omega) hj2
      rw [heq]; intro heq_v; rw [← heq_v] at hm1_0; exact absurd hm1_0 h1
  · exact FullAnalyzeHelpers.filter_step_of_lit
      (fun w => decide ((s.core.lvl[w]?.getD 0#32).toNat = s.core.cur_level))
      (mv := s.core.cur_vars) (tc0 := s.core.tmp_cnt) (tc1 := tc') (v := l_bv.toNat / 2)
      hmp hmp2 (fun w hw h0 hnz => (hnm2 w hw h0 hnz).1) htc_ge hcnt
      (by simpa only [decide_eq_true_eq] using htc2_eq)
  · exact m6o_res_step_of_lit (mv := s.core.cur_vars) (v := l_bv.toNat / 2) hmp hmp2
      (fun w hw h0 hnz => (hnm2 w hw h0 hnz).1) hres_l hres2

private theorem m6o_hdrBitsUpdate_cut {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {k : FullCoreState} (hlen : k.LengthsOk c)
    (hw : FullWitnessCutInv c F0 F_cur cut k)
    {cref : Nat} (hcref : cref ∈ fullArenaClauseRefsCore k)
    (f : BitVec 32 → BitVec 32) (ag' ni' nr' : BitVec 64)
    (hgarb : (f (fullArenaHdrCore k cref) &&& 0x00080000#32) =
      (fullArenaHdrCore k cref &&& 0x00080000#32))
    (hshrk : (f (fullArenaHdrCore k cref) &&& 0x00800000#32) =
      (fullArenaHdrCore k cref &&& 0x00800000#32)) :
    let hdr' := f (fullArenaHdrCore k cref)
    let k' : FullCoreState :=
      { k with arena := k.arena.set cref hdr', arena_garbage := ag',
               num_irred := ni', num_redundant := nr' }
    FullWitnessCutInv c F0 F_cur cut k' ∧
    fullArenaClauseRefsCore k' = fullArenaClauseRefsCore k ∧
    (∀ r ∈ fullArenaClauseRefsCore k,
      fullArenaClauseSizeCore k' r = fullArenaClauseSizeCore k r ∧
      fullArenaClauseGarbCore k' r = fullArenaClauseGarbCore k r ∧
      fullArenaClauseLitsCore k' r = fullArenaClauseLitsCore k r) := by
  have hwA : FullAnalyzeSpecs.FullWitnessCutInv c F0 F_cur cut k :=
    { ext_sound := hw.ext_sound, inconsistent_sound := hw.inconsistent_sound,
      arena := hw.arena, watches := hw.watches, cur_level_le := hw.cur_level_le,
      trail_lits_lt := hw.trail_lits_lt, trail_vars_nodup := hw.trail_vars_nodup,
      vals_domain := hw.vals_domain, vals_true_iff := hw.vals_true_iff,
      vals_false_iff := hw.vals_false_iff, lvl_le := hw.lvl_le, dec_earliest := hw.dec_earliest,
      levels_inhabited := hw.levels_inhabited, level0_sound := hw.level0_sound,
      trail_pos_inv := hw.trail_pos_inv, level0_rsn_none := hw.level0_rsn_none,
      frame_trail_lt := hw.frame_trail_lt, frame_trail_mono := hw.frame_trail_mono,
      frame_trail_before_lt := hw.frame_trail_before_lt, frame_dec_lt := hw.frame_dec_lt,
      reason_inv := fun idx hte hcond hne => hcond.elim (hw.reason_inv_cut idx · hne)
        (hw.reason_inv_below idx hte · hne),
      reason_lit_mem := fun idx hte hcond hne hlg => hcond.elim
        (hw.reason_lit_mem_cut idx · hne hlg) (hw.reason_lit_mem_below idx hte · hne hlg) }
  obtain ⟨hw', hrefs', hper'⟩ := FullAnalyzeHelpers.hdrBitsUpdate_preserves_fullWitnessCut
    hlen hwA hcref f ag' ni' nr' hgarb hshrk
  exact ⟨
    { ext_sound := hw'.ext_sound, inconsistent_sound := hw'.inconsistent_sound,
      arena := hw'.arena, watches := hw'.watches, cur_level_le := hw'.cur_level_le,
      trail_lits_lt := hw'.trail_lits_lt, trail_vars_nodup := hw'.trail_vars_nodup,
      vals_domain := hw'.vals_domain, vals_true_iff := hw'.vals_true_iff,
      vals_false_iff := hw'.vals_false_iff, lvl_le := hw'.lvl_le, dec_earliest := hw'.dec_earliest,
      levels_inhabited := hw'.levels_inhabited, level0_sound := hw'.level0_sound,
      trail_pos_inv := hw'.trail_pos_inv, level0_rsn_none := hw'.level0_rsn_none,
      frame_trail_lt := hw'.frame_trail_lt, frame_trail_mono := hw'.frame_trail_mono,
      frame_trail_before_lt := hw'.frame_trail_before_lt, frame_dec_lt := hw'.frame_dec_lt,
      reason_inv_below := fun idx hte hlt hne => hw'.reason_inv idx hte (Or.inr hlt) hne,
      reason_lit_mem_below := fun idx hte hlt hne hlg =>
        hw'.reason_lit_mem idx hte (Or.inr hlt) hne hlg,
      cut_le := hw.cut_le,
      reason_inv_cut := fun idx hcut hne =>
        hw'.reason_inv idx (Nat.lt_of_lt_of_le hcut hw.cut_le) (Or.inl hcut) hne,
      reason_lit_mem_cut := fun idx hcut hne hlg => hw'.reason_lit_mem idx
        (Nat.lt_of_lt_of_le hcut hw.cut_le) (Or.inl hcut) hne hlg }, hrefs', hper'⟩

private theorem m6o_rsn_lit_loop {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {cut : Nat} {ext ext1 : List (BitVec 64)} {s : FullState}
    {R : Mem 64 → Prop} {arena1 : List (BitVec 32)} {sc1 : FullScratch} {m1 : Mem 64}
    {Q : Post [.bool]} {X : XPost} {rsn skip_var : Val i32} {pArena : Val i64} {sz_bv : Val i32}
    (hpArena : pArena = c.pArena)
    (hLit : ∀ a m Q X, Full.fullAnalyzeLitSpec a m Q X →
      Γ "full_analyze_lit" [i64, i32, i32] [.bool] a m Q X)
    (hext1 : M6HdrExtOk ext1) (hwb1 : M6HdrExtInitOk ext → M6ExtW2bPres ext ext1)
    (hlen : s.LengthsOk c) (hwork : FullAnaMarksCov c s) (htl_cv : s.core.tmp_len ≤ s.core.cur_vars)
    (htc_fit : s.core.tmp_cnt + s.core.cur_vars + 1 < 2 ^ 64)
    (hcv_le : s.core.cur_vars ≤ c.max_vars) (hcur32 : s.core.cur_level < 2 ^ 32)
    (hne : rsn ≠ 0xFFFFFFFF#32) (hlarge : (rsn &&& 0x80000000#32) = 0#32)
    (hbd : rsn.toNat + 3 + fullArenaClauseSizeCore s.core rsn.toNat ≤
      fullArenaNextOff s.core.arena s.core.arena_len rsn.toNat)
    (hbd_le : fullArenaNextOff s.core.arena s.core.arena_len rsn.toNat ≤ s.core.arena_len)
    (hsz_idx : (rsn.setWidth 64 + 2#64).toNat = rsn.toNat + 2)
    (hsz_lt : (rsn.setWidth 64 + 2#64).toNat < s.core.arena.length)
    (hsz_bv : sz_bv = s.core.arena[(rsn.setWidth 64 + 2#64).toNat]'hsz_lt)
    (hw1 : FullWitnessCutInv c F0 F_cur cut
      ({ s with core := { s.core with arena := arena1 }, scratch := sc1 } : FullState).core)
    (hlen1 : ({ s with core := { s.core with arena := arena1 }, scratch := sc1 } :
      FullState).LengthsOk c)
    (hexp1 : FullExtScratchPres s
      { s with core := { s.core with arena := arena1 }, scratch := sc1 })
    (hws1 : sc1.work_stk1 = s.scratch.work_stk1) (hws2 : sc1.work_stk2 = s.scratch.work_stk2)
    (hant1 : sc1.ant_sz = s.scratch.ant_sz) (hres1 : sc1.res_sz = s.scratch.res_sz)
    (hrefs1 : fullArenaClauseRefs
      { s with core := { s.core with arena := arena1 }, scratch := sc1 } = fullArenaClauseRefs s)
    (hcl1 : ∀ r ∈ fullArenaClauseRefs s,
      fullArenaClauseSize { s with core := { s.core with arena := arena1 }, scratch := sc1 } r =
        fullArenaClauseSize s r ∧
      fullArenaClauseGarb { s with core := { s.core with arena := arena1 }, scratch := sc1 } r =
        fullArenaClauseGarb s r ∧
      fullArenaClauseLits { s with core := { s.core with arena := arena1 }, scratch := sc1 } r =
        fullArenaClauseLits s r)
    (har1_eq : ∀ k < fullArenaClauseSize s rsn.toNat,
      arena1[rsn.toNat + 3 + k]? = s.core.arena[rsn.toNat + 3 + k]?)
    (hm1 : (FullMem c { s with core := { s.core with arena := arena1 }, scratch := sc1 } ⋆
      (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) m1)
    (hQ : ∀ (ok : Bool) (mrk' : List (BitVec 8)) (tmp' : List (BitVec 32))
        (tc' tl' mcl' : Nat) (arena' : List (BitVec 32)) (sc' : FullScratch)
        (ext' : List (BitVec 64)) (m' : Mem 64),
      let s' : FullState :=
        { core := { s.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                                min_clr_len := mcl', arena := arena' },
          scratch := sc' }
      M6HdrExtOk ext' → (M6HdrExtInitOk ext → M6ExtW2bPres ext ext') →
      s'.LengthsOk c → FullWitnessCutInv c F0 F_cur cut s'.core →
      FullAnaMarksCov c s' → FullExtScratchPres s s' → sc'.work_stk2 = s.scratch.work_stk2 →
      s.core.tmp_len ≤ tl' → tl' ≤ s.core.cur_vars → s.core.tmp_cnt ≤ tc' →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
        fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
        fullArenaClauseLits s' r = fullArenaClauseLits s r) →
      (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 ≠ 0#8 →
        mrk'[v]?.getD 0#8 = s.core.mrk[v]?.getD 0#8) →
      (∀ k < s.core.tmp_len, tmp'[k]? = s.core.tmp[k]?) →
      (∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
        ∃ l ∈ fullRsnLits s rsn, l / 2 = v ∧ v < s.core.cur_vars ∧ v ≠ skip_var.toNat ∧
          0 < (s.core.lvl[v]?.getD 0#32).toNat ∧
          (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level) →
      (∀ j, s.core.tmp_len ≤ j → j < tl' → let l := (tmp'[j]?.getD 0#32).toNat
        l ∈ fullRsnLits s rsn ∧ l < 2 * s.core.cur_vars ∧ l / 2 ≠ skip_var.toNat ∧
        s.core.mrk[l / 2]?.getD 0#8 = 0#8 ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
        (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level ∧ mrk'[l / 2]?.getD 0#8 ≠ 0#8) →
      (∀ j1 j2, s.core.tmp_len ≤ j1 → j1 < j2 → j2 < tl' →
        (tmp'[j1]?.getD 0#32).toNat / 2 ≠ (tmp'[j2]?.getD 0#32).toNat / 2) →
      tc' - s.core.tmp_cnt = ((List.range s.core.cur_vars).filter fun w =>
        decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8) &&
        decide ((s.core.lvl[w]?.getD 0#32).toNat = s.core.cur_level)).length →
      sc'.res_sz = s.scratch.res_sz + BitVec.ofNat 64 ((List.range s.core.cur_vars).filter fun w =>
        decide (s.core.mrk[w]?.getD 0#8 = 0#8) && decide (mrk'[w]?.getD 0#8 ≠ 0#8)).length →
      (ok = true → rsn ≠ 0xFFFFFFFF#32 ∧
        sc'.ant_sz = s.scratch.ant_sz + BitVec.ofNat 64 ((fullRsnLits s rsn).countP fun l =>
          decide (l / 2 < s.core.cur_vars ∧ 0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
            (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level)) ∧
        ∀ l ∈ fullRsnLits s rsn, l / 2 < s.core.cur_vars ∧ (l / 2 ≠ skip_var.toNat →
          (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
          (s.core.mrk[l / 2]?.getD 0#8 = 0#8 →
            (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level ∧
            (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat →
              (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level →
              ∃ j, s.core.tmp_len ≤ j ∧ j < tl' ∧ (tmp'[j]?.getD 0#32).toNat / 2 = l / 2)))) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (Expr.group (sig := [[i32]])
      (fun Js => Blocks.cons (fun p_24 =>
        Expr.let_
          { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool rfl,
            args := (Arg.var p_24.fst, Arg.var sz_bv, ()) } fun p_25 =>
          Expr.jnz (Arg.var p_25.fst)
            (Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var rsn, ()) }
                fun p_26 =>
              Expr.let_
                { sig := [i64, i64], code := OpCode.add i64,
                  args := (Arg.var p_26.fst, Arg.imm 3, ()) } fun p_27 =>
                Expr.let_
                  { sig := [i32], code := OpCode.zext 32 64,
                    args := (Arg.var p_24.fst, ()) } fun p_28 =>
                  Expr.let_
                    { sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var p_27.fst, Arg.var p_28.fst, ()) } fun p_29 =>
                    Expr.let_
                      { sig := [i64, i64], code := OpCode.mul i64,
                        args := (Arg.var p_29.fst, Arg.imm 4, ()) } fun p_30 =>
                      Expr.let_
                        { sig := [i64, i64], code := OpCode.add i64,
                          args := (Arg.var pArena, Arg.var p_30.fst, ()) } fun p_31 =>
                        Expr.load i32 (Arg.var p_31.fst) fun ld =>
                          Expr.call (as := [i64, i32, i32]) (bs := [.bool]) "full_analyze_lit"
                              (Arg.var c.hdr, Arg.var ld, Arg.var skip_var, ()) fun p =>
                            Expr.jnz (Arg.var p.fst)
                              (Expr.let_
                                { sig := [i32, i32], code := OpCode.add i32,
                                  args := (Arg.var p_24.fst, Arg.imm 1, ()) } fun p =>
                                Expr.jump Js.fst (Arg.var p.fst, ()))
                              (Expr.ret (Arg.imm false, ())))
            (Expr.ret (Arg.imm true, ()))) Blocks.nil)
      (fun Js => Expr.jump Js.fst (Arg.imm 0, ()))) m1 := by
  subst hpArena hsz_bv
  let s1 : FullState := { s with core := { s.core with arena := arena1 }, scratch := sc1 }
  have har1_len := hlen1.core_ok.arena_len_arr; have har_len := hlen.core_ok.arena_len_arr
  have har_le := hlen.core_ok.arena_len_le
  let sz : Nat := fullArenaClauseSize s rsn.toNat
  have hsz_at : s.core.arena[(rsn.setWidth 64 + 2#64).toNat]'hsz_lt =
      s.core.arena[rsn.toNat + 2]'(by omega) := FullAnalyzeTactics.getElem_eq_of_idx hsz_idx
  have hsz_val : (s.core.arena[(rsn.setWidth 64 + 2#64).toNat]'hsz_lt).toNat = sz := by
    rw [hsz_at]; unfold sz fullArenaClauseSize fullArenaClauseSizeCore
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  let antPred : Nat → Bool := fun l => decide (l / 2 < s.core.cur_vars ∧
    0 < (s.core.lvl[l / 2]?.getD 0#32).toNat ∧
    (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level)
  refine wp_loop_inv (fun (iv, ()) ml => ∃ i mrk' tmp' mcl' tc' tl' ant' res' ws1',
    i ≤ sz ∧ iv = BitVec.ofNat 32 i ∧
    mrk'.length = c.max_vars ∧ tmp'.length = c.max_vars ∧ ws1'.length = 2 * c.max_vars ∧
    mcl' ≤ c.max_vars ∧ s.core.tmp_len ≤ tl' ∧ tl' ≤ s.core.cur_vars ∧ s.core.tmp_cnt ≤ tc' ∧
    FullAnalyzeSpecs.AnaWorkInv c { s1 with
      core := { s1.core with
        mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl', min_clr_len := mcl' },
      scratch := { sc1 with work_stk1 := ws1', ant_sz := ant', res_sz := res' } } ∧
    M6oRsnStepPre s (fullArenaClauseLits s rsn.toNat) skip_var mrk' tmp' tc' tl' res' ∧
    (∀ w < s.core.cur_vars, s.core.mrk[w]?.getD 0#8 = 0#8 → mrk'[w]?.getD 0#8 ≠ 0#8 →
      (s.core.lvl[w]?.getD 0#32).toNat < s.core.cur_level →
      ∃ j, s.core.tmp_len ≤ j ∧ j < tl' ∧ (tmp'[j]?.getD 0#32).toNat / 2 = w) ∧
    ant' = s.scratch.ant_sz +
      BitVec.ofNat 64 (((fullArenaClauseLits s rsn.toNat).take i).countP antPred) ∧
    (∀ k < i, let l := (s.core.arena[rsn.toNat + 3 + k]?.getD 0#32).toNat
      l / 2 < s.core.cur_vars ∧ (l / 2 ≠ skip_var.toNat →
        (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat → mrk'[l / 2]?.getD 0#8 ≠ 0#8) ∧
        (s.core.mrk[l / 2]?.getD 0#8 = 0#8 → (s.core.lvl[l / 2]?.getD 0#32).toNat ≤ s.core.cur_level
          ∧ (0 < (s.core.lvl[l / 2]?.getD 0#32).toNat →
            (s.core.lvl[l / 2]?.getD 0#32).toNat < s.core.cur_level →
            ∃ j, s.core.tmp_len ≤ j ∧ j < tl' ∧ (tmp'[j]?.getD 0#32).toNat / 2 = l / 2)))) ∧
    (FullMem c { s1 with
      core := { s1.core with
        mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl', min_clr_len := mcl' },
      scratch := { sc1 with work_stk1 := ws1', ant_sz := ant', res_sz := res' } } ⋆
      (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) ml)
    (fun (iv, ()) _ => sz - iv.toNat)
    (fun L hL => by
      c0_hsteps_nogrp
      have hwks : FullAnalyzeSpecs.AnaWorkInv c s1 := by
        obtain ⟨h1, h2, h3, h4⟩ := hwork
        refine ⟨h1, by simpa only [s1, hws1] using h2, by simpa only [s1, hws1] using h3,
          fun v hv hnz => let ⟨k, hk, heq⟩ := h4 v hv hnz
            ⟨heq ▸ (h3 k hk).1, k, hk, by simpa only [s1, hws1] using heq⟩⟩
      refine hL (0#32, ()) m1 ⟨0, s.core.mrk, s.core.tmp, s.core.min_clr_len, s.core.tmp_cnt,
        s.core.tmp_len, s.scratch.ant_sz, s.scratch.res_sz, s.scratch.work_stk1,
        Nat.zero_le _, rfl, hlen1.core_ok.mrk_len, hlen1.core_ok.tmp_len_arr,
        hlen.scratch_ok.work_stk1_len, hlen1.core_ok.min_clr_len_le, Nat.le_refl _, htl_cv,
        Nat.le_refl _, (by simpa only [s1, ← hant1, ← hres1, ← hws1] using hwks),
        ⟨fun _ _ _ => rfl, fun _ _ => rfl, fun _ _ h0 hnz => absurd h0 hnz,
          fun _ h1 h2 => by omega, fun _ _ _ h1 h2 => by omega,
          by rw [Nat.sub_self, m6o_filter_zero]; intro _ _; simp,
          by rw [m6o_filter_zero (fun _ _ => by simp)]; simp⟩,
        fun _ _ h0 hnz _ => absurd h0 hnz, by simp, fun _ hk => by omega, ?_⟩
      simpa only [s1, ← hant1, ← hres1, ← hws1] using hm1)
    (fun L (iv, ()) ml ⟨i, mrk', tmp', mcl', tc', tl', ant', res', ws1', hile, hiv_eq,
        hml_l, htl_l, hws_l, hmcl_le, htl_ge, htl_le, htc_ge, hwk', hpre, hnewlow, hant_l,
        hdone, hml⟩ hL => ?_)
  · subst hiv_eq
    have ⟨hmpres, htpres, hnewm, hnewt, hnd_t, hcnt, hres_l⟩ := hpre
    have hi32 : i < 2 ^ 32 := by omega
    have hi_mod : (BitVec.ofNat 32 i).toNat = i := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi32]
    c0_hsteps_nogrp
    · have hilt : i < sz := by
        have hlt_bv : (BitVec.ofNat 32 i).toNat < (s.core.arena[(rsn.setWidth 64 + 2#64).toNat]'(
            by rw [hsz_idx]; omega)).toNat := BitVec.lt_def.mp (by assumption)
        rw [hi_mod, hsz_val] at hlt_bv; exact hlt_bv
      have hidx_l : (rsn.setWidth 64 + 3 + (BitVec.ofNat 32 i).setWidth 64).toNat =
          rsn.toNat + 3 + i := by
        rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_setWidth]
        simp [Nat.mod_eq_of_lt (by omega : rsn.toNat < 2 ^ 64),
          Nat.mod_eq_of_lt (by omega : i < 2 ^ 32)]
        omega
      have hsz_core : sz = fullArenaClauseSizeCore s.core rsn.toNat := rfl
      have hidx_lt : (rsn.setWidth 64 + 3 + (BitVec.ofNat 32 i).setWidth 64).toNat <
          arena1.length := by rw [hidx_l, har1_len]; rw [hsz_core] at hilt; omega
      have htc_le_mv : tc' - s.core.tmp_cnt ≤ s.core.cur_vars := by
        rw [hcnt]; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
      let st : FullState := { s1 with
        core := { s1.core with
          mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl', min_clr_len := mcl' },
        scratch := { sc1 with work_stk1 := ws1', ant_sz := ant', res_sz := res' } }
      have hst_len : st.LengthsOk c := ⟨{ hlen1.core_ok with
          mrk_len := hml_l, tmp_len_arr := htl_l,
          tmp_len_le := (by dsimp [st]; omega), min_clr_len_le := hmcl_le },
        { hlen1.scratch_ok with work_stk1_len := hws_l }⟩
      let l_bv : BitVec 32 := arena1[rsn.toNat + 3 + i]'(by omega)
      have hl_eq : l_bv = s.core.arena[rsn.toNat + 3 + i]'(by omega) := by
        have h1 : arena1[rsn.toNat + 3 + i]? = some l_bv := List.getElem?_eq_getElem (by omega)
        rw [har1_eq i hilt, List.getElem?_eq_getElem (by omega)] at h1
        exact (Option.some.inj h1).symm
      have hl_get : (s.core.arena[rsn.toNat + 3 + i]?.getD 0#32).toNat = l_bv.toNat := by
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some, ← hl_eq]
      have hl_mem : l_bv.toNat ∈ fullArenaClauseLits s rsn.toNat :=
        (mem_fullArenaClauseLitsCore_iff (by omega)).mpr ⟨i, hilt, by rw [← hl_eq]⟩
      c0_hsteps_nogrp; dsimp only [st, s1]
      rw [FullAnalyzeTactics.getElem_eq_of_idx (hi := hidx_lt) (hj := by omega) hidx_l]
      c0_call hLit
      refine ⟨c, st, m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R, rfl, hst_len, hcur32, htl_le,
        by dsimp [st]; omega,
        ⟨hwk'.1, hwk'.2.1, hwk'.2.2.1, fun v hv hnz => (hwk'.2.2.2 v hv hnz).2⟩, hml,
        fun ok2 mrk2 tmp2 tc2 tl2 mcl2 ws2 ant2 res2 m2 hlen2 hwk2 htl2_ge htl2_inc htl2_le
          htc2_ge hant2 hres2 htc2_eq hmpres2 htpres2 hnewm2 hnewt2 hok2 hm2 => ?_⟩
      dsimp only [st] at *
      have hwk2_ana : FullAnalyzeSpecs.AnaWorkInv c { s1 with
          core := { s1.core with
            mrk := mrk2, tmp := tmp2, tmp_cnt := tc2, tmp_len := tl2, min_clr_len := mcl2 },
          scratch := { sc1 with work_stk1 := ws2, ant_sz := ant2, res_sz := res2 } } :=
        ⟨hwk2.1, hwk2.2.1, hwk2.2.2.1, fun v hv hnz => let ⟨k, hk, heq⟩ := hwk2.2.2.2 v hv hnz
          ⟨heq ▸ (hwk2.2.2.1 k hk).1, k, hk, heq⟩⟩
      have hpre2 := m6o_rsn_comb_step htl_ge htl2_ge htl2_inc htc_ge hl_mem hpre
        (fun w hw => hmpres2 w (Nat.lt_of_lt_of_le hw hcv_le)) htpres2 (fun w hw h0 hnz =>
          let h := hnewm2 w (Nat.lt_of_lt_of_le hw hcv_le) h0 hnz; ⟨h.1, h.2.2.1, h.2.2.2⟩)
        hnewt2 hres2 htc2_eq
      cases ok2 with
      | false =>
        c0_hsteps_nogrp; obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hpre2
        have h1c : ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 ≠ 0#8 →
            mrk2[v]?.getD 0#8 = s.core.mrk[v]?.getD 0#8 := fun v hv hnz =>
          h1 v (let ⟨k, hk, heq⟩ := hwork.2.2.2 v hv hnz; heq ▸ (hwork.2.2.1 k hk).1) hnz
        have h3c : ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8 → mrk2[v]?.getD 0#8 ≠ 0#8 →
            ∃ l ∈ fullRsnLits s rsn, l / 2 = v ∧ v < s.core.cur_vars ∧ v ≠ skip_var.toNat ∧
              0 < (s.core.lvl[v]?.getD 0#32).toNat ∧
              (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level := fun v hv h0 hnz =>
          let hvlt := (hwk2_ana.2.2.2 v hv hnz).1; let ⟨l, hl, hr⟩ := h3 v hvlt h0 hnz
          ⟨l, (FullAnalyzeHelpers.mem_fullRsnLits_large hne hlarge).mpr hl, hr.1, hvlt, hr.2⟩
        exact hQ false mrk2 tmp2 tc2 tl2 mcl2 arena1
          { sc1 with work_stk1 := ws2, ant_sz := ant2, res_sz := res2 } ext1 m2
          hext1 hwb1 hlen2
          { hw1 with
            arena := { hw1.arena with len_ok := hw1.arena.len_ok },
            watches := hw1.watches.with_wstk rfl rfl rfl rfl rfl fun _ hr => hr }
          hwk2 hexp1 hws2 (Nat.le_trans htl_ge htl2_ge) htl2_le (Nat.le_trans htc_ge htc2_ge)
          hrefs1 hcl1 h1c h2 h3c (fun j hj1 hj2 => let ⟨ha, hr⟩ := h4 j hj1 hj2
            ⟨(FullAnalyzeHelpers.mem_fullRsnLits_large hne hlarge).mpr ha, hr⟩)
          h5 h6 h7 (fun hc => by cases hc) (fullM6HdrMem_unfocus hm2)
      | true =>
        c0_hsteps_nogrp
        · obtain ⟨hvlt, hrest⟩ := hok2 rfl
          have htake1 : (fullArenaClauseLits s rsn.toNat).take (i + 1) =
              (fullArenaClauseLits s rsn.toNat).take i ++ [l_bv.toNat] := by
            have hlen_l : (fullArenaClauseLits s rsn.toNat).length = sz := by
              simp [fullArenaClauseLits, fullArenaClauseLitsCore, sz, fullArenaClauseSize]; omega
            rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some]
            congr 2; unfold fullArenaClauseLits fullArenaClauseLitsCore
            simp [List.getElem_map, List.getElem_take, List.getElem_drop, ← hl_eq]
          have hant2_eq : ant2 = s.scratch.ant_sz + BitVec.ofNat 64
              (((fullArenaClauseLits s rsn.toNat).take (i + 1)).countP antPred) := by
            rw [hant2, hant_l, htake1, List.countP_append, List.countP_cons, List.countP_nil,
              Nat.zero_add, BitVec.add_assoc, BitVec.ofNat_add]
            exact congrArg (s.scratch.ant_sz + ·) (congrArg _
              (m6o_bv64_ite_iff (by simp only [antPred, decide_eq_true_eq]; rfl)))
          rw [show BitVec.ofNat 32 i + 1 = BitVec.ofNat 32 (i + 1) from
            BitVec.eq_of_toNat_eq (by simp [BitVec.toNat_add, hi_mod])]
          refine hL (BitVec.ofNat 32 (i + 1), ()) m2
            (by rw [bv32_ofNat_toNat (by omega), hi_mod]; omega)
            ⟨i + 1, mrk2, tmp2, mcl2, tc2, tl2, ant2, res2, ws2, by omega, rfl,
              hlen2.core_ok.mrk_len, hlen2.core_ok.tmp_len_arr, hlen2.scratch_ok.work_stk1_len,
              hlen2.core_ok.min_clr_len_le, by omega, htl2_le, by omega, hwk2_ana, hpre2, ?_,
              hant2_eq, ?_, hm2⟩
          · intro w hw_lt hs0 hmnz2 hltcl
            by_cases hm1_w : mrk'[w]?.getD 0#8 = 0#8
            · obtain ⟨rfl, _, hne', hpos, _⟩ :=
                hnewm2 w (Nat.lt_of_lt_of_le hw_lt hcv_le) hm1_w hmnz2
              obtain ⟨_, htget⟩ := ((hrest hne').2 hm1_w).2.2 hpos hltcl
              exact ⟨tl', htl_ge, by omega, by rw [htget]; rfl⟩
            · obtain ⟨j, hj1, hj2, hjeq⟩ := hnewlow w hw_lt hs0 hm1_w hltcl
              exact ⟨j, hj1, by omega, by rw [htpres2 j hj2]; exact hjeq⟩
          · intro k hk; by_cases hki : k = i
            · subst hki; rw [hl_get]; refine ⟨hvlt, fun hne' => ?_⟩
              obtain ⟨hpos_m, hm1_r⟩ := hrest hne'; refine ⟨hpos_m, fun hs0 => ?_⟩
              by_cases hm1_w : mrk'[l_bv.toNat / 2]?.getD 0#8 = 0#8
              · obtain ⟨hle, _, hlow⟩ := hm1_r hm1_w
                exact ⟨hle, fun hpos hltcl => let ⟨_, htget⟩ := hlow hpos hltcl
                  ⟨tl', htl_ge, by omega, by rw [htget]; rfl⟩⟩
              · obtain ⟨_, _, _, _, _, hle⟩ := hnewm _ hvlt hs0 hm1_w
                exact ⟨hle, fun _ hltcl =>
                  let ⟨j, hj1, hj2, hjeq⟩ := hnewlow _ hvlt hs0 hm1_w hltcl
                  ⟨j, hj1, by omega, by rw [htpres2 j hj2]; exact hjeq⟩⟩
            · obtain ⟨hkv, hkrest⟩ := hdone k (by omega)
              refine ⟨hkv, fun hne' => ?_⟩; obtain ⟨h1, h2⟩ := hkrest hne'
              refine ⟨fun hp => by
                rw [hmpres2 _ (Nat.lt_of_lt_of_le hkv hcv_le) (h1 hp)]; exact h1 hp, fun hs0 => ?_⟩
              obtain ⟨hle, hlow⟩ := h2 hs0
              exact ⟨hle, fun hpos hltcl => let ⟨j, hj1, hj2, hjeq⟩ := hlow hpos hltcl
                ⟨j, hj1, by omega, by rw [htpres2 j hj2]; exact hjeq⟩⟩
        · exact False.elim (Bool.noConfusion (by assumption : true = false))
    · c0_hsteps_nogrp
      have hieq : i = sz := by
        have hnot : ¬ BitVec.ofNat 32 i <
            s.core.arena[(rsn.setWidth 64 + 2#64).toNat]'(by rw [hsz_idx]; omega) := by assumption
        have hge_bv : ¬ (BitVec.ofNat 32 i).toNat <
            (s.core.arena[(rsn.setWidth 64 + 2#64).toNat]'(by rw [hsz_idx]; omega)).toNat :=
          fun h => hnot (BitVec.lt_def.mpr h)
        rw [hi_mod, hsz_val] at hge_bv; omega
      have h1c : ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 ≠ 0#8 →
          mrk'[v]?.getD 0#8 = s.core.mrk[v]?.getD 0#8 := fun v hv hnz =>
        hmpres v (let ⟨k, hk, heq⟩ := hwork.2.2.2 v hv hnz; heq ▸ (hwork.2.2.1 k hk).1) hnz
      have h3c : ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
          ∃ l ∈ fullRsnLits s rsn, l / 2 = v ∧ v < s.core.cur_vars ∧ v ≠ skip_var.toNat ∧
            0 < (s.core.lvl[v]?.getD 0#32).toNat ∧
            (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level := fun v hv h0 hnz =>
        let hvlt := (hwk'.2.2.2 v hv hnz).1; let ⟨l, hl, hr⟩ := hnewm v hvlt h0 hnz
        ⟨l, (FullAnalyzeHelpers.mem_fullRsnLits_large hne hlarge).mpr hl, hr.1, hvlt, hr.2⟩
      refine hQ true mrk' tmp' tc' tl' mcl' arena1
        { sc1 with work_stk1 := ws1', ant_sz := ant', res_sz := res' } ext1 ml hext1 hwb1
        ⟨{ hlen1.core_ok with
            mrk_len := hml_l, tmp_len_arr := htl_l,
            tmp_len_le := (by dsimp; omega), min_clr_len_le := hmcl_le },
         { hlen1.scratch_ok with work_stk1_len := hws_l }⟩
        { hw1 with
          arena := { hw1.arena with len_ok := hw1.arena.len_ok },
          watches := hw1.watches.with_wstk rfl rfl rfl rfl rfl fun _ hr => hr }
        ⟨hwk'.1, hwk'.2.1, hwk'.2.2.1, fun v hv hnz => (hwk'.2.2.2 v hv hnz).2⟩
        hexp1 hws2 htl_ge htl_le htc_ge hrefs1 hcl1 h1c htpres h3c
        (fun j hj1 hj2 => let ⟨ha, hr⟩ := hnewt j hj1 hj2
          ⟨(FullAnalyzeHelpers.mem_fullRsnLits_large hne hlarge).mpr ha, hr⟩)
        hnd_t hcnt hres_l (fun _ => ?_) (fullM6HdrMem_unfocus hml)
      refine ⟨hne, ?_, fun l hl => ?_⟩
      · have hlen_l : (fullArenaClauseLits s rsn.toNat).length = sz := by
          simp only [fullArenaClauseLits, fullArenaClauseLitsCore, sz, fullArenaClauseSize,
            List.length_map, List.length_take, List.length_drop]; omega
        rw [hant_l, hieq, List.take_of_length_le (Nat.le_of_eq hlen_l)]
        simp [fullRsnLits, hne, hlarge, antPred]
      · simp only [fullRsnLits, hne, hlarge, ↓reduceIte] at hl
        obtain ⟨k, hk, hget⟩ := (mem_fullArenaClauseLitsCore_iff (by omega)).mp hl
        have hkget : (s.core.arena[rsn.toNat + 3 + k]?.getD 0#32).toNat = l := by
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hget]
        have hd := hdone k (by rw [hieq]; exact hk); rwa [hkget] at hd

private def m6oGlueStepExpr {ret : List Ty} (pLvl cv64 var64 lo best : Val i64) (k : Val i32)
    (Li : Cont [i64, i32]) : Expr Val Cont ret :=
  Expr.group (sig := [[i64]]) (fun _Js => Blocks.cons (fun p =>
      Expr.let_ { sig := [i32, i32], code := OpCode.add i32, args := (Arg.var k, Arg.imm 1, ()) }
        fun p_38 => Expr.jump Li (Arg.var p.fst, Arg.var p_38.fst, ())) Blocks.nil)
    fun Js => Expr.let_
      { sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64 Ty.bool rfl,
        args := (Arg.var var64, Arg.var cv64, ()) } fun p_38 =>
    Expr.jnz (Arg.var p_38.fst)
      (Expr.let_
        { sig := [i64, i64], code := OpCode.mul i64, args := (Arg.var var64, Arg.imm 4, ()) }
          fun p =>
      Expr.let_
        { sig := [i64, i64], code := OpCode.add i64, args := (Arg.var pLvl, Arg.var p.fst, ()) }
          fun p =>
      Expr.load i32 (Arg.var p.fst) fun ld =>
      Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var ld, ()) } fun p =>
      Expr.group (sig := [[i64]])
        (fun _Js => Blocks.cons (fun p => Expr.jump Js.fst (Arg.var p.fst, ())) Blocks.nil)
        fun Js => Expr.let_
          { sig := [i64, i64], code := OpCode.cmp CmpOp.uge i64 Ty.bool rfl,
            args := (Arg.var p.fst, Arg.var lo, ()) } fun p_39 =>
        Expr.jnz (Arg.var p_39.fst)
          (Expr.let_
            { sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64 Ty.bool rfl,
              args := (Arg.var p.fst, Arg.var best, ()) } fun p_40 =>
          Expr.jnz (Arg.var p_40.fst) (Expr.jump Js.fst (Arg.var p.fst, ()))
            (Expr.jump Js.fst (Arg.var best, ())))
          (Expr.jump Js.fst (Arg.var best, ())))
      (Expr.jump Js.fst (Arg.var best, ()))

private theorem m6o_rsn_glue_step {Γ : Env} {c : FullCfg} {ext : List (BitVec 64)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [.bool]} {X : XPost}
    {k : Val i32} {var64 pLvl cv64 lo best : Val i64} {Li : Cont [i64, i32]}
    (hpLvl : pLvl = c.pLevel) (hcv64 : cv64 = BitVec.ofNat 64 s.core.cur_vars)
    (hlen : s.LengthsOk c) (hmf : (FullMem c s ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m)
    (hLi : ∀ best' : Val i64, Li (best', k + 1#32, ()) m) :
    wp Γ Q X (m6oGlueStepExpr pLvl cv64 var64 lo best k Li) m := by
  subst hpLvl hcv64; unfold m6oGlueStepExpr
  refine wp_join_group (ts := [i64]) (fun _ ml => ml = m) ?_ ?_
  · rintro _ ⟨best', ⟨⟩⟩ ml hml; cases hml; c0_hsteps_nogrp; exact hLi best'
  · intro Jb hJb; c0_hsteps_nogrp
    · have hkv_lt : var64.toNat < s.core.lvl.length := by
        have hcv_le := hlen.core_ok.cur_vars_le; have hmax := fullInv_max_vars_lt32 c
        have hlt : var64.toNat < s.core.cur_vars % 2 ^ 64 := by assumption
        rw [Nat.mod_eq_of_lt (by omega)] at hlt; rw [hlen.core_ok.lvl_len]; omega
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64]) (fun _ ml => ml = m)
        (fun _ ⟨best', ⟨⟩⟩ ml hml => by cases hml; exact hJb _ m rfl)
        (fun Jb2 hJb2 => by c0_hsteps_nogrp <;> exact hJb2 _ m rfl)
    · exact hJb _ m rfl

private def M6oGluePred (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (cut : Nat)
    (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop) (rsn : Val i32)
    (p : Tup Val [i32, i64]) (m0 : Mem 64) : Prop :=
  ∃ arena0,
    let s0 : FullState := { s with core := { s.core with arena := arena0 } }
    arena0[rsn.toNat]? = some p.1 ∧ FullWitnessCutInv c F0 F_cur cut s0.core ∧
    s0.LengthsOk c ∧ fullArenaClauseRefs s0 = fullArenaClauseRefs s ∧
    (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s0 r = fullArenaClauseSize s r ∧
      fullArenaClauseGarb s0 r = fullArenaClauseGarb s r ∧
      fullArenaClauseLits s0 r = fullArenaClauseLits s r) ∧
    (∀ k < fullArenaClauseSize s rsn.toNat,
      arena0[rsn.toNat + 3 + k]? = s.core.arena[rsn.toNat + 3 + k]?) ∧
    (FullMem c s0 ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m0

private theorem m6o_rsn_glue_lo {Γ : Env} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {cut : Nat} {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [.bool]} {X : XPost} {rsn ld_2 sz_bv : Val i32}
    {pArena pLvl cv64 glue lim : Val i64} {Jg : Cont [i32, i64]}
    (hpArena : pArena = c.pArena) (hpLvl : pLvl = c.pLevel)
    (hcv64 : cv64 = BitVec.ofNat 64 s.core.cur_vars)
    (hlen : s.LengthsOk c) (hw : FullWitnessCutInv c F0 F_cur cut s.core)
    (href : rsn.toNat ∈ fullArenaClauseRefs s) (hrsn_lt : rsn.toNat < s.core.arena.length)
    (hrsn_z_lt : (rsn.setWidth 64).toNat < s.core.arena.length)
    (hsz_lt : rsn.toNat + 2 < s.core.arena.length)
    (hsz_idx : (rsn.setWidth 64 + 2#64).toNat = rsn.toNat + 2)
    (hld2 : ld_2 = s.core.arena[(rsn.setWidth 64).toNat]'hrsn_z_lt)
    (hglue : glue = (ld_2 &&& 524287#32).setWidth 64)
    (hsz_bv : sz_bv = s.core.arena[(rsn.setWidth 64 + 2#64).toNat]'(by rw [hsz_idx]; exact hsz_lt))
    (hsz_get : (s.core.arena[rsn.toNat + 2]'hsz_lt).toNat = fullArenaClauseSize s rsn.toNat)
    (hrsn_get : s.core.arena[rsn.toNat]? = some ld_2)
    (hmf : (FullMem c s ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m) (hlim : lim.toNat < 2 ^ 19)
    (hJg : ∀ (xs : Tup Val [i32, i64]) (m0 : Mem 64),
      M6oGluePred c F0 F_cur cut ext s R rsn xs m0 → Jg xs m0) :
    wp Γ Q X (Expr.group (sig := [[i64, i64, .bool]]) (fun Js_3 => Blocks.cons (fun p_33 =>
      Expr.group (sig := [[]]) (fun _Js_4 => Blocks.cons (fun _p_34 =>
        Expr.group (sig := [[i32, i64]])
          (fun _Js_5 => Blocks.cons (fun p => Expr.jump Jg (Arg.var p.fst, Arg.var p.snd.fst, ()))
            Blocks.nil)
          fun Js => Expr.jnz (Arg.var p_33.snd.snd.fst)
            (Expr.jump Js.fst (Arg.var ld_2, Arg.var glue, ()))
            (Expr.let_
              { sig := [i64, i64], code := OpCode.cmp CmpOp.ugt i64 Ty.bool rfl,
                args := (Arg.var p_33.fst, Arg.imm 0, ()) } fun p_35 =>
            Expr.jnz (Arg.var p_35.fst)
              (Expr.let_
                { sig := [i64, i64], code := OpCode.cmp CmpOp.ult i64 Ty.bool rfl,
                  args := (Arg.var p_33.fst, Arg.var glue, ()) } fun p_36 =>
              Expr.jnz (Arg.var p_36.fst)
                (Expr.let_ { sig := [i32], code := OpCode.not i32, args := (Arg.imm 524287, ()) }
                  fun p_37 =>
                Expr.let_
                  { sig := [i32, i32], code := OpCode.and i32,
                    args := (Arg.var ld_2, Arg.var p_37.fst, ()) } fun p_38 =>
                Expr.let_
                  { sig := [i64], code := OpCode.trunc 64 32,
                    args := (Arg.var p_33.fst, ()) } fun p_39 =>
                Expr.let_
                  { sig := [i32, i32], code := OpCode.or i32,
                    args := (Arg.var p_38.fst, Arg.var p_39.fst, ()) } fun p_40 =>
                Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var rsn, ()) }
                  fun p =>
                Expr.let_
                  { sig := [i64, i64], code := OpCode.mul i64,
                    args := (Arg.var p.fst, Arg.imm 4, ()) } fun p =>
                Expr.let_
                  { sig := [i64, i64], code := OpCode.add i64,
                    args := (Arg.var pArena, Arg.var p.fst, ()) } fun p =>
                Expr.store (t := i32) (Arg.var p_40.fst) (Arg.var p.fst)
                  (Expr.jump Js.fst (Arg.var p_40.fst, Arg.var p_33.fst, ())))
                (Expr.jump Js.fst (Arg.var ld_2, Arg.var glue, ())))
              (Expr.jump Js.fst (Arg.var ld_2, Arg.var glue, ())))) Blocks.nil)
        fun Js => Expr.jnz (Arg.var p_33.snd.snd.fst)
          (Expr.let_
            { sig := [i64, i64], code := OpCode.cmp CmpOp.ule i64 Ty.bool rfl,
              args := (Arg.var p_33.fst, Arg.var lim, ()) } fun p_34 =>
          Expr.jnz (Arg.var p_34.fst)
            (Expr.group (sig := [[i64, i32]]) (fun Li => Blocks.cons (fun p_35 =>
              Expr.let_
                { sig := [i32, i32], code := OpCode.cmp CmpOp.ult i32 Ty.bool rfl,
                  args := (Arg.var p_35.snd.fst, Arg.var sz_bv, ()) } fun p_36 =>
              Expr.jnz (Arg.var p_36.fst)
                (Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var rsn, ()) }
                  fun p_r =>
                Expr.let_
                  { sig := [i64, i64], code := OpCode.add i64,
                    args := (Arg.var p_r.fst, Arg.imm 3, ()) } fun p =>
                Expr.let_
                  { sig := [i32], code := OpCode.zext 32 64,
                    args := (Arg.var p_35.snd.fst, ()) } fun p_37 =>
                Expr.let_
                  { sig := [i64, i64], code := OpCode.add i64,
                    args := (Arg.var p.fst, Arg.var p_37.fst, ()) } fun p =>
                Expr.let_
                  { sig := [i64, i64], code := OpCode.mul i64,
                    args := (Arg.var p.fst, Arg.imm 4, ()) } fun p =>
                Expr.let_
                  { sig := [i64, i64], code := OpCode.add i64,
                    args := (Arg.var pArena, Arg.var p.fst, ()) } fun p =>
                Expr.load i32 (Arg.var p.fst) fun ld =>
                Expr.let_
                  { sig := [i32, i32], code := OpCode.lshr i32,
                    args := (Arg.var ld, Arg.imm 1, ()) } fun p =>
                Expr.let_ { sig := [i32], code := OpCode.zext 32 64, args := (Arg.var p.fst, ()) }
                  fun p =>
                    m6oGlueStepExpr pLvl cv64 p.fst p_33.snd.fst p_35.fst p_35.snd.fst Li.fst)
                (Expr.group (sig := [[i64, i64, .bool]]) (fun _Js => Blocks.cons (fun p =>
                  Expr.jump Js_3.fst (Arg.var p.fst, Arg.var p.snd.fst, Arg.var p.snd.snd.fst, ()))
                  Blocks.nil) fun Js => Expr.let_
                  { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
                    args := (Arg.var p_35.fst, Arg.imm 0xFFFFFFFFFFFFFFFF, ()) } fun p =>
                Expr.jnz (Arg.var p.fst)
                  (Expr.jump Js.fst (Arg.var p_33.fst, Arg.var p_33.snd.fst, Arg.imm false, ()))
                  (Expr.let_
                    { sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var p_33.fst, Arg.imm 1, ()) } fun p =>
                  Expr.let_
                    { sig := [i64, i64], code := OpCode.add i64,
                      args := (Arg.var p_35.fst, Arg.imm 1, ()) } fun p_37 => Expr.jump Js.fst
                    (Arg.var p.fst, Arg.var p_37.fst, Arg.var p_33.snd.snd.fst, ()))))
              Blocks.nil) fun Li => Expr.jump Li.fst (Arg.imm 0xFFFFFFFFFFFFFFFF, Arg.imm 0, ()))
            (Expr.jump Js.fst ()))
          (Expr.jump Js.fst ())) Blocks.nil)
      fun Lo => Expr.jump Lo.fst (Arg.imm 0, Arg.imm 0, Arg.imm true, ())) m := by
  obtain ⟨_, _, hbd, hbd_le, _⟩ := hw.arena.refs_wf rsn.toNat href
  have har_len := hlen.core_ok.arena_len_arr; have har_le := hlen.core_ok.arena_len_le
  have hhdr_get : s.core.arena[rsn.toNat]'hrsn_lt = fullArenaHdrCore s.core rsn.toNat := by
    unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem hrsn_lt, Option.getD_some]
  subst hpArena hpLvl hcv64 hld2 hglue hsz_bv
  have hg_lt : (fullArenaHdrCore s.core rsn.toNat &&& 0x7FFFF#32).toNat < 2 ^ 19 :=
    Nat.lt_of_le_of_lt (bv32_and_le_right _ _) (by decide)
  have hgl_z : ((fullArenaHdrCore s.core rsn.toNat &&& 0x7FFFF#32).setWidth 64).toNat =
      (fullArenaHdrCore s.core rsn.toNat &&& 0x7FFFF#32).toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans hg_lt (by decide))]
  have hhdr' : s.core.arena[(rsn.setWidth 64).toNat]'hrsn_z_lt =
      fullArenaHdrCore s.core rsn.toNat := by simpa only [bv_c0_zext32_64] using hhdr_get
  refine wp_loop_inv (fun (ng, lo, more, ()) ml => ml = m ∧ ng.toNat ≤ lim.toNat + 1)
    (fun (ng, _, more, ()) _ => (if more then 1 else 0) + (lim.toNat + 1 - ng.toNat))
    (fun Lo hLo => by c0_hsteps_nogrp; exact hLo (0#64, 0#64, true, ()) m ⟨rfl, Nat.zero_le _⟩)
    (fun Lo (ng, lo, more, ()) ml ⟨hml, hng_le⟩ hLo => ?_)
  cases hml
  refine wp_join_group (ts := []) (fun (_ : Tup Val []) m_ex => m_ex = m) ?_ ?_
  · rintro _ _ m_ex hm_ex; cases hm_ex; c0_hsteps_nogrp
    refine wp_join_group (ts := [i32, i64]) (M6oGluePred c F0 F_cur cut ext s R rsn)
        (fun _ xs m0 h => hJg xs m0 h) ?_
    · intro Jg2 hJg2; c0_hsteps_nogrp
      all_goals try exact hJg2 (_, _, ()) m ⟨s.core.arena, hrsn_get, hw, hlen, rfl,
        fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ _ => rfl, hmf⟩
      · have hng_c : ng.toNat < ((s.core.arena[(rsn.setWidth 64).toNat]'hrsn_z_lt &&&
            524287#32).setWidth 64).toNat := BitVec.lt_def.mp (by assumption)
        have hng_lt_g : (ng.setWidth 32).toNat < 2 ^ 19 := by
          rw [hhdr', hgl_z] at hng_c; rw [BitVec.toNat_setWidth]; omega
        have hup := m6o_hdrBitsUpdate_cut hlen.core_ok hw href
          (fun x => (x &&& 0xFFF80000#32) ||| ng.setWidth 32)
          s.core.arena_garbage s.core.num_irred s.core.num_redundant
          (m6o_bv32_glue_bit (b := 19) _ _ _ (by decide) (by decide) (by decide) hng_lt_g)
          (m6o_bv32_glue_bit (b := 23) _ _ _ (by decide) (by decide) (by decide) hng_lt_g)
        let arena0 := s.core.arena.set rsn.toNat
          ((fullArenaHdrCore s.core rsn.toNat &&& 0xFFF80000#32) ||| ng.setWidth 32)
        have hm0' : (FullMem c { s with core := { s.core with arena := arena0 } } ⋆
            (m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R)) m := by
          have hm_rw : s.core.arena.set (rsn.setWidth 64).toNat
              ((s.core.arena[(rsn.setWidth 64).toNat]'hrsn_z_lt &&& 4294443008#32) |||
                ng.setWidth 32) = arena0 := by
            dsimp only [arena0]; rw [hhdr', bv_c0_zext32_64]
          rw [← hm_rw]; exact hm
        have hset : arena0[rsn.toNat]? = some
            ((s.core.arena[(rsn.setWidth 64).toNat]'hrsn_z_lt &&& ~~~524287#32) |||
              ng.setWidth 32) := by
          dsimp only [arena0]; rw [hhdr']; exact List.getElem?_set_self hrsn_lt
        exact hJg2 (_, ng, ()) _ ⟨arena0, hset, hup.1,
          ⟨{ hlen.core_ok with arena_len_arr := by simp [arena0, har_len] }, hlen.scratch_ok⟩,
          hup.2.1, hup.2.2, fun k _ => List.getElem?_set_ne (by omega), hm0'⟩
  · intro Jex hJex; c0_hsteps_nogrp
    · have hng_le' : ng.toNat ≤ lim.toNat := by bv_omega
      let sz : Nat := fullArenaClauseSize s rsn.toNat
      refine wp_loop_inv (fun (best, k, ()) ml => ml = m ∧ k.toNat ≤ sz)
        (fun (_, k, ()) _ => sz - k.toNat)
        (fun Li hLi => by
          c0_hsteps_nogrp; exact hLi (0xFFFFFFFFFFFFFFFF#64, 0#32, ()) m ⟨rfl, by simp⟩)
        (fun Li (best, k, ()) ml ⟨hkl, hkle⟩ hLi => ?_)
      · cases hkl; c0_hsteps_nogrp
        · have hk_lt : k.toNat < sz := by
            have h : k.toNat < (s.core.arena[(rsn.setWidth 64 + 2#64).toNat]'(by
                rw [hsz_idx]; exact hsz_lt)).toNat := BitVec.lt_def.mp ‹_›
            rwa [FullAnalyzeTactics.getElem_eq_of_idx hsz_idx, hsz_get] at h
          have hk1 : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
          have har_k_lt : (rsn.setWidth 64 + 3#64 + k.setWidth 64).toNat < s.core.arena.length := by
            have h3 : (rsn.setWidth 64 + 3#64).toNat = rsn.toNat + 3 := by bv_omega
            rw [BitVec.toNat_add, h3, BitVec.toNat_setWidth,
              Nat.mod_eq_of_lt (by omega : k.toNat < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
            have hk_lt_core : k.toNat < fullArenaClauseSizeCore s.core rsn.toNat := hk_lt; omega
          c0_hsteps_nogrp
          exact m6o_rsn_glue_step rfl rfl hlen hmf fun best' =>
            hLi (best', k + 1#32, ()) m (by dsimp only; rw [hk1]; omega) ⟨rfl, by rw [hk1]; omega⟩
        · refine wp_join_group (ts := [i64, i64, .bool]) (fun (p : Tup Val [i64, i64, .bool]) ml =>
              ml = m ∧ p.1.toNat ≤ lim.toNat + 1 ∧
              (if p.2.2.1 then 1 else 0) + (lim.toNat + 1 - p.1.toNat) <
                (if more then 1 else 0) + (lim.toNat + 1 - ng.toNat)) ?_ ?_
          · rintro _ ⟨ng', lo', more', ⟨⟩⟩ ml ⟨hml, hle', hlt'⟩
            cases hml; c0_hsteps_nogrp; exact hLo (ng', lo', more', ()) m hlt' ⟨rfl, hle'⟩
          · intro Jm hJm; c0_hsteps_nogrp
            · have hm_eq : more = true := by assumption
              subst hm_eq; exact hJm (ng, lo, false, ()) m ⟨rfl, hng_le, by simp⟩
            · have hm_eq : more = true := by assumption
              subst hm_eq; have hng1 : (ng + 1#64).toNat = ng.toNat + 1 := by bv_omega
              exact hJm (ng + 1#64, best + 1#64, true, ()) m
                ⟨rfl, by rw [hng1]; omega, by simp [hng1]; omega⟩
    all_goals exact hJex () m rfl

theorem full_analyze_rsn_m6_hdr_wp (Γ : Env)
    (hLit : ∀ a m Q X, Full.fullAnalyzeLitSpec a m Q X →
      Γ "full_analyze_lit" [i64, i32, i32] [.bool] a m Q X)
    (hRec : ∀ a m Q X, m6HdrW2aSpec [i64] [] a m Q X →
      Γ "m6_hdr_record_used" [i64, i64] [] a m Q X) :
    ∀ a m Q X, m6AnalyzeRsnHdrSpec a m Q X →
      Func.wp Γ full_analyze_rsn_m6_hdr_body a m Q X := by
  rintro ⟨h, rsn, skip_var, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, cut, ext, s, R, rfl, hcfg, hext, hlen, hw, hwork, htl_cv, htc_fit,
      hrsn_ref, hm, hQ⟩
  have hmax32 := fullInv_max_vars_lt32 c; have hcv_le := hlen.core_ok.cur_vars_le
  have har_len := hlen.core_ok.arena_len_arr; have har_le := hlen.core_ok.arena_len_le
  have hcur32 : s.core.cur_level < 2 ^ 32 := by
    have := hw.cur_level_le; have := hlen.core_ok.trail_end_le; omega
  have hret_false_same : Q (false, ()) m :=
    hQ false s.core.mrk s.core.tmp s.core.tmp_cnt s.core.tmp_len s.core.min_clr_len s.core.arena
      s.scratch ext m hext (fun _ => M6ExtW2bPres.refl ext) hlen hw hwork ⟨rfl, rfl⟩ rfl
      (Nat.le_refl _) htl_cv (Nat.le_refl _) rfl (fun _ _ => ⟨rfl, rfl, rfl⟩)
      (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ _ h0 h => absurd h0 h)
      (fun _ h1 h2 => by omega) (fun _ _ _ h1 h2 => by omega)
      (by rw [Nat.sub_self, m6o_filter_zero]; intro _ _; simp)
      (by rw [m6o_filter_zero (fun _ _ => by simp)]; simp) (fun hc => by cases hc) hm
  unfold Func.wp full_analyze_rsn_m6_hdr_body
  c0_hsteps_nogrp
  · exact hret_false_same
  · have hne : rsn ≠ 0xFFFFFFFF#32 := by assumption
    have hbin : (rsn &&& 0x80000000#32) ≠ 0#32 := by assumption
    refine wp_m6Hdr_focus_frame hm fun hmf => ?_
    c0_hsteps_nogrp; c0_call hLit
    refine ⟨c, s, m6ExtMem (m6ExtAddr c.hdr) ext ⋆ R, rfl, hlen, hcur32, htl_cv, by omega,
      hwork, hmf, fun ok mrk' tmp' tc' tl' mcl' ws1' ant' res' m' hlen' hwork' htl_ge
        htl_le1 htl_cv' htc_ge hant' hres' htc_eq hmpres htpres hnewm hnewt hok hm' => ?_⟩
    c0_hsteps_nogrp
    have hsame_c : FullWitnessCutInv c F0 F_cur cut
        { s.core with mrk := mrk', tmp := tmp', tmp_cnt := tc', tmp_len := tl',
                      min_clr_len := mcl' } :=
      { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }
                watches := hw.watches.with_wstk rfl rfl rfl rfl rfl fun _ hr => hr }
    have htc_f := FullAnalyzeHelpers.filter_step_of_lit
      (fun w => decide ((s.core.lvl[w]?.getD 0#32).toNat = s.core.cur_level))
      (mv := s.core.cur_vars) (tc0 := s.core.tmp_cnt) (tc1 := s.core.tmp_cnt) (tc2 := tc')
      (v := (rsn &&& 0x7FFFFFFF#32).toNat / 2) (fun _ _ _ => rfl)
      (fun w hw => hmpres w (Nat.lt_of_lt_of_le hw hcv_le))
      (fun w hw_lt h0 hnz => (hnewm w (Nat.lt_of_lt_of_le hw_lt hcv_le) h0 hnz).1)
      (Nat.le_refl _) (by rw [Nat.sub_self, m6o_filter_zero]; intro _ _; simp)
      (by
        rw [htc_eq]; congr 1
        exact ite_congr
          (propext (by simp only [BitVec.ofNat_eq_ofNat, decide_eq_true_eq]))
          (fun _ => rfl) (fun _ => rfl))
    have hres_f := m6o_res_step_of_lit (mv := s.core.cur_vars)
      (v := (rsn &&& 0x7FFFFFFF#32).toNat / 2) (r0 := s.scratch.res_sz)
      (r1 := s.scratch.res_sz) (fun _ _ _ => rfl)
      (fun w hw => hmpres w (Nat.lt_of_lt_of_le hw hcv_le))
      (fun w hw_lt h0 hnz => (hnewm w (Nat.lt_of_lt_of_le hw_lt hcv_le) h0 hnz).1)
      (by rw [m6o_filter_zero (fun _ _ => by simp)]; simp) hres'
    have hmp_cv : ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 ≠ 0#8 →
        mrk'[v]?.getD 0#8 = s.core.mrk[v]?.getD 0#8 := fun v hv hnz => hmpres v hv hnz
    have hnewm_cv : ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8 → mrk'[v]?.getD 0#8 ≠ 0#8 →
        ∃ l ∈ fullRsnLits s rsn, l / 2 = v ∧ v < s.core.cur_vars ∧ v ≠ skip_var.toNat ∧
          0 < (s.core.lvl[v]?.getD 0#32).toNat ∧
          (s.core.lvl[v]?.getD 0#32).toNat ≤ s.core.cur_level := fun v hv h0 hnz => by
      obtain ⟨i, hi, heqv⟩ := hwork'.2.2.2 v hv hnz; have hvlt := (hwork'.2.2.1 i hi).1
      dsimp only at hvlt heqv; rw [heqv] at hvlt
      obtain ⟨rfl, _, hne', hpos, hle⟩ := hnewm v hv h0 hnz
      exact ⟨(rsn &&& 0x7FFFFFFF#32).toNat,
        (FullAnalyzeHelpers.mem_fullRsnLits_bin hne hbin).mpr rfl, rfl, hvlt, hne', hpos, hle⟩
    refine hQ ok mrk' tmp' tc' tl' mcl' s.core.arena _ ext m' hext
      (fun _ => M6ExtW2bPres.refl ext) hlen' hsame_c hwork' ⟨rfl, rfl⟩ rfl htl_ge htl_cv'
      htc_ge rfl (fun _ _ => ⟨rfl, rfl, rfl⟩) hmp_cv htpres hnewm_cv ?_
      (fun _ _ _ h1 h2 => by omega) htc_f hres_f ?_ (fullM6HdrMem_unfocus hm')
    · intro j hj1 hj2; obtain ⟨heq, _, _, h0, hpos, hcl, hmk⟩ := hnewt j hj1 hj2
      exact ⟨(FullAnalyzeHelpers.mem_fullRsnLits_bin hne hbin).mpr heq, by omega, by omega,
        by rwa [heq], by rwa [heq], by rwa [heq], by rwa [heq]⟩
    · intro hok'; obtain ⟨hvlt, hrest⟩ := hok hok'; refine ⟨hne, ?_, fun l hl => ?_⟩
      · rw [hant', fullRsnLits, ite_eq_right (fun h => hne h), ite_eq_left hbin, List.countP_cons,
          List.countP_nil, Nat.zero_add]
        exact congrArg (s.scratch.ant_sz + ·)
          (m6o_bv64_ite_iff (by simp only [decide_eq_true_eq]; rfl))
      · simp only [fullRsnLits, ite_eq_right (fun h => hne h), ite_eq_left hbin,
          List.mem_singleton] at hl; subst hl
        refine ⟨hvlt, fun hne' => ?_⟩
        obtain ⟨hm1, h0r⟩ := hrest hne'; refine ⟨hm1, fun h0 => ?_⟩
        obtain ⟨hle, _, hlow⟩ := h0r h0
        exact ⟨hle, fun hpos hlt => let ⟨_, htget⟩ := hlow hpos hlt
          ⟨s.core.tmp_len, Nat.le_refl _, by omega, by rw [htget]; rfl⟩⟩
  · have hne : rsn ≠ 0xFFFFFFFF#32 := by assumption
    have hlarge : (rsn &&& 0x80000000#32) = 0#32 := by assumption
    have href : rsn.toNat ∈ fullArenaClauseRefs s := hrsn_ref hne hlarge
    obtain ⟨hbd3, hsz3, hbd, hbd_le, _⟩ := hw.arena.refs_wf rsn.toNat href
    have hrsn_lt : rsn.toNat < s.core.arena.length := by omega
    have hsz_idx : (rsn.setWidth 64 + 2#64).toNat = rsn.toNat + 2 := by
      have hlt32 : rsn.toNat < 2 ^ 32 := rsn.isLt
      have hsw : (rsn.setWidth 64).toNat = rsn.toNat := by
        rw [BitVec.toNat_setWidth]; exact Nat.mod_eq_of_lt (by omega)
      rw [BitVec.toNat_add, hsw, show (2#64).toNat = 2 from rfl, Nat.mod_eq_of_lt (by omega)]
    have hsz_get : (s.core.arena[rsn.toNat + 2]'(by omega)).toNat =
        fullArenaClauseSize s rsn.toNat := by
      unfold fullArenaClauseSize fullArenaClauseSizeCore
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    have hhdr_get : s.core.arena[rsn.toNat]'hrsn_lt =
        fullArenaHdrCore s.core rsn.toNat := by
      unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem hrsn_lt, Option.getD_some]
    refine wp_m6Hdr_focus_frame hm fun hmf => ?_
    c0_hsteps_nogrp; all_goals try exact hret_false_same
    c0_hsteps_nogrp; all_goals try exact hret_false_same
    c0_hsteps_nogrp; all_goals try exact hret_false_same
    refine wp_join_group (ts := [i32]) (fun (_ : Tup Val [i32]) m1 =>
        ∃ (arena1 : List (BitVec 32)) (sc1 : FullScratch) (ext1 : List (BitVec 64)),
        let s1 : FullState := { s with core := { s.core with arena := arena1 }, scratch := sc1 }
        M6HdrExtOk ext1 ∧ (M6HdrExtInitOk ext → M6ExtW2bPres ext ext1) ∧
        FullWitnessCutInv c F0 F_cur cut s1.core ∧ s1.LengthsOk c ∧
        FullExtScratchPres s s1 ∧ sc1.work_stk1 = s.scratch.work_stk1 ∧
        sc1.work_stk2 = s.scratch.work_stk2 ∧ sc1.ant_sz = s.scratch.ant_sz ∧
        sc1.res_sz = s.scratch.res_sz ∧ fullArenaClauseRefs s1 = fullArenaClauseRefs s ∧
        (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s1 r = fullArenaClauseSize s r ∧
          fullArenaClauseGarb s1 r = fullArenaClauseGarb s r ∧
          fullArenaClauseLits s1 r = fullArenaClauseLits s r) ∧
        (∀ k < fullArenaClauseSize s rsn.toNat,
          arena1[rsn.toNat + 3 + k]? = s.core.arena[rsn.toNat + 3 + k]?) ∧
        (FullMem c s1 ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) m1) ?_ ?_
    · rintro _ ⟨_hdr, ⟨⟩⟩ m1 ⟨arena1, sc1, ext1, hext1, hwb1, hw1, hlen1, hexp1, hws1, hws2,
        hant1, hres1, hrefs1, hcl1, har1_eq, hm1⟩
      have hsz_lt_len : (rsn.setWidth 64 + 2#64).toNat < s.core.arena.length := by
        have := hlen.core_ok.arena_len_le; rw [hsz_idx]; omega
      c0_hsteps_nogrp
      exact m6o_rsn_lit_loop rfl hLit hext1 hwb1 hlen hwork htl_cv htc_fit hcv_le
        hcur32 hne hlarge hbd hbd_le hsz_idx hsz_lt_len rfl hw1 hlen1
        hexp1 hws1 hws2 hant1 hres1 hrefs1 hcl1 har1_eq hm1 hQ
    · intro Jred hJred
      c0_hsteps_nogrp
      · refine wp_join_group (ts := [i32, i64]) (M6oGluePred c F0 F_cur cut ext s R rsn) ?_ ?_
        · rintro _ ⟨hdr1, glue1, ⟨⟩⟩ m0 ⟨arena0, hget0, hw0, hlen0, hrefs0, hcl0,
            har0_eq, hm0⟩
          have har0_len : arena0.length = c.arena_cap := hlen0.core_ok.arena_len_arr
          let s0 : FullState := { s with core := { s.core with arena := arena0 } }
          c0_hsteps_nogrp
          refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hRec _ _ _ _ h) hcfg hext hlen0
            (fullM6HdrMem_unfocus hm0) fun _ ext1 s1 m1 hc1 hl1 hms1 hext1 hwb1 hm1 => ?_
          refine wp_m6Hdr_focus_frame hm1 fun hm1f => ?_
          have har1_len : s1.core.arena.length = c.arena_cap := hl1.core_ok.arena_len_arr
          c0_hsteps_nogrp
          refine wp_join_group (ts := []) (fun (_ : Tup Val []) m2 =>
              ∃ arena2 : List (BitVec 32),
              let s2 : FullState :=
                { core := { s.core with arena := arena2 }, scratch := s1.scratch }
              FullWitnessCutInv c F0 F_cur cut s2.core ∧ s2.core.LengthsOk c ∧
              fullArenaClauseRefs s2 = fullArenaClauseRefs s ∧
              (∀ r ∈ fullArenaClauseRefs s, fullArenaClauseSize s2 r = fullArenaClauseSize s r ∧
                fullArenaClauseGarb s2 r = fullArenaClauseGarb s r ∧
                fullArenaClauseLits s2 r = fullArenaClauseLits s r) ∧
              (∀ k < fullArenaClauseSize s rsn.toNat,
                arena2[rsn.toNat + 3 + k]? = s.core.arena[rsn.toNat + 3 + k]?) ∧
              (FullMem c s2 ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) m2) ?_ ?_
          · rintro _ ⟨⟩ m2 ⟨arena2, hw2, hlen2, hrefs2, hcl2, har2_eq, hm2⟩
            exact hJred (_, ()) m2 ⟨arena2, s1.scratch, ext1, hext1, (fun h0 => (hwb1 h0).2),
              hw2, ⟨hlen2, hl1.scratch_ok⟩, hms1.extPres, hms1.ws1, hms1.ws2,
              hms1.ant_sz, hms1.res_sz, hrefs2, hcl2, har2_eq, hm2⟩
          · intro Ju hJu
            have hrsn_cap : rsn.toNat < c.arena_cap := by rw [← har_len]; omega
            dsimp only [s0] at hw0 hlen0 hrefs0 hcl0 hc1
            suffices hdone : ∀ (ar2 : List (BitVec 32)) (m2 : Mem 64),
                (ar2 = s1.core.arena ∨
                  ar2 = s1.core.arena.set (rsn.setWidth 64).toNat
                    ((hdr1 &&& 134217727#32) ||| 4160749568#32)) →
                (FullMem c { s1 with core := { s1.core with arena := ar2 } } ⋆
                  (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) m2 →
                Ju () m2 by
              clear hJu hLit hRec hQ hwork hw htl_cv htc_fit hrsn_ref hret_false_same
                hm hm0 hmf hms1 hwb1 hext1 hl1 hm1 hw0 hlen0 hrefs0 hcl0 har0_eq hget0 hc1
                s0 har0_len arena0
              c0_hsteps_nogrp
              · exact hdone _ _ (Or.inr rfl) (by assumption)
              · exact hdone s1.core.arena m1 (Or.inl rfl) hm1f
            rintro ar2 m2 (rfl | rfl) hm2
            · have hs1_eq : { core := { s.core with arena := arena0 }, scratch := s1.scratch } =
                  s1 := by cases s1; dsimp only at hc1; rw [hc1]
              exact hJu () m2 ⟨arena0, hw0, hlen0.core_ok, hrefs0, hcl0, har0_eq, by rwa [hs1_eq]⟩
            · have hrsn1_lt : rsn.toNat < arena0.length := by rw [har0_len]; omega
              have href0c : rsn.toNat ∈ fullArenaClauseRefsCore
                  { s.core with arena := arena0 } := by
                change rsn.toNat ∈ fullArenaClauseRefs
                  { s with core := { s.core with arena := arena0 } }
                rw [hrefs0]; exact href
              have hbum := m6o_hdrBitsUpdate_cut hlen0.core_ok hw0 href0c
                (fun x => (x &&& 0x07FFFFFF#32) ||| (31#32 <<< 27))
                s.core.arena_garbage s.core.num_irred s.core.num_redundant
                (FullAnalyzeTactics.bv32_mask_usage_garb _ 31#32)
                (FullAnalyzeTactics.bv32_mask_usage_shrk _ 31#32)
              have hhdr0_eq : hdr1 =
                  fullArenaHdrCore { s.core with arena := arena0 } rsn.toNat := by
                unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem hrsn1_lt] at hget0
                rw [List.getElem?_eq_getElem hrsn1_lt, Option.getD_some]
                exact (Option.some.inj hget0).symm
              let arena2 := arena0.set rsn.toNat ((fullArenaHdrCore
                { s.core with arena := arena0 } rsn.toNat &&& 0x07FFFFFF#32) ||| (31#32 <<< 27))
              have har_u_eq : s1.core.arena.set (rsn.setWidth 64).toNat
                  ((hdr1 &&& 134217727#32) ||| 4160749568#32) = arena2 := by
                rw [hc1, bv_c0_zext32_64, hhdr0_eq]; rfl
              refine hJu () _ ⟨arena2, hbum.1, { hlen0.core_ok with
                  arena_len_arr := (by dsimp only [arena2]; rw [List.length_set, har0_len]) },
                hbum.2.1.trans hrefs0, fun r hr => ?_, fun k hk => ?_, ?_⟩
              · have hr0 : r ∈ fullArenaClauseRefsCore { s.core with arena := arena0 } := by
                  change r ∈ fullArenaClauseRefs { s with core := { s.core with arena := arena0 } }
                  rwa [hrefs0]
                obtain ⟨a, b, d⟩ := hbum.2.2 r hr0
                exact ⟨a.trans (hcl0 r hr).1, b.trans (hcl0 r hr).2.1, d.trans (hcl0 r hr).2.2⟩
              · rw [List.getElem?_set_ne (by omega)]; exact har0_eq k hk
              · have hs2_eq : ({ core := { s.core with arena := arena2 }, scratch := s1.scratch } :
                    FullState) = { s1 with core := { s1.core with arena := (s1.core.arena.set
                    (rsn.setWidth 64).toNat ((hdr1 &&& 134217727#32) ||| 4160749568#32)) } } := by
                  rw [har_u_eq]; cases s1; dsimp only at hc1 ⊢; rw [hc1]
                rw [hs2_eq]; exact hm2
        · intro Jg hJg
          clear hLit hRec hQ hwork htl_cv htc_fit hrsn_ref hret_false_same hm hcfg hext hmax32
            hcv_le hcur32 hne hlarge
          have hrsn_get : s.core.arena[rsn.toNat]? = some (s.core.arena[(rsn.setWidth 64).toNat]'
              (by rw [bv_c0_zext32_64]; exact hrsn_lt)) := by
            simp only [bv_c0_zext32_64]; exact List.getElem?_eq_getElem hrsn_lt
          have hg_lt : (fullArenaHdrCore s.core rsn.toNat &&& 0x7FFFF#32).toNat < 2 ^ 19 :=
            Nat.lt_of_le_of_lt (bv32_and_le_right _ _) (by decide)
          c0_hsteps_nogrp
          · have hgl_z : ((fullArenaHdrCore s.core rsn.toNat &&& 0x7FFFF#32).setWidth 64).toNat =
                (fullArenaHdrCore s.core rsn.toNat &&& 0x7FFFF#32).toNat := by
              rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans hg_lt (by decide))]
            let limP (p : Tup Val [i64]) (ml : Mem 64) :=
              ml = m ∧ p.1.toNat < (fullArenaHdrCore s.core rsn.toNat &&& 0x7FFFF#32).toNat
            refine wp_join_group (ts := [i64]) limP ?_ ?_
            · rintro _ ⟨lim0, ⟨⟩⟩ m0 ⟨hm0, hlim0⟩; cases hm0
              refine wp_join_group (ts := [i64]) limP ?_ ?_
              · rintro _ ⟨lim, ⟨⟩⟩ m1 ⟨hm1, hlim⟩; cases hm1; c0_hsteps_nogrp
                have hrsn_z_lt : (rsn.setWidth 64).toNat < s.core.arena.length := by
                  rw [bv_c0_zext32_64]; exact hrsn_lt
                exact m6o_rsn_glue_lo rfl rfl rfl hlen hw href hrsn_lt hrsn_z_lt
                  (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_trans hbd3 (har_len ▸ har_le)))
                  hsz_idx rfl rfl rfl hsz_get hrsn_get hmf (Nat.lt_trans hlim hg_lt) hJg
              · intro Jlim2 hJlim2; c0_hsteps_nogrp
                · exact hJlim2 (32#64, ()) m
                    ⟨rfl, Nat.lt_trans (BitVec.lt_def.mp (by assumption : 32#64 < lim0)) hlim0⟩
                · exact hJlim2 (lim0, ()) m ⟨rfl, hlim0⟩
            · intro Jlim hJlim
              have hhdr_z : s.core.arena[(rsn.setWidth 64).toNat]'(by
                  rw [bv_c0_zext32_64]; exact hrsn_lt) = fullArenaHdrCore s.core rsn.toNat := by
                rw [FullAnalyzeTactics.getElem_eq_of_idx (hj := hrsn_lt) (bv_c0_zext32_64 rsn),
                  hhdr_get]
              c0_hsteps_nogrp
              have hgt1 : 1 < (fullArenaHdrCore s.core rsn.toNat &&& 0x7FFFF#32).toNat := by
                simpa only [hhdr_get] using
                  (by assumption : 1 < (s.core.arena[rsn.toNat] &&& 524287#32).toNat)
              all_goals refine hJlim _ m ⟨rfl, ?_⟩
              · dsimp only
                have htc : s.scratch.tier2.toNat < (2 ^ 64 - 1 +
                    (fullArenaHdrCore s.core rsn.toNat &&& 0x7FFFF#32).toNat) % 2 ^ 64 := by
                  simpa only [hhdr_get] using (by assumption : s.scratch.tier2.toNat <
                    (2 ^ 64 - 1 + (s.core.arena[rsn.toNat] &&& 524287#32).toNat) % 2 ^ 64)
                omega
              · dsimp only
                have hgt1' : 1 < (fullArenaHdrCore s.core rsn.toNat &&& 0x7FFFF#32).toNat := by
                  simpa only [hhdr_get] using
                    (by assumption : 1 < (s.core.arena[rsn.toNat] &&& 524287#32).toNat)
                have hle1 : (1#64 : BitVec 64) ≤
                    (fullArenaHdrCore s.core rsn.toNat &&& 0x7FFFF#32).setWidth 64 := by
                  refine BitVec.le_def.mpr ?_
                  rw [hgl_z]; have h1n : (1#64 : BitVec 64).toNat = 1 := rfl; omega
                rw [hhdr_z, show (524287 : BitVec 32) = 0x7FFFF#32 from rfl,
                  show (1 : BitVec 64) = 1#64 from rfl, BitVec.toNat_sub_of_le hle1, hgl_z]
                have h1n : (1#64 : BitVec 64).toNat = 1 := rfl; omega
          · exact hJg (_, _, ()) m ⟨s.core.arena, hrsn_get, hw, hlen, rfl,
              fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ _ => rfl, hmf⟩
      · exact hJred (_, ()) m ⟨s.core.arena, s.scratch, ext, hext,
          fun _ => M6ExtW2bPres.refl ext, hw, hlen, fullExtScratchPres_refl s,
          rfl, rfl, rfl, rfl, rfl, fun _ _ => ⟨rfl, rfl, rfl⟩, fun _ _ => rfl, hmf⟩

/-! ### `full_switch_mode_m6` -/

private def M6oModeSt (c : FullCfg) (ext0 : List (BitVec 64)) (s0 : FullState)
    (R : Mem 64 → Prop) (ext : List (BitVec 64)) (s : FullState) (m : Mem 64) : Prop :=
  s.core = s0.core ∧ s.LengthsOk c ∧ FullProbeScratchPres s0 s ∧ M6HdrExtOk ext ∧
    (M6HdrExtInitOk ext0 → M6HdrExtInitOk ext ∧ M6ExtW2bPres ext0 ext) ∧
    (FullM6HdrMem c ext s ⋆ R) m

private theorem m6oModeSt_step {c : FullCfg} {ext0 ext : List (BitVec 64)} {s0 s s' : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (h : M6oModeSt c ext0 s0 R ext s m)
    (hstep : s'.LengthsOk c ∧ s'.core = s.core ∧ FullProbeScratchPres s s' ∧
      s'.scratch.delayed_len = s.scratch.delayed_len ∧ s'.scratch.delayed = s.scratch.delayed)
    {m' : Mem 64} (hm' : (FullM6HdrMem c ext s' ⋆ R) m') : M6oModeSt c ext0 s0 R ext s' m' :=
  ⟨hstep.2.1.trans h.1, hstep.1, fullProbeScratchPres_trans h.2.2.1 hstep.2.2.1,
    h.2.2.2.1, h.2.2.2.2.1, hm'⟩

private theorem m6oModeSt_wm {c : FullCfg} {ext0 ext ext1 ext2 ext3 : List (BitVec 64)}
    {s0 s s2 s3 : FullState} {R : Mem 64 → Prop} {m m3 : Mem 64}
    (h : M6oModeSt c ext0 s0 R ext s m)
    (_hi1 : M6HdrExtInitOk ext1) (heq1 : M6HdrExtInitOk ext → ext1 = ext)
    (hc2 : s2.core = s.core) (hp2 : M6HdrScratchPres s s2)
    (hwb2 : M6HdrExtInitOk ext1 → M6HdrExtInitOk ext2 ∧ M6ExtW2bPres ext1 ext2)
    (hc3 : s3.core = s2.core) (hl3 : s3.LengthsOk c) (hp3 : M6HdrScratchPres s2 s3)
    (hext3 : M6HdrExtOk ext3)
    (hwb3 : M6HdrExtInitOk ext2 → M6HdrExtInitOk ext3 ∧ M6ExtW2bPres ext2 ext3)
    (hm3 : (FullM6HdrMem c ext3 s3 ⋆ R) m3) : M6oModeSt c ext0 s0 R ext3 s3 m3 := by
  refine ⟨hc3.trans (hc2.trans h.1), hl3,
    fullProbeScratchPres_trans h.2.2.1 (fullProbeScratchPres_trans hp2.probePres hp3.probePres),
    hext3, fun h0 => ?_, hm3⟩
  obtain ⟨hi0, hwb0⟩ := h.2.2.2.2.1 h0
  have h1 := heq1 hi0
  obtain ⟨hi2, hwb12⟩ := hwb2 (h1 ▸ hi0)
  obtain ⟨hi3, hwb23⟩ := hwb3 hi2
  exact ⟨hi3, hwb0.trans ((h1 ▸ hwb12).trans hwb23)⟩

private theorem m6o_upd_heap_pos_step {c : FullCfg} {s : FullState} (hs : s.LengthsOk c)
    {hp' ps' : List (BitVec 32)} (hhp : hp'.length = s.scratch.heap.length)
    (hps : ps'.length = s.scratch.pos.length) :
    let s' : FullState := { s with scratch := { s.scratch with heap := hp', pos := ps' } }
    s'.LengthsOk c ∧ s'.core = s.core ∧ FullProbeScratchPres s s' ∧
      s'.scratch.delayed_len = s.scratch.delayed_len ∧ s'.scratch.delayed = s.scratch.delayed :=
  ⟨⟨hs.1, fullScratch_lengthsOk_of_arr_len hs.2 rfl rfl rfl rfl rfl hhp hps rfl rfl rfl rfl rfl
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩,
    rfl, ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩

private theorem m6o_upd_mode_qsearch_step {c : FullCfg} {s : FullState} (hs : s.LengthsOk c)
    (mcl mst qi qs : BitVec 64) :
    let s' : FullState :=
      { s with scratch :=
        { s.scratch with
          mode_confl_lim := mcl, mode_saved_ticks := mst,
          q_search_idx := qi, q_search_stamp := qs } }
    s'.LengthsOk c ∧ s'.core = s.core ∧ FullProbeScratchPres s s' ∧
      s'.scratch.delayed_len = s.scratch.delayed_len ∧ s'.scratch.delayed = s.scratch.delayed :=
  ⟨⟨hs.1, fullScratch_lengthsOk_of_arr_len hs.2 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩,
    rfl, ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩

theorem full_switch_mode_m6_wp (Γ : Env)
    (hReady : ∀ a m Q X, m6HdrExtReadySpec a m Q X →
      Γ "m6_hdr_ext_ready" [i64] [.bool] a m Q X)
    (hGetWm : ∀ a m Q X, m6HdrW2aSpec [i64] [i64] a m Q X →
      Γ "m6_hdr_get_watermark" [i64, i64] [i64] a m Q X)
    (hSetWm : ∀ a m Q X, m6HdrW2aSpec [i64, i64] [] a m Q X →
      Γ "m6_hdr_set_watermark" [i64, i64, i64] [] a m Q X)
    (hDown : ∀ a m Q X, fullHeapDownSpec a m Q X →
      Γ "full_heap_down" [i64, i32] [] a m Q X)
    (hLog : ∀ a m Q X, FullM5Sched.m5Log10Q16Spec a m Q X →
      Γ "full_log10_q16" [i64] [i64] a m Q X)
    (hEma : ∀ a m Q X, m6EmaSwapSpec a m Q X →
      Γ "full_ema_swap_m6" [i64, i64, i64] [] a m Q X)
    (hIlog : ∀ a m Q X, fullIlog10Spec a m Q X →
      Γ "full_ilog10" [i64] [i64] a m Q X) :
    ∀ a m Q X, m6SwitchModeSpec a m Q X →
      Func.wp Γ full_switch_mode_m6_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X hs
  rcases m6SwitchModeSpec_elim hs with ⟨c, ext, s, R, rfl, hcfg, hext, hlen, hm, hQ⟩
  have hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  unfold dimacsBound at hmax
  have hcv_le := hlen.core_ok.cur_vars_le
  unfold Func.wp full_switch_mode_m6_body
  refine wp_m6Hdr_focus_frame hm fun hmf => ?_
  c0_hsteps_nogrp
  refine wp_join_group
      (fun (_ : Tup Val [i64, i64]) m' => ∃ ext1 s1, M6oModeSt c ext s R ext1 s1 m') ?_ ?_
  · rintro J ⟨old_m, new_m, ⟨⟩⟩ m1 ⟨ext1, s1, hst1⟩
    have hms1 := hst1.2.2.2.2.2
    refine wp_m6Hdr_focus_frame hms1 fun hms1f => ?_
    have hstep1 := fullState_upd_mode_step hst1.2.1 s1.scratch.stable
      (s1.scratch.switched + 1#64) (s1.scratch.mode_count + 1#64)
      s1.scratch.mode_confl_lim s1.scratch.mode_tick_lim s1.scratch.mode_saved_ticks
    c0_hsteps_nogrp
    have hst1' := m6oModeSt_step hst1 hstep1 (fullM6HdrMem_unfocus (by assumption))
    refine m6o_call_emaSwap rfl (fun _ _ _ _ h => hEma _ _ _ _ h) hcfg hst1'.2.2.2.1 hst1'.2.1
      hst1'.2.2.2.2.2 fun s2 m2 hc2 hl2 hp2 hm2 => ?_
    have hst2 : M6oModeSt c ext s R ext1 s2 m2 :=
      ⟨hc2.trans hst1'.1, hl2, fullProbeScratchPres_trans hst1'.2.2.1 hp2,
        hst1'.2.2.2.1, hst1'.2.2.2.2.1, hm2⟩
    refine wp_m6Hdr_focus_frame hm2 fun hm2f => ?_
    c0_hsteps_nogrp
    refine wp_unroll_group fun Jret hJret => ?_
    c0_hsteps_nogrp
    · refine wp_join_group (fun (_ : Tup Val [i64]) m3 => m3 = m2)
        (fun _ (delta, ()) m3 hm3 => ?_) ?_
      · subst hm3; c0_hsteps_nogrp
        try (apply hJret; rw [Blocks.get_here]; c0_hsteps_nogrp)
        have hsr := fullState_upd_restarts_step hst2.2.1 s2.scratch.restarts
          (s2.scratch.conflicts + delta)
        have hm3f := fullM6HdrMem_unfocus (by assumption)
        exact hQ ext1 _ _ (hsr.2.1.trans hst2.1) hsr.1
          (fullProbeScratchPres_trans hst2.2.2.1 hsr.2.2.1) hst2.2.2.2.1 hst2.2.2.2.2.1 hm3f
      · intro Jd hJd; c0_hsteps_nogrp
        · refine wp_join_group (fun (_ : Tup Val [i64]) m3 => m3 = m2)
            (fun _ (rc, ()) m3 hm3 => ?_) ?_
          · subst hm3; c0_hsteps_nogrp; c0_call hIlog; intro d10 _ _; c0_hsteps
            · exact hJd (d10 - 1#64, ()) _ rfl
            · exact hJd (1#64, ()) _ rfl
          · intro Jrc hJrc; c0_hsteps_nogrp <;> exact hJrc (_, ()) _ rfl
        · exact hJd (1#64, ()) _ rfl
    · try (apply hJret; rw [Blocks.get_here]; c0_hsteps_nogrp)
      exact hQ ext1 s2 m2 hst2.1 hst2.2.1 hst2.2.2.1 hst2.2.2.2.1 hst2.2.2.2.2.1 hm2
  · intro J hJ; c0_hsteps_nogrp
    · exact hQ ext s m rfl hlen (fullProbeScratchPres_refl s) hext
        (fun h => ⟨h, M6ExtW2bPres.refl ext⟩) hm
    · have hstep0 := fullState_upd_mode_step hlen 1#64 s.scratch.switched s.scratch.mode_count
        s.scratch.mode_confl_lim s.scratch.mode_tick_lim s.scratch.mode_saved_ticks
      have hst0 : M6oModeSt c ext s R ext _ m :=
        ⟨hstep0.2.1, hstep0.1, hstep0.2.2.1, hext,
          fun h => ⟨h, M6ExtW2bPres.refl ext⟩, fullM6HdrMem_unfocus hm⟩
      refine wp_join_group (fun (_ : Tup Val [i64]) m1 => m1 = m)
        (fun _ (dticks, ()) m1 hm1 => ?_) ?_
      · subst hm1
        refine wp_join_state0 (α := FullState × List (BitVec 64))
          (fun p m2 => M6oModeSt c ext s R p.2 p.1 m2) ?_ ?_
        · rintro Jw ⟨s1, ext1⟩ m2 hst1
          refine wp_m6Hdr_focus_frame hst1.2.2.2.2.2 fun hm2f => ?_
          c0_hsteps_nogrp
          have hstep1a := fullState_upd_mode_step hst1.2.1 s1.scratch.stable s1.scratch.switched
            s1.scratch.mode_count s1.scratch.mode_confl_lim (s1.scratch.search_ticks + dticks)
            s1.scratch.search_ticks
          have hst1a := m6oModeSt_step hst1 hstep1a (fullM6HdrMem_unfocus (by assumption))
          let sc_lim :=
            { s1.scratch with
              mode_tick_lim := s1.scratch.search_ticks + dticks
              mode_saved_ticks := s1.scratch.search_ticks }
          refine wp_join_group (fun (_ : Tup Val [i64]) m3 =>
              (FullM6HdrMem c ext1 { s1 with scratch := sc_lim } ⋆ R) m3)
            (fun _ (rp, ()) m3 hm3 => ?_) ?_
          · refine wp_m6Hdr_focus_frame hm3 fun hm3f' => ?_
            dsimp only at *; c0_hsteps_nogrp
            have hstep1b := fullState_upd_rel_step hst1a.2.1 s1.scratch.rel_period
              s1.scratch.rel_limit rp 1#64 1#64 0#64
            have hst1b := m6oModeSt_step hst1a hstep1b (fullM6HdrMem_unfocus (by assumption))
            refine wp_m6Hdr_focus_frame hst1b.2.2.2.2.2 fun hm3f => ?_; c0_hsteps_nogrp
            refine wp_loop_inv (fun (n, v, ()) mL => n.toNat ≤ v.toNat ∧ v.toNat ≤ s.core.cur_vars ∧
                ∃ sL, sL.core = s.core ∧ sL.LengthsOk c ∧ FullProbeScratchPres s sL ∧
                  (FullMem c sL ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) mL)
              (fun (_, v, ()) _ => s.core.cur_vars - v.toNat)
              (fun Jl hJl => by
                c0_hsteps_nogrp
                exact hJl (0#64, 0#64, ()) _ ⟨by simp, by simp, _, hst1b.1, hst1b.2.1,
                  hst1b.2.2.1, hm3f⟩)
              (fun Jl (n, v, ()) mL ⟨hnv, hvcv, sL, hcsL, hlL, hpL, hmL⟩ hJl => ?_)
            · have hflL := hlL.core_ok.flags_len; have hvlL := hlL.core_ok.vals_len
              have hhlL := hlL.scratch_ok.heap_len_arr; have hplL := hlL.scratch_ok.pos_len
              c0_hsteps_nogrp
              · have hv_lt : v.toNat < s.core.cur_vars := by
                  have hlt : v.toNat < s1.core.cur_vars % 2 ^ 64 := by assumption
                  rw [hst1.1, Nat.mod_eq_of_lt (by omega)] at hlt; exact hlt
                have hv1 : (v + 1#64).toNat = v.toNat + 1 := by bv_omega
                have hv_fl : v.toNat < sL.core.flags.length := by rw [hflL]; omega
                have hv_pos : v.toNat < sL.scratch.pos.length := by rw [hplL]; omega
                refine wp_join_state1 (α := FullState × BitVec 64) (fun p => p.2)
                  (fun p m' => p.2.toNat ≤ v.toNat + 1 ∧ p.1.core = s.core ∧
                    p.1.LengthsOk c ∧ FullProbeScratchPres s p.1 ∧
                    (FullMem c p.1 ⋆ (m6ExtMem (m6ExtAddr c.hdr) ext1 ⋆ R)) m') ?_ ?_
                · rintro Js ⟨s2, n'⟩ m2 ⟨hn'le, hcs2, hl2, hp2, hm2⟩
                  c0_hsteps_nogrp
                  exact hJl (n', v + 1#64, ()) m2 (by dsimp only; rw [hv1]; omega)
                    ⟨by rw [hv1]; omega, by rw [hv1]; omega, s2, hcs2, hl2, hp2, hm2⟩
                · intro Js hJs
                  have hpos_upd : (let s2 := { sL with scratch :=
                      { sL.scratch with pos := sL.scratch.pos.set v.toNat 0xFFFFFFFF#32 } };
                      s2.LengthsOk c ∧ s2.core = sL.core ∧ FullProbeScratchPres sL s2) :=
                    let hs := m6o_upd_heap_pos_step hlL rfl (by simp [hplL])
                    ⟨hs.1, hs.2.1, hs.2.2.1⟩
                  refine wp_join_group (fun (_ : Tup Val []) mE => mE = mL) (fun _ _ mE hmE => by
                      cases hmE; c0_hsteps_nogrp; exact hJs (_, n) _ ⟨by dsimp only; omega,
                        hpos_upd.2.1.trans hcsL, hpos_upd.1,
                        fullProbeScratchPres_trans hpL hpos_upd.2.2,
                        by simpa using (by assumption)⟩)
                    (fun JE hJE => by
                      have hv2_lt : (v <<< (1 : Nat)).toNat < sL.core.vals.length := by
                        rw [hvlL, BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
                      have hn_lt : n.toNat < sL.scratch.heap.length := by rw [hhlL]; omega
                      have hn1 : (n + 1#64).toNat = n.toNat + 1 := by bv_omega
                      c0_hsteps_nogrp
                      · have hs_hp := m6o_upd_heap_pos_step hlL
                          (hp' := sL.scratch.heap.set n.toNat (v.setWidth 32))
                          (ps' := sL.scratch.pos.set v.toNat (n.setWidth 32))
                          (by simp [hhlL]) (by simp [hplL])
                        exact hJs (_, n + 1#64) _ ⟨by dsimp only; rw [hn1]; omega,
                          hs_hp.2.1.trans hcsL, hs_hp.1, fullProbeScratchPres_trans hpL hs_hp.2.2.1,
                          by simpa using (by assumption)⟩
                      all_goals exact hJE () mL rfl)
              · c0_hsteps_nogrp
                refine wp_loop_inv (fun (sp, ()) mH => sp.toNat ≤ c.max_vars ∧ ∃ sH,
                    sH.core = s.core ∧ sH.LengthsOk c ∧ FullProbeScratchPres s sH ∧
                    (FullM6HdrMem c ext1 sH ⋆ R) mH) (fun (sp, ()) _ => sp.toNat)
                  (fun Jh hJh => by
                    c0_hsteps_nogrp
                    have hhl_step : (let s2 := { sL with scratch :=
                        { sL.scratch with heap_len := n.toNat } };
                        s2.LengthsOk c ∧ s2.core = sL.core ∧ FullProbeScratchPres sL s2) :=
                      ⟨⟨hlL.1, fullScratch_lengthsOk_of_arr_len hlL.2 rfl rfl rfl rfl rfl rfl
                          rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl⟩,
                        rfl, ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
                    exact hJh (n >>> (1 : Nat), ()) _ ⟨by
                      rw [BitVec.toNat_ushiftRight]; simp [Nat.shiftRight_eq_div_pow]; omega,
                      _, hhl_step.2.1.trans hcsL, hhl_step.1,
                      fullProbeScratchPres_trans hpL hhl_step.2.2,
                      fullM6HdrMem_unfocus (by assumption)⟩)
                  (fun Jh (sp, ()) mH ⟨hsple, sH, hcsH, hlH, hpH, hmH⟩ hJh => ?_)
                · refine wp_m6Hdr_focus_frame hmH fun hmHf => ?_
                  have hhlH := hlH.scratch_ok.heap_len_arr; c0_hsteps_nogrp
                  · have hsp_pos : 0 < sp.toNat := BitVec.lt_def.mp (by assumption : 0#64 < sp)
                    have hsm1 : (sp - 1#64).toNat < sp.toNat := by bv_omega
                    have hsm1_lt : (sp - 1#64).toNat < sH.scratch.heap.length := by rw [hhlH]; omega
                    c0_hsteps_nogrp
                    refine m6o_call_heapDown rfl (fun _ _ _ _ h => hDown _ _ _ _ h) hcfg
                      hst1b.2.2.2.1 hlH (fullM6HdrMem_unfocus (by assumption))
                      fun s4 m4 hc4 hl4 _ hp4 hm4 => hJh (sp - 1#64, ()) m4 (by dsimp only; omega)
                        ⟨by omega, s4, hc4.trans hcsH, hl4, fullProbeScratchPres_trans hpH hp4, hm4⟩
                  · exact hJ (0#64, 1#64, ()) mH ⟨ext1, sH,
                      ⟨hcsH, hlH, hpH, hst1b.2.2.2.1, hst1b.2.2.2.2.1, hmH⟩⟩
          · intro Jrp hJrp; c0_hsteps_nogrp <;>
              exact hJrp (_, ()) _ (fullM6HdrMem_unfocus (by assumption))
        · intro Jw hJw; c0_hsteps_nogrp; c0_call hReady
          refine m6HdrExtReadySpec_of hcfg hst0.2.2.2.1 hst0.2.1 hst0.2.2.2.2.2
            fun ext1 m1 hi1 heq1 hm1 => ?_; c0_hsteps_nogrp
          · refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hGetWm _ _ _ _ h) hcfg hi1.toOk
              hst0.2.1 hm1 fun ⟨_, ⟨⟩⟩ ext2 s2 m2 hc2 hlen2 hms2 hext2 hwb2 hm2 => ?_
            c0_hsteps_nogrp
            refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hSetWm _ _ _ _ h) hcfg hext2 hlen2 hm2
              fun _ ext3 s3 m3 hc3 hlen3 hms3 hext3 hwb3 hm3 => hJw (_, _) _
                (m6oModeSt_wm hst0 hi1 heq1 hc2 hms2 hwb2 hc3 hlen3 hms3 hext3 hwb3 hm3)
          · cases hc
      · intro Jdt hJdt; c0_hsteps_nogrp <;> exact hJdt _ m rfl
    · exact hQ ext s m rfl hlen (fullProbeScratchPres_refl s) hext
        (fun h => ⟨h, M6ExtW2bPres.refl ext⟩) hm
    · have hstep0 := fullState_upd_mode_step hlen 0#64 s.scratch.switched s.scratch.mode_count
        s.scratch.mode_confl_lim s.scratch.mode_tick_lim s.scratch.mode_saved_ticks
      have hst0 : M6oModeSt c ext s R ext _ m := ⟨hstep0.2.1, hstep0.1, hstep0.2.2.1, hext,
        fun h => ⟨h, M6ExtW2bPres.refl ext⟩, fullM6HdrMem_unfocus hm⟩
      refine wp_join_group (fun (_ : Tup Val [i64]) m1 => m1 = m)
        (fun _ (dticks, ()) m1 hm1 => ?_) ?_
      · subst hm1
        refine wp_join_state0 (α := FullState × List (BitVec 64))
          (fun p m2 => M6oModeSt c ext s R p.2 p.1 m2) ?_ ?_
        · rintro Jw ⟨s1, ext1⟩ m2 hst1
          refine wp_m6Hdr_focus_frame hst1.2.2.2.2.2 fun hm2f => ?_; c0_hsteps_nogrp
          refine wp_join_group (fun (_ : Tup Val [i64]) m3 => m3 = m2)
            (fun _ (cc, ()) m3 hm3 => ?_) ?_
          · cases hm3; c0_hsteps_nogrp; c0_call hLog; intro q _ _; c0_hsteps_nogrp
            refine wp_join_group (fun (_ : Tup Val [i64]) m4 => m4 = m2)
              (fun _ (scaled, ()) m4 hm4 => ?_) ?_
            · cases hm4
              have hqsl := hst1.2.1.scratch_ok.q_stamp_len; c0_hsteps_nogrp
              refine wp_join_group (fun (_ : Tup Val []) m5 => ∃ qs' : BitVec 64,
                  M6oModeSt c ext s R ext1 { s1 with scratch := { s1.scratch with
                    mode_confl_lim := s1.scratch.conflicts + scaled, mode_saved_ticks :=
                    s1.scratch.search_ticks, q_search_idx := s1.scratch.q_last,
                    q_search_stamp := qs' } } m5)
                (fun _ _ m5 ⟨qs', hst5⟩ => by
                  refine wp_m6Hdr_focus_frame hst5.2.2.2.2.2 fun hm5f => ?_
                  c0_hsteps_nogrp; exact hJ (1#64, 0#64, ()) _ ⟨ext1, _, hst5⟩)
                (fun J5 hJ5 => by
                  c0_hsteps_nogrp
                  · have hlt : s1.scratch.q_last.toNat < s1.core.cur_vars % 2 ^ 64 := by assumption
                    have hqs_lt : s1.scratch.q_last.toNat < s1.scratch.q_stamp.length := by
                      rw [hst1.1, Nat.mod_eq_of_lt (by omega)] at hlt; rw [hqsl]; omega
                    c0_hsteps_nogrp
                    have hs1 := m6o_upd_mode_qsearch_step hst1.2.1 (s1.scratch.conflicts + scaled)
                      s1.scratch.search_ticks s1.scratch.q_last
                      (BitVec.setWidth 64 (s1.scratch.q_stamp[s1.scratch.q_last.toNat]'hqs_lt))
                    exact hJ5 () _ ⟨_, m6oModeSt_step hst1 hs1 (fullM6HdrMem_unfocus ‹_›)⟩
                  · have hs1 := m6o_upd_mode_qsearch_step hst1.2.1 (s1.scratch.conflicts + scaled)
                      s1.scratch.search_ticks s1.scratch.q_last s1.scratch.q_search_stamp
                    exact hJ5 () _ ⟨_, m6oModeSt_step hst1 hs1 (fullM6HdrMem_unfocus ‹_›)⟩)
            · intro Jsc hJsc; c0_hsteps_nogrp
              · exact hJsc _ m2 rfl
              · refine wp_join_group (fun (_ : Tup Val [i64]) m4 => m4 = m2)
                  (fun _ (clim, ()) m4 hm4 => ?_) ?_
                · cases hm4; c0_hsteps_nogrp; exact hJsc _ m2 rfl
                · intro Jcl hJcl; c0_hsteps_nogrp <;> exact hJcl _ m2 rfl
          · intro Jcc hJcc; c0_hsteps_nogrp <;> exact hJcc _ m2 rfl
        · intro Jw hJw; c0_hsteps_nogrp; c0_call hReady
          refine m6HdrExtReadySpec_of hcfg hst0.2.2.2.1 hst0.2.1 hst0.2.2.2.2.2
            fun ext1 m1 hi1 heq1 hm1 => ?_; c0_hsteps_nogrp
          · refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hGetWm _ _ _ _ h) hcfg hi1.toOk
              hst0.2.1 hm1 fun ⟨st, ⟨⟩⟩ ext2 s2 m2 hc2 hlen2 hms2 hext2 hwb2 hm2 => ?_
            c0_hsteps_nogrp
            refine m6Hdr_call_m6HdrW2a rfl (fun _ _ h => hSetWm _ _ _ _ h) hcfg hext2 hlen2 hm2
              fun _ ext3 s3 m3 hc3 hlen3 hms3 hext3 hwb3 hm3 =>
              hJw (_, _) _
                (m6oModeSt_wm hst0 hi1 heq1 hc2 hms2 hwb2 hc3 hlen3 hms3 hext3 hwb3 hm3)
          · cases hc
      · intro Jdt hJdt; c0_hsteps_nogrp <;> exact hJdt _ m rfl

end AnalyzeCoreAndSwitchMode
end LeanQbe.T.Examples.Kissat.FullM6Orch
