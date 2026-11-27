/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S4EVSIDSReorder
public import LeanQbe.T.Examples.Kissat.FullFidelityTumbleSpec
public import LeanQbe.T.Examples.Kissat.FullM6HdrProof0
public import LeanQbe.T.Examples.Kissat.FullM6BcpS15Proof1
public import LeanQbe.T.Examples.Kissat.FullLuckyLemmas
import LeanQbe.T.Examples.Kissat.FullLuckyLemmas1
import LeanQbe.T.Examples.Kissat.FullLuckyLemmas2
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 S4-A Proofs — `full_lucky_scan` (`step13LuckyScanM6Spec`)

UNSAT-only, callee-parametric `Func.wp` proof (`public section`, `0` `@[expose]` on theorems,
`0` `import all`, `XPost`-polymorphic) for Step-13 `full_lucky_scan` lifted over `FullM6HdrMem`
(`step13LuckyScanM6Spec`), calling `full_analyze_m6_hdr` (`m6HdrAnalyzeSpec`) and Step-13
`FullM6HdrMem`-threaded `full_propagate` (`step13PropagateSpec`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S4

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullM6BcpS15
open LeanQbe.T.Examples.Kissat.FullFidelityTumble
open Full.FullLuckyHelpers
open scoped Full.FullArenaTactics Full.FullLuckyTactics
open Kraken.Bedrock2.Test

/-! ## 1. Step-13 `FullM6HdrMem`-Threaded `full_propagate` & `full_lucky_scan` Specs -/

/-- Step-13 `FullM6HdrMem`-threaded `full_propagate` spec (Option A lift of `fullBcpS15Spec`). -/
def step13PropagateSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (ext : List (BitVec 64))
    (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
    FullWitnessInv c F0 F_cur s.core ∧ s.core.dense_mode = 0#64 ∧
    (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk' wlen' wu'
      fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m',
      let s' : FullState :=
        { s with
          core :=
            { s.core with
              vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
              trail_pos := tp', trail_end := te', propagated := prop', unassigned := unass',
              unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
              wusable := wu', fuel := fuel', confl_type := ctype', confl_ref := cref',
              confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
          scratch :=
            { s.scratch with
              search_ticks := ticks', wsort := wsort', phases := phases', delayed := delayed' } }
      M6HdrExtOk ext' → s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullTrailExt s.core s'.core → FullArenaPermEq s.core s'.core →
      (c.delayed_cap = 0 → delayed' = s.scratch.delayed) →
      fuel'.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → prop' = te' ∧ (s.core.oom = 0#64 → oom' = 0#64) ∧
        (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧ FullConflictOkW F_cur s') →
      (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
      (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s' = s) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

theorem step13PropagateSpec_monoX {xs : Tup Val [i64]} {m : Mem 64} {Q : Post [i64]}
    {X X' : XPost} (h : step13PropagateSpec xs m Q X) : step13PropagateSpec xs m Q X' := by
  rcases xs with ⟨_, ⟨⟩⟩; exact h

theorem step13PropagateSpec_of {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {ext : List (BitVec 64)} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext) (hlen : s.LengthsOk c)
    (hw : FullWitnessInv c F0 F_cur s.core) (hdm : s.core.dense_mode = 0#64)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ r ext' vals' flags' lvl' rsns' trl' tp' te' prop' unass' unfl' wvec' arena' wstk'
      wlen' wu' fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases' delayed' m',
      let s' : FullState :=
        { s with
          core :=
            { s.core with
              vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
              trail_pos := tp', trail_end := te', propagated := prop', unassigned := unass',
              unflushed := unfl', wvec := wvec', arena := arena', wstk := wstk', wlen := wlen',
              wusable := wu', fuel := fuel', confl_type := ctype', confl_ref := cref',
              confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
          scratch :=
            { s.scratch with
              search_ticks := ticks', wsort := wsort', phases := phases', delayed := delayed' } }
      M6HdrExtOk ext' → s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      FullTrailExt s.core s'.core → FullArenaPermEq s.core s'.core →
      (c.delayed_cap = 0 → delayed' = s.scratch.delayed) →
      fuel'.toNat ≤ s.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 0#64 → prop' = te' ∧ (s.core.oom = 0#64 → oom' = 0#64) ∧
        (s.core.propagated < s.core.trail_end → fuel'.toNat < s.core.fuel.toNat)) →
      (r = 1#64 → fuel'.toNat < s.core.fuel.toNat ∧ oom' = 0#64 ∧ FullConflictOkW F_cur s') →
      (r = 2#64 → oom' ≠ 0#64 ∨ fuel' = 0#64) →
      (s.core.propagated = s.core.trail_end → r = 0#64 ∧ s' = s) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m') :
    step13PropagateSpec (c.hdr, ()) m Q X :=
  ⟨c, F0, F_cur, ext, s, R, rfl, hcfg, hext, hlen, hw, hdm, hm, hQ⟩

/-- Step-13 `FullM6HdrMem`-threaded `full_lucky_scan` spec (lift of `fullLuckyScanSpec`). -/
def step13LuckyScanM6Spec : Spec [i64, .bool, .bool] [i64] := fun (h, _pos, _fwd, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧
    FullSparseInv c F0 s ∧ s.core.cur_level = 0 ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
    ∀ r ext' s' m',
      M6HdrExtOk ext' → s'.LengthsOk c →
      (r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) →
      (r = 0#64 ∨ r = 2#64 → FullSparseInv c F0 s' ∧ s'.core.cur_level = 0) →
      (r = 10#64 → s'.scratch.extend_len ≤ c.extend_cap) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m'

theorem step13LuckyScanM6Spec_monoX {xs : Tup Val [i64, .bool, .bool]} {m : Mem 64}
    {Q : Post [i64]} {X X' : XPost} (h : step13LuckyScanM6Spec xs m Q X) :
    step13LuckyScanM6Spec xs m Q X' := by
  rcases xs with ⟨_, _, _, ⟨⟩⟩; exact h

theorem step13LuckyScanM6Spec_of {c : FullCfg} {F0 : CNF Nat} {ext : List (BitVec 64)}
    {s : FullState} {pos fwd : Bool} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext)
    (hsp : FullSparseInv c F0 s) (hcl0 : s.core.cur_level = 0)
    (hm : (FullM6HdrMem c ext s ⋆ R) m)
    (hQ : ∀ r ext' s' m',
      M6HdrExtOk ext' → s'.LengthsOk c →
      (r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64) →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 20#64 → F0.Unsat) →
      (r = 0#64 ∨ r = 2#64 → FullSparseInv c F0 s' ∧ s'.core.cur_level = 0) →
      (r = 10#64 → s'.scratch.extend_len ≤ c.extend_cap) →
      (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m') :
    step13LuckyScanM6Spec (c.hdr, pos, fwd, ()) m Q X :=
  ⟨c, F0, ext, s, R, rfl, hcfg, hext, hsp, hcl0, hm, hQ⟩

theorem step13LuckyScanM6Spec_elim {h : BitVec 64} {pos fwd : Bool} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (hs : step13LuckyScanM6Spec (h, pos, fwd, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (ext : List (BitVec 64)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧
      FullSparseInv c F0 s ∧ s.core.cur_level = 0 ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ r ext' s' m',
        M6HdrExtOk ext' → s'.LengthsOk c →
        (r = 0#64 ∨ r = 2#64 ∨ r = 10#64 ∨ r = 20#64) →
        s'.core.fuel.toNat ≤ s.core.fuel.toNat →
        (r = 20#64 → F0.Unsat) →
        (r = 0#64 ∨ r = 2#64 → FullSparseInv c F0 s' ∧ s'.core.cur_level = 0) →
        (r = 10#64 → s'.scratch.extend_len ≤ c.extend_cap) →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q (r, ()) m' :=
  hs

/-! ## 2. Private Helpers for `full_lucky_scan` -/

private theorem s13l_bv64_four : (4#64 : BitVec 64) = (4 : BitVec 64) := rfl
private theorem s13l_bv64_144 : (144#64 : BitVec 64) = (144 : BitVec 64) := rfl
private theorem s13l_bv64_160 : (160#64 : BitVec 64) = (160 : BitVec 64) := rfl
private theorem s13l_bv64_168 : (168#64 : BitVec 64) = (168 : BitVec 64) := rfl
private theorem s13l_bv64_768 : (768#64 : BitVec 64) = (768 : BitVec 64) := rfl

private theorem s13_call_assign_prop_decide_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {ext : List (BitVec 64)} {s s_init : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    {lit : BitVec 32} {v : Nat} {k_prop : Tup Val [i64] → Expr Val Cont [i64]}
    (hAssign : ∀ args m Q X, fullAssignSpec args m Q X →
      Γ "full_assign" [i64, i32, i32] [] args m Q X)
    (hProp : ∀ args m Q X, step13PropagateSpec args m Q X →
      Γ "full_propagate" [i64] [i64] args m Q X)
    (hcfg : FullM6HdrCfgOk c) (hext : M6HdrExtOk ext)
    (hsp : FullSparseInv c F0 s) (hfl : s.core.fuel.toNat ≤ s_init.core.fuel.toNat)
    (hv_lt : v < s.core.cur_vars) (hval0 : s.core.vals[2 * v]?.getD 0#8 = 0#8)
    (hlit_v : lit.toNat / 2 = v)
    (hm : (FullMem c { s with core := { s.core with
      cur_level := s.core.cur_level + 1
      frame_trail := s.core.frame_trail.set (s.core.cur_level + 1)
        (BitVec.ofNat 32 s.core.trail_end)
      frame_dec := s.core.frame_dec.set (s.core.cur_level + 1) lit } } ⋆
      (array64 (c.hdr - 2304) ext ⋆ R)) m)
    (hK : ∀ (r : BitVec 64) (F_cur : List (List Nat)) (ext' : List (BitVec 64))
      (s_asn s_p : FullState) (mp : Mem 64),
      M6HdrExtOk ext' → s_p.LengthsOk c → FullSparseInv c F0 s_p →
      FullWitnessInv c F0 F_cur s_p.core →
      s_p.core.cur_level = s.core.cur_level + 1 → s_p.core.cur_vars = s.core.cur_vars →
      s_p.core.fuel.toNat ≤ s_init.core.fuel.toNat → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64) →
      (r = 1#64 → FullConflictOkW F_cur s_p) → FullTrailExt s_asn.core s_p.core →
      s.core.trail_end < s_asn.core.trail_end → s_asn.core.trl[s.core.trail_end]? = some lit →
      s_asn.core.lvl[v]?.getD 0#32 = BitVec.ofNat 32 (s.core.cur_level + 1) →
      (FullMem c s_p ⋆ (array64 (c.hdr - 2304) ext' ⋆ R)) mp →
      wp Γ Q X (k_prop (r, PUnit.unit)) mp) :
    wp Γ Q X (@Expr.call Val Cont [i64] "full_assign" [i64, i32, i32] []
      (Arg.var c.hdr, Arg.var lit, Arg.imm (4294967295 : BitVec 32), PUnit.unit) fun _ =>
      @Expr.call Val Cont [i64] "full_propagate" [i64] [i64]
        (Arg.var c.hdr, PUnit.unit) k_prop) m := by
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcv_le := hsp.1.lengths.core_ok.cur_vars_le
  have hte_le := hsp.1.lengths.core_ok.trail_end_le
  obtain ⟨_, hw0⟩ := hsp.1.witness
  have hcl0 := hw0.cur_level_le
  have hpr0 := lucky_decide_preserves_fullSparseInv hsp hv_lt hval0 hlit_v
    (unas' := 0#64) (unfl' := 0#64)
    (List.length_replicate (n := c.max_vars) (a := (0 : BitVec 32)))
    (List.length_replicate (n := c.max_vars) (a := (0 : BitVec 8)))
  have hte_lt := hpr0.2.2.1
  have hval_lit := hpr0.2.2.2.2
  let ftrl' := s.core.frame_trail.set (s.core.cur_level + 1) (BitVec.ofNat 32 s.core.trail_end)
  let fdec' := s.core.frame_dec.set (s.core.cur_level + 1) lit
  let s_dec : FullState :=
    { s with core := { s.core with
      cur_level := s.core.cur_level + 1, frame_trail := ftrl', frame_dec := fdec' } }
  have hdec_len : s_dec.LengthsOk c :=
    { hsp.1.lengths with core_ok := { hsp.1.lengths.core_ok with
      frame_trail_len := by
        change ftrl'.length = c.max_vars + 1; simp [ftrl', hsp.1.lengths.core_ok.frame_trail_len]
      frame_dec_len := by
        change fdec'.length = c.max_vars + 1; simp [fdec', hsp.1.lengths.core_ok.frame_dec_len] } }
  have hcl_lt32 : s_dec.core.cur_level < 2 ^ 32 := by change s.core.cur_level + 1 < 2 ^ 32; omega
  have hnot_pre : ¬ (s_dec.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ s_dec.core.trail_end ∨
      s_dec.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8) := by
    change ¬ (s.core.cur_vars ≤ lit.toNat / 2 ∨ c.max_vars ≤ s.core.trail_end ∨
      s.core.vals[lit.toNat]?.getD 0#8 ≠ 0#8)
    rw [hlit_v, hval_lit]; simp; omega
  c0_call hAssign
  refine ⟨c, s_dec, array64 (c.hdr - 2304) ext ⋆ R, rfl, hdec_len, hcl_lt32, hm, ?_⟩
  have hcl_ne0 : s_dec.core.cur_level ≠ 0 := by change s.core.cur_level + 1 ≠ 0; omega
  dsimp only [vals, Arg.val]; simp only [hnot_pre, ↓reduceIte, hcl_ne0]
  intro flags' unass' phases' ma hfl_len hph_len hma
  have hpr := lucky_decide_preserves_fullSparseInv hsp hv_lt hval0 hlit_v
    (unas' := unass') (unfl' := s_dec.core.unflushed) hfl_len hph_len
  let s_asn : FullState :=
    { core := { s_dec.core with
        unassigned := unass', unflushed := s_dec.core.unflushed,
        trail_end := s_dec.core.trail_end + 1,
        vals := (s_dec.core.vals.set lit.toNat 1#8).set (lit.toNat ^^^ 1) 255#8,
        flags := flags',
        lvl := s_dec.core.lvl.set (lit.toNat / 2) (BitVec.ofNat 32 s_dec.core.cur_level),
        rsns := s_dec.core.rsns.set (lit.toNat / 2) 4294967295#32,
        trl := s_dec.core.trl.set s_dec.core.trail_end lit,
        trail_pos := s_dec.core.trail_pos.set (lit.toNat / 2)
          (BitVec.ofNat 32 s_dec.core.trail_end) }
      scratch := { s_dec.scratch with phases := phases' } }
  have hsp_asn : FullSparseInv c F0 s_asn := by
    have h1 : FullLuckySpecs.FullSparseInv c F0 s_asn := by
      simpa only [s_asn, s_dec, ftrl', fdec', hlit_v] using hpr.1
    exact ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2⟩
  obtain ⟨F_cur_a, hw_a⟩ := hsp_asn.1.witness
  c0_call hProp
  refine step13PropagateSpec_of hcfg hext hsp_asn.1.lengths hw_a hsp_asn.2.2.2.2
    ((fullM6HdrMem_iff ..).mpr hma) ?_
  dsimp only
  intro r ext' vals' flags'' lvl' rsns' trl' tp' te' prop' unass'' unfl'' wvec' arena' wstk'
    wlen' wu' fuel' ctype' cref' c0' c1' oom' ticks' wsort' phases'' del' mp
    hext' hlen_p hw_p htr_p hperm_p _ hfl_p hr_or _ h1 _ _ hmp
  let s_p : FullState :=
    { core := { s_asn.core with
        unassigned := unass'', wlen := wlen', wusable := wu', unflushed := unfl'',
        trail_end := te', propagated := prop', fuel := fuel', confl_ref := cref',
        confl_type := ctype', confl_lit0 := c0', confl_lit1 := c1', oom := oom',
        vals := vals', flags := flags'', lvl := lvl', rsns := rsns', trl := trl',
        trail_pos := tp', wvec := wvec', arena := arena', wstk := wstk' }
      scratch := { s_asn.scratch with
        search_ticks := ticks', phases := phases'', wsort := wsort', delayed := del' } }
  have hsp_p : FullSparseInv c F0 s_p :=
    fullSparseInv_of_fullPropagate hsp_asn hlen_p hw_p hperm_p rfl rfl rfl rfl rfl
  have hte_asn : s.core.trail_end < s_asn.core.trail_end := by
    change s.core.trail_end < s.core.trail_end + 1; omega
  have htrl_asn : s_asn.core.trl[s.core.trail_end]? = some lit := by
    change (s.core.trl.set s.core.trail_end lit)[s.core.trail_end]? = some lit
    rw [List.getElem?_set_self]; have := hsp.1.lengths.core_ok.trl_len; omega
  have hlvl_asn : s_asn.core.lvl[v]?.getD 0#32 = BitVec.ofNat 32 (s.core.cur_level + 1) := by
    change (s.core.lvl.set (lit.toNat / 2)
      (BitVec.ofNat 32 (s.core.cur_level + 1)))[v]?.getD 0#32 = _
    rw [hlit_v, List.getElem?_set_self]; simp; have := hsp.1.lengths.core_ok.lvl_len; omega
  exact hK r F_cur_a ext' s_asn s_p mp hext' hlen_p hsp_p hw_p rfl rfl (Nat.le_trans hfl_p hfl)
    hr_or (fun hr1 => (h1 hr1).2.2) htr_p hte_asn htrl_asn hlvl_asn ((fullM6HdrMem_iff ..).mp hmp)

private theorem s13_scan_ana_branch_wp {Γ : Env} {c : FullCfg} {F0 : CNF Nat}
    {F_cur1 : List (List Nat)} {ext1 : List (BitVec 64)} {s_init s_p1 : FullState}
    {R : Mem 64 → Prop} {mp1 : Mem 64} {Q : Post [i64]} {X : XPost}
    {Jbt : Cont [i64]} {karg : Val i64}
    (hProp : ∀ args m Q X, step13PropagateSpec args m Q X →
      Γ "full_propagate" [i64] [i64] args m Q X)
    (hAna : ∀ args m Q X, m6HdrAnalyzeSpec args m Q X →
      Γ "full_analyze_m6_hdr" [i64] [i64] args m Q X)
    (hcfg : FullM6HdrCfgOk c) (hext1 : M6HdrExtOk ext1)
    (hsp1 : FullSparseInv c F0 s_p1) (hw1 : FullWitnessInv c F0 F_cur1 s_p1.core)
    (hcl_eq1 : s_p1.core.cur_level = 1) (hcf1 : FullConflictOkW F_cur1 s_p1)
    (hfl_p1 : s_p1.core.fuel.toNat ≤ s_init.core.fuel.toNat)
    (hmp1 : (FullMem c s_p1 ⋆ (array64 (c.hdr - 2304) ext1 ⋆ R)) mp1)
    (hret2 : ∀ (ext_b : List (BitVec 64)) (s_b : FullState) mb,
      M6HdrExtOk ext_b → FullSparseInv c F0 s_b → s_b.core.fuel.toNat ≤ s_init.core.fuel.toNat →
      (FullMem c s_b ⋆ (array64 (c.hdr - 2304) ext_b ⋆ R)) mb →
      wp Γ Q X (@Expr.call Val Cont [i64] "full_backtrack" [i64, i64] []
        (Arg.var c.hdr, Arg.imm (0 : BitVec 64), PUnit.unit)
        fun _ => Expr.ret (Arg.imm (2 : BitVec 64), PUnit.unit)) mb)
    (hret2_otfs : ∀ (ext_b : List (BitVec 64)) (s_b : FullState) mb,
      M6HdrExtOk ext_b → FullOtfsInvW c F0 F_cur1 s_b →
      s_b.core.fuel.toNat ≤ s_init.core.fuel.toNat →
      (FullMem c s_b ⋆ (array64 (c.hdr - 2304) ext_b ⋆ R)) mb →
      wp Γ Q X (@Expr.call Val Cont [i64] "full_backtrack" [i64, i64] []
        (Arg.var c.hdr, Arg.imm (0 : BitVec 64), PUnit.unit)
        fun _ => Expr.ret (Arg.imm (2 : BitVec 64), PUnit.unit)) mb)
    (hunsat : ∀ (ext_u : List (BitVec 64)) (s_u : FullState) mu,
      M6HdrExtOk ext_u → s_u.LengthsOk c → s_u.core.fuel.toNat ≤ s_init.core.fuel.toNat →
      F0.Unsat → (FullM6HdrMem c ext_u s_u ⋆ R) mu → Q (20#64, PUnit.unit) mu)
    (hJbt : ∀ (ext_o : List (BitVec 64)) (s_o : FullState) mo,
      M6HdrExtOk ext_o → s_o.core.cur_vars = s_p1.core.cur_vars →
      FullSparseInv c F0 s_o → s_o.core.fuel.toNat ≤ s_init.core.fuel.toNat →
      (FullMem c s_o ⋆ (array64 (c.hdr - 2304) ext_o ⋆ R)) mo → Jbt (karg, PUnit.unit) mo) :
    wp Γ Q X (@Expr.call Val Cont [i64] "full_analyze_m6_hdr" [i64] [i64]
      (Arg.var c.hdr, PUnit.unit) fun p_43 =>
      Expr.let_ (op2 (.cmp .eq i64) (Arg.var p_43.fst) (Arg.imm (20 : BitVec 64))) fun p_44 =>
        Expr.jnz (Arg.var p_44.fst) (Expr.ret (Arg.imm (20 : BitVec 64), PUnit.unit))
          (Expr.let_ (op2 (.cmp .ne i64) (Arg.var p_43.fst) (Arg.imm (1 : BitVec 64)))
            fun p_45 =>
              Expr.jnz (Arg.var p_45.fst)
                (@Expr.call Val Cont [i64] "full_backtrack" [i64, i64] []
                  (Arg.var c.hdr, Arg.imm (0 : BitVec 64), PUnit.unit)
                  fun _ => Expr.ret (Arg.imm (2 : BitVec 64), PUnit.unit))
                (@Expr.call Val Cont [i64] "full_propagate" [i64] [i64]
                  (Arg.var c.hdr, PUnit.unit) fun p_46 =>
                  Expr.let_ (op2 (.cmp .eq i64) (Arg.var p_46.fst) (Arg.imm (1 : BitVec 64)))
                    fun p_47 =>
                      Expr.jnz (Arg.var p_47.fst)
                        (Expr.ret (Arg.imm (20 : BitVec 64), PUnit.unit))
                        (Expr.let_
                          (op2 (.cmp .eq i64) (Arg.var p_46.fst) (Arg.imm (2 : BitVec 64)))
                          fun p_48 =>
                            Expr.jnz (Arg.var p_48.fst)
                              (@Expr.call Val Cont [i64] "full_backtrack" [i64, i64] []
                                (Arg.var c.hdr, Arg.imm (0 : BitVec 64), PUnit.unit)
                                fun _ => Expr.ret (Arg.imm (2 : BitVec 64), PUnit.unit))
                              (Expr.jump Jbt (Arg.var karg, PUnit.unit)))))) mp1 := by
  have hsw1 : FullSparseInvW c F0 F_cur1 s_p1 := ⟨hsp1.1.lengths, hw1, hsp1.2⟩
  c0_call hAna
  refine m6HdrAnalyzeSpec_of (FullM6HdrInvW.mk_inv hcfg hext1 hsw1) hcf1
    ((fullM6HdrMem_iff ..).mpr hmp1) ?_
  intro ra ext_a s_a ma hext_a hlen_a hra hcv_a hfl_a _ huns_a hotfs_a h1_a hm_a
  flk_unmdata; flk_to_group
  · flk_steps
    have hra20 : ra = 20#64 := by assumption
    exact hunsat ext_a s_a ma hext_a hlen_a (Nat.le_trans hfl_a hfl_p1) (huns_a hra20) hm_a
  · have hne20 : ra ≠ 20#64 := by assumption
    have hne1 : ra ≠ 1#64 := by assumption
    have hra0 : ra = 0#64 := by
      rcases hra with rfl | rfl | rfl
      · rfl
      · exact absurd rfl hne1
      · exact absurd rfl hne20
    exact hret2_otfs ext_a s_a ma hext_a (hotfs_a hra0) (Nat.le_trans hfl_a hfl_p1)
      ((fullM6HdrMem_iff ..).mp hm_a)
  · have hra1 : ra = 1#64 := by assumption
    obtain ⟨hinv_a, hcl_lt_a⟩ := h1_a hra1
    have hsw_a := hinv_a.sparseW
    have hcl0_a : s_a.core.cur_level = 0 := by omega
    c0_call hProp
    refine step13PropagateSpec_of hcfg hext_a hsw_a.1 hsw_a.2.1 hsw_a.2.2.2.2.2 hm_a ?_
    dsimp only
    intro r3 ext3 vals3 flags3 lvl3 rsns3 trl3 tp3 te3 prop3 unass3 unfl3
      wvec3 arena3 wstk3 wlen3 wu3 fuel3 ctype3 cref3 c03 c13 oom3
      ticks3 wsort3 phases3 del3 mp3 hext3 hlen3 hw3 _ hperm3 _ hfl3 _ _ h1_3 _ _ hmp3
    let s_p3 : FullState :=
      { core := { s_a.core with
          unassigned := unass3, wlen := wlen3, wusable := wu3, unflushed := unfl3,
          trail_end := te3, propagated := prop3, fuel := fuel3, confl_ref := cref3,
          confl_type := ctype3, confl_lit0 := c03, confl_lit1 := c13, oom := oom3,
          vals := vals3, flags := flags3, lvl := lvl3, rsns := rsns3, trl := trl3,
          trail_pos := tp3, wvec := wvec3, arena := arena3, wstk := wstk3 }
        scratch := { s_a.scratch with
          search_ticks := ticks3, phases := phases3, wsort := wsort3, delayed := del3 } }
    have hsp3 : FullSparseInv c F0 s_p3 :=
      fullSparseInv_of_fullPropagate ⟨⟨hsw_a.1, F_cur1, hsw_a.2.1⟩, hsw_a.2.2⟩
        hlen3 hw3 hperm3 rfl rfl rfl rfl rfl
    have hfl_3 : s_p3.core.fuel.toNat ≤ s_init.core.fuel.toNat :=
      Nat.le_trans hfl3 (Nat.le_trans hfl_a hfl_p1)
    flk_unmdata; flk_to_group
    · flk_steps
      have hr3_1 : r3 = 1#64 := by assumption
      have hunsat3 : F0.Unsat :=
        level0_unsat_of_conflict_okW hw3 (show s_p3.core.cur_level = 0 from hcl0_a) (h1_3 hr3_1).2.2
      exact hunsat ext3 s_p3 mp3 hext3 hlen3 hfl_3 hunsat3 hmp3
    · exact hret2 ext3 s_p3 mp3 hext3 hsp3 hfl_3 ((fullM6HdrMem_iff ..).mp hmp3)
    · flk_steps
      exact hJbt ext3 s_p3 mp3 hext3 hcv_a hsp3 hfl_3 ((fullM6HdrMem_iff ..).mp hmp3)

/-! ## 3. `full_lucky_scan` Step-13 Proof (`step13LuckyScanM6Spec`) -/

/-- Step-13 `full_lucky_scan` satisfies `step13LuckyScanM6Spec`. -/
theorem full_lucky_scan_step13_wp (Γ : Env)
    (hOrd : ∀ args m Q X, fullLuckyOrdFidSpec args m Q X →
      Γ "full_lucky_ord_fid" [i64] [i64] args m Q X)
    (hAssign : ∀ args m Q X, fullAssignSpec args m Q X →
      Γ "full_assign" [i64, i32, i32] [] args m Q X)
    (hBt : ∀ args m Q X, fullBacktrackSpec args m Q X →
      Γ "full_backtrack" [i64, i64] [] args m Q X)
    (hProp : ∀ args m Q X, step13PropagateSpec args m Q X →
      Γ "full_propagate" [i64] [i64] args m Q X)
    (hAna : ∀ args m Q X, m6HdrAnalyzeSpec args m Q X →
      Γ "full_analyze_m6_hdr" [i64] [i64] args m Q X) :
    ∀ args m Q X, step13LuckyScanM6Spec args m Q X →
      Func.wp Γ full_lucky_scan_body args m Q X := by
  rintro ⟨h, pol?, fwd?, ⟨⟩⟩ m Q X hs
  obtain ⟨c, F0, ext, s, R, rfl, hcfg, hext, hsp, hcl0, hm, hQ⟩ := step13LuckyScanM6Spec_elim hs
  unfold Func.wp full_lucky_scan_body
  rw [fullM6HdrMem_iff] at hm
  flk_steps
  c0_call hOrd
  refine ⟨c, s, array64 (c.hdr - 2304) ext ⋆ R, rfl, hsp.1.lengths, hm,
    fun ⟨n_bv, ⟨⟩⟩ s0 m0 hcore0 hlen0 ⟨hn_le, hpres0⟩ hm0 => ?_⟩
  dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
    fullSafetySlice_safe] at hcore0 hlen0 hm0
  have hceq0 : s0.core = s.core := hcore0
  have hsp0 : FullSparseInv c F0 s0 := by
    refine ⟨hsp.1.with_scratch hlen0 hcore0, ?_, ?_, ?_, ?_⟩
    · unfold FullLitMarksClear FullMrkZero; rw [hceq0]; exact hsp.2.1
    · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
      rw [hceq0]; exact hsp.2.2.1
    · exact hsp.2.2.2.1.of_pres hpres0 (fun _ hr => by
        unfold fullArenaClauseRefs at hr ⊢; rw [hceq0]; exact hr)
    · rw [hceq0]; exact hsp.2.2.2.2
  have hmaxv := c.hmaxv; unfold dimacsBound at hmaxv
  have hcv_le0 : s.core.cur_vars ≤ c.max_vars := hsp.1.lengths.core_ok.cur_vars_le
  have hn_le_mx : n_bv.toNat ≤ c.max_vars := Nat.le_trans hn_le hcv_le0
  dsimp only
  c0_hsteps_nogrp
  have hret_bt : ∀ r (ext_b : List (BitVec 64)) (s_b : FullState) mb,
      M6HdrExtOk ext_b → FullSparseInv c F0 s_b → s_b.core.fuel.toNat ≤ s.core.fuel.toNat →
      (FullMem c s_b ⋆ (array64 (c.hdr - 2304) ext_b ⋆ R)) mb → (r = 0#64 ∨ r = 2#64) →
      wp Γ Q X (@Expr.call Val Cont [i64] "full_backtrack" [i64, i64] []
        (Arg.var c.hdr, Arg.imm (0 : BitVec 64), PUnit.unit)
        fun _ => Expr.ret (Arg.imm r, PUnit.unit)) mb := by
    intro r ext_b s_b mb hext_b hsb hfl_b hmb hr_or
    refine call_backtrack0_ret_wp hBt hsb hfl_b hmb fun s' m' hlen' hfl' hsp' hcl0' hm' => ?_
    exact hQ r ext_b s' m' hext_b hlen' (by rcases hr_or with rfl | rfl <;> simp) hfl'
      (fun h => by rcases hr_or with rfl | rfl <;> cases h) (fun _ => ⟨hsp', hcl0'⟩)
      (fun _ => hsp'.2.2.2.1.2) ((fullM6HdrMem_iff ..).mpr hm')
  have hret_otfs_bt : ∀ F_cur (ext_b : List (BitVec 64)) (s_b : FullState) mb,
      M6HdrExtOk ext_b → FullOtfsInvW c F0 F_cur s_b → s_b.core.fuel.toNat ≤ s.core.fuel.toNat →
      (FullMem c s_b ⋆ (array64 (c.hdr - 2304) ext_b ⋆ R)) mb →
      wp Γ Q X (@Expr.call Val Cont [i64] "full_backtrack" [i64, i64] []
        (Arg.var c.hdr, Arg.imm (0 : BitVec 64), PUnit.unit)
        fun _ => Expr.ret (Arg.imm (2 : BitVec 64), PUnit.unit)) mb := by
    intro F_cur ext_b s_b mb hext_b hotfs hfl_b hmb
    refine call_backtrack0_otfs_ret2_wp hBt hotfs hfl_b hmb
      fun s' m' hlen' hfl' hsp' hcl0' hm' => ?_
    exact hQ 2#64 ext_b s' m' hext_b hlen' (Or.inr (Or.inl rfl)) hfl'
      (fun h => absurd h (by decide)) (fun _ => ⟨hsp', hcl0'⟩) (fun _ => hsp'.2.2.2.1.2)
      ((fullM6HdrMem_iff ..).mpr hm')
  refine wp_loop_group (ts := [i64])
    (fun rem (idx, _) ml => ∃ (extL : List (BitVec 64)) (st : FullState),
      rem = n_bv.toNat - idx.toNat ∧ idx.toNat ≤ n_bv.toNat ∧ M6HdrExtOk extL ∧
      st.core.cur_vars = s.core.cur_vars ∧ FullSparseInv c F0 st ∧
      st.core.fuel.toNat ≤ s.core.fuel.toNat ∧
      (FullMem c st ⋆ (array64 (c.hdr - 2304) extL ⋆ R)) ml) ?_ ?_
  · rintro Jloop rem ⟨idx, ⟨⟩⟩ ml ih ⟨extL, st, rfl, hidx_le, hextL, hcv_eq, hst, hfl, hml⟩
    have hcv_le := hst.1.lengths.core_ok.cur_vars_le
    dsimp [Blocks.get]
    simp only [wp_let, Op.wp, OpCode.wp, vals, Arg.val, liftCmp, CmpOp.evalBits, Ty.hasFloat]
    rw [wp_jnz]; simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨fun hult => ?_, fun _ => ?_⟩
    · have hidx_lt : idx.toNat < n_bv.toNat := by
        have h1 : BitVec.ult idx n_bv = true := hult
        rwa [BitVec.ult, decide_eq_true_eq] at h1
      have hidx1_nat : (idx + 1#64).toNat = idx.toNat + 1 :=
        FullLuckyTactics.bv64_add1_toNat (by omega)
      refine wp_join_group (ts := [i64]) (fun (j_bv, _) mj =>
          mj = ml ∧ j_bv.toNat < n_bv.toNat) ?_ ?_
      · rintro Jj ⟨j_bv, ⟨⟩⟩ _ ⟨rfl, hj_lt⟩
        dsimp [Blocks.get]
        have hj_tr : j_bv.toNat < st.scratch.tarjan_reach.length := by
          rw [hst.1.lengths.scratch_ok.tarjan_reach_len]; omega
        c0_hsteps_nogrp
        refine wp_load_of (FullArenaTactics.c0_load_full_tarjan_reach hj_tr hml) ?_
        c0_hsteps_nogrp
        refine wp_join_group (ts := []) (fun _ mn =>
            ∃ (ext' : List (BitVec 64)) (st' : FullState),
              M6HdrExtOk ext' ∧ st'.core.cur_vars = s.core.cur_vars ∧
              FullSparseInv c F0 st' ∧ st'.core.fuel.toNat ≤ s.core.fuel.toNat ∧
              (FullMem c st' ⋆ (array64 (c.hdr - 2304) ext' ⋆ R)) mn) ?_ ?_
        · rintro Jnext ⟨⟩ mn ⟨ext', st', hext', hcv', hst', hfl', hmn⟩
          dsimp [Blocks.get]; flk_steps
          exact ih (n_bv.toNat - (idx.toNat + 1)) (idx + 1#64, PUnit.unit) mn (by omega)
            ⟨ext', st', by simp [hidx1_nat], by omega, hext', hcv', hst', hfl', hmn⟩
        · intro Jnext hJnext
          c0_hsplit
          · let v : BitVec 64 := (st.scratch.tarjan_reach[j_bv.toNat]'hj_tr).setWidth 64
            have hv_lt : v.toNat < st.core.cur_vars := by
              have h1 : (st.scratch.tarjan_reach[j_bv.toNat]'hj_tr).toNat <
                  s.core.cur_vars % 2 ^ 64 := by assumption
              dsimp only [v]; simp only [BitVec.toNat_setWidth]
              have := (st.scratch.tarjan_reach[j_bv.toNat]'hj_tr).isLt; rw [hcv_eq]; omega
            have hv_fl : v.toNat < st.core.flags.length := by
              have := hst.1.lengths.core_ok.flags_len; omega
            have hv2_vl : (v <<< 1#64).toNat < st.core.vals.length := by
              have := hst.1.lengths.core_ok.vals_len
              rw [FullLuckyTactics.bv64_shl1_toNat (by omega)]; omega
            flk_unmdata
            simp only [s13l_bv64_four, s13l_bv64_144, s13l_bv64_160, s13l_bv64_168, s13l_bv64_768]
            flk_to_group
            · exact hret_bt 2#64 extL st _ hextL hst hfl hml (Or.inr rfl)
            · have hfl_ne : st.core.fuel ≠ 0#64 := by simpa using hc
              have hfl_sub : (st.core.fuel - 1#64).toNat = st.core.fuel.toNat - 1 :=
                FullLuckyTactics.bv64_sub1_toNat hfl_ne
              have hval0 : st.core.vals[2 * v.toNat]?.getD 0#8 = 0#8 := by
                have h2v : (v <<< 1#64).toNat = 2 * v.toNat :=
                  FullLuckyTactics.bv64_shl1_toNat (by omega)
                have h_eq : BitVec.signExtend 32 st.core.vals[2 * v.toNat % 2 ^ 64] = 0#32 := by
                  assumption
                have h_mod : 2 * v.toNat % 2 ^ 64 = 2 * v.toNat := by omega
                rw [FullLuckyTactics.bv8_sext32_eq0_iff] at h_eq
                have hv2_lt : 2 * v.toNat < st.core.vals.length := by rw [← h2v]; exact hv2_vl
                have h_eq0 : st.core.vals[2 * v.toNat] = 0#8 := by simpa [h_mod] using h_eq
                simp [List.getElem?_eq_getElem hv2_lt, h_eq0]
              let st1 : FullState :=
                { st with core := { st.core with fuel := st.core.fuel - 1#64 } }
              have hst1 : FullSparseInv c F0 st1 :=
                FullSparseInv.with_fuel hst (st.core.fuel - 1#64)
              have hfl1 : st1.core.fuel.toNat ≤ s.core.fuel.toNat := by
                change (st.core.fuel - 1#64).toNat ≤ s.core.fuel.toNat; rw [hfl_sub]; omega
              refine wp_join_group (ts := [i32]) (fun (lit, _) mlit =>
                  (FullMem c st1 ⋆ (array64 (c.hdr - 2304) extL ⋆ R)) mlit ∧
                    lit.toNat / 2 = v.toNat) ?_ ?_
              · rintro Jlit ⟨lit, ⟨⟩⟩ mlit ⟨hmlit, hlit_v⟩
                dsimp [Blocks.get]
                obtain ⟨_, _, _, hnlvl_bv, _, _, _⟩ := decide_nlvl_ok hst1 hv_lt hval0
                have hte32_1 : st1.core.trail_end < 2 ^ 32 := by
                  have := hst1.1.lengths.core_ok.cur_vars_le; omega
                flk_unmdata
                simp only [s13l_bv64_four, s13l_bv64_144, s13l_bv64_160, s13l_bv64_768]
                c0_steps!
                rw [hnlvl_bv, FullLuckyTactics.bv64_trunc32_ofNat hte32_1] at *
                refine s13_call_assign_prop_decide_wp (R := R) hAssign hProp hcfg hextL hst1 hfl1
                  hv_lt hval0 hlit_v (by assumption)
                  fun r1 F_cur1 ext1 s_asn1 s_p1 mp1 hext1 hlen1 hsp1 hw1 hcl1 hcv1
                    hfl_p1 hr1 hcf1 htr1 hte1 htrl1 hlvl1 hmp1 => ?_
                flk_unmdata; flk_to_group
                · exact hret_bt 2#64 ext1 s_p1 mp1 hext1 hsp1 hfl_p1 hmp1 (Or.inr rfl)
                · refine wp_join_group (ts := [i64]) (fun (_, _) m_a =>
                      ∃ (ext_a : List (BitVec 64)) (s_a : FullState),
                        M6HdrExtOk ext_a ∧ s_a.core.cur_vars = s.core.cur_vars ∧
                        FullSparseInv c F0 s_a ∧ s_a.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                        (FullMem c s_a ⋆ (array64 (c.hdr - 2304) ext_a ⋆ R)) m_a) ?_ ?_
                  · rintro Jafter2 ⟨_, ⟨⟩⟩ m_a ⟨ext_a, s_a, hext_a, hcv_a, hsp_a, hfl_a, hm_a⟩
                    dsimp [Blocks.get]; flk_steps
                    exact hJnext PUnit.unit m_a ⟨ext_a, s_a, hext_a, hcv_a, hsp_a, hfl_a, hm_a⟩
                  · intro Jafter2 hJafter2
                    flk_unmdata; flk_to_group
                    · have hr1_eq : r1 = 1#64 := by assumption
                      refine wp_join_group (ts := [i64]) (fun (_, _) m_a =>
                          ∃ (ext_a : List (BitVec 64)) (s_a : FullState),
                            M6HdrExtOk ext_a ∧ s_a.core.cur_vars = s.core.cur_vars ∧
                            FullSparseInv c F0 s_a ∧ s_a.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                            (FullMem c s_a ⋆ (array64 (c.hdr - 2304) ext_a ⋆ R)) m_a) ?_ ?_
                      · rintro Jbt ⟨_, ⟨⟩⟩ m_a ⟨ext_a, s_a, hext_a, hcv_a, hsp_a, hfl_a, hm_a⟩
                        dsimp [Blocks.get]; flk_steps
                        exact hJafter2 _ m_a ⟨ext_a, s_a, hext_a, hcv_a, hsp_a, hfl_a, hm_a⟩
                      · intro Jbt hJbt
                        flk_unmdata; simp only [s13l_bv64_168]; flk_to_group
                        · have hcl_lt64 : s_p1.core.cur_level < 2 ^ 64 := by
                            have := hw1.cur_level_le; have := hlen1.core_ok.trail_end_le
                            have := hlen1.core_ok.cur_vars_le; omega
                          have hcl_mod : 1 < s_p1.core.cur_level % 2 ^ 64 := by simpa using hc
                          have hcl_gt1 : 1 < s_p1.core.cur_level := by omega
                          have hcl_bv : (BitVec.ofNat 64 s_p1.core.cur_level - 1#64).toNat =
                              st1.core.cur_level := by rw [hcl1]; bv_omega
                          c0_call hBt
                          refine ⟨c, s_p1, array64 (c.hdr - 2304) ext1 ⋆ R, rfl, hlen1, hcl_lt64,
                            fun _ => by
                              have := hlen1.core_ok.cur_vars_le; rw [hcl_bv, hcl1] at *; omega,
                            hw1.trail_lits_lt, hmp1, ?_⟩
                          dsimp only
                          intro vals_b lvl_b rsns_b trl_b tp_b te_b prop_b cl_b unass_b sc_b mb
                            hlen_b _ _ _ hps_b _ _ hbv_b hwt_b _ hmb
                          let s_b : FullState :=
                            { core := { s_p1.core with
                                vals := vals_b, lvl := lvl_b, rsns := rsns_b, trl := trl_b,
                                trail_pos := tp_b, trail_end := te_b, propagated := prop_b,
                                cur_level := cl_b, unassigned := unass_b }
                              scratch := sc_b }
                          have hsp_b : FullSparseInv c F0 s_b :=
                            fullSparseInv_of_fullBacktrack hsp1 hlen_b
                              (hwt_b F0 F_cur1 hw1 (by rw [hcl_bv, hcl1]; omega))
                              rfl rfl rfl rfl rfl hps_b.1.1 hps_b.1.2
                          have hv_lt_b : v.toNat < s_b.core.cur_vars := by
                            change v.toNat < s_p1.core.cur_vars; rw [hcv1]; exact hv_lt
                          have hval0_b : s_b.core.vals[2 * v.toNat]?.getD 0#8 = 0#8 := by
                            refine scan_backtrack_unassigned hlit_v hte1 htrl1 hlvl1 ?_ htr1
                              (by rw [hcv1]; exact Nat.mul_lt_mul_of_pos_left hv_lt (by decide)) ?_
                            · change st1.core.cur_level + 1 < 2 ^ 32; omega
                            · intro l hl
                              have := (hbv_b ⟨F0, F_cur1, Or.inl hw1⟩).1 l hl
                              simpa [hcl_bv] using this
                          flk_unmdata; c0_step; (repeat flk_strip); c0_step
                          · exact hret_bt 2#64 ext1 s_b mb hext1 hsp_b hfl_p1 hmb (Or.inr rfl)
                          · have hfl_ne_b : s_b.core.fuel ≠ 0#64 := hc
                            have hfl_sub_b :
                                (s_b.core.fuel - 1#64).toNat = s_b.core.fuel.toNat - 1 :=
                              FullLuckyTactics.bv64_sub1_toNat hfl_ne_b
                            let s_b1 : FullState :=
                              { s_b with core := { s_b.core with fuel := s_b.core.fuel - 1#64 } }
                            have hsb1 : FullSparseInv c F0 s_b1 :=
                              FullSparseInv.with_fuel hsp_b (s_b.core.fuel - 1#64)
                            have hfl_b1 : s_b1.core.fuel.toNat ≤ s.core.fuel.toNat := by
                              change (s_b.core.fuel - 1#64).toNat ≤ s.core.fuel.toNat
                              rw [hfl_sub_b]
                              have : s_b.core.fuel.toNat ≤ s.core.fuel.toNat := hfl_p1
                              omega
                            obtain ⟨_, _, _, hnlvl_b1, _, _, _⟩ :=
                              decide_nlvl_ok hsb1 hv_lt_b hval0_b
                            have hte32_b1 : s_b1.core.trail_end < 2 ^ 32 := by
                              have := hsb1.1.lengths.core_ok.cur_vars_le; omega
                            flk_unmdata; c0_steps!
                            rw [hnlvl_b1, FullLuckyTactics.bv64_trunc32_ofNat hte32_b1] at *
                            refine s13_call_assign_prop_decide_wp (R := R) hAssign hProp hcfg hext1
                              hsb1 hfl_b1 hv_lt_b hval0_b
                              ((FullLuckyHelpers.bv32_xor1_div2 lit).trans hlit_v) (by assumption)
                              fun r2 F_cur2 ext2 s_asn2 s_p2 mp2 hext2 hlen2 hsp2 hw2 hcl2 hcv2
                                hfl_p2 hr2 hcf2 htr2 hte2 htrl2 hlvl2 hmp2 => ?_
                            flk_unmdata; flk_to_group
                            · exact hret_bt 2#64 ext2 s_p2 mp2 hext2 hsp2 hfl_p2 hmp2 (Or.inr rfl)
                            · exact hret_bt 0#64 ext2 s_p2 mp2 hext2 hsp2 hfl_p2 hmp2 (Or.inl rfl)
                            · flk_steps
                              exact hJbt _ mp2 ⟨ext2, s_p2, hext2, by
                                change s_p2.core.cur_vars = s.core.cur_vars; rw [hcv2]
                                change s_b.core.cur_vars = s.core.cur_vars
                                change s_p1.core.cur_vars = s.core.cur_vars
                                rw [hcv1]; exact hcv_eq,
                                hsp2, hfl_p2, hmp2⟩
                        · have hcl_mod : s_p1.core.cur_level % 2 ^ 64 ≤ 1 := by simpa using hc
                          have hcl_lt64 : s_p1.core.cur_level < 2 ^ 64 := by
                            have := hw1.cur_level_le; have := hlen1.core_ok.trail_end_le
                            have := hlen1.core_ok.cur_vars_le; omega
                          have hcl_eq1 : s_p1.core.cur_level = 1 := by omega
                          refine s13_scan_ana_branch_wp hProp hAna hcfg hext1 hsp1 hw1 hcl_eq1
                            (hcf1 hr1_eq) hfl_p1 hmp1
                            (fun ext_b s_b mb hext_b hsb hfl_b hmb =>
                              hret_bt 2#64 ext_b s_b mb hext_b hsb hfl_b hmb (Or.inr rfl))
                            (fun ext_b s_b mb hext_b hotfs hfl_b hmb =>
                              hret_otfs_bt F_cur1 ext_b s_b mb hext_b hotfs hfl_b hmb)
                            (fun ext_u s_u mu hext_u hlen_u hfl_u huns hmu =>
                              hQ 20#64 ext_u s_u mu hext_u hlen_u (Or.inr (Or.inr (Or.inr rfl)))
                                hfl_u (fun _ => huns) (fun h => by rcases h with h | h <;> cases h)
                                (fun h => by cases h) hmu)
                            (fun ext_o s_o mo hext_o hcv_o hsp_o hfl_o hmo =>
                              hJbt _ mo ⟨ext_o, s_o, hext_o, by
                                change s_o.core.cur_vars = s.core.cur_vars; rw [hcv_o]
                                change s_p1.core.cur_vars = s.core.cur_vars
                                rw [hcv1]; exact hcv_eq,
                                hsp_o, hfl_o, hmo⟩)
                    · flk_steps
                      exact hJafter2 _ mp1 ⟨ext1, s_p1, hext1, by
                        change s_p1.core.cur_vars = s.core.cur_vars; rw [hcv1]; exact hcv_eq,
                        hsp1, hfl_p1, hmp1⟩
              · intro Jlit hJlit; flk_steps
                · have hl : (BitVec.setWidth 32 (v <<< 1)).toNat = 2 * v.toNat := by bv_omega
                  exact hJlit _ _ ⟨‹_›, by rw [hl]; omega⟩
                · have h_eq1 : (v <<< 1) = (v <<< 1#64) := rfl
                  have hl : (BitVec.setWidth 32 (v <<< 1) ||| 1#32).toNat = 2 * v.toNat + 1 := by
                    rw [h_eq1]; exact FullLuckyTactics.bv32_shl1_or1_trunc32_toNat (by omega)
                  exact hJlit _ _ ⟨‹_›, by rw [hl]; omega⟩
            · exact hJnext PUnit.unit _ ⟨extL, st, hextL, hcv_eq, hst, hfl, hml⟩
            · exact hJnext PUnit.unit _ ⟨extL, st, hextL, hcv_eq, hst, hfl, hml⟩
          · c0_hsteps; exact hJnext PUnit.unit _ ⟨extL, st, hextL, hcv_eq, hst, hfl, hml⟩
      · intro Jj hJj; flk_steps
        · exact hJj _ ml ⟨rfl, hidx_lt⟩
        · have hsub_nat : (n_bv - 1#64 - idx).toNat = n_bv.toNat - 1 - idx.toNat := by bv_omega
          exact hJj _ ml ⟨rfl, by rw [hsub_nat]; omega⟩
    · flk_steps
      exact hQ 10#64 extL st ml hextL hst.1.lengths (Or.inr (Or.inr (Or.inl rfl))) hfl
        (fun h => absurd h (by decide)) (fun h => by rcases h with h | h <;> cases h)
        (fun _ => hst.2.2.2.1.2) ((fullM6HdrMem_iff ..).mpr hml)
  · intro Jloop hJloop; flk_steps
    exact hJloop n_bv.toNat (0#64, PUnit.unit) m0
      ⟨ext, s0, by simp, Nat.zero_le _, hext, hceq0 ▸ rfl, hsp0,
        by rw [hceq0]; exact Nat.le_refl _, hm0⟩

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S4
