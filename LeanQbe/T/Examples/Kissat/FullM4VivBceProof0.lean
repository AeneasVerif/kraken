module

public import LeanQbe.T.Examples.Kissat.FullSpec3
public import LeanQbe.T.Examples.Kissat.FullVivifyLemmas1
public import LeanQbe.T.Examples.Kissat.FullVivifyLemmas3

/-!
# Kissat M4f Helper Proofs — `red_refs`-Preserving `full_viv_simplify` & `full_viv_commit`

Certifies that the existing unmodified `Full3.full_viv_simplify_body` and
`Full3.full_viv_commit_body` preserve `s.scratch.red_refs` under canonical `FullSpec2/3` callee
hypotheses (`fullUnwatchLargeSpec`, `fullAddUnitSpec`, `fullAddBinSpec`, `fullWatchPushSpec`).
This enables `full_vivify_m4` to store its prefix-sorted candidate schedule in `red_refs` across
`full_viv_clause_m4` calls while proving the canonical `FullFastBveBudgets.fullVivifyFastSpec`
with zero edits to any existing Kissat file.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM4VivBce

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-! ## 1. `red_refs`-preserving specifications (`fullVivSimplifyM4Spec`, `fullVivCommitM4Spec`) -/

/-- `red_refs`-preserving strengthening of `Full.fullVivSimplifySpec`. -/
def fullVivSimplifyM4Spec : Spec [i64, i32] [i64] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullVivifySpecs.FullSparseInvW c F0 F_cur s ∧ s.core.cur_level = 0 ∧
    cref.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cref.toNat = false ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullVivifySpecs.FullSparseInvW c F0 F_cur s' → s'.core.cur_level = 0 →
      s'.core.cur_vars = s.core.cur_vars → s'.core.arena_len = s.core.arena_len →
      s'.core.probing = s.core.probing → s'.core.fuel = s.core.fuel →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.red_refs = s.scratch.red_refs →
      (r = 0#64 ∨ r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (r = 0#64 →
        cref.toNat ∈ fullArenaClauseRefs s' ∧ fullArenaClauseGarb s' cref.toNat = false) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- `red_refs`-preserving strengthening of `Full.fullVivCommitSpec`. -/
def fullVivCommitM4Spec : Spec [i64, i32, i64, i32, .bool] [i64] :=
  fun (h, cref, out_ptr, olen, _used_red, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ out_ptr = c.pWorkStk2 ∧ FullVivifySpecs.FullSparseInvW c F0 F_cur s ∧
      s.core.cur_level = 0 ∧
      cref.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cref.toNat = false ∧
      olen.toNat ≤ c.max_vars ∧
      (olen.toNat < fullArenaClauseSize s cref.toNat →
        (∀ i < olen.toNat, (s.scratch.work_stk2[i]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
        ((s.scratch.work_stk2.take olen.toNat).map fun x => x.toNat / 2).Nodup ∧
        (cnfOfClauses F_cur).EntailsClause
          (cnfClause ((s.scratch.work_stk2.take olen.toNat).map BitVec.toNat))) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ r s' m',
        FullVivifySpecs.FullSparseInvW c F0 F_cur s' → s'.core.cur_level = 0 →
        s'.core.cur_vars = s.core.cur_vars → s'.core.arena_len = s.core.arena_len →
        s'.core.probing = s.core.probing → s'.core.fuel = s.core.fuel →
        fullArenaClauseRefs s' = fullArenaClauseRefs s →
        s'.scratch.red_refs = s.scratch.red_refs →
        (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

theorem fullVivSimplifyM4_implies_canon {a m Q X} (h : fullVivSimplifySpec a m Q X) :
    fullVivSimplifyM4Spec a m Q X := by
  rcases a with ⟨hdr, cref, ⟨⟩⟩
  rcases h with ⟨c, F0, F_cur, s, R, rfl, hsp, hl0, href, hng, hm, hQ⟩
  exact ⟨c, F0, F_cur, s, R, rfl, hsp, hl0, href, hng, hm,
    fun r s' m' hsp' hl' hcv' hal' hpr' hfu' href' _ hr h20 h0 hm' =>
      hQ r s' m' hsp' hl' hcv' hal' hpr' hfu' href' hr h20 h0 hm'⟩

theorem fullVivCommitM4_implies_canon {a m Q X} (h : fullVivCommitSpec a m Q X) :
    fullVivCommitM4Spec a m Q X := by
  rcases a with ⟨hdr, cref, out_ptr, olen, used_red, ⟨⟩⟩
  rcases h with ⟨c, F0, F_cur, s, R, rfl, rfl, hsp, hl0, href, hng, hole, hout, hm, hQ⟩
  exact ⟨c, F0, F_cur, s, R, rfl, rfl, hsp, hl0, href, hng, hole, hout, hm,
    fun r s' m' hsp' hl' hcv' hal' hpr' hfu' href' _ hr h20 hm' =>
      hQ r s' m' hsp' hl' hcv' hal' hpr' hfu' href' hr h20 hm'⟩

section

open FullVivifyTactics FullVivifyHelpers
open FullVivifySpecs hiding FullLitMarksClear FullArenaVarsNodup FullLastLearnedWf FullExtScratchOk
  FullSparseInvW FullSparseInv
open scoped FullArenaTactics FullVivifyTactics

local macro "fv_while" : tactic =>
  `(tactic| ((try fv_unmdata); (repeat fv_strip); c0_step; c0_step))
local macro "fv_to_grp" : tactic => `(tactic| ((try fv_unmdata); (repeat fv_strip); fv_to_group))

private theorem c0_load_ws2_z {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < s.scratch.work_stk2.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pWorkStk2 + 0#64) = some s.scratch.work_stk2[0] :=
  FullArenaTactics.load_full_work_stk2 hi hm
private theorem c0_load_ws2_b {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < s.scratch.work_stk2.length)
    (hm : (FullMem c s ⋆ R) m) : loadVal m i32 c.pWorkStk2 = some s.scratch.work_stk2[0] := by
  simpa using FullArenaTactics.load_full_work_stk2 hi hm
private theorem c0_load_ws2_4 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 1 < s.scratch.work_stk2.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pWorkStk2 + 4#64) = some s.scratch.work_stk2[1] :=
  FullArenaTactics.load_full_work_stk2 hi hm

attribute [local c0_load] c0_load_ws2_z c0_load_ws2_b c0_load_ws2_4

/-! ## 2. Local `red_refs`-preserving callee specs and canonical adapters -/

private def fullVivAddUnitM4Spec : Spec [i64, i32] [.bool] := fun (h, lit, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ lit.toNat < 2 * s.core.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat]) ∧ (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) s' m',
      FullSparseInvW c F0 F_cur s' → s'.core.cur_level = 0 →
      s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
      s'.core.cur_vars = s.core.cur_vars → s'.core.probing = s.core.probing →
      s'.core.oom = s.core.oom → s'.core.fuel = s.core.fuel →
      s'.scratch.red_refs = s.scratch.red_refs →
      (ok = false → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

private def fullVivAddBinM4Spec : Spec [i64, i32, i32] [i64] := fun (h, a, b, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullLitMarksClear c s ∧
    FullExtScratchOk c s ∧ s.core.dense_mode = 0#64 ∧ s.core.cur_level = 0 ∧
    a.toNat < 2 * s.core.cur_vars ∧ b.toNat < 2 * s.core.cur_vars ∧
    (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat, b.toNat]) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (r : BitVec 64) s' m',
      s'.LengthsOk c → (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      FullWitnessInv c F0 F_cur s'.core → FullLitMarksClear c s' → FullExtScratchOk c s' →
      s'.core.dense_mode = 0#64 → s'.core.arena = s.core.arena →
      s'.core.arena_len = s.core.arena_len → s'.core.cur_vars = s.core.cur_vars →
      s'.core.cur_level = 0 → s'.core.probing = s.core.probing → s'.core.fuel = s.core.fuel →
      s'.scratch.red_refs = s.scratch.red_refs →
      (r = 20#64 → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (r, ()) m'

private abbrev HypAddUnitM4 (Γ : Env) : Prop :=
  ∀ a m Q X, fullVivAddUnitM4Spec a m Q X → Γ "full_add_unit" [i64, i32] [.bool] a m Q X

private abbrev HypAddBinM4 (Γ : Env) : Prop :=
  ∀ a m Q X, fullVivAddBinM4Spec a m Q X → Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X

private def VivM4Q (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop) (Q : Post [i64]) (cref : Nat) (allow0 : Bool) : Prop :=
  ∀ (r : BitVec 64) s' m',
    FullSparseInvW c F0 F_cur s' → s'.core.cur_level = 0 → s'.core.cur_vars = s.core.cur_vars →
    s'.core.arena_len = s.core.arena_len → s'.core.probing = s.core.probing →
    s'.core.fuel = s.core.fuel → fullArenaClauseRefs s' = fullArenaClauseRefs s →
    s'.scratch.red_refs = s.scratch.red_refs →
    (if allow0 then r = 0#64 ∨ r = 1#64 ∨ r = 20#64 else r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
    (r = 20#64 → F0.Unsat) →
    (allow0 = true → r = 0#64 →
      cref ∈ fullArenaClauseRefs s' ∧ fullArenaClauseGarb s' cref = false) →
    (FullMem c s' ⋆ R) m' → Q (r, ()) m'

private theorem vivUnwatchM4_adapter {Γ : Env}
    (hUnwatch : ∀ a m Q X, fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X) :
    ∀ a m Q X, fullVivUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X := by
  rintro ⟨h, lit, cref, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hsp, hw, hm, hQ⟩
  have hlay : WatchStackLayout s.core := by
    have hmw := hw.watches; unfold ModeWatchesInv at hmw
    have hdm : s.core.dense_mode = 0#64 := hsp.2.2.2.2
    simp only [hdm, ↓reduceIte] at hmw; exact hmw.layout
  refine hUnwatch _ m Q X ⟨c, s, R, rfl, hsp.1.lengths, hlay, hm, ?_⟩
  dsimp only; intro wvec' wstk' wu' m' hlen' _ hmode' hm'
  have hw' : FullWitnessInv c F0 F_cur
      { s.core with wvec := wvec', wstk := wstk', wusable := wu' } :=
    { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }
              watches := hmode' F_cur hw.watches }
  have hsp' : FullVivifySpecs.FullSparseInv c F0
      { s with core := { s.core with wvec := wvec', wstk := wstk', wusable := wu' } } :=
    ⟨⟨hlen', F_cur, hw'⟩, hsp.2.1, hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2⟩
  exact hQ wvec' wstk' wu' m' hsp' hw' hm'

private theorem vivAddUnitM4_adapter {Γ : Env}
    (hAddUnit : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X) : HypAddUnitM4 Γ := by
  rintro ⟨h, lit, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hsp, hlit, hent, hm, hQ⟩
  refine hAddUnit _ m Q X ⟨c, F0, F_cur, s, R, rfl, hsp.1, hsp.2.1, fun _ => hent, hm, ?_⟩
  dsimp only
  intro ok vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc'
    ph' ta' ba' pt' pb' hp' ps' hl' qsi' qss' m' hlen' hw' hcl0 hltf _ hm'
  let s' : FullState :=
    { s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te',
                            propagated := prop', cur_level := cl', unassigned := unass',
                            unflushed := unfl', inconsistent := inc' }
      scratch := { s.scratch with phases := ph', target_assigned := ta', best_assigned := ba',
                                  phases_target := pt', phases_best := pb', heap := hp',
                                  pos := ps', heap_len := hl', q_search_idx := qsi',
                                  q_search_stamp := qss' } }
  have hsp' : FullSparseInvW c F0 F_cur s' :=
    ⟨hlen', hw', hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩
  exact hQ ok s' m' hsp' hcl0 rfl rfl rfl rfl rfl rfl rfl (fun hf => (hltf hlit hf).1) hm'

private theorem vivAddBinM4_adapter {Γ : Env}
    (hAddBin : ∀ a m Q X, fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X) : HypAddBinM4 Γ := by
  rintro ⟨h, a, b, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hlm, hext, hdm, hcl0, _ha, _hb, hent, hm, hQ⟩
  refine hAddBin _ m Q X ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hcl0, fun _ _ => hent, hm, ?_⟩
  dsimp only
  intro r vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' wlen' wu' nb' oom' inc'
    ph' wso' m' hlen' hw' hr h20 _ hm'
  exact hQ r _ m' hlen' hr hw' hlm hext hdm rfl rfl rfl hcl0 rfl rfl rfl (fun h => (h20 h).1) hm'

private theorem vivWatchPushM4_adapter {Γ : Env}
    (hWatchPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) : HypWatchPush Γ := by
  rintro ⟨h, lit, w0, w1, cnt, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hlay, hc1, hc2, hm, hQ⟩
  exact hWatchPush _ m Q X ⟨c, s, R, rfl, hlen, hlay, hc1, hc2, hm,
    fun ok wvec' wstk' wlen' wu' wsort' m' hlen' hlay' hoth hT hF hm' =>
      hQ ok wvec' wstk' wlen' wu' wsort' m' hlen' hlay' hoth hT (fun hf => (hF hf).1) hm'⟩

/-! ## 3. Small `red_refs`-aware helper packs -/

private theorem fv_len_core_inc_m4 {c : FullCfg} {k : FullCoreState} (hc : k.LengthsOk c)
    (inc' : BitVec 64) : ({ k with inconsistent := inc' } : FullCoreState).LengthsOk c :=
  ⟨hc.1, hc.2, hc.3, hc.4, hc.5, hc.6, hc.7, hc.8, hc.9, hc.10, hc.11, hc.12, hc.13, hc.14,
   hc.15, hc.16, hc.17, hc.18, hc.19, hc.20, hc.21, hc.22, hc.23, hc.24, hc.25⟩

private theorem fv_len_vivcnt_m4 {c : FullCfg} {sc : FullScratch} (hs : sc.LengthsOk c)
    (v : BitVec 64) : ({ sc with viv_cnt := v } : FullScratch).LengthsOk c :=
  ⟨hs.1, hs.2, hs.3, hs.4, hs.5, hs.6, hs.7, hs.8, hs.9, hs.10, hs.11, hs.12, hs.13, hs.14,
   hs.15, hs.16, hs.17, hs.18, hs.19, hs.20, hs.21, hs.22, hs.23, hs.24⟩

private theorem fv_witness_with_inc_m4 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k) (hu : (cnfOfClauses F_cur).Unsat) :
    FullWitnessInv c F0 F_cur { k with inconsistent := 1#64 } :=
  { hw with
    inconsistent_sound := fun _ => hu
    arena := { hw.arena with len_ok := hw.arena.len_ok }
    watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }

private theorem commit_vivcnt_pack_m4 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {m : Mem 64} (hsp : FullSparseInvW c F0 F_cur s)
    (hm : (FullMem c { s with scratch :=
      { s.scratch with viv_cnt := s.scratch.viv_cnt + 1#64 } } ⋆ R) m) :
    ∃ s1 : FullState, s1.core = s.core ∧ s1.scratch.work_stk2 = s.scratch.work_stk2 ∧
      s1.scratch.red_refs = s.scratch.red_refs ∧
      FullSparseInvW c F0 F_cur s1 ∧ (FullMem c s1 ⋆ R) m :=
  ⟨{ s with scratch := { s.scratch with viv_cnt := s.scratch.viv_cnt + 1#64 } }, rfl, rfl, rfl,
    ⟨⟨hsp.1.core_ok, fv_len_vivcnt_m4 hsp.1.scratch_ok _⟩, hsp.2.1, hsp.2.2.1, hsp.2.2.2.1,
      hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩, hm⟩

private theorem commit_zero_pack_m4 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {m : Mem 64} {cref : Nat}
    (hsp : FullSparseInvW c F0 F_cur s) (hl0 : s.core.cur_level = 0)
    (hu : (cnfOfClauses F_cur).Unsat) (hQ : VivM4Q c F0 F_cur s R Q cref false)
    (hm : (FullMem c { { s with scratch := { s.scratch with viv_cnt := s.scratch.viv_cnt + 1#64 } }
      with core := { s.core with inconsistent := 1#64 } } ⋆ R) m) : Q (20#64, ()) m :=
  let s' : FullState := { { s with scratch := { s.scratch with viv_cnt := s.scratch.viv_cnt +
    1#64 } } with core := { s.core with inconsistent := 1#64 } }
  have hsp' : FullSparseInvW c F0 F_cur s' :=
    ⟨⟨fv_len_core_inc_m4 hsp.1.core_ok 1#64, fv_len_vivcnt_m4 hsp.1.scratch_ok _⟩,
      fv_witness_with_inc_m4 hsp.2.1 hu, hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩
  hQ 20#64 s' m hsp' hl0 rfl rfl rfl rfl rfl rfl (Or.inr (Or.inr rfl))
    (fun _ => hsp.2.1.ext_sound.2 hu) (fun h => by cases h) hm

private theorem simplify_zero_pack_m4 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s2 : FullState} {R : Mem 64 → Prop} {Q : Post [i64]} {m : Mem 64} {cref : Nat}
    {ar3 : List (BitVec 32)} (hsp2 : FullSparseInvW c F0 F_cur s2)
    (har_eq : ar3 = s2.core.arena) (hu : (cnfOfClauses F_cur).Unsat) (hm2 : VivMetaEq s s2)
    (href2 : fullArenaClauseRefs s2 = fullArenaClauseRefs s)
    (hrr2 : s2.scratch.red_refs = s.scratch.red_refs)
    (hQ : VivM4Q c F0 F_cur s R Q cref true)
    (hm : (FullMem c { s2 with core :=
      { s2.core with arena := ar3, inconsistent := 1#64 } } ⋆ R) m) : Q (20#64, ()) m :=
  let s' : FullState := { s2 with core := { s2.core with inconsistent := 1#64 } }
  have hsp' : FullSparseInvW c F0 F_cur s' :=
    ⟨⟨fv_len_core_inc_m4 hsp2.1.core_ok 1#64, hsp2.1.scratch_ok⟩,
      fv_witness_with_inc_m4 hsp2.2.1 hu, hsp2.2.2.1, hsp2.2.2.2.1, hsp2.2.2.2.2.1, hsp2.2.2.2.2.2⟩
  hQ 20#64 s' m hsp' hm2.2.2.1 hm2.2.1 hm2.1 hm2.2.2.2.1 hm2.2.2.2.2 href2 hrr2
    (Or.inr (Or.inr rfl)) (fun _ => hsp2.2.1.ext_sound.2 hu) (fun _ h => by cases h)
    (by simpa only [har_eq] using hm)

private theorem addUnit_call_m4_wp (Γ : Env) (hAddUnit : HypAddUnitM4 Γ)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s s_g : FullState}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {lit : Val i32} {m_g : Mem 64} {J : Cont [i64]} (hsp_g : FullSparseInvW c F0 F_cur s_g)
    (hm_g : VivMetaEq s s_g) (ha_g : VivArenaEq s s_g)
    (hrr_g : s_g.scratch.red_refs = s.scratch.red_refs)
    (hlit_lt : lit.toNat < 2 * s_g.core.cur_vars)
    (hlit_ent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat]))
    (hmem_g : (FullMem c s_g ⋆ R) m_g)
    (hJ1 : ∀ s' m', FullSparseInvW c F0 F_cur s' → VivMetaEq s s' → VivArenaEq s s' →
      s'.scratch.red_refs = s.scratch.red_refs →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (Expr.jump J (Arg.imm 1, ())) m')
    (hJ20 : ∀ s' m', FullSparseInvW c F0 F_cur s' → VivMetaEq s s' → VivArenaEq s s' →
      s'.scratch.red_refs = s.scratch.red_refs →
      F0.Unsat → (FullMem c s' ⋆ R) m' → wp Γ Q X (Expr.jump J (Arg.imm 20, ())) m') :
    wp Γ Q X (Expr.call "full_add_unit" (as := [i64, i32]) (bs := [.bool])
      (Arg.var c.hdr, Arg.var lit, ()) fun p => Expr.jnz (Arg.var p.fst)
        (Expr.jump J (Arg.imm 1, ())) (Expr.jump J (Arg.imm 20, ()))) m_g := by
  c0_call hAddUnit
  refine ⟨c, F0, F_cur, s_g, R, rfl, hsp_g, hlit_lt, hlit_ent, hmem_g,
    fun ok s4 m4 hsp4 hl4 har4 halen4 hcv4 hpr4 _ hfu4 hrr4 hok_f hm4 => ?_⟩
  have hmv4 : VivMetaEq s s4 := ⟨halen4.trans hm_g.1, hcv4.trans hm_g.2.1, hl4,
    hpr4.trans hm_g.2.2.2.1, hfu4.trans hm_g.2.2.2.2⟩
  have ha4 : VivArenaEq s s4 :=
    ⟨(show fullArenaClauseRefs s4 = fullArenaClauseRefs s_g by
        unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har4, halen4]).trans ha_g.1,
     fun q hq => by rw [har4]; exact ha_g.2 q hq⟩
  fv_steps
  · exact hJ1 s4 m4 hsp4 hmv4 ha4 (hrr4.trans hrr_g) hm4
  · exact hJ20 s4 m4 hsp4 hmv4 ha4 (hrr4.trans hrr_g) (hok_f hc) hm4

private theorem markGarb_bin_pack_m4 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s2 s4 : FullState} {R : Mem 64 → Prop} {m : Mem 64} {cref : Nat} {hdr : BitVec 32}
    {ag : BitVec 64} (hlen4 : s4.LengthsOk c) (hw4 : FullWitnessInv c F0 F_cur s4.core)
    (hmc4 : FullLitMarksClear c s4) (hext4 : FullExtScratchOk c s4)
    (hdm4 : s4.core.dense_mode = 0#64) (hl4 : s4.core.cur_level = 0)
    (href : cref ∈ fullArenaClauseRefs s) (hs2_ref : fullArenaClauseRefs s2 = fullArenaClauseRefs s)
    (hs2_al : s2.core.arena_len = s.core.arena_len) (har4 : s4.core.arena = s2.core.arena)
    (halen4 : s4.core.arena_len = s2.core.arena_len) (hhdr4 : fullArenaHdr s4 cref = hdr)
    (hnd_other : ∀ r ∈ fullArenaClauseRefs s4, r ≠ cref → fullArenaClauseGarb s4 r = false →
      ((fullArenaClauseLits s4 r).map (· / 2)).Nodup)
    (hnxt_u : ∀ q ∈ fullArenaClauseRefs s2, fullArenaNextOff s2.core.arena s2.core.arena_len q =
      fullArenaNextOff s.core.arena s2.core.arena_len q)
    (hm : (FullMem c { s4 with core := { s4.core with
      arena := s4.core.arena.set cref (hdr ||| 0x00080000#32), arena_garbage := ag } } ⋆ R) m) :
    ∃ s5 : FullState, s5.core.arena_len = s.core.arena_len ∧
      s5.core.cur_vars = s4.core.cur_vars ∧ s5.core.probing = s4.core.probing ∧
      s5.core.fuel = s4.core.fuel ∧ s5.scratch.red_refs = s4.scratch.red_refs ∧
      FullSparseInvW c F0 F_cur s5 ∧ s5.core.cur_level = 0 ∧
      VivArenaEq s s5 ∧ (FullMem c s5 ⋆ R) m := by
  have href4 : fullArenaClauseRefs s4 = fullArenaClauseRefs s2 := by
    unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har4, halen4]
  obtain ⟨s5, _, hm5', hsc5, hsp5, ha5, hm5⟩ := fullArena_markGarb_pack hlen4 hw4 hmc4 hext4 hdm4
    hl4 (href4 ▸ hs2_ref ▸ href) hhdr4 hnd_other hm
  exact ⟨s5, hm5'.1.trans (halen4.trans hs2_al), hm5'.2.1, hm5'.2.2.2.1, hm5'.2.2.2.2,
    congrArg FullScratch.red_refs hsc5, hsp5, hm5'.2.2.1,
    ⟨ha5.1.trans (href4.trans hs2_ref), fun q hq => by
      have h1 := ha5.2 q (href4 ▸ hs2_ref ▸ hq); have h2 := hnxt_u q (hs2_ref ▸ hq)
      rw [halen4, hs2_al] at h1; rw [hs2_al] at h2; rw [har4] at h1; exact h1.trans h2⟩, hm5⟩

private theorem watch2_pre_ok_m4 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {blk cref : BitVec 32} (hsp : FullSparseInvW c F0 F_cur s)
    (hcref : cref ≠ 0xFFFFFFFF#32) :
    s.LengthsOk c ∧ WatchStackLayout s.core ∧
    ((2#32 : BitVec 32).toNat = 1 → (blk &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32) ∧
    ((2#32 : BitVec 32).toNat = 2 →
      (blk &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32 ∧ cref ≠ 0xFFFFFFFF#32) :=
  ⟨hsp.1,
    by have hmw := hsp.2.1.watches; unfold ModeWatchesInv at hmw
       simp only [hsp.2.2.2.2.2, ↓reduceIte] at hmw; exact hmw.layout,
    fun h => absurd h (by decide),
    fun _ => ⟨(bv32_mask_lo31_props _).2, hcref⟩⟩

private theorem watch2_calls_m4_wp (Γ : Env) (hWatchPush : HypWatchPush Γ)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s s_f : FullState} {R : Mem 64 → Prop}
    {cref la lb : Val i32} {k_ok k_oom : Expr Val Cont [i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (hsp : FullSparseInvW c F0 F_cur s_f)
    (hcref : cref.toNat < 0x80000000) (href : cref.toNat ∈ fullArenaClauseRefs s)
    (hsref : fullArenaClauseRefs s_f = fullArenaClauseRefs s) (hm_f : VivMetaEq s s_f)
    (hrr_f : s_f.scratch.red_refs = s.scratch.red_refs) (hm : (FullMem c s_f ⋆ R) m)
    (hok : ∀ s' m', FullSparseInvW c F0 F_cur s' → s'.core.arena = s_f.core.arena →
      VivMetaEq s s' → fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.red_refs = s.scratch.red_refs →
      (FullMem c s' ⋆ R) m' → wp Γ Q X k_ok m')
    (hoom : ∀ s' m', FullSparseInvW c F0 F_cur s' → s'.core.arena = s_f.core.arena →
      VivMetaEq s s' → fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.red_refs = s.scratch.red_refs →
      (FullMem c s' ⋆ R) m' → wp Γ Q X k_oom m') :
    wp Γ Q X (watch2Expr c.hdr cref la lb k_ok k_oom) m := by
  have hne : cref ≠ 0xFFFFFFFF#32 := bv32_ne_sentinel_of_lt hcref
  dsimp only [watch2Expr, fvOp]
  refine wp_join_group
    (fun _ m' => ∃ s' : FullState, FullSparseInvW c F0 F_cur s' ∧
      s'.core.arena = s_f.core.arena ∧ VivMetaEq s s' ∧
      fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
      s'.scratch.red_refs = s.scratch.red_refs ∧ (FullMem c s' ⋆ R) m')
    (fun _ _ _ ⟨s', hsp', har', hmv', href', hrr', hm'⟩ => by
      fv_steps; exact hoom _ _ (fv_with_oomW hsp' 1#64) har' hmv' href' hrr' hm)
    (fun Js hJs => ?_)
  fv_steps; c0_call hWatchPush
  obtain ⟨hl1, lay1, hp1_1, hp1_2⟩ := watch2_pre_ok_m4 (blk := lb) hsp hne
  refine ⟨c, s_f, R, rfl, hl1, lay1, hp1_1, hp1_2, hm,
    fun ok1 wvec3 wstk3 wlen3 wu3 wsort3 m4 hlen4 hlay4 hoth4 hok1_t hok1_f hm4 => ?_⟩
  have hsp4 := fullWatchPush_large_preserves_sparseInvW hsp (bv32_mask_lo31_props lb).1 hcref
    (by rw [hsref]; exact href) hlen4 hlay4 hoth4
    (fun h => let t := hok1_t h; ⟨t.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2 rfl⟩) hok1_f
  fv_steps
  · c0_call hWatchPush
    obtain ⟨hl2, lay2, hp2_1, hp2_2⟩ := watch2_pre_ok_m4 (blk := la) hsp4 hne
    refine ⟨c, _, R, rfl, hl2, lay2, hp2_1, hp2_2, hm4,
      fun ok2 wvec4 wstk4 wlen4 wu4 wsort4 m5 hlen5 hlay5 hoth5 hok2_t hok2_f hm5 => ?_⟩
    have hsp5 := fullWatchPush_large_preserves_sparseInvW hsp4 (bv32_mask_lo31_props la).1 hcref
      (by change cref.toNat ∈ fullArenaClauseRefs s_f; rw [hsref]; exact href) hlen5 hlay5 hoth5
      (fun h => let t := hok2_t h; ⟨t.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2 rfl⟩)
      hok2_f
    fv_steps
    · exact hok _ m5 hsp5 rfl hm_f hsref hrr_f hm5
    · exact hJs () m5 ⟨_, hsp5, rfl, hm_f, hsref, hrr_f, hm5⟩
  · exact hJs () m4 ⟨_, hsp4, rfl, hm_f, hsref, hrr_f, hm4⟩

private theorem unwatch2_state_pack_m4 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s_in : FullState} {R : Mem 64 → Prop} {m : Mem 64} {cref : Nat} {old_sz hdr : BitVec 32}
    (hsp : FullSparseInv c F0 s_in) (hw : FullWitnessInv c F0 F_cur s_in.core)
    (hm : (FullMem c s_in ⋆ R) m) (hng : fullArenaClauseGarb s cref = false)
    (hsz_eq : fullArenaClauseSize s cref = old_sz.toNat) (hhdr_eq : hdr = fullArenaHdr s cref)
    (hs_ar : s_in.core.arena = s.core.arena) (hs_v : s_in.core.vals = s.core.vals)
    (hs_cv : s_in.core.cur_vars = s.core.cur_vars) (hs_al : s_in.core.arena_len = s.core.arena_len)
    (hs_l0 : s_in.core.cur_level = 0) (hs_pr : s_in.core.probing = s.core.probing)
    (hs_fu : s_in.core.fuel = s.core.fuel) (hws2 : s_in.scratch.work_stk2 = s.scratch.work_stk2)
    (hrr : s_in.scratch.red_refs = s.scratch.red_refs) :
    ∃ s2 : FullState, s2.core.arena = s.core.arena ∧ s2.core.vals = s.core.vals ∧
      s2.scratch.work_stk2 = s.scratch.work_stk2 ∧ s2.scratch.red_refs = s.scratch.red_refs ∧
      VivMetaEq s s2 ∧ fullArenaClauseRefs s2 = fullArenaClauseRefs s ∧
      fullArenaClauseGarb s2 cref = false ∧ fullArenaClauseSize s2 cref = old_sz.toNat ∧
      fullArenaHdr s2 cref = hdr ∧ FullSparseInvW c F0 F_cur s2 ∧ (FullMem c s2 ⋆ R) m :=
  ⟨s_in, hs_ar, hs_v, hws2, hrr, ⟨hs_al, hs_cv, hs_l0, hs_pr, hs_fu⟩,
    by unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [hs_ar, hs_al],
    by unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore; rw [hs_ar]; exact hng,
    by unfold fullArenaClauseSize fullArenaClauseSizeCore; rw [hs_ar]; exact hsz_eq,
    by unfold fullArenaHdr fullArenaHdrCore; rw [hs_ar]; exact hhdr_eq.symm,
    ⟨hsp.1.lengths, hw, hsp.2.1, hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2⟩, hm⟩

/-! ## 4. `red_refs`-preserving `full_viv_simplify_m4_wp` -/

private abbrev simplifyPostLoop2ExprM4 (c : FullCfg) (cref hdr old_sz nsz : Val i32) :
    Expr Val Cont [i64] :=
  fvOp (OpCode.cmp .eq i32 .bool rfl) (Arg.var nsz, Arg.imm 0, ()) fun p =>
  Expr.jnz (Arg.var p.fst)
    (fvOp (OpCode.add i64) (Arg.var c.hdr, Arg.imm 1024, ()) fun p =>
     Expr.store (Arg.imm (t := i64) 1) (Arg.var p.fst) (Expr.ret (Arg.imm 20, ())))
    (fvOp (OpCode.cmp .eq i32 .bool rfl) (Arg.var nsz, Arg.imm 1, ()) fun p =>
     Expr.jnz (Arg.var p.fst)
      (arBasePtr c.pArena cref fun p =>
       fvOp (OpCode.or i32) (Arg.var hdr, Arg.imm 524288, ()) fun p1 =>
       Expr.store (Arg.var p1.fst) (Arg.var p) (addArenaGarbageExpr c.hdr old_sz
         (Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun (p : Tup Val [i64]) =>
            Expr.ret (Arg.var p.fst, ())) Blocks.nil) fun Js =>
          arOffPtr c.pArena cref 3 fun p => Expr.load i32 (Arg.var p) fun ld =>
          Expr.call "full_add_unit" (as := [i64, i32]) (bs := [.bool])
            (Arg.var c.hdr, Arg.var ld, ()) fun p => Expr.jnz (Arg.var p.fst)
            (Expr.jump Js.fst (Arg.imm 1, ())) (Expr.jump Js.fst (Arg.imm 20, ())))))
      (fvOp (OpCode.cmp .eq i32 .bool rfl) (Arg.var nsz, Arg.imm 2, ()) fun p =>
       Expr.jnz (Arg.var p.fst)
        (arOffPtr c.pArena cref 3 fun p => Expr.load i32 (Arg.var p) fun l0 =>
         arOffPtr c.pArena cref 4 fun p => Expr.load i32 (Arg.var p) fun l1 =>
         Expr.call "full_add_bin" (as := [i64, i32, i32]) (bs := [i64])
           (Arg.var c.hdr, Arg.var l0, Arg.var l1, ()) fun br =>
         arBasePtr c.pArena cref fun p =>
         fvOp (OpCode.or i32) (Arg.var hdr, Arg.imm 524288, ()) fun p1 =>
         Expr.store (Arg.var p1.fst) (Arg.var p) (addArenaGarbageExpr c.hdr old_sz
           (Expr.group (sig := [[i64]]) (fun _ => Blocks.cons (fun (p : Tup Val [i64]) =>
              Expr.ret (Arg.var p.fst, ())) Blocks.nil) fun Js =>
            fvOp (OpCode.cmp .eq i64 .bool rfl) (Arg.var br.fst, Arg.imm 20, ()) fun p =>
            Expr.jnz (Arg.var p.fst) (Expr.jump Js.fst (Arg.imm 20, ()))
              (Expr.jump Js.fst (Arg.imm 1, ())))))
        (arOffPtr c.pArena cref 2 fun p => Expr.store (Arg.var nsz) (Arg.var p)
         (arOffPtr c.pArena cref 1 fun p => Expr.store (Arg.imm (t := i32) 2) (Arg.var p)
          (Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
             arOffPtr c.pArena cref 3 fun p => Expr.load i32 (Arg.var p) fun l0 =>
             arOffPtr c.pArena cref 4 fun p => Expr.load i32 (Arg.var p) fun l1 =>
             Expr.group (sig := [[]]) (fun _ => Blocks.cons (fun (_ : Tup Val []) =>
               Expr.ret (Arg.imm 0, ())) Blocks.nil) fun Js =>
             watch2Expr c.hdr cref l0 l1 (Expr.jump Js.fst ()) (Expr.jump Js.fst ()))
             Blocks.nil) fun Js =>
           fvOp (OpCode.and i32) (Arg.var hdr, Arg.imm 8388608, ()) fun p =>
           fvOp (OpCode.cmp .eq i32 .bool rfl) (Arg.var p.fst, Arg.imm 0, ()) fun p =>
           Expr.jnz (Arg.var p.fst) (arBasePtr c.pArena cref fun p =>
              fvOp (OpCode.or i32) (Arg.var hdr, Arg.imm 8388608, ()) fun p1 =>
              Expr.store (Arg.var p1.fst) (Arg.var p)
                (storeTermExpr c.pArena cref old_sz (Expr.jump Js.fst ())))
              (Expr.jump Js.fst ()))))))

private abbrev simplifyLoop2ExprM4 (c : FullCfg) (cref hdr old_sz : Val i32) :
    Expr Val Cont [i64] :=
  Expr.group (sig := [[i32, i32]]) (fun Js => Blocks.cons (fun (p : Tup Val [i32, i32]) =>
    fvOp (OpCode.cmp .ult i32 .bool rfl) (Arg.var p.fst, Arg.var old_sz, ()) fun pb =>
    Expr.jnz (Arg.var pb.fst)
      (arLitPtr c.pArena cref p.fst fun pa => Expr.load i32 (Arg.var pa) fun ld =>
       Expr.group (sig := [[i32]]) (fun _Js1 => Blocks.cons (fun (pn : Tup Val [i32]) =>
         fvOp (OpCode.add i32) (Arg.var p.fst, Arg.imm 1, ()) fun pi =>
         Expr.jump Js.fst (Arg.var pi.fst, Arg.var pn.fst, ())) Blocks.nil) fun Js1 =>
       fvOp (OpCode.zext 32 64) (Arg.var ld, ()) fun pl =>
       fvOp (OpCode.add i64) (Arg.var c.pVals, Arg.var pl.fst, ()) fun pv =>
       Expr.load i8 (Arg.var pv.fst) fun lv =>
       fvOp (OpCode.trunc 32 8) (Arg.imm 0, ()) fun pz =>
       fvOp (OpCode.sext 8 32) (Arg.var lv, ()) fun plv =>
       fvOp (OpCode.sext 8 32) (Arg.var pz.fst, ()) fun pz32 =>
       fvOp (OpCode.cmp .eq i32 .bool rfl) (Arg.var plv.fst, Arg.var pz32.fst, ()) fun pc =>
       Expr.jnz (Arg.var pc.fst)
         (arLitPtr c.pArena cref p.snd.fst fun pn => Expr.store (Arg.var ld) (Arg.var pn)
            (fvOp (OpCode.add i32) (Arg.var p.snd.fst, Arg.imm 1, ())
              fun pnsz => Expr.jump Js1.fst (Arg.var pnsz.fst, ())))
         (Expr.jump Js1.fst (Arg.var p.snd.fst, ())))
      (simplifyPostLoop2ExprM4 c cref hdr old_sz p.snd.fst)) Blocks.nil)
  fun Js => Expr.jump Js.fst (Arg.imm 0, Arg.imm 0, ())

private theorem simplify_post_loop2_m4_wp (Γ : Env) (hAddUnit : HypAddUnitM4 Γ)
    (hAddBin : HypAddBinM4 Γ) (hWatchPush : HypWatchPush Γ) {c : FullCfg} {F0 : CNF Nat}
    {F_cur0 : List (List Nat)} {s s2 : FullState} {R : Mem 64 → Prop}
    {cref hdr old_sz nsz : Val i32} {ar3 : List (BitVec 32)} {idxs : List Nat} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (hsp2 : FullSparseInvW c F0 F_cur0 s2)
    (href : cref.toNat ∈ fullArenaClauseRefs s)
    (hs2_ref : fullArenaClauseRefs s2 = fullArenaClauseRefs s)
    (hs2_ng : fullArenaClauseGarb s2 cref.toNat = false) (hs2_ar : s2.core.arena = s.core.arena)
    (hm2_eq : VivMetaEq s s2) (hrr2 : s2.scratch.red_refs = s.scratch.red_refs)
    (hs2_sz : fullArenaClauseSize s2 cref.toNat = old_sz.toNat)
    (hs2_hdr : fullArenaHdr s2 cref.toNat = hdr) (hhdr_ng : (hdr &&& 0x00080000#32) = 0#32)
    (hnsz_lt : nsz.toNat < old_sz.toNat) (har3_len : ar3.length = c.arena_cap)
    (hout3 : ∀ p, (p < cref.toNat + 3 ∨ cref.toNat + 3 + nsz.toNat ≤ p) →
      ar3[p]? = s2.core.arena[p]?)
    (hid_len : idxs.length = nsz.toNat) (hid_pw : idxs.Pairwise (· < ·))
    (hid_lt : ∀ q ∈ idxs, q < old_sz.toNat)
    (hsub3 : ∀ t < nsz.toNat,
      ar3[cref.toNat + 3 + t]? = s2.core.arena[cref.toNat + 3 + idxs[t]?.getD 0]?)
    (hcov3 : ∀ j < old_sz.toNat,
      s2.core.vals[(s2.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat]?.getD 0#8 = 0#8 →
      ∃ t < nsz.toNat, ar3[cref.toNat + 3 + t]? = s2.core.arena[cref.toNat + 3 + j]?)
    (hno1_2 : ∀ j < old_sz.toNat,
      s2.core.vals[(s2.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat]?.getD 0#8 ≠ 1#8)
    (hm : (FullMem c { s2 with core := { s2.core with arena := ar3 } } ⋆ R) m)
    (hQ : VivM4Q c F0 F_cur0 s R Q cref.toNat true) :
    wp Γ Q X (simplifyPostLoop2ExprM4 c cref hdr old_sz nsz) m := by
  have hw2 := hsp2.2.1; have hcl := hsp2.1.core_ok
  have hcap := c.harena; unfold dimacsBound at hcap
  have har2_len := hcl.arena_len_arr; have halen_le := hcl.arena_len_le
  have href2 : cref.toNat ∈ fullArenaClauseRefs s2 := by rw [hs2_ref]; exact href
  have hwf := hw2.arena.refs_wf cref.toNat href2
  have hcref_lt : cref.toNat < s2.core.arena.length := by omega
  have hcref0 : (cref.setWidth 64).toNat = cref.toNat := by bv_omega
  have hcref1 : (cref.setWidth 64 + 1#64).toNat = cref.toNat + 1 := by bv_omega
  have hcref2 : (cref.setWidth 64 + 2#64).toNat = cref.toNat + 2 := by bv_omega
  have hcref3 : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3 := by bv_omega
  have hcref4 : (cref.setWidth 64 + 4#64).toNat = cref.toNat + 4 := by bv_omega
  have har3_lt0 : cref.toNat < ar3.length := by omega
  have har3_lt3 : (cref.setWidth 64 + 3#64).toNat < ar3.length := by omega
  have har3_lt4 : (cref.setWidth 64 + 4#64).toNat < ar3.length := by omega
  obtain ⟨hnew_lits_lt, hent_new, hupd_w, hnd_other_ar3⟩ :=
    simplify_compact_facts hsp2 hm2_eq.2.2.1 href2 hs2_ng (by omega) har3_len hid_len hout3
      (by simpa [hs2_sz] using hid_lt) hsub3
      (fun j hj => hcov3 j (by rw [hs2_sz] at hj; exact hj))
      (fun j hj => hno1_2 j (by rw [hs2_sz] at hj; exact hj))
  dsimp only [simplifyPostLoop2ExprM4, arBasePtr, arOffPtr, addArenaGarbageExpr, storeTermExpr,
    fvOp]
  fv_to_grp
  · have hnsz0 : nsz.toNat = 0 := by c0_bound
    have har3_eq : ar3 = s2.core.arena :=
      List.ext_getElem (har3_len.trans har2_len.symm) fun p hp1 hp2 => Option.some.inj (by
        rw [← List.getElem?_eq_getElem hp1, ← List.getElem?_eq_getElem hp2]
        exact hout3 p (by omega))
    exact simplify_zero_pack_m4 hsp2 har3_eq
      (unsat_of_entails_nil (by simpa [hnsz0] using hent_new)) hm2_eq hs2_ref hrr2 hQ hm
  · have hnsz1 : nsz.toNat = 1 := by c0_bound
    fv_steps; obtain ⟨hlen_u, hw_u, hrefs_u, hnxt_u⟩ := hupd_w (by omega)
    let s_upd : FullState := { s2 with core := { s2.core with arena := ar3 } }
    have hhdr_u : fullArenaHdr s_upd cref.toNat = hdr := by
      unfold fullArenaHdr fullArenaHdrCore; dsimp only [s_upd]
      rw [hout3 cref.toNat (Or.inl (by omega))]; exact hs2_hdr
    have hext_u : FullExtScratchOk c s_upd := ⟨fun i hi => by
      dsimp only [FullLastLearnedWf, s_upd]; rw [hrefs_u]
      exact hsp2.2.2.2.2.1.1 i hi, hsp2.2.2.2.2.1.2⟩
    obtain ⟨s_g, _, hmg, hsc_g, hsp_g, ha_g, hm_g⟩ :=
      fullArena_markGarb_pack hlen_u hw_u hsp2.2.2.1 hext_u hsp2.2.2.2.2.2 hm2_eq.2.2.1
        (by rw [hrefs_u]; exact href2) hhdr_u
        (fun r hr hne hngr => hnd_other_ar3 s_upd rfl rfl r (hrefs_u ▸ hr) hne hngr) hm
    have hms_g : VivMetaEq s s_g :=
      ⟨hmg.1.trans hm2_eq.1, hmg.2.1.trans hm2_eq.2.1, hmg.2.2.1,
       hmg.2.2.2.1.trans hm2_eq.2.2.2.1, hmg.2.2.2.2.trans hm2_eq.2.2.2.2⟩
    have has_g : VivArenaEq s s_g :=
      ⟨ha_g.1.trans (hrefs_u.trans hs2_ref), fun q hq => by
        have h1 := ha_g.2 q (hrefs_u ▸ hs2_ref ▸ hq)
        have h2 := hnxt_u q (hs2_ref ▸ hq); dsimp only [s_upd] at h1 h2
        rw [hm2_eq.1] at h1 h2; rw [hs2_ar] at h2; exact h1.trans h2⟩
    have hrr_g : s_g.scratch.red_refs = s.scratch.red_refs :=
      (congrArg FullScratch.red_refs hsc_g).trans hrr2
    have hcref3' : (cref.setWidth 64 + (3 : BitVec 64)).toNat = cref.toNat + 3 := hcref3
    have hne03 : (cref.setWidth 64).toNat ≠ (cref.setWidth 64 + (3 : BitVec 64)).toNat := by
      bv_omega
    have hu0_eq : (ar3.set (cref.setWidth 64).toNat (hdr ||| 524288))[(cref.setWidth 64 +
        (3 : BitVec 64)).toNat]'(by rw [List.length_set, har3_len, hcref3']; omega) =
        ar3[cref.toNat + 3]'(by omega) := by rw [List.getElem_set_ne hne03]; simp only [hcref3']
    have hu0_lt : (ar3[cref.toNat + 3]'(by omega)).toNat < 2 * s_g.core.cur_vars := by
      rw [hms_g.2.1, ← hm2_eq.2.1]; have := hnew_lits_lt 0 (by omega)
      rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
    refine addUnit_call_m4_wp Γ hAddUnit hsp_g hms_g has_g hrr_g (by rwa [hu0_eq])
      (by rw [hu0_eq]; exact range_entails_1 hnsz1 (by omega) hent_new) hm_g ?_ ?_
    · intro s4 m4 hsp4 hm4' ha4 hrr4 hmem4; fv_steps
      exact hQ 1#64 s4 m4 hsp4 hm4'.2.2.1 hm4'.2.1 hm4'.1 hm4'.2.2.2.1 hm4'.2.2.2.2 ha4.1 hrr4
        (Or.inr (Or.inl rfl)) (fun h => by cases h) (fun _ h => by cases h) hmem4
    · intro s4 m4 hsp4 hm4' ha4 hrr4 hu4 hmem4; fv_steps
      exact hQ 20#64 s4 m4 hsp4 hm4'.2.2.1 hm4'.2.1 hm4'.1 hm4'.2.2.2.1 hm4'.2.2.2.2 ha4.1 hrr4
        (Or.inr (Or.inr rfl)) (fun _ => hu4) (fun _ h => by cases h) hmem4
  · have hnsz2 : nsz.toNat = 2 := by c0_bound
    obtain ⟨hlen_u, hw_u, hrefs_u, hnxt_u⟩ := hupd_w (by omega)
    let s_upd : FullState := { s2 with core := { s2.core with arena := ar3 } }
    have hu0_lt : (ar3[(cref.setWidth 64 + 3#64).toNat]'har3_lt3).toNat <
        2 * s_upd.core.cur_vars := by
      simp only [hcref3]; have := hnew_lits_lt 0 (by omega)
      rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
    have hu1_lt : (ar3[(cref.setWidth 64 + 4#64).toNat]'har3_lt4).toNat <
        2 * s_upd.core.cur_vars := by
      simp only [hcref4]; have := hnew_lits_lt 1 (by omega)
      rwa [show cref.toNat + 3 + 1 = cref.toNat + 4 by omega,
        List.getElem?_eq_getElem (by omega), Option.getD_some] at this
    have hbin_ent : (cnfOfClauses F_cur0).EntailsClause
        (cnfClause [(ar3[(cref.setWidth 64 + 3#64).toNat]'har3_lt3).toNat,
                    (ar3[(cref.setWidth 64 + 4#64).toNat]'har3_lt4).toNat]) := by
      simp only [hcref3, hcref4]; simpa [show cref.toNat + 3 + 1 = cref.toNat + 4 by omega] using
        range_entails_2 hnsz2 (by omega) hent_new
    have hext_u : FullExtScratchOk c s_upd := ⟨fun i hi => by
      dsimp only [FullLastLearnedWf, s_upd]; rw [hrefs_u]
      exact hsp2.2.2.2.2.1.1 i hi, hsp2.2.2.2.2.1.2⟩
    c0_call hAddBin
    refine ⟨c, F0, F_cur0, s_upd, R, rfl, hlen_u, hw_u, hsp2.2.2.1, hext_u, hsp2.2.2.2.2.2,
      hm2_eq.2.2.1, hu0_lt, hu1_lt, hbin_ent, hm,
      fun br s4 m4 hlen4 _ hw4 hmc4 hext4 hdm4 har4 halen4 hcv4 hl4 hpr4 hfu4 hrr4 h20 hm4 => ?_⟩
    have har4_len : s4.core.arena.length = c.arena_cap := hlen4.core_ok.arena_len_arr
    have hcref_lt4 : cref.toNat < s4.core.arena.length := by rw [har4_len]; omega
    have hhdr4 : fullArenaHdr s4 cref.toNat = hdr := by
      unfold fullArenaHdr fullArenaHdrCore; rw [har4]; dsimp only [s_upd]
      rw [hout3 cref.toNat (Or.inl (by omega))]; exact hs2_hdr
    fv_steps
    · have hm_g := fullMem_eq_of_arena_ag_eq (a2 := s4.core.arena.set cref.toNat
          (hdr ||| 0x00080000#32)) (by rw [hcref0]; rfl) hm
      obtain ⟨s5, hs5_al, hs5_cv, hs5_pr, hs5_fu, hs5_rr, hsp5, hl5, ha5, hm5⟩ :=
        markGarb_bin_pack_m4 hlen4 hw4 hmc4 hext4 hdm4 hl4 href (hrefs_u.trans hs2_ref) hm2_eq.1
          har4 halen4 hhdr4 (fun r hr hne hngr => hnd_other_ar3 s4 har4 halen4 r
            (by rw [← hrefs_u]; change r ∈ fullArenaClauseRefs s_upd
                unfold fullArenaClauseRefs fullArenaClauseRefsCore at *; rwa [← har4, ← halen4])
            hne hngr) (fun q hq => by
            have h := hnxt_u q (hrefs_u ▸ hq); dsimp only [s_upd] at h ⊢; rwa [hs2_ar] at h) hm_g
      exact hQ 20#64 s5 _ hsp5 hl5 (hs5_cv.trans (hcv4.trans hm2_eq.2.1)) hs5_al
        (hs5_pr.trans (hpr4.trans hm2_eq.2.2.2.1)) (hs5_fu.trans (hfu4.trans hm2_eq.2.2.2.2))
        ha5.1 (hs5_rr.trans (hrr4.trans hrr2)) (Or.inr (Or.inr rfl)) (fun _ => h20 hc)
        (fun _ h => by cases h) hm5
    · have hm_g := fullMem_eq_of_arena_ag_eq (a2 := s4.core.arena.set cref.toNat
          (hdr ||| 0x00080000#32)) (by rw [hcref0]; rfl) hm
      obtain ⟨s5, hs5_al, hs5_cv, hs5_pr, hs5_fu, hs5_rr, hsp5, hl5, ha5, hm5⟩ :=
        markGarb_bin_pack_m4 hlen4 hw4 hmc4 hext4 hdm4 hl4 href (hrefs_u.trans hs2_ref) hm2_eq.1
          har4 halen4 hhdr4 (fun r hr hne hngr => hnd_other_ar3 s4 har4 halen4 r
            (by rw [← hrefs_u]; change r ∈ fullArenaClauseRefs s_upd
                unfold fullArenaClauseRefs fullArenaClauseRefsCore at *; rwa [← har4, ← halen4])
            hne hngr) (fun q hq => by
            have h := hnxt_u q (hrefs_u ▸ hq); dsimp only [s_upd] at h ⊢; rwa [hs2_ar] at h) hm_g
      exact hQ 1#64 s5 _ hsp5 hl5 (hs5_cv.trans (hcv4.trans hm2_eq.2.1)) hs5_al
        (hs5_pr.trans (hpr4.trans hm2_eq.2.2.2.1)) (hs5_fu.trans (hfu4.trans hm2_eq.2.2.2.2))
        ha5.1 (hs5_rr.trans (hrr4.trans hrr2)) (Or.inr (Or.inl rfl)) (fun h => by cases h)
        (fun _ h => by cases h) hm5
  · have hnsz3 : 3 ≤ nsz.toNat := bv32_ge3_of_ne nsz (by c0_bound) (by c0_bound) (by c0_bound)
    have hterm_eq : (cref.setWidth 64 + 3#64 + old_sz.setWidth 64 - 1#64).toNat =
        cref.toNat + 3 + old_sz.toNat - 1 := by bv_omega
    have hterm_lt : (cref.setWidth 64 + 3#64 + old_sz.setWidth 64 - 1#64).toNat < c.arena_cap := by
      have hsz_core : fullArenaClauseSizeCore s2.core cref.toNat = old_sz.toNat := hs2_sz
      have := hsp2.1.core_ok.arena_len_arr; rw [hterm_eq]; omega
    refine wp_join_group
      (fun _ mf => ∃ (ar_f : List (BitVec 32)), ar_f.length = c.arena_cap ∧
        (∀ k, (k < cref.toNat ∨ cref.toNat + 3 + old_sz.toNat ≤ k) →
          ar_f[k]? = s2.core.arena[k]?) ∧
        (ar_f[cref.toNat]?.getD 0#32 &&& 0x00080000#32) = 0#32 ∧
        (ar_f[cref.toNat]?.getD 0#32 &&& 0x00800000#32) ≠ 0#32 ∧
        (ar_f[cref.toNat + 2]?.getD 0#32).toNat = nsz.toNat ∧
        (∀ t < nsz.toNat, ar_f[cref.toNat + 3 + t]? = ar3[cref.toNat + 3 + t]?) ∧
        ShrkPad ar_f s2.core.arena cref.toNat old_sz.toNat nsz.toNat ∧
        (FullMem c { s2 with core := { s2.core with arena := ar_f } } ⋆ R) mf)
      (fun _ _ mf ⟨ar_f, harf_len, hout_f, hng_f, hsh_f, hsz_f, hpay_f, hpad_f, hmf⟩ => by
        obtain ⟨hsp_f, hgb_f, ha_f⟩ := simplify_shrk_sparseInv hsp2 hm2_eq.2.2.1 href2 hs2_ng
          hnsz3 (by omega) harf_len hid_len hid_pw (fun q hq => by have := hid_lt q hq; omega)
          hsub3 hnew_lits_lt hent_new (by simpa [hs2_sz] using hout_f) hng_f hsh_f hsz_f hpay_f
          (by simpa [hs2_sz] using hpad_f)
        let s_f : FullState := { s2 with core := { s2.core with arena := ar_f } }
        have harf_lt3 : (cref.setWidth 64 + 3#64).toNat < s_f.core.arena.length := by
          change (cref.setWidth 64 + 3#64).toNat < ar_f.length; rw [harf_len]; omega
        have harf_lt4 : (cref.setWidth 64 + 4#64).toNat < s_f.core.arena.length := by
          change (cref.setWidth 64 + 4#64).toNat < ar_f.length; rw [harf_len]; omega
        fv_to_grp
        refine wp_join_group
          (fun _ m' => ∃ s' : FullState, FullSparseInvW c F0 F_cur0 s' ∧
            s'.core.arena = s_f.core.arena ∧ VivMetaEq s s' ∧
            fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
            s'.scratch.red_refs = s.scratch.red_refs ∧ (FullMem c s' ⋆ R) m')
          (fun _ _ m' ⟨s', hsp', har', hms', href', hrr', hm'⟩ => by
            fv_steps
            have hgb' : fullArenaClauseGarb s' cref.toNat = false := by
              unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
              rw [har']; exact hgb_f
            exact hQ 0#64 s' m' hsp' hms'.2.2.1 hms'.2.1 hms'.1 hms'.2.2.2.1 hms'.2.2.2.2 href'
              hrr' (Or.inl rfl) (fun h => by cases h) (fun _ _ => ⟨href' ▸ href, hgb'⟩) hm')
          (fun Js hJs => by
            refine watch2_calls_m4_wp Γ hWatchPush hsp_f (by omega) href (ha_f.1.trans hs2_ref)
              hm2_eq hrr2 hmf ?_ ?_
            · intro s' m' a1 a2 a3 a4 a5 a6; fv_steps
              exact hJs () m' ⟨s', a1, a2, a3, a4, a5, a6⟩
            · intro s' m' a1 a2 a3 a4 a5 a6; fv_steps
              exact hJs () m' ⟨s', a1, a2, a3, a4, a5, a6⟩))
      (fun J_shrk hJ_shrk => ?_)
    obtain ⟨hasz_len, hasz_out, hasz_sz, hasz_pay, hasz_pad, hasz_hdr⟩ :=
      ar_set_sz_props (ar0 := ar3) (ar_orig := s2.core.arena) (by omega) hnsz3 hnsz_lt
        (by omega) rfl hcref2 hcref1 hout3
    fv_steps
    · have hsh0 : (hdr &&& 0x00800000#32) = 0#32 := by c0_bound
      obtain ⟨hlf, hout_f, hng_f, hsh_f, hsz_f, hpad_f⟩ :=
        ar_set_shrk_facts (nhdr := hdr) (ar_orig := s2.core.arena) (hasz_len.trans har2_len)
          (by omega) hterm_eq hnsz_lt hnsz3 hhdr_ng hsh0
          (by change (fullArenaHdr s2 cref.toNat &&& _) = _; rw [hs2_hdr])
          hasz_out hasz_sz hasz_pad
      exact hJ_shrk () _ ⟨_, hlf, hout_f, hng_f, hsh_f, hsz_f,
        (fun t ht => by rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
                        exact hasz_pay t ht), hpad_f, hm⟩
    · have hsh_ne : (hdr &&& 0x00800000#32) ≠ 0#32 := by c0_bound
      refine hJ_shrk () _ ⟨_, hasz_len.trans har2_len, hasz_out,
        (by rw [hasz_hdr]; change (fullArenaHdr s2 cref.toNat &&& _) = _
            rw [hs2_hdr]; exact hhdr_ng),
        (by rw [hasz_hdr]; change (fullArenaHdr s2 cref.toNat &&& _) ≠ _
            rw [hs2_hdr]; exact hsh_ne),
        hasz_sz, hasz_pay, (by unfold ShrkPad; rw [ite_eq_right (by
          change (fullArenaHdr s2 cref.toNat &&& 0x00800000#32) ≠ 0#32
          rw [hs2_hdr]; exact hsh_ne)]; exact hasz_pad), hm⟩

private theorem simplify_loop2_m4_wp (Γ : Env) (hAddUnit : HypAddUnitM4 Γ)
    (hAddBin : HypAddBinM4 Γ) (hWatchPush : HypWatchPush Γ) {c : FullCfg} {F0 : CNF Nat}
    {F_cur0 : List (List Nat)} {s s2 : FullState} {R : Mem 64 → Prop} {cref hdr old_sz : Val i32}
    {j0 : Nat} {m2 : Mem 64} {Q : Post [i64]} {X : XPost} (hsp2 : FullSparseInvW c F0 F_cur0 s2)
    (href : cref.toNat ∈ fullArenaClauseRefs s)
    (hs2_ref : fullArenaClauseRefs s2 = fullArenaClauseRefs s)
    (hs2_ng : fullArenaClauseGarb s2 cref.toNat = false) (hs2_ar : s2.core.arena = s.core.arena)
    (hm2_eq : VivMetaEq s s2) (hrr2 : s2.scratch.red_refs = s.scratch.red_refs)
    (hs2_sz : fullArenaClauseSize s2 cref.toNat = old_sz.toNat)
    (hs2_hdr : fullArenaHdr s2 cref.toNat = hdr) (hhdr_ng : (hdr &&& 0x00080000#32) = 0#32)
    (hsz3 : 3 ≤ old_sz.toNat) (har2_bd : cref.toNat + 3 + old_sz.toNat ≤ s2.core.arena.length)
    (hj0_lt : j0 < old_sz.toNat) (hj0_ff2 :
      s2.core.vals[(s2.core.arena[cref.toNat + 3 + j0]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8)
    (hno1_2 : ∀ j < old_sz.toNat,
      s2.core.vals[(s2.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat]?.getD 0#8 ≠ 1#8)
    (hlit2_lt : ∀ (j : Nat) (_hj : j < old_sz.toNat),
      (s2.core.arena[cref.toNat + 3 + j]'(by omega)).toNat < 2 * s2.core.cur_vars)
    (hm2 : (FullMem c s2 ⋆ R) m2) (hQv : VivM4Q c F0 F_cur0 s R Q cref.toNat true) :
    wp Γ Q X (simplifyLoop2ExprM4 c cref hdr old_sz) m2 := by
  have hcl := hsp2.1.core_ok; have har2_len := hcl.arena_len_arr
  have hv2_len := hcl.vals_len; have hcv2_le := hcl.cur_vars_le; have halen_le := hcl.arena_len_le
  have hcap := c.harena; have hmx := c.hmaxv; unfold dimacsBound at hcap hmx
  dsimp only [simplifyLoop2ExprM4, arLitPtr, fvOp]
  refine wp_loop_inv
    (fun (i2, nsz, ()) m3 => ∃ (ar3 : List (BitVec 32)) (idxs : List Nat),
      i2.toNat ≤ old_sz.toNat ∧ nsz.toNat ≤ i2.toNat ∧ (j0 < i2.toNat → nsz.toNat < i2.toNat) ∧
      ar3.length = c.arena_cap ∧ (∀ p, (p < cref.toNat + 3 ∨ cref.toNat + 3 + nsz.toNat ≤ p) →
        ar3[p]? = s2.core.arena[p]?) ∧ idxs.length = nsz.toNat ∧ idxs.Pairwise (· < ·) ∧
      (∀ q ∈ idxs, q < i2.toNat) ∧ (∀ t < nsz.toNat,
        ar3[cref.toNat + 3 + t]? = s2.core.arena[cref.toNat + 3 + idxs[t]?.getD 0]?) ∧
      (∀ j < i2.toNat,
        s2.core.vals[(s2.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat]?.getD 0#8 = 0#8 →
        ∃ t < nsz.toNat, ar3[cref.toNat + 3 + t]? = s2.core.arena[cref.toNat + 3 + j]?) ∧
      (FullMem c { s2 with core := { s2.core with arena := ar3 } } ⋆ R) m3)
    (fun (i2, _, ()) _ => old_sz.toNat - i2.toNat)
    (fun J2 hJ2 => by fv_steps; exact hJ2 (0#32, 0#32, ()) m2 ⟨s2.core.arena, [], by simp,
      by simp, fun h => by simp at h, har2_len, fun _ _ => rfl, rfl, .nil,
      fun _ h => by simp at h, fun _ h => by simp at h, fun _ h => by simp at h, hm2⟩)
    (fun J2 (i2, nsz, ()) m3 ⟨ar3, idxs, hi2_le, hnsz_le, hlt_j0, har3_len, hout3, hid_len,
         hid_pw, hid_lt, hsub3, hcov3, hm3⟩ ih2 => ?_)
  fv_while
  · have hi2_lt : i2.toNat < old_sz.toNat := by c0_bound
    have hi2_idx : (cref.setWidth 64 + 3#64 + i2.setWidth 64).toNat =
        cref.toNat + 3 + i2.toNat := by bv_omega
    have hmod3i2 : (cref.toNat + BitVec.toNat (3 : BitVec 64) + i2.toNat) % 2 ^ 64 =
        cref.toNat + 3 + i2.toNat := by
      rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl]; exact Nat.mod_eq_of_lt (by omega)
    have har3_i2_lt : cref.toNat + 3 + i2.toNat < ar3.length := by omega
    have hs2_i2_lt : cref.toNat + 3 + i2.toNat < s2.core.arena.length := by omega
    have hi2_lt_ar : (cref.setWidth 64 + 3#64 + i2.setWidth 64).toNat < ar3.length := by omega
    have hnsz_idx : (cref.setWidth 64 + 3#64 + nsz.setWidth 64).toNat =
        cref.toNat + 3 + nsz.toNat := by bv_omega
    have hnsz_lt_ar : (cref.setWidth 64 + 3#64 + nsz.setWidth 64).toNat < ar3.length := by omega
    have hlit2_eq : ar3[cref.toNat + 3 + i2.toNat]'har3_i2_lt =
        s2.core.arena[cref.toNat + 3 + i2.toNat]'hs2_i2_lt := by
      have := hout3 (cref.toNat + 3 + i2.toNat) (Or.inr (by omega))
      rw [List.getElem?_eq_getElem har3_i2_lt, List.getElem?_eq_getElem hs2_i2_lt] at this
      exact Option.some.inj this
    have hlit2_v : (ar3[cref.toNat + 3 + i2.toNat]'har3_i2_lt).toNat < 2 * s2.core.cur_vars := by
      rw [hlit2_eq]; exact hlit2_lt i2.toNat hi2_lt
    have hlit2_vlt : (ar3[(cref.setWidth 64 + 3#64 + i2.setWidth 64).toNat]'hi2_lt_ar).toNat <
        s2.core.vals.length := by
      rw [show ar3[(cref.setWidth 64 + 3#64 + i2.setWidth 64).toNat]'hi2_lt_ar =
        ar3[cref.toNat + 3 + i2.toNat]'har3_i2_lt by simp only [hi2_idx]]; omega
    have hi2_1 : (i2 + 1#32).toNat = i2.toNat + 1 := by bv_omega
    fv_steps
    · have hv0 : s2.core.vals[(s2.core.arena[cref.toNat + 3 + i2.toNat]?.getD 0#32).toNat]?.getD
          0#8 = 0#8 := by
        rw [List.getElem?_eq_getElem hs2_i2_lt, Option.getD_some, ← hlit2_eq,
          List.getElem?_eq_getElem (by rw [hv2_len]; omega), Option.getD_some]
        simp only [hmod3i2] at hc; exact (bv8_sext32_eq0_iff _).mp hc
      have hi2_ne_j0 : i2.toNat ≠ j0 := fun h => by subst h; rw [hv0] at hj0_ff2; cases hj0_ff2
      have hnsz1 : (nsz + 1#32).toNat = nsz.toNat + 1 := by bv_omega
      let lit2 := ar3[cref.toNat + 3 + i2.toNat]'har3_i2_lt
      let ar4 := ar3.set (cref.toNat + 3 + nsz.toNat) lit2
      have har4_eq : ar3.set (cref.setWidth 64 + 3#64 + nsz.setWidth 64).toNat
          (ar3[(cref.setWidth 64 + 3#64 + i2.setWidth 64).toNat]'hi2_lt_ar) = ar4 := by
        simp only [ar4, lit2, hnsz_idx, hi2_idx]
      refine ih2 (i2 + 1#32, nsz + 1#32, ()) _ (by dsimp only; omega)
        ⟨ar4, idxs ++ [i2.toNat], by omega, by omega, fun hj => by omega,
         by simp [ar4, har3_len], fun p hp => ?_, by simp [hid_len, hnsz1], ?_, ?_, ?_, ?_,
         fullMem_eq_of_arena_eq har4_eq hm⟩
      · dsimp only [ar4]; rw [List.getElem?_set_ne (by omega)]; exact hout3 p (by omega)
      · exact List.pairwise_append.mpr ⟨hid_pw, List.pairwise_singleton _ _,
          fun a ha b hb => by simp at hb; subst hb; exact hid_lt a ha⟩
      · intro q hq; simp at hq
        exact hq.elim (fun h => Nat.lt_trans (hid_lt q h) (by omega)) (fun h => by omega)
      · intro t ht; by_cases htn : t = nsz.toNat
        · subst htn; dsimp only [ar4]; rw [List.getElem?_set_self (by omega)]
          have hget_id : (idxs ++ [i2.toNat])[nsz.toNat]?.getD 0 = i2.toNat := by
            rw [List.getElem?_append_right (by omega), show nsz.toNat - idxs.length = 0 by omega]
            rfl
          rw [hget_id, List.getElem?_eq_getElem hs2_i2_lt]; dsimp only [lit2]; rw [hlit2_eq]
        · dsimp only [ar4]; rw [List.getElem?_set_ne (by omega),
            List.getElem?_append_left (by omega)]; exact hsub3 t (by omega)
      · intro j hj hvj; rcases (by omega : j < i2.toNat ∨ j = i2.toNat) with hj' | rfl
        · obtain ⟨t, ht, hteq⟩ := hcov3 j hj' hvj
          exact ⟨t, by omega, by dsimp only [ar4]; rw [List.getElem?_set_ne (by omega)]; exact hteq⟩
        · refine ⟨nsz.toNat, by omega, ?_⟩; dsimp only [ar4]
          rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem hs2_i2_lt]
          dsimp only [lit2]; rw [hlit2_eq]
    · have hvne0 : s2.core.vals[(s2.core.arena[cref.toNat + 3 + i2.toNat]?.getD 0#32).toNat]?.getD
          0#8 ≠ 0#8 := fun h0 => by
        rw [List.getElem?_eq_getElem hs2_i2_lt, Option.getD_some, ← hlit2_eq,
          List.getElem?_eq_getElem (by rw [hv2_len]; omega), Option.getD_some] at h0
        simp only [hmod3i2] at hc; exact hc ((bv8_sext32_eq0_iff _).mpr h0)
      refine ih2 (i2 + 1#32, nsz, ()) m3 (by dsimp only; omega)
        ⟨ar3, idxs, by omega, by omega, fun hj => by omega, har3_len, hout3, hid_len, hid_pw,
         fun q hq => Nat.lt_trans (hid_lt q hq) (by omega), hsub3, fun j hj hvj =>
         (by omega : j < i2.toNat ∨ j = i2.toNat).elim (fun h => hcov3 j h hvj)
           (fun h => absurd (h ▸ hvj) hvne0), hm3⟩
  · have hi2_eq : i2.toNat = old_sz.toNat := by c0_bound
    have hnsz_lt : nsz.toNat < old_sz.toNat := by have := hlt_j0 (by omega); omega
    exact simplify_post_loop2_m4_wp Γ hAddUnit hAddBin hWatchPush hsp2 href hs2_ref hs2_ng
      hs2_ar hm2_eq hrr2 hs2_sz hs2_hdr hhdr_ng hnsz_lt har3_len hout3 hid_len hid_pw
      (fun q hq => by have := hid_lt q hq; omega) hsub3 (fun j hj => hcov3 j (by omega))
      (fun j hj => hno1_2 j (by omega)) hm3 hQv

/-- `red_refs`-preserving `Func.wp` proof for unmodified `Full3.full_viv_simplify_body`. -/
theorem full_viv_simplify_m4_wp (Γ : Env)
    (hUnwatchC : ∀ a m Q X, fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    (hAddUnitC : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hAddBinC : ∀ a m Q X, fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X)
    (hWatchPushC : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullVivSimplifyM4Spec a m Q X →
      Func.wp Γ full_viv_simplify_body a m Q X := by
  have hUnwatch := vivUnwatchM4_adapter hUnwatchC
  have hAddUnit := vivAddUnitM4_adapter hAddUnitC
  have hAddBin := vivAddBinM4_adapter hAddBinC
  have hWatchPush := vivWatchPushM4_adapter hWatchPushC
  rintro ⟨h, cref, ⟨⟩⟩ m Q X ⟨c, F0, F_cur0, s, R, rfl, hsp, hl0, href, hng, hm, hQ⟩
  have hQv : VivM4Q c F0 F_cur0 s R Q cref.toNat true :=
    fun r s' m' hsp' hl' hcv' hal' hpr' hfu' href' hrr' hr h20 h0 =>
      hQ r s' m' hsp' hl' hcv' hal' hpr' hfu' href' hrr' hr h20 (h0 rfl)
  have hw0 := hsp.2.1; have hcl := hsp.1.core_ok
  have hcap := c.harena; have hmx := c.hmaxv; unfold dimacsBound at hcap hmx
  have har_len := hcl.arena_len_arr; have halen_le := hcl.arena_len_le
  have hcv_le := hcl.cur_vars_le; have hv_len := hcl.vals_len
  have hcref_wf := hw0.arena.refs_wf cref.toNat href
  obtain ⟨hcref_lt, hmod2, hcref0_eq, hcref1_eq, hcref2_eq, hcref3_eq, hcref4_eq, hhdr_ng_raw⟩ :=
    cref_hdr_facts (fv_sparseW_to_sparse hsp) hw0 href hng
  let hdr := s.core.arena[(cref.setWidth 64).toNat]'(by rw [hcref0_eq]; exact hcref_lt)
  let old_sz := s.core.arena[(cref.setWidth 64 + 2#64).toNat]'(by rw [hcref2_eq]; omega)
  have hhdr_eq : hdr = fullArenaHdr s cref.toNat := ar_get_eq_getD hcref0_eq _
  have hold_sz_eq : old_sz.toNat = fullArenaClauseSizeCore s.core cref.toNat :=
    congrArg BitVec.toNat (ar_get_eq_getD hcref2_eq _)
  have hold_sz_3 : 3 ≤ old_sz.toNat := by rw [hold_sz_eq]; exact hcref_wf.2.1
  have hold_sz_bd : cref.toNat + 3 + old_sz.toNat ≤ s.core.arena.length := by
    rw [hold_sz_eq]; omega
  have hhdr_ng : (hdr &&& 0x00080000#32) = 0#32 := by
    simpa [hhdr_eq, fullArenaHdr, fullArenaHdrCore] using hhdr_ng_raw
  have hcref3_lt : (cref.setWidth 64 + 3#64).toNat < s.core.arena.length := by omega
  have hcref4_lt : (cref.setWidth 64 + 4#64).toNat < s.core.arena.length := by omega
  have hsz_s_eq : fullArenaClauseSize s cref.toNat = old_sz.toNat := hold_sz_eq.symm
  have hlit_lt : ∀ (j : Nat) (_hj : j < old_sz.toNat),
      (s.core.arena[cref.toNat + 3 + j]'(by omega)).toNat < 2 * s.core.cur_vars := fun j hj =>
    hw0.arena.lits_lt cref.toNat href hng _
      ((mem_fullArenaClauseLitsCore_iff (by omega)).mpr ⟨j, by rw [← hold_sz_eq]; exact hj, rfl⟩)
  fv_steps
  refine wp_loop_inv
    (fun (k, i, ()) m1 => m1 = m ∧ i.toNat ≤ old_sz.toNat ∧ k.toNat ≤ i.toNat ∧
      (∀ j < i.toNat, s.core.vals[(s.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat]?.getD
        0#8 ≠ 1#8) ∧ (k.toNat < i.toNat → ∃ j0 < i.toNat,
        s.core.vals[(s.core.arena[cref.toNat + 3 + j0]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8))
    (fun (_, i, ()) _ => old_sz.toNat - i.toNat)
    (fun J1 hJ1 => by fv_steps; exact hJ1 (0#32, 0#32, ()) m ⟨rfl, by simp, by simp,
      fun _ hj => by simp at hj, fun hlt => by simp at hlt⟩)
    (fun J1 (k, i, ()) m1 ⟨hm1, hi_le, hk_le, hno1, hhasf⟩ ih1 => ?_)
  subst hm1; fv_while
  · have hi_lt : i.toNat < old_sz.toNat := by dsimp only [old_sz]; c0_bound
    have hidx_eq : (cref.setWidth 64 + 3#64 + i.setWidth 64).toNat =
        cref.toNat + 3 + i.toNat := by bv_omega
    have hmod3i : (cref.toNat + BitVec.toNat (3 : BitVec 64) + i.toNat) % 2 ^ 64 =
        cref.toNat + 3 + i.toNat := by
      rw [show BitVec.toNat (3 : BitVec 64) = 3 from rfl]; exact Nat.mod_eq_of_lt (by omega)
    have hidx_lt : (cref.setWidth 64 + 3#64 + i.setWidth 64).toNat < s.core.arena.length := by
      omega
    let lit := s.core.arena[cref.toNat + 3 + i.toNat]'(by omega)
    have hlit_getD : s.core.arena[cref.toNat + 3 + i.toNat]?.getD 0#32 = lit := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    have hlit_v : lit.toNat < 2 * s.core.cur_vars := hlit_lt i.toNat hi_lt
    have hlit_vlt : (s.core.arena[(cref.setWidth 64 + 3#64 + i.setWidth 64).toNat]'hidx_lt).toNat <
        s.core.vals.length := by
      rw [show s.core.arena[(cref.setWidth 64 + 3#64 + i.setWidth 64).toNat]'hidx_lt = lit by
        simp only [lit, hidx_eq]]; omega
    have hdom := hw0.vals_domain lit.toNat hlit_v
    have hv_get : s.core.vals[lit.toNat]'(by omega) = s.core.vals[lit.toNat]?.getD 0#8 := by
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    have hi1_eq : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
    fv_steps
    · c0_call hUnwatch
      refine ⟨c, F0, F_cur0, s, R, rfl, fv_sparseW_to_sparse hsp, hw0, hm,
        fun wvec1 wstk1 wu1 m2 hsp1 hw1 hm2 => ?_⟩
      have hcref4_lt1 : (cref.setWidth 64 + 4#64).toNat < ({ s with core :=
          { s.core with wvec := wvec1, wstk := wstk1, wusable := wu1 } } :
          FullState).core.arena.length := hcref4_lt
      fv_steps; c0_call hUnwatch
      refine ⟨c, F0, F_cur0, _, R, rfl, hsp1, hw1, hm2, fun wvec2 wstk2 wu2 m3 hsp2w hw2 hm3 => ?_⟩
      fv_steps
      have hsp2W : FullSparseInvW c F0 F_cur0 { s with core :=
          { s.core with wvec := wvec2, wstk := wstk2, wusable := wu2 } } :=
        ⟨hsp2w.1.lengths, hw2, hsp2w.2.1, hsp2w.2.2.1, hsp2w.2.2.2.1, hsp2w.2.2.2.2⟩
      obtain ⟨hsp3, hrefs3, _⟩ :=
        fv_markGarbW hsp2W hl0 href (s.core.arena_garbage + 3#64 + old_sz.setWidth 64)
      have har_eq := congrArg (fun x => s.core.arena.set cref.toNat (x ||| 0x00080000#32)) hhdr_eq
      exact hQv 1#64 _ _ hsp3 hl0 rfl rfl rfl rfl hrefs3 rfl (Or.inr (Or.inl rfl))
        (fun h => by cases h) (fun _ h => by cases h) (fullMem_eq_of_arena_ag_eq har_eq hm)
    · have hne1 : s.core.vals[lit.toNat]?.getD 0#8 ≠ 1#8 := by
        simp only [hmod3i] at hc; rw [← hv_get, (bv8_sext32_eq0_iff _).mp hc]; decide
      have hk1_eq : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
      refine ih1 (k + 1#32, i + 1#32, ()) m1 (by dsimp only; omega)
        ⟨rfl, by omega, by omega, fun j hj => (by omega : j < i.toNat ∨ j = i.toNat).elim
          (hno1 j) (fun h => by rw [h, hlit_getD]; exact hne1),
         fun hlt => by obtain ⟨j0, hj0, hf0⟩ := hhasf (by omega); exact ⟨j0, by omega, hf0⟩⟩
    · rename_i hc_slt
      have hne1 : s.core.vals[lit.toNat]?.getD 0#8 ≠ 1#8 := fun heq => by
        have h1 : s.core.vals[lit.toNat]'(by omega) = 1#8 := hv_get.trans heq
        simp only [hmod3i] at hc_slt; rw [h1] at hc_slt; revert hc_slt; decide
      have hff : s.core.vals[lit.toNat]?.getD 0#8 = 0xFF#8 := by
        rcases hdom with h0 | h1 | hff
        · exfalso; have h0' : s.core.vals[lit.toNat]'(by omega) = 0#8 := hv_get.trans h0
          simp only [hmod3i] at hc; exact hc ((bv8_sext32_eq0_iff _).mpr h0')
        · exact absurd h1 hne1
        · exact hff
      refine ih1 (k, i + 1#32, ()) m1 (by dsimp only; omega)
        ⟨rfl, by omega, by omega, fun j hj => (by omega : j < i.toNat ∨ j = i.toNat).elim
          (hno1 j) (fun h => by rw [h, hlit_getD]; exact hne1),
         fun _ => ⟨i.toNat, by omega, by rwa [hlit_getD]⟩⟩
  · have hi_eq : i.toNat = old_sz.toNat := by dsimp only [old_sz] at hi_le ⊢; c0_bound
    clear hc; fv_steps
    · exact hQv 0#64 s m1 hsp hl0 rfl rfl rfl rfl rfl rfl (Or.inl rfl) (fun h => by cases h)
        (fun _ _ => ⟨href, hng⟩) hm
    · have hk_lt : k.toNat < old_sz.toNat := by
        have hne : k.toNat ≠ old_sz.toNat :=
          fun h => (by dsimp only [old_sz]; c0_bound : k ≠ old_sz) (BitVec.eq_of_toNat_eq h)
        omega
      obtain ⟨j0, hj0_lt, hj0_ff⟩ := hhasf (by omega)
      c0_call hUnwatch
      refine ⟨c, F0, F_cur0, s, R, rfl, fv_sparseW_to_sparse hsp, hw0, hm,
        fun wvec1 wstk1 wu1 m1' hsp1 hw1 hm1' => ?_⟩
      have hcref4_lt1 : (cref.setWidth 64 + 4#64).toNat < ({ s with core :=
          { s.core with wvec := wvec1, wstk := wstk1, wusable := wu1 } } :
          FullState).core.arena.length := hcref4_lt
      fv_steps; c0_call hUnwatch
      refine ⟨c, F0, F_cur0, _, R, rfl, hsp1, hw1, hm1',
        fun wvec2 wstk2 wu2 m2 hsp2w hw2w hm2w => ?_⟩
      obtain ⟨s2, hs2_ar, hs2_v, _, hrr2, hm2_eq, hs2_ref, hs2_ng, hs2_sz, hs2_hdr, hsp2, hm2⟩ :=
        unwatch2_state_pack_m4 hsp2w hw2w hm2w hng hsz_s_eq hhdr_eq rfl rfl rfl rfl hl0 rfl rfl
          rfl rfl
      have hno1_2 : ∀ j < old_sz.toNat,
          s2.core.vals[(s2.core.arena[cref.toNat + 3 + j]?.getD 0#32).toNat]?.getD 0#8 ≠ 1#8 :=
        fun j hj => by rw [hs2_v, hs2_ar]; exact hno1 j (by omega)
      have hj0_ff2 : s2.core.vals[(s2.core.arena[cref.toNat + 3 + j0]?.getD 0#32).toNat]?.getD
          0#8 = 0xFF#8 := by rw [hs2_v, hs2_ar]; exact hj0_ff
      have har2_bd : cref.toNat + 3 + old_sz.toNat ≤ s2.core.arena.length := by
        rw [hs2_ar]; exact hold_sz_bd
      have hcref2_mem : cref.toNat ∈ fullArenaClauseRefsCore s2.core := by
        change cref.toNat ∈ fullArenaClauseRefs s2; rw [hs2_ref]; exact href
      have hsz_c2 : fullArenaClauseSizeCore s2.core cref.toNat = old_sz.toNat := hs2_sz
      have hlit2_lt : ∀ (j : Nat) (_hj : j < old_sz.toNat),
          (s2.core.arena[cref.toNat + 3 + j]'(by omega)).toNat < 2 * s2.core.cur_vars :=
        fun j hj => hsp2.2.1.arena.lits_lt cref.toNat hcref2_mem hs2_ng _
          ((mem_fullArenaClauseLitsCore_iff (by omega)).mpr ⟨j, by rw [hsz_c2]; exact hj, rfl⟩)
      fv_steps
      exact simplify_loop2_m4_wp Γ hAddUnit hAddBin hWatchPush hsp2 href hs2_ref hs2_ng hs2_ar
        hm2_eq hrr2 hs2_sz hs2_hdr hhdr_ng hold_sz_3 har2_bd (lt_of_lt_of_eq hj0_lt hi_eq)
        hj0_ff2 hno1_2 hlit2_lt hm2 hQv

/-! ## 5. `red_refs`-preserving `full_viv_commit_m4_wp` -/

private abbrev commitShrkTailBlockM4 (c : FullCfg) (cref : Val i32) :
    Blocks Val Cont [i64] [[i32]] :=
  Blocks.cons (fun (p : Tup Val [i32]) => arBasePtr c.pArena cref fun p_3 =>
    Expr.store (Arg.var p.fst) (Arg.var p_3)
      (fvOp (OpCode.sext 32 64) (Arg.imm 0, ()) fun p =>
       fvOp (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
       fvOp (OpCode.add i64) (Arg.var c.pWorkStk2, Arg.var p.fst, ()) fun p =>
       Expr.load i32 (Arg.var p.fst) fun ld =>
       fvOp (OpCode.sext 32 64) (Arg.imm 1, ()) fun p =>
       fvOp (OpCode.mul i64) (Arg.var p.fst, Arg.imm 4, ()) fun p =>
       fvOp (OpCode.add i64) (Arg.var c.pWorkStk2, Arg.var p.fst, ()) fun p =>
       Expr.load i32 (Arg.var p.fst) fun ld_1 =>
       watch2Expr c.hdr cref ld ld_1 (Expr.ret (Arg.imm 1, ())) (Expr.ret (Arg.imm 2, ()))))
    Blocks.nil

private theorem commit_shrk_mid_m4_wp (Γ : Env) (hWatchPush : HypWatchPush Γ)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s s3 : FullState}
    {R : Mem 64 → Prop} {cref olen old_sz : Val i32} {hdr nhdr : BitVec 32}
    {ni1 nr1 : BitVec 64} {ar_sz : List (BitVec 32)} {m5 : Mem 64} {Q : Post [i64]} {X : XPost}
    (hsp3 : FullSparseInvW c F0 F_cur s3)
    (href : cref.toNat ∈ fullArenaClauseRefs s)
    (hs3_ref : fullArenaClauseRefs s3 = fullArenaClauseRefs s)
    (hs3_ng : fullArenaClauseGarb s3 cref.toNat = false) (hs3_ar : s3.core.arena = s.core.arena)
    (hm3_eq : VivMetaEq s s3) (hs3_ws2 : s3.scratch.work_stk2 = s.scratch.work_stk2)
    (hrr3 : s3.scratch.red_refs = s.scratch.red_refs)
    (hs3_sz : fullArenaClauseSize s3 cref.toNat = old_sz.toNat)
    (hs3_hdr : fullArenaHdr s3 cref.toNat = hdr)
    (holen3 : 3 ≤ olen.toNat) (holen_lt : olen.toNat < old_sz.toNat)
    (holen_le : olen.toNat ≤ 2 * c.max_vars)
    (hout_lt : ∀ j < olen.toNat, (s.scratch.work_stk2[j]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hout_nd : (((s.scratch.work_stk2.take olen.toNat).map BitVec.toNat).map (· / 2)).Nodup)
    (hout_ent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s.scratch.work_stk2.take olen.toNat).map BitVec.toNat)))
    (hasz_cap : ar_sz.length = c.arena_cap) (hng_nh : (nhdr &&& 0x00080000#32) = 0#32)
    (hsh_nh : (nhdr &&& 0x00800000#32) = (hdr &&& 0x00800000#32))
    (hasz_out : ∀ k, (k < cref.toNat ∨ cref.toNat + 3 + old_sz.toNat ≤ k) →
      ar_sz[k]? = s3.core.arena[k]?)
    (hasz_sz : (ar_sz[cref.toNat + 2]?.getD 0#32).toNat = olen.toNat)
    (hcp_sz : ∀ j < olen.toNat, ar_sz[cref.toNat + 3 + j]? = s3.scratch.work_stk2[j]?)
    (hasz_pad : ∀ k, cref.toNat + 3 + olen.toNat ≤ k → k < cref.toNat + 3 + old_sz.toNat →
      ar_sz[k]? = s3.core.arena[k]?)
    (hm5 : (FullMem c { s3 with core := { s3.core with
      arena := ar_sz, num_irred := ni1, num_redundant := nr1 } } ⋆ R) m5)
    (hQ : VivM4Q c F0 F_cur s R Q cref.toNat false) :
    wp Γ Q X ((Blocks.cons (fun (p : Tup Val [i32]) =>
      Expr.group (sig := [[i32]]) (fun _ => commitShrkTailBlockM4 c cref) fun Js =>
      fvOp (OpCode.and i32) (Arg.var p.fst, Arg.imm 8388608, ()) fun p1 =>
      fvOp (OpCode.cmp .eq i32 .bool rfl) (Arg.var p1.fst, Arg.imm 0, ()) fun p2 =>
      Expr.jnz (Arg.var p2.fst) (storeTermExpr c.pArena cref old_sz
        (fvOp (OpCode.or i32) (Arg.var p.fst, Arg.imm 8388608, ())
          fun q => Expr.jump Js.fst (Arg.var q.fst, ())))
        (Expr.jump Js.fst (Arg.var p.fst, ()))) Blocks.nil).get Member.here (nhdr, ())) m5 := by
  have hw3 := hsp3.2.1; have hcl := hsp3.1.core_ok; have har3_len := hcl.arena_len_arr
  have hscl := hsp3.1.scratch_ok; have hws2_3 := hscl.work_stk2_len
  have hle := hcl.arena_len_le; have hcap := c.harena; have hmx := c.hmaxv
  unfold dimacsBound at hcap hmx
  have href3 : cref.toNat ∈ fullArenaClauseRefs s3 := by rw [hs3_ref]; exact href
  have hwf := hw3.arena.refs_wf cref.toNat href3
  have hsz_core : fullArenaClauseSizeCore s3.core cref.toNat = old_sz.toNat := hs3_sz
  have hterm_eq : (cref.setWidth 64 + 3#64 + old_sz.setWidth 64 - 1#64).toNat =
      cref.toNat + 3 + old_sz.toNat - 1 := by bv_omega
  have hterm_lt : (cref.setWidth 64 + 3#64 + old_sz.setWidth 64 - 1#64).toNat < ar_sz.length := by
    rw [hterm_eq, hasz_cap]; omega
  dsimp only [storeTermExpr, fvOp]; fv_to_grp
  refine wp_join_group
    (fun (nhdr2, ()) m6 => ∃ ar_p : List (BitVec 32), ar_p.length = c.arena_cap ∧
      (nhdr2 &&& 0x00080000#32) = 0#32 ∧ (nhdr2 &&& 0x00800000#32) ≠ 0#32 ∧
      (∀ k, (k < cref.toNat ∨ cref.toNat + 3 + old_sz.toNat ≤ k) → ar_p[k]? = s3.core.arena[k]?) ∧
      (ar_p[cref.toNat + 2]?.getD 0#32).toNat = olen.toNat ∧
      (∀ j < olen.toNat, ar_p[cref.toNat + 3 + j]? = s3.scratch.work_stk2[j]?) ∧
      ShrkPad ar_p s3.core.arena cref.toNat old_sz.toNat olen.toNat ∧
      (FullMem c { s3 with core := { s3.core with
        arena := ar_p, num_irred := ni1, num_redundant := nr1 } } ⋆ R) m6)
    (fun _ (nhdr2, ()) m6 ⟨ar_p, harp_len, hng2, hsh2, hout_p, hsz_p, hpay_p, hpad_p, hm6⟩ => by
      have hcref_ltp : cref.toNat < ar_p.length := by rw [harp_len]; omega
      have hcref_lt8 : cref.toNat < 0x80000000 := by omega
      have h0_ws2 : 0 < s3.scratch.work_stk2.length := by rw [hws2_3]; omega
      have h1_ws2 : 1 < s3.scratch.work_stk2.length := by rw [hws2_3]; omega
      obtain ⟨hsp_f, ha_f⟩ := commit_shrk_sparseInv hsp3 hm3_eq.2.2.1 href3 hs3_ng holen3
        (by omega) (by omega) (by simpa [hs3_ws2, hm3_eq.2.1] using hout_lt)
        (by simpa [hs3_ws2] using hout_nd) (by simpa [hs3_ws2] using hout_ent) harp_len hng2 hsh2
        (by simpa [hs3_sz] using hout_p) hsz_p hpay_p (by simpa [hs3_sz] using hpad_p)
      let s_f : FullState := { s3 with core := { s3.core with
        arena := ar_p.set cref.toNat nhdr2, num_irred := ni1, num_redundant := nr1 } }
      have has_f : VivArenaEq s s_f :=
        ⟨ha_f.1.trans hs3_ref, fun q hq => by
          have := ha_f.2 q (by rw [hs3_ref]; exact hq); rwa [hm3_eq.1, hs3_ar] at this⟩
      dsimp only [commitShrkTailBlockM4, arBasePtr, fvOp]; fv_steps
      refine watch2_calls_m4_wp Γ hWatchPush hsp_f hcref_lt8 href has_f.1 hm3_eq hrr3 hm ?_ ?_
      · intro s' m' hsp' har' hm' href' hrr' hm''; fv_steps
        exact hQ 1#64 s' m' hsp' hm'.2.2.1 hm'.2.1 hm'.1 hm'.2.2.2.1 hm'.2.2.2.2 href' hrr'
          (Or.inl rfl) (fun h => by cases h) (fun h => by cases h) hm''
      · intro s' m' hsp' har' hm' href' hrr' hm''; fv_steps
        exact hQ 2#64 s' m' hsp' hm'.2.2.1 hm'.2.1 hm'.1 hm'.2.2.2.1 hm'.2.2.2.2 href' hrr'
          (Or.inr (Or.inl rfl)) (fun h => by cases h) (fun h => by cases h) hm'')
    (fun J_shrk hJ_shrk => ?_)
  fv_steps
  · have hsh0 : (nhdr &&& 0x00800000#32) = 0#32 := by c0_bound
    let term := (cref.setWidth 64 + 3#64 + old_sz.setWidth 64 - 1#64).toNat
    refine hJ_shrk (nhdr ||| 0x00800000#32, ()) _
      ⟨ar_sz.set term 0xFFFFFFFF#32, by simp [hasz_cap], by rw [bv32_or_shrk_garb, hng_nh],
       bv32_or_shrk_ne0 nhdr,
       fun k hk => by rw [List.getElem?_set_ne (by omega)]; exact hasz_out k hk,
       by rw [List.getElem?_set_ne (by omega)]; exact hasz_sz,
       fun j hj => by rw [List.getElem?_set_ne (by omega)]; exact hcp_sz j hj,
       by unfold ShrkPad
          rw [ite_eq_left (by change (fullArenaHdr s3 cref.toNat &&& 0x00800000#32) = 0#32
                              rw [hs3_hdr, ← hsh_nh, hsh0])]
          exact ⟨fun k hk1 hk2 => by rw [List.getElem?_set_ne (by omega)]
                                     exact hasz_pad k hk1 (by omega),
            by rw [show cref.toNat + 3 + old_sz.toNat - 1 = term by omega]
               exact List.getElem?_set_self (by omega)⟩, hm⟩
  · have hsh_ne : (nhdr &&& 0x00800000#32) ≠ 0#32 := by c0_bound
    refine hJ_shrk (nhdr, ()) m5 ⟨ar_sz, hasz_cap, hng_nh, hsh_ne, hasz_out, hasz_sz, hcp_sz,
      by unfold ShrkPad
         rw [ite_eq_right (by change (fullArenaHdr s3 cref.toNat &&& 0x00800000#32) ≠ 0#32
                              rw [hs3_hdr, ← hsh_nh]; exact hsh_ne)]
         exact hasz_pad, hm5⟩

/-- `red_refs`-preserving `Func.wp` proof for unmodified `Full3.full_viv_commit_body`. -/
theorem full_viv_commit_m4_wp (Γ : Env)
    (hUnwatchC : ∀ a m Q X, fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    (hAddUnitC : ∀ a m Q X, fullAddUnitSpec a m Q X →
      Γ "full_add_unit" [i64, i32] [.bool] a m Q X)
    (hAddBinC : ∀ a m Q X, fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X)
    (hWatchPushC : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X) :
    ∀ a m Q X, fullVivCommitM4Spec a m Q X →
      Func.wp Γ full_viv_commit_body a m Q X := by
  have hUnwatch := vivUnwatchM4_adapter hUnwatchC
  have hAddUnit := vivAddUnitM4_adapter hAddUnitC
  have hAddBin := vivAddBinM4_adapter hAddBinC
  have hWatchPush := vivWatchPushM4_adapter hWatchPushC
  rintro ⟨h, cref, out_ptr, olen, used_red, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, rfl, hsp, hl0, href, hng, holen_le_mv, hout_ok, hm, hQ⟩
  have hQv : VivM4Q c F0 F_cur s R Q cref.toNat false :=
    fun r s' m' hsp' hl' hcv' hal' hpr' hfu' href' hrr' hr h20 _ =>
      hQ r s' m' hsp' hl' hcv' hal' hpr' hfu' href' hrr' hr h20
  have hw := hsp.2.1; have hcl := hsp.1.core_ok; have hscl := hsp.1.scratch_ok
  have hcap := c.harena; have hmx := c.hmaxv; unfold dimacsBound at hcap hmx
  have har_len := hcl.arena_len_arr; have halen_le := hcl.arena_len_le
  have hws2_len := hscl.work_stk2_len; have hcref_wf := hw.arena.refs_wf cref.toNat href
  have holen_le : olen.toNat ≤ 2 * c.max_vars := by omega
  obtain ⟨hcref_lt, hmod2, hcref0_eq, hcref1_eq, hcref2_eq, hcref3_eq, hcref4_eq, hhdr_ng_raw⟩ :=
    cref_hdr_facts (fv_sparseW_to_sparse hsp) hw href hng
  let hdr := s.core.arena[(cref.setWidth 64).toNat]'(by rw [hcref0_eq]; exact hcref_lt)
  let old_sz := s.core.arena[(cref.setWidth 64 + 2#64).toNat]'(by rw [hcref2_eq]; omega)
  have hhdr_eq : hdr = fullArenaHdr s cref.toNat := ar_get_eq_getD hcref0_eq _
  have hold_sz_eq : old_sz.toNat = fullArenaClauseSizeCore s.core cref.toNat :=
    congrArg BitVec.toNat (ar_get_eq_getD hcref2_eq _)
  have hold_sz_3 : 3 ≤ old_sz.toNat := by rw [hold_sz_eq]; exact hcref_wf.2.1
  have hold_sz_bd : cref.toNat + 3 + old_sz.toNat ≤ s.core.arena.length := by
    rw [hold_sz_eq]; omega
  have hhdr_ng : (hdr &&& 0x00080000#32) = 0#32 := by
    simpa [hhdr_eq, fullArenaHdr, fullArenaHdrCore] using hhdr_ng_raw
  have hcref3_lt : (cref.setWidth 64 + 3#64).toNat < s.core.arena.length := by omega
  have hcref4_lt : (cref.setWidth 64 + 4#64).toNat < s.core.arena.length := by omega
  have hsz_s_eq : fullArenaClauseSize s cref.toNat = old_sz.toNat := hold_sz_eq.symm
  fv_steps
  · exact hQv 1#64 s m hsp hl0 rfl rfl rfl rfl rfl rfl (Or.inl rfl) (fun h => by cases h)
      (fun h => by cases h) hm
  · have holen_lt : olen.toNat < old_sz.toNat := by dsimp only [old_sz]; c0_bound
    obtain ⟨_, _, hout_ent⟩ := hout_ok (by rw [hsz_s_eq]; exact holen_lt)
    have holen0 : olen.toNat = 0 := by c0_bound
    exact commit_zero_pack_m4 hsp hl0
      (unsat_of_entails_nil (by simpa [holen0] using hout_ent)) hQv hm
  · obtain ⟨s1, hs1_core, hs1_ws2, hs1_rr, hsp1, hm1⟩ := commit_vivcnt_pack_m4 hsp hm
    have hw1 := hsp1.2.1
    have holen_lt : olen.toNat < old_sz.toNat := by dsimp only [old_sz]; c0_bound
    obtain ⟨hout_lt, hout_nd', hout_ent⟩ := hout_ok (by rw [hsz_s_eq]; exact holen_lt)
    have hout_nd : (((s.scratch.work_stk2.take olen.toNat).map BitVec.toNat).map (· / 2)).Nodup :=
      by simpa only [List.map_map, Function.comp_def] using hout_nd'
    have h0_ws2 : 0 < s.scratch.work_stk2.length := by
      have : olen.toNat ≠ 0 := fun h => (by c0_bound : olen ≠ 0#32) (BitVec.eq_of_toNat_eq h)
      omega
    have hcref4_lt_s1 : (cref.setWidth 64 + 4#64).toNat < s1.core.arena.length := by
      rw [hs1_core]; exact hcref4_lt
    c0_call hUnwatch
    refine ⟨c, F0, F_cur, s1, R, rfl, fv_sparseW_to_sparse hsp1, hw1, hm1,
      fun wvec1 wstk1 wu1 m2 hsp2 hw2 hm2 => ?_⟩
    have hcref4_lt1 : (cref.setWidth 64 + 4#64).toNat < ({ s1 with core :=
        { s1.core with wvec := wvec1, wstk := wstk1, wusable := wu1 } } :
        FullState).core.arena.length := hcref4_lt_s1
    fv_steps; c0_call hUnwatch
    refine ⟨c, F0, F_cur, _, R, rfl, hsp2, hw2, hm2, fun wvec2 wstk2 wu2 m3 hsp3w hw3w hm3w => ?_⟩
    obtain ⟨s3, hs3_ar, _, hs3_ws2, hrr3, hm3_eq, hs3_ref, hs3_ng, hs3_sz, hs3_hdr, hsp3, hm3⟩ :=
      unwatch2_state_pack_m4 hsp3w hw3w hm3w hng hsz_s_eq hhdr_eq (by rw [hs1_core])
        (by rw [hs1_core]) (by rw [hs1_core]) (by rw [hs1_core]) (by rw [hs1_core]; exact hl0)
        (by rw [hs1_core]) (by rw [hs1_core]) hs1_ws2 hs1_rr
    clear hsp3w hw3w hm3w wvec1 wstk1 wu1 m2 hsp2 hw2 hm2 wvec2 wstk2 wu2 hcref4_lt1
      hcref4_lt_s1 s1 hs1_core hs1_ws2 hs1_rr hsp1 hw1 hm1
    have har3_len := hsp3.1.core_ok.arena_len_arr
    have hws2_3 := hsp3.1.scratch_ok.work_stk2_len
    have hcref_lt3 : cref.toNat < s3.core.arena.length := by rw [har3_len]; omega
    have h0_ws2_3 : 0 < s3.scratch.work_stk2.length := by rw [hws2_3]; omega
    fv_steps
    · have holen1 : olen.toNat = 1 := by c0_bound
      fv_steps
      obtain ⟨s_g, _, hmg, hsc_g, hsp_g, ha_g, hm_g⟩ :=
        fullArena_markGarb_pack hsp3.1 hsp3.2.1 hsp3.2.2.1 hsp3.2.2.2.2.1 hsp3.2.2.2.2.2
          hm3_eq.2.2.1 (by rw [hs3_ref]; exact href) hs3_hdr
          (fun r hr _ hngr => hsp3.2.2.2.1 r hr hngr) hm
      have hms_g : VivMetaEq s s_g :=
        ⟨hmg.1.trans hm3_eq.1, hmg.2.1.trans hm3_eq.2.1, hmg.2.2.1,
         hmg.2.2.2.1.trans hm3_eq.2.2.2.1, hmg.2.2.2.2.trans hm3_eq.2.2.2.2⟩
      have has_g : VivArenaEq s s_g :=
        ⟨ha_g.1.trans hs3_ref, fun q hq => by
          have := ha_g.2 q (by rw [hs3_ref]; exact hq); rwa [hm3_eq.1, hs3_ar] at this⟩
      have hrr_g : s_g.scratch.red_refs = s.scratch.red_refs :=
        (congrArg FullScratch.red_refs hsc_g).trans hrr3
      have hu0_lt := ws2_lt_cv (j := 0) (by omega) hout_lt hs3_ws2 hm3_eq.2.1 hmg.2.1 (by omega)
      have hu0_ent : (cnfOfClauses F_cur).EntailsClause
          (cnfClause [(s3.scratch.work_stk2[0]'(by omega)).toNat]) := by
        simpa only [← hs3_ws2] using take_entails_1 holen1 (by rw [hws2_len]; omega) hout_ent
      refine addUnit_call_m4_wp Γ hAddUnit hsp_g hms_g has_g hrr_g hu0_lt hu0_ent hm_g ?_ ?_
      · intro s4 m4 hsp4 hm4' ha4 hrr4 hmem4; fv_steps
        exact hQv 1#64 s4 m4 hsp4 hm4'.2.2.1 hm4'.2.1 hm4'.1 hm4'.2.2.2.1 hm4'.2.2.2.2 ha4.1 hrr4
          (Or.inl rfl) (fun h => by cases h) (fun h => by cases h) hmem4
      · intro s4 m4 hsp4 hm4' ha4 hrr4 hu4 hmem4; fv_steps
        exact hQv 20#64 s4 m4 hsp4 hm4'.2.2.1 hm4'.2.1 hm4'.1 hm4'.2.2.2.1 hm4'.2.2.2.2 ha4.1 hrr4
          (Or.inr (Or.inr rfl)) (fun _ => hu4) (fun h => by cases h) hmem4
    · have holen2 : olen.toNat = 2 := by c0_bound
      have h1_ws2_3 : 1 < s3.scratch.work_stk2.length := by rw [hws2_3]; omega
      fv_steps
      obtain ⟨s_g, _, hmg, hsc_g, hsp_g, ha_g, hm_g⟩ :=
        fullArena_markGarb_pack hsp3.1 hsp3.2.1 hsp3.2.2.1 hsp3.2.2.2.2.1 hsp3.2.2.2.2.2
          hm3_eq.2.2.1 (by rw [hs3_ref]; exact href) hs3_hdr
          (fun r hr _ hngr => hsp3.2.2.2.1 r hr hngr) hm
      have hrr_g : s_g.scratch.red_refs = s.scratch.red_refs :=
        (congrArg FullScratch.red_refs hsc_g).trans hrr3
      have hu0_lt := ws2_lt_cv (j := 0) (by omega) hout_lt hs3_ws2 hm3_eq.2.1 hmg.2.1 (by omega)
      have hu1_lt := ws2_lt_cv (j := 1) (by omega) hout_lt hs3_ws2 hm3_eq.2.1 hmg.2.1 (by omega)
      have hbin_ent : (cnfOfClauses F_cur).EntailsClause
          (cnfClause [(s3.scratch.work_stk2[0]'(by omega)).toNat,
                      (s3.scratch.work_stk2[1]'(by omega)).toNat]) := by
        simpa only [← hs3_ws2] using take_entails_2 holen2 (by rw [hws2_len]; omega) hout_ent
      c0_call hAddBin
      refine ⟨c, F0, F_cur, s_g, R, rfl, hsp_g.1, hsp_g.2.1, hsp_g.2.2.1, hsp_g.2.2.2.2.1,
        hsp_g.2.2.2.2.2, hmg.2.2.1, hu0_lt, hu1_lt, hbin_ent, hm_g,
        fun br s4 m4 hlen4 _ hw4 hmc4 hext4 hdm4 har4 halen4 hcv4 hl4 hpr4 hfu4 hrr4 h20 hm4 => ?_⟩
      have has_g : VivArenaEq s s_g := ⟨ha_g.1.trans hs3_ref, fun q hq => by
        have := ha_g.2 q (by rw [hs3_ref]; exact hq); rwa [hm3_eq.1, hs3_ar] at this⟩
      obtain ⟨hsp4, hl4', ha4⟩ := addBin_ok_post hlen4 hw4 hmc4 hext4 hdm4 hl4 har4
        halen4 hsp_g.2.2.2.1 has_g
      fv_steps
      · exact hQv 20#64 s4 m4 hsp4 hl4' (hcv4.trans (hmg.2.1.trans hm3_eq.2.1))
          (halen4.trans (hmg.1.trans hm3_eq.1)) (hpr4.trans (hmg.2.2.2.1.trans hm3_eq.2.2.2.1))
          (hfu4.trans (hmg.2.2.2.2.trans hm3_eq.2.2.2.2)) ha4.1 (hrr4.trans hrr_g)
          (Or.inr (Or.inr rfl)) (fun _ => h20 hc) (fun h => by cases h) hm4
      · exact hQv 1#64 s4 m4 hsp4 hl4' (hcv4.trans (hmg.2.1.trans hm3_eq.2.1))
          (halen4.trans (hmg.1.trans hm3_eq.1)) (hpr4.trans (hmg.2.2.2.1.trans hm3_eq.2.2.2.1))
          (hfu4.trans (hmg.2.2.2.2.trans hm3_eq.2.2.2.2)) ha4.1 (hrr4.trans hrr_g)
          (Or.inl rfl) (fun h => by cases h) (fun h => by cases h) hm4
    · have holen3 : 3 ≤ olen.toNat :=
        bv32_ge3_of_ne olen (by c0_bound) (by c0_bound) (by c0_bound)
      have h1_ws2_3 : 1 < s3.scratch.work_stk2.length := by rw [hws2_3]; omega
      refine wp_loop_inv
        (fun (i, ()) m4 => ∃ ar4 : List (BitVec 32), i.toNat ≤ olen.toNat ∧
          ar4.length = c.arena_cap ∧ (∀ k < i.toNat, ar4[cref.toNat + 3 + k]? =
            s3.scratch.work_stk2[k]?) ∧
          (∀ p, (p < cref.toNat + 3 ∨ cref.toNat + 3 + i.toNat ≤ p) →
            ar4[p]? = s3.core.arena[p]?) ∧
          (FullMem c { s3 with core := { s3.core with arena := ar4 } } ⋆ R) m4)
        (fun (i, ()) _ => olen.toNat - i.toNat)
        (fun Jc hJc => by fv_steps; exact hJc (0#32, ()) m3 ⟨s3.core.arena, by simp, har3_len,
          fun _ hk => by simp at hk, fun _ _ => rfl, hm3⟩)
        (fun Jc (i, ()) m4 ⟨ar4, hi_le, har4_len, hcp4, hout4, hm4⟩ ihc => ?_)
      fv_while
      · have hi_lt : i.toNat < olen.toNat := by c0_bound
        have hi_idx : (cref.setWidth 64 + 3#64 + i.setWidth 64).toNat =
            cref.toNat + 3 + i.toNat := by bv_omega
        have hi_lt_ar : (cref.setWidth 64 + 3#64 + i.setWidth 64).toNat < ar4.length := by omega
        have hi_lt_ws2 : i.toNat < s3.scratch.work_stk2.length := by omega
        have hi1_eq : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
        fv_steps
        let ar5 := ar4.set (cref.toNat + 3 + i.toNat) (s3.scratch.work_stk2[i.toNat]'hi_lt_ws2)
        have har5_eq : ar4.set (cref.setWidth 64 + 3#64 + i.setWidth 64).toNat
            (s3.scratch.work_stk2[i.toNat]'hi_lt_ws2) = ar5 := by simp only [ar5, hi_idx]
        refine ihc (i + 1#32, ()) _ (by dsimp only; omega)
          ⟨ar5, by omega, by simp [ar5, har4_len], fun k hk => ?_, fun p hp => ?_,
            fullMem_eq_of_arena_eq har5_eq hm⟩
        · rcases (by omega : k < i.toNat ∨ k = i.toNat) with hk' | rfl
          · dsimp only [ar5]; rw [List.getElem?_set_ne (by omega)]; exact hcp4 k hk'
          · dsimp only [ar5]
            rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem hi_lt_ws2]
        · dsimp only [ar5]; rw [List.getElem?_set_ne (by omega)]; exact hout4 p (by omega)
      · have hi_eq : i.toNat = olen.toNat := by c0_bound
        have har4_lt2 : (cref.setWidth 64 + 2#64).toNat < ar4.length := by omega
        have har4_lt1 : (cref.setWidth 64 + 1#64).toNat < ar4.length := by omega
        let ar_sz := (ar4.set (cref.setWidth 64 + 2#64).toNat olen).set
          (cref.setWidth 64 + 1#64).toNat 2#32
        obtain ⟨hasz_len, hasz_out, hasz_sz, hasz_pay, hasz_pad, _⟩ :=
          ar_set_sz_props (ar0 := ar4) (ar_orig := s3.core.arena) (by omega) holen3 holen_lt
            (by omega) rfl hcref2_eq hcref1_eq (by simpa [hi_eq] using hout4)
        have hasz_cap : ar_sz.length = c.arena_cap := hasz_len.trans har3_len
        have hcp_sz : ∀ j < olen.toNat, ar_sz[cref.toNat + 3 + j]? = s3.scratch.work_stk2[j]? :=
          fun j hj => by rw [hasz_pay j hj]; exact hcp4 j (by omega)
        clear hc Jc ihc hcp4 hout4 har4_len har4_lt2 har4_lt1
        fv_to_grp
        refine wp_join_group
          (fun (nhdr, ()) m5 => ∃ ni1 nr1 : BitVec 64,
            (nhdr &&& 0x00080000#32) = 0#32 ∧
            (nhdr &&& 0x00800000#32) = (hdr &&& 0x00800000#32) ∧
            (FullMem c { s3 with core := { s3.core with
              arena := ar_sz, num_irred := ni1, num_redundant := nr1 } } ⋆ R) m5)
          (fun _ (nhdr, ()) m5 ⟨ni1, nr1, hng_nh, hsh_nh, hm5⟩ =>
            commit_shrk_mid_m4_wp Γ hWatchPush hsp3 href hs3_ref hs3_ng hs3_ar hm3_eq hs3_ws2 hrr3
              hs3_sz hs3_hdr holen3 holen_lt holen_le hout_lt hout_nd hout_ent hasz_cap
              hng_nh hsh_nh hasz_out hasz_sz hcp_sz hasz_pad hm5 hQv)
          (fun J_red hJ_red => ?_)
        fv_steps
        · exact hJ_red (hdr, ()) _ ⟨_, _, hhdr_ng, rfl, hm⟩
        · exact hJ_red (hdr &&& ~~~0x00400000#32, ()) _
            ⟨_, _, by rw [bv32_clr_red_garb, hhdr_ng], bv32_clr_red_shrk hdr, hm⟩
        · exact hJ_red (hdr &&& ~~~0x00400000#32, ()) _
            ⟨_, _, by rw [bv32_clr_red_garb, hhdr_ng], bv32_clr_red_shrk hdr, hm⟩
        · exact hJ_red (hdr, ()) _ ⟨_, _, hhdr_ng, rfl, hm⟩

end

end LeanQbe.T.Examples.Kissat.FullM4VivBce
