/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullM8SbvaTie
public import LeanQbe.T.Examples.Kissat.FullBvaHeapSpec
public import LeanQbe.T.Examples.Kissat.FullBvaHeapLemmas
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat M8 `FullM8SbvaTie` Proofs (`FullM8SbvaTieProof`)

M1-clean UNSAT-only proofs (`public section`, `0` `@[expose]`, `0` `import all`, `0` SAT proofs):
1. `full_bva_pick_sbva3_m8_wp`: callee-free parametric `(Γ : Env)` `Func.wp` proof of
   `full_bva_pick_sbva3_m8_body` against canonical `FullBvaHeap.fullBvaPickCandSpec` (preserving
   `FullDenseInvNoLm`, `FullMem`, `work_stk1`, `work_stk2`, `cur_vars`, and all core/arena/watch
   structures).
2. `fullBvaPickPres` & `full_bva_pick_sbva3_m8_pres_wp`: explicit state-preservation corollary
   (`FullDenseInvNoLm`, `FullExtScratchPres`, `FullMem`, unchanged `work_stk1`/`work_stk2`).
3. Closed `1`-row `m8SbvaTieSpecTable`, `m8SbvaTieEnv`, `m8SbvaTieEnv_noExit`,
   `m8SbvaTie_tableImpl`, `m8SbvaTie_moduleOk`, and `FullM7Splice`/`PatchModule` bridges
   (`m8SbvaTiePatchRows`, `m8SbvaPickCandFn_impl`, `m8SbvaTiePatch_tableImpl`,
   `m8SbvaTiePatch_tableImpl_of`).
4. Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`):
   - `nv_m8_bva_pick_sbva3`: on `FullBvaHeap.nvBvaDenseMem` (`ncntd = 2#32`).
   - `nv_m8_bva_pick_sbva3_tie_3hop`: on a mutated `Mem 64` tie state (`wsort = [2, 2]`,
     `work_stk1 = [0, 1]`, `best_c = 2`, `ties = 2 > 1`) actively entering the 3-hop SBVA
     tie-breaking path.
-/

set_option autoImplicit false

public section

local elab "c0_hfast_nogrp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

namespace LeanQbe.T.Examples.Kissat.FullM8SbvaTie

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapHelpers
open LeanQbe.T.Examples.Kissat.FullBvaHeap.FullBvaHeapTactics
open Kraken.Bedrock2.Test
open scoped FullArenaTactics FullBvaHeapTactics

/-! ## 1. Pure BitVec & Arena Helpers -/

section Helpers

private theorem sbva_hop_wvec_bounds {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hinv : FullDenseInvNoLm c F0 F_cur s) {sl : Nat}
    (hsl : sl < 2 * s.core.cur_vars) :
    fullWatchOffCore s.core sl + fullWatchSizeCore s.core sl ≤ s.core.wlen ∧
    DenseWatchSliceOk F_cur s.core sl (fullWatchOffCore s.core sl)
      (fullWatchSizeCore s.core sl) := by
  have hdw : DenseWatchesInv F_cur s.core := by
    have h := hinv.2.1.watches; unfold ModeWatchesInv at h
    rwa [ite_eq_right hinv.2.2.2.2.2] at h
  exact ⟨hdw.layout.bounds sl hsl, hdw.slices sl hsl⟩

private theorem sbva_bv32_shl1_or_lt2 {x y : BitVec 32} (hy : y.toNat < 2)
    (hx : x.toNat < 2 ^ 31) :
    ((x <<< (1 : Nat)) ||| y).toNat = 2 * x.toNat + y.toNat := by
  have hev : (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
    rw [bv32_shl1_nat, Nat.mod_eq_of_lt (by omega)]
  rcases (by omega : y.toNat = 0 ∨ y.toNat = 1) with h0 | h1
  · have hy0 : y = 0#32 := BitVec.eq_of_toNat_eq h0; subst hy0
    rw [BitVec.or_zero, hev]; rfl
  · have hy1 : y = 1#32 := BitVec.eq_of_toNat_eq h1; subst hy1
    rw [FullBvaFwdTactics.bv32_or1_of_even (by omega), hev]; rfl

private theorem sbva_garb_zero_of_and_red {x : BitVec 32}
    (h : (x &&& (0x00080000#32 ||| 0x00400000#32)) = 0#32) :
    (x &&& 0x00080000#32) = 0#32 := by
  have h1 := congrArg (· &&& 0x00080000#32) h
  rw [BitVec.and_assoc,
    show ((0x00080000#32 ||| 0x00400000#32) &&& 0x00080000#32) = 0x00080000#32 from by decide,
    BitVec.zero_and] at h1
  exact h1

private theorem sbva_arena_lit_lt {F0 : CNF Nat} {F_cur : List (List Nat)} {c : FullCfg}
    {s : FullState} (hlen : s.core.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    {cr j sz : Nat} (hcr : cr ∈ fullArenaClauseRefsCore s.core)
    (hng : fullArenaClauseGarbCore s.core cr = false)
    (hsz : sz = fullArenaClauseSizeCore s.core cr) (hj : j < sz)
    (har : cr + 3 + j < s.core.arena.length) :
    (s.core.arena[cr + 3 + j]'har).toNat < 2 * s.core.cur_vars := by
  have hwf := hw.arena.refs_wf cr hcr
  have hal := hlen.arena_len_le
  have harr := hlen.arena_len_arr
  have hl_mem : (s.core.arena[cr + 3 + j]'har).toNat ∈ fullArenaClauseLitsCore s.core cr :=
    List.mem_of_getElem? (FullBvaFwdHelpers.fullArenaClauseLitsCore_getElem
      (k := s.core) (r := cr) (j := j) (hsz ▸ hj) (by omega))
  exact hw.arena.lits_lt cr hcr hng _ hl_mem

private theorem sbva_bv32_add1 {x : BitVec 32} {n : Nat}
    (hx : x.toNat < n) (hn : n < 2 ^ 32) : (x + 1#32).toNat = x.toNat + 1 := by
  simp only [bv_c0]
  omega

private theorem sbva_bw64_shl1 (x : BitVec 32) :
    (BitVec.setWidth 64 x <<< (1 : Nat)).toNat = 2 * x.toNat := by
  simp only [bv_c0]
  omega

private theorem sbva_bw64_shl1_add1 (x : BitVec 32) :
    ((BitVec.setWidth 64 x <<< (1 : Nat)) + 1#64).toNat = 2 * x.toNat + 1 := by
  simp only [bv_c0]
  omega

private theorem sbva_lt_bv32 {x : BitVec 32} {n : Nat}
    (hn : n < 2 ^ 32) (h : x.toNat < BitVec.toNat (OfNat.ofNat n : BitVec 32)) :
    x.toNat < n := by
  have h' : x.toNat < (BitVec.ofNat 32 n).toNat := h
  simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] using h'

private theorem sbva_bv64_add1 {x : BitVec 64} {n : Nat}
    (hx : x.toNat < n) (hn : n < 2 ^ 64) : (x + 1#64).toNat = x.toNat + 1 := by
  simp only [bv_c0]
  omega

private theorem sbva_bv64_add2 {x : BitVec 64} (hx : x.toNat + 2 < 2 ^ 64) :
    (x + 1#64 + 1#64).toNat = x.toNat + 2 := by
  simp only [bv_c0]
  omega

private theorem sbva_bw64_add2 (x : BitVec 32) :
    (BitVec.setWidth 64 x + 2#64).toNat = x.toNat + 2 := by
  simp only [bv_c0]
  omega

private theorem sbva_bw64_add3_add (a b : BitVec 32) :
    (BitVec.setWidth 64 a + 3 + BitVec.setWidth 64 b).toNat = a.toNat + 3 + b.toNat := by
  change (BitVec.setWidth 64 a + 3#64 + BitVec.setWidth 64 b).toNat = _
  simp only [bv_c0]
  omega

private theorem nat_two_add1_lt {k m : Nat} (h : k < m) : 2 * k + 1 < 2 * m := by omega
private theorem nat_two_lt {k m : Nat} (h : k < m) : 2 * k < 2 * m := by omega

end Helpers

/-! ## 2. Explicit Preservation Predicate & `full_bva_pick_sbva3_m8_wp` -/

/-- State preservation contract for `full_bva_pick_sbva3_m8`: preserves `FullExtScratchPres`,
`work_stk1`, `work_stk2`, `cur_vars`, `arena`, `wstk`, `wvec`, `vals`, `mrk`, and `lit_mark`. -/
def fullBvaPickPres (s s' : FullState) : Prop :=
  FullExtScratchPres s s' ∧
  s'.scratch.work_stk1 = s.scratch.work_stk1 ∧
  s'.scratch.work_stk2 = s.scratch.work_stk2 ∧
  s'.core.cur_vars = s.core.cur_vars ∧
  s'.core.arena = s.core.arena ∧
  s'.core.wstk = s.core.wstk ∧
  s'.core.wvec = s.core.wvec ∧
  s'.core.vals = s.core.vals ∧
  s'.core.mrk = s.core.mrk ∧
  s'.core.lit_mark = s.core.lit_mark

private def sbvaBfsSt (s : FullState) (mc rp : List (BitVec 32))
    (sig : List (BitVec 64)) : FullState :=
  { core := { s.core with repr := rp, min_clr := mc }
    scratch := { s.scratch with sim_sig := sig } }

private def SbvaMem (c : FullCfg) (s : FullState) (mc rp : List (BitVec 32))
    (sig : List (BitVec 64)) (m : Mem 64) : Prop :=
  FullMem c (sbvaBfsSt s mc rp sig) m

private def sbvaFinSt (s : FullState) (mc rp ws : List (BitVec 32))
    (sig : List (BitVec 64)) : FullState :=
  { core := { s.core with repr := rp, min_clr := mc }
    scratch := { s.scratch with wsort := ws, sim_sig := sig } }

private def SbvaFinMem (c : FullCfg) (s : FullState) (mc rp ws : List (BitVec 32))
    (sig : List (BitVec 64)) (m : Mem 64) : Prop :=
  FullMem c (sbvaFinSt s mc rp ws sig) m

private def sbvaFinQ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop) (Q : Post [i32]) (r : BitVec 32) (rp mc : List (BitVec 32))
    (_tc _tl : Nat) (ws : List (BitVec 32)) (_ant : BitVec 64) (sig : List (BitVec 64))
    (_sh : List (BitVec 32)) (m' : Mem 64) : Prop :=
  let s' := sbvaFinSt s mc rp ws sig
  FullDenseInvNoLm c F0 F_cur s' →
  (r = 0xFFFFFFFF#32 ∨ r.toNat < 2 * s.core.cur_vars) →
  (FullMem c s' ⋆ R) m' → Q (r, ()) m'

private def sbvaTbJoin (c : FullCfg) (s : FullState) (R : Mem 64 → Prop) (best_c : BitVec 32)
    (_bdF blF _ciF : BitVec 32) (mcF rpF : List (BitVec 32))
    (sigF : List (BitVec 64)) (mf : Mem 64) : Prop :=
  (2 ≤ best_c.toNat → blF.toNat < 2 * s.core.cur_vars) ∧
  mcF.length = c.max_vars ∧ rpF.length = 2 * c.max_vars ∧ sigF.length = c.max_vars ∧
  (FullMem c (sbvaBfsSt s mcF rpF sigF) ⋆ R) mf

private def sbvaBfsInv (c : FullCfg) (s : FullState) (R : Mem 64 → Prop) (cap : BitVec 32)
    (mc rp : List (BitVec 32)) (sig : List (BitVec 64)) (vn : BitVec 32)
    (mb : Mem 64) : Prop :=
  mc.length = c.max_vars ∧ rp.length = 2 * c.max_vars ∧ sig.length = c.max_vars ∧
  1 ≤ vn.toNat ∧ vn.toNat ≤ cap.toNat ∧
  (∀ k < vn.toNat, (mc[k]?.getD 0#32).toNat < s.core.cur_vars) ∧
  (SbvaMem c s mc rp sig ⋆ R) mb

private theorem sbva_upd4_eq (s : FullState) (mc rp0 rp1 : List (BitVec 32))
    (sig : List (BitVec 64)) :
    (let s1 := { s with core := { s.core with min_clr := mc } }
     let s2 := { s1 with core := { s1.core with repr := rp0 } }
     let s3 := { s2 with core := { s2.core with repr := rp1 } }
     { s3 with scratch := { s3.scratch with sim_sig := sig } }) = sbvaBfsSt s mc rp1 sig := by
  rcases s with ⟨c0, sc0⟩; rfl

private theorem sbvaBfsSt_self (s : FullState) :
    sbvaBfsSt s s.core.min_clr s.core.repr s.scratch.sim_sig = s := by
  rcases s with ⟨c0, sc0⟩; rfl

attribute [local bv_c0] List.length_set

@[local c0_load] private theorem c0_load_sbva_min_clr {c : FullCfg} {s : FullState}
    {mc rp : List (BitVec 32)} {sig : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    {i : BitVec 64} (hi : i.toNat < mc.length) (hm : (SbvaMem c s mc rp sig ⋆ R) m) :
    loadVal m i32 (c.pMinClr + i * 4) = some mc[i.toNat] :=
  FullArenaTactics.c0_load_full_min_clr (s := sbvaBfsSt s mc rp sig) hi hm

@[local c0_store] private theorem c0_store_sbva_min_clr {c : FullCfg} {s : FullState}
    {mc rp : List (BitVec 32)} {sig : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    {i : BitVec 64} (v : BitVec 32) (hi : i.toNat < mc.length)
    (hm : (SbvaMem c s mc rp sig ⋆ R) m) :
    storeOk m i32 (c.pMinClr + i * 4) ∧
    (SbvaMem c s (mc.set i.toNat v) rp sig ⋆ R)
      (storeMem m i32 (c.pMinClr + i * 4) v) := by
  have ⟨h1, h2⟩ := FullArenaTactics.c0_store_full_min_clr (s := sbvaBfsSt s mc rp sig) v hi hm
  refine ⟨h1, ?_⟩
  rwa [show { sbvaBfsSt s mc rp sig with core := { (sbvaBfsSt s mc rp sig).core with
    min_clr := (sbvaBfsSt s mc rp sig).core.min_clr.set i.toNat v } } =
    sbvaBfsSt s (mc.set i.toNat v) rp sig from by rcases s with ⟨c0, sc0⟩; rfl] at h2

@[local c0_load] private theorem c0_load_sbva_repr {c : FullCfg} {s : FullState}
    {mc rp : List (BitVec 32)} {sig : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    {i : BitVec 64} (hi : i.toNat < rp.length) (hm : (SbvaMem c s mc rp sig ⋆ R) m) :
    loadVal m i32 (c.pRepr + i * 4) = some rp[i.toNat] :=
  FullArenaTactics.c0_load_full_repr (s := sbvaBfsSt s mc rp sig) hi hm

@[local c0_store] private theorem c0_store_sbva_repr {c : FullCfg} {s : FullState}
    {mc rp : List (BitVec 32)} {sig : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    {i : BitVec 64} (v : BitVec 32) (hi : i.toNat < rp.length)
    (hm : (SbvaMem c s mc rp sig ⋆ R) m) :
    storeOk m i32 (c.pRepr + i * 4) ∧
    (SbvaMem c s mc (rp.set i.toNat v) sig ⋆ R)
      (storeMem m i32 (c.pRepr + i * 4) v) := by
  have ⟨h1, h2⟩ := FullArenaTactics.c0_store_full_repr (s := sbvaBfsSt s mc rp sig) v hi hm
  refine ⟨h1, ?_⟩
  rwa [show { sbvaBfsSt s mc rp sig with core := { (sbvaBfsSt s mc rp sig).core with
    repr := (sbvaBfsSt s mc rp sig).core.repr.set i.toNat v } } =
    sbvaBfsSt s mc (rp.set i.toNat v) sig from by rcases s with ⟨c0, sc0⟩; rfl] at h2

@[local c0_load] private theorem c0_load_sbva_sim_sig {c : FullCfg} {s : FullState}
    {mc rp : List (BitVec 32)} {sig : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    {i : BitVec 64} (hi : i.toNat < sig.length) (hm : (SbvaMem c s mc rp sig ⋆ R) m) :
    loadVal m i64 (c.pSimSig + i * 8) = some sig[i.toNat] :=
  FullArenaTactics.c0_load_full_sim_sig (s := sbvaBfsSt s mc rp sig) hi hm

@[local c0_store] private theorem c0_store_sbva_sim_sig {c : FullCfg} {s : FullState}
    {mc rp : List (BitVec 32)} {sig : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    {i : BitVec 64} (v : BitVec 64) (hi : i.toNat < sig.length)
    (hm : (SbvaMem c s mc rp sig ⋆ R) m) :
    storeOk m i64 (c.pSimSig + i * 8) ∧
    (SbvaMem c s mc rp (sig.set i.toNat v) ⋆ R)
      (storeMem m i64 (c.pSimSig + i * 8) v) := by
  have ⟨h1, h2⟩ := FullArenaTactics.c0_store_full_sim_sig (s := sbvaBfsSt s mc rp sig) v hi hm
  refine ⟨h1, ?_⟩
  rwa [show { sbvaBfsSt s mc rp sig with scratch := { (sbvaBfsSt s mc rp sig).scratch with
    sim_sig := (sbvaBfsSt s mc rp sig).scratch.sim_sig.set i.toNat v } } =
    sbvaBfsSt s mc rp (sig.set i.toNat v) from by rcases s with ⟨c0, sc0⟩; rfl] at h2

@[local c0_load] private theorem c0_load_sbva_wvec {c : FullCfg} {s : FullState}
    {mc rp : List (BitVec 32)} {sig : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    {i : BitVec 64} (hi : i.toNat < s.core.wvec.length) (hm : (SbvaMem c s mc rp sig ⋆ R) m) :
    loadVal m i32 (c.pWvec + i * 4) = some s.core.wvec[i.toNat] :=
  FullArenaTactics.c0_load_full_wvec (s := sbvaBfsSt s mc rp sig) hi hm

@[local c0_load] private theorem c0_load_sbva_wstk {c : FullCfg} {s : FullState}
    {mc rp : List (BitVec 32)} {sig : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    {i : BitVec 64} (hi : i.toNat < s.core.wstk.length) (hm : (SbvaMem c s mc rp sig ⋆ R) m) :
    loadVal m i32 (c.pWstk + i * 4) = some s.core.wstk[i.toNat] :=
  FullArenaTactics.c0_load_full_wstk (s := sbvaBfsSt s mc rp sig) hi hm

@[local c0_load] private theorem c0_load_sbva_arena {c : FullCfg} {s : FullState}
    {mc rp : List (BitVec 32)} {sig : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    {i : BitVec 64} (hi : i.toNat < s.core.arena.length) (hm : (SbvaMem c s mc rp sig ⋆ R) m) :
    loadVal m i32 (c.pArena + i * 4) = some s.core.arena[i.toNat] :=
  FullArenaTactics.c0_load_full_arena (s := sbvaBfsSt s mc rp sig) hi hm

@[local c0_load] private theorem c0_load_sbva_work_stk1 {c : FullCfg} {s : FullState}
    {mc rp : List (BitVec 32)} {sig : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    {i : BitVec 64} (hi : i.toNat < s.scratch.work_stk1.length)
    (hm : (SbvaMem c s mc rp sig ⋆ R) m) :
    loadVal m i32 (c.pWorkStk1 + i * 4) = some s.scratch.work_stk1[i.toNat] :=
  FullArenaTactics.c0_load_full_work_stk1 (s := sbvaBfsSt s mc rp sig) hi hm

@[local c0_load] private theorem c0_load_sbva_wsort {c : FullCfg} {s : FullState}
    {mc rp : List (BitVec 32)} {sig : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    {i : BitVec 64} (hi : i.toNat < s.scratch.wsort.length) (hm : (SbvaMem c s mc rp sig ⋆ R) m) :
    loadVal m i32 (c.pWsort + i * 4) = some s.scratch.wsort[i.toNat] :=
  FullArenaTactics.c0_load_full_wsort (s := sbvaBfsSt s mc rp sig) hi hm

@[local c0_load] private theorem c0_load_sbva_fin_work_stk1 {c : FullCfg} {s : FullState}
    {mc rp ws : List (BitVec 32)} {sig : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    {i : BitVec 64} (hi : i.toNat < s.scratch.work_stk1.length)
    (hm : (SbvaFinMem c s mc rp ws sig ⋆ R) m) :
    loadVal m i32 (c.pWorkStk1 + i * 4) = some s.scratch.work_stk1[i.toNat] :=
  FullArenaTactics.c0_load_full_work_stk1 (s := sbvaFinSt s mc rp ws sig) hi hm

@[local c0_store] private theorem c0_store_sbva_fin_wsort {c : FullCfg} {s : FullState}
    {mc rp ws : List (BitVec 32)} {sig : List (BitVec 64)} {R : Mem 64 → Prop} {m : Mem 64}
    {i : BitVec 64} (v : BitVec 32) (hi : i.toNat < ws.length)
    (hm : (SbvaFinMem c s mc rp ws sig ⋆ R) m) :
    storeOk m i32 (c.pWsort + i * 4) ∧
    (SbvaFinMem c s mc rp (ws.set i.toNat v) sig ⋆ R)
      (storeMem m i32 (c.pWsort + i * 4) v) := by
  have ⟨h1, h2⟩ := FullArenaTactics.c0_store_full_wsort (s := sbvaFinSt s mc rp ws sig) v hi hm
  refine ⟨h1, ?_⟩
  rwa [show { sbvaFinSt s mc rp ws sig with scratch := { (sbvaFinSt s mc rp ws sig).scratch with
    wsort := (sbvaFinSt s mc rp ws sig).scratch.wsort.set i.toNat v } } =
    sbvaFinSt s mc rp (ws.set i.toNat v) sig from by rcases s with ⟨c0, sc0⟩; rfl] at h2



private abbrev sbvaOp1 {t r : Ty} (code : OpCode [t] [r]) (a : Arg Val t) : Op Val [r] :=
  { sig := [t], code := code, args := (a, ()) }

private abbrev sbvaOp2 {t r : Ty} (code : OpCode [t, t] [r]) (a b : Arg Val t) : Op Val [r] :=
  { sig := [t, t], code := code, args := (a, b, ()) }

private abbrev sbvaL35Expr (pMinClr pRepr pSimSig : Val i64) (cw vis_n_j hop cap ov : Val i32)
    (J35 : Cont [i32]) : Expr Val Cont [i32] :=
Expr.group (sig := [[i32]])
  (fun Js =>
  Blocks.cons
   (fun p =>
    Expr.group (sig := [[]])
    (fun _Js =>
     Blocks.cons
      (fun _p_1 =>
      Expr.group (sig := [[i32]])
       (fun _Js =>
        Blocks.cons
        (fun p_2 =>
         Expr.group (sig := [[]])
          (fun _Js =>
          Blocks.cons (fun _p => Expr.jump J35 (Arg.var p_2.fst, ())) Blocks.nil)
          fun Js =>
          Expr.let_
          (sbvaOp2 (.cmp .ult i32 .bool rfl) (Arg.var p.fst) (Arg.var p_2.fst))
          fun p_3 =>
          Expr.jnz (Arg.var p_3.fst)
           (Expr.let_ (sbvaOp1 (.zext 32 64) (Arg.var p.fst))
            fun p_4 =>
            Expr.let_
            (sbvaOp2 (.mul i64) (Arg.var p_4.fst) (Arg.imm 8))
            fun p_5 =>
            Expr.let_
            (sbvaOp2 (.add i64) (Arg.var pSimSig) (Arg.var p_5.fst))
            fun p_6 =>
            Expr.let_
            (sbvaOp1 (.zext 32 64) (Arg.var p.fst))
            fun p_7 =>
            Expr.let_
            (sbvaOp2 (.mul i64) (Arg.var p_7.fst) (Arg.imm 8))
            fun p_8 =>
            Expr.let_
            (sbvaOp2 (.add i64) (Arg.var pSimSig) (Arg.var p_8.fst))
            fun p_9 =>
            Expr.load i64 (Arg.var p_9.fst) fun ld =>
            Expr.let_
            (sbvaOp1 (.zext 32 64) (Arg.var cw))
            fun p_10 =>
            Expr.let_
            (sbvaOp2 (.add i64) (Arg.var ld) (Arg.var p_10.fst))
            fun p_11 =>
            Expr.store (Arg.var p_11.fst) (Arg.var p_6.fst)
            (Expr.let_
            (sbvaOp1 (.zext 32 64) (Arg.var p.fst))
            fun p_12 =>
            Expr.let_
            (sbvaOp1 (.sext 32 64) (Arg.imm 1))
            fun p_13 =>
            Expr.let_
            (sbvaOp2 (.shl i64) (Arg.var p_12.fst) (Arg.var p_13.fst))
            fun p_14 =>
            Expr.let_
            (sbvaOp2 (.add i64) (Arg.var p_14.fst) (Arg.imm 1))
            fun p_15 =>
            Expr.let_
            (sbvaOp2 (.mul i64) (Arg.var p_15.fst) (Arg.imm 4))
            fun p_16 =>
            Expr.let_
            (sbvaOp2 (.add i64) (Arg.var pRepr) (Arg.var p_16.fst))
            fun p_17 =>
            Expr.load i32 (Arg.var p_17.fst) fun ld =>
            Expr.let_
            (sbvaOp1 (.zext 32 64) (Arg.var ld))
            fun p_18 =>
            Expr.let_
            (sbvaOp1 (.zext 32 64) (Arg.var cw))
            fun p_19 =>
            Expr.let_
            (sbvaOp2 (.add i64) (Arg.var p_18.fst) (Arg.var p_19.fst))
            fun p_20 =>
            Expr.group (sig := [[i32]])
            (fun _Js_1 =>
            Blocks.cons
            (fun p_21 =>
            Expr.let_
            (sbvaOp1 (.zext 32 64) (Arg.var p.fst))
            fun p =>
            Expr.let_
            (sbvaOp1 (.sext 32 64) (Arg.imm 1))
            fun p_22 =>
            Expr.let_
            (sbvaOp2 (.shl i64) (Arg.var p.fst) (Arg.var p_22.fst))
            fun p =>
            Expr.let_
            (sbvaOp2 (.add i64) (Arg.var p.fst) (Arg.imm 1))
            fun p =>
            Expr.let_
            (sbvaOp2 (.mul i64) (Arg.var p.fst) (Arg.imm 4))
            fun p =>
            Expr.let_
            (sbvaOp2 (.add i64) (Arg.var pRepr) (Arg.var p.fst))
            fun p =>
            Expr.store
            (Arg.var p_21.fst)
            (Arg.var p.fst)
            (Expr.jump Js.fst ()))
            Blocks.nil)
            fun Js =>
            Expr.let_
            (sbvaOp2 (.cmp .ugt i64 .bool rfl) (Arg.var p_20.fst) (Arg.imm 268435455))
            fun p =>
            Expr.jnz (Arg.var p.fst)
            (Expr.jump Js.fst
            (Arg.imm 268435455, ()))
            (Expr.let_
            (sbvaOp1 (.trunc 64 32) (Arg.var p_20.fst))
            fun p =>
            Expr.jump Js.fst
            (Arg.var p.fst, ()))))
           (Expr.jump Js.fst ()))
        Blocks.nil)
       fun Js =>
       Expr.let_
        (sbvaOp2 (.cmp .eq i32 .bool rfl) (Arg.var p.fst) (Arg.var vis_n_j))
        fun p =>
        Expr.jnz (Arg.var p.fst)
        (Expr.let_
         (sbvaOp2 (.cmp .ult i32 .bool rfl) (Arg.var hop) (Arg.imm 2))
         fun p =>
         Expr.jnz (Arg.var p.fst)
          (Expr.let_
          (sbvaOp2 (.cmp .ult i32 .bool rfl) (Arg.var vis_n_j) (Arg.var cap))
          fun p =>
          Expr.jnz (Arg.var p.fst)
           (Expr.let_
            (sbvaOp1 (.zext 32 64) (Arg.var vis_n_j))
            fun p =>
            Expr.let_
            (sbvaOp2 (.mul i64) (Arg.var p.fst) (Arg.imm 4))
            fun p =>
            Expr.let_
            (sbvaOp2 (.add i64) (Arg.var pMinClr) (Arg.var p.fst))
            fun p =>
            Expr.store (Arg.var ov) (Arg.var p.fst)
            (Expr.let_
            (sbvaOp1 (.zext 32 64) (Arg.var vis_n_j))
            fun p =>
            Expr.let_
            (sbvaOp1 (.sext 32 64) (Arg.imm 1))
            fun p_2 =>
            Expr.let_
            (sbvaOp2 (.shl i64) (Arg.var p.fst) (Arg.var p_2.fst))
            fun p =>
            Expr.let_
            (sbvaOp2 (.mul i64) (Arg.var p.fst) (Arg.imm 4))
            fun p =>
            Expr.let_
            (sbvaOp2 (.add i64) (Arg.var pRepr) (Arg.var p.fst))
            fun p =>
            Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
            (Expr.let_
            (sbvaOp1 (.zext 32 64) (Arg.var vis_n_j))
            fun p =>
            Expr.let_
            (sbvaOp1 (.sext 32 64) (Arg.imm 1))
            fun p_3 =>
            Expr.let_
            (sbvaOp2 (.shl i64) (Arg.var p.fst) (Arg.var p_3.fst))
            fun p =>
            Expr.let_
            (sbvaOp2 (.add i64) (Arg.var p.fst) (Arg.imm 1))
            fun p =>
            Expr.let_
            (sbvaOp2 (.mul i64) (Arg.var p.fst) (Arg.imm 4))
            fun p =>
            Expr.let_
            (sbvaOp2 (.add i64) (Arg.var pRepr) (Arg.var p.fst))
            fun p =>
            Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
            (Expr.let_
            (sbvaOp1 (.zext 32 64) (Arg.var vis_n_j))
            fun p =>
            Expr.let_
            (sbvaOp2 (.mul i64) (Arg.var p.fst) (Arg.imm 8))
            fun p =>
            Expr.let_
            (sbvaOp2 (.add i64) (Arg.var pSimSig) (Arg.var p.fst))
            fun p =>
            Expr.store (t := i64) (Arg.imm 0) (Arg.var p.fst)
            (Expr.let_
            (sbvaOp2 (.add i32) (Arg.var vis_n_j) (Arg.imm 1))
            fun p =>
            Expr.jump Js.fst (Arg.var p.fst, ()))))))
           (Expr.jump Js.fst (Arg.var vis_n_j, ())))
          (Expr.jump Js.fst (Arg.var vis_n_j, ())))
        (Expr.jump Js.fst (Arg.var vis_n_j, ())))
      Blocks.nil)
    fun Js_1 =>
    Expr.let_
     (sbvaOp2 (.cmp .ult i32 .bool rfl) (Arg.var p.fst) (Arg.var vis_n_j))
     fun p_1 =>
     Expr.jnz (Arg.var p_1.fst)
      (Expr.let_ (sbvaOp1 (.zext 32 64) (Arg.var p.fst)) fun p_2 =>
      Expr.let_ (sbvaOp2 (.mul i64) (Arg.var p_2.fst) (Arg.imm 4))
       fun p_3 =>
       Expr.let_
        (sbvaOp2 (.add i64) (Arg.var pMinClr) (Arg.var p_3.fst))
        fun p_4 =>
        Expr.load i32 (Arg.var p_4.fst) fun ld =>
        Expr.let_
         (sbvaOp2 (.cmp .ne i32 .bool rfl) (Arg.var ld) (Arg.var ov))
         fun p_5 =>
         Expr.jnz (Arg.var p_5.fst)
          (Expr.let_
          (sbvaOp2 (.add i32) (Arg.var p.fst) (Arg.imm 1))
          fun p => Expr.jump Js.fst (Arg.var p.fst, ()))
          (Expr.jump Js_1.fst ()))
      (Expr.jump Js_1.fst ()))
   Blocks.nil)
  fun Js => Expr.jump Js.fst (Arg.imm 0, ())

private abbrev sbvaL14Expr (pWorkStk1 pWsort pWvec pMinClr pSimSig : Val i64)
    (ncntd best_c fb_bl vis_n_h : Val i32) (J9 : Cont [i32, i32, i32]) :
    Expr Val Cont [i32] :=
    ((Blocks.cons (ts := [])
   (fun _p =>
    Expr.group (sig := [[i32, i32, i32, i64, i32]])
    (fun Js =>
     Blocks.cons
      (fun p =>
      Expr.group (sig := [[]])
       (fun _Js =>
        Blocks.cons
        (fun _p_1 =>
         Expr.group (sig := [[i32]])
          (fun _Js =>
          Blocks.cons
           (fun p_2 =>
            Expr.jump J9 (Arg.var p.fst, Arg.var p_2.fst, Arg.var p.snd.snd.fst, ()))
           Blocks.nil)
          fun Js =>
          Expr.let_
          (sbvaOp2 (.cmp .eq i32 .bool rfl) (Arg.var p.snd.fst) (Arg.imm 4294967295))
          fun p_2 =>
          Expr.jnz (Arg.var p_2.fst)
           (Expr.jump Js.fst
            (Arg.var fb_bl, ()))
           (Expr.jump Js.fst (Arg.var p.snd.fst, ())))
        Blocks.nil)
       fun Js_1 =>
       Expr.let_
        (sbvaOp2 (.cmp .ult i32 .bool rfl) (Arg.var p.snd.snd.fst) (Arg.var ncntd))
        fun p_1 =>
        Expr.jnz (Arg.var p_1.fst)
        (Expr.let_
         (sbvaOp2 (.cmp .ult i32 .bool rfl) (Arg.var p.snd.snd.snd.snd.fst) (Arg.imm 64))
         fun p_2 =>
         Expr.jnz (Arg.var p_2.fst)
          (Expr.let_
          (sbvaOp1 (.zext 32 64) (Arg.var p.snd.snd.fst))
          fun p_3 =>
          Expr.let_
           (sbvaOp2 (.mul i64) (Arg.var p_3.fst) (Arg.imm 4))
           fun p_4 =>
           Expr.let_
            (sbvaOp2 (.add i64) (Arg.var pWorkStk1) (Arg.var p_4.fst))
            fun p_5 =>
            Expr.load i32 (Arg.var p_5.fst) fun ld =>
            Expr.group (sig := [[i32, i32, i64, i32]])
            (fun _Js_2 =>
            Blocks.cons
            (fun p_6 =>
            Expr.let_
            (sbvaOp2 (.add i32) (Arg.var p.snd.snd.fst) (Arg.imm 1))
            fun p =>
            Expr.jump Js.fst
            (Arg.var p_6.fst, Arg.var p_6.snd.fst, Arg.var p.fst,
            Arg.var p_6.snd.snd.fst, Arg.var p_6.snd.snd.snd.fst, ()))
            Blocks.nil)
            fun Js =>
            Expr.let_ (sbvaOp1 (.zext 32 64) (Arg.var ld))
            fun p_6 =>
            Expr.let_
            (sbvaOp2 (.mul i64) (Arg.var p_6.fst) (Arg.imm 4))
            fun p_7 =>
            Expr.let_
            (sbvaOp2 (.add i64) (Arg.var pWsort) (Arg.var p_7.fst))
            fun p_8 =>
            Expr.load i32 (Arg.var p_8.fst) fun ld_1 =>
            Expr.let_
            (sbvaOp2 (.cmp .eq i32 .bool rfl) (Arg.var ld_1) (Arg.var best_c))
            fun p_9 =>
            Expr.jnz (Arg.var p_9.fst)
            (Expr.let_
            (sbvaOp2 (.add i32) (Arg.var p.snd.snd.snd.snd.fst) (Arg.imm 1))
            fun p_10 =>
            Expr.let_
            (sbvaOp2 (.lshr i32) (Arg.var ld) (Arg.imm 1))
            fun p_11 =>
            Expr.group (sig := [[i64, i32]])
            (fun _Js_2 =>
            Blocks.cons
            (fun p_12 =>
            Expr.let_
            (sbvaOp1 (.zext 32 64) (Arg.var ld))
            fun p_13 =>
            Expr.let_
            (sbvaOp1 (.sext 32 64) (Arg.imm 1))
            fun p_14 =>
            Expr.let_
            (sbvaOp2 (.shl i64) (Arg.var p_13.fst) (Arg.var p_14.fst))
            fun p_15 =>
            Expr.let_
            (sbvaOp2 (.add i64) (Arg.var p_15.fst) (Arg.imm 1))
            fun p_16 =>
            Expr.let_
            (sbvaOp2 (.mul i64) (Arg.var p_16.fst) (Arg.imm 4))
            fun p_17 =>
            Expr.let_
            (sbvaOp2 (.add i64) (Arg.var pWvec) (Arg.var p_17.fst))
            fun p_18 =>
            Expr.load i32 (Arg.var p_18.fst) fun ld_2 =>
            Expr.group (sig := [[i32, i32, i64]])
            (fun _Js_3 =>
            Blocks.cons
            (fun p =>
            Expr.jump Js.fst
            (Arg.var p.fst,
            Arg.var p.snd.fst,
            Arg.var p.snd.snd.fst,
            Arg.var p_10.fst, ()))
            Blocks.nil)
            fun Js =>
            Expr.let_
            (sbvaOp2 (.cmp .eq i32 .bool rfl) (Arg.var p.snd.fst) (Arg.imm 4294967295))
            fun p_19 =>
            Expr.jnz (Arg.var p_19.fst)
            (Expr.jump Js.fst
            (Arg.var ld_2, Arg.var ld,
            Arg.var p_12.fst, ()))
            (Expr.let_
            (sbvaOp2 (.cmp .ugt i64 .bool rfl) (Arg.var p_12.fst) (Arg.var p.snd.snd.snd.fst))
            fun p_20 =>
            Expr.jnz (Arg.var p_20.fst)
            (Expr.jump Js.fst
            (Arg.var ld_2, Arg.var ld,
            Arg.var p_12.fst, ()))
            (Expr.let_
            (sbvaOp2 (.cmp .eq i64 .bool rfl) (Arg.var p_12.fst) (Arg.var p.snd.snd.snd.fst))
            fun p_21 =>
            Expr.jnz (Arg.var p_21.fst)
            (Expr.let_
            (sbvaOp2 (.cmp .ugt i32 .bool rfl) (Arg.var ld_2) (Arg.var p.fst))
            fun p_22 =>
            Expr.jnz
            (Arg.var p_22.fst)
            (Expr.jump Js.fst
            (Arg.var ld_2,
            Arg.var ld,
            Arg.var p_12.fst,
            ()))
            (Expr.let_
            (sbvaOp2 (.cmp .eq i32 .bool rfl) (Arg.var ld_2) (Arg.var p.fst))
            fun p_23 =>
            Expr.jnz
            (Arg.var p_23.fst)
            (Expr.let_
            (sbvaOp2 (.cmp .ult i32 .bool rfl) (Arg.var ld) (Arg.var p.snd.fst))
            fun p_24 =>
            Expr.jnz
            (Arg.var
            p_24.fst)
            (Expr.jump
            Js.fst
            (Arg.var ld_2,
            Arg.var ld,
            Arg.var
            p_12.fst,
            ()))
            (Expr.jump
            Js.fst
            (Arg.var
            p.fst,
            Arg.var
            p.snd.fst,
            Arg.var
            p.snd.snd.snd.fst,
            ())))
            (Expr.jump Js.fst
            (Arg.var p.fst,
            Arg.var
            p.snd.fst,
            Arg.var
            p.snd.snd.snd.fst,
            ()))))
            (Expr.jump Js.fst
            (Arg.var p.fst,
            Arg.var p.snd.fst,
            Arg.var
            p.snd.snd.snd.fst,
            ())))))
            Blocks.nil)
            fun Js =>
            Expr.group (sig := [[i32]])
            (fun Js_2 =>
            Blocks.cons
            (fun p =>
            Expr.let_
            (sbvaOp2 (.cmp .ult i32 .bool rfl) (Arg.var p.fst) (Arg.var vis_n_h))
            fun p_12 =>
            Expr.jnz (Arg.var p_12.fst)
            (Expr.let_
            (sbvaOp1 (.zext 32 64) (Arg.var p.fst))
            fun p_13 =>
            Expr.let_
            (sbvaOp2 (.mul i64) (Arg.var p_13.fst) (Arg.imm 4))
            fun p_14 =>
            Expr.let_
            (sbvaOp2 (.add i64) (Arg.var pMinClr) (Arg.var p_14.fst))
            fun p_15 =>
            Expr.load i32 (Arg.var p_15.fst) fun ld =>
            Expr.let_
            (sbvaOp2 (.cmp .eq i32 .bool rfl) (Arg.var ld) (Arg.var p_11.fst))
            fun p_16 =>
            Expr.jnz (Arg.var p_16.fst)
            (Expr.let_
            (sbvaOp1 (.zext 32 64) (Arg.var p.fst))
            fun p_17 =>
            Expr.let_
            (sbvaOp2 (.mul i64) (Arg.var p_17.fst) (Arg.imm 8))
            fun p_18 =>
            Expr.let_
            (sbvaOp2 (.add i64) (Arg.var pSimSig) (Arg.var p_18.fst))
            fun p_19 =>
            Expr.load i64 (Arg.var p_19.fst)
            fun ld =>
            Expr.jump Js.fst
            (Arg.var ld, Arg.var p.fst,
            ()))
            (Expr.let_
            (sbvaOp2 (.add i32) (Arg.var p.fst) (Arg.imm 1))
            fun p =>
            Expr.jump Js_2.fst
            (Arg.var p.fst, ())))
            (Expr.jump Js.fst (Arg.imm 0, Arg.var p.fst, ())))
            Blocks.nil)
            fun Js => Expr.jump Js.fst (Arg.imm 0, ()))
            (Expr.jump Js.fst
            (Arg.var p.fst, Arg.var p.snd.fst, Arg.var p.snd.snd.snd.fst,
            Arg.var p.snd.snd.snd.snd.fst, ())))
          (Expr.jump Js_1.fst ()))
        (Expr.jump Js_1.fst ()))
      Blocks.nil)
    fun Js => Expr.jump Js.fst (Arg.imm 0, Arg.imm 4294967295, Arg.imm 0, Arg.imm 0, Arg.imm 0, ()))
   Blocks.nil).get
  Member.here ())

private abbrev sbvaL41Expr (pWstk pArena p1 end64 : Val i64) (Jcl : Cont [i64, i32, i32]) :
    Expr Val Cont [i32] :=
Expr.group (sig := [[i64, i32, i32]])
  (fun _Js =>
  Blocks.cons (fun p => Expr.jump Jcl (Arg.var p.fst, Arg.var p.snd.fst, Arg.var p.snd.snd.fst, ()))
   Blocks.nil)
  fun Js =>
  Expr.let_
  (sbvaOp2 (.cmp .ult i64 .bool rfl) (Arg.var p1) (Arg.var end64))
  fun p_1 =>
  Expr.jnz (Arg.var p_1.fst)
   (Expr.let_ (sbvaOp2 (.mul i64) (Arg.var p1) (Arg.imm 4))
    fun p_2 =>
    Expr.let_ (sbvaOp2 (.add i64) (Arg.var pWstk) (Arg.var p_2.fst))
    fun p_3 =>
    Expr.load i32 (Arg.var p_3.fst) fun ld =>
     Expr.let_
      (sbvaOp2 (.add i64) (Arg.var p1) (Arg.imm 1))
      fun p =>
      Expr.group (sig := [[i32]])
      (fun _Js_1 =>
       Blocks.cons (fun p_4 => Expr.jump Js.fst (Arg.var p.fst, Arg.var ld, Arg.var p_4.fst, ()))
        Blocks.nil)
      fun Js =>
      Expr.let_ (sbvaOp1 (.zext 32 64) (Arg.var ld)) fun p =>
       Expr.let_ (sbvaOp2 (.mul i64) (Arg.var p.fst) (Arg.imm 4))
        fun p =>
        Expr.let_
        (sbvaOp2 (.add i64) (Arg.var pArena) (Arg.var p.fst))
        fun p =>
        Expr.load i32 (Arg.var p.fst) fun ld_1 =>
         Expr.let_
          (sbvaOp2 (.or i32) (Arg.imm 524288) (Arg.imm 4194304))
          fun p =>
          Expr.let_
          (sbvaOp2 (.and i32) (Arg.var ld_1) (Arg.var p.fst))
          fun p =>
          Expr.let_
           (sbvaOp2 (.cmp .eq i32 .bool rfl) (Arg.var p.fst) (Arg.imm 0))
           fun p =>
           Expr.jnz (Arg.var p.fst)
            (Expr.let_ (sbvaOp1 (.zext 32 64) (Arg.var ld))
            fun p =>
            Expr.let_
            (sbvaOp2 (.add i64) (Arg.var p.fst) (Arg.imm 2))
            fun p =>
            Expr.let_
            (sbvaOp2 (.mul i64) (Arg.var p.fst) (Arg.imm 4))
            fun p =>
            Expr.let_
            (sbvaOp2 (.add i64) (Arg.var pArena) (Arg.var p.fst))
            fun p =>
            Expr.load i32 (Arg.var p.fst) fun ld =>
            Expr.group (sig := [[i32]])
            (fun _Js_1 =>
            Blocks.cons (fun p => Expr.jump Js.fst (Arg.var p.fst, ()))
            Blocks.nil)
            fun Js =>
            Expr.let_
            (sbvaOp2 (.cmp .ule i32 .bool rfl) (Arg.var ld) (Arg.imm 5))
            fun p =>
            Expr.jnz (Arg.var p.fst)
            (Expr.let_
            (sbvaOp2 (.cmp .ugt i32 .bool rfl) (Arg.var ld) (Arg.imm 0))
            fun p =>
            Expr.jnz (Arg.var p.fst) (Expr.jump Js.fst (Arg.var ld, ()))
            (Expr.jump Js.fst (Arg.imm 0, ())))
            (Expr.jump Js.fst (Arg.imm 0, ())))
            (Expr.jump Js.fst (Arg.imm 0, ())))
   (Expr.jump Js.fst (Arg.var p1, Arg.imm 0, Arg.imm 0, ()))

private abbrev sbvaL11ContExpr (pWorkStk1 pWsort pMinClr pRepr pSimSig : Val i64)
    (ncntd best_c ci vis_n seed_cap : Val i32) (Jp : Cont [i32, i32]) (J12 : Cont []) :
    Expr Val Cont [i32] :=
    (Expr.let_
  (sbvaOp2 (.cmp .ult i32 .bool rfl) (Arg.var ci) (Arg.var ncntd))
  fun p =>
  Expr.jnz (Arg.var p.fst)
  (Expr.let_
   (sbvaOp2 (.cmp .ult i32 .bool rfl) (Arg.var vis_n) (Arg.var seed_cap))
   fun p =>
   Expr.jnz (Arg.var p.fst)
    (Expr.let_ (sbvaOp1 (.zext 32 64) (Arg.var ci)) fun p =>
    Expr.let_ (sbvaOp2 (.mul i64) (Arg.var p.fst) (Arg.imm 4)) fun p =>
     Expr.let_
      (sbvaOp2 (.add i64) (Arg.var pWorkStk1) (Arg.var p.fst))
      fun p =>
      Expr.load i32 (Arg.var p.fst) fun ld =>
      Expr.group (sig := [[i32]])
       (fun _Js =>
        Blocks.cons
        (fun p =>
         Expr.let_
          (sbvaOp2 (.add i32) (Arg.var ci) (Arg.imm 1))
          fun p_1 => Expr.jump Jp (Arg.var p_1.fst, Arg.var p.fst, ()))
        Blocks.nil)
       fun Js =>
       Expr.let_ (sbvaOp1 (.zext 32 64) (Arg.var ld)) fun p =>
        Expr.let_ (sbvaOp2 (.mul i64) (Arg.var p.fst) (Arg.imm 4))
        fun p =>
        Expr.let_
         (sbvaOp2 (.add i64) (Arg.var pWsort) (Arg.var p.fst))
         fun p =>
         Expr.load i32 (Arg.var p.fst) fun ld_1 =>
          Expr.let_
          (sbvaOp2 (.cmp .eq i32 .bool rfl) (Arg.var ld_1) (Arg.var best_c))
          fun p =>
          Expr.jnz (Arg.var p.fst)
           (Expr.let_
            (sbvaOp2 (.lshr i32) (Arg.var ld) (Arg.imm 1))
            fun p =>
            Expr.group (sig := [[i32]])
            (fun Js_1 =>
            Blocks.cons
            (fun p_1 =>
            Expr.group (sig := [[]])
            (fun _Js_2 =>
            Blocks.cons
            (fun _p_2 =>
            Expr.group (sig := [[i32]])
            (fun _Js_3 =>
            Blocks.cons (fun p => Expr.jump Js.fst (Arg.var p.fst, ()))
            Blocks.nil)
            fun Js =>
            Expr.let_
            (sbvaOp2 (.cmp .eq i32 .bool rfl) (Arg.var p_1.fst) (Arg.var vis_n))
            fun p_3 =>
            Expr.jnz (Arg.var p_3.fst)
            (Expr.let_
            (sbvaOp1 (.zext 32 64) (Arg.var vis_n))
            fun p_4 =>
            Expr.let_
            (sbvaOp2 (.mul i64) (Arg.var p_4.fst) (Arg.imm 4))
            fun p_5 =>
            Expr.let_
            (sbvaOp2 (.add i64) (Arg.var pMinClr) (Arg.var p_5.fst))
            fun p_6 =>
            Expr.store (Arg.var p.fst) (Arg.var p_6.fst)
            (Expr.let_
            (sbvaOp1 (.zext 32 64) (Arg.var vis_n))
            fun p =>
            Expr.let_
            (sbvaOp1 (.sext 32 64) (Arg.imm 1))
            fun p_7 =>
            Expr.let_
            (sbvaOp2 (.shl i64) (Arg.var p.fst) (Arg.var p_7.fst))
            fun p =>
            Expr.let_
            (sbvaOp2 (.mul i64) (Arg.var p.fst) (Arg.imm 4))
            fun p =>
            Expr.let_
            (sbvaOp2 (.add i64) (Arg.var pRepr) (Arg.var p.fst))
            fun p =>
            Expr.store (t := i32) (Arg.imm 0) (Arg.var p.fst)
            (Expr.let_
            (sbvaOp1 (.zext 32 64) (Arg.var vis_n))
            fun p =>
            Expr.let_
            (sbvaOp1 (.sext 32 64) (Arg.imm 1))
            fun p_8 =>
            Expr.let_
            (sbvaOp2 (.shl i64) (Arg.var p.fst) (Arg.var p_8.fst))
            fun p =>
            Expr.let_
            (sbvaOp2 (.add i64) (Arg.var p.fst) (Arg.imm 1))
            fun p =>
            Expr.let_
            (sbvaOp2 (.mul i64) (Arg.var p.fst) (Arg.imm 4))
            fun p =>
            Expr.let_
            (sbvaOp2 (.add i64) (Arg.var pRepr) (Arg.var p.fst))
            fun p =>
            Expr.store (t := i32) (Arg.imm 0)
            (Arg.var p.fst)
            (Expr.let_
            (sbvaOp1 (.zext 32 64) (Arg.var vis_n))
            fun p =>
            Expr.let_
            (sbvaOp2 (.mul i64) (Arg.var p.fst) (Arg.imm 8))
            fun p =>
            Expr.let_
            (sbvaOp2 (.add i64) (Arg.var pSimSig) (Arg.var p.fst))
            fun p =>
            Expr.store (t := i64) (Arg.imm 0)
            (Arg.var p.fst)
            (Expr.let_
            (sbvaOp2 (.add i32) (Arg.var vis_n) (Arg.imm 1))
            fun p =>
            Expr.jump Js.fst
            (Arg.var p.fst,
            ()))))))
            (Expr.jump Js.fst (Arg.var vis_n, ())))
            Blocks.nil)
            fun Js =>
            Expr.let_
            (sbvaOp2 (.cmp .ult i32 .bool rfl) (Arg.var p_1.fst) (Arg.var vis_n))
            fun p_2 =>
            Expr.jnz (Arg.var p_2.fst)
            (Expr.let_
            (sbvaOp1 (.zext 32 64) (Arg.var p_1.fst))
            fun p_3 =>
            Expr.let_
            (sbvaOp2 (.mul i64) (Arg.var p_3.fst) (Arg.imm 4))
            fun p_4 =>
            Expr.let_
            (sbvaOp2 (.add i64) (Arg.var pMinClr) (Arg.var p_4.fst))
            fun p_5 =>
            Expr.load i32 (Arg.var p_5.fst) fun ld =>
            Expr.let_
            (sbvaOp2 (.cmp .ne i32 .bool rfl) (Arg.var ld) (Arg.var p.fst))
            fun p =>
            Expr.jnz (Arg.var p.fst)
            (Expr.let_
            (sbvaOp2 (.add i32) (Arg.var p_1.fst) (Arg.imm 1))
            fun p => Expr.jump Js_1.fst (Arg.var p.fst, ()))
            (Expr.jump Js.fst ()))
            (Expr.jump Js.fst ()))
            Blocks.nil)
            fun Js => Expr.jump Js.fst (Arg.imm 0, ()))
           (Expr.jump Js.fst (Arg.var vis_n, ())))
    (Expr.jump J12 ()))
  (Expr.jump J12 ()))

private theorem sbva_l14_wp {Γ : Env} {Q : Post [i32]} {X : XPost}
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m14 : Mem 64}
    {ncntd best_c best_lit vis_n_h cap : BitVec 32}
    {mc14 rp14 : List (BitVec 32)} {sig14 : List (BitVec 64)}
    {J9 : Cont [i32, i32, i32]}
    (hcv_le : s.core.cur_vars ≤ c.max_vars) (hwv_len : s.core.wvec.length = 4 * c.max_vars)
    (hws_len : s.scratch.wsort.length = 2 * c.max_vars)
    (hws1_len : s.scratch.work_stk1.length = 2 * c.max_vars)
    (hnc_le : ncntd.toNat ≤ 2 * s.core.cur_vars) (h2cv_lt32 : 2 * s.core.cur_vars < 2 ^ 32)
    (hcntd_ok : ∀ i < ncntd.toNat, (s.scratch.work_stk1[i]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hbc_ge2 : 2 ≤ best_c.toNat)
    (hbl_ok : 2 ≤ best_c.toNat → best_lit.toNat < 2 * s.core.cur_vars)
    (hcap_le_cv : cap.toNat ≤ s.core.cur_vars) (hcap_le_32 : cap.toNat ≤ 32)
    (hvn14_c : vis_n_h.toNat ≤ cap.toNat)
    (hmc14 : mc14.length = c.max_vars) (hrp14 : rp14.length = 2 * c.max_vars)
    (hsig14 : sig14.length = c.max_vars)
    (hm14 : (SbvaMem c s mc14 rp14 sig14 ⋆ R) m14)
    (hJ9 : ∀ (st : BitVec 32 × BitVec 32 × BitVec 32 × List (BitVec 32) ×
        List (BitVec 32) × List (BitVec 64)) (m' : Mem 64),
      sbvaTbJoin c s R best_c st.1 st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2.1 st.2.2.2.2.2 m' →
      J9 (st.1, st.2.1, st.2.2.1, ()) m') :
    wp Γ Q X (sbvaL14Expr c.pWorkStk1 c.pWsort c.pWvec c.pMinClr c.pSimSig
      ncntd best_c best_lit vis_n_h J9) m14 := by
  dsimp only [sbvaL14Expr, sbvaOp1, sbvaOp2]
  c0_hfast_nogrp
  refine wp_loop_inv
    (fun (best_deg2, best_lit2, ci2, best_sc, tt, ()) ml2 =>
      ml2 = m14 ∧ ci2.toNat ≤ ncntd.toNat ∧
      (best_lit2 = 0xFFFFFFFF#32 ∨ best_lit2.toNat < 2 * s.core.cur_vars))
    (fun (_, _, ci2, _, _, _) _ => ncntd.toNat - ci2.toNat)
    (fun J3 hJ3 => hJ3 (0#32, 0xFFFFFFFF#32, 0#32, 0#64, 0#32, ()) m14
      ⟨rfl, Nat.zero_le _, Or.inl rfl⟩)
    (fun J3 (best_deg2, best_lit2, ci2, best_sc, tt, ()) ml2
        ⟨hml2, hci2_le, hbl2⟩ ih3 => ?_)
  subst ml2
  c0_hfast_nogrp
  -- Exit join `L16` (`sig = [[]]`) of `L15` -> `L17` (`if (best_lit == -1)`) -> `J9`
  refine wp_join0 (fun m16 => m16 = m14)
    (fun J16 m16 hm16 => by
      subst m16
      c0_hfast
      · exact hJ9 ⟨best_deg2, best_lit, ci2, mc14, rp14, sig14⟩ m14
          ⟨fun _ => hbl_ok hbc_ge2, hmc14, hrp14, hsig14, hm14⟩
      · refine hJ9 ⟨best_deg2, best_lit2, ci2, mc14, rp14, sig14⟩ m14
          ⟨fun _ => ?_, hmc14, hrp14, hsig14, hm14⟩
        rcases hbl2 with hff | hlt
        · exact absurd hff (by assumption)
        · exact hlt)
    (fun J16 hJ16 => ?_)
  c0_hsplit
  · c0_hsplit
    {
    have hci2_lt : ci2.toNat < ncntd.toNat := by assumption
    have hci2_64 : (BitVec.setWidth 64 ci2).toNat = ci2.toNat :=
      bv64_setWidth_32 ci2
    have hclit_lt :
        (s.scratch.work_stk1[ci2.toNat]'(by omega)).toNat <
          2 * s.core.cur_vars := by
      have := hcntd_ok ci2.toNat hci2_lt
      rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
    have hclit_lt64 :
        (s.scratch.work_stk1[(BitVec.setWidth 64 ci2).toNat]'(by
          rw [hci2_64]; omega)).toNat < 2 * s.core.cur_vars := by
      simpa only [hci2_64] using hclit_lt
    have hci2_1 : (ci2 + 1#32).toNat = ci2.toNat + 1 :=
      sbva_bv32_add1 hci2_lt (Nat.lt_of_le_of_lt hnc_le h2cv_lt32)
    have h2clit :
        ((BitVec.setWidth 64
          (s.scratch.work_stk1[ci2.toNat]'(by omega)) <<< (1 : Nat)) + 1#64).toNat =
          2 * (s.scratch.work_stk1[ci2.toNat]'(by omega)).toNat + 1 :=
      sbva_bw64_shl1_add1 _
    have hclit_wvec :
        ((BitVec.setWidth 64
          (s.scratch.work_stk1[(BitVec.setWidth 64 ci2).toNat]'(by
            rw [hci2_64]; omega)) <<< (1 : Nat)) + 1#64).toNat <
          s.core.wvec.length := by
      simp only [hci2_64, h2clit, hwv_len]; omega
    c0_hfast_nogrp
    -- Join `L18` (`if (cnt[clit] == best_c)`) carrying `(bd, bl, bsc, tt)`
    refine wp_join_state
      (α := BitVec 32 × BitVec 32 × BitVec 64 × BitVec 32)
      (fun st => (st.1, st.2.1, st.2.2.1, st.2.2.2, ()))
      (fun ⟨bd3, bl3, bsc3, tt3⟩ m18 =>
        m18 = m14 ∧ (bl3 = 0xFFFFFFFF#32 ∨ bl3.toNat < 2 * s.core.cur_vars))
      (fun _ ⟨bd3, bl3, bsc3, tt3⟩ m18 ⟨hm18, hbl3⟩ => by
        subst m18
        c0_hfast
        exact ih3 (bd3, bl3, ci2 + 1#32, bsc3, tt3, ()) m14
          (by dsimp only; rw [hci2_1]; omega)
          ⟨rfl, by rw [hci2_1]; omega, hbl3⟩)
      (fun J18 hJ18 => ?_)
    c0_hfast_nogrp
    · -- `break` join `L19` (`sig = [[i64, i32]]`, `(sc, k_brk)`) -> `L20` -> `J18`
      refine wp_join_state
        (α := BitVec 64 × BitVec 32) (fun p => (p.1, p.2, ()))
        (fun _ m19 => m19 = m14)
        (fun _ ⟨_sc, _kb⟩ m19 hm19 => by
          subst m19
          c0_hfast_nogrp
          refine wp_join_state
            (α := BitVec 32 × BitVec 32 × BitVec 64)
            (fun st => (st.1, st.2.1, st.2.2, ()))
            (fun ⟨bd4, bl4, bsc4⟩ m20 =>
              m20 = m14 ∧ (bl4 = 0xFFFFFFFF#32 ∨ bl4.toNat < 2 * s.core.cur_vars))
            (fun _ ⟨bd4, bl4, bsc4⟩ m20 ⟨hm20, hbl4⟩ => by
              subst m20
              exact hJ18 (bd4, bl4, bsc4, tt + 1#32) m14 ⟨rfl, hbl4⟩)
            (fun J20 hJ20 => by
              c0_hfast
              all_goals first
                | exact hJ20 (_, _, _) m14
                    ⟨rfl, Or.inr (by simpa only [hci2_64] using hclit_lt)⟩
                | exact hJ20 (best_deg2, best_lit2, best_sc) m14 ⟨rfl, hbl2⟩))
        (fun J19 hJ19 => by
          c0_hfast_nogrp
          -- `L21`: `while (k < vis_n_h)` inside `L19`
          refine wp_loop_inv
            (fun (k, ()) mk => mk = m14 ∧ k.toNat ≤ vis_n_h.toNat)
            (fun (k, ()) _ => vis_n_h.toNat - k.toNat)
            (fun Jk hJk => hJk (0#32, ()) m14 ⟨rfl, Nat.zero_le _⟩)
            (fun Jk (k, ()) mk ⟨hmk, hk_le⟩ ihk => ?_)
          subst mk
          have hk64 : (BitVec.setWidth 64 k).toNat = k.toNat := bv64_setWidth_32 k
          c0_hsplit
          · have hk_lt : k.toNat < vis_n_h.toNat := by assumption
            have hk_mc : (BitVec.setWidth 64 k).toNat < mc14.length := by
              rw [hk64, hmc14]
              exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hk_lt hvn14_c)
                (Nat.le_trans hcap_le_cv hcv_le)
            have hk_sig : (BitVec.setWidth 64 k).toNat < sig14.length := by
              rw [hk64, hsig14]
              exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hk_lt hvn14_c)
                (Nat.le_trans hcap_le_cv hcv_le)
            have hk1 : (k + 1#32).toNat = k.toNat + 1 :=
              sbva_bv32_add1 hk_lt
                (Nat.lt_of_le_of_lt hvn14_c
                  (Nat.lt_of_le_of_lt hcap_le_32 (by decide)))
            c0_hfast_nogrp
            · exact hJ19 (_, k) m14 rfl
            · exact ihk (k + 1#32, ()) m14
                (by dsimp only; rw [hk1]
                    exact Nat.sub_lt_sub_left hk_lt (Nat.lt_succ_self _))
                ⟨rfl, by rw [hk1]; exact hk_lt⟩
          · exact hJ19 (0#64, k) m14 rfl)
    · exact hJ18 (best_deg2, best_lit2, best_sc, tt) m14 ⟨rfl, hbl2⟩
    }
    · c0_hfast; exact hJ16 m14 rfl
  · c0_hfast; exact hJ16 m14 rfl

private theorem sbva_l35_wp {Γ : Env} {Q : Post [i32]} {X : XPost}
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {mj : Mem 64}
    {cap cw vis_n_j hop ov layer_n : BitVec 32}
    {mc_j rp_j : List (BitVec 32)} {sig_j : List (BitVec 64)}
    {J35 : Cont [i32]}
    (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hcap_le_cv : cap.toNat ≤ s.core.cur_vars) (hcap_le_32 : cap.toNat ≤ 32)
    (hlay_j : layer_n.toNat ≤ vis_n_j.toNat)
    (hmc_jl : mc_j.length = c.max_vars) (hrp_jl : rp_j.length = 2 * c.max_vars)
    (hsig_jl : sig_j.length = c.max_vars)
    (hvn_j1 : 1 ≤ vis_n_j.toNat) (hvn_jc : vis_n_j.toNat ≤ cap.toNat)
    (hmc_jok : ∀ k < vis_n_j.toNat, (mc_j[k]?.getD 0#32).toNat < s.core.cur_vars)
    (hmj' : (SbvaMem c s mc_j rp_j sig_j ⋆ R) mj)
    (hov_lt : ov.toNat < s.core.cur_vars)
    (hJ35 : ∀ (st : BitVec 32) (m' : Mem 64),
      (∃ mc35 rp35 sig35, layer_n.toNat ≤ st.toNat ∧
        sbvaBfsInv c s R cap mc35 rp35 sig35 st m') →
      J35 (id st, ()) m') :
    wp Γ Q X (sbvaL35Expr c.pMinClr c.pRepr c.pSimSig cw vis_n_j hop cap ov J35) mj := by
  dsimp only [sbvaL35Expr, sbvaOp1, sbvaOp2]
  refine wp_loop_inv
    (fun (k, ()) mk => mk = mj ∧ k.toNat ≤ vis_n_j.toNat)
    (fun (k, ()) _ => vis_n_j.toNat - k.toNat)
    (fun Jk hJk => hJk (0#32, ()) mj ⟨rfl, Nat.zero_le _⟩)
    (fun Jk (k, ()) mk ⟨hmk, hk_le⟩ ihk => ?_)
  subst mk
  have hk64 : (BitVec.setWidth 64 k).toNat = k.toNat :=
    bv64_setWidth_32 k
  c0_hfast_nogrp
  -- Exit join `L37` (`sig = [[]]`) of `L36`
  refine wp_join0 (fun m37 => m37 = mj)
    (fun J37 m37 hm37 => by
      subst m37
      c0_hfast_nogrp
      -- Join `L38` (`vis_n_k`)
      refine wp_join_state1 (t := i32) (α := BitVec 32) id
        (fun vn_k ma => ∃ mc_a rp_a sig_a,
          layer_n.toNat ≤ vn_k.toNat ∧
          sbvaBfsInv c s R cap mc_a rp_a sig_a vn_k ma)
        (fun _ vn_k ma ⟨mc_a, rp_a, sig_a, hlay_a, hmc_al,
            hrp_al, hsig_al, hvn_a1, hvn_ac, hmc_aok,
            hma⟩ => ?_)
        (fun Ja hJa => ?_)
      · -- `BLOCK L38`: Join `L39` (`if (k < vn_k)`) -> `hJ35`
        refine wp_join0
          (fun m39 => ∃ rp39 sig39,
            rp39.length = 2 * c.max_vars ∧
            sig39.length = c.max_vars ∧
            (SbvaMem c s mc_a rp39 sig39 ⋆ R) m39)
          (fun J39 m39 ⟨rp39, sig39, hrp39, hsig39, hm39⟩ =>
            by
            c0_hfast
            exact hJ35 vn_k m39
              ⟨mc_a, rp39, sig39, hlay_a, hmc_al, hrp39,
               hsig39, hvn_a1, hvn_ac, hmc_aok, hm39⟩)
          (fun J39 hJ39 => ?_)
        c0_hsplit
        · have hk_lt_a : k.toNat < vn_k.toNat :=
            by assumption
          have h2k0 :
              (BitVec.setWidth 64 k <<< (1 : Nat)).toNat =
                2 * k.toNat := sbva_bw64_shl1 _
          have h2k1 :
              ((BitVec.setWidth 64 k <<< (1 : Nat)) +
                1#64).toNat = 2 * k.toNat + 1 :=
            sbva_bw64_shl1_add1 _
          have hk_sig :
              (BitVec.setWidth 64 k).toNat <
                sig_a.length := by
            rw [hk64, hsig_al]
            exact Nat.lt_of_lt_of_le hk_lt_a
              (Nat.le_trans hvn_ac
                (Nat.le_trans hcap_le_cv hcv_le))
          have hk_rp1 :
              ((BitVec.setWidth 64 k <<< (1 : Nat)) +
                1#64).toNat < rp_a.length := by
            rw [h2k1, hrp_al]
            exact nat_two_add1_lt (Nat.lt_of_lt_of_le hk_lt_a
              (Nat.le_trans hvn_ac
                (Nat.le_trans hcap_le_cv hcv_le)))
          c0_hfast_nogrp
          -- Join `L40` (`add` ternary)
          refine wp_join_state1 (t := i32) (α := BitVec 32) id
            (fun _ m40 => ∃ sig40,
              sig40.length = c.max_vars ∧
              (SbvaMem c s mc_a rp_a sig40 ⋆ R) m40)
            (fun _ add m40 ⟨sig40, hsig40, hm40⟩ => by
              c0_hfast
              exact hJ39 _
                ⟨_, sig40, by rw [List.length_set, hrp_al],
                 hsig40, hm⟩)
            (fun J40 hJ40 => by
              c0_hfast
              · exact hJ40 268435455#32 _
                  ⟨_, by rw [List.length_set, hsig_al], hm⟩
              · exact hJ40 _ _
                  ⟨_, by rw [List.length_set, hsig_al], hm⟩)
        · c0_hfast
          exact hJ39 ma ⟨rp_a, sig_a, hrp_al, hsig_al, hma⟩
      · have hJaF := hJa vis_n_j mj
          ⟨mc_j, rp_j, sig_j, hlay_j, hmc_jl, hrp_jl,
           hsig_jl, hvn_j1, hvn_jc, hmc_jok, hmj'⟩
        c0_hsplit; rotate_left 1; · exact hJaF
        c0_hsplit; rotate_left 1; · exact hJaF
        c0_hsplit; rotate_left 1; · exact hJaF
        have hvnj_lt_cap : vis_n_j.toNat < cap.toNat :=
          by assumption
        have hvn_j1_lt : (vis_n_j + 1#32).toNat =
            vis_n_j.toNat + 1 :=
          sbva_bv32_add1 hvnj_lt_cap
            (Nat.lt_of_le_of_lt hcap_le_32 (by decide))
        have hvnj64 : (BitVec.setWidth 64 vis_n_j).toNat =
            vis_n_j.toNat := bv64_setWidth_32 vis_n_j
        have h2vnj0 :
            (BitVec.setWidth 64 vis_n_j <<<
              (1 : Nat)).toNat = 2 * vis_n_j.toNat :=
          sbva_bw64_shl1 _
        have h2vnj1 :
            ((BitVec.setWidth 64 vis_n_j <<< (1 : Nat)) +
              1#64).toNat = 2 * vis_n_j.toNat + 1 :=
          sbva_bw64_shl1_add1 _
        have hvnj_mc :
            (BitVec.setWidth 64 vis_n_j).toNat <
              mc_j.length := by
          rw [hvnj64, hmc_jl]
          exact Nat.lt_of_lt_of_le hvnj_lt_cap
            (Nat.le_trans hcap_le_cv hcv_le)
        have hvnj_rp0 :
            (BitVec.setWidth 64 vis_n_j <<< (1 : Nat)).toNat <
              rp_j.length := by
          rw [h2vnj0, hrp_jl]
          exact nat_two_lt (Nat.lt_of_lt_of_le hvnj_lt_cap
            (Nat.le_trans hcap_le_cv hcv_le))
        have hvnj_rp1 :
            ((BitVec.setWidth 64 vis_n_j <<< (1 : Nat)) +
              1#64).toNat <
              (rp_j.set (BitVec.setWidth 64 vis_n_j <<<
                (1 : Nat)).toNat 0#32).length := by
          rw [h2vnj1, List.length_set, hrp_jl]
          exact nat_two_add1_lt (Nat.lt_of_lt_of_le
            hvnj_lt_cap (Nat.le_trans hcap_le_cv hcv_le))
        have hvnj_sig :
            (BitVec.setWidth 64 vis_n_j).toNat <
              sig_j.length := by
          rw [hvnj64, hsig_jl]
          exact Nat.lt_of_lt_of_le hvnj_lt_cap
            (Nat.le_trans hcap_le_cv hcv_le)
        c0_hfast
        exact hJa (vis_n_j + 1#32) _
          ⟨_, _, _, by rw [hvn_j1_lt]; omega,
           by rw [List.length_set, hmc_jl],
           by rw [List.length_set, List.length_set,
             hrp_jl],
           by rw [List.length_set, hsig_jl],
           by rw [hvn_j1_lt]; omega,
           by rw [hvn_j1_lt]; omega,
           fun idx hidx => by
             by_cases he : idx = vis_n_j.toNat
             · subst he
               simp only [hvnj64]
               rw [List.getElem?_set_self (by omega),
                 Option.getD_some]
               exact hov_lt
             · simp only [hvnj64]
               rw [List.getElem?_set_ne (Ne.symm he)]
               exact hmc_jok idx
                 (by rw [hvn_j1_lt] at hidx; omega),
           hm⟩)
    (fun J37 hJ37 => by
      c0_hsplit
      · have hk_lt : k.toNat < vis_n_j.toNat :=
          by assumption
        have hk_mc : (BitVec.setWidth 64 k).toNat <
            mc_j.length := by
          rw [hk64, hmc_jl]
          exact Nat.lt_of_lt_of_le
            (Nat.lt_of_lt_of_le hk_lt hvn_jc)
            (Nat.le_trans hcap_le_cv hcv_le)
        have hk1 : (k + 1#32).toNat = k.toNat + 1 :=
          sbva_bv32_add1 hk_lt
            (Nat.lt_of_le_of_lt hvn_jc
              (Nat.lt_of_le_of_lt hcap_le_32 (by decide)))
        c0_hfast
        · exact ihk (k + 1#32, ()) mj
            (Nat.sub_lt_sub_left hk_lt (Nat.lt_succ_self _)
              |> fun h => by dsimp only; rw [hk1]; exact h)
            ⟨rfl, by rw [hk1]; exact hk_lt⟩
        · exact hJ37 mj rfl
      · exact hJ37 mj rfl)

private theorem sbva_l41_wp {Γ : Env} {Q : Post [i32]} {X : XPost}
    {F0 : CNF Nat} {F_cur : List (List Nat)} {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {mp' : Mem 64} {sl : BitVec 32} {off0 sz0 : Nat}
    {p end64 : BitVec 64}
    {mc_p rp_p : List (BitVec 32)} {sig_p : List (BitVec 64)}
    {Jcl : Cont [i64, i32, i32]}
    (hwcap : c.wcap < 2 * 2 ^ 28) (_har_b : c.arena_cap < 2 * 2 ^ 28)
    (_hcl : s.core.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hwstk_len : s.core.wstk.length = c.wcap) (hwlen_le : s.core.wlen ≤ c.wcap)
    (har_arr : s.core.arena.length = c.arena_cap) (hal_le : s.core.arena_len ≤ c.arena_cap)
    (hbd_sl' : off0 + sz0 ≤ s.core.wlen)
    (_hp_ge : off0 ≤ p.toNat) (hp_lt : p.toNat < off0 + sz0)
    (hp_ws : p.toNat < s.core.wstk.length)
    (hp1_n : (p + 1#64).toNat = p.toNat + 1)
    (hp1_mod : (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 = p.toNat + 1)
    (hend64 : end64.toNat = off0 + sz0)
    (hslice_p : DenseWatchSliceOk F_cur s.core sl.toNat p.toNat (off0 + sz0 - p.toNat))
    (hnbin_w0 : ((s.core.wstk[p.toNat]'hp_ws) &&& 0x80000000#32) = 0#32)
    (h2le : 2 ≤ off0 + sz0 - p.toNat)
    (hrem_nxt : DenseWatchSliceOk F_cur s.core sl.toNat (p.toNat + 2) (off0 + sz0 - p.toNat - 2))
    (hmp' : (SbvaMem c s mc_p rp_p sig_p ⋆ R) mp')
    (hJcl : ∀ (st : BitVec 64 × BitVec 32 × BitVec 32) (m' : Mem 64),
      (m' = mp' ∧ p.toNat < st.1.toNat ∧ st.1.toNat ≤ off0 + sz0 ∧
        DenseWatchSliceOk F_cur s.core sl.toNat st.1.toNat (off0 + sz0 - st.1.toNat) ∧
        (0 < st.2.2.toNat →
          (st.2.2 = 1#32 ∧ ((s.core.wstk[p.toNat]'hp_ws) &&& 0x80000000#32) ≠ 0#32 ∧
            ((s.core.wstk[p.toNat]'hp_ws) &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars) ∨
          (((s.core.wstk[p.toNat]'hp_ws) &&& 0x80000000#32) = 0#32 ∧ 1 ≤ st.2.2.toNat ∧
            st.2.2.toNat ≤ 5 ∧
            st.2.1.toNat ∈ fullArenaClauseRefsCore s.core ∧
            fullArenaClauseGarbCore s.core st.2.1.toNat = false ∧
            st.2.2.toNat = fullArenaClauseSizeCore s.core st.2.1.toNat))) →
      Jcl (st.1, st.2.1, st.2.2, ()) m') :
    wp Γ Q X (sbvaL41Expr c.pWstk c.pArena (p + 1#64) end64 Jcl) mp' := by
  let w0 := s.core.wstk[p.toNat]'hp_ws
  change ((w0 &&& 0x80000000#32) = 0#32) at hnbin_w0
  dsimp only [sbvaL41Expr, sbvaOp1, sbvaOp2]
  refine wp_join_state
    (α := BitVec 64 × BitVec 32 × BitVec 32)
    (fun st => (st.1, st.2.1, st.2.2, ()))
    (fun ⟨p_nxt, cr, clim⟩ m41 =>
      m41 = mp' ∧ p.toNat < p_nxt.toNat ∧
      p_nxt.toNat ≤ off0 + sz0 ∧
      DenseWatchSliceOk F_cur s.core sl.toNat p_nxt.toNat
        (off0 + sz0 - p_nxt.toNat) ∧
      (0 < clim.toNat →
        (w0 &&& 0x80000000#32) = 0#32 ∧ 1 ≤ clim.toNat ∧
        clim.toNat ≤ 5 ∧
        cr.toNat ∈ fullArenaClauseRefsCore s.core ∧
        fullArenaClauseGarbCore s.core cr.toNat = false ∧
        clim.toNat = fullArenaClauseSizeCore s.core cr.toNat))
    (fun _ ⟨p_nxt, cr, clim⟩ m41
        ⟨hm41, hp_inc, hp_nxt_le, hslice_nxt, hclim_41⟩ => by
      subst m41
      exact hJcl (p_nxt, cr, clim) mp'
        ⟨rfl, hp_inc, hp_nxt_le, hslice_nxt,
          fun hc => Or.inr (hclim_41 hc)⟩)
    (fun J41 hJ41 => ?_)
  c0_hsplit
  · have hp1_lt : p.toNat + 1 < off0 + sz0 := by
      rw [hend64] at hc
      rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc
    have hp1_ws : p.toNat + 1 < s.core.wstk.length := by omega
    have hp2_n : (p + 1#64 + 1#64).toNat = p.toNat + 2 :=
      sbva_bv64_add2 (Nat.lt_of_le_of_lt
        (Nat.le_trans hp1_lt (Nat.le_trans hbd_sl' hwlen_le))
        (Nat.lt_trans hwcap (by decide)))
    have ⟨_, hcr_ref0, _⟩ :=
      FullBvaFwdHelpers.fwd_slice_occ_info hslice_p (by omega)
        hp_ws hp1_ws hnbin_w0
    let cr := s.core.wstk[(p + 1#64).toNat]'(by
      rw [hp1_n]; exact hp1_ws)
    have hcr_ref : cr.toNat ∈ fullArenaClauseRefsCore s.core := by
      simpa only [cr, hp1_n] using hcr_ref0
    have hcr_wf := hw.arena.refs_wf _ hcr_ref
    have hcr_al : cr.toNat + 3 +
        fullArenaClauseSizeCore s.core cr.toNat ≤
        s.core.arena_len := by
      have h1 := hcr_wf.2.2.1; have h2 := hcr_wf.2.2.2.1
      omega
    have hcr2_n : (BitVec.setWidth 64 cr + 2#64).toNat =
        cr.toNat + 2 := sbva_bw64_add2 _
    have hcr_lt_ar : (BitVec.setWidth 64 cr).toNat <
        s.core.arena.length := by
      rw [bv64_setWidth_32]; omega
    have hcr2_lt_ar : (BitVec.setWidth 64 cr + 2#64).toNat <
        s.core.arena.length := by
      rw [hcr2_n]; omega
    have hsz_cr : (s.core.arena[cr.toNat + 2]'(by omega)).toNat =
        fullArenaClauseSizeCore s.core cr.toNat := by
      unfold fullArenaClauseSizeCore
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    c0_hfast_nogrp
    -- Join `L42` (`clim42`) after `cr = wstk[p1]`
    refine wp_join_state1 (t := i32) (α := BitVec 32) id
      (fun clim m42 =>
        m42 = mp' ∧
        (0 < clim.toNat →
          (w0 &&& 0x80000000#32) = 0#32 ∧ 1 ≤ clim.toNat ∧
          clim.toNat ≤ 5 ∧
          cr.toNat ∈ fullArenaClauseRefsCore s.core ∧
          fullArenaClauseGarbCore s.core cr.toNat = false ∧
          clim.toNat = fullArenaClauseSizeCore s.core cr.toNat))
      (fun _ clim m42 ⟨hm42, hclim_42⟩ => by
        subst m42
        exact hJ41 (p + 1#64 + 1#64, cr, clim) mp'
          ⟨rfl, by rw [hp2_n]; omega, by rw [hp2_n]; omega,
           by rw [hp2_n,
                show off0 + sz0 - (p.toNat + 2) =
                  off0 + sz0 - p.toNat - 2 by omega]
              exact hrem_nxt,
           hclim_42⟩)
      (fun J42 hJ42 => ?_)
    c0_hfast_nogrp
    · have hmask : (s.core.arena[cr.toNat]'(by omega) &&&
          (0x00080000#32 ||| 0x00400000#32)) = 0#32 := by
        simpa [bv64_setWidth_32] using ‹_›
      have hcr_ng : fullArenaClauseGarbCore s.core cr.toNat =
          false := by
        unfold fullArenaClauseGarbCore fullArenaHdrCore
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        simp [sbva_garb_zero_of_and_red hmask]
      -- Join `L43` (`clim43`) after `sz = ar[cr + 2]`
      refine wp_join_state1 (t := i32) (α := BitVec 32) id
        (fun clim m43 =>
          m43 = mp' ∧
          (0 < clim.toNat →
            1 ≤ clim.toNat ∧ clim.toNat ≤ 5 ∧
            clim.toNat = fullArenaClauseSizeCore s.core cr.toNat))
        (fun _ clim m43 ⟨hm43, hclim_43⟩ => by
          subst m43
          exact hJ42 clim mp'
            ⟨rfl, fun hc =>
              let ⟨h1, h5, hsz⟩ := hclim_43 hc
              ⟨hnbin_w0, h1, h5, hcr_ref, hcr_ng, hsz⟩⟩)
        (fun J43 hJ43 => by
          c0_hfast
          · have h_cr_raw :
                s.core.wstk[(p.toNat +
                  BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                  rw [hp1_mod]; exact hp1_ws) = cr := by
              simp only [cr, hp1_mod, hp1_n]
            have hidx_cr :
                ((s.core.wstk[(p.toNat +
                    BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                    rw [hp1_mod]; exact hp1_ws)).toNat +
                  BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 =
                  cr.toNat + 2 := by
              rw [h_cr_raw,
                show BitVec.toNat (2 : BitVec 64) = 2 from rfl]
              exact Nat.mod_eq_of_lt (by omega)
            have hsz_le5 : (s.core.arena[cr.toNat + 2]'(by
                omega)).toNat ≤ 5 := by
              have h1 : (s.core.arena[((s.core.wstk[(p.toNat +
                  BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                  rw [hp1_mod]; exact hp1_ws)).toNat +
                  BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
                  rw [hidx_cr]; omega)).toNat ≤
                  (5 : BitVec 32).toNat := by assumption
              simpa only [hidx_cr,
                show (5 : BitVec 32).toNat = 5 from rfl] using h1
            have hsz_gt0 : 0 < (s.core.arena[cr.toNat + 2]'(by
                omega)).toNat := by
              have h1 : (0 : BitVec 32).toNat <
                  (s.core.arena[((s.core.wstk[(p.toNat +
                  BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                  rw [hp1_mod]; exact hp1_ws)).toNat +
                  BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
                  rw [hidx_cr]; omega)).toNat := by assumption
              simpa only [hidx_cr,
                show (0 : BitVec 32).toNat = 0 from rfl] using h1
            refine hJ43 _ mp' ⟨rfl, fun _ => ?_⟩
            have heq : ∀ (hx : (BitVec.setWidth 64
                (s.core.wstk[(p + 1#64).toNat]'(by rw [hp1_n]; exact hp1_ws)) +
                2).toNat < s.core.arena.length),
                s.core.arena[(BitVec.setWidth 64
                  (s.core.wstk[(p + 1#64).toNat]'(by rw [hp1_n]; exact hp1_ws)) +
                  2).toNat]'hx = s.core.arena[cr.toNat + 2]'(by omega) := fun _ => by
              congr 1
            rw [heq]; exact ⟨hsz_gt0, hsz_le5, hsz_cr⟩
          all_goals
            exact hJ43 0#32 mp' ⟨rfl, fun h => by simp at h⟩)
    · exact hJ42 0#32 mp' ⟨rfl, fun h => by simp at h⟩
  · c0_hfast
    exact hJ41 (p + 1#64, 0#32, 0#32) mp'
      ⟨rfl, by rw [hp1_n]; omega,
       by rw [hp1_n]; omega,
       by exfalso
          rw [hend64] at hc
          rw [Nat.mod_eq_of_lt (by omega)] at hc; exact hc (by omega),
       fun h => by simp at h⟩

private theorem sbva_l11_cont_wp {Γ : Env} {Q : Post [i32]} {X : XPost}
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {mp : Mem 64}
    {ncntd best_c ci vis_n seed_cap cap : BitVec 32}
    {mc rp : List (BitVec 32)} {sig : List (BitVec 64)}
    {Jp : Cont [i32, i32]} {J12 : Cont []}
    (hcv_le : s.core.cur_vars ≤ c.max_vars)
    (hws_len : s.scratch.wsort.length = 2 * c.max_vars)
    (hws1_len : s.scratch.work_stk1.length = 2 * c.max_vars)
    (hnc_le : ncntd.toNat ≤ 2 * s.core.cur_vars) (h2cv_lt32 : 2 * s.core.cur_vars < 2 ^ 32)
    (hcntd_ok : ∀ i < ncntd.toNat, (s.scratch.work_stk1[i]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hcap_le_cv : cap.toNat ≤ s.core.cur_vars) (hcap_le_32 : cap.toNat ≤ 32)
    (hsc_le : seed_cap.toNat ≤ cap.toNat)
    (_hci_le : ci.toNat ≤ ncntd.toNat)
    (hmc_l : mc.length = c.max_vars) (hrp_l : rp.length = 2 * c.max_vars)
    (hsig_l : sig.length = c.max_vars)
    (hvn1 : 1 ≤ vis_n.toNat) (hvn_c : vis_n.toNat ≤ cap.toNat)
    (hmc_ok : ∀ k < vis_n.toNat, (mc[k]?.getD 0#32).toNat < s.core.cur_vars)
    (hmp : (SbvaMem c s mc rp sig ⋆ R) mp)
    (ihp : ∀ (ys : Tup Val [i32, i32]) (m' : Mem 64),
      ncntd.toNat - ys.1.toNat < ncntd.toNat - ci.toNat →
      (∃ mc' rp' sig', ys.1.toNat ≤ ncntd.toNat ∧ sbvaBfsInv c s R cap mc' rp' sig' ys.2.1 m') →
      Jp ys m')
    (hJ12 : ∀ (m' : Mem 64),
      (∃ mc12 rp12 sig12, sbvaBfsInv c s R cap mc12 rp12 sig12 vis_n m') → J12 () m') :
    wp Γ Q X (sbvaL11ContExpr c.pWorkStk1 c.pWsort c.pMinClr c.pRepr c.pSimSig
      ncntd best_c ci vis_n seed_cap Jp J12) mp := by
  dsimp only [sbvaL11ContExpr, sbvaOp1, sbvaOp2]
  c0_hsplit
  · c0_hsplit
    · have hci_lt : ci.toNat < ncntd.toNat := by assumption
      have hvn_lt_sc : vis_n.toNat < seed_cap.toNat := by assumption
      have hvn_lt_cap : vis_n.toNat < cap.toNat := by omega
      have hci64 : (BitVec.setWidth 64 ci).toNat = ci.toNat := bv64_setWidth_32 ci
      have hclit_lt :
          (s.scratch.work_stk1[ci.toNat]'(by omega)).toNat <
            2 * s.core.cur_vars := by
        have := hcntd_ok ci.toNat hci_lt
        rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
      have hclit_lt64 :
          (s.scratch.work_stk1[(BitVec.setWidth 64 ci).toNat]'(by
            rw [hci64]; omega)).toNat < 2 * s.core.cur_vars := by
        simpa only [hci64] using hclit_lt
      have hci1 : (ci + 1#32).toNat = ci.toNat + 1 :=
        sbva_bv32_add1 hci_lt (Nat.lt_of_le_of_lt hnc_le h2cv_lt32)
      c0_hfast_nogrp
      -- Join `L44` (`if (cnt[clit] == best_c)`) carrying `vis_n'` -> `ihp`
      refine wp_join_state1 (t := i32)
        (α := BitVec 32 × List (BitVec 32) × List (BitVec 32) × List (BitVec 64))
        (·.1)
        (fun ⟨vn44, mc44, rp44, sig44⟩ m44 =>
          sbvaBfsInv c s R cap mc44 rp44 sig44 vn44 m44)
        (fun _ ⟨vn44, mc44, rp44, sig44⟩ m44 hbfs44 => by
          c0_hfast
          exact ihp (ci + 1#32, vn44, ()) m44 (by dsimp only; rw [hci1]; omega)
            ⟨mc44, rp44, sig44, by rw [hci1]; omega, hbfs44⟩)
        (fun J44 hJ44 => ?_)
      c0_hfast_nogrp
      · -- `L45`: `while (k < vis_n && vis[k] != cvar)`
        refine wp_loop_inv
          (fun (k, ()) mk => mk = mp ∧ k.toNat ≤ vis_n.toNat)
          (fun (k, ()) _ => vis_n.toNat - k.toNat)
          (fun Jk hJk => hJk (0#32, ()) mp ⟨rfl, Nat.zero_le _⟩)
          (fun Jk (k, ()) mk ⟨hmk, hk_le⟩ ihk => ?_)
        subst mk
        have hk64 : (BitVec.setWidth 64 k).toNat = k.toNat := bv64_setWidth_32 k
        c0_hfast_nogrp
        -- Exit join `L46` (`sig = [[]]`) -> `L47` (`if (k == vis_n)`) -> `hJ44`
        refine wp_join0 (fun m46 => m46 = mp)
          (fun J46 m46 hm46 => by
            subst m46
            have hvn1_lt : (vis_n + 1#32).toNat = vis_n.toNat + 1 :=
              sbva_bv32_add1 hvn_lt_cap (Nat.lt_of_le_of_lt hcap_le_32 (by decide))
            have hvn64 : (BitVec.setWidth 64 vis_n).toNat = vis_n.toNat :=
              bv64_setWidth_32 vis_n
            have h2vn0 :
                (BitVec.setWidth 64 vis_n <<< (1 : Nat)).toNat = 2 * vis_n.toNat :=
              sbva_bw64_shl1 _
            have h2vn1 :
                ((BitVec.setWidth 64 vis_n <<< (1 : Nat)) + 1#64).toNat =
                  2 * vis_n.toNat + 1 := sbva_bw64_shl1_add1 _
            have hcvar_lt :
                ((s.scratch.work_stk1[(BitVec.setWidth 64 ci).toNat]'(by
                  rw [hci64]; omega)) >>> 1).toNat < s.core.cur_vars := by
              rw [bv32_lshr1_nat]
              exact Nat.div_lt_of_lt_mul hclit_lt64
            have hvn_mc : (BitVec.setWidth 64 vis_n).toNat < mc.length := by
              rw [hvn64, hmc_l]
              exact Nat.lt_of_lt_of_le hvn_lt_cap (Nat.le_trans hcap_le_cv hcv_le)
            have hvn_rp0 :
                (BitVec.setWidth 64 vis_n <<< (1 : Nat)).toNat < rp.length := by
              rw [h2vn0, hrp_l]
              exact nat_two_lt (Nat.lt_of_lt_of_le hvn_lt_cap
                (Nat.le_trans hcap_le_cv hcv_le))
            have hvn_rp1 :
                ((BitVec.setWidth 64 vis_n <<< (1 : Nat)) + 1#64).toNat <
                  (rp.set (BitVec.setWidth 64 vis_n <<< (1 : Nat)).toNat
                    0#32).length := by
              rw [h2vn1, List.length_set, hrp_l]
              exact nat_two_add1_lt (Nat.lt_of_lt_of_le hvn_lt_cap
                (Nat.le_trans hcap_le_cv hcv_le))
            have hvn_sig : (BitVec.setWidth 64 vis_n).toNat < sig.length := by
              rw [hvn64, hsig_l]
              exact Nat.lt_of_lt_of_le hvn_lt_cap (Nat.le_trans hcap_le_cv hcv_le)
            c0_hfast
            · exact hJ44 ⟨vis_n + 1#32, _, _, _⟩ _
                ⟨by rw [List.length_set, hmc_l],
                 by rw [List.length_set, List.length_set, hrp_l],
                 by rw [List.length_set, hsig_l],
                 by rw [hvn1_lt]; omega, by rw [hvn1_lt]; omega,
                 fun idx hidx => by
                   by_cases he : idx = vis_n.toNat
                   · subst he
                     simp only [hvn64]
                     rw [List.getElem?_set_self (by omega), Option.getD_some]
                     exact hcvar_lt
                   · simp only [hvn64]
                     rw [List.getElem?_set_ne (Ne.symm he)]
                     exact hmc_ok idx (by rw [hvn1_lt] at hidx; omega),
                 hm⟩
            · exact hJ44 ⟨vis_n, mc, rp, sig⟩ mp
                ⟨hmc_l, hrp_l, hsig_l, hvn1, hvn_c, hmc_ok, hmp⟩)
          (fun J46 hJ46 => by
            c0_hsplit
            · have hk_lt : k.toNat < vis_n.toNat := by assumption
              have hk_mc : (BitVec.setWidth 64 k).toNat < mc.length := by
                rw [hk64, hmc_l]
                exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hk_lt hvn_c)
                  (Nat.le_trans hcap_le_cv hcv_le)
              have hk1 : (k + 1#32).toNat = k.toNat + 1 :=
                sbva_bv32_add1 hk_lt
                  (Nat.lt_of_le_of_lt hvn_c
                    (Nat.lt_of_le_of_lt hcap_le_32 (by decide)))
              c0_hfast
              · exact ihk (k + 1#32, ()) mp
                  (by dsimp only; rw [hk1]
                      exact Nat.sub_lt_sub_left hk_lt (Nat.lt_succ_self _))
                  ⟨rfl, by rw [hk1]; exact hk_lt⟩
              · exact hJ46 mp rfl
            · exact hJ46 mp rfl)
      · exact hJ44 ⟨vis_n, mc, rp, sig⟩ mp
          ⟨hmc_l, hrp_l, hsig_l, hvn1, hvn_c, hmc_ok, hmp⟩
    · c0_hfast
      exact hJ12 mp ⟨mc, rp, sig, hmc_l, hrp_l, hsig_l, hvn1, hvn_c, hmc_ok, hmp⟩
  · c0_hfast
    exact hJ12 mp ⟨mc, rp, sig, hmc_l, hrp_l, hsig_l, hvn1, hvn_c, hmc_ok, hmp⟩
/-- Callee-free parametric `Func.wp` proof of `full_bva_pick_sbva3_m8_body` against canonical
`FullBvaHeap.fullBvaPickCandSpec`. -/
theorem full_bva_pick_sbva3_m8_wp (Γ : Env) :
    ∀ args m Q X, fullBvaPickCandSpec args m Q X →
      Func.wp Γ full_bva_pick_sbva3_m8_body args m Q X := by
  rintro ⟨h, ncntd, f0, ⟨⟩⟩ m Q X
    ⟨c, F0, F_cur, s, R, rfl, hinv, hf0_lt, hnc_le, hcntd_ok, hm, hQ⟩
  have hQ_wrap : ∀ (r : BitVec 32) (rp mc : List (BitVec 32)) (tc tl : Nat)
      (ws : List (BitVec 32)) (ant : BitVec 64) (sig : List (BitVec 64))
      (sh : List (BitVec 32)) (m' : Mem 64),
      sbvaFinQ c F0 F_cur s R Q r rp mc tc tl ws ant sig sh m' :=
        fun r rp mc tc tl ws ant sig sh m' =>
    fun h1 h2 h3 => hQ r rp mc s.core.tmp_cnt s.core.tmp_len ws s.scratch.ant_sz sig
      s.scratch.shrink_stk m' h1 h2 h3
  clear hQ
  have hmx := c.hmaxv; have hwcap := c.hwcap; have har_b := c.harena
  unfold dimacsBound at hmx hwcap har_b
  have hcl := hinv.1.core_ok; have hsc := hinv.1.scratch_ok; have hw := hinv.2.1
  have hcv_le := hcl.cur_vars_le; have hwv_len := hcl.wvec_len
  have hws_len := hsc.wsort_len; have hws1_len := hsc.work_stk1_len
  have hmclr_len := hcl.min_clr_len_arr; have hrepr_len := hcl.repr_len
  have hsig_len := hsc.sim_sig_len; have hwstk_len := hcl.wstk_len_arr
  have hwlen_le := hcl.wlen_le; have har_arr := hcl.arena_len_arr
  have hal_le := hcl.arena_len_le
  have hcv_pos : 1 ≤ s.core.cur_vars := by omega
  have h2cv_lt32 : 2 * s.core.cur_vars < 2 ^ 32 := by omega
  c0_hfast_nogrp
  -- Loop 1 (`L0`): single-pass scan computing `best_c`, `best_deg`, `best_lit`, `ties`, `ci`
  refine wp_loop_inv
    (fun (best_c, best_deg, best_lit, ties, ci, ()) ml =>
      ml = m ∧ ci.toNat ≤ ncntd.toNat ∧
      (2 ≤ best_c.toNat → best_lit.toNat < 2 * s.core.cur_vars))
    (fun (_, _, _, _, ci, _) _ => ncntd.toNat - ci.toNat)
    (fun J1 hJ1 => by
      c0_hfast
      exact hJ1 (0#32, 0#32, 0xFFFFFFFF#32, 0#32, 0#32, ()) m
        ⟨rfl, Nat.zero_le _, fun h => by simp only [bv_c0] at h; omega⟩)
    (fun J1 (best_c, best_deg, best_lit, ties, ci, ()) ml ⟨hml, hci_le, hbl_ok⟩ ih1 => ?_)
  subst ml
  c0_hfast_nogrp
  · have hci_lt : ci.toNat < ncntd.toNat := by c0_bound
    have hci64 : (BitVec.setWidth 64 ci).toNat = ci.toNat := by c0_bound
    have hclit_lt :
        (s.scratch.work_stk1[ci.toNat]'(by omega)).toNat < 2 * s.core.cur_vars := by
      have := hcntd_ok ci.toNat hci_lt
      rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
    have hci1 : (ci + 1#32).toNat = ci.toNat + 1 := by c0_bound
    have h2clit :
        ((BitVec.setWidth 64 (s.scratch.work_stk1[ci.toNat]'(by omega)) <<< (1 : Nat)) + 1).toNat =
          2 * (s.scratch.work_stk1[ci.toNat]'(by omega)).toNat + 1 := by
      change ((BitVec.setWidth 64 _ <<< (1 : Nat)) + 1#64).toNat = _; c0_bound
    have hclit_wvec :
        ((BitVec.setWidth 64
          (s.scratch.work_stk1[(BitVec.setWidth 64 ci).toNat]'(by rw [hci64]; omega)) <<<
            (1 : Nat)) + 1).toNat < s.core.wvec.length := by
      simp only [hci64, h2clit, hwv_len]; omega
    c0_hfast
    all_goals first
      | exact ih1 (_, _, _, _, ci + 1#32, ()) m (by dsimp only; rw [hci1]; omega)
          ⟨rfl, by rw [hci1]; omega, fun _ => by simpa only [hci64] using hclit_lt⟩
      | exact ih1 (_, _, best_lit, _, ci + 1#32, ()) m (by dsimp only; rw [hci1]; omega)
          ⟨rfl, by rw [hci1]; omega, hbl_ok⟩
  · -- Join `L5` over `if (best_c >= 2u && ties > 1u)` carrying `(best_deg, best_lit, ci)`
    refine wp_join_state
      (α := BitVec 32 × BitVec 32 × BitVec 32 × List (BitVec 32) × List (BitVec 32) ×
        List (BitVec 64))
      (fun st => (st.1, st.2.1, st.2.2.1, ()))
      (fun ⟨bdF, blF, ciF, mcF, rpF, sigF⟩ mf =>
        sbvaTbJoin c s R best_c bdF blF ciF mcF rpF sigF mf)
      (fun _ ⟨bdF, blF, ciF, mcF, rpF, sigF⟩ mf ⟨hblF, hmcF, hrpF, hsigF, hmf⟩ => ?_)
      (fun Jtb hJtb => ?_)
    · -- Loop 2 (`L6`): zero `cnt[cntd[0..ncntd)] = 0u`, then `L7` return
      c0_hfast_nogrp
      refine wp_loop_inv
        (fun (ci2, ()) m2 => ∃ ws2,
          ci2.toNat ≤ ncntd.toNat ∧ ws2.length = 2 * c.max_vars ∧
          (SbvaFinMem c s mcF rpF ws2 sigF ⋆ R) m2)
        (fun (ci2, ()) _ => ncntd.toNat - ci2.toNat)
        (fun J2 hJ2 => by
          c0_hfast
          exact hJ2 (0#32, ()) mf ⟨s.scratch.wsort, Nat.zero_le _, hws_len, hmf⟩)
        (fun J2 (ci2, ()) m2 ⟨ws2, hci2_le, hws2_len, hm2⟩ ih2 => ?_)
      c0_hfast_nogrp
      · have hci2_lt : ci2.toNat < ncntd.toNat := by c0_bound
        have hci2_64 : (BitVec.setWidth 64 ci2).toNat = ci2.toNat := by c0_bound
        have hclit_lt :
            (s.scratch.work_stk1[ci2.toNat]'(by omega)).toNat < 2 * s.core.cur_vars := by
          have := hcntd_ok ci2.toNat hci2_lt
          rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
        have hclit_lt64 :
            (s.scratch.work_stk1[(BitVec.setWidth 64 ci2).toNat]'(by
              rw [hci2_64]; omega)).toNat < 2 * s.core.cur_vars := by
          simpa only [hci2_64] using hclit_lt
        have hci2_1 : (ci2 + 1#32).toNat = ci2.toNat + 1 := by c0_bound
        c0_hfast
        exact ih2 (ci2 + 1#32, ()) m (by dsimp only; rw [hci2_1]; omega)
          ⟨_, by rw [hci2_1]; omega, by simp [hws2_len], hm⟩
      · have hinv_fin : FullDenseInvNoLm c F0 F_cur (sbvaFinSt s mcF rpF ws2 sigF) :=
          fullDenseInvNoLm_with_core_aux hinv hrpF hmcF hcl.tmp_len_arr hcl.flags_len
            hcl.tmp_len_le { hsc with wsort_len := hws2_len, sim_sig_len := hsigF } rfl rfl
        c0_hfast
        · exact hQ_wrap 0xFFFFFFFF#32 rpF mcF s.core.tmp_cnt s.core.tmp_len ws2 s.scratch.ant_sz
            sigF s.scratch.shrink_stk m2 hinv_fin (Or.inl rfl) hm2
        · exact hQ_wrap blF rpF mcF s.core.tmp_cnt s.core.tmp_len ws2 s.scratch.ant_sz
            sigF s.scratch.shrink_stk m2 hinv_fin (Or.inr (hblF (by c0_bound))) hm2
    · -- Tie-break branch `if (best_c >= 2u && ties > 1u)`
      c0_hfast_nogrp
      · have hbc_ge2 : 2 ≤ best_c.toNat := by c0_bound
        -- Join `L8` for `cap = (cv < 32ULL) ? (u32)cv : 32u`
        refine wp_join_state1 (t := i32) (α := BitVec 32) id
          (fun cap m8 => m8 = m ∧ 1 ≤ cap.toNat ∧ cap.toNat ≤ s.core.cur_vars ∧
            cap.toNat ≤ 32)
          (fun _ cap m8 ⟨hm8, hcap_pos, hcap_le_cv, hcap_le_32⟩ => ?_)
          (fun Jcap hJcap => by
            c0_hfast
            · have hsw :
                  ((if h : 64 ≤ 32 then BitVec.setWidth' h (BitVec.ofNat 64 s.core.cur_vars)
                    else BitVec.ofNat 32 (BitVec.ofNat 64 s.core.cur_vars).toNat) :
                      BitVec 32).toNat = s.core.cur_vars := by
                rw [dite_eq_right (fun h => absurd h (by decide)), BitVec.toNat_ofNat,
                  BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
              have hc' : s.core.cur_vars < 32 := by
                have hc0 : s.core.cur_vars % 2 ^ 64 < BitVec.toNat (32 : BitVec 64) := by assumption
                rw [Nat.mod_eq_of_lt (by omega)] at hc0; exact hc0
              exact hJcap _ m
                ⟨rfl, by rw [hsw]; exact hcv_pos, by rw [hsw]; exact Nat.le_refl _,
                  by rw [hsw]; omega⟩
            · exact hJcap 32#32 m ⟨rfl, by decide, by c0_bound, by decide⟩)
        · subst m8
          c0_hfast_nogrp
          -- Join `L9` (`if (cap > 0u)`) wrapping `Jtb`
          refine wp_join_state
            (α := BitVec 32 × BitVec 32 × BitVec 32 × List (BitVec 32) × List (BitVec 32) ×
              List (BitVec 64))
            (fun st => (st.1, st.2.1, st.2.2.1, ()))
            (fun ⟨bdF, blF, ciF, mcF, rpF, sigF⟩ mf =>
              sbvaTbJoin c s R best_c bdF blF ciF mcF rpF sigF mf)
            (fun _ st m9 hst => by
              c0_hfast
              exact hJtb st m9 hst)
            (fun J9 hJ9 => ?_)
          c0_hfast_nogrp
          · have hf0v_lt : (f0 >>> 1).toNat < s.core.cur_vars := by rw [bv32_lshr1_nat]; omega
            have h0_mc : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0)).toNat <
                s.core.min_clr.length := by
              rw [show (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0)).toNat = 0 from rfl]; omega
            have h0_rp : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0)).toNat <
                s.core.repr.length := by
              rw [show (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0)).toNat = 0 from rfl]; omega
            have h1_rp : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 1)).toNat <
                s.core.repr.length := by
              rw [show (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 1)).toNat = 1 from rfl]; omega
            have h0_sg : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0)).toNat <
                s.scratch.sim_sig.length := by
              rw [show (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0)).toNat = 0 from rfl]; omega
            c0_hfast_nogrp
            rw [show (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0)).toNat = 0 from rfl,
                show (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 1)).toNat = 1 from rfl,
                sbva_upd4_eq] at hm
            change (SbvaMem c s (s.core.min_clr.set 0 (f0 >>> 1))
              ((s.core.repr.set 0 1#32).set 1 0#32) (s.scratch.sim_sig.set 0 1#64) ⋆ R) m at hm
            -- Join `L10` for `seed_cap = (cap < 16u) ? cap : 16u`
            refine wp_join_state1 (t := i32) (α := BitVec 32) id
              (fun seed_cap m10 => 1 ≤ seed_cap.toNat ∧ seed_cap.toNat ≤ cap.toNat ∧
                sbvaBfsInv c s R cap (s.core.min_clr.set 0 (f0 >>> 1))
                  ((s.core.repr.set 0 1#32).set 1 0#32) (s.scratch.sim_sig.set 0 1#64) 1#32 m10)
              (fun _ seed_cap m10 ⟨hsc_pos, hsc_le, hinit_bfs⟩ => ?_)
              (fun Jsc hJsc => by
                have hinit : sbvaBfsInv c s R cap (s.core.min_clr.set 0 (f0 >>> 1))
                    ((s.core.repr.set 0 1#32).set 1 0#32)
                    (s.scratch.sim_sig.set 0 1#64) 1#32 m := by
                  refine ⟨by simp [hmclr_len], by simp [hrepr_len], by simp [hsig_len], by decide,
                    hcap_pos, fun k hk => ?_, hm⟩
                  have hk0 : k = 0 := by simp only [bv_c0] at hk; omega
                  subst hk0
                  rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hf0v_lt
                c0_hfast
                · exact hJsc cap m ⟨hcap_pos, Nat.le_refl _, hinit⟩
                · have hc' : ¬ (id cap).toNat < BitVec.toNat (16 : BitVec 32) := by assumption
                  have hc16 : 16 ≤ cap.toNat := by
                    change ¬ cap.toNat < 16 at hc'
                    omega
                  exact hJsc 16#32 m ⟨by decide, hc16, hinit⟩)
            · clear hm
              c0_hfast_nogrp
              -- Pre-seed loop `L11`: `while (ci < ncntd && vis_n < seed_cap)` -> `(ci, vis_n, ())`
              refine wp_loop_inv
                (fun (ci, vis_n, ()) mp => ∃ mc rp sig,
                  ci.toNat ≤ ncntd.toNat ∧ sbvaBfsInv c s R cap mc rp sig vis_n mp)
                (fun (ci, _, _) _ => ncntd.toNat - ci.toNat)
                (fun Jp hJp => hJp (0#32, 1#32, ()) m10
                  ⟨_, _, _, Nat.zero_le _, hinit_bfs⟩)
                (fun Jp (ci, vis_n, ()) mp ⟨mc, rp, sig, hci_le, hmc_l, hrp_l, hsig_l, hvn1,
                    hvn_c, hmc_ok, hmp⟩ ihp => ?_)
              c0_hfast_nogrp
              -- Exit join `L12` (`sig = [[]]`) of `L11` -> 3-hop BFS `L13..L21`
              refine wp_join0
                (fun m12 => ∃ mc12 rp12 sig12, sbvaBfsInv c s R cap mc12 rp12 sig12 vis_n m12)
                (fun J12 m12 ⟨mc12, rp12, sig12, hmc12, hrp12, hsig12, hvn12_1, hvn12_c,
                    hmc12_ok, hm12⟩ => ?_)
                (fun J12 hJ12 => ?_)
              · -- `BLOCK L12`: 3-hop forward BFS `L13`: `(vis_n_h, steps_h, hop, ())`
                clear hinit_bfs hmc_l hrp_l hsig_l hvn1 hvn_c hmc_ok hmp mc rp sig ihp hQ_wrap
                  ih1 hJtb
                c0_hfast_nogrp
                refine wp_loop_inv
                  (fun (vis_n_h, steps_h, hop, ()) mh => ∃ mc rp sig,
                    hop.toNat ≤ 3 ∧ sbvaBfsInv c s R cap mc rp sig vis_n_h mh)
                  (fun (_, _, hop, _) _ => 3 - hop.toNat)
                  (fun Jh hJh => hJh (vis_n, 0#32, 0#32, ()) m12
                    ⟨mc12, rp12, sig12, Nat.zero_le _, hmc12, hrp12, hsig12, hvn12_1, hvn12_c,
                     hmc12_ok, hm12⟩)
                  (fun Jh (vis_n_h, steps_h, hop, ()) mh ⟨mc_h, rp_h, sig_h, hhop_le, hmc_hl,
                      hrp_hl, hsig_hl, hvn_h1, hvn_hc, hmc_hok, hmh⟩ ihh => ?_)
                clear hmc12 hrp12 hsig12 hvn12_1 hvn12_c hmc12_ok hm12 mc12 rp12 sig12
                c0_hfast_nogrp
                -- Exit join `L14` (`sig = [[]]`) of `L13` -> Loop 3 `L15..L21`
                refine wp_join0
                  (fun m14 => ∃ mc14 rp14 sig14,
                    vis_n_h.toNat ≤ cap.toNat ∧ mc14.length = c.max_vars ∧
                    rp14.length = 2 * c.max_vars ∧ sig14.length = c.max_vars ∧
                    (SbvaMem c s mc14 rp14 sig14 ⋆ R) m14)
                  (fun J14 m14 ⟨mc14, rp14, sig14, hvn14_c, hmc14, hrp14, hsig14, hm14⟩ => ?_)
                  (fun J14 hJ14 => ?_)
                · -- `BLOCK L14`: Loop 3 (`L15`) scoring up to 64 tied candidates
                  exact sbva_l14_wp hcv_le hwv_len hws_len hws1_len hnc_le h2cv_lt32 hcntd_ok
                    hbc_ge2 hbl_ok hcap_le_cv hcap_le_32 hvn14_c hmc14 hrp14 hsig14 hm14 hJ9
                · -- `CONT L14`: `if (hop < 3 && steps_h < 128)` -> `qi` loop `L22..L43`
                  c0_hfast_nogrp
                  · have hhop_lt : hop.toNat < 3 := sbva_lt_bv32 (by decide) (by assumption)
                    have hsteps_h_lt : steps_h.toNat < 128 :=
                      sbva_lt_bv32 (by decide) (by assumption)
                    have hhop1 : (hop + 1#32).toNat = hop.toNat + 1 :=
                      sbva_bv32_add1 hhop_lt (by decide)
                    clear hf0_lt hnc_le hcntd_ok hbl_ok hbc_ge2 hJ9 hf0v_lt h0_mc h0_rp h1_rp h0_sg
                      hsc_pos hsc_le
                    let layer_n := vis_n_h
                    -- `L22`: `qi` loop `(vis_n_q, steps_q, qi, ())`
                    refine wp_loop_inv
                      (fun (vis_n_q, steps_q, qi, ()) mq => ∃ mc_q rp_q sig_q,
                        qi.toNat ≤ layer_n.toNat ∧ layer_n.toNat ≤ vis_n_q.toNat ∧
                        sbvaBfsInv c s R cap mc_q rp_q sig_q vis_n_q mq)
                      (fun (_, _, qi, _) _ => layer_n.toNat - qi.toNat)
                      (fun Jqi hJqi => hJqi (vis_n_h, steps_h, 0#32, ()) mh
                        ⟨mc_h, rp_h, sig_h, Nat.zero_le _, Nat.le_refl _, hmc_hl, hrp_hl, hsig_hl,
                         hvn_h1, hvn_hc, hmc_hok, hmh⟩)
                      (fun Jqi (vis_n_q, steps_q, qi, ()) mq ⟨mc_q, rp_q, sig_q, hqi_le, hlay_le,
                          hmc_ql, hrp_ql, hsig_ql, hvn_q1, hvn_qc, hmc_qok, hmq⟩ ihqi => ?_)
                    c0_hfast_nogrp
                    -- Exit join `L23` (`sig = [[]]`) of `L22` -> optional `hop < 2` shift -> `ihh`
                    refine wp_join0
                      (fun m23 => ∃ mc23 rp23 sig23,
                        sbvaBfsInv c s R cap mc23 rp23 sig23 vis_n_q m23)
                      (fun J23 m23 ⟨mc23, rp23, sig23, hmc23, hrp23, hsig23, hvn23_1, hvn23_c,
                          hmc23_ok, hm23⟩ => ?_)
                      (fun J23 hJ23 => ?_)
                    · -- `BLOCK L23`: Join `L24` (`sig = [[]]`) over `if (hop < 2u)` -> `ihh`
                      refine wp_join0
                        (fun m24 => ∃ rp_sh,
                          rp_sh.length = 2 * c.max_vars ∧
                          (SbvaMem c s mc23 rp_sh sig23 ⋆ R) m24)
                        (fun J24 m24 ⟨rp_sh, hrp_shl, hm24⟩ => by
                          c0_hfast
                          exact ihh (vis_n_q, steps_q, hop + 1#32, ()) m24
                            (by dsimp only; rw [hhop1]; omega)
                            ⟨mc23, rp_sh, sig23, by rw [hhop1]; omega, hmc23, hrp_shl, hsig23,
                             hvn23_1, hvn23_c, hmc23_ok, hm24⟩)
                        (fun J24 hJ24 => by
                          c0_hfast_nogrp
                          · refine wp_loop_inv
                              (fun (k, ()) msh => ∃ rp_sh,
                                k.toNat ≤ vis_n_q.toNat ∧ rp_sh.length = 2 * c.max_vars ∧
                                (SbvaMem c s mc23 rp_sh sig23 ⋆ R) msh)
                              (fun (k, ()) _ => vis_n_q.toNat - k.toNat)
                              (fun Jk hJk => hJk (0#32, ()) m23 ⟨rp23, Nat.zero_le _, hrp23, hm23⟩)
                              (fun Jk (k, ()) msh ⟨rp_sh, hk_le, hrp_shl, hmsh⟩ ihk => ?_)
                            c0_hfast_nogrp
                            · have hk_lt : k.toNat < vis_n_q.toNat := by assumption
                              have hk1 : (k + 1#32).toNat = k.toNat + 1 :=
                                sbva_bv32_add1 hk_lt
                                  (Nat.lt_of_le_of_lt hvn23_c
                                    (Nat.lt_of_le_of_lt hcap_le_32 (by decide)))
                              have h2k0 : (BitVec.setWidth 64 k <<< (1 : Nat)).toNat =
                                  2 * k.toNat := sbva_bw64_shl1 _
                              have h2k1 : ((BitVec.setWidth 64 k <<< (1 : Nat)) + 1#64).toNat =
                                  2 * k.toNat + 1 := sbva_bw64_shl1_add1 _
                              have h2k0_lt : (BitVec.setWidth 64 k <<< (1 : Nat)).toNat <
                                  rp_sh.length := by
                                rw [h2k0, hrp_shl]
                                exact nat_two_lt (Nat.lt_of_lt_of_le
                                  (Nat.lt_of_lt_of_le hk_lt hvn23_c)
                                  (Nat.le_trans hcap_le_cv hcv_le))
                              have h2k1_lt : ((BitVec.setWidth 64 k <<< (1 : Nat)) + 1#64).toNat <
                                  rp_sh.length := by
                                rw [h2k1, hrp_shl]
                                exact nat_two_add1_lt (Nat.lt_of_lt_of_le
                                  (Nat.lt_of_lt_of_le hk_lt hvn23_c)
                                  (Nat.le_trans hcap_le_cv hcv_le))
                              have h2k0_lt_set : (BitVec.setWidth 64 k <<< (1 : Nat)).toNat <
                                  (rp_sh.set ((BitVec.setWidth 64 k <<< (1 : Nat)) + 1#64).toNat
                                    0#32).length := by
                                rw [List.length_set]; exact h2k0_lt
                              have h2k1_lt_set :
                                  ((BitVec.setWidth 64 k <<< (1 : Nat)) + 1#64).toNat <
                                    (rp_sh.set (BitVec.setWidth 64 k <<< (1 : Nat)).toNat
                                      rp_sh[((BitVec.setWidth 64 k <<< (1 : Nat)) +
                                        1#64).toNat]).length := by
                                rw [List.length_set]; exact h2k1_lt
                              c0_hfast
                              exact ihk (k + 1#32, ()) m (by dsimp only; rw [hk1]; omega)
                                ⟨_, by rw [hk1]; omega,
                                 by rw [List.length_set, List.length_set, hrp_shl], hm⟩
                            · exact hJ24 msh ⟨rp_sh, hrp_shl, hmsh⟩
                          · exact hJ24 m23 ⟨rp23, hrp23, hm23⟩)
                    · -- `CONT L23`: `qi` loop body
                      c0_hsplit
                      · c0_hsplit
                        · have hqi_lt : qi.toNat < layer_n.toNat := by assumption
                          have hqi_vn : qi.toNat < vis_n_q.toNat :=
                            Nat.lt_of_lt_of_le hqi_lt hlay_le
                          have hqi1 : (qi + 1#32).toNat = qi.toNat + 1 :=
                            sbva_bv32_add1 hqi_lt
                              (Nat.lt_of_le_of_lt hvn_hc
                                (Nat.lt_of_le_of_lt hcap_le_32 (by decide)))
                          have hcw_b :
                              ((BitVec.setWidth 64 qi) <<< (1 : Nat)).toNat < rp_q.length := by
                            rw [sbva_bw64_shl1 _, hrp_ql]; omega
                          c0_hfast_nogrp
                          -- Join `L26` (`if (cw > 0u)`) carrying `(vis_n_s, steps_s)` -> `ihqi`
                          refine wp_join_state
                            (α := BitVec 32 × BitVec 32) (fun p => (p.1, p.2, ()))
                            (fun ⟨vn_26, st_26⟩ m26 => ∃ mc26 rp26 sig26,
                              layer_n.toNat ≤ vn_26.toNat ∧
                              sbvaBfsInv c s R cap mc26 rp26 sig26 vn_26 m26)
                            (fun _ ⟨vn_26, st_26⟩ m26 ⟨mc26, rp26, sig26, hlay26, hmc26, hrp26,
                                hsig26, hvn26_1, hvn26_c, hmc26_ok, hm26⟩ => by
                              c0_hfast
                              exact ihqi (vn_26, st_26, qi + 1#32, ()) m26
                                (by dsimp only; rw [hqi1]; omega)
                                ⟨mc26, rp26, sig26, by rw [hqi1]; omega, hlay26, hmc26, hrp26,
                                 hsig26, hvn26_1, hvn26_c, hmc26_ok, hm26⟩)
                            (fun J26 hJ26 => ?_)
                          c0_hfast_nogrp
                          · have hqi64 : (BitVec.setWidth 64 qi).toNat = qi.toNat :=
                              bv64_setWidth_32 qi
                            have hqi_mc : (BitVec.setWidth 64 qi).toNat < mc_q.length := by
                              rw [hqi64]; omega
                            let sidx := mc_q[(BitVec.setWidth 64 qi).toNat]'hqi_mc
                            have hsidx_lt : sidx.toNat < s.core.cur_vars := by
                              have h1 := hmc_qok qi.toNat hqi_vn
                              rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h1
                              simpa only [sidx, hqi64] using h1
                            -- `L27`: `sgn` loop `(vis_n_s, steps_s, sgn, ())`
                            refine wp_loop_inv
                              (fun (vis_n_s, steps_s, sgn, ()) ms => ∃ mc_s rp_s sig_s,
                                sgn.toNat ≤ 2 ∧ layer_n.toNat ≤ vis_n_s.toNat ∧
                                sbvaBfsInv c s R cap mc_s rp_s sig_s vis_n_s ms)
                              (fun (_, _, sgn, _) _ => 2 - sgn.toNat)
                              (fun Js hJs => hJs (vis_n_q, steps_q, 0#32, ()) mq
                                ⟨mc_q, rp_q, sig_q, Nat.zero_le _, hlay_le, hmc_ql, hrp_ql,
                                 hsig_ql, hvn_q1, hvn_qc, hmc_qok, hmq⟩)
                              (fun Js (vis_n_s, steps_s, sgn, ()) ms ⟨mc_s, rp_s, sig_s, hsgn_le,
                                  hlay_s, hmc_sl, hrp_sl, hsig_sl, hvn_s1, hvn_sc, hmc_sok,
                                  hms⟩ ihs => ?_)
                            c0_hsplit
                            · c0_hsplit
                              · have hsgn_lt : sgn.toNat < 2 :=
                                  sbva_lt_bv32 (by decide) (by assumption)
                                have hsgn1 : (sgn + 1#32).toNat = sgn.toNat + 1 :=
                                  sbva_bv32_add1 hsgn_lt (by decide)
                                let sl := (sidx <<< (1 : Nat)) ||| sgn
                                have hsl_nat : sl.toNat = 2 * sidx.toNat + sgn.toNat :=
                                  sbva_bv32_shl1_or_lt2 hsgn_lt (Nat.lt_trans hsidx_lt (by omega))
                                have hsl_lt : sl.toNat < 2 * s.core.cur_vars := by
                                  rw [hsl_nat]; omega
                                obtain ⟨hbd_sl, hslice_sl⟩ := sbva_hop_wvec_bounds hinv hsl_lt
                                let off0 := fullWatchOffCore s.core sl.toNat
                                let sz0 := fullWatchSizeCore s.core sl.toNat
                                have hbd_sl' : off0 + sz0 ≤ s.core.wlen := hbd_sl
                                have h2sl0 : (BitVec.setWidth 64 sl <<< (1 : Nat)).toNat =
                                    2 * sl.toNat := sbva_bw64_shl1 _
                                have h2sl1 : ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1#64).toNat =
                                    2 * sl.toNat + 1 := sbva_bw64_shl1_add1 _
                                have h2sl0_lt : (BitVec.setWidth 64 sl <<< (1 : Nat)).toNat <
                                    s.core.wvec.length := by rw [h2sl0, hwv_len]; omega
                                have h2sl1_lt :
                                    ((BitVec.setWidth 64 sl <<< (1 : Nat)) + 1#64).toNat <
                                    s.core.wvec.length := by rw [h2sl1, hwv_len]; omega
                                have hwv0_b : 2 * sl.toNat < s.core.wvec.length := by
                                  rw [hwv_len]; omega
                                have hwv1_b : 2 * sl.toNat + 1 < s.core.wvec.length := by
                                  rw [hwv_len]; omega
                                have hwv0_eq : (s.core.wvec[2 * sl.toNat]'hwv0_b).toNat = off0 := by
                                  unfold off0 fullWatchOffCore
                                  rw [List.getElem?_eq_getElem hwv0_b, Option.getD_some]
                                have hwv1_eq : (s.core.wvec[2 * sl.toNat + 1]'hwv1_b).toNat =
                                    sz0 := by
                                  unfold sz0 fullWatchSizeCore
                                  rw [List.getElem?_eq_getElem hwv1_b, Option.getD_some]
                                have hoff_c0 :
                                    (BitVec.setWidth 64
                                      (s.core.wvec[(BitVec.setWidth 64 sl <<<
                                        (1 : Nat)).toNat]'h2sl0_lt)).toNat = off0 := by
                                  rw [bv64_setWidth_32]
                                  simp only [h2sl0]
                                  exact hwv0_eq
                                have hmod_end : (off0 + sz0) % 2 ^ 64 = off0 + sz0 :=
                                  Nat.mod_eq_of_lt (by omega)
                                have hwv0_mod : ∀ (h : 2 * sl.toNat % 2 ^ 64 < s.core.wvec.length),
                                    (s.core.wvec[2 * sl.toNat % 2 ^ 64]'h).toNat = off0 :=
                                  fun _ => by
                                    simp only [Nat.mod_eq_of_lt (by omega : 2 * sl.toNat < 2 ^ 64)]
                                    exact hwv0_eq
                                have hwv1_mod : ∀ (h : (2 * sl.toNat + 1) % 2 ^ 64 <
                                    s.core.wvec.length),
                                    (s.core.wvec[(2 * sl.toNat + 1) % 2 ^ 64]'h).toNat = sz0 :=
                                  fun _ => by
                                    simp only [Nat.mod_eq_of_lt (by omega :
                                      2 * sl.toNat + 1 < 2 ^ 64)]
                                    exact hwv1_eq
                                have hqi_mc_q : qi.toNat < mc_q.length := by
                                  rw [hmc_ql]
                                  exact Nat.lt_of_lt_of_le hqi_vn
                                    (Nat.le_trans hvn_qc (Nat.le_trans hcap_le_cv hcv_le))
                                have hsl_raw :
                                    ((mc_q[qi.toNat]'hqi_mc_q <<< (1 : Nat)) |||
                                      sgn).toNat = sl.toNat := by
                                  simp only [sl, sidx, hqi64]
                                have hbv1_64 : BitVec.toNat (1 : BitVec 64) = 1 := rfl
                                have hend_c0 :
                                    ∀ (h0 : 2 * ((mc_q[qi.toNat]'hqi_mc_q <<<
                                        (1 : Nat)) ||| sgn).toNat % 2 ^ 64 < s.core.wvec.length)
                                      (h1 : (2 * ((mc_q[qi.toNat]'hqi_mc_q <<<
                                        (1 : Nat)) ||| sgn).toNat + BitVec.toNat (1 : BitVec 64)) %
                                        2 ^ 64 < s.core.wvec.length),
                                      ((s.core.wvec[2 * ((mc_q[qi.toNat]'hqi_mc_q <<<
                                          (1 : Nat)) ||| sgn).toNat % 2 ^ 64]'h0).toNat +
                                       (s.core.wvec[(2 * ((mc_q[qi.toNat]'hqi_mc_q <<<
                                          (1 : Nat)) ||| sgn).toNat +
                                        BitVec.toNat (1 : BitVec 64)) %
                                          2 ^ 64]'h1).toNat) % 2 ^ 64 = off0 + sz0 := by
                                  intro h0 h1
                                  simp only [hsl_raw, hbv1_64, hwv0_mod, hwv1_mod, hmod_end]
                                c0_hfast_nogrp
                                -- `L28`: `p` loop `(vis_n_p, steps_p, p, ())`
                                refine wp_loop_inv
                                  (fun (vis_n_p, steps_p, p, ()) mp' => ∃ mc_p rp_p sig_p,
                                    off0 ≤ p.toNat ∧ p.toNat ≤ off0 + sz0 ∧
                                    DenseWatchSliceOk F_cur s.core sl.toNat p.toNat
                                      (off0 + sz0 - p.toNat) ∧
                                    layer_n.toNat ≤ vis_n_p.toNat ∧
                                    sbvaBfsInv c s R cap mc_p rp_p sig_p vis_n_p mp')
                                  (fun (_, _, p, _) _ => off0 + sz0 - p.toNat)
                                  (fun Jp' hJp' => by
                                    c0_hfast
                                    exact hJp' (vis_n_s, steps_s, _, ()) ms
                                      ⟨mc_s, rp_s, sig_s, by rw [hoff_c0]; exact Nat.le_refl _,
                                       by rw [hoff_c0]; omega,
                                       by rw [hoff_c0, Nat.add_sub_cancel_left]; exact hslice_sl,
                                       hlay_s, hmc_sl, hrp_sl, hsig_sl, hvn_s1, hvn_sc, hmc_sok,
                                       hms⟩)
                                  (fun Jp' (vis_n_p, steps_p, p, ()) mp' ⟨mc_p, rp_p, sig_p,
                                      hp_ge, hp_le, hslice_p, hlay_p, hmc_pl, hrp_pl, hsig_pl,
                                      hvn_p1, hvn_pc, hmc_pok, hmp'⟩ ihp' => ?_)
                                c0_hfast_nogrp
                                -- Exit join `L29` (`sig = [[]]`) of `L28` -> `ihs`
                                refine wp_join0
                                  (fun m29 => ∃ mc29 rp29 sig29,
                                    layer_n.toNat ≤ vis_n_p.toNat ∧
                                    sbvaBfsInv c s R cap mc29 rp29 sig29 vis_n_p m29)
                                  (fun J29 m29 ⟨mc29, rp29, sig29, hlay29, hmc29, hrp29, hsig29,
                                      hvn29_1, hvn29_c, hmc29_ok, hm29⟩ => by
                                    c0_hfast
                                    exact ihs (vis_n_p, steps_p, sgn + 1#32, ()) m29
                                      (by dsimp only; rw [hsgn1]; omega)
                                      ⟨mc29, rp29, sig29, by rw [hsgn1]; omega, hlay29, hmc29,
                                       hrp29, hsig29, hvn29_1, hvn29_c, hmc29_ok, hm29⟩)
                                  (fun J29 hJ29 => ?_)
                                c0_hsplit
                                · have hp_lt : p.toNat < off0 + sz0 := by
                                    simp only [hend_c0] at hc
                                    exact hc
                                  c0_hsplit
                                  {
                              have hsteps_p_lt : steps_p.toNat < 128 :=
                                sbva_lt_bv32 (by decide) (by assumption)
                              have hp_ws : p.toNat < s.core.wstk.length := by omega
                              have hp1_n : (p + 1#64).toNat = p.toNat + 1 :=
                                sbva_bv64_add1 hp_lt (by omega)
                              have hp1_mod :
                                  (p.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 =
                                    p.toNat + 1 := by
                                rw [show BitVec.toNat (1 : BitVec 64) = 1 from rfl]; omega
                              clear ihh hJ14 ihqi hJ23 hJ26 ihs
                              clear hmh hms hmq
                              let w0 := s.core.wstk[p.toNat]'hp_ws
                              c0_hfast_nogrp
                              -- Join `L30` (`is_bin`)
                              refine wp_join_state1 (t := i32) (α := BitVec 32) id
                                (fun is_bin m30 => m30 = mp' ∧
                                  (is_bin ≠ 0#32 ↔ (w0 &&& 0x80000000#32) ≠ 0#32))
                                (fun _ is_bin m30 ⟨hm30, his_bin_iff⟩ => ?_)
                                (fun Jib hJib => by
                                  c0_hfast
                                  · exact hJib 1#32 mp' ⟨rfl, ⟨fun _ => hc, fun _ => by decide⟩⟩
                                  · exact hJib 0#32 mp' ⟨rfl,
                                      ⟨fun h => absurd rfl h, fun h => absurd hc h⟩⟩)
                              · subst m30
                                -- Join `L31` (`(p_nxt, cr, clim)`)
                                refine wp_join_state
                                  (α := BitVec 64 × BitVec 32 × BitVec 32)
                                  (fun st => (st.1, st.2.1, st.2.2, ()))
                                  (fun ⟨p_nxt, cr, clim⟩ mjoin =>
                                    mjoin = mp' ∧ p.toNat < p_nxt.toNat ∧ p_nxt.toNat ≤ off0 + sz0 ∧
                                    DenseWatchSliceOk F_cur s.core sl.toNat p_nxt.toNat
                                      (off0 + sz0 - p_nxt.toNat) ∧
                                    (0 < clim.toNat →
                                      (clim = 1#32 ∧ (w0 &&& 0x80000000#32) ≠ 0#32 ∧
                                        (w0 &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars) ∨
                                      ((w0 &&& 0x80000000#32) = 0#32 ∧ 1 ≤ clim.toNat ∧
                                        clim.toNat ≤ 5 ∧
                                        cr.toNat ∈ fullArenaClauseRefsCore s.core ∧
                                        fullArenaClauseGarbCore s.core cr.toNat = false ∧
                                        clim.toNat = fullArenaClauseSizeCore s.core cr.toNat)))
                                  (fun _ ⟨p_nxt, cr, clim⟩ mjoin
                                      ⟨hmj, hp_inc, hp_nxt_le, hslice_nxt,
                                      hclim_ok⟩ => ?_)
                                  (fun Jcl hJcl => ?_)
                                · subst mjoin
                                  -- Join `L32` (`if (clim == 0u)`) carrying `(vis_n, steps)`
                                  refine wp_join_state
                                    (α := BitVec 32 × BitVec 32) (fun p => (p.1, p.2, ()))
                                    (fun ⟨vn32, st32⟩ m32 => ∃ mc32 rp32 sig32,
                                      layer_n.toNat ≤ vn32.toNat ∧
                                      sbvaBfsInv c s R cap mc32 rp32 sig32 vn32 m32)
                                    (fun _ ⟨vn32, st32⟩ m32
                                        ⟨mc32, rp32, sig32, hlay32, hmc32, hrp32,
                                        hsig32, hvn32_1, hvn32_c, hmc32_ok, hm32⟩ => by
                                      c0_hfast
                                      exact ihp' (vn32, st32, p_nxt, ()) m32
                                        (by dsimp only; omega)
                                        ⟨mc32, rp32, sig32, by omega, hp_nxt_le, hslice_nxt, hlay32,
                                         hmc32, hrp32, hsig32, hvn32_1, hvn32_c, hmc32_ok, hm32⟩)
                                    (fun J32 hJ32 => ?_)
                                  c0_hfast_nogrp
                                  · have hsteps_p1 : (steps_p + 1#32).toNat = steps_p.toNat + 1 :=
                                      sbva_bv32_add1 hsteps_p_lt (by decide)
                                    exact hJ32 (vis_n_p, steps_p + 1#32) mp'
                                      ⟨mc_p, rp_p, sig_p, hlay_p, hmc_pl, hrp_pl, hsig_pl, hvn_p1,
                                       hvn_pc, hmc_pok, hmp'⟩
                                  · have hclim_pos : 0 < clim.toNat := by c0_bound
                                    have hcl_info := hclim_ok hclim_pos
                                    -- `L33`: `j` loop `(vis_n_j, steps_j, j, ())`
                                    refine wp_loop_inv
                                      (fun (vis_n_j, steps_j, j, ()) mj => ∃ mc_j rp_j sig_j,
                                        j.toNat ≤ clim.toNat ∧ layer_n.toNat ≤ vis_n_j.toNat ∧
                                        sbvaBfsInv c s R cap mc_j rp_j sig_j vis_n_j mj)
                                      (fun (_, _, j, _) _ => clim.toNat - j.toNat)
                                      (fun Jj hJj => hJj (vis_n_p, steps_p, 0#32, ()) mp'
                                        ⟨mc_p, rp_p, sig_p, Nat.zero_le _, hlay_p, hmc_pl, hrp_pl,
                                         hsig_pl, hvn_p1, hvn_pc, hmc_pok, hmp'⟩)
                                      (fun Jj (vis_n_j, steps_j, j, ()) mj ⟨mc_j, rp_j, sig_j,
                                          hj_le, hlay_j, hmc_jl, hrp_jl, hsig_jl, hvn_j1, hvn_jc,
                                          hmc_jok, hmj'⟩ ihj => ?_)
                                    c0_hfast_nogrp
                                    · have hj_lt : j.toNat < clim.toNat := by assumption
                                      have hsteps_j_lt : steps_j.toNat < 128 :=
                                        sbva_lt_bv32 (by decide) (by assumption)
                                      have hj1 : (j + 1#32).toNat = j.toNat + 1 :=
                                        sbva_bv32_add1 hj_lt (by
                                    rcases hcl_info with ⟨rfl, _⟩ | ⟨_, _, h5, _⟩
                                    · decide
                                    · exact Nat.lt_of_le_of_lt h5 (by decide))
                                      have hsteps_j1 : (steps_j + 1#32).toNat =
                                          steps_j.toNat + 1 :=
                                        sbva_bv32_add1 hsteps_j_lt (by decide)
                                      -- Join `L34` (`ov`)
                                      refine wp_join_state1 (t := i32) (α := BitVec 32) id
                                        (fun ov mo => mo = mj ∧ ov.toNat < s.core.cur_vars)
                                        (fun _ ov mo ⟨hmo, hov_lt⟩ => ?_)
                                        (fun Jov hJov => ?_)
                                      · subst mo
                                        -- Join `L35` (`if (ov != sidx)`) carrying `vis_n'` -> `ihj`
                                        refine wp_join_state1 (t := i32) (α := BitVec 32) id
                                          (fun vn35 m35 => ∃ mc35 rp35 sig35,
                                            layer_n.toNat ≤ vn35.toNat ∧
                                            sbvaBfsInv c s R cap mc35 rp35 sig35 vn35 m35)
                                          (fun _ vn35 m35 ⟨mc35, rp35, sig35, hlay35, hmc35, hrp35,
                                              hsig35, hvn35_1, hvn35_c, hmc35_ok, hm35⟩ => by
                                            c0_hfast
                                            exact ihj (vn35, steps_j + 1#32, j + 1#32, ()) m35
                                              (by dsimp only; rw [hj1]; omega)
                                              ⟨mc35, rp35, sig35, by rw [hj1]; omega, hlay35, hmc35,
                                               hrp35, hsig35, hvn35_1, hvn35_c, hmc35_ok, hm35⟩)
                                          (fun J35 hJ35 => ?_)
                                        c0_hfast_nogrp
                                        · exact sbva_l35_wp hcv_le hcap_le_cv hcap_le_32 hlay_j
                                            hmc_jl hrp_jl hsig_jl hvn_j1 hvn_jc hmc_jok hmj'
                                            hov_lt hJ35
                                        · exact hJ35 vis_n_j mj
                                            ⟨mc_j, rp_j, sig_j, hlay_j, hmc_jl, hrp_jl, hsig_jl,
                                             hvn_j1, hvn_jc, hmc_jok, hmj'⟩
                                      · rcases hcl_info with
                                            ⟨rfl, hbin, hlit_lt⟩ |
                                              ⟨hnbin, h1, h5, hcr_ref, hcr_ng, hsz_eq⟩
                                        · have his1 : is_bin ≠ 0#32 := his_bin_iff.mpr hbin
                                          c0_hfast
                                          · refine hJov ((w0 &&& 0x7FFFFFFF#32) >>> 1) mj ⟨rfl, ?_⟩
                                            rw [bv32_lshr1_nat]; omega
                                          · exact absurd (by assumption) his1
                                        · have his0 : is_bin = 0#32 :=
                                            Decidable.byContradiction fun hne =>
                                              (his_bin_iff.mp hne) hnbin
                                          have hcr_wf := hw.arena.refs_wf cr.toNat hcr_ref
                                          have hcr_end : cr.toNat + 3 + j.toNat <
                                              s.core.arena.length := by
                                            have h1' := hcr_wf.2.2.1; have h2' := hcr_wf.2.2.2.1
                                            rw [← hsz_eq] at h1'; omega
                                          have hcrj_eq :
                                              (BitVec.setWidth 64 cr + 3 +
                                                BitVec.setWidth 64 j).toNat =
                                                cr.toNat + 3 + j.toNat :=
                                            sbva_bw64_add3_add _ _
                                          c0_hfast
                                          · exact absurd his0 (by assumption)
                                          · have hol_lt :
                                                (s.core.arena[cr.toNat + 3 + j.toNat]'(by
                                                  omega)).toNat < 2 * s.core.cur_vars :=
                                              sbva_arena_lit_lt hcl hw hcr_ref hcr_ng hsz_eq
                                                hj_lt hcr_end
                                            refine hJov ((s.core.arena[(BitVec.setWidth 64 cr + 3 +
                                                BitVec.setWidth 64 j).toNat]'(by
                                                rw [hcrj_eq]; exact hcr_end)) >>> 1) mj ⟨rfl, ?_⟩
                                            rw [bv32_lshr1_nat]; simp only [hcrj_eq]; omega
                                    all_goals
                                      exact hJ32 (vis_n_j, steps_j) mj
                                        ⟨mc_j, rp_j, sig_j, hlay_j, hmc_jl, hrp_jl, hsig_jl, hvn_j1,
                                         hvn_jc, hmc_jok, hmj'⟩
                                · c0_hfast_nogrp
                                  · have his1 : is_bin ≠ 0#32 := by assumption
                                    have hbin_w0 : (w0 &&& 0x80000000#32) ≠ 0#32 :=
                                      his_bin_iff.mp his1
                                    have ⟨hot_lt, _, hrem_nxt⟩ :=
                                      FullBvaFwdHelpers.bva_slice_bin_info hslice_p (by omega) hp_ws
                                        hbin_w0
                                    exact hJcl (p + 1#64, 0#32, 1#32) mp'
                                      ⟨rfl, by rw [hp1_n]; omega, by rw [hp1_n]; omega,
                                       by rw [hp1_n,
                                            show off0 + sz0 - (p.toNat + 1) =
                                              off0 + sz0 - p.toNat - 1 by omega]
                                          exact hrem_nxt,
                                       fun _ => Or.inl ⟨rfl, hbin_w0, hot_lt⟩⟩
                                  · have his0 : is_bin = 0#32 := by assumption
                                    have hnbin_w0 : (w0 &&& 0x80000000#32) = 0#32 :=
                                      Decidable.byContradiction fun hne =>
                                        (his_bin_iff.mpr hne) his0
                                    have ⟨h2le, hrem_nxt⟩ :=
                                      FullBvaFwdHelpers.bva_slice_occ_info hslice_p (by omega) hp_ws
                                        hnbin_w0
                                    refine sbva_l41_wp hwcap har_b hcl hw hwstk_len hwlen_le
                                      har_arr hal_le hbd_sl' hp_ge hp_lt hp_ws hp1_n hp1_mod ?_
                                      hslice_p hnbin_w0 h2le hrem_nxt hmp' hJcl
                                    simp only [bv_c0, hsl_raw, hbv1_64, hwv0_mod, hwv1_mod,
                                      hmod_end]
                                  }
                                  · c0_hfast
                                    exact hJ29 mp'
                                      ⟨mc_p, rp_p, sig_p, hlay_p, hmc_pl, hrp_pl, hsig_pl, hvn_p1,
                                       hvn_pc, hmc_pok, hmp'⟩
                                · c0_hfast
                                  exact hJ29 mp'
                                    ⟨mc_p, rp_p, sig_p, hlay_p, hmc_pl, hrp_pl, hsig_pl, hvn_p1,
                                     hvn_pc, hmc_pok, hmp'⟩
                              · c0_hfast
                                exact hJ26 (vis_n_s, steps_s) ms
                                  ⟨mc_s, rp_s, sig_s, hlay_s, hmc_sl, hrp_sl, hsig_sl, hvn_s1,
                                   hvn_sc, hmc_sok, hms⟩
                            · c0_hfast
                              exact hJ26 (vis_n_s, steps_s) ms
                                ⟨mc_s, rp_s, sig_s, hlay_s, hmc_sl, hrp_sl, hsig_sl, hvn_s1,
                                 hvn_sc, hmc_sok, hms⟩
                          · exact hJ26 (vis_n_q, steps_q) mq
                              ⟨mc_q, rp_q, sig_q, hlay_le, hmc_ql, hrp_ql, hsig_ql, hvn_q1, hvn_qc,
                               hmc_qok, hmq⟩
                        · c0_hfast
                          exact hJ23 mq
                            ⟨mc_q, rp_q, sig_q, hmc_ql, hrp_ql, hsig_ql, hvn_q1, hvn_qc, hmc_qok,
                             hmq⟩
                      · c0_hfast
                        exact hJ23 mq
                          ⟨mc_q, rp_q, sig_q, hmc_ql, hrp_ql, hsig_ql, hvn_q1, hvn_qc, hmc_qok,
                           hmq⟩
                  all_goals
                    exact hJ14 mh ⟨mc_h, rp_h, sig_h, hvn_hc, hmc_hl, hrp_hl, hsig_hl, hmh⟩
              · -- `CONT L12`: `if (ci < ncntd && vis_n < seed_cap)` body of `L11`
                exact sbva_l11_cont_wp hcv_le hws_len hws1_len hnc_le h2cv_lt32 hcntd_ok
                  hcap_le_cv hcap_le_32 hsc_le hci_le hmc_l hrp_l hsig_l hvn1 hvn_c hmc_ok hmp
                  ihp hJ12
          · have hc0 : ¬ BitVec.toNat (0 : BitVec 32) < (id cap).toNat := by assumption
            exfalso
            rw [show BitVec.toNat (0 : BitVec 32) = 0 from rfl] at hc0
            exact hc0 hcap_pos
      all_goals
        exact hJtb ⟨best_deg, best_lit, ci, s.core.min_clr, s.core.repr, s.scratch.sim_sig⟩ m
          ⟨hbl_ok, hmclr_len, hrepr_len, hsig_len, by rw [sbvaBfsSt_self]; exact hm⟩

/-- State-preservation corollary exposing `fullBvaPickPres`, `FullDenseInvNoLm`, and `FullMem`.
-/
theorem full_bva_pick_sbva3_m8_pres_wp (Γ : Env)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {ncntd f0 : BitVec 32}
    (hinv : FullDenseInvNoLm c F0 F_cur s)
    (hf0 : f0.toNat < 2 * s.core.cur_vars) (hnc : ncntd.toNat ≤ 2 * s.core.cur_vars)
    (hcntd : ∀ i < ncntd.toNat, (s.scratch.work_stk1[i]?.getD 0#32).toNat < 2 * s.core.cur_vars)
    (hm : (FullMem c s ⋆ R) m)
    {Q : Post [i32]} {X : XPost}
    (hPost : ∀ (r : BitVec 32) (s' : FullState) (m' : Mem 64),
      FullDenseInvNoLm c F0 F_cur s' → fullBvaPickPres s s' →
      (r = 0xFFFFFFFF#32 ∨ r.toNat < 2 * s.core.cur_vars) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    Func.wp Γ full_bva_pick_sbva3_m8_body (c.hdr, ncntd, f0, ()) m Q X :=
  full_bva_pick_sbva3_m8_wp Γ (c.hdr, ncntd, f0, ()) m Q X
    ⟨c, F0, F_cur, s, R, rfl, hinv, hf0, hnc, hcntd, hm,
      fun r _repr' _mclr' _tc' _tl' _wsort' _ant' _sig' _shrk' m' hinv' hr hm' =>
        hPost r _ m' hinv'
          ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hr hm'⟩

/-! ## 3. Closed `1`-Row Spec Table, `m8SbvaTieEnv`, & `PatchModule` Exports -/

/-- Closed `1`-row specification table for `m8SbvaTieModule` (`noExit = true`). -/
def m8SbvaTieSpecTable : List SpecEntry :=
  [ ⟨"full_bva_pick_cand", [i64, i32, i32], [i32], fullBvaPickCandSpec, true⟩ ]

/-- Closed specification environment for `m8SbvaTieModule`. -/
def m8SbvaTieEnv : Env := Env.ofTable m8SbvaTieSpecTable

theorem m8SbvaTieSpecTable_len : m8SbvaTieSpecTable.length = 1 := by
  simp [m8SbvaTieSpecTable]

theorem m8SbvaTieSpecTable_sigs :
    m8SbvaTieSpecTable.map (fun e => (e.name, e.as, e.rs)) = m8SbvaTieModule.sigs := by
  t_kernel_rfl

theorem m8SbvaTieSpecTable_noExit : ∀ e ∈ m8SbvaTieSpecTable, e.noExit = true := by
  intro e he
  simp only [m8SbvaTieSpecTable, List.mem_cons, List.not_mem_nil, or_false] at he
  subst he; rfl

theorem m8SbvaTieEnv_noExit :
    ∀ f as bs xs m Q X X',
      m8SbvaTieEnv f as bs xs m Q X → m8SbvaTieEnv f as bs xs m Q X' :=
  Env.ofTable_noExit m8SbvaTieSpecTable_noExit

theorem m8SbvaPickCandFn_impl : SpecEntry.Impl m8SbvaTieEnv m8SbvaPickCandFn
    ⟨"full_bva_pick_cand", [i64, i32, i32], [i32], fullBvaPickCandSpec, true⟩ :=
  SpecEntry.Impl.of (full_bva_pick_sbva3_m8_wp m8SbvaTieEnv)

theorem m8SbvaTie_tableImpl :
    TableImpl m8SbvaTieEnv m8SbvaTieFns m8SbvaTieSpecTable :=
  ⟨m8SbvaPickCandFn_impl, trivial⟩

/-- Unconditional closed `ModuleOk` for `m8SbvaTieModule` (`0` externs, `0` exits). -/
theorem m8SbvaTie_moduleOk : ModuleOk m8SbvaTieEnv m8SbvaTieModule :=
  Env.ofTable_moduleOk m8SbvaTie_acyclic ⟨full_bva_pick_sbva3_m8_wf, trivial⟩ m8SbvaTie_tableImpl

/-- `FullM7Splice.patchRows`/`PatchModule`-ready `1`-row replacement preserving exact
`fullBvaPickCandSpec`. -/
def m8SbvaTiePatchRows : List SpecEntry :=
  [ ⟨"full_bva_pick_cand", [i64, i32, i32], [i32], fullBvaPickCandSpec, true⟩ ]

theorem m8SbvaTiePatchRows_sigs :
    m8SbvaTiePatchRows.map (fun e => (e.name, e.as, e.rs)) =
      m8SbvaTiePatchFns.map Fn.sig := by
  t_kernel_rfl

theorem m8SbvaTiePatchRows_noExit :
    m8SbvaTiePatchRows.all SpecEntry.noExit = true := by
  simp [m8SbvaTiePatchRows]

theorem m8SbvaTiePatch_tableImpl :
    TableImpl m8SbvaTieEnv m8SbvaTiePatchFns m8SbvaTiePatchRows :=
  m8SbvaTie_tableImpl

/-- Callee-free `TableImpl` lift for any downstream M8 environment `Γ`. -/
theorem m8SbvaTiePatch_tableImpl_of (Γ : Env) :
    TableImpl Γ m8SbvaTiePatchFns m8SbvaTiePatchRows :=
  ⟨SpecEntry.Impl.of (full_bva_pick_sbva3_m8_wp Γ), trivial⟩

/-! ## 4. Concrete `Mem 64` UNSAT Non-Vacuity (`XPost := False`, `0` SAT Proofs) -/

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) on `nvBvaDenseMem` with `ncntd = 2#32`
(exercising Loop 1 + Loop 2). -/
theorem nv_m8_bva_pick_sbva3 :
    Func.wp m8SbvaTieEnv full_bva_pick_sbva3_m8_body
      (nvOneLitCfg.hdr, 2#32, 0#32, ()) nvBvaDenseMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInvNoLm nvOneLitCfg nvOneLitF0 [[0], [1]] s' ∧
        (r = 0xFFFFFFFF#32 ∨ r.toNat < 2) ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvOneLitCfg nvBvaDenseState ⋆ emp) nvBvaDenseMem := by
    rw [sep_emp]; exact nvBvaDenseMem_ok
  refine full_bva_pick_sbva3_m8_wp m8SbvaTieEnv _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, [[0], [1]], nvBvaDenseState, emp, rfl,
      FullDenseInvW.toNoLm nvBvaDense_invW, by decide, by decide, ?_, hm,
      fun r _ _ _ _ _ _ _ _ m' hnl hr hm' => by
        rw [sep_emp] at hm'; exact ⟨_, hnl, hr, nvDeduceF0_unsat, hm'⟩⟩
  intro i hi
  have hi' : i < 2 := hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> decide

/-- Mutated concrete `Mem 64` state (`wsort := [2, 2]`, `work_stk1 := [0, 1]`) forcing
`best_c = 2` and `ties = 2 > 1` so the 3-hop SBVA tie-breaker branch actively runs. -/
def nvSbvaTieState : FullState :=
  { nvBvaDenseState with
    scratch := { nvBvaDenseState.scratch with
      wsort := [2#32, 2#32]
      work_stk1 := [0#32, 1#32] } }

/-- Concrete `Mem 64` memory image backing `nvSbvaTieState`. -/
def nvSbvaTieMem : Mem 64 :=
  storeMem (storeMem (storeMem (storeMem nvBvaDenseMem
    i32 nvOneLitCfg.pWsort 2#32)
    i32 (nvOneLitCfg.pWsort + 4#64) 2#32)
    i32 nvOneLitCfg.pWorkStk1 0#32)
    i32 (nvOneLitCfg.pWorkStk1 + 4#64) 1#32

private theorem nvSbvaTieMem_ok : (FullMem nvOneLitCfg nvSbvaTieState ⋆ emp) nvSbvaTieMem := by
  have hm0 : (FullMem nvOneLitCfg nvBvaDenseState ⋆ emp) nvBvaDenseMem := by
    rw [sep_emp]; exact nvBvaDenseMem_ok
  have h1 := (FullArenaTactics.store_full_wsort (i := 0) 2#32 (by decide) hm0).2
  have h2 := (FullArenaTactics.store_full_wsort (i := 1) 2#32 (by decide) h1).2
  have h3 := (FullArenaTactics.store_full_work_stk1 (i := 0) 0#32 (by decide) h2).2
  have h4 := (FullArenaTactics.store_full_work_stk1 (i := 1) 1#32 (by decide) h3).2
  have hws_eq :
      ((nvBvaDenseState.scratch.wsort.set 0 2#32).set 1 2#32) = [2#32, 2#32] := rfl
  have hwk_eq :
      ((nvBvaDenseState.scratch.work_stk1.set 0 0#32).set 1 1#32) = [0#32, 1#32] := rfl
  simpa only [nvSbvaTieMem, nvSbvaTieState, hws_eq, hwk_eq,
    show BitVec.ofNat 64 (4 * 0) = 0#64 from rfl,
    show BitVec.ofNat 64 (4 * 1) = 4#64 from rfl,
    BitVec.add_zero] using h4

private theorem nvSbvaTie_invNoLm :
    FullDenseInvNoLm nvOneLitCfg nvOneLitF0 [[0], [1]] nvSbvaTieState := by
  have h0 := FullDenseInvW.toNoLm nvBvaDense_invW
  exact fullDenseInvNoLm_with_core_aux h0 h0.1.core_ok.repr_len h0.1.core_ok.min_clr_len_arr
    h0.1.core_ok.tmp_len_arr h0.1.core_ok.flags_len h0.1.core_ok.tmp_len_le
    { h0.1.scratch_ok with wsort_len := rfl, work_stk1_len := rfl } rfl rfl

/-- Concrete `Mem 64` UNSAT non-vacuity (`XPost := False`) actively executing the
`best_c >= 2 && ties > 1` 3-hop SBVA tie-breaking branch (`0#32` and `1#32` tied at `cnt = 2`). -/
theorem nv_m8_bva_pick_sbva3_tie_3hop :
    Func.wp m8SbvaTieEnv full_bva_pick_sbva3_m8_body
      (nvOneLitCfg.hdr, 2#32, 0#32, ()) nvSbvaTieMem
      (fun (r, ()) m' => ∃ s',
        FullDenseInvNoLm nvOneLitCfg nvOneLitF0 [[0], [1]] s' ∧
        (r = 0xFFFFFFFF#32 ∨ r.toNat < 2) ∧ nvOneLitF0.Unsat ∧ FullMem nvOneLitCfg s' m')
      (fun _ _ _ _ => False) := by
  refine full_bva_pick_sbva3_m8_wp m8SbvaTieEnv _ _ _ _
    ⟨nvOneLitCfg, nvOneLitF0, [[0], [1]], nvSbvaTieState, emp, rfl,
      nvSbvaTie_invNoLm, by decide, by decide, ?_, nvSbvaTieMem_ok,
      fun r _ _ _ _ _ _ _ _ m' hnl hr hm' => by
        rw [sep_emp] at hm'; exact ⟨_, hnl, hr, nvDeduceF0_unsat, hm'⟩⟩
  intro i hi
  have hi' : i < 2 := hi
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> decide

end LeanQbe.T.Examples.Kissat.FullM8SbvaTie

end
