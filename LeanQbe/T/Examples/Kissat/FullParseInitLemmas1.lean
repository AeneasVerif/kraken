module

public import LeanQbe.T.Examples.Kissat.Full1
public import LeanQbe.T.Examples.Kissat.FullInv2
public import LeanQbe.T.Examples.Kissat.FullArena
public import LeanQbe.T.Examples.Kissat.DimacsLemmas
public meta import Lean.Elab.Tactic
public meta import LeanQbe.T.Logic.C0Step
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Parse/Init Specs, Geometry, Tactics, and Sizing Helpers (Part 1, `Stage 4`)

Defines:
1. Canonical Stage-4 shared invariants in `FullParseInitSpecs` (`FullMrkZero`, `FullLitMarksClear`,
   `FullArenaVarsNodup`, `FullLastLearnedWf`, `FullExtScratchOk`, `FullExtScratchPres`,
   `FullSparseInv`), pure sizing functions matching `Full1.lean`, and `hdrTail4` layout helpers.
2. Per-function `Spec` definitions matching `FullSpec2` for all `10` owned `Full1.lean` init,
   sizing, and zeroing functions (`full_fixed_bytes`, `full_calc_max_v`, `full_calc_ext_cap`,
   `full_calc_scr_cap`, `full_init_ptrs`, `full_init_hdr`, `full_init_arenas`,
   `full_zero_tables1`, `full_zero_tables2`, `full_init_state`).
3. Strictly scoped tactic bundle `FullParseInitTactics` (`fp_steps`, `fp_head_steps`, `hdrTail4`).
4. `BitVec` alignment, shift, and `array64`/`hdrTail4` slice indexing bridges.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
  LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 1. Canonical Stage-4 invariants, pure sizing, and `hdrTail4` -/

namespace FullParseInitSpecs

/-- Variable marks (`mrk[0 ..< max_vars]`) are cleared to `0#8`. -/
def FullMrkZero (c : FullCfg) (s : FullState) : Prop :=
  ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8

/-- Both variable `mrk[0..max_vars)` and literal `lit_mark[0..2*max_vars)` arrays are zero. -/
def FullLitMarksClear (c : FullCfg) (s : FullState) : Prop :=
  FullMrkZero c s ∧ (∀ l < 2 * c.max_vars, s.core.lit_mark[l]?.getD 0#8 = 0#8)

/-- Every non-garbage clause in the `D-Full` arena has variable-distinct literals. -/
def FullArenaVarsNodup (s : FullState) : Prop :=
  ∀ r ∈ fullArenaClauseRefs s, fullArenaClauseGarb s r = false →
    ((fullArenaClauseLits s r).map (· / 2)).Nodup

/-- Every active slot in `last_learned[0..8)` is `0xFFFFFFFF#32` or a live arena cref. -/
def FullLastLearnedWf (s : FullState) : Prop :=
  ∀ i < 8,
    let cr := s.scratch.last_learned[i]?.getD 0xFFFFFFFF#32
    cr = 0xFFFFFFFF#32 ∨ cr.toNat ∈ fullArenaClauseRefs s

/-- Combined Stage-4 scratch well-formedness (`FullLastLearnedWf` and `extend_len ≤ cap`). -/
def FullExtScratchOk (c : FullCfg) (s : FullState) : Prop :=
  FullLastLearnedWf s ∧ s.scratch.extend_len ≤ c.extend_cap

/-- Scratch-level equality predicate preserving `last_learned` and `extend_len`. -/
def FullExtScratchPres (s s' : FullState) : Prop :=
  s'.scratch.last_learned = s.scratch.last_learned ∧
  s'.scratch.extend_len = s.scratch.extend_len

/-- Canonical Stage-4 sparse-mode CDCL invariant (`UNSAT`-only). -/
def FullSparseInv (c : FullCfg) (F0 : CNF Nat) (s : FullState) : Prop :=
  FullCoreInv c F0 s ∧ FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧
  FullExtScratchOk c s ∧ s.core.dense_mode = 0#64

theorem FullLitMarksClear.to_marksClear {c : FullCfg} {s : FullState}
    (hlen : s.LengthsOk c) (h : FullLitMarksClear c s) : FullMarksClear s :=
  fun v hv => h.1 v (Nat.lt_of_lt_of_le hv hlen.core_ok.cur_vars_le)

theorem FullLitMarksClear.with_d {c : FullCfg} {s : FullState} (h : FullLitMarksClear c s)
    (dc dv : BitVec 64) :
    FullLitMarksClear c { s with core := { s.core with d_cur := dc, d_val := dv } } := h

theorem FullArenaVarsNodup.with_d {s : FullState} (h : FullArenaVarsNodup s)
    (dc dv : BitVec 64) :
    FullArenaVarsNodup { s with core := { s.core with d_cur := dc, d_val := dv } } := h

theorem FullExtScratchOk.with_d {c : FullCfg} {s : FullState} (h : FullExtScratchOk c s)
    (dc dv : BitVec 64) :
    FullExtScratchOk c { s with core := { s.core with d_cur := dc, d_val := dv } } := h

theorem FullSparseInv.with_d {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) (dc dv : BitVec 64) :
    FullSparseInv c F0 { s with core := { s.core with d_cur := dc, d_val := dv } } :=
  ⟨h.1.with_d dc dv, h.2.1.with_d dc dv, h.2.2.1.with_d dc dv, h.2.2.2.1.with_d dc dv, h.2.2.2.2⟩

theorem fullInv_init_sparse {c : FullCfg} {F0 : CNF Nat} {s : FullState} (hlen : s.LengthsOk c)
    (hinc : s.core.inconsistent = 0#64) (hal : s.core.arena_len = 0)
    (hwvec : s.core.wvec = List.replicate (4 * c.max_vars) 0#32)
    (hte : s.core.trail_end = 0) (hcl : s.core.cur_level = 0)
    (hft0 : (s.core.frame_trail[0]?.getD 0#32).toNat = 0)
    (hvals : s.core.vals = List.replicate (2 * c.max_vars) 0#8)
    (hmrk : s.core.mrk = List.replicate c.max_vars 0#8)
    (hlm : s.core.lit_mark = List.replicate (2 * c.max_vars) 0#8)
    (hll : ∀ i < 8, s.scratch.last_learned[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32)
    (hext : s.scratch.extend_len = 0) (hdense : s.core.dense_mode = 0#64) :
    FullSparseInv c F0 s := by
  have hi := fullInv_init (F0 := F0) hlen hinc hal hwvec hte hcl hft0 hvals hmrk
  refine ⟨hi.core, ⟨fun v hv => by rw [hmrk]; simp [hv], fun l hl => by rw [hlm]; simp [hl]⟩,
    ?_, ⟨fun i hi8 => Or.inl (hll i hi8), by omega⟩, hdense⟩
  intro r hr
  have : fullArenaClauseRefs s = [] := by
    unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [hal]; rfl
  rw [this] at hr; cases hr

theorem fullSparseInv_init {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (hlen : s.LengthsOk c) (hinc : s.core.inconsistent = 0#64) (hal : s.core.arena_len = 0)
    (hwvec : s.core.wvec = List.replicate (4 * c.max_vars) 0#32)
    (hte : s.core.trail_end = 0) (hcl : s.core.cur_level = 0)
    (hft0 : (s.core.frame_trail[0]?.getD 0#32).toNat = 0)
    (hvals : s.core.vals = List.replicate (2 * c.max_vars) 0#8)
    (hmrk : s.core.mrk = List.replicate c.max_vars 0#8)
    (hlmrk : s.core.lit_mark = List.replicate (2 * c.max_vars) 0#8)
    (hll : s.scratch.last_learned = List.replicate 16 0xFFFFFFFF#32)
    (hext : s.scratch.extend_len = 0) (hdense : s.core.dense_mode = 0#64) :
    FullSparseInv c F0 s :=
  fullInv_init_sparse hlen hinc hal hwvec hte hcl hft0 hvals hmrk hlmrk (fun i hi => by
    rw [hll]; simp only [List.getElem?_replicate, show i < 16 by omega, ↓reduceIte,
      Option.getD_some]) hext hdense

/-! ### Pure `Full1.lean` sizing functions and capacity bounds -/

def fullCalcMaxV (avail mv nc f0 : Nat) : Nat :=
  let rem0 := avail - f0
  let bva_cap :=
    if 2 ≤ mv ∧ nc * 48 + 8192 < rem0 then
      let cand := min (mv / 2 + 16) 4096
      let max_bva := (rem0 - nc * 48 - 4096) / 2688
      min cand max_bva
    else 0
  let max_v := mv + bva_cap
  let fixed := fullFixedBytes max_v
  if avail < fixed ∨ avail - fixed < nc * 40 + 136 then mv else max_v

def fullCalcExtCap (rem : Nat) : Nat :=
  if rem < 8192 then 0 else ((min (rem / 32) 131072) / 2) * 2

def fullCalcScrCap (rem : Nat) : Nat :=
  if rem < 8192 then 0 else
    let c := if 16384 ≤ rem then rem / 16 else rem / 32
    ((min c 32768) / 2) * 2

def fullInitDelCap (rem : Nat) : Nat :=
  if 524288 ≤ rem then 4096 else 8

def fullInitExtCap (nc rem : Nat) : Nat :=
  let del_b := fullInitDelCap rem * 12
  let e := fullCalcExtCap rem
  let s := fullCalcScrCap rem
  let dyn := del_b + 4 * e + 4 * s
  if rem < dyn + nc * 40 + 136 then 0 else e

def fullInitScrCap (nc rem : Nat) : Nat :=
  let del_b := fullInitDelCap rem * 12
  let e := fullCalcExtCap rem
  let s := fullCalcScrCap rem
  let dyn := del_b + 4 * e + 4 * s
  if rem < dyn + nc * 40 + 136 then 0 else s

def fullInitDyn (nc rem : Nat) : Nat :=
  fullInitDelCap rem * 12 + 4 * fullInitExtCap nc rem + 4 * fullInitScrCap nc rem

def fullInitAp (avail_dyn : Nat) : Nat :=
  min (((avail_dyn / 8) * 3) / 5) 134217727

def fullInitRp (avail_dyn : Nat) : Nat :=
  (fullInitAp avail_dyn + 5) / 6

def fullInitWp (avail_dyn : Nat) : Nat :=
  min (avail_dyn / 8 - fullInitAp avail_dyn - fullInitRp avail_dyn) 134217727

theorem fullCalcMaxV_ge {avail mv nc : Nat} :
    mv ≤ fullCalcMaxV avail mv nc (fullFixedBytes mv) := by
  unfold fullCalcMaxV; dsimp only; split <;> (try dsimp only) <;> split <;> omega

theorem fullCalcMaxV_le {avail mv nc f0 : Nat} :
    fullCalcMaxV avail mv nc f0 ≤ mv + 4096 := by
  unfold fullCalcMaxV; dsimp only; split <;> (try dsimp only) <;> split <;> omega

theorem fullCalcMaxV_lt {avail mv nc f0 : Nat} (hmv : mv < dimacsBound) :
    fullCalcMaxV avail mv nc f0 < 2 * dimacsBound := by
  have := fullCalcMaxV_le (avail := avail) (mv := mv) (nc := nc) (f0 := f0)
  unfold dimacsBound at *; omega

theorem fullCalcMaxV_fits {avail mv nc : Nat}
    (hfit : fullFixedBytes mv + nc * 40 + 136 ≤ avail) :
    fullFixedBytes (fullCalcMaxV avail mv nc (fullFixedBytes mv)) + nc * 40 + 136 ≤ avail := by
  unfold fullCalcMaxV; dsimp only; split <;> (try dsimp only) <;> split <;> omega

theorem fullCalcExtCap_lt {rem : Nat} : fullCalcExtCap rem < dimacsBound := by
  unfold fullCalcExtCap dimacsBound; split <;> omega

theorem fullCalcScrCap_lt {rem : Nat} : fullCalcScrCap rem < dimacsBound := by
  unfold fullCalcScrCap dimacsBound; split; omega; dsimp only; split <;> omega

theorem fullInitDelCap_lt {rem : Nat} : fullInitDelCap rem < dimacsBound := by
  unfold fullInitDelCap dimacsBound; split <;> omega

theorem fullInitExtCap_lt {nc rem : Nat} : fullInitExtCap nc rem < dimacsBound := by
  unfold fullInitExtCap; dsimp only; split
  · unfold dimacsBound; omega
  · exact fullCalcExtCap_lt

theorem fullInitScrCap_lt {nc rem : Nat} : fullInitScrCap nc rem < dimacsBound := by
  unfold fullInitScrCap; dsimp only; split
  · unfold dimacsBound; omega
  · exact fullCalcScrCap_lt

theorem fullInitAp_add_rp_le (avail_dyn : Nat) :
    fullInitAp avail_dyn + fullInitRp avail_dyn ≤ avail_dyn / 8 := by
  have h1 : fullInitAp avail_dyn ≤ (avail_dyn / 8 * 3) / 5 := Nat.min_le_left _ _
  have h2 : (avail_dyn / 8 * 3) / 5 + ((avail_dyn / 8 * 3) / 5 + 5) / 6 ≤ avail_dyn / 8 := by
    omega
  unfold fullInitRp; omega

theorem fullInitAp_lt {avail_dyn : Nat} : 2 * fullInitAp avail_dyn < 2 * dimacsBound := by
  unfold fullInitAp dimacsBound; omega

theorem fullInitWp_lt {avail_dyn : Nat} : 2 * fullInitWp avail_dyn < 2 * dimacsBound := by
  unfold fullInitWp dimacsBound; omega

theorem fullInitRp_lt {avail_dyn : Nat} : 2 * fullInitRp avail_dyn < 2 * dimacsBound := by
  unfold fullInitRp fullInitAp dimacsBound; omega

theorem fullInitDyn_le {nc rem : Nat} (hrem : nc * 40 + 136 ≤ rem) :
    fullInitDyn nc rem + 40 ≤ rem := by
  unfold fullInitDyn fullInitExtCap fullInitScrCap fullInitDelCap; dsimp only
  split <;> split <;> omega

theorem full_init_arena_fits {max_v nc avail : Nat}
    (h : fullFixedBytes max_v + nc * 40 + 136 ≤ avail) :
    let rem := avail - fullFixedBytes max_v
    let dyn := fullInitDyn nc rem
    let adyn := rem - dyn
    fullFixedBytes max_v + 4 * (2 * fullInitAp adyn) + 4 * (2 * fullInitWp adyn) +
      12 * fullInitDelCap rem + 4 * (2 * fullInitRp adyn) +
      4 * fullInitExtCap nc rem + 4 * fullInitScrCap nc rem ≤ avail := by
  intro rem dyn adyn
  have hap := fullInitAp_add_rp_le adyn
  have hdyn_eq : dyn = 12 * fullInitDelCap rem + 4 * fullInitExtCap nc rem +
      4 * fullInitScrCap nc rem := by dsimp only [dyn]; unfold fullInitDyn; omega
  have hwp : 8 * fullInitWp adyn ≤ 8 * (adyn / 8 - fullInitAp adyn - fullInitRp adyn) := by
    unfold fullInitWp; omega
  have hle8 : 8 * (adyn / 8) ≤ adyn := by omega
  have hdyn_le : dyn ≤ rem := by
    have := fullInitDyn_le (nc := nc) (rem := rem) (by omega); omega
  omega

/-! ### Pure `FullHdr` pointer offsets (`full_init_ptrs`, `full_init_arenas`, `full_init_hdr`) -/

def fullPVals (hdr : BitVec 64) (_mx : Nat) : BitVec 64 := hdr + BitVec.ofNat 64 1152
def fullPWalkVals (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPVals hdr mx + BitVec.ofNat 64 (valsBytes mx)
def fullPLitMark (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPWalkVals hdr mx + BitVec.ofNat 64 (valsBytes mx)
def fullPMark (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPLitMark hdr mx + BitVec.ofNat 64 (valsBytes mx)
def fullPPhases (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPMark hdr mx + BitVec.ofNat 64 (markBytes mx)
def fullPPhasesTarget (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPPhases hdr mx + BitVec.ofNat 64 (markBytes mx)
def fullPPhasesBest (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPPhasesTarget hdr mx + BitVec.ofNat 64 (markBytes mx)
def fullPWalkBest (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPPhasesBest hdr mx + BitVec.ofNat 64 (markBytes mx)
def fullPFlags (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPWalkBest hdr mx + BitVec.ofNat 64 (markBytes mx)
def fullPLevel (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPFlags hdr mx + BitVec.ofNat 64 (u32FullBytes mx)
def fullPReason (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPLevel hdr mx + BitVec.ofNat 64 (u32FullBytes mx)
def fullPTrail (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPReason hdr mx + BitVec.ofNat 64 (u32FullBytes mx)
def fullPTrailPos (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPTrail hdr mx + BitVec.ofNat 64 (u32FullBytes mx)
def fullPTmp (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPTrailPos hdr mx + BitVec.ofNat 64 (u32FullBytes mx)
def fullPHeap (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPTmp hdr mx + BitVec.ofNat 64 (u32FullBytes mx)
def fullPPos (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPHeap hdr mx + BitVec.ofNat 64 (u32FullBytes mx)
def fullPMinClr (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPPos hdr mx + BitVec.ofNat 64 (u32FullBytes mx)
def fullPShrinkStk (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPMinClr hdr mx + BitVec.ofNat 64 (u32FullBytes mx)
def fullPQPrev (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPShrinkStk hdr mx + BitVec.ofNat 64 (u32FullBytes mx)
def fullPQNext (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPQPrev hdr mx + BitVec.ofNat 64 (u32FullBytes mx)
def fullPQStamp (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPQNext hdr mx + BitVec.ofNat 64 (u32FullBytes mx)
def fullPFrameTrail (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPQStamp hdr mx + BitVec.ofNat 64 (u32FullBytes mx)
def fullPFrameDec (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPFrameTrail hdr mx + BitVec.ofNat 64 (u32FullBytes mx)
def fullPWvec (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPFrameDec hdr mx + BitVec.ofNat 64 (u32FullBytes mx)
def fullPRepr (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPWvec hdr mx + BitVec.ofNat 64 (16 * mx)
def fullPWsort (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPRepr hdr mx + BitVec.ofNat 64 (8 * mx)
def fullPWorkStk1 (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPWsort hdr mx + BitVec.ofNat 64 (8 * mx)
def fullPWorkStk2 (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPWorkStk1 hdr mx + BitVec.ofNat 64 (8 * mx)
def fullPTarjanMark (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPWorkStk2 hdr mx + BitVec.ofNat 64 (8 * mx)
def fullPTarjanReach (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPTarjanMark hdr mx + BitVec.ofNat 64 (8 * mx)
def fullPScore (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPTarjanReach hdr mx + BitVec.ofNat 64 (8 * mx)
def fullPSimSig (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPScore hdr mx + BitVec.ofNat 64 (8 * mx)
def fullPMinStk (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPSimSig hdr mx + BitVec.ofNat 64 (8 * mx)
def fullPGlueUsed (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPMinStk hdr mx + BitVec.ofNat 64 (8 * fullMinDepthOf mx)
def fullPLastLearned (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPGlueUsed hdr mx + BitVec.ofNat 64 256
def fullPArena (hdr : BitVec 64) (mx : Nat) : BitVec 64 :=
  fullPLastLearned hdr mx + BitVec.ofNat 64 64

def ptrsW0 (hdr : BitVec 64) (mx : Nat) (w0 : List (BitVec 64)) : List (BitVec 64) :=
  ((((((((((((((w0.set 4 (fullPVals hdr mx)).set 5 (fullPMark hdr mx)).set
    24 (fullPPhases hdr mx)).set 6 (fullPLevel hdr mx)).set 7 (fullPReason hdr mx)).set
    8 (fullPTrail hdr mx)).set 13 (fullPTmp hdr mx)).set 21 (fullPHeap hdr mx)).set
    22 (fullPPos hdr mx)).set 26 (fullPMinClr hdr mx)).set 9 (fullPWvec hdr mx)).set
    23 (fullPScore hdr mx)).set 25 (fullPMinStk hdr mx)).set 10 (fullPArena hdr mx)).set
    29 (BitVec.ofNat 64 (fullMinDepthOf mx))

def ptrsW1 (hdr : BitVec 64) (mx : Nat) (w1 : List (BitVec 64)) : List (BitVec 64) :=
  ((((((((w1.set 10 (fullPPhasesTarget hdr mx)).set 11 (fullPPhasesBest hdr mx)).set
    6 (fullPTrailPos hdr mx)).set 13 (fullPShrinkStk hdr mx)).set 7 (fullPQPrev hdr mx)).set
    8 (fullPQNext hdr mx)).set 9 (fullPQStamp hdr mx)).set 12 (fullPWsort hdr mx)).set
    15 (fullPGlueUsed hdr mx)

def ptrsW2 (hdr : BitVec 64) (mx : Nat) (w2 : List (BitVec 64)) : List (BitVec 64) :=
  ((((((((w2.set 27 (fullPLitMark hdr mx)).set 26 (fullPFlags hdr mx)).set
    30 (fullPFrameTrail hdr mx)).set 31 (fullPFrameDec hdr mx)).set 28 (fullPRepr hdr mx)).set
    32 (fullPWorkStk1 hdr mx)).set 33 (fullPWorkStk2 hdr mx)).set 34 (fullPTarjanMark hdr mx)).set
    29 (fullPSimSig hdr mx)

def ptrsW3 (hdr : BitVec 64) (mx : Nat) (w3 : List (BitVec 64)) : List (BitVec 64) :=
  (((w3.set 1 (fullPWalkVals hdr mx)).set 2 (fullPWalkBest hdr mx)).set
    0 (fullPTarjanReach hdr mx)).set 8 (fullPLastLearned hdr mx)

def arenasW0 (hdr : BitVec 64) (mx adyn : Nat) (w0 : List (BitVec 64)) : List (BitVec 64) :=
  let ap := fullInitAp adyn; let wp := fullInitWp adyn
  let pWstk := fullPArena hdr mx + BitVec.ofNat 64 (8 * ap)
  let pDel := pWstk + BitVec.ofNat 64 (8 * wp)
  ((((ptrsW0 hdr mx w0).set 11 pWstk).set 12 pDel).set
    0 (BitVec.ofNat 64 (2 * ap))).set 1 (BitVec.ofNat 64 (2 * wp))

def arenasW1 (hdr : BitVec 64) (mx adyn del_cap : Nat) (w1 : List (BitVec 64)) :
    List (BitVec 64) :=
  let ap := fullInitAp adyn; let wp := fullInitWp adyn; let rp := fullInitRp adyn
  let pRed := fullPArena hdr mx + BitVec.ofNat 64 (8 * ap) + BitVec.ofNat 64 (8 * wp) +
    BitVec.ofNat 64 (del_cap * 12)
  ((ptrsW1 hdr mx w1).set 14 pRed).set 16 (BitVec.ofNat 64 (2 * rp))

def arenasW3 (hdr : BitVec 64) (mx adyn del_cap ext_cap : Nat) (w3 : List (BitVec 64)) :
    List (BitVec 64) :=
  let ap := fullInitAp adyn; let wp := fullInitWp adyn; let rp := fullInitRp adyn
  let pExt := fullPArena hdr mx + BitVec.ofNat 64 (8 * ap) + BitVec.ofNat 64 (8 * wp) +
    BitVec.ofNat 64 (del_cap * 12) + BitVec.ofNat 64 (8 * rp)
  let pScr := pExt + BitVec.ofNat 64 (4 * ext_cap)
  ((ptrsW3 hdr mx w3).set 3 pExt).set 6 pScr

def hdrW0 (mv : Nat) (fuel : BitVec 64) (w0 : List (BitVec 64)) : List (BitVec 64) :=
  ((((((((((((((((w0.set 2 0#64).set 3 1#64).set 14 0#64).set 15 0#64).set 16 0#64).set
    17 fuel).set 18 0xFFFFFFFF#64).set 19 0#64).set 20 0#64).set
    27 (BitVec.ofNat 64 mv)).set 28 (1#64 <<< 28)).set 30 0#64).set 31 0#64).set
    32 1024#64).set 33 1048576#64).set 34 1024#64)

def hdrW1 (w1 : List (BitVec 64)) : List (BitVec 64) :=
  ((((((((((((((((((((((w1.set 18 0#64).set 19 0#64).set 20 0#64).set
    21 0xFFFFFFFF#64).set 22 0#64).set 23 0#64).set 24 0#64).set 25 0#64).set
    26 0#64).set 27 0#64).set 28 0#64).set 29 0#64).set 0 1#64).set 1 1#64).set
    2 0#64).set 3 0#64).set 4 0#64).set 5 0#64).set 30 0#64).set 31 0#64).set
    32 0#64).set 33 1000#64).set 34 0#64

def hdrW2 (mv max_v : Nat) (w2 : List (BitVec 64)) : List (BitVec 64) :=
  let q0 := if mv = 0 then 0xFFFFFFFF#64 else 0#64
  let ql := if mv = 0 then 0xFFFFFFFF#64 else BitVec.ofNat 64 (mv - 1)
  (((((((((((((((((((((((((w2.set 22 (BitVec.ofNat 64 max_v)).set
    23 (BitVec.ofNat 64 mv)).set 24 (BitVec.ofNat 64 (max_v - mv))).set
    25 (BitVec.ofNat 64 mv)).set 0 0#64).set 1 0#64).set 2 q0).set 3 ql).set 4 ql).set
    5 (BitVec.ofNat 64 mv)).set 6 (BitVec.ofNat 64 mv)).set 7 0#64).set 8 0#64).set
    9 1000#64).set 10 0#64).set 11 1000#64).set 12 0#64).set 13 2#64).set 14 6#64).set
    15 0#64).set 16 1#64).set 17 0#64).set 18 (1#64 <<< 24)).set 19 0#64).set
    20 (1#64 <<< 24)).set 21 0#64

def hdrW3 (mv : Nat) (w3 : List (BitVec 64)) : List (BitVec 64) :=
  let rng := 0x9E3779B97F4A7C15#64 ^^^ (BitVec.ofNat 64 mv + 1#64)
  ((((((((((((((((((((((((((w3.set 5 0#64).set 9 rng).set 10 100#64).set 11 0#64).set
    12 0#64).set 13 500#64).set 14 0#64).set 15 1500#64).set 16 0#64).set 17 0#64).set
    18 0#64).set 19 0#64).set 20 0#64).set 21 0#64).set 22 0#64).set 23 0#64).set
    24 0#64).set 25 0#64).set 26 0#64).set 27 0#64).set 28 0#64).set 29 0#64).set
    30 0#64).set 31 0#64).set 32 0#64).set 33 0#64).set 34 0#64

@[simp] theorem ptrsW0_len {h : BitVec 64} {mx : Nat} {w : List (BitVec 64)} :
    (ptrsW0 h mx w).length = w.length := by simp [ptrsW0]
@[simp] theorem ptrsW1_len {h : BitVec 64} {mx : Nat} {w : List (BitVec 64)} :
    (ptrsW1 h mx w).length = w.length := by simp [ptrsW1]
@[simp] theorem ptrsW2_len {h : BitVec 64} {mx : Nat} {w : List (BitVec 64)} :
    (ptrsW2 h mx w).length = w.length := by simp [ptrsW2]
@[simp] theorem ptrsW3_len {h : BitVec 64} {mx : Nat} {w : List (BitVec 64)} :
    (ptrsW3 h mx w).length = w.length := by simp [ptrsW3]
@[simp] theorem arenasW0_len {h : BitVec 64} {mx a : Nat} {w : List (BitVec 64)} :
    (arenasW0 h mx a w).length = w.length := by simp [arenasW0]
@[simp] theorem arenasW1_len {h : BitVec 64} {mx a d : Nat} {w : List (BitVec 64)} :
    (arenasW1 h mx a d w).length = w.length := by simp [arenasW1]
@[simp] theorem arenasW3_len {h : BitVec 64} {mx a d e : Nat} {w : List (BitVec 64)} :
    (arenasW3 h mx a d e w).length = w.length := by simp [arenasW3]
@[simp] theorem hdrW0_len {mv : Nat} {fu : BitVec 64} {w : List (BitVec 64)} :
    (hdrW0 mv fu w).length = w.length := by simp [hdrW0]
@[simp] theorem hdrW1_len {w : List (BitVec 64)} : (hdrW1 w).length = w.length := by simp [hdrW1]
@[simp] theorem hdrW2_len {mv mx : Nat} {w : List (BitVec 64)} :
    (hdrW2 mv mx w).length = w.length := by simp [hdrW2]
@[simp] theorem hdrW3_len {mv : Nat} {w : List (BitVec 64)} :
    (hdrW3 mv w).length = w.length := by simp [hdrW3]

/-- `4`-chunk `140`-word `FullHdr` tail assertion splitting `array64 (hdr + 32)`. -/
def hdrTail4 (hdr : BitVec 64) (w0 w1 w2 w3 : List (BitVec 64)) : Mem 64 → Prop :=
  fun m => w0.length = 35 ∧ w1.length = 35 ∧ w2.length = 35 ∧ w3.length = 35 ∧
    (array64 (hdr + 32) w0 ⋆ array64 (hdr + 312) w1 ⋆
      array64 (hdr + 592) w2 ⋆ array64 (hdr + 872) w3) m

theorem array64_append_eq (a : BitVec 64) (xs ys : List (BitVec 64)) :
    array64 a (xs ++ ys) =
      (array64 a xs ⋆ array64 (a + BitVec.ofNat 64 (8 * xs.length)) ys) := by
  rw [array64_eq_array, array64_eq_array, array64_eq_array, array_append]
  simp [Ty.bytes, Ty.size, i64]

theorem hdrTail4_eq_array64 {hdr : BitVec 64} {w0 w1 w2 w3 : List (BitVec 64)}
    (h0 : w0.length = 35) (h1 : w1.length = 35) (h2 : w2.length = 35) (h3 : w3.length = 35) :
    hdrTail4 hdr w0 w1 w2 w3 = array64 (hdr + 32) (w0 ++ w1 ++ w2 ++ w3) := by
  funext m; apply propext; constructor
  · rintro ⟨_, _, _, _, hm⟩
    rw [array64_append_eq, array64_append_eq, array64_append_eq]
    simp only [List.length_append, h0, h1, h2]
    rw [show hdr + 32 + BitVec.ofNat 64 (8 * 35) = hdr + 312 from by
      rw [show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl, ptr_add_ofNat]; rfl,
      show hdr + 32 + BitVec.ofNat 64 (8 * (35 + 35)) = hdr + 592 from by
      rw [show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl, ptr_add_ofNat]; rfl,
      show hdr + 32 + BitVec.ofNat 64 (8 * (35 + 35 + 35)) = hdr + 872 from by
      rw [show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl, ptr_add_ofNat]; rfl]
    exact sep_ac hm
  · intro hm
    rw [array64_append_eq, array64_append_eq, array64_append_eq] at hm
    simp only [List.length_append, h0, h1, h2] at hm
    rw [show hdr + 32 + BitVec.ofNat 64 (8 * 35) = hdr + 312 from by
      rw [show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl, ptr_add_ofNat]; rfl,
      show hdr + 32 + BitVec.ofNat 64 (8 * (35 + 35)) = hdr + 592 from by
      rw [show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl, ptr_add_ofNat]; rfl,
      show hdr + 32 + BitVec.ofNat 64 (8 * (35 + 35 + 35)) = hdr + 872 from by
      rw [show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl, ptr_add_ofNat]; rfl] at hm
    exact ⟨h0, h1, h2, h3, sep_ac hm⟩

/-! ### `Spec` definitions for all `10` owned `Full1.lean` functions (aligned with `FullSpec2`) -/

def fullZeroTables1Spec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    ∀ wstk' mstk' repr' sc' m',
      wstk'.length = c.wcap → mstk'.length = 2 * c.minDepth → repr'.length = 2 * c.max_vars →
      sc'.LengthsOk c → sc'.extend_len = s.scratch.extend_len →
      (∀ i < 16, sc'.last_learned[i]?.getD 0#32 = 0xFFFFFFFF#32) →
      let s' : FullState :=
        { s with
          core := { s.core with vals := List.replicate (2 * c.max_vars) 0#8
                                lit_mark := List.replicate (2 * c.max_vars) 0#8
                                wvec := List.replicate (4 * c.max_vars) 0#32
                                wstk := wstk', min_stk := mstk', repr := repr' }
          scratch := sc' }
      (FullMem c s' ⋆ R) m' → Q () m'

def fullZeroTables2Spec : Spec [i64] [] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    ∀ flags' fdec' sc' m',
      flags'.length = c.max_vars → fdec'.length = c.max_vars + 1 →
      sc'.LengthsOk c → FullExtScratchPres s { s with scratch := sc' } →
      let s' : FullState :=
        { s with
          core := { s.core with mrk := List.replicate c.max_vars 0#8
                                flags := flags'
                                lvl := List.replicate c.max_vars 0#32
                                rsns := List.replicate c.max_vars 0xFFFFFFFF#32
                                frame_trail := List.replicate (c.max_vars + 1) 0#32
                                frame_dec := fdec' }
          scratch := sc' }
      (FullMem c s' ⋆ R) m' → Q () m'

def fullFixedBytesSpec : Spec [i64] [i64] := fun (max_v, ()) m Q _ =>
  max_v.toNat < 2 * dimacsBound ∧ Q (BitVec.ofNat 64 (fullFixedBytes max_v.toNat), ()) m

def fullInitPtrsSpec : Spec [i64, i64, i64] [] := fun (h, hdr_addr, max_v, ()) m Q _ =>
  ∃ (ws : List (BitVec 64)) (R : Mem 64 → Prop),
    h = hdr_addr ∧ ws.length = 140 ∧ max_v.toNat < 2 * dimacsBound ∧
    hdr_addr.toNat + fullFixedBytes max_v.toNat < 2 ^ 64 ∧
    (array64 (hdr_addr + 32) ws ⋆ R) m ∧
    ∀ ws' m', ws'.length = 140 →
      (∀ (c : FullCfg), c.hdr = hdr_addr → c.max_vars = max_v.toNat →
        ws'[4]? = some c.pVals ∧ ws'[5]? = some c.pMark ∧ ws'[6]? = some c.pLevel ∧
        ws'[7]? = some c.pReason ∧ ws'[8]? = some c.pTrail ∧ ws'[9]? = some c.pWvec ∧
        ws'[10]? = some c.pArena ∧ ws'[13]? = some c.pTmp ∧ ws'[21]? = some c.pHeap ∧
        ws'[22]? = some c.pPos ∧ ws'[23]? = some c.pScore ∧ ws'[24]? = some c.pPhases ∧
        ws'[25]? = some c.pMinStk ∧ ws'[26]? = some c.pMinClr ∧
        ws'[29]? = some (BitVec.ofNat 64 c.minDepth) ∧ ws'[41]? = some c.pTrailPos ∧
        ws'[42]? = some c.pQPrev ∧ ws'[43]? = some c.pQNext ∧ ws'[44]? = some c.pQStamp ∧
        ws'[45]? = some c.pPhasesTarget ∧ ws'[46]? = some c.pPhasesBest ∧
        ws'[47]? = some c.pWsort ∧ ws'[48]? = some c.pShrinkStk ∧ ws'[50]? = some c.pGlueUsed ∧
        ws'[96]? = some c.pFlags ∧ ws'[97]? = some c.pLitMark ∧ ws'[98]? = some c.pRepr ∧
        ws'[99]? = some c.pSimSig ∧ ws'[100]? = some c.pFrameTrail ∧
        ws'[101]? = some c.pFrameDec ∧ ws'[102]? = some c.pWorkStk1 ∧
        ws'[103]? = some c.pWorkStk2 ∧ ws'[104]? = some c.pTarjanMark ∧
        ws'[105]? = some c.pTarjanReach ∧ ws'[106]? = some c.pWalkVals ∧
        ws'[107]? = some c.pWalkBest ∧ ws'[113]? = some c.pLastLearned) →
      (∀ i ∈ [0, 1, 11, 12, 49, 51, 52, 108, 109, 111, 112], ws'[i]? = ws[i]?) →
      (array64 (hdr_addr + 32) ws' ⋆ R) m' → Q () m'

def fullInitHdrSpec : Spec [i64, i64, i64, i64] [] := fun (h, mv, max_v, fuel, ()) m Q _ =>
  ∃ (c : FullCfg) (ws : List (BitVec 64)) (R : Mem 64 → Prop),
    h = c.hdr ∧ mv = BitVec.ofNat 64 c.mv ∧ max_v = BitVec.ofNat 64 c.max_vars ∧
    ws.length = 140 ∧
    (∀ (s0 : FullState),
      ∀ i ∈ [0, 1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 21, 22, 23, 24, 25, 26, 29,
              41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 96, 97, 98, 99, 100, 101,
              102, 103, 104, 105, 106, 107, 108, 109, 111, 112, 113],
        ws[i]? = (hdrTailWords c s0)[i]?) ∧
    (array64 (c.hdr + 32) ws ⋆ R) m ∧
    ∀ (s : FullState) m',
      s.core.cur_vars = c.mv → s.core.arena_len = 0 → s.core.wlen = 1 →
      s.core.trail_end = 0 → s.core.propagated = 0 → s.core.cur_level = 0 →
      s.core.tmp_len = 0 → s.core.fuel = fuel → s.core.unflushed = 0#64 →
      s.core.probing = 0#64 → s.core.min_clr_len = 0 → s.core.min_clr_full = 0#64 →
      s.core.oom = 0#64 → s.core.dense_mode = 0#64 → s.core.inconsistent = 0#64 →
      s.scratch.extend_len = 0 →
      (array64 (c.hdr + 32) (hdrTailWords c s) ⋆ R) m' → Q () m'

def fullCalcMaxVSpec : Spec [i64, i64, i64, i64] [i64] := fun (avail, mv, nc, f0, ()) m Q _ =>
  mv.toNat < dimacsBound ∧ nc.toNat < dimacsBound ∧
  f0.toNat = fullFixedBytes mv.toNat ∧ f0.toNat + nc.toNat * 40 + 136 ≤ avail.toNat ∧
  ∀ r : BitVec 64,
    mv.toNat ≤ r.toNat → r.toNat < 2 * dimacsBound →
    fullFixedBytes r.toNat + nc.toNat * 40 + 136 ≤ avail.toNat →
    Q (r, ()) m

def fullCalcExtCapSpec : Spec [i64] [i64] := fun (rem, ()) m Q _ =>
  ∀ r : BitVec 64,
    r.toNat ≤ 131072 → (rem.toNat < 8192 → r = 0#64) → 4 * r.toNat ≤ rem.toNat / 8 →
    Q (r, ()) m

def fullCalcScrCapSpec : Spec [i64] [i64] := fun (rem, ()) m Q _ =>
  ∀ r : BitVec 64,
    r.toNat ≤ 32768 → (rem.toNat < 8192 → r = 0#64) → 4 * r.toNat ≤ rem.toNat / 4 →
    Q (r, ()) m

def fullInitArenasSpec : Spec [i64, i64, i64, i64] [] :=
  fun (h, hdr_addr, max_v, avail_dyn, ()) m Q _ =>
    ∃ (ws : List (BitVec 64)) (dcap ecap scap : Nat) (R : Mem 64 → Prop),
      h = hdr_addr ∧ ws.length = 140 ∧ max_v.toNat < 2 * dimacsBound ∧
      dcap < dimacsBound ∧ ecap < dimacsBound ∧ scap < dimacsBound ∧
      ws[52]? = some (BitVec.ofNat 64 dcap) ∧ ws[109]? = some (BitVec.ofNat 64 ecap) ∧
      ws[112]? = some (BitVec.ofNat 64 scap) ∧
      hdr_addr.toNat + fullFixedBytes max_v.toNat + avail_dyn.toNat +
        12 * dcap + 4 * ecap + 4 * scap < 2 ^ 64 ∧
      (array64 (hdr_addr + 32) ws ⋆ R) m ∧
      ∀ (acap wcap rcap : Nat) (ws' : List (BitVec 64)) m',
        ws'.length = 140 →
        acap < 2 * dimacsBound → wcap < 2 * dimacsBound → rcap < 2 * dimacsBound →
        4 * acap + 4 * wcap + 4 * rcap ≤ avail_dyn.toNat →
        (40 ≤ avail_dyn.toNat → 1 ≤ wcap) →
        (∀ (c : FullCfg), c.hdr = hdr_addr → c.max_vars = max_v.toNat →
          c.arena_cap = acap → c.wcap = wcap → c.delayed_cap = dcap → c.red_cap = rcap →
          c.extend_cap = ecap → c.scratch_cap = scap →
          ws'[0]? = some (BitVec.ofNat 64 c.arena_cap) ∧
          ws'[1]? = some (BitVec.ofNat 64 c.wcap) ∧
          ws'[4]? = some c.pVals ∧ ws'[5]? = some c.pMark ∧ ws'[6]? = some c.pLevel ∧
          ws'[7]? = some c.pReason ∧ ws'[8]? = some c.pTrail ∧ ws'[9]? = some c.pWvec ∧
          ws'[10]? = some c.pArena ∧ ws'[11]? = some c.pWstk ∧ ws'[12]? = some c.pDelayed ∧
          ws'[13]? = some c.pTmp ∧ ws'[21]? = some c.pHeap ∧ ws'[22]? = some c.pPos ∧
          ws'[23]? = some c.pScore ∧ ws'[24]? = some c.pPhases ∧ ws'[25]? = some c.pMinStk ∧
          ws'[26]? = some c.pMinClr ∧ ws'[29]? = some (BitVec.ofNat 64 c.minDepth) ∧
          ws'[41]? = some c.pTrailPos ∧ ws'[42]? = some c.pQPrev ∧ ws'[43]? = some c.pQNext ∧
          ws'[44]? = some c.pQStamp ∧ ws'[45]? = some c.pPhasesTarget ∧
          ws'[46]? = some c.pPhasesBest ∧ ws'[47]? = some c.pWsort ∧
          ws'[48]? = some c.pShrinkStk ∧ ws'[49]? = some c.pRedRefs ∧
          ws'[50]? = some c.pGlueUsed ∧ ws'[51]? = some (BitVec.ofNat 64 c.red_cap) ∧
          ws'[52]? = some (BitVec.ofNat 64 c.delayed_cap) ∧ ws'[96]? = some c.pFlags ∧
          ws'[97]? = some c.pLitMark ∧ ws'[98]? = some c.pRepr ∧ ws'[99]? = some c.pSimSig ∧
          ws'[100]? = some c.pFrameTrail ∧ ws'[101]? = some c.pFrameDec ∧
          ws'[102]? = some c.pWorkStk1 ∧ ws'[103]? = some c.pWorkStk2 ∧
          ws'[104]? = some c.pTarjanMark ∧ ws'[105]? = some c.pTarjanReach ∧
          ws'[106]? = some c.pWalkVals ∧ ws'[107]? = some c.pWalkBest ∧
          ws'[108]? = some c.pExtendStk ∧ ws'[109]? = some (BitVec.ofNat 64 c.extend_cap) ∧
          ws'[111]? = some c.pScratchBuf ∧ ws'[112]? = some (BitVec.ofNat 64 c.scratch_cap) ∧
          ws'[113]? = some c.pLastLearned) →
        (array64 (hdr_addr + 32) ws' ⋆ R) m' → Q () m'

def fullInitStateSpec : Spec [i64, i64, i64, i64, i64] [.bool] :=
  fun (cnf_ptr, cend, hdr_addr, avail, fuel, ()) m Q _ =>
    ∃ (cnfBytes : List UInt8) (R : Mem 64 → Prop),
      cend = cnf_ptr + BitVec.ofNat 64 cnfBytes.length ∧
      cnf_ptr.toNat + cnfBytes.length < 2 ^ 64 ∧
      hdr_addr.toNat + avail.toNat < 2 ^ 64 ∧
      1152 ≤ avail.toNat ∧
      (bytes cnf_ptr cnfBytes ⋆ region hdr_addr avail.toNat ⋆ R) m ∧
      (∀ m', (bytes cnf_ptr cnfBytes ⋆ region hdr_addr avail.toNat ⋆ R) m' →
        (∀ mv nc rest, parseHeader cnfBytes = some (mv, nc, rest) →
          avail.toNat < fullFixedBytes mv + nc * 40 + 136) →
        Q (false, ()) m') ∧
      (∀ (c : FullCfg) (s : FullState) (j : Nat) (rest : List UInt8) (m' : Mem 64),
        c.hdr = hdr_addr → c.avail = avail.toNat →
        parseHeader cnfBytes = some (c.mv, c.nc, rest) →
        j ≤ cnfBytes.length → cnfBytes.drop j = rest →
        FullSparseInv c (shiftDownCnf CNF.empty) s →
        s.core.cur_vars = c.mv →
        s.core.d_cur = cnf_ptr + BitVec.ofNat 64 j →
        s.core.arena_len = 0 → s.core.wlen = 1 → s.core.trail_end = 0 →
        s.core.propagated = 0 → s.core.cur_level = 0 → s.core.fuel = fuel →
        s.core.unflushed = 0#64 → s.core.probing = 0#64 →
        s.core.min_clr_len = 0 → s.core.min_clr_full = 0#64 →
        s.core.oom = 0#64 → s.core.inconsistent = 0#64 →
        s.core.vals = List.replicate (2 * c.max_vars) 0#8 →
        s.core.wvec = List.replicate (4 * c.max_vars) 0#32 →
        s.core.mrk = List.replicate c.max_vars 0#8 →
        s.core.lit_mark = List.replicate (2 * c.max_vars) 0#8 →
        s.scratch.extend_len = 0 →
        (bytes cnf_ptr cnfBytes ⋆ FullMem c s ⋆ R) m' →
        Q (true, ()) m')

end FullParseInitSpecs

/-! ## 2. Scoped tactics (`FullParseInitTactics`) and `hdrTail4` accessors -/

namespace FullParseInitTactics

open FullParseInitSpecs

section BvC0Extras
@[scoped bv_c0] theorem bv32_0 : (0 : BitVec 32).toNat = 0 := rfl
@[scoped bv_c0] theorem bv32_1 : (1 : BitVec 32).toNat = 1 := rfl
@[scoped bv_c0] theorem bv64_0 : (0 : BitVec 64).toNat = 0 := rfl
@[scoped bv_c0] theorem bv64_1 : (1 : BitVec 64).toNat = 1 := rfl
@[scoped bv_c0] theorem bv32_mod64 (x : BitVec 32) : x.toNat % 2 ^ 64 = x.toNat :=
  Nat.mod_eq_of_lt (by have := x.isLt; omega)
@[scoped bv_c0] theorem bv32_div2_mod64 (x : BitVec 32) : (x.toNat / 2) % 2 ^ 64 = x.toNat / 2 :=
  Nat.mod_eq_of_lt (by have := x.isLt; omega)
@[scoped bv_c0] theorem bv64_mod64 (x : BitVec 64) : x.toNat % 2 ^ 64 = x.toNat :=
  Nat.mod_eq_of_lt x.isLt
@[scoped bv_c0] theorem bv64_shl1 (x : BitVec 64) :
    (x <<< (1 : Nat)).toNat = (2 * x.toNat) % 2 ^ 64 := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm]
@[scoped bv_c0] theorem bv64_xor1_nat (n : Nat) : n ^^^ 1 = n + 1 - 2 * (n % 2) := by
  have h := Kissat.litNeg_eq n; unfold Kissat.litNeg at h; rw [h]; split <;> omega
attribute [scoped bv_c0] BitVec.toNat_ushiftRight BitVec.toNat_shiftLeft BitVec.toNat_xor
  BitVec.toNat_and Nat.shiftLeft_eq Nat.shiftRight_eq_div_pow List.length_set List.length_replicate
attribute [scoped bv_c0 high] LeanQbe.T.bv_c0_zext32_64 LeanQbe.T.bv_c0_zext8_64
  LeanQbe.T.bv_c0_zext8_32
end BvC0Extras

theorem strip_le_32_64 {P : Prop} (h : P) : 32 ≤ 64 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_32 {P : Prop} (h : P) : 8 ≤ 32 ∧ P := ⟨by decide, h⟩
theorem strip_le_8_64 {P : Prop} (h : P) : 8 ≤ 64 ∧ P := ⟨by decide, h⟩

scoped elab "fp_unmdata" : tactic => Lean.Elab.Tactic.liftMetaTactic1 fun g => do
  let ty ← Lean.instantiateMVars (← g.getType)
  if ty.isMData then return some (← g.replaceTargetDefEq ty.consumeMData) else return some g

scoped macro "fp_strip" : tactic =>
  `(tactic| first | apply strip_le_32_64 | apply strip_le_8_32 | apply strip_le_8_64)

scoped macro "fp_clean" : tactic =>
  `(tactic| simp only [Nat.reduceLeDiff, Nat.le_refl, true_and, and_true, Bool.false_or,
    Bool.or_false, Bool.true_and, Bool.and_true, Bool.not_true, Bool.not_false,
    decide_eq_true_eq, decide_eq_false_iff_not])

/-- Run `c0_steps`, discharging width side-conditions left by `zext`/`sext`/`trunc`. -/
scoped macro "fp_steps" : tactic =>
  `(tactic| (all_goals try fp_unmdata; (repeat fp_strip); c0_steps; repeat (
    any_goals (first | fp_clean | fp_strip)
    all_goals try fp_unmdata; (repeat fp_strip); c0_steps)))

theorem ptr_add_nat (p : BitVec 64) (a b : Nat) :
    p + BitVec.ofNat 64 a + BitVec.ofNat 64 b = p + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

section Hdr4Access
@[scoped c0_load] theorem c0_load_dimacs_mv {d mv nc cur val : BitVec 64}
    {F : Mem 64 → Prop} {m : Mem 64} (hm : (dimacsState d mv nc cur val ⋆ F) m) :
    loadVal m i64 d = some mv := Kissat.load_dimacs_mv hm
@[scoped c0_load] theorem c0_load_dimacs_nc {d mv nc cur val : BitVec 64}
    {F : Mem 64 → Prop} {m : Mem 64} (hm : (dimacsState d mv nc cur val ⋆ F) m) :
    loadVal m i64 (d + 8) = some nc := Kissat.load_dimacs_nc hm

private theorem load_hdr4_idx (hdr off : BitVec 64) (w : List (BitVec 64))
    (base : Nat) {F : Mem 64 → Prop} {m : Mem 64} (hw : w.length = 35)
    (h1 : base ≤ off.toNat ∧ (off.toNat - base) % 8 = 0 ∧ (off.toNat - base) / 8 < 35)
    (hm : (array64 (hdr + BitVec.ofNat 64 base) w ⋆ F) m) :
    loadVal m i64 (hdr + off) = some (w[(off.toNat - base) / 8]'(by omega)) := by
  have haddr : hdr + BitVec.ofNat 64 base + BitVec.ofNat 64 (8 * ((off.toNat - base) / 8)) =
      hdr + off := by
    rw [ptr_add_nat, show base + 8 * ((off.toNat - base) / 8) = off.toNat by omega,
      bv_ofNat_toNat_eq]
  simpa [haddr] using loadVal_array64 (i := (off.toNat - base) / 8) (by omega) hm

private theorem store_hdr4_idx (hdr off v : BitVec 64) (w : List (BitVec 64))
    (base : Nat) {F : Mem 64 → Prop} {m : Mem 64} (hw : w.length = 35)
    (h1 : base ≤ off.toNat ∧ (off.toNat - base) % 8 = 0 ∧ (off.toNat - base) / 8 < 35)
    (hm : (array64 (hdr + BitVec.ofNat 64 base) w ⋆ F) m) :
    storeOk m i64 (hdr + off) ∧
      (array64 (hdr + BitVec.ofNat 64 base) (w.set ((off.toNat - base) / 8) v) ⋆ F)
        (storeMem m i64 (hdr + off) v) := by
  have haddr : hdr + BitVec.ofNat 64 base + BitVec.ofNat 64 (8 * ((off.toNat - base) / 8)) =
      hdr + off := by
    rw [ptr_add_nat, show base + 8 * ((off.toNat - base) / 8) = off.toNat by omega,
      bv_ofNat_toNat_eq]
  obtain ⟨hok, hst⟩ := store_array64 (i := (off.toNat - base) / 8) v (by omega) hm
  rw [haddr] at hok hst; exact ⟨hok, hst⟩

private theorem hdr4_split {hdr : BitVec 64} {w0 w1 w2 w3 : List (BitVec 64)}
    {F : Mem 64 → Prop} {m : Mem 64} (hm : (hdrTail4 hdr w0 w1 w2 w3 ⋆ F) m) :
    w0.length = 35 ∧ w1.length = 35 ∧ w2.length = 35 ∧ w3.length = 35 ∧
    ((array64 (hdr + BitVec.ofNat 64 32) w0 ⋆ array64 (hdr + BitVec.ofNat 64 312) w1 ⋆
      array64 (hdr + BitVec.ofNat 64 592) w2 ⋆ array64 (hdr + BitVec.ofNat 64 872) w3) ⋆ F) m := by
  obtain ⟨m1, m2, hu, hd, ⟨h0, h1, h2, h3, ha⟩, hf⟩ := hm
  have ha' : (array64 (hdr + BitVec.ofNat 64 32) w0 ⋆ array64 (hdr + BitVec.ofNat 64 312) w1 ⋆
      array64 (hdr + BitVec.ofNat 64 592) w2 ⋆ array64 (hdr + BitVec.ofNat 64 872) w3) m1 := by
    rw [show (BitVec.ofNat 64 32 : BitVec 64) = 32 from rfl,
      show (BitVec.ofNat 64 312 : BitVec 64) = 312 from rfl,
      show (BitVec.ofNat 64 592 : BitVec 64) = 592 from rfl,
      show (BitVec.ofNat 64 872 : BitVec 64) = 872 from rfl]
    exact ha
  exact ⟨h0, h1, h2, h3, m1, m2, hu, hd, ha', hf⟩

private theorem hdr4_join {hdr : BitVec 64} {w0 w1 w2 w3 : List (BitVec 64)}
    {F : Mem 64 → Prop} {m : Mem 64} (h0 : w0.length = 35) (h1 : w1.length = 35)
    (h2 : w2.length = 35) (h3 : w3.length = 35)
    (hm : ((array64 (hdr + BitVec.ofNat 64 32) w0 ⋆ array64 (hdr + BitVec.ofNat 64 312) w1 ⋆
      array64 (hdr + BitVec.ofNat 64 592) w2 ⋆ array64 (hdr + BitVec.ofNat 64 872) w3) ⋆ F) m) :
    (hdrTail4 hdr w0 w1 w2 w3 ⋆ F) m := by
  obtain ⟨m1, m2, hu, hd, ha, hf⟩ := hm
  have ha' : (array64 (hdr + 32) w0 ⋆ array64 (hdr + 312) w1 ⋆
      array64 (hdr + 592) w2 ⋆ array64 (hdr + 872) w3) m1 := by
    rw [show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl,
      show (312 : BitVec 64) = BitVec.ofNat 64 312 from rfl,
      show (592 : BitVec 64) = BitVec.ofNat 64 592 from rfl,
      show (872 : BitVec 64) = BitVec.ofNat 64 872 from rfl]
    exact ha
  exact ⟨m1, m2, hu, hd, ⟨h0, h1, h2, h3, ha'⟩, hf⟩

private theorem rot4_0 {A B C D F : Mem 64 → Prop} {m : Mem 64}
    (h : ((A ⋆ B ⋆ C ⋆ D) ⋆ F) m) : (A ⋆ (B ⋆ C ⋆ D ⋆ F)) m := sep_ac h
private theorem rot4_0_inv {A B C D F : Mem 64 → Prop} {m : Mem 64}
    (h : (A ⋆ (B ⋆ C ⋆ D ⋆ F)) m) : ((A ⋆ B ⋆ C ⋆ D) ⋆ F) m := sep_ac h
private theorem rot4_1 {A B C D F : Mem 64 → Prop} {m : Mem 64}
    (h : ((A ⋆ B ⋆ C ⋆ D) ⋆ F) m) : (B ⋆ (A ⋆ C ⋆ D ⋆ F)) m := sep_ac h
private theorem rot4_1_inv {A B C D F : Mem 64 → Prop} {m : Mem 64}
    (h : (B ⋆ (A ⋆ C ⋆ D ⋆ F)) m) : ((A ⋆ B ⋆ C ⋆ D) ⋆ F) m := sep_ac h
private theorem rot4_2 {A B C D F : Mem 64 → Prop} {m : Mem 64}
    (h : ((A ⋆ B ⋆ C ⋆ D) ⋆ F) m) : (C ⋆ (A ⋆ B ⋆ D ⋆ F)) m := sep_ac h
private theorem rot4_2_inv {A B C D F : Mem 64 → Prop} {m : Mem 64}
    (h : (C ⋆ (A ⋆ B ⋆ D ⋆ F)) m) : ((A ⋆ B ⋆ C ⋆ D) ⋆ F) m := sep_ac h
private theorem rot4_3 {A B C D F : Mem 64 → Prop} {m : Mem 64}
    (h : ((A ⋆ B ⋆ C ⋆ D) ⋆ F) m) : (D ⋆ (A ⋆ B ⋆ C ⋆ F)) m := sep_ac h
private theorem rot4_3_inv {A B C D F : Mem 64 → Prop} {m : Mem 64}
    (h : (D ⋆ (A ⋆ B ⋆ C ⋆ F)) m) : ((A ⋆ B ⋆ C ⋆ D) ⋆ F) m := sep_ac h

@[scoped c0_load] theorem c0_load_hdr4_0 {hdr off : BitVec 64} {w0 w1 w2 w3 : List (BitVec 64)}
    {F : Mem 64 → Prop} {m : Mem 64} (hm : (hdrTail4 hdr w0 w1 w2 w3 ⋆ F) m)
    (h : 32 ≤ off.toNat ∧ (off.toNat - 32) % 8 = 0 ∧ (off.toNat - 32) / 8 < 35) :
    loadVal m i64 (hdr + off) = some (w0[(off.toNat - 32) / 8]?.getD 0#64) := by
  obtain ⟨h0, _, _, _, hs⟩ := hdr4_split hm
  have hl := load_hdr4_idx hdr off w0 32 h0 h (rot4_0 hs)
  rwa [List.getElem?_eq_getElem (by omega), Option.getD_some]

@[scoped c0_load] theorem c0_load_hdr4_1 {hdr off : BitVec 64} {w0 w1 w2 w3 : List (BitVec 64)}
    {F : Mem 64 → Prop} {m : Mem 64} (hm : (hdrTail4 hdr w0 w1 w2 w3 ⋆ F) m)
    (h : 312 ≤ off.toNat ∧ (off.toNat - 312) % 8 = 0 ∧ (off.toNat - 312) / 8 < 35) :
    loadVal m i64 (hdr + off) = some (w1[(off.toNat - 312) / 8]?.getD 0#64) := by
  obtain ⟨_, h1, _, _, hs⟩ := hdr4_split hm
  have hl := load_hdr4_idx hdr off w1 312 h1 h (rot4_1 hs)
  rwa [List.getElem?_eq_getElem (by omega), Option.getD_some]

@[scoped c0_load] theorem c0_load_hdr4_2 {hdr off : BitVec 64} {w0 w1 w2 w3 : List (BitVec 64)}
    {F : Mem 64 → Prop} {m : Mem 64} (hm : (hdrTail4 hdr w0 w1 w2 w3 ⋆ F) m)
    (h : 592 ≤ off.toNat ∧ (off.toNat - 592) % 8 = 0 ∧ (off.toNat - 592) / 8 < 35) :
    loadVal m i64 (hdr + off) = some (w2[(off.toNat - 592) / 8]?.getD 0#64) := by
  obtain ⟨_, _, h2, _, hs⟩ := hdr4_split hm
  have hl := load_hdr4_idx hdr off w2 592 h2 h (rot4_2 hs)
  rwa [List.getElem?_eq_getElem (by omega), Option.getD_some]

@[scoped c0_load] theorem c0_load_hdr4_3 {hdr off : BitVec 64} {w0 w1 w2 w3 : List (BitVec 64)}
    {F : Mem 64 → Prop} {m : Mem 64} (hm : (hdrTail4 hdr w0 w1 w2 w3 ⋆ F) m)
    (h : 872 ≤ off.toNat ∧ (off.toNat - 872) % 8 = 0 ∧ (off.toNat - 872) / 8 < 35) :
    loadVal m i64 (hdr + off) = some (w3[(off.toNat - 872) / 8]?.getD 0#64) := by
  obtain ⟨_, _, _, h3, hs⟩ := hdr4_split hm
  have hl := load_hdr4_idx hdr off w3 872 h3 h (rot4_3 hs)
  rwa [List.getElem?_eq_getElem (by omega), Option.getD_some]

@[scoped c0_store] theorem c0_store_hdr4_0 (off v hdr : BitVec 64) (w0 w1 w2 w3 : List (BitVec 64))
    {F : Mem 64 → Prop} {m : Mem 64} (hm : (hdrTail4 hdr w0 w1 w2 w3 ⋆ F) m)
    (h : 32 ≤ off.toNat ∧ (off.toNat - 32) % 8 = 0 ∧ (off.toNat - 32) / 8 < 35) :
    storeOk m i64 (hdr + off) ∧
      (hdrTail4 hdr (w0.set ((off.toNat - 32) / 8) v) w1 w2 w3 ⋆ F)
        (storeMem m i64 (hdr + off) v) := by
  obtain ⟨h0, h1, h2, h3, hs⟩ := hdr4_split hm
  obtain ⟨hok, hst⟩ := store_hdr4_idx hdr off v w0 32 h0 h (rot4_0 hs)
  exact ⟨hok, hdr4_join (by simp [h0]) h1 h2 h3 (rot4_0_inv hst)⟩

@[scoped c0_store] theorem c0_store_hdr4_1 (off v hdr : BitVec 64) (w0 w1 w2 w3 : List (BitVec 64))
    {F : Mem 64 → Prop} {m : Mem 64} (hm : (hdrTail4 hdr w0 w1 w2 w3 ⋆ F) m)
    (h : 312 ≤ off.toNat ∧ (off.toNat - 312) % 8 = 0 ∧ (off.toNat - 312) / 8 < 35) :
    storeOk m i64 (hdr + off) ∧
      (hdrTail4 hdr w0 (w1.set ((off.toNat - 312) / 8) v) w2 w3 ⋆ F)
        (storeMem m i64 (hdr + off) v) := by
  obtain ⟨h0, h1, h2, h3, hs⟩ := hdr4_split hm
  obtain ⟨hok, hst⟩ := store_hdr4_idx hdr off v w1 312 h1 h (rot4_1 hs)
  exact ⟨hok, hdr4_join h0 (by simp [h1]) h2 h3 (rot4_1_inv hst)⟩

@[scoped c0_store] theorem c0_store_hdr4_2 (off v hdr : BitVec 64) (w0 w1 w2 w3 : List (BitVec 64))
    {F : Mem 64 → Prop} {m : Mem 64} (hm : (hdrTail4 hdr w0 w1 w2 w3 ⋆ F) m)
    (h : 592 ≤ off.toNat ∧ (off.toNat - 592) % 8 = 0 ∧ (off.toNat - 592) / 8 < 35) :
    storeOk m i64 (hdr + off) ∧
      (hdrTail4 hdr w0 w1 (w2.set ((off.toNat - 592) / 8) v) w3 ⋆ F)
        (storeMem m i64 (hdr + off) v) := by
  obtain ⟨h0, h1, h2, h3, hs⟩ := hdr4_split hm
  obtain ⟨hok, hst⟩ := store_hdr4_idx hdr off v w2 592 h2 h (rot4_2 hs)
  exact ⟨hok, hdr4_join h0 h1 (by simp [h2]) h3 (rot4_2_inv hst)⟩

@[scoped c0_store] theorem c0_store_hdr4_3 (off v hdr : BitVec 64) (w0 w1 w2 w3 : List (BitVec 64))
    {F : Mem 64 → Prop} {m : Mem 64} (hm : (hdrTail4 hdr w0 w1 w2 w3 ⋆ F) m)
    (h : 872 ≤ off.toNat ∧ (off.toNat - 872) % 8 = 0 ∧ (off.toNat - 872) / 8 < 35) :
    storeOk m i64 (hdr + off) ∧
      (hdrTail4 hdr w0 w1 w2 (w3.set ((off.toNat - 872) / 8) v) ⋆ F)
        (storeMem m i64 (hdr + off) v) := by
  obtain ⟨h0, h1, h2, h3, hs⟩ := hdr4_split hm
  obtain ⟨hok, hst⟩ := store_hdr4_idx hdr off v w3 872 h3 h (rot4_3 hs)
  exact ⟨hok, hdr4_join h0 h1 h2 (by simp [h3]) (rot4_3_inv hst)⟩
end Hdr4Access

/-! ### Fast `fp_head_steps` tactic for `hdrTail4` initialization -/

scoped elab "fp_beta" : tactic => Lean.Elab.Tactic.withMainContext do
  let g ← Lean.Elab.Tactic.getMainGoal
  let ty ← Lean.instantiateMVars (← g.getType)
  if ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6 then
    let e := ty.getArg! 4; let e' := e.headBeta
    if e' != e then
      let g' ← Lean.Meta.withTransparency .reducible
        (g.replaceTargetDefEq (Lean.mkAppN ty.getAppFn (ty.getAppArgs.set! 4 e')))
      Lean.Elab.Tactic.setGoals [g']

private meta def clearStaleMem (m0 : Lean.Expr) : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
    let .fvar mId := m0 | return
    for d in (← Lean.getLCtx).decls.toArray.reverse do
      let some d := d | continue
      let t ← Lean.instantiateMVars d.type
      if t.isAppOf ``Std.ExtHashMap.sep && t.appArg! == m0 then
        try Lean.Elab.Tactic.liftMetaTactic1 fun g => some <$> g.clear d.fvarId catch _ => pure ()
    try Lean.Elab.Tactic.liftMetaTactic1 fun g => some <$> g.clear mId catch _ => pure ()

theorem fp_fst {α β : Type} (a : α) (b : β) : (a, b).1 = a := rfl
theorem fp_snd {α β : Type} (a : α) (b : β) : (a, b).2 = b := rfl

section FpLetSteps
variable {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64} {n : Nat}
theorem fp_let_copy {t : Ty} (a : Arg Val t) (k : Tup Val [t] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.copy t) (a, ())) k) m = wp Γ Q X (k (a.val, ())) m := by
  simp [wp_let_copy_eq]
theorem fp_let_add (a b : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.add (.bits n)) (a, b, ())) k) m =
      wp Γ Q X (k (a.val + b.val, ())) m := by simp [wp_let_add_eq, lift2, Ty.hasFloat]
theorem fp_let_sub (a b : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.sub (.bits n)) (a, b, ())) k) m =
      wp Γ Q X (k (a.val - b.val, ())) m := by simp [wp_let_sub_eq, lift2, Ty.hasFloat]
theorem fp_let_mul (a b : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.mul (.bits n)) (a, b, ())) k) m =
      wp Γ Q X (k (a.val * b.val, ())) m := by simp [wp_let_mul_eq, lift2, Ty.hasFloat]
theorem fp_let_and (a b : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.and (.bits n)) (a, b, ())) k) m =
      wp Γ Q X (k (a.val &&& b.val, ())) m := by simp [wp_let_and_eq, lift2]
theorem fp_let_xor (a b : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.xor (.bits n)) (a, b, ())) k) m =
      wp Γ Q X (k (a.val ^^^ b.val, ())) m := by simp [wp_let_xor_eq, lift2]
theorem fp_let_not (a : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.not (.bits n)) (a, ())) k) m =
      wp Γ Q X (k (~~~a.val, ())) m := by simp [wp_let_not_eq, lift1]
theorem fp_let_shl (a b : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.shl (.bits n)) (a, b, ())) k) m =
      wp Γ Q X (k (a.val <<< (b.val.toNat % n), ())) m := by
  simp [wp_let_shl_eq, lift2, Ty.hasFloat]
theorem fp_let_lshr (a b : Arg Val (.bits n)) (k : Tup Val [.bits n] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.lshr (.bits n)) (a, b, ())) k) m =
      wp Γ Q X (k (a.val >>> (b.val.toNat % n), ())) m := by
  simp [wp_let_lshr_eq, lift2, Ty.hasFloat]
theorem fp_let_sext {mW nW : Nat} (a : Arg Val (.bits mW))
    (k : Tup Val [.bits nW] → Expr Val Cont rs) (h : mW ≤ nW) :
    wp Γ Q X (.let_ (Op.mk (.sext mW nW) (a, ())) k) m =
      wp Γ Q X (k (a.val.signExtend nW, ())) m := by simp [wp_let_sext_eq, h]
theorem fp_let_ult {hm : Ty.bool = (Ty.bits n).mask} (a b : Arg Val (.bits n))
    (k : Tup Val [.bool] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.cmp .ult (.bits n) .bool hm) (a, b, ())) k) m =
      wp Γ Q X (k (a.val.ult b.val, ())) m := by
  simp [wp_let_cmp_eq, liftCmp, Ty.hasFloat, CmpOp.evalBits]
theorem fp_let_ule {hm : Ty.bool = (Ty.bits n).mask} (a b : Arg Val (.bits n))
    (k : Tup Val [.bool] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.cmp .ule (.bits n) .bool hm) (a, b, ())) k) m =
      wp Γ Q X (k (a.val.ule b.val, ())) m := by
  simp [wp_let_cmp_eq, liftCmp, Ty.hasFloat, CmpOp.evalBits]
theorem fp_let_ugt {hm : Ty.bool = (Ty.bits n).mask} (a b : Arg Val (.bits n))
    (k : Tup Val [.bool] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.cmp .ugt (.bits n) .bool hm) (a, b, ())) k) m =
      wp Γ Q X (k (b.val.ult a.val, ())) m := by
  simp [wp_let_cmp_eq, liftCmp, Ty.hasFloat, CmpOp.evalBits]
theorem fp_let_uge {hm : Ty.bool = (Ty.bits n).mask} (a b : Arg Val (.bits n))
    (k : Tup Val [.bool] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.cmp .uge (.bits n) .bool hm) (a, b, ())) k) m =
      wp Γ Q X (k (b.val.ule a.val, ())) m := by
  simp [wp_let_cmp_eq, liftCmp, Ty.hasFloat, CmpOp.evalBits]
theorem fp_let_eq {hm : Ty.bool = (Ty.bits n).mask} (a b : Arg Val (.bits n))
    (k : Tup Val [.bool] → Expr Val Cont rs) :
    wp Γ Q X (.let_ (Op.mk (.cmp .eq (.bits n) .bool hm) (a, b, ())) k) m =
      wp Γ Q X (k (a.val == b.val, ())) m := by
  have heq : decide (a.val = b.val) = (a.val == b.val) := by
    cases hb : a.val == b.val <;> simp_all
  simp [wp_let_cmp_eq, liftCmp, Ty.hasFloat, CmpOp.evalBits, heq]
end FpLetSteps

scoped macro "fp_val_simp" : conv =>
  `(conv| simp only [fp_fst, fp_snd, LeanQbe.T.op1_eq_mk, LeanQbe.T.op2_eq_mk, LeanQbe.T.vals_nil,
    LeanQbe.T.vals_cons, LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm, LeanQbe.T.Ty.hasFloat,
    LeanQbe.T.OpCode.ult, LeanQbe.T.OpCode.ule, LeanQbe.T.OpCode.ugt, LeanQbe.T.OpCode.uge,
    LeanQbe.T.OpCode.eq, LeanQbe.T.evalBits_ult_eq, LeanQbe.T.evalBits_ule_eq,
    LeanQbe.T.evalBits_ugt_eq, LeanQbe.T.evalBits_uge_eq, LeanQbe.T.evalBits_eq_beq,
    LeanQbe.T.liftCmp, cast_eq, ite_self, ite_true, ite_false])

private meta def findSepMem (m0 : Lean.Expr) : Lean.Elab.Tactic.TacticM (Option Lean.Expr) :=
  Lean.Elab.Tactic.withMainContext do
    for d in (← Lean.getLCtx).decls.toArray.reverse do
      let some d := d | continue
      if d.isImplementationDetail then continue
      let t ← Lean.instantiateMVars d.type
      if t.isAppOf ``Std.ExtHashMap.sep && t.appArg! == m0 then
        let sArgs := t.getAppArgs
        if sArgs.size ≥ 3 && sArgs[sArgs.size - 3]!.isAppOf ``hdrTail4 then
          return some d.toExpr
    return none

private meta def normHdrIdx (hmId : Lean.FVarId) : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
    let ty ← Lean.instantiateMVars (← hmId.getType)
    if !ty.isAppOf ``Std.ExtHashMap.sep then return
    let sArgs := ty.getAppArgs
    if sArgs.size < 3 then return
    let p := sArgs[sArgs.size - 3]!
    if !(p.isAppOf ``hdrTail4 && p.getAppNumArgs == 5) then return
    let mut args := p.getAppArgs
    let mut changed := false
    for i in [1, 2, 3, 4] do
      let wi := args[i]!
      if wi.isAppOf ``List.set && wi.getAppNumArgs == 4 then
        let idx := wi.getArg! 2
        if !idx.isRawNatLit then
          if let .lit (.natVal n) ← Lean.Meta.whnf idx then
            args := args.set! i (Lean.mkAppN wi.getAppFn (wi.getAppArgs.set! 2 (Lean.mkNatLit n)))
            changed := true
    if changed then
      let p' := Lean.mkAppN p.getAppFn args
      let ty' := Lean.mkAppN ty.getAppFn (sArgs.set! (sArgs.size - 3) p')
      let g ← Lean.Elab.Tactic.getMainGoal
      let g' ← g.replaceLocalDeclDefEq hmId ty'
      Lean.Elab.Tactic.setGoals [g']

private meta def fpLetStep (e : Lean.Expr) : Lean.Elab.Tactic.TacticM Unit := do
  let op := e.getAppArgs[e.getAppNumArgs - 2]!
  let code := op.getAppArgs[op.getAppNumArgs - 2]!
  let tac ← match code.getAppFn.constName? with
    | some ``LeanQbe.T.OpCode.copy => `(tactic| refine (fp_let_copy _ _).mpr ?_)
    | some ``LeanQbe.T.OpCode.add => `(tactic| refine (fp_let_add _ _ _).mpr ?_)
    | some ``LeanQbe.T.OpCode.sub => `(tactic| refine (fp_let_sub _ _ _).mpr ?_)
    | some ``LeanQbe.T.OpCode.mul => `(tactic| refine (fp_let_mul _ _ _).mpr ?_)
    | some ``LeanQbe.T.OpCode.and => `(tactic| refine (fp_let_and _ _ _).mpr ?_)
    | some ``LeanQbe.T.OpCode.xor => `(tactic| refine (fp_let_xor _ _ _).mpr ?_)
    | some ``LeanQbe.T.OpCode.not => `(tactic| refine (fp_let_not _ _).mpr ?_)
    | some ``LeanQbe.T.OpCode.shl => `(tactic| refine (fp_let_shl _ _ _).mpr ?_)
    | some ``LeanQbe.T.OpCode.lshr => `(tactic| refine (fp_let_lshr _ _ _).mpr ?_)
    | some ``LeanQbe.T.OpCode.sext => `(tactic| refine (fp_let_sext _ _ (by decide)).mpr ?_)
    | some ``LeanQbe.T.OpCode.cmp =>
      match (code.getArg! 0).getAppFn.constName? with
      | some ``LeanQbe.T.CmpOp.ult => `(tactic| refine (fp_let_ult _ _ _).mpr ?_)
      | some ``LeanQbe.T.CmpOp.ule => `(tactic| refine (fp_let_ule _ _ _).mpr ?_)
      | some ``LeanQbe.T.CmpOp.ugt => `(tactic| refine (fp_let_ugt _ _ _).mpr ?_)
      | some ``LeanQbe.T.CmpOp.uge => `(tactic| refine (fp_let_uge _ _ _).mpr ?_)
      | some ``LeanQbe.T.CmpOp.eq => `(tactic| refine (fp_let_eq _ _ _).mpr ?_)
      | _ => `(tactic| (
          refine (LeanQbe.T.wp_let_cmp_eq _ _ _ _ _).mpr ?_
          rw [ite_eq_right (fun hc => by revert hc; decide)]))
    | _ => `(tactic| first
        | refine (LeanQbe.T.wp_let_or_eq _ _ _).mpr ?_
        | refine (LeanQbe.T.wp_let_select_eq _ _ _).mpr ?_
        | refine (LeanQbe.T.wp_let_zext_eq _ _ _ _).mpr ⟨by decide, ?_⟩
        | refine (LeanQbe.T.wp_let_trunc_eq _ _ _ _).mpr ⟨by decide, ?_⟩)
  Lean.Elab.Tactic.evalTactic tac

private meta def fpHeadStepOnce : Lean.Elab.Tactic.TacticM Bool :=
  Lean.Elab.Tactic.withMainContext do
    let g ← Lean.Elab.Tactic.getMainGoal
    let ty0 ← Lean.instantiateMVars (← g.getType)
    if ty0.isMData then Lean.Elab.Tactic.setGoals [← g.replaceTargetDefEq ty0.consumeMData]
    let g ← Lean.Elab.Tactic.getMainGoal
    let ty := (← Lean.instantiateMVars (← g.getType)).headBeta
    if !(ty.isAppOf ``LeanQbe.T.wp && ty.getAppNumArgs == 6) then return false
    let e0 := ty.getArg! 4
    if e0.isMData then Lean.Elab.Tactic.setGoals [← g.replaceTargetDefEq
      (Lean.mkAppN ty.getAppFn (ty.getAppArgs.set! 4 e0.consumeMData))]
    let g ← Lean.Elab.Tactic.getMainGoal
    let e := ((← Lean.instantiateMVars (← g.getType)).headBeta.getArg! 4).headBeta
    match e.getAppFn.constName? with
    | some ``LeanQbe.T.Expr.let_ =>
      Lean.Elab.Tactic.evalTactic (← `(tactic| conv => arg 4; arg 1; fp_val_simp))
      let g ← Lean.Elab.Tactic.getMainGoal
      fpLetStep ((← Lean.instantiateMVars (← g.getType)).headBeta.getArg! 4).headBeta
      Lean.Elab.Tactic.evalTactic (← `(tactic| fp_beta)); return true
    | some ``LeanQbe.T.Expr.load =>
      Lean.Elab.Tactic.evalTactic (← `(tactic| conv => arg 4; arg 2; fp_val_simp))
      let g ← Lean.Elab.Tactic.getMainGoal
      let [hl, hk] := (← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels
        ``LeanQbe.T.wp_load_of)).take 2 | return false
      LeanQbe.T.C0Step.memSolve true hl; Lean.Elab.Tactic.setGoals [hk]
      Lean.Elab.Tactic.evalTactic (← `(tactic| fp_beta)); return true
    | some ``LeanQbe.T.Expr.store =>
      Lean.Elab.Tactic.evalTactic (← `(tactic| conv => arg 4; arg 1; fp_val_simp))
      Lean.Elab.Tactic.evalTactic (← `(tactic| conv => arg 4; arg 2; fp_val_simp))
      let g ← Lean.Elab.Tactic.getMainGoal
      let m0 := (← Lean.instantiateMVars (← g.getType)).getArg! 5
      let [hs, hk] := (← g.apply (← Lean.Meta.mkConstWithFreshMVarLevels
        ``LeanQbe.T.wp_store_sep)).take 2 | return false
      Lean.Elab.Tactic.setGoals [hs]
      let okFast ← try
        let some hmE ← findSepMem m0 | throwError "no sep"
        let hmS ← Lean.Elab.Term.exprToSyntax hmE
        Lean.Elab.Tactic.evalTactic (← `(tactic| first
          | refine c0_store_hdr4_0 _ _ _ _ _ _ _ $hmS (by decide)
          | refine c0_store_hdr4_1 _ _ _ _ _ _ _ $hmS (by decide)
          | refine c0_store_hdr4_2 _ _ _ _ _ _ _ $hmS (by decide)
          | refine c0_store_hdr4_3 _ _ _ _ _ _ _ $hmS (by decide)))
        pure (← Lean.Elab.Tactic.getUnsolvedGoals).isEmpty
      catch _ => pure false
      if !okFast then LeanQbe.T.C0Step.memSolve false hs
      Lean.Elab.Tactic.setGoals [hk]
      let mId := Lean.mkIdent `m; let hmId := Lean.mkIdent `hm
      Lean.Elab.Tactic.evalTactic (← `(tactic| intro $mId:ident $hmId:ident))
      Lean.Elab.Tactic.evalTactic (← `(tactic| try dsimp only
        [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm, fp_fst, fp_snd] at $hmId:ident))
      if okFast then
        Lean.Elab.Tactic.withMainContext do
          if let some d := (← Lean.getLCtx).findFromUserName? `hm then
            normHdrIdx d.fvarId
      if !okFast then Lean.Elab.Tactic.evalTactic (← `(tactic| try simp only
        [Std.ExtHashMap.sep_emp] at $hmId:ident))
      clearStaleMem m0; return true
    | some ``LeanQbe.T.Expr.ret =>
      Lean.Elab.Tactic.evalTactic (← `(tactic| (rw [LeanQbe.T.wp_ret]; try simp only
        [LeanQbe.T.vals_cons, LeanQbe.T.vals_nil, LeanQbe.T.Arg.val_var,
          LeanQbe.T.Arg.val_imm, fp_fst, fp_snd]))); return true
    | some ``LeanQbe.T.Expr.jump =>
      Lean.Elab.Tactic.evalTactic (← `(tactic| (rw [LeanQbe.T.wp_jump]; try simp only
        [LeanQbe.T.vals_cons, LeanQbe.T.vals_nil, LeanQbe.T.Arg.val_var,
          LeanQbe.T.Arg.val_imm, fp_fst, fp_snd]))); return true
    | some ``LeanQbe.T.Expr.jnz =>
      Lean.Elab.Tactic.evalTactic (← `(tactic| conv => arg 4; arg 1; fp_val_simp)); return false
    | _ => return false

scoped elab "fp_head_steps" : tactic => do
  for _ in [:400] do
    let gs ← Lean.Elab.Tactic.getUnsolvedGoals
    if gs.isEmpty then break
    let g := gs.head!; Lean.Elab.Tactic.setGoals [g]
    let s ← Lean.Elab.Tactic.saveState
    let ok ← try fpHeadStepOnce catch _ => s.restore; pure false
    Lean.Elab.Tactic.setGoals ((← Lean.Elab.Tactic.getUnsolvedGoals) ++ gs.tail!)
    if !ok then break
  let gs ← Lean.Elab.Tactic.getUnsolvedGoals
  if !gs.isEmpty then
    let g := gs.head!; Lean.Elab.Tactic.setGoals [g]
    try Lean.Elab.Tactic.evalTactic (← `(tactic|
      dsimp only [LeanQbe.T.Arg.val_var, LeanQbe.T.Arg.val_imm, fp_fst, fp_snd]))
    catch _ => pure ()
    Lean.Elab.Tactic.setGoals ((← Lean.Elab.Tactic.getUnsolvedGoals) ++ gs.tail!)

end FullParseInitTactics

namespace FullParseInitHelpers
open FullParseInitSpecs
open scoped FullParseInitTactics
open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.ProofUtil
  LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 3. Bitvector sizing, list/array, and region-peeling helpers -/

theorem fp_align8 {n : Nat} (hn : n + 7 < 2 ^ 64) :
    (BitVec.ofNat 64 n + (7 : BitVec 64)) &&& (~~~(7 : BitVec 64)) =
      BitVec.ofNat 64 (((n + 7) / 8) * 8) := by
  apply BitVec.eq_of_toNat_eq; rw [show (7 : BitVec 64) = BitVec.ofNat 64 7 from rfl, bv_add_ofNat]
  simp only [BitVec.toNat_and, BitVec.toNat_not, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show ((n + 7) / 8) * 8 < 2 ^ 64 by omega),
    show (2 ^ 64 - 1 - 7 % 2 ^ 64) = 2 ^ 64 - 8 from by decide]
  have hd := Nat.and_div_two_pow (a := n + 7) (b := 2 ^ 64 - 8) (n := 3)
  have hr := Nat.and_mod_two_pow (a := n + 7) (b := 2 ^ 64 - 8) (n := 3)
  rw [show (2 ^ 64 - 8) / 2 ^ 3 = 2 ^ 61 - 1 from by decide] at hd
  rw [show (2 ^ 64 - 8) % 2 ^ 3 = 0 from by decide, Nat.and_zero] at hr
  have hq := Nat.and_two_pow_sub_one_eq_mod ((n + 7) / 8) 61; rw [Nat.mod_eq_of_lt (by omega)] at hq
  rw [show (2 ^ 3 : Nat) = 8 from by decide] at hd hr; rw [hq] at hd; omega

theorem fp_and_not1 {x : BitVec 64} :
    (x &&& ~~~(1 : BitVec 64)) = BitVec.ofNat 64 ((x.toNat / 2) * 2) := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  simp only [BitVec.toNat_and, BitVec.toNat_not, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show ((x.toNat / 2) * 2) < 2 ^ 64 by omega),
    show (2 ^ 64 - 1 - (1 : BitVec 64).toNat) = 2 ^ 64 - 2 from by decide]
  have hd := Nat.and_div_two_pow (a := x.toNat) (b := 2 ^ 64 - 2) (n := 1)
  have hr := Nat.and_mod_two_pow (a := x.toNat) (b := 2 ^ 64 - 2) (n := 1)
  rw [show (2 ^ 64 - 2) / 2 ^ 1 = 2 ^ 63 - 1 from by decide] at hd
  rw [show (2 ^ 64 - 2) % 2 ^ 1 = 0 from by decide, Nat.and_zero] at hr
  have hq := Nat.and_two_pow_sub_one_eq_mod (x.toNat / 2) 63; rw [Nat.mod_eq_of_lt (by omega)] at hq
  rw [show (2 ^ 1 : Nat) = 2 from by decide] at hd hr; rw [hq] at hd; omega

theorem fp_shl_sext3 {n : Nat} :
    BitVec.ofNat 64 n <<< (((3 : BitVec 32).signExtend 64).toNat % 64) =
      BitVec.ofNat 64 (8 * n) := by
  have hs : ((3 : BitVec 32).signExtend 64).toNat % 64 = 3 := rfl
  rw [hs]; apply BitVec.eq_of_toNat_eq; simp [Nat.mul_comm]

theorem fp_shl_sext6 {n : Nat} :
    BitVec.ofNat 64 n <<< (((6 : BitVec 32).signExtend 64).toNat % 64) =
      BitVec.ofNat 64 (64 * n) := by
  have hs : ((6 : BitVec 32).signExtend 64).toNat % 64 = 6 := rfl
  rw [hs]; apply BitVec.eq_of_toNat_eq; simp [Nat.shiftLeft_eq, Nat.mul_comm]

theorem fp_shr_sext1 {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n >>> (((1 : BitVec 32).signExtend 64).toNat % 64) =
      BitVec.ofNat 64 (n / 2) := by
  have hs : ((1 : BitVec 32).signExtend 64).toNat % 64 = 1 := rfl
  rw [hs]; apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (by omega : n / 2 < 2 ^ 64)]

theorem fp_shr_sext3 {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n >>> (((3 : BitVec 32).signExtend 64).toNat % 64) =
      BitVec.ofNat 64 (n / 8) := by
  have hs : ((3 : BitVec 32).signExtend 64).toNat % 64 = 3 := rfl
  rw [hs]; apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (by omega : n / 8 < 2 ^ 64)]

theorem fp_shr_sext4 {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n >>> (((4 : BitVec 32).signExtend 64).toNat % 64) =
      BitVec.ofNat 64 (n / 16) := by
  have hs : ((4 : BitVec 32).signExtend 64).toNat % 64 = 4 := rfl
  rw [hs]; apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (by omega : n / 16 < 2 ^ 64)]

theorem fp_shr_sext5 {n : Nat} (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 n >>> (((5 : BitVec 32).signExtend 64).toNat % 64) =
      BitVec.ofNat 64 (n / 32) := by
  have hs : ((5 : BitVec 32).signExtend 64).toNat % 64 = 5 := rfl
  rw [hs]; apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (by omega : n / 32 < 2 ^ 64)]

theorem fp_vb_eq {mx : Nat} (hmx : mx < 2 * dimacsBound) :
    (BitVec.ofNat 64 mx <<< (((1 : BitVec 32).signExtend 64).toNat % 64) + 7) &&& ~~~7 =
      BitVec.ofNat 64 (valsBytes mx) := by
  unfold dimacsBound at hmx; rw [Kissat.bv_shl_sext1, fp_align8 (n := 2 * mx) (by omega)]; rfl

theorem fp_mb_eq {mx : Nat} (hmx : mx < 2 * dimacsBound) :
    (BitVec.ofNat 64 mx + (7 : BitVec 64)) &&& ~~~(7 : BitVec 64) =
      BitVec.ofNat 64 (markBytes mx) := by
  unfold dimacsBound at hmx; rw [fp_align8 (n := mx) (by omega)]; rfl

theorem fp_ub_eq {mx : Nat} (hmx : mx < 2 * dimacsBound) :
    ((BitVec.ofNat 64 mx + 1) <<< (((2 : BitVec 32).signExtend 64).toNat % 64) + 7) &&& ~~~7 =
      BitVec.ofNat 64 (u32FullBytes mx) := by
  unfold dimacsBound at hmx
  rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, bv_add_ofNat,
    Kissat.bv_shl_sext2, fp_align8 (n := 4 * (mx + 1)) (by omega)]
  rfl

theorem fp_mul_nat (n k : Nat) :
    BitVec.ofNat 64 n * BitVec.ofNat 64 k = BitVec.ofNat 64 (n * k) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, Nat.mul_mod]

theorem shiftDownCnf_empty : (shiftDownCnf CNF.empty : CNF Nat) = CNF.empty := by
  simp [shiftDownCnf, CNF.empty]

theorem array64_to_hdrTail4 {hdr : BitVec 64} {ws : List (BitVec 64)} {R : Mem 64 → Prop}
    {m : Mem 64} (hw : ws.length = 140) (hm : (array64 (hdr + 32) ws ⋆ R) m) :
    (hdrTail4 hdr (ws.take 35) ((ws.drop 35).take 35) ((ws.drop 70).take 35)
      ((ws.drop 105).take 35) ⋆ R) m := by
  have h1 : (ws.take 35).length = 35 := by simp [hw]
  have h2 : ((ws.drop 35).take 35).length = 35 := by simp [hw]
  have h3 : ((ws.drop 70).take 35).length = 35 := by simp [hw]
  have h4 : ((ws.drop 105).take 35).length = 35 := by simp [hw]
  have hsp : ws.take 35 ++ (ws.drop 35).take 35 ++ (ws.drop 70).take 35 ++
      (ws.drop 105).take 35 = ws := by
    have hd1 : (ws.drop 35).drop 35 = ws.drop 70 := by rw [List.drop_drop]
    have hd2 : (ws.drop 70).drop 35 = ws.drop 105 := by rw [List.drop_drop]
    have ht4 : (ws.drop 105).take 35 = ws.drop 105 := List.take_of_length_le (by simp [hw])
    rw [ht4]; simp only [List.append_assoc]
    rw [← hd2, List.take_append_drop, ← hd1, List.take_append_drop, List.take_append_drop]
  rw [hdrTail4_eq_array64 h1 h2 h3 h4, hsp]; exact hm

theorem append4_getElem?_0 {α : Type} {w0 w1 w2 w3 : List α} (h0 : w0.length = 35)
    {i : Nat} (hi : i < 35) : (w0 ++ w1 ++ w2 ++ w3)[i]? = w0[i]? := by
  simp only [List.append_assoc]
  exact List.getElem?_append_left (by omega)

theorem append4_getElem?_1 {α : Type} {w0 w1 w2 w3 : List α} (h0 : w0.length = 35)
    (h1 : w1.length = 35) {i : Nat} (hi0 : 35 ≤ i) (hi1 : i < 70) :
    (w0 ++ w1 ++ w2 ++ w3)[i]? = w1[i - 35]? := by
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by omega), h0, List.getElem?_append_left (by omega)]

theorem append4_getElem?_2 {α : Type} {w0 w1 w2 w3 : List α} (h0 : w0.length = 35)
    (h1 : w1.length = 35) (h2 : w2.length = 35) {i : Nat} (hi0 : 70 ≤ i) (hi1 : i < 105) :
    (w0 ++ w1 ++ w2 ++ w3)[i]? = w2[i - 70]? := by
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by omega), h0, List.getElem?_append_right (by omega), h1,
    List.getElem?_append_left (by omega), show i - 35 - 35 = i - 70 by omega]

theorem append4_getElem?_3 {α : Type} {w0 w1 w2 w3 : List α} (h0 : w0.length = 35)
    (h1 : w1.length = 35) (h2 : w2.length = 35) {i : Nat} (hi0 : 105 ≤ i) :
    (w0 ++ w1 ++ w2 ++ w3)[i]? = w3[i - 105]? := by
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (by omega), h0, List.getElem?_append_right (by omega), h1,
    List.getElem?_append_right (by omega), h2, show i - 35 - 35 - 35 = i - 105 by omega]

theorem drop_take_getElem? {α : Type} (xs : List α) (off n i : Nat) (hi : i < n) :
    ((xs.drop off).take n)[i]? = xs[off + i]? := by
  rw [List.getElem?_take_of_lt hi, List.getElem?_drop]

theorem list_eq_replicate_of_forall {α : Type} {xs : List α} {n : Nat} {x : α}
    (hlen : xs.length = n) (hall : ∀ i < n, xs[i]? = some x) : xs = List.replicate n x := by
  apply List.ext_getElem (by simp [hlen]); intro i hi _
  have h1 := hall i (by omega)
  rw [List.getElem?_eq_getElem (by omega)] at h1; simpa using h1

theorem wvec_eq_replicate_of_pairs {xs : List (BitVec 32)} {n : Nat}
    (hlen : xs.length = 2 * n)
    (hp : ∀ j < n, xs[2 * j]? = some 0#32 ∧ xs[2 * j + 1]? = some 0#32) :
    xs = List.replicate (2 * n) 0#32 := by
  refine list_eq_replicate_of_forall hlen fun i hi => ?_
  have hdiv : i / 2 < n := by omega
  have hid := Nat.div_add_mod i 2
  rcases Nat.mod_two_eq_zero_or_one i with hm | hm
  · have := (hp (i / 2) hdiv).1; rwa [show 2 * (i / 2) = i by omega] at this
  · have := (hp (i / 2) hdiv).2; rwa [show 2 * (i / 2) + 1 = i by omega] at this

theorem last_learned_getD_eq {xs : List (BitVec 32)}
    (h : ∀ j < 16, xs[j]? = some 0xFFFFFFFF#32) :
    ∀ i < 16, xs[i]?.getD 0#32 = 0xFFFFFFFF#32 := fun i hi => by
  rw [h i hi, Option.getD_some]

theorem last_learned_getD_ff_of_zero {xs : List (BitVec 32)}
    (h : ∀ i < 16, xs[i]?.getD 0#32 = 0xFFFFFFFF#32) :
    ∀ i < 8, xs[i]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 := fun i hi => by
  have hi16 := h i (by omega)
  cases hx : xs[i]? with
  | none => rfl
  | some v => rw [hx, Option.getD_some] at hi16; simp [hi16]

theorem bv64_shl1_eq_2mul {n : Nat} (hn : 2 * n < 2 ^ 64) :
    (BitVec.ofNat 64 n <<< (((1 : BitVec 32).signExtend 64).toNat % 64)).toNat = 2 * n := by
  rw [show ((1 : BitVec 32).signExtend 64).toNat % 64 = 1 from rfl]
  simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega

theorem bv64_mul_nat3 (x : BitVec 64) (k : Nat) :
    x * BitVec.ofNat 64 k = BitVec.ofNat 64 (x.toNat * k) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul, Nat.mul_mod]

theorem bv64_shl2_nat {n : Nat} (_hn : 4 * n < 2 ^ 64) :
    BitVec.ofNat 64 n <<< (((2 : BitVec 32).signExtend 64).toNat % 64) =
      BitVec.ofNat 64 (4 * n) := by
  simpa [show ((2 : BitVec 32).signExtend 64).toNat % 64 = 2 from rfl, Nat.mul_comm] using
    Kissat.bv_shl_sext2 (n := n)

theorem bv64_shl2_val {x : BitVec 64} (hx : 4 * x.toNat < 2 ^ 64) :
    x <<< (((2 : BitVec 32).signExtend 64).toNat % 64) = BitVec.ofNat 64 (4 * x.toNat) := by
  simpa [bv_ofNat_toNat_eq x] using bv64_shl2_nat hx

theorem sep_push {P Q : Mem 64 → Prop} {m1 m2 m : Mem 64} (hu : m1.union m2 = m)
    (hd : m1.inter m2 = ∅) (hp : P m1) (hq : Q m2) : (P ⋆ Q) m :=
  ⟨m1, m2, hu, hd, hp, hq⟩

theorem reg_peel {a b : BitVec 64} {n1 n2 n : Nat} {m : Mem 64} (hm : region a n m)
    (hb : a + BitVec.ofNat 64 n1 = b := by rfl) (hn : n = n1 + n2 := by omega)
    (hle : n1 + n2 ≤ 2 ^ 64 := by omega) : (region a n1 ⋆ region b n2) m := by
  subst hb hn
  rwa [← region_merge_eq (a := a) (n1 := n1) (n2 := n2) (n := n1 + n2) rfl hle] at hm

theorem reg_pad_i8 {a : BitVec 64} (k : Nat) {n : Nat} {m : Mem 64} (hm : region a n m)
    (hk : k ≤ n := by omega) (hle : n ≤ 2 ^ 64 := by omega) :
    ∃ xs : List (BitVec 8), xs.length = k ∧
      (array (t := i8) a xs ⋆ region (a + BitVec.ofNat 64 k) (n - k)) m := by
  obtain ⟨m1, m2, hu, hd, h1, h2⟩ := reg_peel (n1 := k) (n2 := n - k) hm
  obtain ⟨xs, h, ha⟩ := region_to_array_i8 k (by omega) h1
  exact ⟨xs, h, m1, m2, hu, hd, ha, h2⟩

theorem reg_pad_i32 {a : BitVec 64} (k : Nat) {n : Nat} {m : Mem 64} (hm : region a n m)
    (hk : 4 * k ≤ n := by omega) (hle : n ≤ 2 ^ 64 := by omega) :
    ∃ xs : List (BitVec 32), xs.length = k ∧
      (array (t := i32) a xs ⋆ region (a + BitVec.ofNat 64 (4 * k)) (n - 4 * k)) m := by
  obtain ⟨m1, m2, hu, hd, h1, h2⟩ := reg_peel (n1 := 4 * k) (n2 := n - 4 * k) hm
  obtain ⟨xs, h, ha⟩ := region_to_array_i32 k (by omega) h1
  exact ⟨xs, h, m1, m2, hu, hd, ha, h2⟩

theorem peel_step_i8 {A Q : Mem 64 → Prop} {a b : BitVec 64} (k n1 n2 n : Nat)
    {m : Mem 64} (hm : ((A ⋆ Q) ⋆ region a n) m)
    (hb : a + BitVec.ofNat 64 n1 = b := by rfl) (hn : n = n1 + n2 := by omega)
    (hk : k ≤ n1 := by omega) (hle : n1 + n2 ≤ 2 ^ 64 := by omega) :
    ∃ xs : List (BitVec 8), xs.length = k ∧
      (((A ⋆ array (t := i8) a xs) ⋆ (Q ⋆ region (a + BitVec.ofNat 64 k) (n1 - k))) ⋆
        region b n2) m := by
  obtain ⟨m0, mr, hu0, hd0, hp, hreg⟩ := hm
  obtain ⟨m1, m2, hu1, hd1, r1, r2⟩ := reg_peel (b := b) (n1 := n1) (n2 := n2) hreg hb hn hle
  obtain ⟨xs, hxl, ax⟩ := reg_pad_i8 k r1 hk (by omega)
  exact ⟨xs, hxl, sep_ac (sep_push hu0 hd0 hp (sep_push hu1 hd1 ax r2))⟩

theorem peel_step_i32 {A Q : Mem 64 → Prop} {a b : BitVec 64} (k n1 n2 n : Nat)
    {m : Mem 64} (hm : ((A ⋆ Q) ⋆ region a n) m)
    (hb : a + BitVec.ofNat 64 n1 = b := by rfl) (hn : n = n1 + n2 := by omega)
    (hk : 4 * k ≤ n1 := by omega) (hle : n1 + n2 ≤ 2 ^ 64 := by omega) :
    ∃ xs : List (BitVec 32), xs.length = k ∧
      (((A ⋆ array (t := i32) a xs) ⋆ (Q ⋆ region (a + BitVec.ofNat 64 (4 * k)) (n1 - 4 * k))) ⋆
        region b n2) m := by
  obtain ⟨m0, mr, hu0, hd0, hp, hreg⟩ := hm
  obtain ⟨m1, m2, hu1, hd1, r1, r2⟩ := reg_peel (b := b) (n1 := n1) (n2 := n2) hreg hb hn hle
  obtain ⟨xs, hxl, ax⟩ := reg_pad_i32 k r1 hk (by omega)
  exact ⟨xs, hxl, sep_ac (sep_push hu0 hd0 hp (sep_push hu1 hd1 ax r2))⟩

theorem peel_step_exact_i32 {A : Mem 64 → Prop} {a b : BitVec 64} (k n2 n : Nat)
    {m : Mem 64} (hm : (A ⋆ region a n) m)
    (hb : a + BitVec.ofNat 64 (4 * k) = b := by rfl) (hn : n = 4 * k + n2 := by omega)
    (hle : 4 * k + n2 ≤ 2 ^ 64 := by omega) :
    ∃ xs : List (BitVec 32), xs.length = k ∧ ((A ⋆ array (t := i32) a xs) ⋆ region b n2) m := by
  obtain ⟨m0, mr, hu0, hd0, hp, hreg⟩ := hm
  obtain ⟨m1, m2, hu1, hd1, r1, r2⟩ :=
    reg_peel (b := b) (n1 := 4 * k) (n2 := n2) hreg hb hn hle
  obtain ⟨xs, hxl, ax⟩ := region_to_array_i32 k (by omega) r1
  exact ⟨xs, hxl, sep_ac (sep_push hu0 hd0 hp (sep_push hu1 hd1 ax r2))⟩

theorem peel_step_exact_i64 {A : Mem 64 → Prop} {a b : BitVec 64} (k n2 n : Nat)
    {m : Mem 64} (hm : (A ⋆ region a n) m)
    (hb : a + BitVec.ofNat 64 (8 * k) = b := by rfl) (hn : n = 8 * k + n2 := by omega)
    (hle : 8 * k + n2 ≤ 2 ^ 64 := by omega) :
    ∃ xs : List (BitVec 64), xs.length = k ∧ ((A ⋆ array64 a xs) ⋆ region b n2) m := by
  obtain ⟨m0, mr, hu0, hd0, hp, hreg⟩ := hm
  obtain ⟨m1, m2, hu1, hd1, r1, r2⟩ :=
    reg_peel (b := b) (n1 := 8 * k) (n2 := n2) hreg hb hn hle
  obtain ⟨xs, hxl, ax⟩ := region_to_array64 k (by omega) r1
  exact ⟨xs, hxl, sep_ac (sep_push hu0 hd0 hp (sep_push hu1 hd1 ax r2))⟩

end FullParseInitHelpers

end LeanQbe.T.Examples.Kissat.Full
