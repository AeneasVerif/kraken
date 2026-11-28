/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Logic.SpecTable
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Header
public import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts2
public import Kraken.Mem
public import Kraken.Separation

/-!
# Canonical XFree-by-Construction Contract Combinators & Framing Algebra (`Proof.Spec.Core`)

Pure specification-level combinators (zero theorems, zero tactics, zero `meta import`, zero
`C0Step` import):
1. `ExtFrame`, `CorePres`, `ScratchField` (`87` `FullScratch` fields), and `ScratchModifies`.
2. Five XFree-by-construction contract combinators: `PureContract`, `FnContract`, `FullContract`,
   `M6HdrContract`, `FullCfgContract`, and `M6HdrCfgContract` (with `extraArgs` after `h`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Spec

open LeanQbe.T
open Kraken.Bedrock2.Test

/-! ## 1. `M6HdrExt` & `FullScratch` Framing Algebras -/

/-- Preservation policy for the `288`-word `M6HdrExt` prefix (`c.hdr - 2304`). -/
inductive ExtFrame where
  | preserveAll
  | w2aOnly
  | w2bOnly
  | initPres
  | any
  deriving DecidableEq, Repr

@[expose] def ExtFrame.rel : ExtFrame → List (BitVec 64) → List (BitVec 64) → Prop
  | .preserveAll, ext, ext' => ext' = ext
  | .w2aOnly,     ext, ext' => M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2bPres ext ext'
  | .w2bOnly,     ext, ext' => M6HdrExtInitOk ext → M6HdrExtInitOk ext' ∧ M6ExtW2aPres ext ext'
  | .initPres,    ext, ext' => M6HdrExtInitOk ext → M6HdrExtInitOk ext'
  | .any,         _,   _    => True

/-- Shorthand for core-preserving heuristic/tier/walk/config functions. -/
@[expose] def CorePres (s s' : FullState) : Prop := s'.core = s.core

/-- Named descriptor for every mutable `FullScratch` field (`87` fields total). -/
inductive ScratchField where
  | heap_len | scinc
  | rel_period | rel_limit | rel_wait | rel_u | rel_v | rel_trigger
  | conflicts | learned_lits | min_removed | delayed_len
  | stable | switched | mode_count | mode_confl_lim | mode_tick_lim | mode_saved_ticks
  | search_ticks
  | q_first | q_last | q_search_idx | q_search_stamp | q_cur_stamp
  | target_assigned | best_assigned | rephase_limit | rephased
  | reduce_limit | reductions | tier1 | tier2 | restarts | restart_limit
  | ema_fast_biased | ema_fast_exp | ema_slow_biased | ema_slow_exp
  | extend_len | rng_state | chrono_levels | otfs_cnt | eager_sub_cnt
  | probe_limit | probings | elim_limit | eliminations | elim_bound | iterating
  | hbr_cnt | trans_cnt | viv_cnt | subst_cnt | cong_cnt | sweep_cnt
  | bve_cnt | bce_cnt | bva_cnt | walk_cnt_stat | fwd_sub_cnt | fwd_str_cnt
  | ant_sz | res_sz
  | walk_vals | phases | phases_target | phases_best | walk_best
  | heap | pos | shrink_stk | q_prev | q_next | q_stamp
  | wsort | work_stk1 | work_stk2 | tarjan_mark | tarjan_reach
  | score | sim_sig | glue_used | last_learned | delayed | red_refs | extend_stk | scratch_buf
  deriving DecidableEq, Repr

/-- Lean value type of each `ScratchField`. -/
@[expose] def ScratchField.ty : ScratchField → Type
  | .heap_len | .delayed_len | .extend_len => Nat
  | .walk_vals | .phases | .phases_target | .phases_best | .walk_best => List (BitVec 8)
  | .score | .sim_sig => List (BitVec 64)
  | .heap | .pos | .shrink_stk | .q_prev | .q_next | .q_stamp | .wsort | .work_stk1
  | .work_stk2 | .tarjan_mark | .tarjan_reach | .glue_used | .last_learned | .delayed
  | .red_refs | .extend_stk | .scratch_buf => List (BitVec 32)
  | _ => BitVec 64

/-- Field-indexed accessor on `FullScratch`. -/
@[expose] def FullScratch.getField (sc : FullScratch) : (f : ScratchField) → f.ty
  | .heap_len => sc.heap_len
  | .scinc => sc.scinc
  | .rel_period => sc.rel_period
  | .rel_limit => sc.rel_limit
  | .rel_wait => sc.rel_wait
  | .rel_u => sc.rel_u
  | .rel_v => sc.rel_v
  | .rel_trigger => sc.rel_trigger
  | .conflicts => sc.conflicts
  | .learned_lits => sc.learned_lits
  | .min_removed => sc.min_removed
  | .delayed_len => sc.delayed_len
  | .stable => sc.stable
  | .switched => sc.switched
  | .mode_count => sc.mode_count
  | .mode_confl_lim => sc.mode_confl_lim
  | .mode_tick_lim => sc.mode_tick_lim
  | .mode_saved_ticks => sc.mode_saved_ticks
  | .search_ticks => sc.search_ticks
  | .q_first => sc.q_first
  | .q_last => sc.q_last
  | .q_search_idx => sc.q_search_idx
  | .q_search_stamp => sc.q_search_stamp
  | .q_cur_stamp => sc.q_cur_stamp
  | .target_assigned => sc.target_assigned
  | .best_assigned => sc.best_assigned
  | .rephase_limit => sc.rephase_limit
  | .rephased => sc.rephased
  | .reduce_limit => sc.reduce_limit
  | .reductions => sc.reductions
  | .tier1 => sc.tier1
  | .tier2 => sc.tier2
  | .restarts => sc.restarts
  | .restart_limit => sc.restart_limit
  | .ema_fast_biased => sc.ema_fast_biased
  | .ema_fast_exp => sc.ema_fast_exp
  | .ema_slow_biased => sc.ema_slow_biased
  | .ema_slow_exp => sc.ema_slow_exp
  | .extend_len => sc.extend_len
  | .rng_state => sc.rng_state
  | .chrono_levels => sc.chrono_levels
  | .otfs_cnt => sc.otfs_cnt
  | .eager_sub_cnt => sc.eager_sub_cnt
  | .probe_limit => sc.probe_limit
  | .probings => sc.probings
  | .elim_limit => sc.elim_limit
  | .eliminations => sc.eliminations
  | .elim_bound => sc.elim_bound
  | .iterating => sc.iterating
  | .hbr_cnt => sc.hbr_cnt
  | .trans_cnt => sc.trans_cnt
  | .viv_cnt => sc.viv_cnt
  | .subst_cnt => sc.subst_cnt
  | .cong_cnt => sc.cong_cnt
  | .sweep_cnt => sc.sweep_cnt
  | .bve_cnt => sc.bve_cnt
  | .bce_cnt => sc.bce_cnt
  | .bva_cnt => sc.bva_cnt
  | .walk_cnt_stat => sc.walk_cnt_stat
  | .fwd_sub_cnt => sc.fwd_sub_cnt
  | .fwd_str_cnt => sc.fwd_str_cnt
  | .ant_sz => sc.ant_sz
  | .res_sz => sc.res_sz
  | .walk_vals => sc.walk_vals
  | .phases => sc.phases
  | .phases_target => sc.phases_target
  | .phases_best => sc.phases_best
  | .walk_best => sc.walk_best
  | .heap => sc.heap
  | .pos => sc.pos
  | .shrink_stk => sc.shrink_stk
  | .q_prev => sc.q_prev
  | .q_next => sc.q_next
  | .q_stamp => sc.q_stamp
  | .wsort => sc.wsort
  | .work_stk1 => sc.work_stk1
  | .work_stk2 => sc.work_stk2
  | .tarjan_mark => sc.tarjan_mark
  | .tarjan_reach => sc.tarjan_reach
  | .score => sc.score
  | .sim_sig => sc.sim_sig
  | .glue_used => sc.glue_used
  | .last_learned => sc.last_learned
  | .delayed => sc.delayed
  | .red_refs => sc.red_refs
  | .extend_stk => sc.extend_stk
  | .scratch_buf => sc.scratch_buf

/-- `s'.scratch` agrees with `s.scratch` on every field not listed in `mod`. -/
@[expose] def ScratchModifies (mod : List ScratchField) (s s' : FullState) : Prop :=
  ∀ f : ScratchField, f ∉ mod → s'.scratch.getField f = s.scratch.getField f

@[expose] def ScratchModifies.none (s s' : FullState) : Prop :=
  s'.scratch = s.scratch

@[expose] def ScratchModifies.extPres (s s' : FullState) : Prop :=
  s'.scratch.last_learned = s.scratch.last_learned ∧
  s'.scratch.extend_len = s.scratch.extend_len

@[expose] def ScratchModifies.probePres (s s' : FullState) : Prop :=
  ScratchModifies.extPres s s' ∧
  s'.scratch.work_stk1 = s.scratch.work_stk1 ∧
  s'.scratch.work_stk2 = s.scratch.work_stk2 ∧
  s'.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
  s'.scratch.scratch_buf = s.scratch.scratch_buf ∧
  s'.scratch.ant_sz = s.scratch.ant_sz ∧
  s'.scratch.res_sz = s.scratch.res_sz ∧
  s'.scratch.sim_sig = s.scratch.sim_sig

@[expose] def ScratchModifies.hdrPres (s s' : FullState) : Prop :=
  ScratchModifies.probePres s s' ∧
  s'.scratch.delayed = s.scratch.delayed ∧
  s'.scratch.delayed_len = s.scratch.delayed_len

/-! ## 2. The Five XFree-by-Construction Contract Combinators -/

/-- 1. Pure zero-memory contract (`Float64`, pure bitops, `Config` masks, sizing math). -/
structure PureContract (as rs : List Ty) where
  pre  : Tup Val as → Prop := fun _ => True
  post : Tup Val as → Tup Val rs → Prop

@[expose] def PureContract.toSpec {as rs} (K : PureContract as rs) : Spec as rs :=
  fun args m Q _ => K.pre args ∧ ∀ res, K.post args res → Q res m

@[expose] def PureContract.det {as rs} (f : Tup Val as → Tup Val rs) : Spec as rs :=
  PureContract.toSpec { post := fun a r => r = f a }

/-- 2. General frame-polymorphic raw-memory / custom-footprint contract (`bytes`, `region`,
`array64`, `K6Mem`, `K6BufMem`, `init_ptrs`, `init_arenas`, `solve_bytes`).
Splits pure `post` from spatial `postMem` so `∃` never appears inside `⋆`. -/
structure FnContract (as rs : List Ty) (W W' : Type) where
  pre     : Tup Val as → W → Prop
  mem     : Tup Val as → W → (Mem 64 → Prop)
  post    : Tup Val as → W → Tup Val rs → W' → Prop
  postMem : Tup Val as → W → Tup Val rs → W' → (Mem 64 → Prop)

@[expose] def FnContract.toSpec {as rs W W'} (K : FnContract as rs W W') : Spec as rs :=
  fun args m Q _ =>
    ∃ (w : W) (R : Mem 64 → Prop),
      K.pre args w ∧ (K.mem args w ⋆ R) m ∧
      ∀ res w' m', K.post args w res w' → (K.postMem args w res w' ⋆ R) m' → Q res m'

/-- 3. Fixed-`FullCfg`, `FullMem`-threaded solver contract.
Enforces `h = c.hdr` and `s.LengthsOk c` / `s'.LengthsOk c` automatically; lifts to
`FullM6HdrMem` for free by framing `m6ExtMem` into `R`. -/
structure FullContract (extraArgs rs : List Ty) (W : Type) where
  pre  : FullCfg → FullState → Tup Val extraArgs → W → Prop
  post : FullCfg → FullState → Tup Val extraArgs → W → Tup Val rs → FullState → Prop

@[expose] def FullContract.toSpec {extraArgs rs W} (K : FullContract extraArgs rs W) :
    Spec (i64 :: extraArgs) rs :=
  fun (h, args) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (w : W) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ K.pre c s args w ∧ (FullMem c s ⋆ R) m ∧
      ∀ res s' m', s'.LengthsOk c → K.post c s args w res s' →
        (FullMem c s' ⋆ R) m' → Q res m'

/-- 4. Fixed-`FullCfg`, `FullM6HdrMem`-threaded contract (for fns touching `M6HdrExt`). -/
structure M6HdrContract (extraArgs rs : List Ty) (W : Type) where
  extFrame : ExtFrame := .any
  pre      : FullCfg → List (BitVec 64) → FullState → Tup Val extraArgs → W → Prop
  post     : FullCfg → List (BitVec 64) → FullState → Tup Val extraArgs → W →
             Tup Val rs → List (BitVec 64) → FullState → Prop

@[expose] def M6HdrContract.toSpec {extraArgs rs W} (K : M6HdrContract extraArgs rs W) :
    Spec (i64 :: extraArgs) rs :=
  fun (h, args) m Q _ =>
    ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (w : W) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
      K.pre c ext s args w ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ res ext' s' m',
        M6HdrExtOk ext' → K.extFrame.rel ext ext' → s'.LengthsOk c →
        K.post c ext s args w res ext' s' →
        (FullM6HdrMem c ext' s' ⋆ R) m' → Q res m'

/-- 5a. Cfg-updating `FullMem` contract (`FullCfgCompat c c'`). -/
structure FullCfgContract (extraArgs rs : List Ty) (W : Type) where
  pre  : FullCfg → FullState → Tup Val extraArgs → W → Prop
  post : FullCfg → FullState → Tup Val extraArgs → W → Tup Val rs → FullCfg → FullState → Prop

@[expose] def FullCfgContract.toSpec {extraArgs rs W} (K : FullCfgContract extraArgs rs W) :
    Spec (i64 :: extraArgs) rs :=
  fun (h, args) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (w : W) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ K.pre c s args w ∧ (FullMem c s ⋆ R) m ∧
      ∀ res c' s' m',
        FullCfgCompat c c' → s'.LengthsOk c' → K.post c s args w res c' s' →
        (FullMem c' s' ⋆ R) m' → Q res m'

/-- 5b. Cfg-updating `FullM6HdrMem` contract. -/
structure M6HdrCfgContract (extraArgs rs : List Ty) (W : Type) where
  extFrame : ExtFrame := .any
  pre      : FullCfg → List (BitVec 64) → FullState → Tup Val extraArgs → W → Prop
  post     : FullCfg → List (BitVec 64) → FullState → Tup Val extraArgs → W →
             Tup Val rs → FullCfg → List (BitVec 64) → FullState → Prop

@[expose] def M6HdrCfgContract.toSpec {extraArgs rs W} (K : M6HdrCfgContract extraArgs rs W) :
    Spec (i64 :: extraArgs) rs :=
  fun (h, args) m Q _ =>
    ∃ (c : FullCfg) (ext : List (BitVec 64)) (s : FullState) (w : W) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullM6HdrCfgOk c ∧ M6HdrExtOk ext ∧ s.LengthsOk c ∧
      K.pre c ext s args w ∧ (FullM6HdrMem c ext s ⋆ R) m ∧
      ∀ res c' ext' s' m',
        FullCfgCompat c c' → FullM6HdrCfgOk c' → M6HdrExtOk ext' →
        K.extFrame.rel ext ext' → s'.LengthsOk c' →
        K.post c ext s args w res c' ext' s' →
        (FullM6HdrMem c' ext' s' ⋆ R) m' → Q res m'

end LeanQbe.T.Examples.Kissat.Proof.Spec
