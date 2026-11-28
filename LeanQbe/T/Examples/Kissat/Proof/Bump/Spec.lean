/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Spec.Core
public import LeanQbe.T.Logic.CanonicalEnv

/-!
# Canonical Specifications for `Kissat.Src.Bump` (`9` C0 Functions)

Pure specifications only: `0` theorems, `0` tactics, `0` `deps`, `0` cross-subsystem `Spec` imports.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.Bump.Spec

open LeanQbe.T
open LeanQbe.T.Examples.Kissat.Proof.Spec
open Kraken.Bedrock2.Test

/-- VMTF doubly-linked queue scratch fields modified by `full_queue_mtf`. -/
@[expose] def queueFields : List ScratchField :=
  [ .q_prev, .q_next, .q_stamp, .q_first, .q_last, .q_cur_stamp,
    .q_search_idx, .q_search_stamp ]

/-- `AgreesExcept` mask for `full_sort_ana_qs_m6` (`core.repr`, `work_stk1`, `wsort`,
`scratch_buf`). -/
@[expose] def sortAnaQsMask (s : FullState) : FullState :=
  { core := { s.core with repr := [] }
    scratch := { s.scratch with work_stk1 := [], wsort := [], scratch_buf := [] } }

/-- `AgreesExcept` core mask for `full_bump_analyzed_mode_fid` (`mrk`, `min_clr_len`, `repr`). -/
@[expose] def bumpAnalyzedCoreMask (k : FullCoreState) : FullCoreState :=
  { k with mrk := [], min_clr_len := 0, repr := [] }

/-- Mode-dependent precondition for `full_bump_analyzed_mode_fid`. -/
@[expose] def FullBumpPre (allow_reasons : Bool) (c : FullCfg) (s : FullState) : Prop :=
  if allow_reasons then FullAnaMarksCov c s
  else s.core.min_clr_len ≤ s.core.cur_vars ∧
    ∀ k < s.core.min_clr_len, (s.scratch.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars

/-- Shared contract for `full_rescale_m6(h)`, `full_rescale(h)`, and `full_bump_decay(h)`. -/
@[expose] def rescaleSpec : Spec [i64] [] :=
  FullContract.toSpec (W := Unit)
    { pre := fun _ _ () () => True
      post := fun _ s () () () s' =>
        CorePres s s' ∧ ScratchModifies [.score, .scinc] s s' }

/-- `full_bump_var(h, v)`: increments EVSIDS score, sifts heap when stable, and rescales on
overflow. -/
@[expose] def bumpVarSpec : Spec [i64, i32] [] :=
  FullContract.toSpec (W := Unit)
    { pre := fun _ _ _ () => True
      post := fun _ s _ () () s' =>
        CorePres s s' ∧ ScratchModifies [.score, .scinc, .heap, .pos] s s' }

/-- `full_queue_renumber(h)`: reassigns monotonic VMTF stamps along the queue. -/
@[expose] def queueRenumberSpec : Spec [i64] [] :=
  FullContract.toSpec (W := Unit)
    { pre := fun _ _ () () => True
      post := fun _ s () () () s' =>
        CorePres s s' ∧ ScratchModifies [.q_stamp, .q_cur_stamp, .q_search_stamp] s s' }

/-- `full_queue_mtf(h, v)`: moves variable `v` to the back of the VMTF queue. -/
@[expose] def queueMtfSpec : Spec [i64, i32] [] :=
  FullContract.toSpec (W := Unit)
    { pre := fun _ _ _ () => True
      post := fun _ s _ () () s' => CorePres s s' ∧ ScratchModifies queueFields s s' }

/-- `full_ana_sift_m6(qs, ana, cv, start, n)`: raw 2-array heap sift-down preserving permutation
and `< cv` bounds on `ana[0 ..< n)`. -/
@[expose] def anaSiftSpec : Spec [i64, i64, i64, i64, i64] [] :=
  FnContract.toSpec (W := List (BitVec 32) × List (BitVec 32)) (W' := List (BitVec 32))
    { pre := fun (_, _, cv, start, n, ()) (qs, ana) =>
        cv.toNat ≤ qs.length ∧ start.toNat ≤ n.toNat ∧ n.toNat ≤ ana.length ∧
        n.toNat < 2 ^ 62 ∧ ∀ k < n.toNat, (ana[k]?.getD 0#32).toNat < cv.toNat
      mem := fun (qs_ptr, ana_ptr, _, _, _, ()) (qs, ana) =>
        array (t := i32) qs_ptr qs ⋆ array (t := i32) ana_ptr ana
      post := fun (_, _, cv, _, n, ()) (_, ana) () ana' =>
        ana'.length = ana.length ∧ (ana'.take n.toNat).Perm (ana.take n.toNat) ∧
        (∀ k, n.toNat ≤ k → ana'[k]? = ana[k]?) ∧
        ∀ k < n.toNat, (ana'[k]?.getD 0#32).toNat < cv.toNat
      postMem := fun (qs_ptr, ana_ptr, _, _, _, ()) (qs, _) () ana' =>
        array (t := i32) qs_ptr qs ⋆ array (t := i32) ana_ptr ana' }

/-- `full_sort_ana_qs_m6(h, n)`: sorts `work_stk1[0 ..< n)` by VMTF queue stamp. -/
@[expose] def sortAnaQsSpec : Spec [i64, i64] [] :=
  FullContract.toSpec (W := Unit)
    { pre := fun _ s (n, ()) () =>
        n.toNat ≤ s.core.cur_vars ∧
        ∀ k < n.toNat, (s.scratch.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars
      post := fun _ s (n, ()) () () s' =>
        AgreesExcept sortAnaQsMask s s' ∧
        (s'.scratch.work_stk1.take n.toNat).Perm (s.scratch.work_stk1.take n.toNat) ∧
        (∀ k, n.toNat ≤ k → s'.scratch.work_stk1[k]? = s.scratch.work_stk1[k]?) ∧
        ∀ k < n.toNat, (s'.scratch.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars }

/-- `full_bump_analyzed_mode_fid(h, allow_reasons)`: bumps analyzed variables (plus reason-side
variables when `allow_reasons = true` and delay/decision-rate gates allow). -/
@[expose] def bumpAnalyzedModeSpec : Spec [i64, .bool] [] :=
  M6HdrContract.toSpec (W := Unit)
    { extFrame := .w2aOnly
      pre := fun c _ s (allow_reasons, ()) () => FullBumpPre allow_reasons c s
      post := fun c ext s (allow_reasons, ()) () () ext' s' =>
        AgreesExcept bumpAnalyzedCoreMask s.core s'.core ∧
        (FullAnaMarksCov c s → FullAnaMarksCov c s') ∧
        (allow_reasons = false →
          s'.core.mrk = s.core.mrk ∧ s'.core.min_clr_len = s.core.min_clr_len ∧ ext' = ext) ∧
        (allow_reasons = false →
          ∀ k < s'.core.min_clr_len,
            (s'.scratch.work_stk1[k]?.getD 0#32).toNat < s.core.cur_vars) ∧
        ScratchModifies.extPres s s' ∧
        s'.scratch.work_stk2 = s.scratch.work_stk2 }

/-- Canonical `9`-row specification table aligned 1:1 with `Src.Bump.fns`. -/
@[expose] def specs : List SpecEntry :=
  [ ⟨"full_rescale_m6",             [i64],                     [], rescaleSpec,          true⟩
  , ⟨"full_rescale",                [i64],                     [], rescaleSpec,          true⟩
  , ⟨"full_bump_var",               [i64, i32],                [], bumpVarSpec,          true⟩
  , ⟨"full_bump_decay",             [i64],                     [], rescaleSpec,          true⟩
  , ⟨"full_queue_renumber",         [i64],                     [], queueRenumberSpec,    true⟩
  , ⟨"full_queue_mtf",              [i64, i32],                [], queueMtfSpec,         true⟩
  , ⟨"full_ana_sift_m6",            [i64, i64, i64, i64, i64], [], anaSiftSpec,          true⟩
  , ⟨"full_sort_ana_qs_m6",         [i64, i64],                [], sortAnaQsSpec,        true⟩
  , ⟨"full_bump_analyzed_mode_fid", [i64, .bool],              [], bumpAnalyzedModeSpec, true⟩
  ]

end LeanQbe.T.Examples.Kissat.Proof.Bump.Spec
