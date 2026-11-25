/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityBvaProof0

/-!
# Kissat Fidelity Step-7 BVA Specifications (`FullFidelityStep7BvaSpec`)

Pure specification module (`public section`, only trivial congruence / `noExit` / `monoX`
lemmas) for the Step-7 BVA commit path of `FullFidelityStep7` (`full_bva_commit` row compaction,
`full_bva_try_lit` setting `h->res_sz = best_k`, and the `full_factor` post-commit refresh):
1. `Step7BvaLayout` / `Step7BvaMatrixInv`: `FullFidelityBva.FidBvaMatrixInv` plus the monotone
   bump layout produced by `full_bva_try_lit` (`nrow_off = bump`, `par_off = bump + max_new`,
   `new_qn ≤ max_new ≤ cur_qn`): row lengths are non-increasing and the row / parent blocks
   `[ro, ro + qn)`, `[po, po + qn)` are ordered and pairwise disjoint.
2. `Step7RowRefOk` / `Step7BvaCommittedOk`: post-commit bounds read by `full_factor`
   (`h->res_sz = best_k < sc`, compacted rows `0 ..= best_k` of binary watches or possibly
   garbage-marked arena clause refs whose literals stay `< 2 * cur_vars`).
3. `step7InitFreshVarSpec`: `FullBvaHeap.fullInitFreshVarHeapSpec` plus `res_sz` preservation
   (needed because `full_bva_try_lit` stores `h->res_sz` before calling `full_bva_commit`).
4. `step7BvaCommitSpec` (`full_bva_commit`) and `step7BvaTryLitSpec` (`full_bva_try_lit`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep7

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullBvaHeap
open Kraken.Bedrock2.Test

/-! ## 1. Monotone Bump Layout & Step-7 Matrix Invariant -/

/-- Monotone bump layout of the packed Step-7 matrix over rows `0 ..< step`
(`ro r = sb[sc + r]`, `qn r = sb[2 * sc + r]`, `po r = sb[3 * sc + r]`): row `r > 0` is followed
by its parent block, row lengths are non-increasing, and every row / parent block of row `r` ends
before row `r' > r` begins. -/
@[expose] def Step7BvaLayout (c : FullCfg) (s : FullState) (step : Nat) : Prop :=
  let sc := FullFidelityBva.fidStepsCap c.scratch_cap
  let sb := s.scratch.scratch_buf
  (∀ r < step, 0 < r →
    (sb[sc + r]?.getD 0#32).toNat + (sb[2 * sc + r]?.getD 0#32).toNat ≤
      (sb[3 * sc + r]?.getD 0#32).toNat) ∧
  (∀ r r', r < r' → r' < step →
    (sb[2 * sc + r']?.getD 0#32).toNat ≤ (sb[2 * sc + r]?.getD 0#32).toNat ∧
    (sb[sc + r]?.getD 0#32).toNat + (sb[2 * sc + r]?.getD 0#32).toNat ≤
      (sb[sc + r']?.getD 0#32).toNat ∧
    (0 < r → (sb[3 * sc + r]?.getD 0#32).toNat + (sb[2 * sc + r]?.getD 0#32).toNat ≤
      (sb[sc + r']?.getD 0#32).toNat))

/-- Step-7 packed matrix invariant: `FidBvaMatrixInv` plus the monotone bump layout. -/
@[expose] def Step7BvaMatrixInv (c : FullCfg) (F_cur : List (List Nat)) (s : FullState)
    (step bump : Nat) : Prop :=
  FullFidelityBva.FidBvaMatrixInv c F_cur s step bump ∧ Step7BvaLayout c s step

theorem Step7BvaMatrixInv.toFid {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {step bump : Nat} (h : Step7BvaMatrixInv c F_cur s step bump) :
    FullFidelityBva.FidBvaMatrixInv c F_cur s step bump :=
  h.1

theorem Step7BvaLayout.mono {c : FullCfg} {s : FullState} {step step' : Nat}
    (hle : step' ≤ step) (h : Step7BvaLayout c s step) : Step7BvaLayout c s step' :=
  ⟨fun r hr hr0 => h.1 r (by omega) hr0, fun r r' hrr hr' => h.2 r r' hrr (by omega)⟩

theorem Step7BvaLayout.congr {c : FullCfg} {s s' : FullState} {step : Nat}
    (hsb : s'.scratch.scratch_buf = s.scratch.scratch_buf) (h : Step7BvaLayout c s step) :
    Step7BvaLayout c s' step := by
  unfold Step7BvaLayout at h ⊢; rw [hsb]; exact h

/-! ## 2. Post-Commit Bounds Read by `full_factor` -/

/-- Validity of one compacted Step-7 matrix entry `w` read by `full_factor`: a binary watch
`PW_BIN_FLAG | q` with `q < 2 * cur_vars`, or an in-bounds arena clause ref (possibly already
garbage-marked by `full_bva_commit`) whose literals are all `< 2 * cur_vars`. -/
@[expose] def Step7RowRefOk (s : FullState) (w : BitVec 32) : Prop :=
  if (w &&& 0x80000000#32) ≠ 0#32 then (w &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars
  else
    w.toNat ∈ fullArenaClauseRefs s ∧
    w.toNat + 3 + fullArenaClauseSize s w.toNat ≤ s.core.arena_len ∧
    ∀ l ∈ fullArenaClauseLits s w.toNat, l < 2 * s.core.cur_vars

/-- Post-commit state read by `full_factor` after `full_bva_try_lit` returns `true`:
`h->res_sz = bk < sc`, and every row `q ≤ bk` has factor literal `< 2 * cur_vars`, an in-bounds
block `[ro, ro + qn) ⊆ [0, scratch_cap)`, and valid entries (`Step7RowRefOk`). -/
@[expose] def Step7BvaCommittedOk (c : FullCfg) (s : FullState) (bk : Nat) : Prop :=
  let sc := FullFidelityBva.fidStepsCap c.scratch_cap
  let sb := s.scratch.scratch_buf
  bk < sc ∧ s.scratch.res_sz = BitVec.ofNat 64 bk ∧
  ∀ q ≤ bk,
    let ro := (sb[sc + q]?.getD 0#32).toNat
    let qn := (sb[2 * sc + q]?.getD 0#32).toNat
    (sb[q]?.getD 0#32).toNat < 2 * s.core.cur_vars ∧ ro + qn ≤ c.scratch_cap ∧
    ∀ qi < qn, Step7RowRefOk s (sb[ro + qi]?.getD 0#32)

theorem Step7RowRefOk.congr {s s' : FullState} {w : BitVec 32}
    (hcv : s'.core.cur_vars = s.core.cur_vars) (har : s'.core.arena = s.core.arena)
    (hal : s'.core.arena_len = s.core.arena_len) (h : Step7RowRefOk s w) :
    Step7RowRefOk s' w := by
  unfold Step7RowRefOk at h ⊢
  simp only [fullArenaClauseRefs, fullArenaClauseSize, fullArenaClauseLits,
    fullArenaClauseRefsCore, fullArenaClauseSizeCore, fullArenaClauseLitsCore, har, hal,
    hcv] at h ⊢
  exact h

/-- `Step7BvaCommittedOk` only depends on `cur_vars`, `arena`, `arena_len`, `scratch_buf`, and
`res_sz` (e.g. it survives `full_bva_upd_lit_fid` heap / degree refreshes). -/
theorem Step7BvaCommittedOk.congr {c : FullCfg} {s s' : FullState} {bk : Nat}
    (hcv : s'.core.cur_vars = s.core.cur_vars) (har : s'.core.arena = s.core.arena)
    (hal : s'.core.arena_len = s.core.arena_len)
    (hsb : s'.scratch.scratch_buf = s.scratch.scratch_buf)
    (hres : s'.scratch.res_sz = s.scratch.res_sz) (h : Step7BvaCommittedOk c s bk) :
    Step7BvaCommittedOk c s' bk := by
  dsimp only [Step7BvaCommittedOk] at h ⊢
  obtain ⟨hbk, hrs, hrows⟩ := h
  refine ⟨hbk, hres.trans hrs, fun q hq => ?_⟩
  obtain ⟨hfr, hro, hent⟩ := hrows q hq
  rw [hsb, hcv]
  exact ⟨hfr, hro, fun qi hqi => (hent qi hqi).congr hcv har hal⟩

/-! ## 3. `full_init_fresh_var` with `res_sz` Preservation -/

/-- `FullBvaHeap.fullInitFreshVarHeapSpec` strengthened with `res_sz` preservation (`full_factor`
reads `h->res_sz = best_k` stored by `full_bva_try_lit` before `full_bva_commit`). -/
@[expose] def step7InitFreshVarSpec : Spec [i64, i32] [] := fun (h, fv, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ fv.toNat < s.core.cur_vars ∧ (FullMem c s ⋆ R) m ∧
    ∀ vals' mrk' flags' lvl' rsns' wvec' unass' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with vals := vals', mrk := mrk', flags := flags', lvl := lvl',
                                rsns := rsns', wvec := wvec', unassigned := unass' }
          scratch := sc' }
      s'.LengthsOk c → FullExtScratchPres s s' →
      sc'.scratch_buf = s.scratch.scratch_buf →
      sc'.wsort = s.scratch.wsort →
      sc'.tarjan_mark = s.scratch.tarjan_mark →
      sc'.tarjan_reach = s.scratch.tarjan_reach →
      sc'.sim_sig = s.scratch.sim_sig →
      sc'.res_sz = s.scratch.res_sz →
      vals'[2 * fv.toNat]?.getD 1#8 = 0#8 → vals'[2 * fv.toNat + 1]?.getD 1#8 = 0#8 →
      (∀ l < 2 * c.max_vars, l / 2 ≠ fv.toNat → vals'[l]? = s.core.vals[l]?) →
      mrk'[fv.toNat]?.getD 1#8 = 0#8 →
      (∀ v < c.max_vars, v ≠ fv.toNat → mrk'[v]? = s.core.mrk[v]?) →
      lvl'[fv.toNat]?.getD 1#32 = 0#32 →
      (∀ v < c.max_vars, v ≠ fv.toNat → lvl'[v]? = s.core.lvl[v]?) →
      rsns'[fv.toNat]?.getD 0#32 = 0xFFFFFFFF#32 →
      (∀ v < c.max_vars, v ≠ fv.toNat → rsns'[v]? = s.core.rsns[v]?) →
      (∀ k < 4, wvec'[4 * fv.toNat + k]?.getD 1#32 = 0#32) →
      (∀ i < 4 * c.max_vars, i / 4 ≠ fv.toNat → wvec'[i]? = s.core.wvec[i]?) →
      (FullMem c s' ⋆ R) m' → Q () m'

/-- Any `step7InitFreshVarSpec` implementation also satisfies `fullInitFreshVarHeapSpec`. -/
theorem step7InitFreshVarSpec_of_heap :
    ∀ xs m Q X, fullInitFreshVarHeapSpec xs m Q X → step7InitFreshVarSpec xs m Q X := by
  rintro ⟨h, fv, ⟨⟩⟩ m Q X ⟨c, s, R, hh, hl, hfv, hm, hQ⟩
  exact ⟨c, s, R, hh, hl, hfv, hm, fun vals' mrk' flags' lvl' rsns' wvec' unass' sc' m'
    h1 h2 h3 h4 h5 h6 h7 _ => hQ vals' mrk' flags' lvl' rsns' wvec' unass' sc' m'
      h1 h2 h3 h4 h5 h6 h7⟩

theorem step7InitFreshVarSpec_monoX {xs : Tup Val [i64, i32]} {m : Mem 64} {Q : Post []}
    {X X' : XPost} (h : step7InitFreshVarSpec xs m Q X) : step7InitFreshVarSpec xs m Q X' := by
  rcases xs with ⟨_, _, ⟨⟩⟩; exact h

theorem step7InitFreshVarSpec_noExit :
    ∀ xs m Q X, step7InitFreshVarSpec xs m Q X →
      step7InitFreshVarSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => step7InitFreshVarSpec_monoX h

/-! ## 4. `full_bva_commit` & `full_bva_try_lit` Specifications -/

/-- Spec for Step-7 `full_bva_commit`: consumes `Step7BvaMatrixInv` over rows `0 ..= best_k`
with `h->res_sz = best_k`, and on `ok = true` strictly increments `cur_vars` and exports the
compacted matrix (`Step7BvaCommittedOk`). -/
@[expose] def step7BvaCommitSpec : Spec [i64, i32] [.bool] := fun (h, best_k, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
    (R : Mem 64 → Prop) (bump : Nat),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧
    1 ≤ best_k.toNat ∧ best_k.toNat < FullFidelityBva.fidStepsCap c.scratch_cap ∧
    Step7BvaMatrixInv c F_cur s (best_k.toNat + 1) bump ∧
    s.scratch.res_sz = BitVec.ofNat 64 best_k.toNat ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) s' m',
      FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars →
      (ok = true → s.core.cur_vars < s'.core.cur_vars) →
      (ok = true → Step7BvaCommittedOk c s' best_k.toNat) →
      s'.core.fuel = s.core.fuel →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- Spec for Step-7 `full_bva_try_lit`: `FullFidelityBva.fidBvaTryLitSpec` plus the post-commit
matrix bounds (`Step7BvaCommittedOk`) read by `full_factor` on `ok = true`. -/
@[expose] def step7BvaTryLitSpec : Spec [i64, i32, i64] [.bool] :=
  fun (h, f0, _init_cv, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInv c F0 s ∧ f0.toNat < 2 * s.core.cur_vars ∧ (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) s' m',
        FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars →
        (ok = true → s.core.cur_vars < s'.core.cur_vars) →
        (ok = true → ∃ bk, Step7BvaCommittedOk c s' bk) →
        s'.core.fuel = s.core.fuel →
        s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
        s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

/-- Any `step7BvaTryLitSpec` implementation also satisfies `fidBvaTryLitSpec`. -/
theorem step7BvaTryLitSpec_of_fid :
    ∀ xs m Q X, FullFidelityBva.fidBvaTryLitSpec xs m Q X → step7BvaTryLitSpec xs m Q X := by
  rintro ⟨h, f0, init_cv, ⟨⟩⟩ m Q X ⟨c, F0, s, R, hh, hinv, hf0, hm, hQ⟩
  exact ⟨c, F0, s, R, hh, hinv, hf0, hm, fun ok s' m' hi hcv hlt _ hfu htm htr hm' =>
    hQ ok s' m' hi hcv hlt hfu htm htr hm'⟩

theorem step7BvaCommitSpec_monoX {xs : Tup Val [i64, i32]} {m : Mem 64} {Q : Post [.bool]}
    {X X' : XPost} (h : step7BvaCommitSpec xs m Q X) : step7BvaCommitSpec xs m Q X' := by
  rcases xs with ⟨_, _, ⟨⟩⟩; exact h

theorem step7BvaCommitSpec_noExit :
    ∀ xs m Q X, step7BvaCommitSpec xs m Q X →
      step7BvaCommitSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => step7BvaCommitSpec_monoX h

theorem step7BvaTryLitSpec_monoX {xs : Tup Val [i64, i32, i64]} {m : Mem 64}
    {Q : Post [.bool]} {X X' : XPost} (h : step7BvaTryLitSpec xs m Q X) :
    step7BvaTryLitSpec xs m Q X' := by
  rcases xs with ⟨_, _, _, ⟨⟩⟩; exact h

theorem step7BvaTryLitSpec_noExit :
    ∀ xs m Q X, step7BvaTryLitSpec xs m Q X →
      step7BvaTryLitSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => step7BvaTryLitSpec_monoX h

end LeanQbe.T.Examples.Kissat.FullFidelityStep7

end
