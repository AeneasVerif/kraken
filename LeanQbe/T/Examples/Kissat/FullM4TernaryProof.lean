module

public import LeanQbe.T.Examples.Kissat.FullM4Ternary
public import LeanQbe.T.Examples.Kissat.FullSpec3
public import LeanQbe.T.Examples.Kissat.FullArena
public import LeanQbe.T.Logic.C0HeadStep
public import LeanQbe.T.Logic.C0Agrees
public import LeanQbe.T.Logic.ControlComb
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` M4c `Func.wp` UNSAT Soundness Proofs & Non-Vacuity (`FullM4TernaryProof`)

Complete parametric `(Γ : Env)` `Func.wp` proofs (UNSAT soundness + `FullSparseInv` preservation +
concrete `Mem 64` non-vacuity, standard Lean axioms only, UNSAT-only) for all `14`
C0 functions in `FullM4Ternary.lean`:
1. `promote.c`: `full_compute_lbd`, `full_promote_clause`, `full_promote_reasons`
2. `reorder.c` / `tumble`: `full_score_sift`, `full_reorder_queue`, `full_reorder_heap`,
   `full_tumble_clause`, `full_tumble_clauses`, `full_reorder`
3. `ternary.c`: `full_ternary_match_bin`, `full_ternary_collect`, `full_ternary_resolve_bin`,
   `full_ternary_round`, `full_ternary`
4. Closed `20`-row `m4TernarySpecTable`, `m4TernaryEnv`, `m4TernaryEnv_noExit`, and
   `m4TernaryEnv_moduleOk : ModuleOk m4TernaryEnv fullM4TernaryModule`.
5. Concrete `2128`-byte `Mem 64` sparse-mode UNSAT instance (`nvM4TernaryCfg`, `nvM4TernaryState`,
   `nvM4TernaryMem`, `nvM4TernaryF0 = {(x0 ∨ x1 ∨ x2), (¬x0 ∨ x1 ∨ x2), (¬x1), (¬x2)}`) with
   unconditional `XPost := fun _ _ _ _ => False` non-vacuity theorems.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.FullM4Ternary

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open Kraken.Bedrock2.Test

/-- Parameterized environment assumption shorthand for callee `Spec` contracts. -/
abbrev EnvSpec (Γ : Env) (nm : String) {as rs : List Ty} (sp : Spec as rs) : Prop :=
  ∀ a m Q X, sp a m Q X → Γ nm as rs a m Q X

/-! ## 1. Per-Function UNSAT-Only `Spec` Contracts & `20`-Row `m4TernarySpecTable` -/

/-- Collected live ternary clause refs in `scratch_buf[0 ..< n)`. -/
def FullTernaryRefsOk (s : FullState) (n : Nat) : Prop :=
  n ≤ s.scratch.scratch_buf.length ∧
  ∀ k < n,
    let cr := (s.scratch.scratch_buf[k]?.getD 0#32).toNat
    cr ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s cr = false ∧
    fullArenaClauseSize s cr = 3

def fullComputeLbdSpec : Spec [i64, i32] [i32] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _cref, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => ∃ ws2', s'.scratch = { s.scratch with work_stk2 := ws2' })

def fullPromoteClauseSpec : Spec [i64, i32] [.bool] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ cref.toNat ∈ fullArenaClauseRefs s ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) ar' ws2' gu' m',
      let s' : FullState :=
        { core := { s.core with arena := ar' }
          scratch := { s.scratch with work_stk2 := ws2', glue_used := gu' } }
      FullSparseInvW c F0 F_cur s' →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (∀ r ∈ fullArenaClauseRefs s,
        fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
        fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
        fullArenaClauseLits s' r = fullArenaClauseLits s r) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullPromoteReasonsSpec : Spec [i64] [i64] := fun (h, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r ar' ws2' gu' m',
      let s' : FullState :=
        { core := { s.core with arena := ar' }
          scratch := { s.scratch with work_stk2 := ws2', glue_used := gu' } }
      FullSparseInv c F0 s' → (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullScoreSiftSpec : Spec [i64, i64, i64] [] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _start, n, ()) s =>
      h = c.hdr ∧
      (n.toNat ≤ s.core.cur_vars →
        ∀ k < n.toNat, (s.scratch.wsort[k]?.getD 0#32).toNat < s.core.cur_vars))
    (fun _ (_, _, n, ()) _ s s' =>
      (∃ ws', s'.scratch = { s.scratch with wsort := ws' }) ∧
      (∀ k, n.toNat ≤ k → s'.scratch.wsort[k]? = s.scratch.wsort[k]?) ∧
      (n.toNat ≤ s.core.cur_vars →
        ∀ k < n.toNat, (s'.scratch.wsort[k]?.getD 0#32).toNat < s.core.cur_vars))

def fullReorderQueueSpec : Spec [i64] [i64] :=
  SafetySlice.spec fullSafetySlice (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => FullExtScratchPres s s')

def fullReorderHeapSpec : Spec [i64] [i64] :=
  SafetySlice.spec fullSafetySlice (fun c (h, ()) _ => h = c.hdr)
    (fun _ _ _ s s' => FullExtScratchPres s s')

def fullTumbleClauseSpec : Spec [i64, i32] [.bool] := fun (h, cref, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ cref.toNat ∈ fullArenaClauseRefs s ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) ar' rng' m',
      let s' : FullState :=
        { core := { s.core with arena := ar' }, scratch := { s.scratch with rng_state := rng' } }
      FullSparseInvW c F0 F_cur s' → FullArenaPermEq s.core s'.core →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullTumbleClausesSpec : Spec [i64, i64] [i64] := fun (h, _budget, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r ar' rng' m',
      let s' : FullState :=
        { core := { s.core with arena := ar' }, scratch := { s.scratch with rng_state := rng' } }
      FullSparseInvW c F0 F_cur s' → FullArenaPermEq s.core s'.core →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullReorderSpec : Spec [i64, i64] [i64] := fun (h, _budget, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInv c F0 s' → FullArenaPermEq s.core s'.core →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullTernaryMatchBinSpec : Spec [i32, i32, i32, i32, i32, i32] [.bool] :=
  fun (p, u, v, b0, b1, b2, ()) m Q _ =>
    ∀ ok : Bool,
      (ok = true →
        let np := p ^^^ 1#32
        (b0 = np ∧ ((b1 = u ∧ b2 = v) ∨ (b1 = v ∧ b2 = u))) ∨
        (b1 = np ∧ ((b0 = u ∧ b2 = v) ∨ (b0 = v ∧ b2 = u))) ∨
        (b2 = np ∧ ((b0 = u ∧ b1 = v) ∨ (b0 = v ∧ b1 = u)))) →
      Q (ok, ()) m

def fullTernaryCollectSpec : Spec [i64, i64] [i64] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _cap, ()) s => h = c.hdr ∧ ∃ F0, FullSparseInv c F0 s)
    (fun c _ (r, ()) s s' =>
      (∃ scr', s'.scratch = { s.scratch with scratch_buf := scr' }) ∧
      r.toNat ≤ c.scratch_cap ∧ FullTernaryRefsOk s' r.toNat)

def fullTernaryResolveBinSpec : Spec [i64, i32, i32] [i64] := fun (h, c1, c2, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ s.core.cur_level = 0 ∧
    c1.toNat ∈ fullArenaClauseRefs s ∧ c2.toNat ∈ fullArenaClauseRefs s ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' wlen' wu' nb' oom' inc'
      phases' wsort' hbr' m',
      let s' : FullState :=
        { core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', trail_end := te',
                                unassigned := unass', unflushed := unfl', wvec := wvec',
                                wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
                                oom := oom', inconsistent := inc' }
          scratch := { s.scratch with phases := phases', wsort := wsort', hbr_cnt := hbr' } }
      FullSparseInvW c F0 F_cur s' →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat ∧ inc' ≠ 0#64) → (r = 2#64 → oom' ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullTernaryRoundSpec : Spec [i64, i64, i64] [i64] := fun (h, n, _budget, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInvW c F0 F_cur s ∧ s.core.cur_level = 0 ∧
    n.toNat ≤ c.scratch_cap ∧ FullTernaryRefsOk s n.toNat ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInvW c F0 F_cur s' → s'.core.cur_level = 0 →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullTernarySpec : Spec [i64, i64, i64] [i64] := fun (h, _rounds, _budget, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullSparseInv c F0 s' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) → (r = 1#64 → s'.core.cur_level = 0) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

/-- `20`-row specification table: `14` owned `FullM4Ternary` functions + `6` canonical externs. -/
def m4TernarySpecTable : List SpecEntry :=
  [ ⟨"full_compute_lbd", [i64, i32], [i32], fullComputeLbdSpec, true⟩
  , ⟨"full_promote_clause", [i64, i32], [.bool], fullPromoteClauseSpec, true⟩
  , ⟨"full_promote_reasons", [i64], [i64], fullPromoteReasonsSpec, true⟩
  , ⟨"full_score_sift", [i64, i64, i64], [], fullScoreSiftSpec, true⟩
  , ⟨"full_reorder_queue", [i64], [i64], fullReorderQueueSpec, true⟩
  , ⟨"full_reorder_heap", [i64], [i64], fullReorderHeapSpec, true⟩
  , ⟨"full_tumble_clause", [i64, i32], [.bool], fullTumbleClauseSpec, true⟩
  , ⟨"full_tumble_clauses", [i64, i64], [i64], fullTumbleClausesSpec, true⟩
  , ⟨"full_reorder", [i64, i64], [i64], fullReorderSpec, true⟩
  , ⟨"full_ternary_match_bin", [i32, i32, i32, i32, i32, i32], [.bool],
      fullTernaryMatchBinSpec, true⟩
  , ⟨"full_ternary_collect", [i64, i64], [i64], fullTernaryCollectSpec, true⟩
  , ⟨"full_ternary_resolve_bin", [i64, i32, i32], [i64], fullTernaryResolveBinSpec, true⟩
  , ⟨"full_ternary_round", [i64, i64, i64], [i64], fullTernaryRoundSpec, true⟩
  , ⟨"full_ternary", [i64, i64, i64], [i64], fullTernarySpec, true⟩
  , ⟨"full_arena_next", [i64, i32], [i32], Full.fullArenaNextSpec, true⟩
  , ⟨"full_rng_next", [i64], [i64], Full.fullRngNextSpec, true⟩
  , ⟨"full_heap_push", [i64, i32], [], Full.fullHeapPushSpec, true⟩
  , ⟨"full_backtrack", [i64, i64], [], Full.fullBacktrackSpec, true⟩
  , ⟨"full_propagate", [i64], [i64], Full.fullPropagateSpec, true⟩
  , ⟨"full_add_bin", [i64, i32, i32], [i64], Full.fullAddBinSpec, true⟩ ]

def m4TernaryEnv : Env := Env.ofTable m4TernarySpecTable

theorem m4TernarySpecTable_nodup : (m4TernarySpecTable.map SpecEntry.name).Nodup := by decide

theorem m4TernarySpecTable_noExit : ∀ e ∈ m4TernarySpecTable, e.noExit = true := by
  intro e he
  have hall : m4TernarySpecTable.all (fun x => x.noExit) = true := by t_kernel_rfl
  exact List.all_eq_true.mp hall e he

theorem m4TernarySpecTable_sigs :
    (m4TernarySpecTable.take 14).map (fun e => (e.name, e.as, e.rs)) =
      full_m4_ternary_fns.map (fun f => (f.name, f.as, f.rs)) := rfl

theorem m4TernarySpecTable_ext_sigs :
    (m4TernarySpecTable.drop 14).map (fun e => ⟨e.name, e.as, e.rs⟩) = fullM4TernaryExterns := rfl

theorem m4TernaryEnv_noExit :
    ∀ f as bs xs m Q X X',
      m4TernaryEnv f as bs xs m Q X → m4TernaryEnv f as bs xs m Q X' :=
  Env.ofTable_noExit m4TernarySpecTable_noExit

/-! ## 2. Self-Contained Semantic, Bitvector, Arena & Invariant Helpers -/

section Helpers

private theorem bv32_promote_hdr_garb (hdr fg nu : BitVec 32) :
    (((hdr &&& 0x07F80000#32) ||| (fg &&& 0x0007FFFF#32) ||| (nu <<< 27)) &&& 0x00080000#32) =
      (hdr &&& 0x00080000#32) := by
  ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_shiftLeft]
  by_cases h19 : i = 19
  · subst h19; simp
  · have hm : (0x00080000#32)[i] = false := by
      have : ∀ j : Nat, (hj : j < 32) → j ≠ 19 → (0x00080000#32)[j] = false := by decide
      exact this i hi h19
    simp [hm]

private theorem bv32_promote_hdr_shrk (hdr fg nu : BitVec 32) :
    (((hdr &&& 0x07F80000#32) ||| (fg &&& 0x0007FFFF#32) ||| (nu <<< 27)) &&& 0x00800000#32) =
      (hdr &&& 0x00800000#32) := by
  ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_shiftLeft]
  by_cases h23 : i = 23
  · subst h23; simp
  · have hm : (0x00800000#32)[i] = false := by
      have : ∀ j : Nat, (hj : j < 32) → j ≠ 23 → (0x00800000#32)[j] = false := by decide
      exact this i hi h23
    simp [hm]

private theorem bv64_shl1_toNat {x : BitVec 64} (hx : 2 * x.toNat < 2 ^ 64) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm, Nat.mod_eq_of_lt hx]

private theorem bv64_shr1_toNat (x : BitVec 64) : (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem bv32_shr1_toNat (x : BitVec 32) : (x >>> (1 : Nat)).toNat = x.toNat / 2 := by
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

private theorem bv32_xor1_toNat (x : BitVec 32) : (x ^^^ 1#32).toNat = x.toNat ^^^ 1 := by
  simp [BitVec.toNat_xor]

private theorem fullInv_max_vars_lt32 (c : FullCfg) : c.max_vars < 2 ^ 32 := by
  have h := c.hmaxv; unfold dimacsBound at h; omega

private theorem fullInv_arena_cap_lt32 (c : FullCfg) : c.arena_cap < 2 ^ 32 := by
  have h := c.harena; unfold dimacsBound at h; omega

private theorem fullInv_scratch_cap_lt32 (c : FullCfg) : c.scratch_cap < 2 ^ 32 := by
  have h := c.hscr; unfold dimacsBound at h; omega

private theorem fullArenaScanRefs_zero_mem {ar : List (BitVec 32)} {alen : Nat}
    (hlen : alen = 0 ∨ 3 ≤ alen) (hpos : 0 < alen) :
    0 ∈ fullArenaScanRefs ar alen 0 alen := by
  have h3 : 3 ≤ alen := by omega
  cases alen with
  | zero => omega
  | succ n => unfold fullArenaScanRefs; simp [show 0 + 3 ≤ n + 1 by omega]

private theorem fullArenaScanRefs_next_mem {ar : List (BitVec 32)} {alen : Nat} :
    ∀ {fuel pos p : Nat}, alen - pos ≤ fuel → p ∈ fullArenaScanRefs ar alen pos fuel →
      fullArenaNextOff ar alen p + 3 ≤ alen →
      fullArenaNextOff ar alen p ∈ fullArenaScanRefs ar alen pos fuel
  | 0, _, _, _, h, _ => by simp [fullArenaScanRefs] at h
  | fuel + 1, pos, p, hfl, hmem, hnext3 => by
    unfold fullArenaScanRefs at hmem ⊢; split at hmem
    · rename_i hpos3
      simp only [hpos3, ↓reduceIte, List.mem_cons] at hmem ⊢
      have hnb := fullArenaNextOff_bounds (ar := ar) (alen := alen) (cref := pos) hpos3
      rcases hmem with rfl | hrest
      · right; cases fuel with | zero => omega | succ _ => unfold fullArenaScanRefs; simp [hnext3]
      · exact Or.inr (fullArenaScanRefs_next_mem (by omega) hrest hnext3)
    · simp at hmem

private theorem fullArenaClauseRefs_next_or_end {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {k : FullCoreState} (hw : FullWitnessInv c F0 F_cur k)
    {p : Nat} (hp : p ∈ fullArenaClauseRefsCore k) :
    let np := fullArenaNextOff k.arena k.arena_len p
    p < np ∧ np ≤ k.arena_len ∧ (np = k.arena_len ∨ np ∈ fullArenaClauseRefsCore k) := by
  have hwf := hw.arena.refs_wf p hp
  have hnb := fullArenaNextOff_bounds (ar := k.arena) (alen := k.arena_len) (cref := p) hwf.1
  exact ⟨hnb.1, hnb.2, hwf.2.2.2.2.imp id (fullArenaScanRefs_next_mem (Nat.le_refl _) hp)⟩

/-- Shared in-place arena mutation wrapper preserving `FullSparseInvW` and `FullArenaPermEq`. -/
private theorem arenaInPlace_preserves_sparseInvW {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {ar' : List (BitVec 32)} (har_len : ar'.length = c.arena_cap)
    (hnxt : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaNextOff ar' s.core.arena_len r = fullArenaNextOff s.core.arena s.core.arena_len r)
    (hprops : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseSizeCore { s.core with arena := ar' } r = fullArenaClauseSizeCore s.core r ∧
      fullArenaClauseGarbCore { s.core with arena := ar' } r = fullArenaClauseGarbCore s.core r ∧
      (fullArenaClauseLitsCore { s.core with arena := ar' } r).Perm
        (fullArenaClauseLitsCore s.core r))
    (hshrk : ∀ r ∈ fullArenaClauseRefsCore s.core,
      (fullArenaHdrCore { s.core with arena := ar' } r &&& 0x00800000#32) ≠ 0#32 →
      ∃ t, r + 3 + fullArenaClauseSizeCore { s.core with arena := ar' } r ≤ t ∧
        t < s.core.arena_len ∧ ar'[t]? = some 0xFFFFFFFF#32) :
    let s' : FullState := { s with core := { s.core with arena := ar' } }
    FullSparseInvW c F0 F_cur s' ∧ FullArenaPermEq s.core s'.core := by
  intro s'
  have hlen := hsp.1; have hw := hsp.2.1
  have hrefs : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core :=
    fullArenaClauseRefsCore_congr rfl hnxt
  have hmem_iff : ∀ r ∈ fullArenaClauseRefsCore s.core, ∀ l,
      l ∈ fullArenaClauseLitsCore s'.core r ↔ l ∈ fullArenaClauseLitsCore s.core r :=
    fun r hr l => (hprops r hr).2.2.mem_iff
  have harena' : FullArenaClausesInv c F_cur s'.core := by
    refine ⟨hw.arena.len_ok, ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; have hwf := hw.arena.refs_wf r hr
      change _ ∧ _ ∧ _ ∧ _ ∧ _; rw [(hprops r hr).1, hnxt r hr]; exact hwf
    · intro r hr hsh; rw [hrefs] at hr; exact hshrk r hr hsh
    · intro r hr hng l hl; rw [hrefs] at hr
      exact hw.arena.lits_lt r hr ((hprops r hr).2.1.symm.trans hng) l ((hmem_iff r hr l).mp hl)
    · intro r hr hng; rw [hrefs] at hr
      exact entails_of_mem_or_false (hw.arena.entails r hr ((hprops r hr).2.1.symm.trans hng))
        fun l hl => Or.inl ((hmem_iff r hr l).mpr hl)
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := harena'
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => hrefs ▸ hr)
      reason_inv := fun idx hidx hne => by
        have hrs := hw.reason_inv idx hidx hne
        by_cases hb : (s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD
            0xFFFFFFFF#32 &&& 0x80000000#32) ≠ 0#32
        · rw [ite_eq_left hb] at hrs ⊢; exact hrs
        · rw [ite_eq_right hb] at hrs ⊢
          exact ⟨hrefs ▸ hrs.1, (hprops _ hrs.1).2.1.trans hrs.2.1,
            fun q hq => hrs.2.2 q ((hmem_iff _ hrs.1 q).mp hq)⟩
      reason_lit_mem := fun idx hidx hne hlg => by
        have hrs := hw.reason_inv idx hidx hne
        rw [ite_eq_right (fun h => h hlg)] at hrs
        exact (hmem_iff _ hrs.1 _).mpr (hw.reason_lit_mem idx hidx hne hlg) }
  have hlen' : s'.LengthsOk c :=
    ⟨{ hlen.core_ok with arena_len_arr := har_len }, hlen.scratch_ok⟩
  have hnd' : FullArenaVarsNodup s' := fun r hr hng => by
    change r ∈ fullArenaClauseRefsCore s'.core at hr; rw [hrefs] at hr
    exact (((hprops r hr).2.2).map (· / 2)).nodup_iff.mpr
      (hsp.2.2.2.1 r hr ((hprops r hr).2.1.symm.trans hng))
  have hext' : FullExtScratchOk c s' :=
    hsp.2.2.2.2.1.of_pres ⟨rfl, rfl⟩ fun r hr => by
      change r ∈ fullArenaClauseRefsCore s'.core; rw [hrefs]; exact hr
  exact ⟨⟨hlen', hw', hsp.2.2.1, hnd', hext', hsp.2.2.2.2.2⟩, rfl, hrefs, hprops⟩

/-- Updating header bits of `ar[cref]` while preserving `PH_GARB` and `PH_SHRK`. -/
private theorem hdrBitsUpdate_preserves_sparseInvW {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {cref : Nat} (hcref : cref ∈ fullArenaClauseRefs s) (f : BitVec 32 → BitVec 32)
    (hgarb : (f (fullArenaHdrCore s.core cref) &&& 0x00080000#32) =
      (fullArenaHdrCore s.core cref &&& 0x00080000#32))
    (hshrk : (f (fullArenaHdrCore s.core cref) &&& 0x00800000#32) =
      (fullArenaHdrCore s.core cref &&& 0x00800000#32)) :
    let hdr' := f (fullArenaHdrCore s.core cref)
    let s' : FullState := { s with core := { s.core with arena := s.core.arena.set cref hdr' } }
    FullSparseInvW c F0 F_cur s' ∧ fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
    (∀ r ∈ fullArenaClauseRefs s,
      fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
      fullArenaClauseGarb s' r = fullArenaClauseGarb s r ∧
      fullArenaClauseLits s' r = fullArenaClauseLits s r) := by
  intro hdr' s'
  have hlen := hsp.1; have hw := hsp.2.1; have hcref_wf := hw.arena.refs_wf cref hcref
  have hcref_lt : cref < s.core.arena.length := by
    have := hcref_wf.1; have := hlen.core_ok.arena_len_arr; have := hlen.core_ok.arena_len_le; omega
  have har_self : (s.core.arena.set cref hdr')[cref]? = some hdr' := List.getElem?_set_self hcref_lt
  have har_ne : ∀ j, j ≠ cref → (s.core.arena.set cref hdr')[j]? = s.core.arena[j]? := fun j hj =>
    List.getElem?_set_ne (Ne.symm hj)
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaNextOff (s.core.arena.set cref hdr') s.core.arena_len r =
        fullArenaNextOff s.core.arena s.core.arena_len r := by
    intro r hr; by_cases hrc : r = cref
    · subst r; unfold fullArenaNextOff
      have hnot : ¬ (cref + 3 > s.core.arena_len) := by have := hcref_wf.1; omega
      simp only [hnot, ↓reduceIte, har_self, Option.getD_some, har_ne (cref + 2) (by omega)]
      split; · rfl
      · change (if (hdr' &&& 0x00800000#32) ≠ 0#32 then _ else _) =
          if (fullArenaHdrCore s.core cref &&& 0x00800000#32) ≠ 0#32 then _ else _
        rw [hshrk]; split
        · exact fullArenaSkipShrk_congr fun j hj1 _ => har_ne j (by omega)
        · rfl
    · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
      · have := fullArenaScanRefs_disjoint hr hcref hlt
        have := (hw.arena.refs_wf r hr).2.1; have := (hw.arena.refs_wf r hr).2.2.1
        exact fullArenaNextOff_congr_block (har_ne r hrc) (har_ne (r + 2) (by omega))
          fun j _ hk2 => har_ne j (by omega)
      · exact fullArenaNextOff_congr_block (har_ne r hrc) (har_ne (r + 2) (by omega))
          fun j hj1 _ => har_ne j (by omega)
  have hprops : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r ∧
      fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r ∧
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := by
    intro r hr; have hr_wf := hw.arena.refs_wf r hr
    have hnot_in : ∀ j, r + 2 ≤ j → j < r + 3 + fullArenaClauseSizeCore s.core r → j ≠ cref := by
      intro j hj1 hj2 heq; subst j; by_cases hrc : r = cref
      · omega
      · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
        · have := hw.arena.disjoint hr hcref hlt; omega
        · omega
    have hsz : fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := by
      unfold fullArenaClauseSizeCore; dsimp only [s']
      rw [har_ne (r + 2) (hnot_in (r + 2) (Nat.le_refl _) (by have := hr_wf.2.1; omega))]
    have hgb : fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := by
      unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [s']
      by_cases hrc : r = cref
      · subst r; rw [har_self, Option.getD_some]
        change (hdr' &&& 0x00080000#32 != 0#32) = _; rw [hgarb]; rfl
      · rw [har_ne r hrc]
    have hlits : fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := by
      have hbd1 : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
        have := hr_wf.2.2.1; have := hr_wf.2.2.2.1
        have := hlen.core_ok.arena_len_arr; have := hlen.core_ok.arena_len_le; omega
      exact fullArenaClauseLitsCore_eq_of_hold hbd1 (by simpa [s'] using hbd1) hsz
        fun j hj => har_ne (r + 3 + j) (hnot_in (r + 3 + j) (by omega) (by omega))
    exact ⟨hsz, hgb, hlits⟩
  have hshrk_ok : ∀ r ∈ fullArenaClauseRefsCore s.core,
      (fullArenaHdrCore { s.core with arena := s.core.arena.set cref hdr' } r &&&
        0x00800000#32) ≠ 0#32 →
      ∃ t, r + 3 + fullArenaClauseSizeCore { s.core with arena := s.core.arena.set cref hdr' } r ≤ t
        ∧ t < s.core.arena_len ∧ (s.core.arena.set cref hdr')[t]? = some 0xFFFFFFFF#32 := by
    intro r hr hsh
    have hsh0 : (fullArenaHdrCore s.core r &&& 0x00800000#32) ≠ 0#32 := by
      by_cases hrc : r = cref
      · subst r; unfold fullArenaHdrCore at hsh ⊢; rwa [har_self, Option.getD_some, hshrk] at hsh
      · unfold fullArenaHdrCore at hsh ⊢; rwa [har_ne r hrc] at hsh
    obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
    have hr3 := (hw.arena.refs_wf r hr).1
    have hget_r : s.core.arena[r]? = some (fullArenaHdrCore s.core r) := by
      have : r < s.core.arena.length := by
        have := hlen.core_ok.arena_len_le; have := hlen.core_ok.arena_len_arr; omega
      unfold fullArenaHdrCore; rw [List.getElem?_eq_getElem this, Option.getD_some]
    obtain ⟨t0, ht0_lo, _, _, ht0_sent⟩ :=
      fullArenaNextOff_hits_sentinel hr3
        (by rw [hget_r, Option.getD_some]; exact hsh0) ht1 ht2 hsent
    have ht0_ne : t0 ≠ cref := by
      by_cases hrc : r = cref
      · subst r; omega
      · rcases Nat.lt_or_gt_of_ne hrc with hlt | hgt
        · have := fullArenaScanRefs_disjoint hr hcref hlt; omega
        · have := (hw.arena.refs_wf r hr).2.1; omega
    exact ⟨t0, by rw [(hprops r hr).1]; exact ht0_lo, by omega,
      by rw [har_ne t0 ht0_ne]; exact ht0_sent⟩
  obtain ⟨hsp', hperm'⟩ := arenaInPlace_preserves_sparseInvW hsp
    (by simp [hlen.core_ok.arena_len_arr]) hnxt
    (fun r hr => ⟨(hprops r hr).1, (hprops r hr).2.1, (hprops r hr).2.2 ▸ List.Perm.refl _⟩)
    hshrk_ok
  exact ⟨hsp', hperm'.2.1, hprops⟩

private theorem count_set_eq {α : Type} [BEq α] [LawfulBEq α] (xs : List α) {i : Nat}
    (hi : i < xs.length) (v a : α) :
    (xs.set i v).count a + (if xs[i] == a then 1 else 0) =
      xs.count a + (if v == a then 1 else 0) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x tl ih =>
    cases i with
    | zero => simp [List.count_cons]; omega
    | succ i' =>
      simp only [List.set_cons_succ, List.count_cons, List.getElem_cons_succ]
      have := ih (i := i') (by simp at hi; omega); omega

private theorem list_swap_perm {α : Type} [BEq α] [LawfulBEq α] (xs : List α) {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length) :
    ((xs.set i xs[j]).set j xs[i]).Perm xs := by
  rw [List.perm_iff_count]; intro a
  have h1 := count_set_eq xs hi xs[j] a
  have h2 := count_set_eq (xs.set i xs[j]) (i := j) (by simp [hj]) xs[i] a
  by_cases hij : i = j
  · subst hij; simp only [List.getElem_set_self] at h2; omega
  · simp only [List.getElem_set_ne hij] at h2; omega

/-- Updating `ar[cref + 1] := srch` and swapping `ar[cref + 3 + k1]` with `ar[cref + 3 + k2]`. -/
private theorem swapCl_preserves_sparseInvW {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {cref k1 k2 : Nat} {srch : BitVec 32} (hcref : cref ∈ fullArenaClauseRefsCore s.core)
    (hk1 : k1 < fullArenaClauseSizeCore s.core cref)
    (hk2 : k2 < fullArenaClauseSizeCore s.core cref) :
    have hbd : cref + 3 + fullArenaClauseSizeCore s.core cref ≤ s.core.arena.length := by
      have hwf := hsp.2.1.arena.refs_wf cref hcref
      have := hwf.2.2.1; have := hwf.2.2.2.1
      have := hsp.1.core_ok.arena_len_le; have := hsp.1.core_ok.arena_len_arr; omega
    let l1 := s.core.arena[cref + 3 + k1]'(by omega)
    let l2 := s.core.arena[cref + 3 + k2]'(by omega)
    let arena' :=
      ((s.core.arena.set (cref + 1) srch).set (cref + 3 + k1) l2).set (cref + 3 + k2) l1
    let s' : FullState := { s with core := { s.core with arena := arena' } }
    FullSparseInvW c F0 F_cur s' ∧ FullArenaPermEq s.core s'.core := by
  intro hbd l1 l2 arena' s'
  have hlen := hsp.1; have hw := hsp.2.1
  have har0 : arena'[cref]? = s.core.arena[cref]? := by
    simp only [arena']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]
  have har2 : arena'[cref + 2]? = s.core.arena[cref + 2]? := by
    simp only [arena']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]
  have har_out : ∀ i, (i < cref ∨ cref + 3 + fullArenaClauseSizeCore s.core cref ≤ i) →
      arena'[i]? = s.core.arena[i]? := fun i hi => by
    simp only [arena']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega)]
  have hout : ∀ r ∈ fullArenaClauseRefsCore s.core, r ≠ cref →
      (r + 3 + fullArenaClauseSizeCore s.core r ≤ cref ∧
        fullArenaNextOff s.core.arena s.core.arena_len r ≤ cref) ∨
      (cref + 3 + fullArenaClauseSizeCore s.core cref ≤ r) := fun r hr hne => by
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨hw.arena.disjoint hr hcref hlt, fullArenaScanRefs_disjoint hr hcref hlt⟩
    · exact Or.inr (hw.arena.disjoint hcref hr hgt)
  have hnxt : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaNextOff arena' s.core.arena_len r =
        fullArenaNextOff s.core.arena s.core.arena_len r := by
    intro r hr; by_cases hrc : r = cref
    · subst hrc; exact fullArenaNextOff_congr_block har0 har2 fun j hj1 _ => har_out j (Or.inr hj1)
    · rcases hout r hr hrc with ⟨h1, h2⟩ | hgt
      · have h3 := (hw.arena.refs_wf r hr).2.1
        exact fullArenaNextOff_congr_block (har_out r (Or.inl (by omega)))
          (har_out (r + 2) (Or.inl (by omega))) fun j _ hj2 => har_out j (Or.inl (by omega))
      · exact fullArenaNextOff_congr_block (har_out r (Or.inr hgt))
          (har_out (r + 2) (Or.inr (by omega))) fun j _ _ => har_out j (Or.inr (by omega))
  have hsz_eq : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := fun r hr => by
    unfold fullArenaClauseSizeCore; dsimp only [s']
    by_cases hrc : r = cref
    · subst hrc; exact congrArg (fun o => (o.getD 0#32).toNat) har2
    · rcases hout r hr hrc with ⟨h1, _⟩ | hgt
      · have h3 := (hw.arena.refs_wf r hr).2.1; rw [har_out (r + 2) (Or.inl (by omega))]
      · rw [har_out (r + 2) (Or.inr (by omega))]
  have hgb_eq : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := fun r hr => by
    unfold fullArenaClauseGarbCore fullArenaHdrCore; dsimp only [s']
    by_cases hrc : r = cref
    · subst hrc; rw [har0]
    · rcases hout r hr hrc with ⟨h1, _⟩ | hgt
      · rw [har_out r (Or.inl (by omega))]
      · rw [har_out r (Or.inr hgt)]
  have hperm_all : ∀ r ∈ fullArenaClauseRefsCore s.core,
      (fullArenaClauseLitsCore s'.core r).Perm (fullArenaClauseLitsCore s.core r) := by
    intro r hr
    have hbd_r : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
      have hwf := hw.arena.refs_wf r hr; have := hwf.2.2.1; have := hwf.2.2.2.1
      have := hlen.core_ok.arena_len_le; have := hlen.core_ok.arena_len_arr; omega
    by_cases hrc : r = cref
    · subst r
      let xs := fullArenaClauseLitsCore s.core cref
      have hxs_len : xs.length = fullArenaClauseSizeCore s.core cref := by
        simp only [xs, fullArenaClauseLitsCore, List.length_map, List.length_take, List.length_drop]
        omega
      have hxs_get : ∀ j (hj : j < fullArenaClauseSizeCore s.core cref),
          xs[j]'(by omega) = (s.core.arena[cref + 3 + j]'(by omega)).toNat := fun j hj => by
        simp [xs, fullArenaClauseLitsCore]
      have heq_lits : fullArenaClauseLitsCore s'.core cref =
          ((xs.set k1 (xs[k2]'(by omega))).set k2 (xs[k1]'(by omega))) := by
        apply List.ext_getElem
        · simp only [fullArenaClauseLitsCore, hsz_eq cref hr, List.length_map, List.length_take,
            List.length_drop, List.length_set, hxs_len, s', arena']
          omega
        · intro j hj1 _
          have hj : j < fullArenaClauseSizeCore s.core cref := by
            simp only [fullArenaClauseLitsCore, hsz_eq cref hr, List.length_map, List.length_take,
              List.length_drop, s', arena'] at hj1; omega
          simp only [fullArenaClauseLitsCore, List.getElem_map, List.getElem_take,
            List.getElem_drop, s', arena']
          by_cases h2 : j = k2
          · subst j; simp [List.getElem_set_self, l1]; exact (hxs_get k1 hk1).symm
          · rw [List.getElem_set_ne (by omega : cref + 3 + k2 ≠ cref + 3 + j),
              List.getElem_set_ne (by omega : k2 ≠ j)]
            by_cases h1 : j = k1
            · subst j; simp [List.getElem_set_self, l2]; exact (hxs_get k2 hk2).symm
            · rw [List.getElem_set_ne (by omega : cref + 3 + k1 ≠ cref + 3 + j),
                List.getElem_set_ne (by omega : cref + 1 ≠ cref + 3 + j),
                List.getElem_set_ne (by omega : k1 ≠ j), hxs_get j hj]
      rw [heq_lits]; exact list_swap_perm xs (by omega) (by omega)
    · rw [fullArenaClauseLitsCore_eq_of_hold hbd_r (by simp [s', arena', hbd_r]) (hsz_eq r hr)
        fun j hj => by
          dsimp only [s']; rcases hout r hr hrc with ⟨h1, _⟩ | hgt
          · exact har_out (r + 3 + j) (Or.inl (by omega))
          · exact har_out (r + 3 + j) (Or.inr (by omega))]
  have hshrk_ok : ∀ r ∈ fullArenaClauseRefsCore s.core,
      (fullArenaHdrCore s'.core r &&& 0x00800000#32) ≠ 0#32 →
      ∃ t, r + 3 + fullArenaClauseSizeCore s'.core r ≤ t ∧
        t < s.core.arena_len ∧ arena'[t]? = some 0xFFFFFFFF#32 := by
    intro r hr hsh
    have hsh0 : (fullArenaHdrCore s.core r &&& 0x00800000#32) ≠ 0#32 := by
      unfold fullArenaHdrCore at hsh ⊢; dsimp only [s'] at hsh ⊢
      by_cases hrc : r = cref
      · subst hrc; rwa [har0] at hsh
      · rcases hout r hr hrc with ⟨h1, _⟩ | hgt
        · rwa [har_out r (Or.inl (by omega))] at hsh
        · rwa [har_out r (Or.inr hgt)] at hsh
    obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
    have hr3 := (hw.arena.refs_wf r hr).1
    obtain ⟨t0, ht0_lo, ht0_lt, ht0_nxt, ht0_sent⟩ :=
      fullArenaNextOff_hits_sentinel hr3 hsh0 ht1 ht2 hsent
    have ht0_out : t0 < cref ∨ cref + 3 + fullArenaClauseSizeCore s.core cref ≤ t0 := by
      by_cases hrc : r = cref
      · subst hrc; exact Or.inr ht0_lo
      · rcases hout r hr hrc with ⟨_, h2⟩ | hgt
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
    exact ⟨t0, by rw [hsz_eq r hr]; exact ht0_lo, by omega,
      by rw [har_out t0 ht0_out]; exact ht0_sent⟩
  exact arenaInPlace_preserves_sparseInvW hsp (by simp [arena', hlen.core_ok.arena_len_arr])
    hnxt (fun r hr => ⟨hsz_eq r hr, hgb_eq r hr, hperm_all r hr⟩) hshrk_ok

private theorem setSrch_preserves_sparseInvW {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {cref : Nat} {srch : BitVec 32} (hcref : cref ∈ fullArenaClauseRefsCore s.core) :
    let s' : FullState :=
      { s with core := { s.core with arena := s.core.arena.set (cref + 1) srch } }
    FullSparseInvW c F0 F_cur s' ∧ FullArenaPermEq s.core s'.core := by
  have hwf := hsp.2.1.arena.refs_wf cref hcref
  have h3 : 3 ≤ fullArenaClauseSizeCore s.core cref := hwf.2.1
  have hbd : cref + 3 + fullArenaClauseSizeCore s.core cref ≤ s.core.arena.length := by
    have := hwf.2.2.1; have := hwf.2.2.2.1
    have := hsp.1.core_ok.arena_len_le; have := hsp.1.core_ok.arena_len_arr; omega
  have hsw := swapCl_preserves_sparseInvW hsp (cref := cref) (k1 := 0) (k2 := 0) (srch := srch)
    hcref (by omega) (by omega)
  have heq : (((s.core.arena.set (cref + 1) srch).set (cref + 3 + 0)
      (s.core.arena[cref + 3 + 0]'(by omega))).set (cref + 3 + 0)
      (s.core.arena[cref + 3 + 0]'(by omega))) = s.core.arena.set (cref + 1) srch := by
    apply List.ext_getElem (by simp); intro j hj _
    by_cases h0 : j = cref + 3 + 0
    · subst h0; simp [List.getElem_set_self, List.getElem_set_ne (by omega : cref + 1 ≠ cref + 3)]
    · rw [List.getElem_set_ne (Ne.symm h0), List.getElem_set_ne (Ne.symm h0)]
  simpa only [heq] using hsw

private theorem swapLits_preserves_sparseInvW {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {cref k1 k2 : Nat} (hcref : cref ∈ fullArenaClauseRefsCore s.core)
    (hk1 : k1 < fullArenaClauseSizeCore s.core cref)
    (hk2 : k2 < fullArenaClauseSizeCore s.core cref) :
    have hbd : cref + 3 + fullArenaClauseSizeCore s.core cref ≤ s.core.arena.length := by
      have hwf := hsp.2.1.arena.refs_wf cref hcref; have := hwf.2.2.1; have := hwf.2.2.2.1
      have := hsp.1.core_ok.arena_len_le; have := hsp.1.core_ok.arena_len_arr; omega
    let l1 := s.core.arena[cref + 3 + k1]'(by omega)
    let l2 := s.core.arena[cref + 3 + k2]'(by omega)
    let s' : FullState :=
      { s with core := { s.core with arena :=
          (s.core.arena.set (cref + 3 + k1) l2).set (cref + 3 + k2) l1 } }
    FullSparseInvW c F0 F_cur s' ∧ FullArenaPermEq s.core s'.core := by
  intro hbd l1 l2 s'
  have h1_lt : cref + 1 < s.core.arena.length := by omega
  have hsw := swapCl_preserves_sparseInvW hsp (cref := cref) (k1 := k1) (k2 := k2)
    (srch := s.core.arena[cref + 1]'h1_lt) hcref hk1 hk2
  have hset1 : s.core.arena.set (cref + 1) (s.core.arena[cref + 1]'h1_lt) = s.core.arena := by
    apply List.ext_getElem (by simp); intro j hj _
    by_cases h : j = cref + 1
    · subst h; simp
    · rw [List.getElem_set_ne (Ne.symm h)]
  simpa only [hset1] using hsw

private theorem fullArenaPermEq_refl (k : FullCoreState) : FullArenaPermEq k k :=
  ⟨rfl, rfl, fun _ _ => ⟨rfl, rfl, List.Perm.refl _⟩⟩

private theorem fullArenaPermEq_trans {k1 k2 k3 : FullCoreState}
    (h1 : FullArenaPermEq k1 k2) (h2 : FullArenaPermEq k2 k3) : FullArenaPermEq k1 k3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, fun r hr =>
    let ⟨s1, g1, p1⟩ := h1.2.2 r hr
    let ⟨s2, g2, p2⟩ := h2.2.2 r (h1.2.1.symm ▸ hr)
    ⟨s2.trans s1, g2.trans g1, p2.trans p1⟩⟩

private theorem fullSparseInvW_with_scratch {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {sc' : FullScratch} (hok : sc'.LengthsOk c)
    (hll : sc'.last_learned = s.scratch.last_learned)
    (hext : sc'.extend_len = s.scratch.extend_len) :
    FullSparseInvW c F0 F_cur { s with scratch := sc' } :=
  ⟨hsp.1.with_scratch hok, hsp.2.1, hsp.2.2.1, hsp.2.2.2.1,
   hsp.2.2.2.2.1.of_pres ⟨hll, hext⟩ (fun _ hr => hr), hsp.2.2.2.2.2⟩

private theorem fullSparseInvW_of_perm {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (hperm : FullArenaPermEq s.core s'.core)
    (hmrk : s'.core.mrk = s.core.mrk) (hlm : s'.core.lit_mark = s.core.lit_mark)
    (hdm : s'.core.dense_mode = s.core.dense_mode)
    (hpres : FullExtScratchPres s s') : FullSparseInvW c F0 F_cur s' := by
  refine ⟨hlen', hw',
    ⟨fun v hv => by rw [hmrk]; exact hsp.2.2.1.1 v hv,
     fun l hl => by rw [hlm]; exact hsp.2.2.1.2 l hl⟩, ?_, ?_, hdm.trans hsp.2.2.2.2.2⟩
  · intro ref href hng
    have href0 : ref ∈ fullArenaClauseRefsCore s.core := hperm.2.1 ▸ href
    obtain ⟨_, hgb, hp⟩ := hperm.2.2 ref href0
    exact (hp.map (· / 2)).nodup_iff.mpr (hsp.2.2.2.1 ref href0 (hgb.symm.trans hng))
  · exact hsp.2.2.2.2.1.of_pres hpres fun ref href => by
      change ref ∈ fullArenaClauseRefsCore s'.core; rw [hperm.2.1]; exact href

private theorem fullSparseInvW_of_same_arena {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c) (hw' : FullWitnessInv c F0 F_cur s'.core)
    (har : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len)
    (hmrk : s'.core.mrk = s.core.mrk) (hlm : s'.core.lit_mark = s.core.lit_mark)
    (hdm : s'.core.dense_mode = s.core.dense_mode)
    (hpres : FullExtScratchPres s s') : FullSparseInvW c F0 F_cur s' :=
  fullSparseInvW_of_perm hsp hlen' hw'
    ⟨hal, by unfold fullArenaClauseRefsCore; rw [har, hal], fun _ _ =>
      ⟨by unfold fullArenaClauseSizeCore; rw [har],
       by unfold fullArenaClauseGarbCore fullArenaHdrCore; rw [har],
       by unfold fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [har]⟩⟩
    hmrk hlm hdm hpres

private theorem fullSparseInvW_with_inconsistent {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    (hu : (cnfOfClauses F_cur).Unsat) (inc' : BitVec 64) :
    FullSparseInvW c F0 F_cur { s with core := { s.core with inconsistent := inc' } } :=
  ⟨⟨{ hsp.1.core_ok with vals_len := hsp.1.core_ok.vals_len }, hsp.1.scratch_ok⟩,
   { hsp.2.1 with
     inconsistent_sound := fun _ => hu
     arena := { hsp.2.1.arena with len_ok := hsp.2.1.arena.len_ok }
     watches := hsp.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   hsp.2.2.1, hsp.2.2.2.1, hsp.2.2.2.2.1, hsp.2.2.2.2.2⟩

private theorem level0_fcur_unsat_of_conflict_okW {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hw : FullWitnessInv c F0 F_cur s.core)
    (hl0 : s.core.cur_level = 0) (hc : FullConflictOkW F_cur s) :
    (cnfOfClauses F_cur).Unsat := by
  rcases hc with ⟨_, h0lt, h1lt, hf0, hf1, hent⟩ | ⟨_, href, hng, hfals⟩
  · refine unsat_of_entails_nil (entails_of_mem_or_false hent fun l hl => Or.inr ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff _ h0lt).mp hf0
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [heq] at hs
    · obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff _ h1lt).mp hf1
      have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [heq] at hs
  · refine unsat_of_entails_nil
      (entails_of_mem_or_false (hw.arena.entails _ href hng) fun l hl => Or.inr ?_)
    obtain ⟨i, hi, heq⟩ := (hw.vals_false_iff l (hw.arena.lits_lt _ href hng l hl)).mp (hfals l hl)
    have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega); rwa [heq] at hs

private theorem fullTernaryRefsOk_of_perm {s s' : FullState} {n : Nat}
    (h : FullTernaryRefsOk s n) (hscr : s'.scratch.scratch_buf = s.scratch.scratch_buf)
    (hperm : FullArenaPermEq s.core s'.core) : FullTernaryRefsOk s' n := by
  refine ⟨hscr ▸ h.1, fun k hk => ?_⟩
  have hk0 := h.2 k hk
  dsimp only [fullArenaClauseRefs, fullArenaClauseGarb, fullArenaClauseSize] at hk0 ⊢
  rw [hscr]; obtain ⟨hsz, hgb, _⟩ := hperm.2.2 _ hk0.1
  exact ⟨hperm.2.1.symm ▸ hk0.1, hgb.trans hk0.2.1, hsz.trans hk0.2.2⟩

private theorem fullTernaryRefsOk_of_same_arena {s s' : FullState} {n : Nat}
    (h : FullTernaryRefsOk s n) (hscr : s'.scratch.scratch_buf = s.scratch.scratch_buf)
    (har : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len) :
    FullTernaryRefsOk s' n :=
  fullTernaryRefsOk_of_perm h hscr
    ⟨hal, by unfold fullArenaClauseRefsCore; rw [har, hal], fun _ _ =>
      ⟨by unfold fullArenaClauseSizeCore; rw [har],
       by unfold fullArenaClauseGarbCore fullArenaHdrCore; rw [har],
       by unfold fullArenaClauseLitsCore fullArenaClauseSizeCore; rw [har]⟩⟩

/-- Semantic hyper-ternary binary-resolvent soundness:
if `F ⊨ (p ∨ u ∨ v)` and `F ⊨ (¬p ∨ u ∨ v)` (up to literal order), then `F ⊨ (u ∨ v)`. -/
private theorem hyperTernary_resolve_bin_entails {F : CNF Nat} {p u v b0 b1 b2 : Nat}
    (hc1 : F.EntailsClause (cnfClause [p, u, v]))
    (hc2 : F.EntailsClause (cnfClause [b0, b1, b2]))
    (hmatch :
      (b0 = p ^^^ 1 ∧ ((b1 = u ∧ b2 = v) ∨ (b1 = v ∧ b2 = u))) ∨
      (b1 = p ^^^ 1 ∧ ((b0 = u ∧ b2 = v) ∨ (b0 = v ∧ b2 = u))) ∨
      (b2 = p ^^^ 1 ∧ ((b0 = u ∧ b1 = v) ∨ (b0 = v ∧ b1 = u)))) :
    F.EntailsClause (cnfClause [u, v]) := by
  rw [CNF.entails_clause_def] at hc1 hc2 ⊢; intro α hα
  rw [clause_sat_cnfClause_iff]
  obtain ⟨l1, hm1, he1⟩ := (clause_sat_cnfClause_iff α _).mp (hc1 α hα)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm1
  rcases hm1 with h1 | h1 | h1
  · rw [h1] at he1
    obtain ⟨l2, hm2, he2⟩ := (clause_sat_cnfClause_iff α _).mp (hc2 α hα)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm2
    have hcontra : α (litVar (p ^^^ 1)) = !(litSign (p ^^^ 1)) → False := fun hneg =>
      ((sat_cnfClause_litNeg_iff α p).mp ((sat_cnfClause_singleton α (p ^^^ 1)).mpr hneg))
        ((sat_cnfClause_singleton α p).mpr he1)
    rcases hmatch with ⟨h0, ⟨hu, hv⟩ | ⟨hv, hu⟩⟩ |
      ⟨h0, ⟨hu, hv⟩ | ⟨hv, hu⟩⟩ | ⟨h0, ⟨hu, hv⟩ | ⟨hv, hu⟩⟩ <;>
      rcases hm2 with h2 | h2 | h2 <;>
      (rw [h2] at he2; simp only [h0, hu, hv] at he2)
    all_goals first
      | exact absurd he2 hcontra
      | exact ⟨u, by simp, he2⟩
      | exact ⟨v, by simp, he2⟩
  · rw [h1] at he1; exact ⟨u, by simp, he1⟩
  · rw [h1] at he1; exact ⟨v, by simp, he1⟩

private theorem fullArenaClauseLits_eq3 {s : FullState} {cr : Nat}
    (hsz : fullArenaClauseSize s cr = 3) (hbd : cr + 6 ≤ s.core.arena.length) :
    fullArenaClauseLits s cr =
      [(s.core.arena[cr + 3]'(by omega)).toNat,
       (s.core.arena[cr + 4]'(by omega)).toNat,
       (s.core.arena[cr + 5]'(by omega)).toNat] := by
  unfold fullArenaClauseLits fullArenaClauseLitsCore
  change ((s.core.arena.drop (cr + 3)).take (fullArenaClauseSize s cr)).map BitVec.toNat = _
  rw [hsz]
  apply List.ext_getElem
  · simp [List.length_take, List.length_drop]; omega
  · intro i hi _
    have hi3 : i < 3 := by simp [List.length_take, List.length_drop] at hi; omega
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;>
      simp [List.getElem_map, List.getElem_take, List.getElem_drop]

end Helpers

/-! ## 3. Parametric `(Γ : Env)` `Func.wp` Proofs for All `14` Functions -/

section Proofs

open scoped FullArenaTactics

/-! ### 3.1 `promote.c` (`full_compute_lbd`, `full_promote_clause`, `full_promote_reasons`) -/

theorem full_compute_lbd_wp (Γ : Env) :
    ∀ a m Q X, fullComputeLbdSpec a m Q X → Func.wp Γ full_compute_lbd_body a m Q X := by
  rintro ⟨h, cref, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  change (FullMem c s ⋆ R) m at hm
  have hcl := hlen.core_ok; have hsl := hlen.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hmax32 := fullInv_max_vars_lt32 c
  have har32 := fullInv_arena_cap_lt32 c; have hale := hcl.arena_len_le
  have har_len := hcl.arena_len_arr; have hlvl_len := hcl.lvl_len
  have hws2_len := hsl.work_stk2_len
  have hcr3 : (cref.setWidth 64 + 3#64).toNat = cref.toNat + 3 := by bv_omega
  unfold Func.wp full_compute_lbd_body
  c0_hsplit
  · c0_hsteps; exact hQ (0#32, ()) s m rfl hlen ⟨s.scratch.work_stk2, rfl⟩ hm
  · have hcr3_le : cref.toNat + 3 ≤ s.core.arena_len := by bv_omega
    have hcr2_lt : cref.toNat + 2 < s.core.arena.length := by omega
    let sz : BitVec 32 := s.core.arena[cref.toNat + 2]'hcr2_lt
    have hcr3sz : (cref.setWidth 64 + 3#64 + sz.setWidth 64).toNat =
        cref.toNat + 3 + sz.toNat := by bv_omega
    c0_hsplit
    · c0_hsteps; exact hQ (0#32, ()) s m rfl hlen ⟨s.scratch.work_stk2, rfl⟩ hm
    · have hc_fit := hc
      simp only [show (2 : BitVec 64).toNat = 2 by rfl, show (3 : BitVec 64).toNat = 3 by rfl,
        Nat.mod_eq_of_lt (show cref.toNat + 2 < 2 ^ 64 by omega)] at hc_fit
      have hfit : cref.toNat + 3 + sz.toNat ≤ s.core.arena_len := by
        change cref.toNat + 3 + (s.core.arena[cref.toNat + 2]'hcr2_lt).toNat ≤ _
        bv_omega
      c0_hsteps_nogrp
      refine wp_loop_inv
        (fun (glue, i, ()) mI =>
          i.toNat ≤ sz.toNat ∧ glue.toNat ≤ s.core.cur_vars ∧
          ∃ ws2I : List (BitVec 32), ws2I.length = 2 * c.max_vars ∧
            (FullMem c { s with scratch := { s.scratch with work_stk2 := ws2I } } ⋆ R) mI)
        (fun (_, i, ()) _ => sz.toNat - i.toNat)
        (fun JI hLoopI => by
          c0_hsteps
          exact hLoopI (0#32, 0#32, ()) m ⟨Nat.zero_le _, Nat.zero_le _, s.scratch.work_stk2,
            hws2_len, hm⟩)
        (fun JI ⟨glue, i, ⟨⟩⟩ mI ⟨hi_le, hgl_le, ws2I, hws2I_len, hmI⟩ hLoopI => ?_)
      let sI : FullState := { s with scratch := { s.scratch with work_stk2 := ws2I } }
      c0_hsplit
      · have hi_lt : i.toNat < sz.toNat := by
          have hc_i := hc
          simp only [show (2 : BitVec 64).toNat = 2 by rfl,
            Nat.mod_eq_of_lt (show cref.toNat + 2 < 2 ^ 64 by omega)] at hc_i
          exact hc_i
        have hi1 : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
        have hl_idx : cref.toNat + 3 + i.toNat < s.core.arena.length := by omega
        c0_hsteps_nogrp
        let l : BitVec 32 := s.core.arena[cref.toNat + 3 + i.toNat]'hl_idx
        let v : BitVec 32 := l >>> (1 : Nat)
        refine wp_join_group
          (fun (glue', ()) mJ =>
            glue'.toNat ≤ s.core.cur_vars ∧
            ∃ ws2J : List (BitVec 32), ws2J.length = 2 * c.max_vars ∧
              (FullMem c { s with scratch := { s.scratch with work_stk2 := ws2J } } ⋆ R) mJ)
          ?_ ?_
        · rintro _ ⟨glue', ⟨⟩⟩ mJ ⟨hgl', ws2J, hws2J_len, hmJ⟩
          c0_hsteps
          exact hLoopI (glue', i + 1#32, ()) mJ (by dsimp only; rw [hi1]; omega)
            ⟨by rw [hi1]; omega, hgl', ws2J, hws2J_len, hmJ⟩
        · intro Jout hJout
          c0_hsplit
          · have hc_v := hc
            simp only [show (3 : BitVec 64).toNat = 3 by rfl,
              Nat.mod_eq_of_lt (show cref.toNat + 3 + i.toNat < 2 ^ 64 by omega)] at hc_v
            have hv_lt : v.toNat < s.core.cur_vars := by
              change ((s.core.arena[cref.toNat + 3 + i.toNat]'hl_idx) >>> (1 : Nat)).toNat < _
              bv_omega
            have hv_lvl : v.toNat < s.core.lvl.length := by omega
            let lv : BitVec 32 := s.core.lvl[v.toNat]'hv_lvl
            c0_hsteps_nogrp; c0_hstep; c0_hsplit
            · c0_hsteps_nogrp
              refine wp_join_group (fun (_dup, _j, ()) mD => mI = mD) ?_ ?_
              · rintro _ ⟨dup, _j, ⟨⟩⟩ mD rfl
                c0_hstep; c0_hsplit
                · c0_hsteps; exact hJout (glue, ()) mI ⟨hgl_le, ws2I, hws2I_len, hmI⟩
                · c0_hsplit
                  · have hgl_lt : glue.toNat < s.core.cur_vars := by bv_omega
                    c0_hsplit
                    · have hgl_mask : glue.toNat < (0x0007FFFF#32).toNat := by c0_bound
                      have hgl1 : (glue + 1#32).toNat = glue.toNat + 1 := by bv_omega
                      have hgl_ws2 : glue.toNat < ws2I.length := by omega
                      c0_hsteps
                      exact hJout (glue + 1#32, ()) _
                        ⟨by rw [hgl1]; omega, _, by simp [hws2I_len], hm⟩
                    · c0_hsteps; exact hJout (glue, ()) mI ⟨hgl_le, ws2I, hws2I_len, hmI⟩
                  · c0_hsteps; exact hJout (glue, ()) mI ⟨hgl_le, ws2I, hws2I_len, hmI⟩
              · intro JD hJD
                c0_hsteps_nogrp
                refine wp_loop_inv
                  (fun (j, ()) mD => j.toNat ≤ glue.toNat ∧ mI = mD)
                  (fun (j, ()) _ => glue.toNat - j.toNat)
                  (fun JL hLoopD => by
                    c0_hsteps; exact hLoopD (0#32, ()) mI ⟨Nat.zero_le _, rfl⟩)
                  (fun JL ⟨j, ⟨⟩⟩ mD ⟨hj_le, rfl⟩ hLoopD => ?_)
                c0_hsplit
                · have hj_lt : j.toNat < glue.toNat := by c0_bound
                  have hj1 : (j + 1#32).toNat = j.toNat + 1 := by bv_omega
                  have hj_ws2 : j.toNat < ws2I.length := by omega
                  c0_hsplit
                  · c0_hsteps; exact hJD (true, j, ()) mI rfl
                  · c0_hsteps
                    exact hLoopD (j + 1#32, ()) mI (by dsimp only; rw [hj1]; omega)
                      ⟨by rw [hj1]; omega, rfl⟩
                · c0_hsteps; exact hJD (false, j, ()) mI rfl
            · c0_hsteps; exact hJout (glue, ()) mI ⟨hgl_le, ws2I, hws2I_len, hmI⟩
          · c0_hsteps; exact hJout (glue, ()) mI ⟨hgl_le, ws2I, hws2I_len, hmI⟩
      · c0_hsteps
        exact hQ (glue, ()) sI mI rfl ⟨hlen.core_ok, { hsl with work_stk2_len := hws2I_len }⟩
          ⟨ws2I, rfl⟩ hmI

theorem full_promote_clause_wp (Γ : Env)
    (hLbd : EnvSpec Γ "full_compute_lbd" fullComputeLbdSpec) :
    ∀ a m Q X, fullPromoteClauseSpec a m Q X → Func.wp Γ full_promote_clause_body a m Q X := by
  rintro ⟨h, cref, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hsp, hcref, hm, hQ⟩
  have hlen := hsp.1; have hw := hsp.2.1; have hwf := hw.arena.refs_wf cref.toNat hcref
  have hcl := hlen.core_ok; have hsl := hlen.scratch_ok
  have har32 := fullInv_arena_cap_lt32 c; have hale := hcl.arena_len_le
  have har_len := hcl.arena_len_arr; have hgu_len := hsl.glue_used_len
  have hcr3_le : cref.toNat + 3 ≤ s.core.arena_len := hwf.1
  have hcr_lt : (cref.setWidth 64).toNat < s.core.arena.length := by bv_omega
  unfold Func.wp full_promote_clause_body
  c0_hsplit
  · c0_hsteps
    exact hQ false s.core.arena s.scratch.work_stk2 s.scratch.glue_used m hsp rfl
      (fun _ _ => ⟨rfl, rfl, rfl⟩) hm
  · let hdr : BitVec 32 := s.core.arena[(cref.setWidth 64).toNat]'hcr_lt
    have hhdr_eq : hdr = fullArenaHdrCore s.core cref.toNat := by
      unfold hdr fullArenaHdrCore
      have : (cref.setWidth 64).toNat = cref.toNat := by bv_omega
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; simp only [this]
    c0_hsplit
    · c0_hsteps
      exact hQ false s.core.arena s.scratch.work_stk2 s.scratch.glue_used m hsp rfl
        (fun _ _ => ⟨rfl, rfl, rfl⟩) hm
    · c0_hsplit
      · c0_hsteps
        exact hQ false s.core.arena s.scratch.work_stk2 s.scratch.glue_used m hsp rfl
          (fun _ _ => ⟨rfl, rfl, rfl⟩) hm
      · c0_hsteps_nogrp; c0_call hLbd
        refine ⟨c, s, R, rfl, hlen, hm, ?_⟩
        rintro ⟨new_glue, ⟨⟩⟩ s1 m1 hcore1 hlen1 ⟨ws2', hsc1⟩ hm1
        change (FullMem c s1 ⋆ R) m1 at hm1
        have hce1 : s1.core = s.core := fullCoreState_agrees_with_scratch hcore1
        have hs1_eq : s1 = { s with scratch := { s.scratch with work_stk2 := ws2' } } := by
          cases s1; cases s; simp only at hce1 hsc1; subst hce1; subst hsc1; rfl
        subst hs1_eq
        c0_hsteps_nogrp
        refine wp_join_group (fun (bucket, ()) mb => bucket.toNat < 64 ∧ mb = m1) ?_ ?_
        · rintro _ ⟨bucket, ⟨⟩⟩ mb ⟨hb64, rfl⟩
          have hb_lt : (bucket.setWidth 64).toNat < s.scratch.glue_used.length := by bv_omega
          c0_hsteps_nogrp
          let gu' := s.scratch.glue_used.set (bucket.setWidth 64).toNat
            (s.scratch.glue_used[(bucket.setWidth 64).toNat]'hb_lt + 1#32)
          let s2 : FullState :=
            { s with scratch := { s.scratch with work_stk2 := ws2', glue_used := gu' } }
          have hsp2 : FullSparseInvW c F0 F_cur s2 :=
            fullSparseInvW_with_scratch hsp
              { hlen1.scratch_ok with glue_used_len := by simp [gu', hgu_len] } rfl rfl
          have hcr_lt2 : (cref.setWidth 64).toNat < s2.core.arena.length := hcr_lt
          refine wp_join_group (fun (_nu, ()) mn => (FullMem c s2 ⋆ R) mn) ?_ ?_
          · rintro _ ⟨nu, ⟨⟩⟩ mn hmn
            c0_hsteps_nogrp
            refine wp_join_group (fun (_fg, ()) mf => (FullMem c s2 ⋆ R) mf) ?_ ?_
            · rintro _ ⟨fg, ⟨⟩⟩ mf hmf
              c0_hsteps_nogrp
              refine wp_join_group
                (fun () mF => ∃ ar',
                  let sF : FullState :=
                    { core := { s.core with arena := ar' }
                      scratch := { s.scratch with work_stk2 := ws2', glue_used := gu' } }
                  FullSparseInvW c F0 F_cur sF ∧ fullArenaClauseRefs sF = fullArenaClauseRefs s ∧
                  (∀ r ∈ fullArenaClauseRefs s,
                    fullArenaClauseSize sF r = fullArenaClauseSize s r ∧
                    fullArenaClauseGarb sF r = fullArenaClauseGarb s r ∧
                    fullArenaClauseLits sF r = fullArenaClauseLits s r) ∧
                  (FullMem c sF ⋆ R) mF) ?_ ?_
              · rintro _ ⟨⟩ mF ⟨ar', hspF, hrefsF, hpropsF, hmF⟩
                c0_hsteps; exact hQ _ ar' ws2' gu' mF hspF hrefsF hpropsF hmF
              · intro Jwr hJwr
                have hwrite :
                    let nhdr :=
                      (hdr &&& 0x07F80000#32) ||| (fg &&& 0x0007FFFF#32) ||| (nu <<< 27)
                    let ar' := s.core.arena.set (cref.setWidth 64).toNat nhdr
                    let sF : FullState :=
                      { core := { s.core with arena := ar' }
                        scratch := { s.scratch with work_stk2 := ws2', glue_used := gu' } }
                    FullSparseInvW c F0 F_cur sF ∧ fullArenaClauseRefs sF = fullArenaClauseRefs s ∧
                    (∀ r ∈ fullArenaClauseRefs s,
                      fullArenaClauseSize sF r = fullArenaClauseSize s r ∧
                      fullArenaClauseGarb sF r = fullArenaClauseGarb s r ∧
                      fullArenaClauseLits sF r = fullArenaClauseLits s r) := by
                  have hcz : (cref.setWidth 64).toNat = cref.toNat := by bv_omega
                  simpa only [hcz, hhdr_eq] using hdrBitsUpdate_preserves_sparseInvW hsp2 hcref
                    (fun x => (x &&& 0x07F80000#32) ||| (fg &&& 0x0007FFFF#32) ||| (nu <<< 27))
                    (bv32_promote_hdr_garb _ fg nu) (bv32_promote_hdr_shrk _ fg nu)
                c0_hsteps <;> first
                  | exact hJwr () _ ⟨_, hwrite.1, hwrite.2.1, hwrite.2.2, hm⟩
                  | exact hJwr () _ ⟨s.core.arena, hsp2, rfl, fun _ _ => ⟨rfl, rfl, rfl⟩, hmf⟩
            · intro Jfg hJfg; c0_hsteps <;> exact hJfg _ _ hmn
          · intro Jnu hJnu; c0_hsteps <;> exact hJnu _ _ hm
        · intro J hJ
          c0_hsplit
          · c0_hsteps; exact hJ (new_glue, ()) m1 ⟨by c0_bound, rfl⟩
          · c0_hsteps; exact hJ (63#32, ()) m1 ⟨by decide, rfl⟩

theorem full_promote_reasons_wp (Γ : Env)
    (hProm : EnvSpec Γ "full_promote_clause" fullPromoteClauseSpec) :
    ∀ a m Q X, fullPromoteReasonsSpec a m Q X → Func.wp Γ full_promote_reasons_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp, hm, hQ⟩
  obtain ⟨F_cur, hspW⟩ := hsp.exists_witness
  have hlen := hspW.1; have hcl := hlen.core_ok; have hmax32 := fullInv_max_vars_lt32 c
  have hte_le := hcl.trail_end_le; have hcv_le := hcl.cur_vars_le
  have htrl_len := hcl.trl_len; have hlvl_len := hcl.lvl_len; have hrsns_len := hcl.rsns_len
  unfold Func.wp full_promote_reasons_body
  c0_hsteps_nogrp
  refine wp_loop_inv
    (fun (_cnt, i, ()) mI =>
      i.toNat ≤ s.core.trail_end ∧
      ∃ arI ws2I guI,
        let sI : FullState :=
          { core := { s.core with arena := arI }
            scratch := { s.scratch with work_stk2 := ws2I, glue_used := guI } }
        FullSparseInvW c F0 F_cur sI ∧ (FullMem c sI ⋆ R) mI)
    (fun (_, i, ()) _ => s.core.trail_end - i.toNat)
    (fun JI hLoopI => by
      c0_hsteps
      exact hLoopI (0#64, 0#64, ()) m ⟨Nat.zero_le _, s.core.arena, s.scratch.work_stk2,
        s.scratch.glue_used, hspW, hm⟩)
    (fun JI ⟨cnt, i, ⟨⟩⟩ mI ⟨hi_le, arI, ws2I, guI, hspI, hmI⟩ hLoopI => ?_)
  let sI : FullState :=
    { core := { s.core with arena := arI }
      scratch := { s.scratch with work_stk2 := ws2I, glue_used := guI } }
  c0_hsplit
  · have hi_lt : i.toNat < s.core.trail_end := by omega
    have hi1 : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
    have hi_trl : i.toNat < s.core.trl.length := by omega
    c0_hsteps_nogrp
    let lit : BitVec 32 := s.core.trl[i.toNat]'hi_trl
    let v : BitVec 32 := lit >>> (1 : Nat)
    have hv_eq : v.toNat = lit.toNat / 2 := bv32_shr1_toNat lit
    refine wp_join_group
      (fun (_cnt', ()) mJ =>
        ∃ arJ ws2J guJ,
          let sJ : FullState :=
            { core := { s.core with arena := arJ }
              scratch := { s.scratch with work_stk2 := ws2J, glue_used := guJ } }
          FullSparseInvW c F0 F_cur sJ ∧ (FullMem c sJ ⋆ R) mJ) ?_ ?_
    · rintro _ ⟨cnt', ⟨⟩⟩ mJ ⟨arJ, ws2J, guJ, hspJ, hmJ⟩
      c0_hsteps
      exact hLoopI (cnt', i + 1#64, ()) mJ (by dsimp only; rw [hi1]; omega)
        ⟨by rw [hi1]; omega, arJ, ws2J, guJ, hspJ, hmJ⟩
    · intro Jout hJout
      c0_hsplit
      · have hv_lt : v.toNat < s.core.cur_vars := by
          change (s.core.trl[i.toNat]'hi_trl >>> (1 : Nat)).toNat < _ at *; bv_omega
        have hv_lvl : (v.setWidth 64).toNat < s.core.lvl.length := by bv_omega
        c0_hsplit
        · have hv_rsn : (v.setWidth 64).toNat < s.core.rsns.length := by bv_omega
          let rsn : BitVec 32 := s.core.rsns[(v.setWidth 64).toNat]'hv_rsn
          c0_hsteps_nogrp; c0_hstep; c0_hsplit
          · have hc_ne := hc
            c0_hsplit
            · have hc_lg := hc
              have hv64 : (v.setWidth 64).toNat = lit.toNat / 2 := by
                rw [zext_toNat v (by decide)]; exact hv_eq
              have hrsn_idx : rsn = s.core.rsns[s.core.trl[i.toNat].toNat / 2]'(by omega) := by
                dsimp only [rsn]; congr 1
              have hrsn_ne : rsn ≠ 0xFFFFFFFF#32 := by rw [hrsn_idx]; exact hc_ne
              have hrsn_lg : (rsn &&& 0x80000000#32) = 0#32 := by rw [hrsn_idx]; exact hc_lg
              have hrsn_eq : sI.core.rsns[(sI.core.trl[i.toNat]?.getD 0#32).toNat / 2]?.getD
                  0xFFFFFFFF#32 = rsn := by
                change s.core.rsns[(s.core.trl[i.toNat]?.getD 0#32).toNat / 2]?.getD
                  0xFFFFFFFF#32 = s.core.rsns[(v.setWidth 64).toNat]'hv_rsn
                rw [List.getElem?_eq_getElem hi_trl, Option.getD_some]
                rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; congr 1
              have hri := hspI.2.1.reason_inv i.toNat hi_lt (by rwa [hrsn_eq])
              rw [hrsn_eq, ite_eq_right (fun h => h hrsn_lg)] at hri
              c0_hsteps_nogrp; c0_hstep; c0_call hProm
              refine ⟨c, F0, F_cur, sI, R, rfl, hspI, hri.1, hmI, ?_⟩
              rintro ok ar' ws2' gu' m' s' hsp' _ _ hm'
              c0_hsplit
              · c0_hsteps; exact hJout (cnt + 1#64, ()) m' ⟨ar', ws2', gu', hsp', hm'⟩
              · c0_hsteps; exact hJout (cnt, ()) m' ⟨ar', ws2', gu', hsp', hm'⟩
            · c0_hsteps; exact hJout (cnt, ()) mI ⟨arI, ws2I, guI, hspI, hmI⟩
          · c0_hsteps; exact hJout (cnt, ()) mI ⟨arI, ws2I, guI, hspI, hmI⟩
        · c0_hsteps; exact hJout (cnt, ()) mI ⟨arI, ws2I, guI, hspI, hmI⟩
      · c0_hsteps; exact hJout (cnt, ()) mI ⟨arI, ws2I, guI, hspI, hmI⟩
  · c0_hsteps; exact hQ cnt arI ws2I guI mI hspI.toSparse hmI

/-! ### 3.2 `reorder.c` / `tumble` (`full_score_sift` .. `full_reorder`) -/

theorem full_score_sift_wp (Γ : Env) :
    ∀ a m Q X, fullScoreSiftSpec a m Q X → Func.wp Γ full_score_sift_body a m Q X := by
  rintro ⟨h, start, n, ⟨⟩⟩ m Q X ⟨c, s, R, ⟨rfl, hws_lt⟩, hlen, hm, hQ⟩
  change (FullMem c s ⋆ R) m at hm
  have hcl := hlen.core_ok; have hsl := hlen.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hmax32 := fullInv_max_vars_lt32 c
  have hws_len := hsl.wsort_len; have hsc_len := hsl.score_len
  unfold Func.wp full_score_sift_body
  c0_hsplit
  · c0_hsteps; exact hQ () s m rfl hlen ⟨⟨s.scratch.wsort, rfl⟩, fun _ _ => rfl, hws_lt⟩ hm
  · c0_hsplit
    · c0_hsteps; exact hQ () s m rfl hlen ⟨⟨s.scratch.wsort, rfl⟩, fun _ _ => rfl, hws_lt⟩ hm
    · c0_hsplit
      · c0_hsteps; exact hQ () s m rfl hlen ⟨⟨s.scratch.wsort, rfl⟩, fun _ _ => rfl, hws_lt⟩ hm
      · have hn_pos : 0 < n.toNat := by bv_omega
        have hst_lt : start.toNat < n.toNat := by c0_bound
        have hn_le : n.toNat ≤ s.core.cur_vars := by omega
        have hws0 := hws_lt hn_le
        c0_hsteps_nogrp; c0_hstep
        refine wp_loop_inv
          (fun (root, ()) mR =>
            root.toNat < n.toNat ∧
            ∃ wsR : List (BitVec 32), wsR.length = 2 * c.max_vars ∧
              (∀ k, n.toNat ≤ k → wsR[k]? = s.scratch.wsort[k]?) ∧
              (∀ k < n.toNat, (wsR[k]?.getD 0#32).toNat < s.core.cur_vars) ∧
              (FullMem c { s with scratch := { s.scratch with wsort := wsR } } ⋆ R) mR)
          (fun (root, ()) _ => n.toNat - root.toNat)
          (fun JR hLoopR => by
            c0_hsteps
            exact hLoopR (start, ()) m ⟨hst_lt, s.scratch.wsort, hws_len, fun _ _ => rfl,
              hws0, hm⟩)
          (fun JR ⟨root, ⟨⟩⟩ mR ⟨hr_lt, wsR, hwsR_len, houtR, hbdR, hmR⟩ hLoopR => ?_)
        let sR : FullState := { s with scratch := { s.scratch with wsort := wsR } }
        have hch_eq : ((root <<< (1 : Nat)) + 1#64).toNat = 2 * root.toNat + 1 := by
          have := bv64_shl1_toNat (x := root) (by omega); bv_omega
        c0_hstep; rotate_left
        · cases hc
        c0_hsplit
        · c0_hsteps
          exact hQ () sR mR rfl ⟨hlen.core_ok, { hsl with wsort_len := hwsR_len }⟩
            ⟨⟨wsR, rfl⟩, houtR, fun _ => hbdR⟩ hmR
        · have hch_lt : ((root <<< (1 : Nat)) + 1#64).toNat < n.toNat := by c0_bound
          have hrt_ws : root.toNat < wsR.length := by omega
          have hch_ws : ((root <<< (1 : Nat)) + 1#64).toNat < wsR.length := by omega
          have hbv_lt : (wsR[root.toNat]'hrt_ws).toNat < s.core.cur_vars := by
            have := hbdR root.toNat hr_lt
            rwa [List.getElem?_eq_getElem hrt_ws, Option.getD_some] at this
          have hcv_lt : (wsR[((root <<< (1 : Nat)) + 1#64).toNat]'hch_ws).toNat <
              s.core.cur_vars := by
            have := hbdR ((root <<< (1 : Nat)) + 1#64).toNat hch_lt
            rwa [List.getElem?_eq_getElem hch_ws, Option.getD_some] at this
          c0_hsteps_nogrp
          refine wp_join_group
            (fun (best, bv, ()) m1 =>
              (best = root ∨ best = (root <<< (1 : Nat)) + 1#64) ∧
              best.toNat < n.toNat ∧ bv.toNat < s.core.cur_vars ∧
              wsR[best.toNat]? = some bv ∧ mR = m1) ?_ ?_
          · rintro _ ⟨best1, bv1, ⟨⟩⟩ m1 ⟨hb1_or, hb1_lt, hbv1_lt, hbv1_at, rfl⟩
            c0_hsteps_nogrp
            refine wp_join_group
              (fun (best2, bv2, ()) m2 =>
                (best2 = root ∨ root.toNat < best2.toNat) ∧
                best2.toNat < n.toNat ∧ bv2.toNat < s.core.cur_vars ∧
                wsR[best2.toNat]? = some bv2 ∧ mR = m2) ?_ ?_
            · rintro _ ⟨best2, bv2, ⟨⟩⟩ m2 ⟨hb2_or, hb2_lt, hbv2_lt, hbv2_at, rfl⟩
              c0_hsplit
              · c0_hsteps
                exact hQ () sR mR rfl ⟨hlen.core_ok, { hsl with wsort_len := hwsR_len }⟩
                  ⟨⟨wsR, rfl⟩, houtR, fun _ => hbdR⟩ hmR
              · have hrt_lt_b2 : root.toNat < best2.toNat :=
                  hb2_or.resolve_left (by assumption)
                have hb2_ws : best2.toNat < wsR.length := by omega
                have hb2_ws' : best2.toNat < (wsR.set root.toNat bv2).length := by simp [hb2_ws]
                let tmp := wsR[root.toNat]'hrt_ws
                let ws' := (wsR.set root.toNat bv2).set best2.toNat tmp
                have hout' : ∀ k, n.toNat ≤ k → ws'[k]? = s.scratch.wsort[k]? := fun k hk => by
                  simp only [ws']; rw [List.getElem?_set_ne (by omega),
                    List.getElem?_set_ne (by omega)]; exact houtR k hk
                have hbd' : ∀ k < n.toNat, (ws'[k]?.getD 0#32).toNat < s.core.cur_vars := by
                  intro k hk; simp only [ws']
                  by_cases hk2 : k = best2.toNat
                  · subst hk2; rw [List.getElem?_set_self (by simp [hwsR_len]; omega),
                      Option.getD_some]; exact hbv_lt
                  · rw [List.getElem?_set_ne (Ne.symm hk2)]
                    by_cases hk1 : k = root.toNat
                    · subst hk1; rw [List.getElem?_set_self hrt_ws, Option.getD_some]; exact hbv2_lt
                    · rw [List.getElem?_set_ne (Ne.symm hk1)]; exact hbdR k hk
                c0_hsteps
                exact hLoopR (best2, ()) _ (by dsimp only; omega)
                  ⟨hb2_lt, ws', by simp [ws', hwsR_len], hout', hbd', hm⟩
            · intro J2 hJ2
              have hrb1 : best1 = root ∨ root.toNat < best1.toNat :=
                hb1_or.imp id fun heq => by rw [heq, hch_eq]; omega
              c0_hsplit
              · have hrch_lt : (((root <<< (1 : Nat)) + 1#64) + 1#64).toNat < n.toNat := by
                  c0_bound
                have hrch_ws : (((root <<< (1 : Nat)) + 1#64) + 1#64).toNat < wsR.length := by
                  omega
                have hrv_lt : (wsR[(((root <<< (1 : Nat)) + 1#64) + 1#64).toNat]'hrch_ws).toNat <
                    s.core.cur_vars := by
                  have := hbdR _ hrch_lt
                  rwa [List.getElem?_eq_getElem hrch_ws, Option.getD_some] at this
                c0_hsteps_nogrp; c0_hstep; c0_hsplit
                · c0_hsteps
                  exact hJ2 ((((root <<< (1 : Nat)) + 1#64) + 1#64),
                    wsR[(((root <<< (1 : Nat)) + 1#64) + 1#64).toNat]'hrch_ws, ()) mR
                    ⟨Or.inr (by bv_omega), hrch_lt, hrv_lt, List.getElem?_eq_getElem hrch_ws, rfl⟩
                · c0_hsteps; exact hJ2 (best1, bv1, ()) mR ⟨hrb1, hb1_lt, hbv1_lt, hbv1_at, rfl⟩
              · c0_hsteps; exact hJ2 (best1, bv1, ()) mR ⟨hrb1, hb1_lt, hbv1_lt, hbv1_at, rfl⟩
          · intro J1 hJ1
            c0_hsplit
            · c0_hsteps
              exact hJ1 (((root <<< (1 : Nat)) + 1#64),
                wsR[((root <<< (1 : Nat)) + 1#64).toNat]'hch_ws, ()) mR
                ⟨Or.inr rfl, hch_lt, hcv_lt, List.getElem?_eq_getElem hch_ws, rfl⟩
            · c0_hsteps
              exact hJ1 (root, wsR[root.toNat]'hrt_ws, ()) mR
                ⟨Or.inl rfl, hr_lt, hbv_lt, List.getElem?_eq_getElem hrt_ws, rfl⟩

private theorem fullState_mk_eq {s1 s2 : FullState}
    (hc : s1.core = s2.core) (hs : s1.scratch = s2.scratch) : s1 = s2 := by
  cases s1; cases s2; cases hc; cases hs; rfl

private theorem wsort_swap_bd {ws : List (BitVec 32)} {n e cv : Nat}
    (he : e < n) (hn : n ≤ ws.length)
    (hbd : ∀ k < n, (ws[k]?.getD 0#32).toNat < cv) :
    let ws' := (ws.set 0 (ws[e]'(by omega))).set e (ws[0]'(by omega))
    ws'.length = ws.length ∧ ∀ k < n, (ws'[k]?.getD 0#32).toNat < cv := by
  refine ⟨by simp, fun k hk => ?_⟩
  by_cases hke : k = e
  · subst hke; rw [List.getElem?_set_self (by simp; omega), Option.getD_some]
    have := hbd 0 (by omega); rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
  · rw [List.getElem?_set_ne (Ne.symm hke)]
    by_cases hk0 : k = 0
    · subst hk0; rw [List.getElem?_set_self (by omega), Option.getD_some]
      have := hbd e he; rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
    · rw [List.getElem?_set_ne (Ne.symm hk0)]; exact hbd k hk

private theorem wsort_sift_bd {ws ws' : List (BitVec 32)} {n e cv : Nat}
    (hout : ∀ k, e ≤ k → ws'[k]? = ws[k]?)
    (hbd_lo : ∀ k < e, (ws'[k]?.getD 0#32).toNat < cv)
    (hbd_hi : ∀ k < n, (ws[k]?.getD 0#32).toNat < cv) :
    ∀ k < n, (ws'[k]?.getD 0#32).toNat < cv := by
  intro k hk
  by_cases hke : k < e
  · exact hbd_lo k hke
  · rw [hout k (Nat.le_of_not_lt hke)]; exact hbd_hi k hk

theorem full_reorder_queue_wp (Γ : Env)
    (hSift : EnvSpec Γ "full_score_sift" fullScoreSiftSpec) :
    ∀ a m Q X, fullReorderQueueSpec a m Q X → Func.wp Γ full_reorder_queue_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  change (FullMem c s ⋆ R) m at hm
  have hcl := hlen.core_ok; have hsl := hlen.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hmax32 := fullInv_max_vars_lt32 c
  have hfl_len := hcl.flags_len; have hv_len := hcl.vals_len
  have hws_len := hsl.wsort_len; have hqp_len := hsl.q_prev_len
  have hqn_len := hsl.q_next_len; have hqs_len := hsl.q_stamp_len
  unfold Func.wp full_reorder_queue_body
  c0_hsteps_nogrp
  refine wp_loop_inv
    (fun (n, v, ()) m1 =>
      n.toNat ≤ v.toNat ∧ v.toNat ≤ s.core.cur_vars ∧
      ∃ ws1 : List (BitVec 32), ws1.length = 2 * c.max_vars ∧
        (∀ k < n.toNat, (ws1[k]?.getD 0#32).toNat < s.core.cur_vars) ∧
        (FullMem c { s with scratch := { s.scratch with wsort := ws1 } } ⋆ R) m1)
    (fun (_, v, ()) _ => s.core.cur_vars - v.toNat)
    (fun J1 hL1 => by
      c0_hsteps
      exact hL1 (0#64, 0#64, ()) m ⟨Nat.le_refl _, Nat.zero_le _, s.scratch.wsort, hws_len,
        fun _ hk => absurd hk (Nat.not_lt_zero _), hm⟩)
    (fun J1 ⟨n, v, ⟨⟩⟩ m1 ⟨hnv, hv_le, ws1, hws1_len, hbd1, hm1⟩ hL1 => ?_)
  c0_hsplit
  · have hv_lt : v.toNat < s.core.cur_vars := by omega
    have hv1 : (v + 1#64).toNat = v.toNat + 1 := by bv_omega
    have hn1 : (n + 1#64).toNat = n.toNat + 1 := by bv_omega
    c0_hsteps_nogrp; c0_hstep; c0_hsplit
    · have hn_ws : n.toNat < ws1.length := by omega
      c0_hsteps
      refine hL1 (n + 1#64, v + 1#64, ()) _ (by dsimp only; rw [hv1]; omega)
        ⟨by rw [hn1, hv1]; omega, by rw [hv1]; omega, ws1.set n.toNat (v.setWidth 32),
         by simp [hws1_len], fun k hk => ?_, hm⟩
      rw [hn1] at hk
      by_cases hkn : k = n.toNat
      · subst hkn; rw [List.getElem?_set_self hn_ws, Option.getD_some]; bv_omega
      · rw [List.getElem?_set_ne (Ne.symm hkn)]; exact hbd1 k (by omega)
    · c0_hsteps
      exact hL1 (n, v + 1#64, ()) m1 (by dsimp only; rw [hv1]; omega)
        ⟨by rw [hv1]; omega, by rw [hv1]; omega, ws1, hws1_len, hbd1, hm1⟩
  · have hn_le : n.toNat ≤ s.core.cur_vars := by omega
    clear J1 hL1 hm hfl_len hws_len hnv hv_le
    c0_hsteps_nogrp
    refine wp_loop_inv
      (fun (v, ()) m2 =>
        v.toNat ≤ s.core.cur_vars ∧
        ∃ qp2 qn2 qs2 : List (BitVec 32),
          qp2.length = c.max_vars ∧ qn2.length = c.max_vars ∧ qs2.length = c.max_vars ∧
          (FullMem c { s with scratch :=
            { s.scratch with wsort := ws1, q_prev := qp2, q_next := qn2, q_stamp := qs2 } } ⋆ R) m2)
      (fun (v, ()) _ => s.core.cur_vars - v.toNat)
      (fun J2 hL2 => by
        c0_hsteps
        exact hL2 (0#64, ()) m1 ⟨Nat.zero_le _, s.scratch.q_prev, s.scratch.q_next,
          s.scratch.q_stamp, hqp_len, hqn_len, hqs_len, hm1⟩)
      (fun J2 ⟨v, ⟨⟩⟩ m2 ⟨hv_le2, qp2, qn2, qs2, hqp2, hqn2, hqs2, hm2⟩ hL2 => ?_)
    c0_hsplit
    · have hv_lt : v.toNat < s.core.cur_vars := by omega
      have hv1 : (v + 1#64).toNat = v.toNat + 1 := by bv_omega
      c0_hsteps
      exact hL2 (v + 1#64, ()) _ (by dsimp only; rw [hv1]; omega)
        ⟨by rw [hv1]; omega, qp2.set v.toNat 0xFFFFFFFF#32, qn2.set v.toNat 0xFFFFFFFF#32,
         qs2.set v.toNat 0#32, by simp [hqp2], by simp [hqn2], by simp [hqs2], hm⟩
    · clear J2 hL2 hm1 hqp_len hqn_len hqs_len hv_le2
      c0_hsplit
      · c0_hsteps
        let sZ : FullState :=
          { s with scratch :=
            { s.scratch with wsort := ws1, q_prev := qp2, q_next := qn2, q_stamp := qs2,
                             q_first := 0xFFFFFFFF#64, q_last := 0xFFFFFFFF#64,
                             q_search_idx := 0xFFFFFFFF#64, q_cur_stamp := 0#64,
                             q_search_stamp := 0#64 } }
        exact hQ (0#64, ()) sZ _ rfl
          ⟨hlen.core_ok,
           { hsl with wsort_len := hws1_len, q_prev_len := hqp2,
                      q_next_len := hqn2, q_stamp_len := hqs2 }⟩ ⟨rfl, rfl⟩ hm
      · have hn_pos : 0 < n.toNat := by bv_omega
        c0_hsteps_nogrp
        refine wp_loop_inv
          (fun (sv, ()) m3 =>
            sv.toNat ≤ n.toNat ∧
            ∃ ws3 : List (BitVec 32), ws3.length = 2 * c.max_vars ∧
              (∀ k < n.toNat, (ws3[k]?.getD 0#32).toNat < s.core.cur_vars) ∧
              (FullMem c { s with scratch :=
                { s.scratch with wsort := ws3, q_prev := qp2, q_next := qn2, q_stamp := qs2 } } ⋆
                R) m3)
          (fun (sv, ()) _ => sv.toNat)
          (fun J3 hL3 => by
            c0_hsteps
            exact hL3 (n >>> (1 : Nat), ()) m2
              ⟨by rw [bv64_shr1_toNat]; omega, ws1, hws1_len, hbd1, hm2⟩)
          (fun J3 ⟨sv, ⟨⟩⟩ m3 ⟨hsv_le, ws3, hws3_len, hbd3, hm3⟩ hL3 => ?_)
        c0_hsplit
        · have hsv_pos : 0 < sv.toNat := by c0_bound
          have hsv1 : (sv - 1#64).toNat = sv.toNat - 1 := by bv_omega
          let s3 : FullState :=
            { s with scratch :=
              { s.scratch with wsort := ws3, q_prev := qp2, q_next := qn2, q_stamp := qs2 } }
          have hlen3 : s3.LengthsOk c :=
            ⟨hlen.core_ok,
             { hsl with wsort_len := hws3_len, q_prev_len := hqp2,
                        q_next_len := hqn2, q_stamp_len := hqs2 }⟩
          c0_hsteps_nogrp; c0_call hSift
          refine ⟨c, s3, R, ⟨rfl, fun _ => hbd3⟩, hlen3, hm3, ?_⟩
          rintro ⟨⟩ s3' m3' hcore3' hlen3' ⟨⟨ws3', hsc3'⟩, _, hbd3'⟩ hm3'
          change (FullMem c s3' ⋆ R) m3' at hm3'
          have hs3'_eq := fullState_mk_eq (s2 := { s with scratch :=
              { s.scratch with wsort := ws3', q_prev := qp2, q_next := qn2, q_stamp := qs2 } })
            (fullCoreState_agrees_with_scratch hcore3') hsc3'
          rw [hs3'_eq] at hm3' hlen3' hbd3'
          c0_hsteps
          exact hL3 (sv - 1#64, ()) m3' (by dsimp only; rw [hsv1]; omega)
            ⟨by rw [hsv1]; omega, ws3', hlen3'.scratch_ok.wsort_len, hbd3' hn_le, hm3'⟩
        · clear J3 hL3 hm2 hws1_len hbd1 hsv_le
          c0_hsteps_nogrp
          refine wp_loop_inv
            (fun (ev, ()) m4 =>
              1 ≤ ev.toNat ∧ ev.toNat ≤ n.toNat ∧
              ∃ ws4 : List (BitVec 32), ws4.length = 2 * c.max_vars ∧
                (∀ k < n.toNat, (ws4[k]?.getD 0#32).toNat < s.core.cur_vars) ∧
                (FullMem c { s with scratch :=
                  { s.scratch with wsort := ws4, q_prev := qp2, q_next := qn2, q_stamp := qs2 } } ⋆
                  R) m4)
            (fun (ev, ()) _ => ev.toNat)
            (fun J4 hL4 => by
              c0_hsteps
              exact hL4 (n, ()) m3 ⟨hn_pos, Nat.le_refl _, ws3, hws3_len, hbd3, hm3⟩)
            (fun J4 ⟨ev, ⟨⟩⟩ m4 ⟨hev1, hev_le, ws4, hws4_len, hbd4, hm4⟩ hL4 => ?_)
          c0_hsplit
          · have hev_gt1 : 1 < ev.toNat := by c0_bound
            have hev_sub : (ev - 1#64).toNat = ev.toNat - 1 := by bv_omega
            have h0_ws : 0 < ws4.length := by omega
            have he_ws : (ev - 1#64).toNat < ws4.length := by omega
            have hn_ws : n.toNat ≤ ws4.length := by omega
            c0_hsteps_nogrp
            obtain ⟨hws4b_len, hbd4b⟩ := wsort_swap_bd (e := (ev - 1#64).toNat)
              (by omega) hn_ws hbd4
            let ws4b := (ws4.set 0 (ws4[(ev - 1#64).toNat]'he_ws)).set
              (ev - 1#64).toNat (ws4[0]'h0_ws)
            let s4b : FullState :=
              { s with scratch :=
                { s.scratch with wsort := ws4b, q_prev := qp2, q_next := qn2, q_stamp := qs2 } }
            have hlen4b : s4b.LengthsOk c :=
              ⟨hlen.core_ok, { hsl with wsort_len := hws4b_len.trans hws4_len, q_prev_len := hqp2,
                                        q_next_len := hqn2, q_stamp_len := hqs2 }⟩
            c0_call hSift
            refine ⟨c, s4b, R, ⟨rfl, fun _ k hk => hbd4b k (by bv_omega)⟩, hlen4b, hm, ?_⟩
            rintro ⟨⟩ s4' m4' hcore4' hlen4' ⟨⟨ws4', hsc4'⟩, hout4', hbd4'⟩ hm4'
            change (FullMem c s4' ⋆ R) m4' at hm4'
            have hs4'_eq := fullState_mk_eq (s2 := { s with scratch :=
                { s.scratch with wsort := ws4', q_prev := qp2, q_next := qn2, q_stamp := qs2 } })
              (fullCoreState_agrees_with_scratch hcore4') hsc4'
            rw [hs4'_eq] at hm4' hlen4' hout4' hbd4'
            have hbd4'_all := wsort_sift_bd (ws := ws4b) (e := (ev - 1#64).toNat)
              hout4' (hbd4' (by change (ev - 1#64).toNat ≤ s.core.cur_vars; rw [hev_sub]; omega))
              hbd4b
            c0_hsteps
            exact hL4 (ev - 1#64, ()) m4' (by dsimp only; rw [hev_sub]; omega)
              ⟨by rw [hev_sub]; omega, by rw [hev_sub]; omega, ws4',
               hlen4'.scratch_ok.wsort_len, hbd4'_all, hm4'⟩
          · clear J4 hL4 hSift hm3 hws3_len hbd3 hev1 hev_le
            c0_hsteps_nogrp
            refine wp_loop_inv
              (fun (_sidx, _sstamp, i, ()) m5 =>
                i.toNat ≤ n.toNat ∧
                ∃ qp5 qn5 qs5 : List (BitVec 32),
                  qp5.length = c.max_vars ∧ qn5.length = c.max_vars ∧ qs5.length = c.max_vars ∧
                  (FullMem c { s with scratch :=
                    { s.scratch with wsort := ws4, q_prev := qp5, q_next := qn5, q_stamp := qs5 } }
                    ⋆ R) m5)
              (fun (_, _, i, ()) _ => n.toNat - i.toNat)
              (fun J5 hL5 => by
                c0_hsteps
                exact hL5 (0xFFFFFFFF#64, 0#64, 0#64, ()) m4
                  ⟨Nat.zero_le _, qp2, qn2, qs2, hqp2, hqn2, hqs2, hm4⟩)
              (fun J5 ⟨sidx, sstamp, i, ⟨⟩⟩ m5 ⟨hi_le, qp5, qn5, qs5, hqp5, hqn5, hqs5, hm5⟩
                  hL5 => ?_)
            clear hm4 hqp2 hqn2 hqs2
            have hn_ws : n.toNat ≤ ws4.length := by
              rw [hws4_len]; exact Nat.le_trans hn_le (Nat.le_trans hcv_le (by omega))
            c0_hsplit
            · have hi_lt : i.toNat < n.toNat := by c0_bound
              have hi1 : (i + 1#64).toNat = i.toNat + 1 := by
                rw [BitVec.toNat_add, show (1#64).toNat = 1 by rfl, Nat.mod_eq_of_lt (by omega)]
              have hi_ws : i.toNat < ws4.length := Nat.lt_of_lt_of_le hi_lt hn_ws
              let cur : BitVec 32 := ws4[i.toNat]'hi_ws
              have hcur_lt : cur.toNat < s.core.cur_vars := by
                have := hbd4 i.toNat hi_lt
                rwa [List.getElem?_eq_getElem hi_ws, Option.getD_some] at this
              have hcur_m : (cur.setWidth 64).toNat < c.max_vars := by
                rw [zext_toNat cur (by decide)]; exact Nat.lt_of_lt_of_le hcur_lt hcv_le
              have hcur_qp : (cur.setWidth 64).toNat < qp5.length := hqp5.symm ▸ hcur_m
              have hcur_qn : (cur.setWidth 64).toNat < qn5.length := hqn5.symm ▸ hcur_m
              have hcur_qs : (cur.setWidth 64).toNat < qs5.length := hqs5.symm ▸ hcur_m
              c0_hsteps_nogrp
              refine wp_join_group (fun (_pv, ()) mp => mp = m5) ?_ ?_
              · rintro _ ⟨pv, ⟨⟩⟩ mp rfl
                c0_hsteps_nogrp
                let qp5' := qp5.set (cur.setWidth 64).toNat pv
                refine wp_join_group
                  (fun (_nv, ()) mn =>
                    (FullMem c { s with scratch :=
                      { s.scratch with wsort := ws4, q_prev := qp5',
                                       q_next := qn5, q_stamp := qs5 } }
                      ⋆ R) mn) ?_ ?_
                · rintro _ ⟨nv, ⟨⟩⟩ mn hmn
                  have hcur_v : ((cur.setWidth 64) <<< (1 : Nat)).toNat < s.core.vals.length := by
                    have h1 := bv64_shl1_toNat (x := cur.setWidth 64)
                      (by rw [zext_toNat cur (by decide)]; omega)
                    rw [h1, zext_toNat cur (by decide), hv_len]; omega
                  c0_hsteps <;>
                    exact hL5 (_, _, i + 1#64, ()) _ (by dsimp only; rw [hi1]; omega)
                      ⟨by rw [hi1]; omega, qp5', qn5.set (cur.setWidth 64).toNat nv,
                       qs5.set (cur.setWidth 64).toNat ((i + 1#64).setWidth 32),
                       by simp [qp5', hqp5], by simp [hqn5], by simp [hqs5], hm⟩
                · intro Jn hJn
                  c0_hsplit
                  · have hi1_ws : (i + 1#64).toNat < ws4.length :=
                      Nat.lt_of_lt_of_le (by c0_bound) hn_ws
                    c0_hsteps; exact hJn (ws4[(i + 1#64).toNat]'hi1_ws, ()) _ hm
                  · c0_hsteps; exact hJn (0xFFFFFFFF#32, ()) _ hm
              · intro Jp hJp
                c0_hsplit
                · have him1_ws : (i - 1#64).toNat < ws4.length := by
                    have : 0 < i.toNat := by c0_bound
                    have : (i - 1#64).toNat = i.toNat - 1 := by bv_omega
                    omega
                  c0_hsteps; exact hJp (ws4[(i - 1#64).toNat]'him1_ws, ()) m5 rfl
                · c0_hsteps; exact hJp (0xFFFFFFFF#32, ()) m5 rfl
            · have h0_ws : 0 < ws4.length := Nat.lt_of_lt_of_le hn_pos hn_ws
              have hn1_ws : (n - 1#64).toNat < ws4.length := by
                have : (n - 1#64).toNat = n.toNat - 1 := by bv_omega
                omega
              let sF (qf ql si ss : BitVec 64) : FullState :=
                { s with scratch :=
                  { s.scratch with wsort := ws4, q_prev := qp5, q_next := qn5, q_stamp := qs5,
                                   q_first := qf, q_last := ql, q_cur_stamp := n,
                                   q_search_idx := si, q_search_stamp := ss } }
              c0_hsteps <;>
                exact hQ (n, ()) (sF _ _ _ _) _ rfl
                  ⟨hlen.core_ok,
                   { hsl with wsort_len := hws4_len, q_prev_len := hqp5,
                              q_next_len := hqn5, q_stamp_len := hqs5 }⟩ ⟨rfl, rfl⟩ hm

theorem full_reorder_heap_wp (Γ : Env)
    (hPush : EnvSpec Γ "full_heap_push" Full.fullHeapPushSpec) :
    ∀ a m Q X, fullReorderHeapSpec a m Q X → Func.wp Γ full_reorder_heap_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  change (FullMem c s ⋆ R) m at hm
  have hcl := hlen.core_ok; have hsl := hlen.scratch_ok
  have hcv_le := hcl.cur_vars_le; have hmax32 := fullInv_max_vars_lt32 c
  have hfl_len := hcl.flags_len; have hv_len := hcl.vals_len; have hps_len := hsl.pos_len
  unfold Func.wp full_reorder_heap_body
  c0_hsteps_nogrp
  refine wp_loop_inv
    (fun (v, ()) m1 =>
      v.toNat ≤ s.core.cur_vars ∧
      ∃ ps1 : List (BitVec 32), ps1.length = c.max_vars ∧
        (FullMem c { s with scratch := { s.scratch with heap_len := 0, pos := ps1 } } ⋆ R) m1)
    (fun (v, ()) _ => s.core.cur_vars - v.toNat)
    (fun J1 hL1 => by
      c0_hsteps
      exact hL1 (0#64, ()) _ ⟨Nat.zero_le _, s.scratch.pos, hps_len, hm⟩)
    (fun J1 ⟨v, ⟨⟩⟩ m1 ⟨hv_le, ps1, hps1_len, hm1⟩ hL1 => ?_)
  c0_hsplit
  · have hv_lt : v.toNat < s.core.cur_vars := by omega
    have hv1 : (v + 1#64).toNat = v.toNat + 1 := by bv_omega
    c0_hsteps
    exact hL1 (v + 1#64, ()) _ (by dsimp only; rw [hv1]; omega)
      ⟨by rw [hv1]; omega, ps1.set v.toNat 0xFFFFFFFF#32, by simp [hps1_len], hm⟩
  · c0_hsteps_nogrp
    refine wp_loop_inv
      (fun (v, ()) m2 =>
        v.toNat ≤ s.core.cur_vars ∧
        ∃ s2 : FullState, s2.core = s.core ∧ s2.LengthsOk c ∧ FullExtScratchPres s s2 ∧
          (FullMem c s2 ⋆ R) m2)
      (fun (v, ()) _ => s.core.cur_vars - v.toNat)
      (fun J2 hL2 => by
        c0_hsteps
        let s1 : FullState := { s with scratch := { s.scratch with heap_len := 0, pos := ps1 } }
        exact hL2 (0#64, ()) m1 ⟨Nat.zero_le _, s1, rfl,
          ⟨hlen.core_ok, { hsl with pos_len := hps1_len }⟩, ⟨rfl, rfl⟩, hm1⟩)
      (fun J2 ⟨v, ⟨⟩⟩ m2 ⟨hv_le2, s2, hce2, hlen2, hpres2, hm2⟩ hL2 => ?_)
    c0_hsplit
    · have hv_lt : v.toNat < s.core.cur_vars := by omega
      have hv1 : (v + 1#64).toNat = v.toNat + 1 := by bv_omega
      have hv_fl : v.toNat < s2.core.flags.length := by rw [hce2]; omega
      c0_hsteps_nogrp; c0_hstep; c0_hsplit
      · have h2v_lt : (v <<< (1 : Nat)).toNat < s2.core.vals.length := by
          rw [hce2, bv64_shl1_toNat (by omega)]; omega
        c0_hsplit
        · c0_hsteps_nogrp; c0_call hPush
          refine ⟨c, s2, R, rfl, hlen2, hm2, ?_⟩
          rintro ⟨⟩ s3 m3 hcore3 hlen3 hpr3 hm3
          change (FullMem c s3 ⋆ R) m3 at hm3
          have hce3 : s3.core = s.core := (fullCoreState_agrees_with_scratch hcore3).trans hce2
          c0_hsteps
          exact hL2 (v + 1#64, ()) m3 (by dsimp only; rw [hv1]; omega)
            ⟨by rw [hv1]; omega, s3, hce3, hlen3,
             ⟨hpr3.1.1.trans hpres2.1, hpr3.1.2.trans hpres2.2⟩, hm3⟩
        · c0_hsteps
          exact hL2 (v + 1#64, ()) m2 (by dsimp only; rw [hv1]; omega)
            ⟨by rw [hv1]; omega, s2, hce2, hlen2, hpres2, hm2⟩
      · c0_hsteps
        exact hL2 (v + 1#64, ()) m2 (by dsimp only; rw [hv1]; omega)
          ⟨by rw [hv1]; omega, s2, hce2, hlen2, hpres2, hm2⟩
    · c0_hsteps
      exact hQ (BitVec.ofNat 64 s2.scratch.heap_len, ()) s2 m2
        (by unfold PreservesCoreSlice fullSafetySlice; simp [hce2]) hlen2 hpres2 hm2

theorem full_tumble_clause_wp (Γ : Env)
    (hRng : EnvSpec Γ "full_rng_next" Full.fullRngNextSpec) :
    ∀ a m Q X, fullTumbleClauseSpec a m Q X → Func.wp Γ full_tumble_clause_body a m Q X := by
  rintro ⟨h, cref, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hsp, hcref, hm, hQ⟩
  have hlen := hsp.1; have hw := hsp.2.1; have hwf := hw.arena.refs_wf cref.toNat hcref
  have hcl := hlen.core_ok; have har32 := fullInv_arena_cap_lt32 c
  have hale := hcl.arena_len_le; have har_len := hcl.arena_len_arr
  have hcr3_le : cref.toNat + 3 ≤ s.core.arena_len := hwf.1
  have hcr0_lt : (cref.setWidth 64).toNat < s.core.arena.length := by bv_omega
  have hcr2_lt : (cref.setWidth 64 + 2#64).toNat < s.core.arena.length := by bv_omega
  unfold Func.wp full_tumble_clause_body
  c0_hsplit
  · c0_hsteps; exact hQ false s.core.arena s.scratch.rng_state m hsp (fullArenaPermEq_refl _) hm
  · have hcr2_lt' : cref.toNat + 2 < s.core.arena.length := by omega
    let sz := s.core.arena[cref.toNat + 2]'hcr2_lt'
    have hsz_eq : sz.toNat = fullArenaClauseSizeCore s.core cref.toNat := by
      unfold sz fullArenaClauseSizeCore
      rw [List.getElem?_eq_getElem hcr2_lt', Option.getD_some]
    c0_hsplit
    · c0_hsteps; exact hQ false s.core.arena s.scratch.rng_state m hsp (fullArenaPermEq_refl _) hm
    · c0_hsplit
      · c0_hsteps; exact hQ false s.core.arena s.scratch.rng_state m hsp (fullArenaPermEq_refl _) hm
      · have hc_sz4 := hc
        simp only [show (2 : BitVec 64).toNat = 2 by rfl,
          Nat.mod_eq_of_lt (show cref.toNat + 2 < 2 ^ 64 by omega)] at hc_sz4
        c0_hsplit
        · c0_hsteps
          exact hQ false s.core.arena s.scratch.rng_state m hsp (fullArenaPermEq_refl _) hm
        · have hc_fit := hc
          simp only [show (2 : BitVec 64).toNat = 2 by rfl, show (3 : BitVec 64).toNat = 3 by rfl,
            Nat.mod_eq_of_lt (show cref.toNat + 2 < 2 ^ 64 by omega)] at hc_fit
          have hsz4 : 4 ≤ sz.toNat := by
            change 4 ≤ (s.core.arena[cref.toNat + 2]'hcr2_lt').toNat; bv_omega
          have hfit : cref.toNat + 3 + sz.toNat ≤ s.core.arena_len := by
            change cref.toNat + 3 + (s.core.arena[cref.toNat + 2]'hcr2_lt').toNat ≤ _; bv_omega
          have hcr1_lt : (cref.setWidth 64 + 1#64).toNat < s.core.arena.length := by bv_omega
          have hcr1_eq : (cref.setWidth 64 + 1#64).toNat = cref.toNat + 1 := by bv_omega
          obtain ⟨hsp0, hperm0⟩ := setSrch_preserves_sparseInvW hsp (srch := 2#32) hcref
          c0_hsteps_nogrp
          let ar0 := s.core.arena.set (cref.setWidth 64 + 1#64).toNat 2#32
          have har0_eq : ar0 = s.core.arena.set (cref.toNat + 1) 2#32 := by simp [ar0, hcr1_eq]
          have hsz_idx :
              s.core.arena[(cref.setWidth 64 + (2 : BitVec 64)).toNat]'hcr2_lt = sz := by
            dsimp only [sz]; congr 1; bv_omega
          refine wp_loop_inv
            (fun (i, ()) mI =>
              2 ≤ i.toNat ∧ i.toNat < sz.toNat ∧
              ∃ arI rngI,
                let sI : FullState :=
                  { core := { s.core with arena := arI }
                    scratch := { s.scratch with rng_state := rngI } }
                FullSparseInvW c F0 F_cur sI ∧ FullArenaPermEq s.core sI.core ∧
                (FullMem c sI ⋆ R) mI)
            (fun (i, ()) _ => i.toNat)
            (fun JI hLI => by
              c0_hsteps; rw [hsz_idx]
              exact hLI (sz - 1#32, ()) _
                ⟨by bv_omega, by bv_omega, ar0, s.scratch.rng_state,
                 by simpa only [har0_eq] using hsp0, by simpa only [har0_eq] using hperm0, hm⟩)
            (fun JI ⟨i, ⟨⟩⟩ mI ⟨hi2, hi_lt, arI, rngI, hspI, hpermI, hmI⟩ hLI => ?_)
          let sI : FullState :=
            { core := { s.core with arena := arI }
              scratch := { s.scratch with rng_state := rngI } }
          c0_hsplit
          · have hi3 : 3 ≤ i.toNat := by c0_bound
            have hi_sub : (i - 1#32).toNat = i.toNat - 1 := by bv_omega
            c0_hsteps_nogrp; c0_call hRng
            refine ⟨c, sI, R, rfl, hspI.1, hmI, ?_⟩
            rintro ⟨r, ⟨⟩⟩ sR mR hcoreR hlenR hscR hmR
            change (FullMem c sR ⋆ R) mR at hmR
            have hceR : sR.core = sI.core := fullCoreState_agrees_with_scratch hcoreR
            let sR' : FullState :=
              { core := { s.core with arena := arI }
                scratch := { s.scratch with rng_state := sR.scratch.rng_state } }
            have hsR_eq : sR = sR' := fullState_mk_eq hceR hscR
            rw [hsR_eq] at hmR hlenR
            have hspR : FullSparseInvW c F0 F_cur sR' :=
              fullSparseInvW_with_scratch hspI hlenR.scratch_ok rfl rfl
            let span : BitVec 32 := i - 1#32
            have hspan_eq : span.toNat = i.toNat - 1 := hi_sub
            have hsz32 : sz.toNat < 2 ^ 32 := sz.isLt
            have hspan_pos : 2 ≤ span.toNat := by omega
            have hspan_ne : span.setWidth 64 ≠ 0#64 := fun h0 => by
              have := congrArg BitVec.toNat h0
              rw [zext_toNat span (by decide)] at this; simp at this; omega
            have hrem_lt : (r % span.setWidth 64).toNat < span.toNat := by
              rw [BitVec.toNat_umod, zext_toNat span (by decide)]; exact Nat.mod_lt _ (by omega)
            let j : BitVec 32 := 2#32 + (r % span.setWidth 64).setWidth 32
            have hj_lt : j.toNat < sz.toNat := by
              have htr : ((r % span.setWidth 64).setWidth 32).toNat =
                  (r % span.setWidth 64).toNat := by
                rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
              have hj_eq : j.toNat = 2 + (r % span.setWidth 64).toNat := by
                unfold j; rw [BitVec.toNat_add, htr, show (2#32).toNat = 2 by rfl,
                  Nat.mod_eq_of_lt (by omega)]
              omega
            have hcrefR : cref.toNat ∈ fullArenaClauseRefsCore sR'.core := by
              change cref.toNat ∈ fullArenaClauseRefsCore sI.core
              rw [hpermI.2.1]; exact hcref
            have hszR : fullArenaClauseSizeCore sR'.core cref.toNat = sz.toNat := by
              change fullArenaClauseSizeCore sI.core cref.toNat = sz.toNat
              rw [(hpermI.2.2 cref.toNat hcref).1, hsz_eq]
            have harR_len : sR'.core.arena.length = c.arena_cap := hlenR.core_ok.arena_len_arr
            have hi_eq : (cref.setWidth 64 + (3 : BitVec 64) + i.setWidth 64).toNat =
                cref.toNat + 3 + i.toNat := by bv_omega
            have hj_raw :
                (cref.setWidth 64 + (3 : BitVec 64) +
                  ((2 : BitVec 32) + (r % (i - (1 : BitVec 32)).setWidth 64).setWidth 32).setWidth
                    64).toNat =
                cref.toNat + 3 + j.toNat := by
              change (cref.setWidth 64 + 3#64 + j.setWidth 64).toNat = _; bv_omega
            have hi_ar :
                (cref.setWidth 64 + (3 : BitVec 64) + i.setWidth 64).toNat <
                  sR'.core.arena.length := by rw [hi_eq]; omega
            have hj_ar :
                (cref.setWidth 64 + (3 : BitVec 64) +
                  ((2 : BitVec 32) + (r % (i - (1 : BitVec 32)).setWidth 64).setWidth 32).setWidth
                    64).toNat <
                  sR'.core.arena.length := by rw [hj_raw]; omega
            have hj_ar2 :
                (cref.setWidth 64 + (3 : BitVec 64) +
                  ((2 : BitVec 32) + (r % (i - (1 : BitVec 32)).setWidth 64).setWidth 32).setWidth
                    64).toNat <
                  (sR'.core.arena.set (cref.setWidth 64 + (3 : BitVec 64) + i.setWidth 64).toNat
                    (sR'.core.arena[(cref.setWidth 64 + (3 : BitVec 64) +
                      ((2 : BitVec 32) + (r % (i - (1 : BitVec 32)).setWidth 64).setWidth
                        32).setWidth 64).toNat]'hj_ar)).length := by
              rw [List.length_set]; exact hj_ar
            have hsw := swapLits_preserves_sparseInvW hspR (cref := cref.toNat)
              (k1 := i.toNat) (k2 := j.toNat) hcrefR (by omega) (by omega)
            c0_hsteps!
            have hperm' := fullArenaPermEq_trans hpermI hsw.2
            exact hLI (i - 1#32, ()) _ (by dsimp only; rw [hi_sub]; omega)
              ⟨by rw [hi_sub]; omega, by rw [hi_sub]; omega, _, sR.scratch.rng_state,
               by simpa only [sR', hi_eq, hj_raw] using hsw.1,
               by simpa only [sR', hi_eq, hj_raw] using hperm', hm⟩
          · c0_hsteps; exact hQ true arI rngI mI hspI hpermI hmI

theorem full_tumble_clauses_wp (Γ : Env)
    (hNext : EnvSpec Γ "full_arena_next" Full.fullArenaNextSpec)
    (hTumble : EnvSpec Γ "full_tumble_clause" fullTumbleClauseSpec) :
    ∀ a m Q X, fullTumbleClausesSpec a m Q X → Func.wp Γ full_tumble_clauses_body a m Q X := by
  rintro ⟨h, budget, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hsp, hm, hQ⟩
  have hcl := hsp.1.core_ok; have har32 := fullInv_arena_cap_lt32 c; have hale := hcl.arena_len_le
  unfold Func.wp full_tumble_clauses_body
  c0_hsteps_nogrp; c0_hstep
  refine wp_loop_inv
    (fun (p, _done, ()) mP =>
      p.toNat ≤ s.core.arena_len ∧ (p.toNat = s.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs s) ∧
      ∃ arP rngP,
        let sP : FullState :=
          { core := { s.core with arena := arP }, scratch := { s.scratch with rng_state := rngP } }
        FullSparseInvW c F0 F_cur sP ∧ FullArenaPermEq s.core sP.core ∧ (FullMem c sP ⋆ R) mP)
    (fun (p, _, ()) _ => s.core.arena_len - p.toNat)
    (fun JP hLP => by
      c0_hsteps
      refine hLP (0#64, 0#64, ()) m ⟨Nat.zero_le _, ?_, s.core.arena, s.scratch.rng_state,
        hsp, fullArenaPermEq_refl _, hm⟩
      by_cases h0 : s.core.arena_len = 0
      · exact Or.inl h0.symm
      · exact Or.inr (fullArenaScanRefs_zero_mem hsp.2.1.arena.len_ok (Nat.pos_of_ne_zero h0)))
    (fun JP ⟨p, done, ⟨⟩⟩ mP ⟨hp_le, hp_mem, arP, rngP, hspP, hpermP, hmP⟩ hLP => ?_)
  let sP : FullState :=
    { core := { s.core with arena := arP }, scratch := { s.scratch with rng_state := rngP } }
  c0_hsplit
  · have hp_lt : p.toNat < s.core.arena_len := by omega
    c0_hsplit
    · have hp_ref : p.toNat ∈ fullArenaClauseRefs s := hp_mem.resolve_left (by omega)
      have hp_refP : p.toNat ∈ fullArenaClauseRefs sP := by
        change p.toNat ∈ fullArenaClauseRefsCore sP.core; rw [hpermP.2.1]; exact hp_ref
      have hp32 : (p.setWidth 32).toNat = p.toNat := by bv_omega
      c0_hsteps_nogrp; c0_call hNext
      refine ⟨c, sP, R, rfl, hspP.1, hmP, ?_⟩
      obtain ⟨hnp_gt, hnp_le, hnp_memP⟩ := fullArenaClauseRefs_next_or_end hspP.2.1 hp_refP
      dsimp only [sP] at hnp_gt hnp_le
      let np32 := BitVec.ofNat 32
        (fullArenaNextOff sP.core.arena sP.core.arena_len (p.setWidth 32).toNat)
      have hnp_eq : (np32.setWidth 64).toNat = fullArenaNextOff arP s.core.arena_len p.toNat := by
        dsimp only [np32, sP]; rw [hp32, zext_toNat _ (by decide), BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega)]
      have hnp_mem : fullArenaNextOff arP s.core.arena_len p.toNat = s.core.arena_len ∨
          fullArenaNextOff arP s.core.arena_len p.toNat ∈ fullArenaClauseRefs s :=
        hnp_memP.imp id fun h2 => by
          change _ ∈ fullArenaClauseRefsCore sP.core at h2; rwa [hpermP.2.1] at h2
      c0_hsteps_nogrp
      refine wp_join_group
        (fun (_done', ()) mJ =>
          ∃ ar' rng',
            let s' : FullState :=
              { core := { s.core with arena := ar' }
                scratch := { s.scratch with rng_state := rng' } }
            FullSparseInvW c F0 F_cur s' ∧ FullArenaPermEq s.core s'.core ∧
            (FullMem c s' ⋆ R) mJ) ?_ ?_
      · rintro _ ⟨done', ⟨⟩⟩ mJ ⟨ar', rng', hsp', hperm_all, hm'⟩
        c0_hsplit
        · c0_hsteps; exact hQ done' ar' rng' mJ hsp' hperm_all hm'
        · c0_hsteps
          exact hLP (np32.setWidth 64, done', ()) mJ (by dsimp only; rw [hnp_eq]; omega)
            ⟨by rw [hnp_eq]; exact hnp_le, by rwa [hnp_eq], ar', rng', hsp', hperm_all, hm'⟩
      · intro J hJ
        c0_hsteps_nogrp; c0_call hTumble
        refine ⟨c, F0, F_cur, sP, R, rfl, hspP, by rwa [hp32], hmP, ?_⟩
        rintro ok ar' rng' m' s' hsp' hperm' hm'
        have hperm_all := fullArenaPermEq_trans hpermP hperm'
        c0_hsplit <;> (c0_hsteps; exact hJ _ m' ⟨ar', rng', hsp', hperm_all, hm'⟩)
    · c0_hsteps; exact hQ done arP rngP mP hspP hpermP hmP
  · c0_hsteps; exact hQ done arP rngP mP hspP hpermP hmP

theorem full_reorder_wp (Γ : Env)
    (hQueue : EnvSpec Γ "full_reorder_queue" fullReorderQueueSpec)
    (hHeap : EnvSpec Γ "full_reorder_heap" fullReorderHeapSpec)
    (hTumble : EnvSpec Γ "full_tumble_clauses" fullTumbleClausesSpec) :
    ∀ a m Q X, fullReorderSpec a m Q X → Func.wp Γ full_reorder_body a m Q X := by
  rintro ⟨h, budget, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp, hm, hQ⟩
  unfold Func.wp full_reorder_body
  c0_hsteps_nogrp; c0_call hQueue
  refine ⟨c, s, R, rfl, hsp.lengths, hm, ?_⟩
  rintro ⟨_, ⟨⟩⟩ s1 m1 hcore1 hlen1 hpres1 hm1
  change (FullMem c s1 ⋆ R) m1 at hm1
  have hsp1 := hsp.of_safetySlice hlen1 hcore1 hpres1
  have hce1 : s1.core = s.core := fullCoreState_agrees_with_scratch hcore1
  c0_hsteps_nogrp; c0_call hHeap
  refine ⟨c, s1, R, rfl, hlen1, hm1, ?_⟩
  rintro ⟨_, ⟨⟩⟩ s2 m2 hcore2 hlen2 hpres2 hm2
  change (FullMem c s2 ⋆ R) m2 at hm2
  have hsp2 := hsp1.of_safetySlice hlen2 hcore2 hpres2
  have hce2 : s2.core = s.core := (fullCoreState_agrees_with_scratch hcore2).trans hce1
  obtain ⟨F_cur, hspW2⟩ := hsp2.exists_witness
  c0_hsteps_nogrp; c0_call hTumble
  refine ⟨c, F0, F_cur, s2, R, rfl, hspW2, hm2, ?_⟩
  rintro r ar' rng' m3 s3 hspW3 hperm3 hm3
  c0_hsteps
  exact hQ r s3 m3 hspW3.toSparse (by simpa only [hce2] using hperm3) hm3

/-! ### 3.3 `ternary.c` (`full_ternary_match_bin` .. `full_ternary`) -/

theorem full_ternary_match_bin_wp (Γ : Env) :
    ∀ a m Q X, fullTernaryMatchBinSpec a m Q X →
      Func.wp Γ full_ternary_match_bin_body a m Q X := by
  rintro ⟨p, u, v, b0, b1, b2, ⟨⟩⟩ m Q X hQ
  unfold Func.wp full_ternary_match_bin_body
  c0_hsteps
  all_goals first
    | exact hQ false (fun h => by cases h)
    | exact hQ true fun _ => Or.inl ⟨by assumption, Or.inl ⟨by assumption, by assumption⟩⟩
    | exact hQ true fun _ => Or.inl ⟨by assumption, Or.inr ⟨by assumption, by assumption⟩⟩
    | exact hQ true fun _ => Or.inr (Or.inl ⟨by assumption, Or.inl ⟨by assumption, by assumption⟩⟩)
    | exact hQ true fun _ => Or.inr (Or.inl ⟨by assumption, Or.inr ⟨by assumption, by assumption⟩⟩)
    | exact hQ true fun _ => Or.inr (Or.inr ⟨by assumption, Or.inl ⟨by assumption, by assumption⟩⟩)
    | exact hQ true fun _ => Or.inr (Or.inr ⟨by assumption, Or.inr ⟨by assumption, by assumption⟩⟩)

theorem full_ternary_collect_wp (Γ : Env)
    (hNext : EnvSpec Γ "full_arena_next" Full.fullArenaNextSpec) :
    ∀ a m Q X, fullTernaryCollectSpec a m Q X → Func.wp Γ full_ternary_collect_body a m Q X := by
  rintro ⟨h, cap, ⟨⟩⟩ m Q X ⟨c, s, R, ⟨rfl, F0, hsp⟩, hlen, hm, hQ⟩
  change (FullMem c s ⋆ R) m at hm
  obtain ⟨F_cur, hspW⟩ := hsp.exists_witness
  have hcl := hlen.core_ok; have hsl := hlen.scratch_ok
  have har32 := fullInv_arena_cap_lt32 c; have hscr32 := fullInv_scratch_cap_lt32 c
  have hale := hcl.arena_len_le; have har_len := hcl.arena_len_arr
  have hscr_len := hsl.scratch_buf_len
  unfold Func.wp full_ternary_collect_body
  c0_hsteps_nogrp
  refine wp_join_group (fun (lim, ()) ml => lim.toNat ≤ c.scratch_cap ∧ m = ml) ?_ ?_
  · rintro _ ⟨lim, ⟨⟩⟩ ml ⟨hlim_le, rfl⟩
    c0_hsteps_nogrp; c0_hstep
    refine wp_loop_inv
      (fun (p, n, ()) mP =>
        n.toNat ≤ lim.toNat ∧ p.toNat ≤ s.core.arena_len ∧
        (p.toNat = s.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs s) ∧
        ∃ scrP : List (BitVec 32), scrP.length = c.scratch_cap ∧
          FullTernaryRefsOk { s with scratch := { s.scratch with scratch_buf := scrP } } n.toNat ∧
          (FullMem c { s with scratch := { s.scratch with scratch_buf := scrP } } ⋆ R) mP)
      (fun (p, _, ()) _ => s.core.arena_len - p.toNat)
      (fun JP hLP => by
        c0_hsteps
        refine hLP (0#64, 0#64, ()) m ⟨Nat.zero_le _, Nat.zero_le _, ?_, s.scratch.scratch_buf,
          hscr_len, ⟨Nat.zero_le _, fun _ hk => absurd hk (Nat.not_lt_zero _)⟩, hm⟩
        by_cases h0 : s.core.arena_len = 0
        · exact Or.inl h0.symm
        · exact Or.inr (fullArenaScanRefs_zero_mem hspW.2.1.arena.len_ok (Nat.pos_of_ne_zero h0)))
      (fun JP ⟨p, n, ⟨⟩⟩ mP ⟨hn_le, hp_le, hp_mem, scrP, hscrP_len, hrefsP, hmP⟩ hLP => ?_)
    let sP : FullState := { s with scratch := { s.scratch with scratch_buf := scrP } }
    have hlenP : sP.LengthsOk c := ⟨hlen.core_ok, { hsl with scratch_buf_len := hscrP_len }⟩
    c0_hsplit
    · have hp_lt : p.toNat < s.core.arena_len := by omega
      c0_hsplit
      · have hn_lt : n.toNat < lim.toNat := by c0_bound
        have hp_ref : p.toNat ∈ fullArenaClauseRefs s := hp_mem.resolve_left (by omega)
        have hp3_le : p.toNat + 3 ≤ s.core.arena_len := (hspW.2.1.arena.refs_wf p.toNat hp_ref).1
        have hp_ar : p.toNat < s.core.arena.length := by omega
        have hp2_ar : (p + 2#64).toNat < s.core.arena.length := by bv_omega
        c0_hsplit
        · c0_hsteps
          exact hQ (n, ()) sP mP rfl hlenP ⟨⟨scrP, rfl⟩, by omega, hrefsP⟩ hmP
        · let hdr := s.core.arena[p.toNat]'hp_ar
          let sz := s.core.arena[(p + 2#64).toNat]'hp2_ar
          have hp32 : (p.setWidth 32).toNat = p.toNat := by bv_omega
          c0_hsteps_nogrp; c0_call hNext
          refine ⟨c, sP, R, rfl, hlenP, hmP, ?_⟩
          obtain ⟨hnp_gt, hnp_le, hnp_mem⟩ := fullArenaClauseRefs_next_or_end hspW.2.1 hp_ref
          let np32 := BitVec.ofNat 32
            (fullArenaNextOff sP.core.arena sP.core.arena_len (p.setWidth 32).toNat)
          have hnp_eq : (np32.setWidth 64).toNat =
              fullArenaNextOff s.core.arena s.core.arena_len p.toNat := by
            dsimp only [np32, sP]; rw [hp32, zext_toNat _ (by decide), BitVec.toNat_ofNat,
              Nat.mod_eq_of_lt (by omega)]
          c0_hsteps_nogrp
          refine wp_join_group
            (fun (n', ()) mJ =>
              n'.toNat ≤ lim.toNat ∧
              ∃ scrJ : List (BitVec 32), scrJ.length = c.scratch_cap ∧
                FullTernaryRefsOk { s with scratch := { s.scratch with scratch_buf := scrJ } }
                  n'.toNat ∧
                (FullMem c { s with scratch := { s.scratch with scratch_buf := scrJ } } ⋆ R) mJ)
            ?_ ?_
          · rintro _ ⟨n', ⟨⟩⟩ mJ ⟨hn'_le, scrJ, hscrJ_len, hrefsJ, hmJ⟩
            c0_hsplit
            · c0_hsteps
              exact hQ (n', ()) { s with scratch := { s.scratch with scratch_buf := scrJ } } mJ
                rfl ⟨hlen.core_ok, { hsl with scratch_buf_len := hscrJ_len }⟩
                ⟨⟨scrJ, rfl⟩, by omega, hrefsJ⟩ hmJ
            · c0_hsteps
              exact hLP (np32.setWidth 64, n', ()) mJ (by dsimp only; rw [hnp_eq]; omega)
                ⟨hn'_le, by rw [hnp_eq]; exact hnp_le, by rwa [hnp_eq], scrJ, hscrJ_len,
                 hrefsJ, hmJ⟩
          · intro J hJ
            c0_hsplit
            · have hc_g := hc
              c0_hsplit
              · have hc_sz := hc
                simp only [show (2 : BitVec 64).toNat = 2 by rfl,
                  Nat.mod_eq_of_lt (show p.toNat + 2 < 2 ^ 64 by omega)] at hc_sz
                have hng : fullArenaClauseGarb s p.toNat = false := by
                  unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
                  rw [List.getElem?_eq_getElem hp_ar, Option.getD_some]
                  simp; exact hc_g
                have hsz3 : fullArenaClauseSize s p.toNat = 3 := by
                  unfold fullArenaClauseSize fullArenaClauseSizeCore
                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hc_sz]; rfl
                have hn1 : (n + 1#64).toNat = n.toNat + 1 := by bv_omega
                have hn_scr : n.toNat < scrP.length := by omega
                c0_hsteps
                refine hJ (n + 1#64, ()) _ ⟨by rw [hn1]; omega, scrP.set n.toNat (p.setWidth 32),
                  by simp [hscrP_len], ⟨by simp [hscrP_len, hn1]; omega, fun k hk => ?_⟩, hm⟩
                rw [hn1] at hk
                by_cases hkn : k = n.toNat
                · subst hkn; dsimp only
                  rw [List.getElem?_set_self hn_scr, Option.getD_some, hp32]
                  exact ⟨hp_ref, hng, hsz3⟩
                · dsimp only; rw [List.getElem?_set_ne (Ne.symm hkn)]
                  exact hrefsP.2 k (by omega)
              · c0_hsteps; exact hJ (n, ()) mP ⟨hn_le, scrP, hscrP_len, hrefsP, hmP⟩
            · c0_hsteps; exact hJ (n, ()) mP ⟨hn_le, scrP, hscrP_len, hrefsP, hmP⟩
      · c0_hsteps; exact hQ (n, ()) sP mP rfl hlenP ⟨⟨scrP, rfl⟩, by omega, hrefsP⟩ hmP
    · c0_hsteps; exact hQ (n, ()) sP mP rfl hlenP ⟨⟨scrP, rfl⟩, by omega, hrefsP⟩ hmP
  · intro J hJ
    c0_hsplit
    · c0_hsteps; exact hJ (cap, ()) m ⟨by omega, rfl⟩
    · c0_hsteps
      exact hJ (BitVec.ofNat 64 c.scratch_cap, ()) m
        ⟨by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact Nat.le_refl _, rfl⟩

theorem full_ternary_resolve_bin_wp (Γ : Env)
    (hMatch : EnvSpec Γ "full_ternary_match_bin" fullTernaryMatchBinSpec)
    (hAddBin : EnvSpec Γ "full_add_bin" Full.fullAddBinSpec) :
    ∀ a m Q X, fullTernaryResolveBinSpec a m Q X →
      Func.wp Γ full_ternary_resolve_bin_body a m Q X := by
  rintro ⟨h, c1, c2, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hsp, hcl0, hc1, hc2, hm, hQ⟩
  have hlen := hsp.1; have hw := hsp.2.1; have hcl := hlen.core_ok
  have har32 := fullInv_arena_cap_lt32 c; have hale := hcl.arena_len_le
  have har_len := hcl.arena_len_arr
  have hret0 : Q (0#64, ()) m :=
    hQ 0#64 s.core.vals s.core.flags s.core.lvl s.core.rsns s.core.trl s.core.trail_pos
      s.core.trail_end s.core.unassigned s.core.unflushed s.core.wvec s.core.wstk s.core.wlen
      s.core.wusable s.core.num_binary s.core.oom s.core.inconsistent s.scratch.phases
      s.scratch.wsort s.scratch.hbr_cnt m hsp (Or.inl rfl) (fun h => by cases h)
      (fun h => by cases h) hm
  unfold Func.wp full_ternary_resolve_bin_body
  c0_hsplit
  · c0_hsteps; exact hret0
  · c0_hsplit
    · c0_hsteps; exact hret0
    · c0_hsplit
      · c0_hsteps; exact hret0
      · have hfit1 : c1.toNat + 6 ≤ s.core.arena_len := by bv_omega
        have hfit2 : c2.toNat + 6 ≤ s.core.arena_len := by bv_omega
        have h1_0 : (c1.setWidth 64).toNat < s.core.arena.length := by bv_omega
        have h2_0 : (c2.setWidth 64).toNat < s.core.arena.length := by bv_omega
        c0_hsplit
        · c0_hsteps; exact hret0
        · have hc_g1 := hc
          c0_hsplit
          · c0_hsteps; exact hret0
          · have hc_g2 := hc
            have h1_2 : (c1.setWidth 64 + 2#64).toNat < s.core.arena.length := by bv_omega
            have h2_2 : (c2.setWidth 64 + 2#64).toNat < s.core.arena.length := by bv_omega
            c0_hsplit
            · c0_hsteps; exact hret0
            · have hc_s1 := hc
              simp only [show (2 : BitVec 64).toNat = 2 by rfl,
                Nat.mod_eq_of_lt (show c1.toNat + 2 < 2 ^ 64 by omega)] at hc_s1
              c0_hsplit
              · c0_hsteps; exact hret0
              · have hc_s2 := hc
                simp only [show (2 : BitVec 64).toNat = 2 by rfl,
                  Nat.mod_eq_of_lt (show c2.toNat + 2 < 2 ^ 64 by omega)] at hc_s2
                have hng1 : fullArenaClauseGarb s c1.toNat = false := by
                  unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; simp; exact hc_g1
                have hng2 : fullArenaClauseGarb s c2.toNat = false := by
                  unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some]; simp; exact hc_g2
                have hsz1 : fullArenaClauseSize s c1.toNat = 3 := by
                  unfold fullArenaClauseSize fullArenaClauseSizeCore
                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hc_s1]; rfl
                have hsz2 : fullArenaClauseSize s c2.toNat = 3 := by
                  unfold fullArenaClauseSize fullArenaClauseSizeCore
                  rw [List.getElem?_eq_getElem (by omega), Option.getD_some, hc_s2]; rfl
                have h1_3 : (c1.setWidth 64 + 3#64).toNat < s.core.arena.length := by bv_omega
                have h1_4 : (c1.setWidth 64 + 4#64).toNat < s.core.arena.length := by bv_omega
                have h1_5 : (c1.setWidth 64 + 5#64).toNat < s.core.arena.length := by bv_omega
                have h2_3 : (c2.setWidth 64 + 3#64).toNat < s.core.arena.length := by bv_omega
                have h2_4 : (c2.setWidth 64 + 4#64).toNat < s.core.arena.length := by bv_omega
                have h2_5 : (c2.setWidth 64 + 5#64).toNat < s.core.arena.length := by bv_omega
                let a0 := s.core.arena[(c1.setWidth 64 + 3#64).toNat]'h1_3
                let a1 := s.core.arena[(c1.setWidth 64 + 4#64).toNat]'h1_4
                let a2 := s.core.arena[(c1.setWidth 64 + 5#64).toNat]'h1_5
                let b0 := s.core.arena[(c2.setWidth 64 + 3#64).toNat]'h2_3
                let b1 := s.core.arena[(c2.setWidth 64 + 4#64).toNat]'h2_4
                let b2 := s.core.arena[(c2.setWidth 64 + 5#64).toNat]'h2_5
                have hent1 : (cnfOfClauses F_cur).EntailsClause
                    (cnfClause [a0.toNat, a1.toNat, a2.toNat]) := by
                  have hl := fullArenaClauseLits_eq3 hsz1 (by omega)
                  have he := hw.arena.entails c1.toNat hc1 hng1
                  have e3 : (c1.setWidth 64 + 3#64).toNat = c1.toNat + 3 := by bv_omega
                  have e4 : (c1.setWidth 64 + 4#64).toNat = c1.toNat + 4 := by bv_omega
                  have e5 : (c1.setWidth 64 + 5#64).toNat = c1.toNat + 5 := by bv_omega
                  simpa only [a0, a1, a2, e3, e4, e5, hl] using he
                have hent2 : (cnfOfClauses F_cur).EntailsClause
                    (cnfClause [b0.toNat, b1.toNat, b2.toNat]) := by
                  have hl := fullArenaClauseLits_eq3 hsz2 (by omega)
                  have he := hw.arena.entails c2.toNat hc2 hng2
                  have e3 : (c2.setWidth 64 + 3#64).toNat = c2.toNat + 3 := by bv_omega
                  have e4 : (c2.setWidth 64 + 4#64).toNat = c2.toNat + 4 := by bv_omega
                  have e5 : (c2.setWidth 64 + 5#64).toNat = c2.toNat + 5 := by bv_omega
                  simpa only [b0, b1, b2, e3, e4, e5, hl] using he
                have hperm1_102 : (cnfOfClauses F_cur).EntailsClause
                    (cnfClause [a1.toNat, a0.toNat, a2.toNat]) :=
                  entails_of_mem_or_false hent1 fun l hl => by
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl ⊢
                    rcases hl with rfl | rfl | rfl <;> simp
                have hperm1_201 : (cnfOfClauses F_cur).EntailsClause
                    (cnfClause [a2.toNat, a0.toNat, a1.toNat]) :=
                  entails_of_mem_or_false hent1 fun l hl => by
                    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl ⊢
                    rcases hl with rfl | rfl | rfl <;> simp
                c0_hsteps_nogrp
                refine wp_join_group
                  (fun (found, u, v, ()) mJ => m = mJ ∧
                    (found = true → (cnfOfClauses F_cur).EntailsClause
                      (cnfClause [u.toNat, v.toNat]))) ?_ ?_
                · rintro _ ⟨found, u, v, ⟨⟩⟩ mJ ⟨rfl, hent_uv⟩
                  c0_hsplit
                  · have huv := hent_uv hc
                    c0_hsteps_nogrp; c0_call hAddBin
                    refine ⟨c, F0, F_cur, s, R, rfl, hlen, hw, hcl0, fun _ _ => huv, hm, ?_⟩
                    rintro st vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk'
                      wlen' wu' nb' oom' inc' phases' wsort' m' s' hlen' hw' hdom h20 h2 hm'
                    have hsp' : FullSparseInvW c F0 F_cur s' :=
                      fullSparseInvW_of_same_arena hsp hlen' hw' rfl rfl rfl rfl rfl ⟨rfl, rfl⟩
                    c0_hstep; c0_hsplit
                    · c0_hsteps
                      exact hQ st vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk'
                        wlen' wu' nb' oom' inc' phases' wsort' (s.scratch.hbr_cnt + 1#64) _
                        (fullSparseInvW_with_scratch hsp'
                          (by cases hlen'.scratch_ok; constructor <;> assumption) rfl rfl)
                        hdom h20 h2 hm
                    · c0_hsteps
                      exact hQ st vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk'
                        wlen' wu' nb' oom' inc' phases' wsort' s.scratch.hbr_cnt m'
                        hsp' hdom h20 h2 hm'
                  · c0_hsteps; exact hret0
                · intro Jout hJout
                  have toNat_match : ∀ {p u v : BitVec 32},
                      let np := p ^^^ 1#32
                      ((b0 = np ∧ ((b1 = u ∧ b2 = v) ∨ (b1 = v ∧ b2 = u))) ∨
                       (b1 = np ∧ ((b0 = u ∧ b2 = v) ∨ (b0 = v ∧ b2 = u))) ∨
                       (b2 = np ∧ ((b0 = u ∧ b1 = v) ∨ (b0 = v ∧ b1 = u)))) →
                      ((b0.toNat = p.toNat ^^^ 1 ∧
                          ((b1.toNat = u.toNat ∧ b2.toNat = v.toNat) ∨
                           (b1.toNat = v.toNat ∧ b2.toNat = u.toNat))) ∨
                       (b1.toNat = p.toNat ^^^ 1 ∧
                          ((b0.toNat = u.toNat ∧ b2.toNat = v.toNat) ∨
                           (b0.toNat = v.toNat ∧ b2.toNat = u.toNat))) ∨
                       (b2.toNat = p.toNat ^^^ 1 ∧
                          ((b0.toNat = u.toNat ∧ b1.toNat = v.toNat) ∨
                           (b0.toNat = v.toNat ∧ b1.toNat = u.toNat)))) := by
                    intro p u v np hmt
                    rcases hmt with ⟨h0, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ |
                      ⟨h0, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ | ⟨h0, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
                    · exact Or.inl ⟨(by rw [h0]; exact bv32_xor1_toNat p),
                        Or.inl ⟨congrArg BitVec.toNat h1, congrArg BitVec.toNat h2⟩⟩
                    · exact Or.inl ⟨(by rw [h0]; exact bv32_xor1_toNat p),
                        Or.inr ⟨congrArg BitVec.toNat h1, congrArg BitVec.toNat h2⟩⟩
                    · exact Or.inr (Or.inl ⟨(by rw [h0]; exact bv32_xor1_toNat p),
                        Or.inl ⟨congrArg BitVec.toNat h1, congrArg BitVec.toNat h2⟩⟩)
                    · exact Or.inr (Or.inl ⟨(by rw [h0]; exact bv32_xor1_toNat p),
                        Or.inr ⟨congrArg BitVec.toNat h1, congrArg BitVec.toNat h2⟩⟩)
                    · exact Or.inr (Or.inr ⟨(by rw [h0]; exact bv32_xor1_toNat p),
                        Or.inl ⟨congrArg BitVec.toNat h1, congrArg BitVec.toNat h2⟩⟩)
                    · exact Or.inr (Or.inr ⟨(by rw [h0]; exact bv32_xor1_toNat p),
                        Or.inr ⟨congrArg BitVec.toNat h1, congrArg BitVec.toNat h2⟩⟩)
                  c0_call hMatch; intro ok0 hok0
                  c0_hsplit
                  · c0_hsteps
                    exact hJout (true, a1, a2, ()) m ⟨rfl, fun _ =>
                      hyperTernary_resolve_bin_entails hent1 hent2 (toNat_match (hok0 hc))⟩
                  · c0_hsteps_nogrp; c0_hstep; c0_call hMatch; intro ok1 hok1
                    c0_hsplit
                    · c0_hsteps
                      exact hJout (true, a0, a2, ()) m ⟨rfl, fun _ =>
                        hyperTernary_resolve_bin_entails hperm1_102 hent2 (toNat_match (hok1 hc))⟩
                    · c0_hsteps_nogrp; c0_hstep; c0_call hMatch; intro ok2 hok2
                      c0_hsplit
                      · c0_hsteps
                        exact hJout (true, a0, a1, ()) m ⟨rfl, fun _ =>
                          hyperTernary_resolve_bin_entails hperm1_201 hent2
                            (toNat_match (hok2 hc))⟩
                      · c0_hsteps
                        exact hJout (false, 0#32, 0#32, ()) m ⟨rfl, fun h => by cases h⟩

theorem full_ternary_round_wp (Γ : Env)
    (hRes : EnvSpec Γ "full_ternary_resolve_bin" fullTernaryResolveBinSpec)
    (hProp : EnvSpec Γ "full_propagate" Full.fullPropagateSpec) :
    ∀ a m Q X, fullTernaryRoundSpec a m Q X → Func.wp Γ full_ternary_round_body a m Q X := by
  rintro ⟨h, n, budget, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hsp, hcl0, hn_le, hrefs, hm, hQ⟩
  have hscr32 := fullInv_scratch_cap_lt32 c
  unfold Func.wp full_ternary_round_body
  c0_hsteps_nogrp
  refine wp_loop_inv
    (fun (ticks, added, i, ()) mI =>
      i.toNat ≤ n.toNat ∧ ticks.toNat ≤ budget.toNat ∧
      ∃ sI : FullState,
        FullSparseInvW c F0 F_cur sI ∧ sI.core.cur_level = 0 ∧
        sI.core.fuel.toNat ≤ s.core.fuel.toNat ∧ FullTernaryRefsOk sI n.toNat ∧
        (FullMem c sI ⋆ R) mI)
    (fun (_, _, i, ()) _ => n.toNat - i.toNat)
    (fun JI hLI => by
      c0_hsteps
      exact hLI (0#64, 0#64, 0#64, ()) m ⟨Nat.zero_le _, Nat.zero_le _, s, hsp, hcl0,
        Nat.le_refl _, hrefs, hm⟩)
    (fun JI ⟨ticks, added, i, ⟨⟩⟩ mI ⟨hi_le, htk_le, sI, hspI, hclI, hfuI, hrefsI, hmI⟩ hLI => ?_)
  refine wp_join_group (fun () mE => mI = mE) ?_ ?_
  · rintro _ ⟨⟩ mE rfl
    c0_hsteps <;> exact hQ _ sI mI hspI hclI hfuI (by simp) (fun h => by cases h) hmI
  · intro JE hJE
    c0_hsplit
    · have hi_lt : i.toNat < n.toNat := by c0_bound
      c0_hsplit
      · c0_hsplit
        · c0_hsplit
          · have hi1 : (i + 1#64).toNat = i.toNat + 1 := by bv_omega
            c0_hsteps_nogrp
            refine wp_loop_inv
              (fun (ticksJ, addedJ, j, ()) mJ =>
                j.toNat ≤ n.toNat ∧ ticksJ.toNat ≤ budget.toNat ∧
                ∃ sJ : FullState,
                  FullSparseInvW c F0 F_cur sJ ∧ sJ.core.cur_level = 0 ∧
                  sJ.core.fuel.toNat ≤ s.core.fuel.toNat ∧ FullTernaryRefsOk sJ n.toNat ∧
                  (FullMem c sJ ⋆ R) mJ)
              (fun (_, _, j, ()) _ => n.toNat - j.toNat)
              (fun JJ hLJ => by
                c0_hsteps
                exact hLJ (ticks, added, i + 1#64, ()) mI ⟨by rw [hi1]; omega, htk_le, sI, hspI,
                  hclI, hfuI, hrefsI, hmI⟩)
              (fun JJ ⟨ticksJ, addedJ, j, ⟨⟩⟩ mJ ⟨hj_le, htkJ_le, sJ, hspJ, hclJ, hfuJ, hrefsJ, hmJ⟩
                  hLJ => ?_)
            refine wp_join_group (fun () mK => mJ = mK) ?_ ?_
            · rintro _ ⟨⟩ mK rfl
              c0_hsteps
              exact hLI (ticksJ, addedJ, i + 1#64, ()) mJ (by dsimp only; rw [hi1]; omega)
                ⟨by rw [hi1]; omega, htkJ_le, sJ, hspJ, hclJ, hfuJ, hrefsJ, hmJ⟩
            · intro JK hJK
              c0_hsplit
              · have hj_lt : j.toNat < n.toNat := by c0_bound
                c0_hsplit
                · have htkJ_lt : ticksJ.toNat < budget.toNat := by c0_bound
                  have htk1 : (ticksJ + 1#64).toNat = ticksJ.toNat + 1 := by bv_omega
                  have hj1 : (j + 1#64).toNat = j.toNat + 1 := by bv_omega
                  c0_hsplit
                  · c0_hsplit
                    · have hi_scr : i.toNat < sJ.scratch.scratch_buf.length := by
                        have := hrefsJ.1; omega
                      have hj_scr : j.toNat < sJ.scratch.scratch_buf.length := by
                        have := hrefsJ.1; omega
                      have hci_ref : (sJ.scratch.scratch_buf[i.toNat]'hi_scr).toNat ∈
                          fullArenaClauseRefs sJ := by
                        have := (hrefsJ.2 i.toNat hi_lt).1
                        rwa [List.getElem?_eq_getElem hi_scr, Option.getD_some] at this
                      have hcj_ref : (sJ.scratch.scratch_buf[j.toNat]'hj_scr).toNat ∈
                          fullArenaClauseRefs sJ := by
                        have := (hrefsJ.2 j.toNat hj_lt).1
                        rwa [List.getElem?_eq_getElem hj_scr, Option.getD_some] at this
                      c0_hsteps_nogrp; c0_call hRes
                      refine ⟨c, F0, F_cur, sJ, R, rfl, hspJ, hclJ, hci_ref, hcj_ref, hmJ, ?_⟩
                      rintro st vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk'
                        wlen' wu' nb' oom' inc' phases' wsort' hbr' m1 s1 hsp1 hdom1 h20_1 _ hm1
                      have hrefs1 : FullTernaryRefsOk s1 n.toNat :=
                        fullTernaryRefsOk_of_same_arena hrefsJ rfl rfl rfl
                      c0_hsplit
                      · c0_hsteps
                        exact hQ 20#64 s1 m1 hsp1 hclJ hfuJ (Or.inr (Or.inr (Or.inr rfl)))
                          (fun _ => (h20_1 hc).1) hm1
                      · c0_hsplit
                        · c0_hsteps
                          exact hQ 2#64 s1 m1 hsp1 hclJ hfuJ (Or.inr (Or.inr (Or.inl rfl)))
                            (fun h => by cases h) hm1
                        · c0_hstep; c0_hsplit
                          · c0_hsteps_nogrp; c0_call hProp
                            refine ⟨c, F0, F_cur, s1, R, rfl, hsp1.1, hsp1.2.1, hsp1.2.2.2.2.2,
                              hm1, ?_⟩
                            rintro ps vals2 flags2 lvl2 rsns2 trl2 tp2 te2 prop2 unass2 unfl2
                              wvec2 ar2 wstk2 wlen2 wu2 fuel2 ctype2 cref2 c0_2 c1_2 oom2 ticks2
                              wsort2 phases2 m2 s2 hlen2 hw2 _ hperm2 hfu2_le _ _ hps1 _ _ hm2
                            have hsp2 : FullSparseInvW c F0 F_cur s2 :=
                              fullSparseInvW_of_perm hsp1 hlen2 hw2 hperm2 rfl rfl rfl ⟨rfl, rfl⟩
                            have hrefs2 : FullTernaryRefsOk s2 n.toNat :=
                              fullTernaryRefsOk_of_perm hrefs1 rfl hperm2
                            have hfu2 : s2.core.fuel.toNat ≤ s.core.fuel.toNat :=
                              Nat.le_trans hfu2_le hfuJ
                            c0_hsplit
                            · have hconf := (hps1 hc).2.2
                              c0_hsteps
                              exact hQ 20#64
                                { s2 with core := { s2.core with inconsistent := 1#64 } } _
                                (fullSparseInvW_with_inconsistent hsp2
                                  (level0_fcur_unsat_of_conflict_okW hw2 hclJ hconf) 1#64)
                                hclJ hfu2 (Or.inr (Or.inr (Or.inr rfl)))
                                (fun _ => level0_unsat_of_conflict_okW hw2 hclJ hconf) hm
                            · c0_hsplit
                              · c0_hsteps
                                exact hQ 2#64 s2 m2 hsp2 hclJ hfu2 (Or.inr (Or.inr (Or.inl rfl)))
                                  (fun h => by cases h) hm2
                              · c0_hsteps
                                exact hLJ (ticksJ + 1#64, addedJ + 1#64, j + 1#64, ()) m2
                                  (by dsimp only; rw [hj1]; omega)
                                  ⟨by rw [hj1]; omega, by rw [htk1]; omega, s2, hsp2, hclJ, hfu2,
                                   hrefs2, hm2⟩
                          · c0_hsteps
                            exact hLJ (ticksJ + 1#64, addedJ, j + 1#64, ()) m1
                              (by dsimp only; rw [hj1]; omega)
                              ⟨by rw [hj1]; omega, by rw [htk1]; omega, s1, hsp1, hclJ, hfuJ,
                               hrefs1, hm1⟩
                    · c0_hsteps; exact hJK () mJ rfl
                  · c0_hsteps; exact hJK () mJ rfl
                · c0_hsteps; exact hJK () mJ rfl
              · c0_hsteps; exact hJK () mJ rfl
          · c0_hsteps; exact hJE () mI rfl
        · c0_hsteps; exact hJE () mI rfl
      · c0_hsteps; exact hJE () mI rfl
    · c0_hsteps; exact hJE () mI rfl

theorem full_ternary_wp (Γ : Env)
    (hBt : EnvSpec Γ "full_backtrack" Full.fullBacktrackSpec)
    (hProp : EnvSpec Γ "full_propagate" Full.fullPropagateSpec)
    (hCol : EnvSpec Γ "full_ternary_collect" fullTernaryCollectSpec)
    (hRnd : EnvSpec Γ "full_ternary_round" fullTernaryRoundSpec) :
    ∀ a m Q X, fullTernarySpec a m Q X → Func.wp Γ full_ternary_body a m Q X := by
  rintro ⟨h, rounds, budget, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hsp, hm, hQ⟩
  obtain ⟨F_cur, hspW⟩ := hsp.exists_witness
  have hmax32 := fullInv_max_vars_lt32 c
  unfold Func.wp full_ternary_body
  c0_hsplit
  · c0_hsteps
    exact hQ 20#64 s m hsp (Nat.le_refl _) (Or.inr rfl)
      (fun _ => hsp.inconsistent_unsat (by assumption)) (fun h => by cases h) hm
  · refine wp_join_group
      (fun () m0 => ∃ s0 : FullState,
        FullSparseInvW c F0 F_cur s0 ∧ s0.core.cur_level = 0 ∧
        s0.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c s0 ⋆ R) m0) ?_ ?_
    · rintro _ ⟨⟩ m0 ⟨s0, hsp0, hcl0, hfu0, hm0⟩
      c0_hsteps_nogrp; c0_call hProp
      refine ⟨c, F0, F_cur, s0, R, rfl, hsp0.1, hsp0.2.1, hsp0.2.2.2.2.2, hm0, ?_⟩
      rintro p0 vals1 flags1 lvl1 rsns1 trl1 tp1 te1 prop1 unass1 unfl1 wvec1 ar1 wstk1 wlen1
        wu1 fuel1 ctype1 cref1 c0_1 c1_1 oom1 ticks1 wsort1 phases1 m1 s1 hlen1 hw1 _ hperm1
        hfu1_le _ _ hp0_1 _ _ hm1
      have hsp1 : FullSparseInvW c F0 F_cur s1 :=
        fullSparseInvW_of_perm hsp0 hlen1 hw1 hperm1 rfl rfl rfl ⟨rfl, rfl⟩
      have hfu1 : s1.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfu1_le hfu0
      c0_hsplit
      · have hconf := (hp0_1 hc).2.2
        c0_hsteps
        exact hQ 20#64 { s1 with core := { s1.core with inconsistent := 1#64 } } _
          (fullSparseInvW_with_inconsistent hsp1
            (level0_fcur_unsat_of_conflict_okW hw1 hcl0 hconf) 1#64).toSparse
          hfu1 (Or.inr rfl) (fun _ => level0_unsat_of_conflict_okW hw1 hcl0 hconf)
          (fun h => by cases h) hm
      · c0_hsplit
        · c0_hsteps
          exact hQ 1#64 s1 m1 hsp1.toSparse hfu1 (Or.inl rfl) (fun h => by cases h)
            (fun _ => hcl0) hm1
        · c0_hsteps_nogrp; c0_hstep
          refine wp_loop_inv
            (fun (round, ()) mR =>
              round.toNat ≤ rounds.toNat ∧
              ∃ sR : FullState,
                FullSparseInvW c F0 F_cur sR ∧ sR.core.cur_level = 0 ∧
                sR.core.fuel.toNat ≤ s.core.fuel.toNat ∧ (FullMem c sR ⋆ R) mR)
            (fun (round, ()) _ => rounds.toNat - round.toNat)
            (fun JR hLR => by
              c0_hsteps; exact hLR (0#64, ()) m1 ⟨Nat.zero_le _, s1, hsp1, hcl0, hfu1, hm1⟩)
            (fun JR ⟨round, ⟨⟩⟩ mR ⟨hr_le, sR, hspR, hclR, hfuR, hmR⟩ hLR => ?_)
          c0_hsplit
          · have hr_lt : round.toNat < rounds.toNat := by c0_bound
            have hr1 : (round + 1#64).toNat = round.toNat + 1 := by bv_omega
            c0_hsplit
            · c0_hsplit
              · c0_hsteps_nogrp; c0_call hCol
                refine ⟨c, sR, R, ⟨rfl, F0, hspR.toSparse⟩, hspR.1, hmR, ?_⟩
                rintro ⟨n, ⟨⟩⟩ sC mC hcoreC hlenC ⟨⟨scrC, hscC⟩, hn_le, hrefsC⟩ hmC
                change (FullMem c sC ⋆ R) mC at hmC
                have hceC : sC.core = sR.core := fullCoreState_agrees_with_scratch hcoreC
                have hsC_eq : sC =
                    { sR with scratch := { sR.scratch with scratch_buf := scrC } } := by
                  cases sC; simp only at hceC hscC; subst hceC; subst hscC; rfl
                have hspC : FullSparseInvW c F0 F_cur sC := by
                  rw [hsC_eq]
                  exact fullSparseInvW_with_scratch hspR (hsC_eq ▸ hlenC).scratch_ok rfl rfl
                c0_hsplit
                · c0_hsteps
                  exact hQ 1#64 sC mC hspC.toSparse (by rw [hceC]; exact hfuR) (Or.inl rfl)
                    (fun h => by cases h) (fun _ => by rw [hceC]; exact hclR) hmC
                · c0_hsteps_nogrp; c0_call hRnd
                  refine ⟨c, F0, F_cur, sC, R, rfl, hspC, by rw [hceC]; exact hclR, hn_le, hrefsC,
                    hmC, ?_⟩
                  rintro st sD mD hspD hclD hfuD_le _ h20D hmD
                  have hfuD : sD.core.fuel.toNat ≤ s.core.fuel.toNat :=
                    Nat.le_trans hfuD_le (by rw [hceC]; exact hfuR)
                  c0_hsplit
                  · c0_hsteps
                    exact hQ 20#64 sD mD hspD.toSparse hfuD (Or.inr rfl)
                      (fun _ => h20D hc) (fun h => by cases h) hmD
                  · c0_hsplit
                    · c0_hsteps
                      exact hQ 1#64 sD mD hspD.toSparse hfuD (Or.inl rfl) (fun h => by cases h)
                        (fun _ => hclD) hmD
                    · c0_hsteps
                      exact hLR (round + 1#64, ()) mD (by dsimp only; rw [hr1]; omega)
                        ⟨by rw [hr1]; omega, sD, hspD, hclD, hfuD, hmD⟩
              · c0_hsteps
                exact hQ 1#64 sR mR hspR.toSparse hfuR (Or.inl rfl) (fun h => by cases h)
                  (fun _ => hclR) hmR
            · c0_hsteps
              exact hQ 1#64 sR mR hspR.toSparse hfuR (Or.inl rfl) (fun h => by cases h)
                (fun _ => hclR) hmR
          · c0_hsteps
            exact hQ 1#64 sR mR hspR.toSparse hfuR (Or.inl rfl) (fun h => by cases h)
              (fun _ => hclR) hmR
    · intro J hJ
      have hcl_le : s.core.cur_level ≤ c.max_vars :=
        Nat.le_trans hspW.2.1.cur_level_le
          (Nat.le_trans hspW.1.core_ok.trail_end_le hspW.1.core_ok.cur_vars_le)
      c0_hsplit
      · have hcl_pos : 0 < s.core.cur_level := by bv_omega
        c0_hsteps_nogrp; c0_call hBt
        refine ⟨c, s, R, rfl, hspW.1, by omega, fun _ => by omega, hspW.2.1.trail_lits_lt, hm, ?_⟩
        rintro vals' lvl' rsns' trl' tp' te' prop' cl' unass' sc' m' s0 hlen' _ _ hcl' hpr' _ _ _
          hw' _ hm'
        have hsp0 : FullSparseInvW c F0 F_cur s0 :=
          fullSparseInvW_of_same_arena hspW hlen' (hw' F0 F_cur hspW.2.1 (Nat.zero_le _))
            rfl rfl rfl rfl rfl hpr'.1
        c0_hsteps; exact hJ () m' ⟨s0, hsp0, by simpa using hcl', Nat.le_refl _, hm'⟩
      · c0_hsteps; exact hJ () m ⟨s, hspW, by bv_omega, Nat.le_refl _, hm⟩

end Proofs

/-! ## 4. Closed `SpecEntry.Impl` Packaging & `ModuleOk m4TernaryEnv fullM4TernaryModule` -/

theorem m4TernaryEnv_row {nm : String} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m4TernarySpecTable)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False)) :
    EnvSpec m4TernaryEnv nm sp :=
  fun xs m Q X hs =>
    Env.ofTable_of_mem (e := ⟨nm, as, bs, sp, true⟩) hmem m4TernarySpecTable_nodup
      (hno xs m Q X hs)

private theorem m4Ternary_allFns_wf : AllFns Fn.Wf fullM4TernaryModule.fns :=
  ⟨full_compute_lbd_wf, full_promote_clause_wf, full_promote_reasons_wf,
   full_score_sift_wf, full_reorder_queue_wf, full_reorder_heap_wf,
   full_tumble_clause_wf, full_tumble_clauses_wf, full_reorder_wf,
   full_ternary_match_bin_wf, full_ternary_collect_wf, full_ternary_resolve_bin_wf,
   full_ternary_round_wf, full_ternary_wf, trivial⟩

local macro "m4t_row" "(" h:term ")" : term =>
  `(m4TernaryEnv_row $h (fun _ _ _ _ h => h))

theorem m4t_promote_clause_impl :
    SpecEntry.Impl m4TernaryEnv
      ⟨"full_promote_clause", [i64, i32], [.bool], full_promote_clause_body⟩
      ⟨"full_promote_clause", [i64, i32], [.bool], fullPromoteClauseSpec, true⟩ :=
  SpecEntry.Impl.of (full_promote_clause_wp m4TernaryEnv (m4t_row (by simp [m4TernarySpecTable])))

theorem m4t_promote_reasons_impl :
    SpecEntry.Impl m4TernaryEnv
      ⟨"full_promote_reasons", [i64], [i64], full_promote_reasons_body⟩
      ⟨"full_promote_reasons", [i64], [i64], fullPromoteReasonsSpec, true⟩ :=
  SpecEntry.Impl.of (full_promote_reasons_wp m4TernaryEnv (m4t_row (by simp [m4TernarySpecTable])))

theorem m4t_reorder_impl :
    SpecEntry.Impl m4TernaryEnv
      ⟨"full_reorder", [i64, i64], [i64], full_reorder_body⟩
      ⟨"full_reorder", [i64, i64], [i64], fullReorderSpec, true⟩ :=
  SpecEntry.Impl.of (full_reorder_wp m4TernaryEnv
    (m4t_row (by simp [m4TernarySpecTable])) (m4t_row (by simp [m4TernarySpecTable]))
    (m4t_row (by simp [m4TernarySpecTable])))

theorem m4t_ternary_resolve_bin_impl :
    SpecEntry.Impl m4TernaryEnv
      ⟨"full_ternary_resolve_bin", [i64, i32, i32], [i64], full_ternary_resolve_bin_body⟩
      ⟨"full_ternary_resolve_bin", [i64, i32, i32], [i64], fullTernaryResolveBinSpec, true⟩ :=
  SpecEntry.Impl.of (full_ternary_resolve_bin_wp m4TernaryEnv
    (m4t_row (by simp [m4TernarySpecTable])) (m4t_row (by simp [m4TernarySpecTable])))

theorem m4t_ternary_impl :
    SpecEntry.Impl m4TernaryEnv
      ⟨"full_ternary", [i64, i64, i64], [i64], full_ternary_body⟩
      ⟨"full_ternary", [i64, i64, i64], [i64], fullTernarySpec, true⟩ :=
  SpecEntry.Impl.of (full_ternary_wp m4TernaryEnv
    (m4t_row (by simp [m4TernarySpecTable])) (m4t_row (by simp [m4TernarySpecTable]))
    (m4t_row (by simp [m4TernarySpecTable])) (m4t_row (by simp [m4TernarySpecTable])))

theorem m4Ternary_tableImpl :
    TableImpl m4TernaryEnv fullM4TernaryModule.fns m4TernarySpecTable :=
  ⟨SpecEntry.Impl.of (full_compute_lbd_wp m4TernaryEnv),
   m4t_promote_clause_impl, m4t_promote_reasons_impl,
   SpecEntry.Impl.of (full_score_sift_wp m4TernaryEnv),
   SpecEntry.Impl.of (full_reorder_queue_wp m4TernaryEnv (m4t_row (by simp [m4TernarySpecTable]))),
   SpecEntry.Impl.of (full_reorder_heap_wp m4TernaryEnv (m4t_row (by simp [m4TernarySpecTable]))),
   SpecEntry.Impl.of (full_tumble_clause_wp m4TernaryEnv (m4t_row (by simp [m4TernarySpecTable]))),
   SpecEntry.Impl.of (full_tumble_clauses_wp m4TernaryEnv
     (m4t_row (by simp [m4TernarySpecTable])) (m4t_row (by simp [m4TernarySpecTable]))),
   m4t_reorder_impl,
   SpecEntry.Impl.of (full_ternary_match_bin_wp m4TernaryEnv),
   SpecEntry.Impl.of (full_ternary_collect_wp m4TernaryEnv
     (m4t_row (by simp [m4TernarySpecTable]))),
   m4t_ternary_resolve_bin_impl,
   SpecEntry.Impl.of (full_ternary_round_wp m4TernaryEnv
     (m4t_row (by simp [m4TernarySpecTable])) (m4t_row (by simp [m4TernarySpecTable]))),
   m4t_ternary_impl, trivial⟩

/-- Unconditional `ModuleOk` certifying all `14/14` functions of `fullM4TernaryModule`. -/
theorem m4TernaryEnv_moduleOk : ModuleOk m4TernaryEnv fullM4TernaryModule :=
  Env.ofTable_moduleOk fullM4Ternary_acyclic m4Ternary_allFns_wf m4Ternary_tableImpl

/-! ## 5. Concrete `2128`-Byte `Mem 64` Sparse-Mode UNSAT Non-Vacuity (`XPost := False`) -/

def nvM4TernaryClauses : List (List Nat) := [[0, 2, 4], [1, 2, 4], [3], [5]]

def nvM4TernaryF0 : CNF Nat := cnfOfClauses nvM4TernaryClauses

theorem nvM4TernaryF0_unsat : nvM4TernaryF0.Unsat := by
  intro α; cases hα : CNF.eval α nvM4TernaryF0
  · rfl
  · exfalso
    have hall := (cnf_sat_cnfOfClauses_iff α nvM4TernaryClauses).mp hα
    have h1 := (clause_sat_cnfClause_iff α [0, 2, 4]).mp (hall _ (by simp [nvM4TernaryClauses]))
    have h2 := (clause_sat_cnfClause_iff α [1, 2, 4]).mp (hall _ (by simp [nvM4TernaryClauses]))
    have h3 := (sat_cnfClause_singleton α 3).mp (hall _ (by simp [nvM4TernaryClauses]))
    have h4 := (sat_cnfClause_singleton α 5).mp (hall _ (by simp [nvM4TernaryClauses]))
    simp [litVar, litSign] at h3 h4
    obtain ⟨l1, hm1, he1⟩ := h1; obtain ⟨l2, hm2, he2⟩ := h2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm1 hm2
    rcases hm1 with rfl | rfl | rfl <;> simp [litVar, litSign] at he1
    · rcases hm2 with rfl | rfl | rfl <;> simp [litVar, litSign] at he2 <;> simp_all
    · simp_all
    · simp_all

def nvM4TernaryCfg : FullCfg where
  hdr := 0x1000#64; avail := 2128; mv := 3; max_vars := 3; bva_cap := 0; nc := 4
  arena_cap := 12; wcap := 4; delayed_cap := 0; red_cap := 0; extend_cap := 0; scratch_cap := 4
  hbva := rfl; hmv := (by decide); hmaxv := (by decide); hnc := (by decide)
  harena := (by decide); hwcap := (by decide); hdel := (by decide); hred := (by decide)
  hext := (by decide); hscr := (by decide); havail_fit := (by decide); hsize := (by decide)

def nvM4TernaryScratch : FullScratch where
  heap_len := 0; scinc := 0#64; rel_period := 0#64; rel_limit := 0#64; rel_wait := 0#64
  rel_u := 0#64; rel_v := 0#64; rel_trigger := 0#64; conflicts := 0#64; learned_lits := 0#64
  min_removed := 0#64; delayed_len := 0; stable := 0#64; switched := 0#64; mode_count := 0#64
  mode_confl_lim := 0#64; mode_tick_lim := 0#64; mode_saved_ticks := 0#64; search_ticks := 0#64
  q_first := 0#64; q_last := 0#64; q_search_idx := 0#64; q_search_stamp := 0#64
  q_cur_stamp := 0#64; target_assigned := 0#64; best_assigned := 0#64; rephase_limit := 0#64
  rephased := 0#64; reduce_limit := 0#64; reductions := 0#64; tier1 := 2#64; tier2 := 6#64
  restarts := 0#64; restart_limit := 0#64; ema_fast_biased := 0#64; ema_fast_exp := 0#64
  ema_slow_biased := 0#64; ema_slow_exp := 0#64; extend_len := 0; rng_state := 1#64
  chrono_levels := 0#64; otfs_cnt := 0#64; eager_sub_cnt := 0#64; probe_limit := 0#64
  probings := 0#64; elim_limit := 0#64; eliminations := 0#64; elim_bound := 0#64
  iterating := 0#64; hbr_cnt := 0#64; trans_cnt := 0#64; viv_cnt := 0#64; subst_cnt := 0#64
  cong_cnt := 0#64; sweep_cnt := 0#64; bve_cnt := 0#64; bce_cnt := 0#64; bva_cnt := 0#64
  walk_cnt_stat := 0#64; fwd_sub_cnt := 0#64; fwd_str_cnt := 0#64; ant_sz := 0#64; res_sz := 0#64
  walk_vals := List.replicate 6 0#8; phases := List.replicate 3 0#8
  phases_target := List.replicate 3 0#8; phases_best := List.replicate 3 0#8
  walk_best := List.replicate 3 0#8; heap := List.replicate 3 0#32
  pos := List.replicate 3 0xFFFFFFFF#32; shrink_stk := List.replicate 3 0#32
  q_prev := List.replicate 3 0xFFFFFFFF#32; q_next := List.replicate 3 0xFFFFFFFF#32
  q_stamp := List.replicate 3 0#32; wsort := List.replicate 6 0#32
  work_stk1 := List.replicate 6 0#32; work_stk2 := List.replicate 6 0#32
  tarjan_mark := List.replicate 6 0#32; tarjan_reach := List.replicate 6 0#32
  score := [10#64, 30#64, 20#64]; sim_sig := List.replicate 3 0#64
  glue_used := List.replicate 64 0#32; last_learned := List.replicate 16 0xFFFFFFFF#32
  delayed := []; red_refs := []; extend_stk := []; scratch_buf := [0#32, 6#32, 0#32, 0#32]

def nvM4TernaryState : FullState where
  core :=
    { d_cur := 0#64, d_val := 0#64, cur_vars := 3, unassigned := 1#64, arena_len := 12, wlen := 1
      wusable := 0#64, arena_garbage := 0#64, first_reducible := 0#64, num_irred := 0#64
      num_redundant := 2#64, num_binary := 0#64, unflushed := 0#64, probing := 0#64, trail_end := 2
      propagated := 2, cur_level := 0, fuel := 16#64, confl_ref := 0#64, confl_type := 0#64
      confl_lit0 := 0#64, confl_lit1 := 0#64, tmp_cnt := 0, tmp_len := 0, min_clr_len := 0
      min_clr_full := 0#64, oom := 0#64, dense_mode := 0#64, inconsistent := 0#64
      vals := [0#8, 0#8, 0xFF#8, 1#8, 0xFF#8, 1#8], lit_mark := List.replicate 6 0#8
      mrk := List.replicate 3 0#8, flags := [1#32, 1#32, 1#32], lvl := [0#32, 0#32, 0#32]
      rsns := [0xFFFFFFFF#32, 0xFFFFFFFF#32, 0xFFFFFFFF#32], trl := [3#32, 5#32, 0#32]
      trail_pos := [0#32, 0#32, 1#32], tmp := [0#32, 0#32, 0#32], min_clr := [0#32, 0#32, 0#32]
      frame_trail := [0#32, 0#32, 0#32, 0#32], frame_dec := [0#32, 0#32, 0#32, 0#32]
      wvec := List.replicate 12 0#32, repr := List.replicate 6 0#32
      min_stk := List.replicate 8 0#32
      arena := [0x00400002#32, 2#32, 3#32, 0#32, 2#32, 4#32,
                0x00400002#32, 2#32, 3#32, 1#32, 2#32, 4#32]
      wstk := [0#32, 0#32, 0#32, 0#32] }
  scratch := nvM4TernaryScratch

theorem nvM4Ternary_lengths : nvM4TernaryState.LengthsOk nvM4TernaryCfg :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩,
   ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

def nvM4BlockHdr : List UInt8 :=
  bytes64 [3#64, 4#64, 0#64, 0#64] ++ bytes64 (Full.hdrTailWords nvM4TernaryCfg nvM4TernaryState)

def nvM4BlockBytes : List UInt8 :=
  (bytesOf (t := i8) nvM4TernaryState.core.vals ++ List.replicate 2 0) ++
  (bytesOf (t := i8) nvM4TernaryState.scratch.walk_vals ++ List.replicate 2 0) ++
  (bytesOf (t := i8) nvM4TernaryState.core.lit_mark ++ List.replicate 2 0) ++
  (bytesOf (t := i8) nvM4TernaryState.core.mrk ++ List.replicate 5 0) ++
  (bytesOf (t := i8) nvM4TernaryState.scratch.phases ++ List.replicate 5 0) ++
  (bytesOf (t := i8) nvM4TernaryState.scratch.phases_target ++ List.replicate 5 0) ++
  (bytesOf (t := i8) nvM4TernaryState.scratch.phases_best ++ List.replicate 5 0) ++
  (bytesOf (t := i8) nvM4TernaryState.scratch.walk_best ++ List.replicate 5 0)

def nvM4BlockU32A : List UInt8 :=
  (bytesOf (t := i32) nvM4TernaryState.core.flags ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4TernaryState.core.lvl ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4TernaryState.core.rsns ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4TernaryState.core.trl ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4TernaryState.core.trail_pos ++ List.replicate 4 0)

def nvM4BlockU32B : List UInt8 :=
  (bytesOf (t := i32) nvM4TernaryState.core.tmp ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4TernaryState.scratch.heap ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4TernaryState.scratch.pos ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4TernaryState.core.min_clr ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4TernaryState.scratch.shrink_stk ++ List.replicate 4 0)

def nvM4BlockU32C : List UInt8 :=
  (bytesOf (t := i32) nvM4TernaryState.scratch.q_prev ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4TernaryState.scratch.q_next ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4TernaryState.scratch.q_stamp ++ List.replicate 4 0) ++
  (bytesOf (t := i32) nvM4TernaryState.core.frame_trail ++ List.replicate 0 0) ++
  (bytesOf (t := i32) nvM4TernaryState.core.frame_dec ++ List.replicate 0 0)

def nvM4BlockWvec : List UInt8 :=
  bytesOf (t := i32) nvM4TernaryState.core.wvec ++
  bytesOf (t := i32) nvM4TernaryState.core.repr ++
  bytesOf (t := i32) nvM4TernaryState.scratch.wsort ++
  bytesOf (t := i32) nvM4TernaryState.scratch.work_stk1 ++
  bytesOf (t := i32) nvM4TernaryState.scratch.work_stk2 ++
  bytesOf (t := i32) nvM4TernaryState.scratch.tarjan_mark ++
  bytesOf (t := i32) nvM4TernaryState.scratch.tarjan_reach ++
  bytes64 nvM4TernaryState.scratch.score ++ bytes64 nvM4TernaryState.scratch.sim_sig

def nvM4BlockTail : List UInt8 :=
  bytesOf (t := i32) nvM4TernaryState.core.min_stk ++
  bytesOf (t := i32) nvM4TernaryState.scratch.glue_used ++
  bytesOf (t := i32) nvM4TernaryState.scratch.last_learned ++
  bytesOf (t := i32) nvM4TernaryState.core.arena ++
  bytesOf (t := i32) nvM4TernaryState.core.wstk ++
  bytesOf (t := i32) nvM4TernaryState.scratch.delayed ++
  bytesOf (t := i32) nvM4TernaryState.scratch.red_refs ++
  bytesOf (t := i32) nvM4TernaryState.scratch.extend_stk ++
  bytesOf (t := i32) nvM4TernaryState.scratch.scratch_buf ++ List.replicate 0 0

def nvM4TernaryBytes : List UInt8 :=
  nvM4BlockHdr ++ nvM4BlockBytes ++ nvM4BlockU32A ++ nvM4BlockU32B ++
  nvM4BlockU32C ++ nvM4BlockWvec ++ nvM4BlockTail

def nvM4TernaryMem : Mem 64 := nvM4TernaryBytes.At nvM4TernaryCfg.hdr

section NvHelpers

private theorem m4_nv_sep_append {P Q : Mem 64 → Prop} {a b : BitVec 64} {bs1 bs2 : List UInt8}
    (hb : b = a + BitVec.ofNat 64 bs1.length) (hlen : bs1.length + bs2.length ≤ 2 ^ 64)
    (h1 : P (bs1.At a)) (h2 : Q (bs2.At b)) : (P ⋆ Q) ((bs1 ++ bs2).At a) := by
  have heq := congrFun (Mem.At_append_sep bs1 bs2 a hlen) ((bs1 ++ bs2).At a)
  rw [← hb] at heq
  exact sep_mono2 (fun _ h => h ▸ h1) (fun _ h => h ▸ h2) _ (heq.mp rfl)

private theorem m4_nv_arr_pad_p {t : Ty} {a : BitVec 64} {xs : List (Val t)} (n pad : Nat)
    (hn : t.bytes * xs.length = n) (hbd : n + pad ≤ 2 ^ 64) :
    (bytesOf xs ++ List.replicate pad 0).length = n + pad ∧
    (array (t := t) a xs ⋆ region (a + BitVec.ofNat 64 n) pad)
      ((bytesOf xs ++ List.replicate pad 0).At a) :=
  ⟨by rw [List.length_append, bytesOf_length, List.length_replicate, hn],
   m4_nv_sep_append (by rw [bytesOf_length, hn])
     (by rw [bytesOf_length, List.length_replicate]; omega)
     (array_bytes a xs (by omega)) ⟨List.replicate pad 0, List.length_replicate, rfl⟩⟩

private theorem m4_nv_arr_p {t : Ty} {a : BitVec 64} {xs : List (Val t)} (n : Nat)
    (hn : t.bytes * xs.length = n) (hbd : n ≤ 2 ^ 64) :
    (bytesOf xs).length = n ∧ array (t := t) a xs ((bytesOf xs).At a) :=
  ⟨by rw [bytesOf_length, hn], array_bytes a xs (by omega)⟩

private theorem m4_nv_arr64_p {a : BitVec 64} {xs : List (BitVec 64)} (n : Nat)
    (hn : 8 * xs.length = n) (hbd : n ≤ 2 ^ 64) :
    (bytes64 xs).length = n ∧ array64 a xs ((bytes64 xs).At a) :=
  ⟨by rw [bytes64_length, hn], array64_bytes a xs (by omega)⟩

private theorem m4_nv_join {P Q : Mem 64 → Prop} {a b : BitVec 64} {bs1 bs2 : List UInt8}
    {n1 n2 : Nat} (h1 : bs1.length = n1 ∧ P (bs1.At a))
    (h2 : bs2.length = n2 ∧ Q (bs2.At b))
    (hb : b = a + BitVec.ofNat 64 n1) (hbd : n1 + n2 ≤ 2 ^ 64) :
    (bs1 ++ bs2).length = n1 + n2 ∧ (P ⋆ Q) ((bs1 ++ bs2).At a) :=
  ⟨by rw [List.length_append, h1.1, h2.1], m4_nv_sep_append (h1.1 ▸ hb) (by omega) h1.2 h2.2⟩

private theorem m4_nv_reorg {P Q : Mem 64 → Prop} {bs : List UInt8} {a : BitVec 64} {n : Nat}
    (h : bs.length = n ∧ P (bs.At a)) (himp : ∀ m, P m → Q m) : bs.length = n ∧ Q (bs.At a) :=
  ⟨h.1, himp _ h.2⟩

private theorem m4_nv_zip4 {A1 B1 A2 B2 A3 B3 A4 B4 : Mem 64 → Prop} {m : Mem 64}
    (h : ((((A1 ⋆ B1) ⋆ (A2 ⋆ B2)) ⋆ (A3 ⋆ B3)) ⋆ (A4 ⋆ B4)) m) :
    (((A1 ⋆ A3 ⋆ A4) ⋆ A2) ⋆ (B1 ⋆ B2 ⋆ B3 ⋆ B4)) m := sep_ac h

private theorem m4_nv_zip4_tail {C A2 P1 A5 B5 A6 B6 A7 B7 A8 B8 : Mem 64 → Prop} {m : Mem 64}
    (h : ((((((C ⋆ A2) ⋆ P1) ⋆ (A5 ⋆ B5)) ⋆ (A6 ⋆ B6)) ⋆ (A7 ⋆ B7)) ⋆ (A8 ⋆ B8)) m) :
    (C ⋆ (A2 ⋆ A5 ⋆ A6 ⋆ A7 ⋆ A8) ⋆ (P1 ⋆ B5 ⋆ B6 ⋆ B7 ⋆ B8)) m := sep_ac h

end NvHelpers

theorem nvM4TernaryMem_ok : FullMem nvM4TernaryCfg nvM4TernaryState nvM4TernaryMem := by
  let c := nvM4TernaryCfg; let s := nvM4TernaryState
  have hvb : valsBytes c.max_vars - 2 * c.max_vars = 2 := by decide
  have hmb : markBytes c.max_vars - c.max_vars = 5 := by decide
  have hu4 : u32FullBytes c.max_vars - 4 * c.max_vars = 4 := by decide
  have hu8 : u32FullBytes c.max_vars - 4 * (c.max_vars + 1) = 0 := by decide
  have hmv3 : BitVec.ofNat 64 c.max_vars = 3#64 := rfl
  have hmv6 : BitVec.ofNat 64 (2 * c.max_vars) = 6#64 := rfl
  have hmv12 : BitVec.ofNat 64 (4 * c.max_vars) = 12#64 := rfl
  have hmv16 : BitVec.ofNat 64 (4 * (c.max_vars + 1)) = 16#64 := rfl
  have hHdr : nvM4BlockHdr.length = 1152 ∧
      (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc)
        s.core.d_cur s.core.d_val ⋆ array64 (c.hdr + 32) (Full.hdrTailWords c s))
        (nvM4BlockHdr.At c.hdr) :=
    m4_nv_join (m4_nv_arr64_p (a := c.hdr) (xs := [3#64, 4#64, 0#64, 0#64]) 32 rfl (by decide))
      (m4_nv_arr64_p (a := c.hdr + 32) (xs := Full.hdrTailWords c s) 1120
        (by rw [Full.hdrTailWords_length]) (by decide)) (by decide) (by decide)
  have hBytes : nvM4BlockBytes.length = 64 ∧
      (FullCoreByteArrs c s.core ⋆ FullScrByteArrs c s.scratch ⋆ c.padBytes)
        (nvM4BlockBytes.At c.pVals) := by
    let pB1 : Mem 64 → Prop :=
      region (c.pVals + 6#64) 2 ⋆ region (c.pWalkVals + 6#64) 2 ⋆
      region (c.pLitMark + 6#64) 2 ⋆ region (c.pMark + 3#64) 5
    have h12 := m4_nv_join
      (m4_nv_arr_pad_p (t := i8) (a := c.pVals) (xs := s.core.vals) 6 2 rfl (by decide))
      (m4_nv_arr_pad_p (t := i8) (a := c.pWalkVals) (xs := s.scratch.walk_vals) 6 2 rfl (by decide))
      (by decide) (by decide)
    have h123 := m4_nv_join h12
      (m4_nv_arr_pad_p (t := i8) (a := c.pLitMark) (xs := s.core.lit_mark) 6 2 rfl (by decide))
      (by decide) (by decide)
    have h1234 := m4_nv_reorg (m4_nv_join h123
      (m4_nv_arr_pad_p (t := i8) (a := c.pMark) (xs := s.core.mrk) 3 5 rfl (by decide))
      (by decide) (by decide))
      (Q := (FullCoreByteArrs c s.core ⋆ array (t := i8) c.pWalkVals s.scratch.walk_vals) ⋆ pB1)
      fun _ hm => m4_nv_zip4 hm
    have h12345 := m4_nv_join h1234
      (m4_nv_arr_pad_p (t := i8) (a := c.pPhases) (xs := s.scratch.phases) 3 5 rfl (by decide))
      (by decide) (by decide)
    have h123456 := m4_nv_join h12345
      (m4_nv_arr_pad_p (t := i8) (a := c.pPhasesTarget) (xs := s.scratch.phases_target) 3 5 rfl
        (by decide)) (by decide) (by decide)
    have h1234567 := m4_nv_join h123456
      (m4_nv_arr_pad_p (t := i8) (a := c.pPhasesBest) (xs := s.scratch.phases_best) 3 5 rfl
        (by decide)) (by decide) (by decide)
    have hall := m4_nv_join h1234567
      (m4_nv_arr_pad_p (t := i8) (a := c.pWalkBest) (xs := s.scratch.walk_best) 3 5 rfl
        (by decide)) (by decide) (by decide)
    exact m4_nv_reorg hall fun _ hm => by
      have hfin := m4_nv_zip4_tail hm; unfold FullScrByteArrs FullCfg.padBytes
      rw [hvb, hmb, hmv6, hmv3]; simpa only [pB1, sep_assoc] using hfin
  have hU32A : nvM4BlockU32A.length = 80 ∧
      ((array (t := i32) c.pFlags s.core.flags ⋆ array (t := i32) c.pLevel s.core.lvl ⋆
        array (t := i32) c.pReason s.core.rsns ⋆ array (t := i32) c.pTrail s.core.trl ⋆
        array (t := i32) c.pTrailPos s.core.trail_pos) ⋆ c.padU32A)
        (nvM4BlockU32A.At c.pFlags) := by
    have h12 := m4_nv_join
      (m4_nv_arr_pad_p (t := i32) (a := c.pFlags) (xs := s.core.flags) 12 4 rfl (by decide))
      (m4_nv_arr_pad_p (t := i32) (a := c.pLevel) (xs := s.core.lvl) 12 4 rfl (by decide))
      (by decide) (by decide)
    have h123 := m4_nv_join h12
      (m4_nv_arr_pad_p (t := i32) (a := c.pReason) (xs := s.core.rsns) 12 4 rfl (by decide))
      (by decide) (by decide)
    have h1234 := m4_nv_join h123
      (m4_nv_arr_pad_p (t := i32) (a := c.pTrail) (xs := s.core.trl) 12 4 rfl (by decide))
      (by decide) (by decide)
    exact m4_nv_reorg (m4_nv_join h1234
      (m4_nv_arr_pad_p (t := i32) (a := c.pTrailPos) (xs := s.core.trail_pos) 12 4 rfl (by decide))
      (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32A; rw [hu4, hmv12]; exact sep_ac hm
  have hU32B : nvM4BlockU32B.length = 80 ∧
      ((array (t := i32) c.pTmp s.core.tmp ⋆ array (t := i32) c.pMinClr s.core.min_clr) ⋆
        (array (t := i32) c.pHeap s.scratch.heap ⋆ array (t := i32) c.pPos s.scratch.pos ⋆
         array (t := i32) c.pShrinkStk s.scratch.shrink_stk) ⋆ c.padU32B)
        (nvM4BlockU32B.At c.pTmp) := by
    have h12 := m4_nv_join
      (m4_nv_arr_pad_p (t := i32) (a := c.pTmp) (xs := s.core.tmp) 12 4 rfl (by decide))
      (m4_nv_arr_pad_p (t := i32) (a := c.pHeap) (xs := s.scratch.heap) 12 4 rfl (by decide))
      (by decide) (by decide)
    have h123 := m4_nv_join h12
      (m4_nv_arr_pad_p (t := i32) (a := c.pPos) (xs := s.scratch.pos) 12 4 rfl (by decide))
      (by decide) (by decide)
    have h1234 := m4_nv_join h123
      (m4_nv_arr_pad_p (t := i32) (a := c.pMinClr) (xs := s.core.min_clr) 12 4 rfl (by decide))
      (by decide) (by decide)
    exact m4_nv_reorg (m4_nv_join h1234
      (m4_nv_arr_pad_p (t := i32) (a := c.pShrinkStk) (xs := s.scratch.shrink_stk) 12 4 rfl
        (by decide)) (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32B; rw [hu4, hmv12]; exact sep_ac hm
  have hU32C : nvM4BlockU32C.length = 80 ∧
      ((array (t := i32) c.pQPrev s.scratch.q_prev ⋆
        array (t := i32) c.pQNext s.scratch.q_next ⋆
        array (t := i32) c.pQStamp s.scratch.q_stamp) ⋆
        (array (t := i32) c.pFrameTrail s.core.frame_trail ⋆
         array (t := i32) c.pFrameDec s.core.frame_dec) ⋆ c.padU32C)
        (nvM4BlockU32C.At c.pQPrev) := by
    have h12 := m4_nv_join
      (m4_nv_arr_pad_p (t := i32) (a := c.pQPrev) (xs := s.scratch.q_prev) 12 4 rfl (by decide))
      (m4_nv_arr_pad_p (t := i32) (a := c.pQNext) (xs := s.scratch.q_next) 12 4 rfl (by decide))
      (by decide) (by decide)
    have h123 := m4_nv_join h12
      (m4_nv_arr_pad_p (t := i32) (a := c.pQStamp) (xs := s.scratch.q_stamp) 12 4 rfl (by decide))
      (by decide) (by decide)
    have h1234 := m4_nv_join h123
      (m4_nv_arr_pad_p (t := i32) (a := c.pFrameTrail) (xs := s.core.frame_trail) 16 0 rfl
        (by decide)) (by decide) (by decide)
    exact m4_nv_reorg (m4_nv_join h1234
      (m4_nv_arr_pad_p (t := i32) (a := c.pFrameDec) (xs := s.core.frame_dec) 16 0 rfl (by decide))
      (by decide) (by decide)) fun _ hm => by
      unfold FullCfg.padU32C; rw [hu4, hu8, hmv12, hmv16]; exact sep_ac hm
  have hWvec : nvM4BlockWvec.length = 240 ∧
      ((array (t := i32) c.pWvec s.core.wvec ⋆ array (t := i32) c.pRepr s.core.repr) ⋆
        FullScrWksArrs c s.scratch ⋆
        (array64 c.pScore s.scratch.score ⋆ array64 c.pSimSig s.scratch.sim_sig))
        (nvM4BlockWvec.At c.pWvec) := by
    have h12 := m4_nv_join
      (m4_nv_arr_p (t := i32) (a := c.pWvec) (xs := s.core.wvec) 48 rfl (by decide))
      (m4_nv_arr_p (t := i32) (a := c.pRepr) (xs := s.core.repr) 24 rfl (by decide))
      (by decide) (by decide)
    have h123 := m4_nv_join h12
      (m4_nv_arr_p (t := i32) (a := c.pWsort) (xs := s.scratch.wsort) 24 rfl (by decide))
      (by decide) (by decide)
    have h1234 := m4_nv_join h123
      (m4_nv_arr_p (t := i32) (a := c.pWorkStk1) (xs := s.scratch.work_stk1) 24 rfl (by decide))
      (by decide) (by decide)
    have h12345 := m4_nv_join h1234
      (m4_nv_arr_p (t := i32) (a := c.pWorkStk2) (xs := s.scratch.work_stk2) 24 rfl (by decide))
      (by decide) (by decide)
    have h123456 := m4_nv_join h12345
      (m4_nv_arr_p (t := i32) (a := c.pTarjanMark) (xs := s.scratch.tarjan_mark) 24 rfl (by decide))
      (by decide) (by decide)
    have h1234567 := m4_nv_join h123456
      (m4_nv_arr_p (t := i32) (a := c.pTarjanReach) (xs := s.scratch.tarjan_reach) 24 rfl
        (by decide)) (by decide) (by decide)
    have h12345678 := m4_nv_join h1234567
      (m4_nv_arr64_p (a := c.pScore) (xs := s.scratch.score) 24 rfl (by decide))
      (by decide) (by decide)
    exact m4_nv_reorg (m4_nv_join h12345678
      (m4_nv_arr64_p (a := c.pSimSig) (xs := s.scratch.sim_sig) 24 rfl (by decide))
      (by decide) (by decide)) fun _ hm => by unfold FullScrWksArrs; exact sep_ac hm
  have hTail : nvM4BlockTail.length = 432 ∧
      (array (t := i32) c.pMinStk s.core.min_stk ⋆
        (array (t := i32) c.pGlueUsed s.scratch.glue_used ⋆
         array (t := i32) c.pLastLearned s.scratch.last_learned) ⋆
        FullCoreDynArrs c s.core ⋆ FullScrDynArrs c s.scratch ⋆ region c.pSlack c.slack)
        (nvM4BlockTail.At c.pMinStk) := by
    have h12 := m4_nv_join
      (m4_nv_arr_p (t := i32) (a := c.pMinStk) (xs := s.core.min_stk) 32 rfl (by decide))
      (m4_nv_arr_p (t := i32) (a := c.pGlueUsed) (xs := s.scratch.glue_used) 256 rfl (by decide))
      (by decide) (by decide)
    have h123 := m4_nv_join h12
      (m4_nv_arr_p (t := i32) (a := c.pLastLearned) (xs := s.scratch.last_learned) 64 rfl
        (by decide)) (by decide) (by decide)
    have h1234 := m4_nv_join h123
      (m4_nv_arr_p (t := i32) (a := c.pArena) (xs := s.core.arena) 48 rfl (by decide))
      (by decide) (by decide)
    have h12345 := m4_nv_join h1234
      (m4_nv_arr_p (t := i32) (a := c.pWstk) (xs := s.core.wstk) 16 rfl (by decide))
      (by decide) (by decide)
    have h123456 := m4_nv_join h12345
      (m4_nv_arr_p (t := i32) (a := c.pDelayed) (xs := s.scratch.delayed) 0 rfl (by decide))
      (by decide) (by decide)
    have h1234567 := m4_nv_join h123456
      (m4_nv_arr_p (t := i32) (a := c.pRedRefs) (xs := s.scratch.red_refs) 0 rfl (by decide))
      (by decide) (by decide)
    have h12345678 := m4_nv_join h1234567
      (m4_nv_arr_p (t := i32) (a := c.pExtendStk) (xs := s.scratch.extend_stk) 0 rfl (by decide))
      (by decide) (by decide)
    have h123456789 := m4_nv_join h12345678
      (m4_nv_arr_p (t := i32) (a := c.pScratchBuf) (xs := s.scratch.scratch_buf) 16 rfl (by decide))
      (by decide) (by decide)
    have h10 : (List.replicate 0 (0 : UInt8)).length = 0 ∧
        region c.pSlack c.slack ((List.replicate 0 0).At c.pSlack) :=
      ⟨rfl, ⟨List.replicate 0 0, by decide, rfl⟩⟩
    exact m4_nv_reorg (m4_nv_join h123456789 h10 (by decide) (by decide)) fun _ hm => by
      unfold FullCoreDynArrs FullScrDynArrs; exact sep_ac hm
  have h01 := m4_nv_join hHdr hBytes (by decide) (by decide)
  have h02 := m4_nv_join h01 hU32A (by decide) (by decide)
  have h03 := m4_nv_join h02 hU32B (by decide) (by decide)
  have h04 := m4_nv_join h03 hU32C (by decide) (by decide)
  have h05 := m4_nv_join h04 hWvec (by decide) (by decide)
  exact (m4_nv_reorg (Q := FullMem c s) (m4_nv_join h05 hTail (by decide) (by decide))
    fun _ hm => by
      unfold FullMem FullCoreArrays FullCoreU32A FullCoreU32B FullScratchArrays FullScrU32A
        FullScrMetaArrs FullCfg.pad
      exact sep_ac hm).2

private theorem nvM4_entails_mem {cl : List Nat} (hmem : cl ∈ nvM4TernaryClauses) :
    (cnfOfClauses nvM4TernaryClauses).EntailsClause (cnfClause cl) := by
  rw [CNF.entails_clause_def]; intro α hα
  exact (cnf_sat_cnfOfClauses_iff α nvM4TernaryClauses).mp hα cl hmem

theorem nvM4Ternary_refs : fullArenaClauseRefs nvM4TernaryState = [0, 6] := by decide

theorem nvM4Ternary_invW :
    FullSparseInvW nvM4TernaryCfg nvM4TernaryF0 nvM4TernaryClauses nvM4TernaryState := by
  have hrefs : fullArenaClauseRefsCore nvM4TernaryState.core = [0, 6] := nvM4Ternary_refs
  have hcv : nvM4TernaryState.core.cur_vars = 3 := rfl
  have hte : nvM4TernaryState.core.trail_end = 2 := rfl
  have hcl : nvM4TernaryState.core.cur_level = 0 := rfl
  have hdm : nvM4TernaryState.core.dense_mode = 0#64 := rfl
  have hwat : ModeWatchesInv nvM4TernaryClauses nvM4TernaryState.core := by
    unfold ModeWatchesInv; rw [ite_eq_left hdm]
    refine WatchesInv.of_slices (fun l hl => ?_) (fun l hl hp => ?_) (fun l1 _ h1 _ _ hp => ?_)
      (fun l hl => ?_)
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
        rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
        rfl | rfl | rfl | rfl | rfl | rfl <;> simp [fullWatchSizeCore, nvM4TernaryState] at hp
    · rw [hcv] at h1; rcases (by omega : l1 = 0 ∨ l1 = 1 ∨ l1 = 2 ∨ l1 = 3 ∨ l1 = 4 ∨ l1 = 5) with
        rfl | rfl | rfl | rfl | rfl | rfl <;> simp [fullWatchSizeCore, nvM4TernaryState] at hp
    · rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
        rfl | rfl | rfl | rfl | rfl | rfl <;> exact WatchSliceOk.empty
  have harena : FullArenaClausesInv nvM4TernaryCfg nvM4TernaryClauses nvM4TernaryState.core := by
    refine ⟨Or.inr (by decide), ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs] at hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> decide
    · intro r hr hsh; rw [hrefs] at hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact absurd rfl hsh
    · intro r hr _ l hl; rw [hrefs] at hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · change l ∈ [0, 2, 4] at hl; simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl <;> decide
      · change l ∈ [1, 2, 4] at hl; simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl <;> decide
    · intro r hr _; rw [hrefs] at hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> exact nvM4_entails_mem (by decide)
  have hw : FullWitnessInv nvM4TernaryCfg nvM4TernaryF0 nvM4TernaryClauses nvM4TernaryState.core :=
    { ext_sound := ⟨(varsBoundedBool_iff 3 nvM4TernaryClauses).mp rfl, id⟩
      inconsistent_sound := fun h => absurd rfl h
      arena := harena, watches := hwat, cur_level_le := Nat.zero_le _
      trail_lits_lt := fun i hi => by
        rw [hte] at hi; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> decide
      trail_vars_nodup := fun i j hi hj hveq => by
        rw [hte] at hi hj
        rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;>
          rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;>
          first | rfl | exact absurd hveq (by decide)
      vals_domain := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
          rfl | rfl | rfl | rfl | rfl | rfl <;> simp [nvM4TernaryState]
      vals_true_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
          rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first
          | exact ⟨fun _ => ⟨0, by decide, rfl⟩, fun _ => rfl⟩
          | exact ⟨fun _ => ⟨1, by decide, rfl⟩, fun _ => rfl⟩
          | exact ⟨fun h => (by cases h), fun ⟨i, hi, he⟩ =>
              (by rw [hte] at hi; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> cases he)⟩
      vals_false_iff := fun l hl => by
        rw [hcv] at hl; rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
          rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first
          | exact ⟨fun _ => ⟨0, by decide, rfl⟩, fun _ => rfl⟩
          | exact ⟨fun _ => ⟨1, by decide, rfl⟩, fun _ => rfl⟩
          | exact ⟨fun h => (by cases h), fun ⟨i, hi, he⟩ =>
              (by rw [hte] at hi; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> cases he)⟩
      lvl_le := fun i hi => by
        rw [hte] at hi; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> decide
      dec_earliest := fun _ j _ hj _ hpos => by
        rw [hte] at hj; rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl <;>
          exact absurd hpos.1 (by decide)
      levels_inhabited := fun _ _ h2 => by rw [hcl] at h2; omega
      level0_sound := fun i hi _ => by
        rw [hte] at hi; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;>
          exact nvM4_entails_mem (by decide)
      trail_pos_inv := fun i hi => by
        rw [hte] at hi; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl
      level0_rsn_none := fun i hi _ => by
        rw [hte] at hi; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl
      frame_trail_lt := fun L hL => by
        rw [hcl] at hL; obtain rfl : L = 0 := (by omega); decide
      frame_trail_mono := fun L1 L2 _ hL2 => by
        rw [hcl] at hL2; obtain rfl : L1 = 0 := (by omega); obtain rfl : L2 = 0 := (by omega)
        exact Nat.le_refl _
      frame_trail_before_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      frame_dec_lt := fun _ _ h2 => by rw [hcl] at h2; omega
      reason_inv := fun i hi hne => by
        rw [hte] at hi; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> exact absurd rfl hne
      reason_lit_mem := fun i hi hne => by
        rw [hte] at hi; rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> exact absurd rfl hne }
  refine ⟨nvM4Ternary_lengths, hw, ⟨fun v hv => ?_, fun l hl => ?_⟩, fun r hr _ => ?_,
    ⟨FullLastLearnedWf.of_cleared fun i hi => by
      simp only [nvM4TernaryState, nvM4TernaryScratch, List.getElem?_replicate,
        show i < 16 by omega, ↓reduceIte, Option.getD_some], Nat.le_refl 0⟩, rfl⟩
  · change v < 3 at hv; rcases (by omega : v = 0 ∨ v = 1 ∨ v = 2) with rfl | rfl | rfl <;> rfl
  · change l < 6 at hl
    rcases (by omega : l = 0 ∨ l = 1 ∨ l = 2 ∨ l = 3 ∨ l = 4 ∨ l = 5) with
      rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · change r ∈ fullArenaClauseRefsCore nvM4TernaryState.core at hr
    rw [hrefs] at hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide

theorem nv_full_promote_clause :
    Func.wp m4TernaryEnv full_promote_clause_body (nvM4TernaryCfg.hdr, 0#32, ()) nvM4TernaryMem
      (fun (_, ()) m' => ∃ ar' ws2' gu',
        let s' : FullState :=
          { core := { nvM4TernaryState.core with arena := ar' }
            scratch := { nvM4TernaryState.scratch with work_stk2 := ws2', glue_used := gu' } }
        FullSparseInvW nvM4TernaryCfg nvM4TernaryF0 nvM4TernaryClauses s' ∧
        nvM4TernaryF0.Unsat ∧ FullMem nvM4TernaryCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM4TernaryCfg nvM4TernaryState ⋆ emp) nvM4TernaryMem := by
    rw [sep_emp]; exact nvM4TernaryMem_ok
  exact m4t_promote_clause_impl.2 _ _ _ _
    ⟨nvM4TernaryCfg, nvM4TernaryF0, nvM4TernaryClauses, nvM4TernaryState, emp, rfl,
     nvM4Ternary_invW, by rw [nvM4Ternary_refs]; simp, hm,
     fun _ ar' ws2' gu' m' hsp' _ _ hm' => by
       rw [sep_emp] at hm'; exact ⟨ar', ws2', gu', hsp', nvM4TernaryF0_unsat, hm'⟩⟩

theorem nv_full_promote_reasons :
    Func.wp m4TernaryEnv full_promote_reasons_body (nvM4TernaryCfg.hdr, ()) nvM4TernaryMem
      (fun (_, ()) m' => ∃ ar' ws2' gu',
        let s' : FullState :=
          { core := { nvM4TernaryState.core with arena := ar' }
            scratch := { nvM4TernaryState.scratch with work_stk2 := ws2', glue_used := gu' } }
        FullSparseInv nvM4TernaryCfg nvM4TernaryF0 s' ∧
        nvM4TernaryF0.Unsat ∧ FullMem nvM4TernaryCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM4TernaryCfg nvM4TernaryState ⋆ emp) nvM4TernaryMem := by
    rw [sep_emp]; exact nvM4TernaryMem_ok
  exact m4t_promote_reasons_impl.2 _ _ _ _
    ⟨nvM4TernaryCfg, nvM4TernaryF0, nvM4TernaryState, emp, rfl,
     nvM4Ternary_invW.toSparse, hm, fun _ ar' ws2' gu' m' hsp' hm' => by
       rw [sep_emp] at hm'; exact ⟨ar', ws2', gu', hsp', nvM4TernaryF0_unsat, hm'⟩⟩

theorem nv_full_reorder :
    Func.wp m4TernaryEnv full_reorder_body (nvM4TernaryCfg.hdr, 10#64, ()) nvM4TernaryMem
      (fun (_, ()) m' => ∃ s',
        FullSparseInv nvM4TernaryCfg nvM4TernaryF0 s' ∧
        FullArenaPermEq nvM4TernaryState.core s'.core ∧
        nvM4TernaryF0.Unsat ∧ FullMem nvM4TernaryCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM4TernaryCfg nvM4TernaryState ⋆ emp) nvM4TernaryMem := by
    rw [sep_emp]; exact nvM4TernaryMem_ok
  exact m4t_reorder_impl.2 _ _ _ _
    ⟨nvM4TernaryCfg, nvM4TernaryF0, nvM4TernaryState, emp, rfl,
     nvM4Ternary_invW.toSparse, hm, fun _ s' m' hsp' hperm' hm' => by
       rw [sep_emp] at hm'; exact ⟨s', hsp', hperm', nvM4TernaryF0_unsat, hm'⟩⟩

theorem nv_full_ternary_resolve_bin :
    Func.wp m4TernaryEnv full_ternary_resolve_bin_body
      (nvM4TernaryCfg.hdr, 0#32, 6#32, ()) nvM4TernaryMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInvW nvM4TernaryCfg nvM4TernaryF0 nvM4TernaryClauses s' ∧
        (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) ∧
        nvM4TernaryF0.Unsat ∧ FullMem nvM4TernaryCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM4TernaryCfg nvM4TernaryState ⋆ emp) nvM4TernaryMem := by
    rw [sep_emp]; exact nvM4TernaryMem_ok
  exact m4t_ternary_resolve_bin_impl.2 _ _ _ _
    ⟨nvM4TernaryCfg, nvM4TernaryF0, nvM4TernaryClauses, nvM4TernaryState, emp, rfl,
     nvM4Ternary_invW, rfl, by rw [nvM4Ternary_refs]; simp, by rw [nvM4Ternary_refs]; simp, hm,
     fun r _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' hsp' hdom _ _ hm' => by
       rw [sep_emp] at hm'; exact ⟨_, hsp', hdom, nvM4TernaryF0_unsat, hm'⟩⟩

theorem nv_full_ternary :
    Func.wp m4TernaryEnv full_ternary_body (nvM4TernaryCfg.hdr, 2#64, 16#64, ()) nvM4TernaryMem
      (fun (r, ()) m' => ∃ s',
        FullSparseInv nvM4TernaryCfg nvM4TernaryF0 s' ∧
        (r = 1#64 ∨ r = 20#64) ∧ nvM4TernaryF0.Unsat ∧ FullMem nvM4TernaryCfg s' m')
      (fun _ _ _ _ => False) := by
  have hm : (FullMem nvM4TernaryCfg nvM4TernaryState ⋆ emp) nvM4TernaryMem := by
    rw [sep_emp]; exact nvM4TernaryMem_ok
  exact m4t_ternary_impl.2 _ _ _ _
    ⟨nvM4TernaryCfg, nvM4TernaryF0, nvM4TernaryState, emp, rfl,
     nvM4Ternary_invW.toSparse, hm, fun r s' m' hsp' _ hdom _ _ hm' => by
       rw [sep_emp] at hm'; exact ⟨s', hsp', hdom, nvM4TernaryF0_unsat, hm'⟩⟩

end LeanQbe.T.Examples.Kissat.FullM4Ternary
