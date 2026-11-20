module

public import LeanQbe.T.Examples.Kissat.Full
public import LeanQbe.T.Examples.Kissat.FullInv2
public import LeanQbe.T.Examples.Kissat.FullArena
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` UNSAT-Only BVE Top-Shard Proofs — Part 1 (`Stage 4`, BVE-Var Shard)

Provides:
1. Scoped `FullBveVarTactics` bitwise/`BitVec`/pointer-slice accessors and stepping macros.
2. Canonical Stage-4 invariants, watch/arena transition helpers, and `Spec` contracts in
   `FullBveVarSpecs` aligned 1:1 with `FullSpec1..3`.
3. `FullDenseInvW` field-update transport lemmas and `FullResBufOkW` prefix/append lemmas.
4. Parametric `(Γ : Env)` `Func.wp` proof for `full_bve_ext_need`.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test

/-! ## 1. Scoped tactics & bitwise/slice helpers (`FullBveVarTactics`) -/

namespace FullBveVarTactics

open FullArenaTactics
open scoped FullArenaTactics

attribute [scoped bv_c0 high] bv_c0_zext32_64
attribute [scoped bv_c0] bv32_lshr_1 bv32_and_1 bv32_xor_1 List.length_set Bool.false_eq_true

@[scoped bv_c0] theorem bv_c0_fullState_core (k : FullCoreState) (sc : FullScratch) :
    ({ core := k, scratch := sc } : FullState).core = k := rfl

@[scoped bv_c0] theorem bv_c0_lshr1_32 (x : BitVec 32) : (x >>> 1).toNat = x.toNat / 2 :=
  bv32_lshr_1 x

@[scoped bv_c0] theorem bv_c0_shl1_nat_mod {x : BitVec 64} (hx : 2 * x.toNat < 2 ^ 64) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm, Nat.mod_eq_of_lt hx]

@[scoped bv_c0] theorem bv_c0_shl1_toNat32 {x : BitVec 32} (hx : 2 * x.toNat < 2 ^ 32) :
    (x <<< ((BitVec.signExtend 64 (1 : BitVec 32)).toNat % 32)).toNat = 2 * x.toNat := by
  rw [show (BitVec.signExtend 64 (1 : BitVec 32)).toNat % 32 = 1 from rfl]
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_comm, Nat.mod_eq_of_lt hx]

theorem nat_xor1_lt_two_mul {l n : Nat} (hl : l < 2 * n) : l ^^^ 1 < 2 * n := by
  have hdiv : (l ^^^ 1) / 2 = l / 2 := fullInv_var_xor1 l
  omega

theorem bv32_xor_1_toNat (x : BitVec 32) : (x ^^^ 1#32).toNat = x.toNat ^^^ 1 := rfl

theorem bv32_and_litMask_toNat (w : BitVec 32) :
    (w &&& 0x7FFFFFFF#32).toNat = w.toNat % 2 ^ 31 := by
  simpa [BitVec.toNat_and, show (0x7FFFFFFF#32).toNat = 2 ^ 31 - 1 from rfl] using
    Nat.and_two_pow_sub_one_eq_mod w.toNat 31

theorem bv32_and_msb_eq_zero_of_lt {x : BitVec 32} (hx : x.toNat < 2 ^ 31) :
    x &&& 0x80000000#32 = 0#32 := by
  ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_zero]
  rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hi31 | rfl
  · simp [show (0x80000000#32)[i] = false from by
      rw [BitVec.getElem_eq_testBit_toNat, show (0x80000000#32).toNat = 2 ^ 31 by rfl,
        Nat.testBit_two_pow_of_ne (by omega)]]
  · have hb : x[31] = false := by
      rw [BitVec.getElem_eq_testBit_toNat, Nat.testBit, Nat.shiftRight_eq_div_pow,
        Nat.div_eq_of_lt hx]; rfl
    simp [hb]

theorem bv32_bit19_or_garb_ne0 (x : BitVec 32) :
    ((x ||| 0x00080000#32) &&& 0x00080000#32) ≠ 0#32 := by
  intro h; have := congrArg (·[19]) h; simp at this

theorem bv32_bit23_or_garb (x : BitVec 32) :
    ((x ||| 0x00080000#32) &&& 0x00800000#32) = (x &&& 0x00800000#32) := by
  ext i hi; simp only [BitVec.getElem_and, BitVec.getElem_or]
  have h23 : (0x00800000#32)[i] = true → (0x00080000#32)[i] = false := by
    revert i hi; decide
  cases h : (0x00800000#32)[i]
  · simp
  · simp [h23 h]

theorem bv32_ofNat_toNat {n : Nat} (hn : n < 2 ^ 32) : (BitVec.ofNat 32 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]

theorem bv64_toNat_setWidth32_lt {x : BitVec 64} (hx : x.toNat < 2 ^ 32) :
    (BitVec.setWidth 32 x).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx]

@[scoped c0_load] theorem load_full_scratch_buf0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < s.scratch.scratch_buf.length)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 c.pScratchBuf = some s.scratch.scratch_buf[0] := by
  simpa using load_full_scratch_buf (i := 0) hi hm

@[scoped c0_store] theorem store_full_scratch_buf0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.scratch.scratch_buf.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pScratchBuf ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set 0 v } } ⋆ R)
        (storeMem m i32 c.pScratchBuf v) := by
  simpa using store_full_scratch_buf (i := 0) v hi hm

@[scoped c0_load] theorem load_full_scratch_buf_imm {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {d : Nat}
    (hd : d % 4 = 0) (hd64 : d < 2 ^ 64)
    (hi : d / 4 < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (c.pScratchBuf + BitVec.ofNat 64 d) = some s.scratch.scratch_buf[d / 4] := by
  have heq : BitVec.ofNat 64 d = BitVec.ofNat 64 (4 * (d / 4)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd64,
      Nat.mod_eq_of_lt (by omega)]; omega
  rw [heq]; exact load_full_scratch_buf hi hm

@[scoped c0_store] theorem store_full_scratch_buf_imm {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {d : Nat} (v : BitVec 32)
    (hd : d % 4 = 0) (hd64 : d < 2 ^ 64)
    (hi : d / 4 < s.scratch.scratch_buf.length) (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pScratchBuf + BitVec.ofNat 64 d) ∧
      (FullMem c { s with scratch := { s.scratch with
        scratch_buf := s.scratch.scratch_buf.set (d / 4) v } } ⋆ R)
        (storeMem m i32 (c.pScratchBuf + BitVec.ofNat 64 d) v) := by
  have heq : BitVec.ofNat 64 d = BitVec.ofNat 64 (4 * (d / 4)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd64,
      Nat.mod_eq_of_lt (by omega)]; omega
  rw [heq]; exact store_full_scratch_buf v hi hm

@[scoped c0_load] theorem load_full_arena0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < s.core.arena.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 c.pArena = some s.core.arena[0] := by
  simpa using load_full_arena (i := 0) hi hm

@[scoped c0_store] theorem store_full_arena0 {c : FullCfg} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (v : BitVec 32) (hi : 0 < s.core.arena.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 c.pArena ∧
      (FullMem c { s with core := { s.core with arena := s.core.arena.set 0 v } } ⋆ R)
        (storeMem m i32 c.pArena v) := by
  simpa using store_full_arena (i := 0) v hi hm

/-- Strip `Expr.mdata` after unfolding `Func.wp`, then run `c0_steps`. -/
scoped syntax "bve_steps" : tactic
scoped macro_rules
  | `(tactic| bve_steps) => `(tactic| (
      (try change Func.wp _ _ _ _ _ _); (try change wp _ _ _ _ _); c0_steps))

/-- Strip `Expr.mdata` after unfolding `Func.wp`, then run strict `c0_steps!`. -/
scoped syntax "bve_steps!" : tactic
scoped macro_rules
  | `(tactic| bve_steps!) => `(tactic| (
      (try change Func.wp _ _ _ _ _ _); (try change wp _ _ _ _ _); c0_steps!))

end FullBveVarTactics

open FullBveVarTactics
open scoped FullArenaTactics FullBveVarTactics

/-! ## 2. Canonical Stage-4 shared invariants & local `Spec` contracts (`FullBveVarSpecs`) -/

namespace FullBveVarSpecs

def FullMrkZero (c : FullCfg) (s : FullState) : Prop :=
  ∀ v < c.max_vars, s.core.mrk[v]?.getD 0#8 = 0#8

def FullLitMarksClear (c : FullCfg) (s : FullState) : Prop :=
  FullMrkZero c s ∧ ∀ l < 2 * c.max_vars, s.core.lit_mark[l]?.getD 0#8 = 0#8

def FullArenaVarsNodup (s : FullState) : Prop :=
  ∀ r ∈ fullArenaClauseRefs s, fullArenaClauseGarb s r = false →
    ((fullArenaClauseLits s r).map (· / 2)).Nodup

def FullLastLearnedWf (s : FullState) : Prop :=
  ∀ i < 8,
    let cr := s.scratch.last_learned[i]?.getD 0xFFFFFFFF#32
    cr = 0xFFFFFFFF#32 ∨ cr.toNat ∈ fullArenaClauseRefs s

def FullExtScratchOk (c : FullCfg) (s : FullState) : Prop :=
  FullLastLearnedWf s ∧ s.scratch.extend_len ≤ c.extend_cap

def FullExtScratchPres (s s' : FullState) : Prop :=
  s'.scratch.last_learned = s.scratch.last_learned ∧
  s'.scratch.extend_len = s.scratch.extend_len

def FullProbeScratchPres (s s' : FullState) : Prop :=
  FullExtScratchPres s s' ∧
  s'.scratch.work_stk1 = s.scratch.work_stk1 ∧
  s'.scratch.work_stk2 = s.scratch.work_stk2 ∧
  s'.scratch.tarjan_mark = s.scratch.tarjan_mark ∧
  s'.scratch.scratch_buf = s.scratch.scratch_buf ∧
  s'.scratch.ant_sz = s.scratch.ant_sz ∧
  s'.scratch.res_sz = s.scratch.res_sz ∧
  s'.scratch.sim_sig = s.scratch.sim_sig

def FullDenseInv (c : FullCfg) (F0 : CNF Nat) (s : FullState) : Prop :=
  FullCoreInv c F0 s ∧ FullLitMarksClear c s ∧ FullArenaVarsNodup s ∧
  FullExtScratchOk c s ∧ s.core.cur_level = 0 ∧ s.core.dense_mode ≠ 0#64

def FullDenseInvW (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) : Prop :=
  s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ FullLitMarksClear c s ∧
  FullArenaVarsNodup s ∧ FullExtScratchOk c s ∧ s.core.cur_level = 0 ∧ s.core.dense_mode ≠ 0#64

theorem FullDenseInvW.toDense {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) : FullDenseInv c F0 s :=
  ⟨⟨h.1, F_cur, h.2.1⟩, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

def FullBveEntryOkW (F_cur : List (List Nat)) (s : FullState) (lit : Nat) (w : BitVec 32) : Prop :=
  if (w &&& 0x80000000#32) ≠ 0#32 then
    let ot := (w &&& 0x7FFFFFFF#32).toNat
    ot < 2 * s.core.cur_vars ∧ (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, ot])
  else
    w.toNat ∈ fullArenaClauseRefs s ∧ fullArenaClauseGarb s w.toNat = false

/-- Weak structural entry validity for `full_bve_weaken` (without `garb = false` or binary
entailment, preserved across marking other occurrences `PH_GARB`). -/
def FullBveWeakItemOk (s : FullState) (w : BitVec 32) : Prop :=
  if (w &&& 0x80000000#32) ≠ 0#32 then
    (w &&& 0x7FFFFFFF#32).toNat < 2 * s.core.cur_vars
  else
    w.toNat ∈ fullArenaClauseRefs s

/-- Geometric entry validity for `full_bve_try_bce` (`cr`), invariant under `PH_GARB`. -/
def FullBveTryBceEntryOk (c : FullCfg) (s : FullState) (cr : BitVec 32) : Prop :=
  if (cr &&& 0x80000000#32) ≠ 0#32 then
    (cr &&& 0x7FFFFFFF#32).toNat < 2 * c.max_vars
  else
    cr.toNat ∈ fullArenaClauseRefs s ∧
    cr.toNat + 3 + fullArenaClauseSize s cr.toNat ≤ s.core.arena_len ∧
    (∀ l ∈ fullArenaClauseLits s cr.toNat, l < 2 * c.max_vars) ∧
    ((fullArenaClauseLits s cr.toNat).map (· / 2)).Nodup

/-- Geometric opposite-entry validity for `full_bve_try_bce` (`ow`), invariant under `PH_GARB`. -/
def FullBveTryBceOppOk (c : FullCfg) (s : FullState) (ow : BitVec 32) : Prop :=
  if (ow &&& 0x80000000#32) ≠ 0#32 then
    (ow &&& 0x7FFFFFFF#32).toNat < 2 * c.max_vars
  else
    ow.toNat ∈ fullArenaClauseRefs s ∧
    ow.toNat + 3 + fullArenaClauseSize s ow.toNat ≤ s.core.arena_len ∧
    (∀ l ∈ fullArenaClauseLits s ow.toNat, l < 2 * c.max_vars)

inductive FullResBufOkW (F_cur : List (List Nat)) (s : FullState) (r_end : Nat) : Nat → Prop where
  | nil : FullResBufOkW F_cur s r_end r_end
  | cons {p sz : Nat} :
      p + 1 + sz ≤ r_end →
      (s.scratch.scratch_buf[p]?.getD 0#32).toNat = sz →
      (∀ k < sz, (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat < 2 * s.core.cur_vars) →
      ((List.range sz).map fun k =>
        (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat / 2).Nodup →
      (cnfOfClauses F_cur).EntailsClause (cnfClause ((List.range sz).map fun k =>
        (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat)) →
      FullResBufOkW F_cur s r_end (p + 1 + sz) →
      FullResBufOkW F_cur s r_end p

def fullAllocClSpec : Spec [i64, i32, i32, .bool] [i64] := fun (h, sz, _glue, red, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    if c.arena_cap - s.core.arena_len < 3 + sz.toNat then
      Q (0xFFFFFFFF#64, ()) m
    else
      ∀ arena' m',
        let alen' := s.core.arena_len + 3 + sz.toNat
        let s' : FullState :=
          { s with core := { s.core with arena_len := alen', arena := arena' } }
        s'.LengthsOk c →
        (∀ i < s.core.arena_len, arena'[i]? = s.core.arena[i]?) →
        (arena'[s.core.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32 →
        (arena'[s.core.arena_len]?.getD 0#32 &&& 0x00080000#32) = 0#32 →
        ((arena'[s.core.arena_len]?.getD 0#32 &&& 0x00400000#32) ≠ 0#32 ↔ red = true) →
        (arena'[s.core.arena_len + 2]?.getD 0#32).toNat = sz.toNat →
        (FullMem c s' ⋆ R) m' →
        Q (BitVec.ofNat 64 s.core.arena_len, ()) m'

def fullWatchPushSpec : Spec [i64, i32, i32, i32, i32] [.bool] :=
  fun (h, lit, w0, w1, cnt, ()) m Q _ =>
    ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧
      (cnt.toNat = 1 → w0 ≠ 0xFFFFFFFF#32) ∧
      (cnt.toNat = 2 → w0 ≠ 0xFFFFFFFF#32 ∧ w1 ≠ 0xFFFFFFFF#32) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (ok : Bool) wvec' wstk' wlen' wusable' wsort' m',
        let s' : FullState :=
          { s with
            core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen',
                                  wusable := wusable' }
            scratch := { s.scratch with wsort := wsort' } }
        s'.LengthsOk c → WatchStackLayout s'.core →
        (∀ l < 2 * s.core.cur_vars, l ≠ lit.toNat →
          fullWatchSize s' l = fullWatchSize s l ∧
          ∀ k < fullWatchSize s l,
            s'.core.wstk[fullWatchOff s' l + k]? = s.core.wstk[fullWatchOff s l + k]?) →
        (ok = true →
          lit.toNat < 2 * s.core.cur_vars ∧ (cnt.toNat = 1 ∨ cnt.toNat = 2) ∧
          fullWatchSize s' lit.toNat = fullWatchSize s lit.toNat + cnt.toNat ∧
          (∀ k < fullWatchSize s lit.toNat,
            s'.core.wstk[fullWatchOff s' lit.toNat + k]? =
              s.core.wstk[fullWatchOff s lit.toNat + k]?) ∧
          s'.core.wstk[fullWatchOff s' lit.toNat + fullWatchSize s lit.toNat]? = some w0 ∧
          (cnt.toNat = 2 →
            s'.core.wstk[fullWatchOff s' lit.toNat + fullWatchSize s lit.toNat + 1]? = some w1)) →
        (ok = false →
          (lit.toNat < 2 * s.core.cur_vars →
            fullWatchSize s' lit.toNat = fullWatchSize s lit.toNat ∧
            ∀ k < fullWatchSize s lit.toNat,
              s'.core.wstk[fullWatchOff s' lit.toNat + k]? =
                s.core.wstk[fullWatchOff s lit.toNat + k]?) ∧
          (2 * s.core.cur_vars ≤ lit.toNat ∨ (cnt.toNat ≠ 1 ∧ cnt.toNat ≠ 2) ∨
            s' = s ∨ wusable' = 0#64)) →
        (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullAddBinSpec : Spec [i64, i32, i32] [i64] := fun (h, a, b, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧ s.core.cur_level = 0 ∧
    (a.toNat < 2 * s.core.cur_vars → b.toNat < 2 * s.core.cur_vars →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [a.toNat, b.toNat])) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r vals' flags' lvl' rsns' trl' tp' te' unass' unfl' wvec' wstk' wlen' wu' nb' oom' inc'
      phases' wsort' m',
      let s' : FullState :=
        { s with
          core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', trail_end := te',
                                unassigned := unass', unflushed := unfl', wvec := wvec',
                                wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
                                oom := oom', inconsistent := inc' }
          scratch := { s.scratch with phases := phases', wsort := wsort' } }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core →
      (r = 0#64 ∨ r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat ∧ inc' ≠ 0#64) →
      (r = 2#64 → oom' ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullDeleteBinarySpec : Spec [i64, i32, i32] [] := fun (h, _a, _b, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ WatchStackLayout s.core ∧ (FullMem c s ⋆ R) m ∧
    ∀ wvec' wstk' wu' nb' m',
      let s' : FullState :=
        { s with core := { s.core with wvec := wvec', wstk := wstk',
                                       wusable := wu', num_binary := nb' } }
      s'.LengthsOk c → WatchStackLayout s'.core →
      (∀ F_cur, ModeWatchesInv F_cur s.core → ModeWatchesInv F_cur s'.core) →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullSetInactiveSpec : Spec [i64, i32, i32] [] := fun (h, _v, _flag, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ (FullMem c s ⋆ R) m ∧
    ∀ flags' unass' m',
      flags'.length = c.max_vars →
      (FullMem c { s with core := { s.core with flags := flags', unassigned := unass' } } ⋆ R) m' →
      Q () m'

def fullAddUnitSpec : Spec [i64, i32] [.bool] := fun (h, lit, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ FullWitnessInv c F0 F_cur s.core ∧
    (lit.toNat < 2 * s.core.cur_vars → (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat])) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) vals' flags' lvl' rsns' trl' tp' te' prop' cl' unass' unfl' inc' sc' m',
      let s' : FullState :=
        { s with
          core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                                trl := trl', trail_pos := tp', trail_end := te',
                                propagated := prop', cur_level := cl', unassigned := unass',
                                unflushed := unfl', inconsistent := inc' }
          scratch := sc' }
      s'.LengthsOk c → FullWitnessInv c F0 F_cur s'.core → FullProbeScratchPres s s' → cl' = 0 →
      (lit.toNat < 2 * s.core.cur_vars → ok = false → F0.Unsat ∧ inc' ≠ 0#64) →
      (ok = false → 2 * s.core.cur_vars ≤ lit.toNat ∨ (F0.Unsat ∧ inc' ≠ 0#64)) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullExtendPush2Spec : Spec [i64, i32, i32] [.bool] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _blk, _ot, ()) s => h = c.hdr ∧ s.scratch.extend_len ≤ c.extend_cap)
    (fun c _ _ s s' =>
      s'.scratch.last_learned = s.scratch.last_learned ∧
      s'.scratch.extend_len ≤ c.extend_cap ∧
      s'.scratch.scratch_buf = s.scratch.scratch_buf)

def fullExtendPushClSpec : Spec [i64, i32, i32] [.bool] :=
  SafetySlice.spec fullSafetySlice
    (fun c (h, _blk, _cref, ()) s => h = c.hdr ∧ s.scratch.extend_len ≤ c.extend_cap)
    (fun c _ _ s s' =>
      s'.scratch.last_learned = s.scratch.last_learned ∧
      s'.scratch.extend_len ≤ c.extend_cap ∧
      s'.scratch.scratch_buf = s.scratch.scratch_buf)

def fullBveCollectSpec : Spec [i64, i32, i64, i32] [i32] :=
  fun (h, lit, out_ptr, cap, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (out_off : Nat)
      (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ lit.toNat < 2 * s.core.cur_vars ∧
      out_ptr = c.pScratchBuf + BitVec.ofNat 64 (4 * out_off) ∧
      out_off + cap.toNat ≤ c.scratch_cap ∧ (FullMem c s ⋆ R) m ∧
      ∀ r scr' m',
        let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
        scr'.length = c.scratch_cap →
        (∀ i < c.scratch_cap, (i < out_off ∨ out_off + cap.toNat ≤ i) →
          scr'[i]? = s.scratch.scratch_buf[i]?) →
        (r = 0xFFFFFFFF#32 ∨ (r.toNat ≤ cap.toNat ∧
          ∀ i < r.toNat, FullBveEntryOkW F_cur s' lit.toNat (scr'[out_off + i]?.getD 0#32))) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullBveGatesSpec : Spec [i64, i32, i32, i32] [] := fun (h, v, np, nn, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ 132 ≤ c.scratch_cap ∧
    v.toNat < s.core.cur_vars ∧ np.toNat ≤ 64 ∧ nn.toNat ≤ 64 ∧
    (∀ i < np.toNat, FullBveEntryOkW F_cur s (2 * v.toNat)
      (s.scratch.scratch_buf[i]?.getD 0#32)) ∧
    (∀ j < nn.toNat, FullBveEntryOkW F_cur s (2 * v.toNat + 1)
      (s.scratch.scratch_buf[64 + j]?.getD 0#32)) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ lm' scr' m',
      let s' : FullState :=
        { s with
          core := { s.core with lit_mark := lm' }
          scratch := { s.scratch with scratch_buf := scr' } }
      FullDenseInvW c F0 F_cur s' →
      (∀ i < c.scratch_cap, (i < 128 ∨ 132 ≤ i) → scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q () m'

def fullBveResolvePairSpec : Spec [i64, i32, i32, i32] [.bool] := fun (h, v, pc, nc, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ v.toNat < s.core.cur_vars ∧
    FullBveEntryOkW F_cur s (2 * v.toNat) pc ∧ FullBveEntryOkW F_cur s (2 * v.toNat + 1) nc ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) lm' tmp' tl' m',
      let s' : FullState :=
        { s with core := { s.core with lit_mark := lm', tmp := tmp', tmp_len := tl' } }
      FullDenseInvW c F0 F_cur s' → tl' ≤ s.core.cur_vars →
      (ok = true →
        (∀ k < tl', (tmp'[k]?.getD 0#32).toNat < 2 * s.core.cur_vars) ∧
        ((tmp'.take tl').map fun x => x.toNat / 2).Nodup ∧
        (cnfOfClauses F_cur).EntailsClause (cnfClause ((tmp'.take tl').map BitVec.toNat))) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullBveWeakenSpec : Spec [i64, i32, i32, i32] [.bool] := fun (h, blk_lit, off, cnt, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ blk_lit.toNat < 2 * s.core.cur_vars ∧
    off.toNat + cnt.toNat ≤ c.scratch_cap ∧
    (∀ i < cnt.toNat, FullBveWeakItemOk s (s.scratch.scratch_buf[off.toNat + i]?.getD 0#32)) ∧
    (FullMem c s ⋆ R) m ∧
    ∀ (ok : Bool) s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → s'.scratch.scratch_buf = s.scratch.scratch_buf →
      fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m'

def fullBveTryBceSpec : Spec [i64, i32, i32, i32, i32] [.bool] :=
  fun (h, blk_lit, cr, opp_off, opp_n, ()) m Q _ =>
    ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ blk_lit.toNat < 2 * s.core.cur_vars ∧
      FullBveTryBceEntryOk c s cr ∧ opp_off.toNat + opp_n.toNat ≤ c.scratch_cap ∧
      (∀ j < opp_n.toNat, FullBveTryBceOppOk c s
        (s.scratch.scratch_buf[opp_off.toNat + j]?.getD 0#32)) ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (blk : Bool) lm' tmp' m',
        let s' : FullState := { s with core := { s.core with lit_mark := lm', tmp := tmp' } }
        FullDenseInvW c F0 F_cur s' → (FullMem c s' ⋆ R) m' → Q (blk, ()) m'

def fullBveCommitResSpec : Spec [i64, i64, i64] [i64] := fun (h, r_off, r_end, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInvW c F0 F_cur s ∧ r_off.toNat ≤ r_end.toNat ∧
    r_end.toNat ≤ c.scratch_cap ∧ FullResBufOkW F_cur s r_end.toNat r_off.toNat ∧
    (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) →
      (r = 20#64 → F0.Unsat) → (FullMem c s' ⋆ R) m' → Q (r, ()) m'

def fullBveExtNeedSpec : Spec [i64, i32, i32] [i64] := fun (h, off, cnt, ()) m Q _ =>
  ∃ (c : FullCfg) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ s.LengthsOk c ∧ off.toNat + cnt.toNat ≤ c.scratch_cap ∧
    (∀ i < cnt.toNat,
      let w := s.scratch.scratch_buf[off.toNat + i]?.getD 0#32
      (w &&& 0x80000000#32) ≠ 0#32 ∨ w.toNat + 2 < c.arena_cap) ∧
    (FullMem c s ⋆ R) m ∧ ∀ r : BitVec 64, Q (r, ()) m

def fullBveVarSpec : Spec [i64, i32] [i64] := fun (h, v, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullDenseInv c F0 s ∧ v.toNat < s.core.cur_vars ∧ (FullMem c s ⋆ R) m ∧
    ∀ r s' m',
      FullDenseInv c F0 s' → s.core.cur_vars ≤ s'.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (r = 1#64 ∨ r = 2#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m'

end FullBveVarSpecs

open FullBveVarSpecs

/-! ## 3. Shared `FullDenseInvW`, `FullResBufOkW`, and BVE/BCE transport helpers
(`FullBveVarHelpers`) -/

namespace FullBveVarHelpers

theorem fullDenseInv_exists_witness {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) : ∃ F_cur, FullDenseInvW c F0 F_cur s :=
  let ⟨F_cur, hw⟩ := h.1.witness
  ⟨F_cur, h.1.lengths, hw, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem FullLastLearnedWf.of_refs_subset {s s' : FullState}
    (h : FullLastLearnedWf s) (hll : s'.scratch.last_learned = s.scratch.last_learned)
    (hsub : ∀ r ∈ fullArenaClauseRefs s, r ∈ fullArenaClauseRefs s') : FullLastLearnedWf s' := by
  intro i hi; dsimp only; rw [hll]
  exact (h i hi).elim Or.inl fun hr => Or.inr (hsub _ hr)

theorem FullExtScratchOk.of_pres {c : FullCfg} {s s' : FullState}
    (h : FullExtScratchOk c s) (hpres : FullExtScratchPres s s')
    (hsub : ∀ r ∈ fullArenaClauseRefs s, r ∈ fullArenaClauseRefs s') : FullExtScratchOk c s' :=
  ⟨FullLastLearnedWf.of_refs_subset h.1 hpres.1 hsub, hpres.2 ▸ h.2⟩

theorem level0_unit_conflict_unsat {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullCoreInv c F0 s) (hl0 : s.core.cur_level = 0) {lit : Nat}
    (hlt : lit < 2 * s.core.cur_vars) (hfals : s.core.vals[lit]?.getD 0#8 = 0xFF#8)
    (hent : ∀ F_cur, FullWitnessInv c F0 F_cur s.core →
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit])) : F0.Unsat := by
  obtain ⟨F_cur, hw⟩ := h.witness
  refine hw.ext_sound.2
    (unsat_of_entails_nil (entails_of_mem_or_false (hent F_cur hw) fun l hl => ?_))
  simp only [List.mem_singleton] at hl; subst hl; right
  obtain ⟨i, hi, hieq⟩ := (hw.vals_false_iff l hlt).mp hfals
  have hs := hw.level0_sound i hi (by have := hw.lvl_le i hi; omega)
  rwa [hieq] at hs

private theorem watchSlice_relocate {F F' : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} (hF : (cnfOfClauses F').Entails (cnfOfClauses F))
    (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : WatchSliceOk F k lit p rem) : WatchSliceOk F' k' lit p' rem := by
  induction h generalizing p' with
  | empty => exact .empty
  | @bin p rem w0 hp hflag hne hlt hent _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hflag hne (by omega)
      (CNF.entails_clause_trans hF hent)
      (ih (p' := p' + 1) fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 1) (by omega))
  | @large p rem w0 cref hp hp1 hflag hlt href _ ih =>
    refine .large (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hflag hlt (hsub _ href)
      (ih (p' := p' + 2) fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 2) (by omega))

private theorem denseWatchSlice_relocate {F F' : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} (hF : (cnfOfClauses F').Entails (cnfOfClauses F))
    (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : DenseWatchSliceOk F k lit p rem) : DenseWatchSliceOk F' k' lit p' rem := by
  induction h generalizing p' with
  | empty => exact .empty
  | @bin p rem w0 hp hflag hne hlt hent _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hflag hne (by omega)
      (CNF.entails_clause_trans hF hent)
      (ih (p' := p' + 1) fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 1) (by omega))
  | @occ p rem w0 cref hp hp1 hflag hsz hlt href _ ih =>
    refine .occ (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hflag hsz hlt (hsub _ href)
      (ih (p' := p' + 2) fun idx hi => by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hwstk (idx + 2) (by omega))

private theorem watchSlice_append_bin {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} {w0 : BitVec 32} (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : WatchSliceOk F_cur k lit p rem) (hw0 : k'.wstk[p' + rem]? = some w0)
    (hflag : (w0 &&& 0x80000000#32) ≠ 0#32) (hne : w0 ≠ 0xFFFFFFFF#32)
    (hlt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k'.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat])) :
    WatchSliceOk F_cur k' lit p' (rem + 1) := by
  induction h generalizing p' with
  | empty => exact .bin (by simpa using hw0) hflag hne hlt hent .empty
  | @bin p rem w hp hf hn hl he _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hn (by omega) he ?_
    exact ih (p' := p' + 1)
      (fun idx hi => by simpa [show p' + 1 + idx = p' + (idx + 1) by omega,
        show p + 1 + idx = p + (idx + 1) by omega] using hwstk (idx + 1) (by omega))
      (by simpa [show p' + 1 + rem = p' + (rem + 1) by omega] using hw0)
  | @large p rem w cref hp hp1 hf hl href _ ih =>
    refine .large (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hf hl (hsub _ href) ?_
    exact ih (p' := p' + 2)
      (fun idx hi => by simpa [show p' + 2 + idx = p' + (idx + 2) by omega,
        show p + 2 + idx = p + (idx + 2) by omega] using hwstk (idx + 2) (by omega))
      (by simpa [show p' + 2 + rem = p' + (rem + 2) by omega] using hw0)

private theorem watchSlice_append_large {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} {w0 cref : BitVec 32} (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : WatchSliceOk F_cur k lit p rem)
    (hw0 : k'.wstk[p' + rem]? = some w0) (hw1 : k'.wstk[p' + rem + 1]? = some cref)
    (hflag : (w0 &&& 0x80000000#32) = 0#32) (hlt : cref.toNat < 0x80000000)
    (href : cref.toNat ∈ fullArenaClauseRefsCore k') :
    WatchSliceOk F_cur k' lit p' (rem + 2) := by
  induction h generalizing p' with
  | empty => exact .large (by simpa using hw0) (by simpa using hw1) hflag hlt href .empty
  | @bin p rem w hp hf hn hl he _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hn (by omega) he ?_
    exact ih (p' := p' + 1)
      (fun idx hi => by simpa [show p' + 1 + idx = p' + (idx + 1) by omega,
        show p + 1 + idx = p + (idx + 1) by omega] using hwstk (idx + 1) (by omega))
      (by simpa [show p' + 1 + rem = p' + (rem + 1) by omega] using hw0)
      (by simpa [show p' + 1 + rem + 1 = p' + (rem + 1) + 1 by omega] using hw1)
  | @large p rem w cr hp hp1 hf hl hr _ ih =>
    refine .large (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hf hl (hsub _ hr) ?_
    exact ih (p' := p' + 2)
      (fun idx hi => by simpa [show p' + 2 + idx = p' + (idx + 2) by omega,
        show p + 2 + idx = p + (idx + 2) by omega] using hwstk (idx + 2) (by omega))
      (by simpa [show p' + 2 + rem = p' + (rem + 2) by omega] using hw0)
      (by simpa [show p' + 2 + rem + 1 = p' + (rem + 2) + 1 by omega] using hw1)

private theorem denseWatchSlice_append_bin {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} {w0 : BitVec 32} (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : DenseWatchSliceOk F_cur k lit p rem) (hw0 : k'.wstk[p' + rem]? = some w0)
    (hflag : (w0 &&& 0x80000000#32) ≠ 0#32) (hne : w0 ≠ 0xFFFFFFFF#32)
    (hlt : (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k'.cur_vars)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause [lit, (w0 &&& 0x7FFFFFFF#32).toNat])) :
    DenseWatchSliceOk F_cur k' lit p' (rem + 1) := by
  induction h generalizing p' with
  | empty => exact .bin (by simpa using hw0) hflag hne hlt hent .empty
  | @bin p rem w hp hf hn hl he _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hn (by omega) he ?_
    exact ih (p' := p' + 1)
      (fun idx hi => by simpa [show p' + 1 + idx = p' + (idx + 1) by omega,
        show p + 1 + idx = p + (idx + 1) by omega] using hwstk (idx + 1) (by omega))
      (by simpa [show p' + 1 + rem = p' + (rem + 1) by omega] using hw0)
  | @occ p rem w cref hp hp1 hf hsz hl href _ ih =>
    refine .occ (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hf hsz hl (hsub _ href) ?_
    exact ih (p' := p' + 2)
      (fun idx hi => by simpa [show p' + 2 + idx = p' + (idx + 2) by omega,
        show p + 2 + idx = p + (idx + 2) by omega] using hwstk (idx + 2) (by omega))
      (by simpa [show p' + 2 + rem = p' + (rem + 2) by omega] using hw0)

private theorem denseWatchSlice_append_occ {F_cur : List (List Nat)} {k k' : FullCoreState}
    {lit p p' rem : Nat} {w0 cref : BitVec 32} (hvars : k.cur_vars ≤ k'.cur_vars)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hwstk : ∀ idx < rem, k'.wstk[p' + idx]? = k.wstk[p + idx]?)
    (h : DenseWatchSliceOk F_cur k lit p rem)
    (hw0 : k'.wstk[p' + rem]? = some w0) (hw1 : k'.wstk[p' + rem + 1]? = some cref)
    (hflag : (w0 &&& 0x80000000#32) = 0#32) (hsz : 3 ≤ w0.toNat) (hlt : cref.toNat < 0x80000000)
    (href : cref.toNat ∈ fullArenaClauseRefsCore k') :
    DenseWatchSliceOk F_cur k' lit p' (rem + 2) := by
  induction h generalizing p' with
  | empty => exact .occ (by simpa using hw0) (by simpa using hw1) hflag hsz hlt href .empty
  | @bin p rem w hp hf hn hl he _ ih =>
    refine .bin (by simpa using (hwstk 0 (by omega)).trans hp) hf hn (by omega) he ?_
    exact ih (p' := p' + 1)
      (fun idx hi => by simpa [show p' + 1 + idx = p' + (idx + 1) by omega,
        show p + 1 + idx = p + (idx + 1) by omega] using hwstk (idx + 1) (by omega))
      (by simpa [show p' + 1 + rem = p' + (rem + 1) by omega] using hw0)
      (by simpa [show p' + 1 + rem + 1 = p' + (rem + 1) + 1 by omega] using hw1)
  | @occ p rem w cr hp hp1 hf hsz0 hl hr _ ih =>
    refine .occ (by simpa using (hwstk 0 (by omega)).trans hp)
      (by simpa using (hwstk 1 (by omega)).trans hp1) hf hsz0 hl (hsub _ hr) ?_
    exact ih (p' := p' + 2)
      (fun idx hi => by simpa [show p' + 2 + idx = p' + (idx + 2) by omega,
        show p + 2 + idx = p + (idx + 2) by omega] using hwstk (idx + 2) (by omega))
      (by simpa [show p' + 2 + rem = p' + (rem + 2) by omega] using hw0)
      (by simpa [show p' + 2 + rem + 1 = p' + (rem + 2) + 1 by omega] using hw1)

theorem fullWatchPush_preserves_modeWatchesInv {F_cur : List (List Nat)}
    {k k' : FullCoreState} {lit w0 w1 cnt : BitVec 32} {ok : Bool}
    (hw : ModeWatchesInv F_cur k) (hlay : WatchStackLayout k')
    (hvars : k'.cur_vars = k.cur_vars) (hdm : k'.dense_mode = k.dense_mode)
    (hsub : ∀ r ∈ fullArenaClauseRefsCore k, r ∈ fullArenaClauseRefsCore k')
    (hbin : cnt.toNat = 1 →
      (w0 &&& 0x80000000#32) ≠ 0#32 ∧ w0 ≠ 0xFFFFFFFF#32 ∧
      (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k'.cur_vars ∧
      (cnfOfClauses F_cur).EntailsClause (cnfClause [lit.toNat, (w0 &&& 0x7FFFFFFF#32).toNat]))
    (hlarge : cnt.toNat = 2 →
      (w0 &&& 0x80000000#32) = 0#32 ∧ (k.dense_mode ≠ 0#64 → 3 ≤ w0.toNat) ∧
      w1.toNat < 0x80000000 ∧ w1.toNat ∈ fullArenaClauseRefsCore k')
    (hother : ∀ l < 2 * k.cur_vars, l ≠ lit.toNat →
      fullWatchSizeCore k' l = fullWatchSizeCore k l ∧
      ∀ idx < fullWatchSizeCore k l,
        k'.wstk[fullWatchOffCore k' l + idx]? = k.wstk[fullWatchOffCore k l + idx]?)
    (hok_true : ok = true →
      lit.toNat < 2 * k.cur_vars ∧ (cnt.toNat = 1 ∨ cnt.toNat = 2) ∧
      fullWatchSizeCore k' lit.toNat = fullWatchSizeCore k lit.toNat + cnt.toNat ∧
      (∀ idx < fullWatchSizeCore k lit.toNat,
        k'.wstk[fullWatchOffCore k' lit.toNat + idx]? =
          k.wstk[fullWatchOffCore k lit.toNat + idx]?) ∧
      k'.wstk[fullWatchOffCore k' lit.toNat + fullWatchSizeCore k lit.toNat]? = some w0 ∧
      (cnt.toNat = 2 →
        k'.wstk[fullWatchOffCore k' lit.toNat + fullWatchSizeCore k lit.toNat + 1]? = some w1))
    (hok_false : ok = false → lit.toNat < 2 * k.cur_vars →
      fullWatchSizeCore k' lit.toNat = fullWatchSizeCore k lit.toNat ∧
      ∀ idx < fullWatchSizeCore k lit.toNat,
        k'.wstk[fullWatchOffCore k' lit.toNat + idx]? =
          k.wstk[fullWatchOffCore k lit.toNat + idx]?) :
    ModeWatchesInv F_cur k' := by
  have hrefl : (cnfOfClauses F_cur).Entails (cnfOfClauses F_cur) := by
    rw [CNF.entails_def]; exact fun _ h => h
  unfold ModeWatchesInv at hw ⊢; rw [hdm]
  by_cases hc : k.dense_mode = 0#64 <;> simp only [hc, ↓reduceIte] at hw ⊢
  · refine ⟨hlay, fun l hl => ?_⟩
    by_cases hle : l = lit.toNat
    · subst hle; cases ok with
      | false =>
        obtain ⟨hsz, hslice⟩ := hok_false rfl (hvars ▸ hl); rw [hsz]
        exact watchSlice_relocate hrefl (by omega) hsub hslice (hw.slices _ (hvars ▸ hl))
      | true =>
        obtain ⟨_, hcnt, hsz, hpre, hw0, hw1⟩ := hok_true rfl; rw [hsz]
        rcases hcnt with hc1 | hc2
        · rw [hc1]; obtain ⟨hf, hn, hlt, hent⟩ := hbin hc1
          exact watchSlice_append_bin (by omega) hsub hpre
            (hw.slices _ (hvars ▸ hl)) hw0 hf hn hlt hent
        · rw [hc2]; obtain ⟨hf, _, hlt, href⟩ := hlarge hc2
          exact watchSlice_append_large (by omega) hsub hpre
            (hw.slices _ (hvars ▸ hl)) hw0 (hw1 hc2) hf hlt href
    · obtain ⟨hsz, hslice⟩ := hother l (hvars ▸ hl) hle; rw [hsz]
      exact watchSlice_relocate hrefl (by omega) hsub hslice (hw.slices l (hvars ▸ hl))
  · refine ⟨hlay, fun l hl => ?_⟩
    by_cases hle : l = lit.toNat
    · subst hle; cases ok with
      | false =>
        obtain ⟨hsz, hslice⟩ := hok_false rfl (hvars ▸ hl); rw [hsz]
        exact denseWatchSlice_relocate hrefl (by omega) hsub hslice (hw.slices _ (hvars ▸ hl))
      | true =>
        obtain ⟨_, hcnt, hsz, hpre, hw0, hw1⟩ := hok_true rfl; rw [hsz]
        rcases hcnt with hc1 | hc2
        · rw [hc1]; obtain ⟨hf, hn, hlt, hent⟩ := hbin hc1
          exact denseWatchSlice_append_bin (by omega) hsub hpre
            (hw.slices _ (hvars ▸ hl)) hw0 hf hn hlt hent
        · rw [hc2]; obtain ⟨hf, h3, hlt, href⟩ := hlarge hc2
          exact denseWatchSlice_append_occ (by omega) hsub hpre
            (hw.slices _ (hvars ▸ hl)) hw0 (hw1 hc2) hf (h3 hc) hlt href
    · obtain ⟨hsz, hslice⟩ := hother l (hvars ▸ hl) hle; rw [hsz]
      exact denseWatchSlice_relocate hrefl (by omega) hsub hslice (hw.slices l (hvars ▸ hl))

theorem FullArenaVarsNodup.of_markGarb {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (hlen : s.LengthsOk c) (hw : FullWitnessInv c F0 F_cur s.core)
    (hnd : FullArenaVarsNodup s) {cref : Nat} (href : cref ∈ fullArenaClauseRefs s)
    (ag' : BitVec 64) :
    let s' : FullState :=
      { s with core :=
        { s.core with
          arena := s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32)
          arena_garbage := ag' } }
    FullArenaVarsNodup s' := by
  intro s' r hr hng
  have hmg := hw.arena.markGarb hlen.core_ok href ag'
  have hr0 : r ∈ fullArenaClauseRefsCore s.core := by
    change r ∈ fullArenaClauseRefsCore s'.core at hr; rwa [hmg.1] at hr
  have har_len : cref < s.core.arena.length := by
    have := (hw.arena.refs_wf cref href).1; have := hlen.core_ok.arena_len_le
    have := hlen.core_ok.arena_len_arr; omega
  have hne : r ≠ cref := by
    rintro rfl
    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore s' at hng
    rw [List.getElem?_set_self har_len, Option.getD_some] at hng
    exact bv32_bit19_or_garb_ne0 (fullArenaHdr s r) (by simpa using hng)
  have hng0 : fullArenaClauseGarb s r = false := by
    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore at hng ⊢
    simpa [s', List.getElem?_set_ne hne.symm] using hng
  have hdisj : r + 3 + fullArenaClauseSizeCore s.core r ≤ cref ∨ cref + 3 ≤ r := by
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl (hw.arena.disjoint hr0 href hlt)
    · exact Or.inr (by have := hw.arena.disjoint href hr0 hgt; omega)
  have hbd : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
    have := (hw.arena.refs_wf r hr0).2.2.1; have := (hw.arena.refs_wf r hr0).2.2.2.1
    have := hlen.core_ok.arena_len_le; have := hlen.core_ok.arena_len_arr; omega
  have hlits : fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r :=
    (fullArenaClauseLitsCore_set_outside (v := fullArenaHdr s cref ||| 0x00080000#32)
      hbd hdisj).2
  unfold fullArenaClauseLits; rw [hlits]; exact hnd r hr0 hng0

theorem FullDenseInvW.with_oom {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) (v : BitVec 64) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with oom := v } } := by
  refine ⟨⟨{ h.1.core_ok with vals_len := h.1.core_ok.vals_len }, h.1.scratch_ok⟩,
    ?_, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
  let hw := h.2.1
  exact { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }
                  watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }

theorem fullDenseInv_with_oom {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullDenseInv c F0 s) (v : BitVec 64) :
    FullDenseInv c F0 { s with core := { s.core with oom := v } } :=
  let ⟨_, hw⟩ := fullDenseInv_exists_witness h
  FullDenseInvW.toDense (FullDenseInvW.with_oom hw v)

theorem FullDenseInvW.with_inconsistent {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) (v : BitVec 64)
    (hinc : v ≠ 0#64 → (cnfOfClauses F_cur).Unsat) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with inconsistent := v } } := by
  refine ⟨⟨{ h.1.core_ok with vals_len := h.1.core_ok.vals_len }, h.1.scratch_ok⟩,
    ?_, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
  let hw := h.2.1
  exact { hw with inconsistent_sound := hinc
                  arena := { hw.arena with len_ok := hw.arena.len_ok }
                  watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }

theorem FullDenseInvW.with_scratch_buf {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {scr' : List (BitVec 32)}
    (hlen : scr'.length = c.scratch_cap) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with scratch_buf := scr' } } :=
  ⟨⟨h.1.core_ok, { h.1.scratch_ok with scratch_buf_len := hlen }⟩,
   h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem FullDenseInvW.with_bve_cnt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) (v : BitVec 64) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with bve_cnt := v } } :=
  ⟨⟨h.1.core_ok, { h.1.scratch_ok with scratch_buf_len := h.1.scratch_ok.scratch_buf_len }⟩,
   h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem FullDenseInvW.with_bce_cnt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) (v : BitVec 64) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with bce_cnt := v } } :=
  ⟨⟨h.1.core_ok, { h.1.scratch_ok with scratch_buf_len := h.1.scratch_ok.scratch_buf_len }⟩,
   h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem FullDenseInvW.with_flags_unassigned {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {fl' : List (BitVec 32)}
    (hfl : fl'.length = c.max_vars) (un' : BitVec 64) :
    FullDenseInvW c F0 F_cur
      { s with core := { s.core with flags := fl', unassigned := un' } } := by
  refine ⟨⟨{ h.1.core_ok with flags_len := hfl }, h.1.scratch_ok⟩, ?_, h.2.2.1, h.2.2.2.1,
    h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
  let hw := h.2.1
  exact { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }
                  watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }

theorem FullDenseInvW.of_safetySlice {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} (h : FullDenseInvW c F0 F_cur s) (hlen' : s'.LengthsOk c)
    (hcore : PreservesCoreSlice (fullSafetySlice c).coreProj s s')
    (hpres : FullExtScratchPres s s') : FullDenseInvW c F0 F_cur s' := by
  have heq : s'.core = s.core := fullCoreState_agrees_with_scratch hcore
  refine ⟨hlen', heq ▸ h.2.1, ?_, ?_, ?_, heq ▸ h.2.2.2.2.2.1, heq ▸ h.2.2.2.2.2.2⟩
  · unfold FullLitMarksClear FullMrkZero; rw [heq]; exact h.2.2.1
  · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
    rw [heq]; exact h.2.2.2.1
  · exact FullExtScratchOk.of_pres h.2.2.2.2.1 hpres fun r hr => by
      unfold fullArenaClauseRefs; rwa [heq]

theorem FullDenseInvW.of_deleteBinary {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {wvec' wstk' : List (BitVec 32)} {wu' nb' : BitVec 64}
    (hlen' : ({ s with core := { s.core with wvec := wvec', wstk := wstk',
                                             wusable := wu', num_binary := nb' } } :
      FullState).LengthsOk c)
    (hwat : ModeWatchesInv F_cur
      { s.core with wvec := wvec', wstk := wstk', wusable := wu', num_binary := nb' }) :
    FullDenseInvW c F0 F_cur
      { s with core := { s.core with wvec := wvec', wstk := wstk',
                                     wusable := wu', num_binary := nb' } } := by
  let hw := h.2.1
  refine ⟨hlen', { hw with arena := { hw.arena with len_ok := hw.arena.len_ok }, watches := hwat },
    h.2.2.1, ?_, ?_, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
  · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
      fullArenaClauseRefsCore fullArenaClauseGarbCore fullArenaClauseLitsCore fullArenaHdrCore
      fullArenaClauseSizeCore
    exact h.2.2.2.1
  · unfold FullExtScratchOk FullLastLearnedWf fullArenaClauseRefs fullArenaClauseRefsCore
    exact h.2.2.2.2.1

theorem FullDenseInvW.of_addUnit {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' cl' : Nat} {unass' unfl' inc' : BitVec 64} {sc' : FullScratch}
    (hlen' : ({ s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te',
                            propagated := prop', cur_level := cl', unassigned := unass',
                            unflushed := unfl', inconsistent := inc' }
      scratch := sc' } : FullState).LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur
      { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                    trl := trl', trail_pos := tp', trail_end := te',
                    propagated := prop', cur_level := cl', unassigned := unass',
                    unflushed := unfl', inconsistent := inc' })
    (hpres : FullExtScratchPres s
      { s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te',
                              propagated := prop', cur_level := cl', unassigned := unass',
                              unflushed := unfl', inconsistent := inc' }
        scratch := sc' })
    (hcl0 : cl' = 0) :
    FullDenseInvW c F0 F_cur
      { s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te',
                              propagated := prop', cur_level := cl', unassigned := unass',
                              unflushed := unfl', inconsistent := inc' }
        scratch := sc' } := by
  refine ⟨hlen', hw', h.2.2.1, ?_, ?_, hcl0, h.2.2.2.2.2.2⟩
  · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
      fullArenaClauseRefsCore fullArenaClauseGarbCore fullArenaClauseLitsCore fullArenaHdrCore
      fullArenaClauseSizeCore
    exact h.2.2.2.1
  · exact FullExtScratchOk.of_pres h.2.2.2.2.1 hpres fun r hr => by
      unfold fullArenaClauseRefs fullArenaClauseRefsCore at hr ⊢; exact hr

theorem FullDenseInvW.of_addBin {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' : Nat} {unass' unfl' : BitVec 64} {wvec' wstk' : List (BitVec 32)}
    {wlen' : Nat} {wu' nb' oom' inc' : BitVec 64} {phases' : List (BitVec 8)}
    {wsort' : List (BitVec 32)}
    (hlen' : ({ s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te',
                            unassigned := unass', unflushed := unfl', wvec := wvec',
                            wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
                            oom := oom', inconsistent := inc' }
      scratch := { s.scratch with phases := phases', wsort := wsort' } } : FullState).LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur
      { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                    trl := trl', trail_pos := tp', trail_end := te',
                    unassigned := unass', unflushed := unfl', wvec := wvec',
                    wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
                    oom := oom', inconsistent := inc' }) :
    FullDenseInvW c F0 F_cur
      { s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te',
                              unassigned := unass', unflushed := unfl', wvec := wvec',
                              wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb',
                              oom := oom', inconsistent := inc' }
        scratch := { s.scratch with phases := phases', wsort := wsort' } } := by
  refine ⟨hlen', hw', h.2.2.1, ?_, ?_, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
  · unfold FullArenaVarsNodup fullArenaClauseRefs fullArenaClauseGarb fullArenaClauseLits
      fullArenaClauseRefsCore fullArenaClauseGarbCore fullArenaClauseLitsCore fullArenaHdrCore
      fullArenaClauseSizeCore
    exact h.2.2.2.1
  · exact FullExtScratchOk.of_pres h.2.2.2.2.1 ⟨rfl, rfl⟩ fun r hr => by
      unfold fullArenaClauseRefs fullArenaClauseRefsCore at hr ⊢; exact hr

theorem FullDenseInvW.of_markGarb_zero {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {cref : Nat}
    (href : cref ∈ fullArenaClauseRefs s) (ag' : BitVec 64) :
    let s' : FullState :=
      { s with core :=
        { s.core with
          arena := s.core.arena.set cref (fullArenaHdr s cref ||| 0x00080000#32)
          arena_garbage := ag' } }
    FullDenseInvW c F0 F_cur s' := by
  intro s'
  have hlen' : s'.LengthsOk c :=
    ⟨{ h.1.core_ok with arena_len_arr := by simp [s', h.1.core_ok.arena_len_arr] },
     h.1.scratch_ok⟩
  have hmg := h.2.1.arena.markGarb h.1.core_ok href ag'
  have hrefs : fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core := hmg.1
  have hdisj_lits : ∀ {r : Nat}, r ∈ fullArenaClauseRefsCore s.core → r ≠ cref →
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := fun {r} hr hne => by
    have hdisj : r + 3 + fullArenaClauseSizeCore s.core r ≤ cref ∨ cref + 3 ≤ r := by
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inl (h.2.1.arena.disjoint hr href hlt)
      · exact Or.inr (by have := h.2.1.arena.disjoint href hr hgt; omega)
    have hbd : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
      have := (h.2.1.arena.refs_wf r hr).2.2.1
      have := (h.2.1.arena.refs_wf r hr).2.2.2.1
      have := h.1.core_ok.arena_len_le; have := h.1.core_ok.arena_len_arr; omega
    exact (fullArenaClauseLitsCore_set_outside hbd hdisj).2
  have hl0 : s.core.cur_level = 0 := h.2.2.2.2.2.1
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { h.2.1 with
      arena := hmg.2
      watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun r hr => hrefs ▸ hr)
      reason_inv := fun idx hi hne =>
        absurd (h.2.1.level0_rsn_none idx hi (by have := h.2.1.lvl_le idx hi; omega)) hne
      reason_lit_mem := fun idx hi hne _ =>
        absurd (h.2.1.level0_rsn_none idx hi (by have := h.2.1.lvl_le idx hi; omega)) hne }
  exact ⟨hlen', hw', h.2.2.1, FullArenaVarsNodup.of_markGarb h.1 h.2.1 h.2.2.2.1 href ag',
    FullExtScratchOk.of_pres h.2.2.2.2.1 ⟨rfl, rfl⟩ (fun r hr => by
      change r ∈ fullArenaClauseRefsCore s'.core; rwa [hrefs]),
    hl0, h.2.2.2.2.2.2⟩

theorem addEntailedClause_preserves_witness {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {len : Nat}
    {arena' wvec' wstk' : List (BitVec 32)} {wlen' : Nat} {wusable' ni' : BitVec 64}
    (hlen' : ({ s with
      core := { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len,
                            wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable',
                            num_irred := ni' } } : FullState).LengthsOk c)
    (hge3 : 3 ≤ len)
    (hlits_lt : ∀ l ∈ fullArenaClauseLitsCore
      { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len } s.core.arena_len,
      l < 2 * s.core.cur_vars)
    (hnodup : ((fullArenaClauseLitsCore
      { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len }
        s.core.arena_len).map (· / 2)).Nodup)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause (fullArenaClauseLitsCore
      { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len } s.core.arena_len)))
    (hhold_arena : ∀ k < s.core.arena_len, arena'[k]? = s.core.arena[k]?)
    (hnew_noshrk : (arena'[s.core.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32)
    (hnew_sz : (arena'[s.core.arena_len + 2]?.getD 0#32).toNat = len)
    (hwat : ModeWatchesInv F_cur
      { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len,
                    wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable',
                    num_irred := ni' }) :
    FullDenseInvW c F0 F_cur
      { s with
        core := { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len,
                              wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable',
                              num_irred := ni' } } := by
  let s' : FullState :=
    { s with
      core := { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len,
                            wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable',
                            num_irred := ni' } }
  let hw := h.2.1
  have hnxt_hold := hw.arena.arenaNextOff_extend (alen' := s.core.arena_len + 3 + len)
    (by omega) hhold_arena
  have hrefs :
      fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core ++ [s.core.arena_len] :=
    fullArenaClauseRefsCore_append hw.arena hge3 rfl hhold_arena hnew_noshrk hnew_sz
  have hold_garb : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := fun r hr => by
    have := (hw.arena.refs_wf r hr).1
    unfold fullArenaClauseGarbCore fullArenaHdrCore s'; simp [hhold_arena r (by omega)]
  have hold_sz : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := fun r hr => by
    have := (hw.arena.refs_wf r hr).1
    unfold fullArenaClauseSizeCore s'; simp [hhold_arena (r + 2) (by omega)]
  have hold_lits : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := fun r hr => by
    have hwf := hw.arena.refs_wf r hr
    have h1l := h.1.core_ok.arena_len_arr; have h1e := h.1.core_ok.arena_len_le
    have h2l : arena'.length = c.arena_cap := hlen'.core_ok.arena_len_arr
    have h2e : s.core.arena_len + 3 + len ≤ c.arena_cap := hlen'.core_ok.arena_len_le
    have hbd_ar : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena_len := by omega
    exact fullArenaClauseLitsCore_eq_of_hold (by omega) (by dsimp only [s']; omega)
      (hold_sz r hr) fun j hj => hhold_arena (r + 3 + j) (by omega)
  have hnew_lits_eq : fullArenaClauseLitsCore s'.core s.core.arena_len =
      fullArenaClauseLitsCore
        { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len }
        s.core.arena_len := by
    unfold fullArenaClauseLitsCore fullArenaClauseSizeCore; rfl
  have harena' : FullArenaClausesInv c F_cur s'.core := by
    refine ⟨Or.inr (by dsimp [s']; omega), ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · have hwf := hw.arena.refs_wf r hr
        rw [hnxt_hold r hr, hold_sz r hr]
        refine ⟨by dsimp [s']; omega, hwf.2.1, hwf.2.2.1, by dsimp [s']; omega, ?_⟩
        rcases hwf.2.2.2.2 with he | h3 <;> right <;> dsimp [s'] <;> omega
      · have hnxt_new : fullArenaNextOff s'.core.arena s'.core.arena_len s.core.arena_len =
            s.core.arena_len + 3 + len := by unfold fullArenaNextOff s'; simp [hnew_sz, hnew_noshrk]
        rw [hnxt_new, show fullArenaClauseSizeCore s'.core s.core.arena_len = len from hnew_sz]
        refine ⟨by dsimp [s']; omega, hge3, by omega, by dsimp [s']; omega, Or.inl (by dsimp [s'])⟩
    · intro r hr hsh; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · have hr3 := (hw.arena.refs_wf r hr).1
        have hsh0 : (fullArenaHdrCore s.core r &&& 0x00800000#32) ≠ 0#32 := by
          unfold fullArenaHdrCore at hsh ⊢; dsimp only [s'] at hsh
          rwa [hhold_arena r (by omega)] at hsh
        obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
        exact ⟨t, by rw [hold_sz r hr]; exact ht1, by dsimp only [s']; omega,
          by dsimp only [s']; rw [hhold_arena t ht2]; exact hsent⟩
      · unfold fullArenaHdrCore at hsh; dsimp only [s'] at hsh; exact absurd hnew_noshrk hsh
    · intro r hr hng; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · rw [hold_garb r hr] at hng; rw [hold_lits r hr]; exact hw.arena.lits_lt r hr hng
      · rw [hnew_lits_eq]; exact hlits_lt
    · intro r hr hng; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · rw [hold_garb r hr] at hng; rw [hold_lits r hr]; exact hw.arena.entails r hr hng
      · rw [hnew_lits_eq]; exact hent
  have hnd' : FullArenaVarsNodup s' := by
    intro r hr hng
    change r ∈ fullArenaClauseRefsCore s'.core at hr
    rw [hrefs, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · change fullArenaClauseGarbCore s'.core r = false at hng
      rw [hold_garb r hr] at hng
      unfold fullArenaClauseLits; rw [hold_lits r hr]; exact h.2.2.2.1 r hr hng
    · change ((fullArenaClauseLitsCore s'.core s.core.arena_len).map (· / 2)).Nodup
      rw [hnew_lits_eq]; exact hnodup
  have hl0 : s.core.cur_level = 0 := h.2.2.2.2.2.1
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := harena', watches := hwat
      reason_inv := fun idx hi hne =>
        absurd (hw.level0_rsn_none idx hi (by have := hw.lvl_le idx hi; omega)) hne
      reason_lit_mem := fun idx hi hne _ =>
        absurd (hw.level0_rsn_none idx hi (by have := hw.lvl_le idx hi; omega)) hne }
  exact ⟨hlen', hw', h.2.2.1, hnd',
    FullExtScratchOk.of_pres h.2.2.2.2.1 ⟨rfl, rfl⟩ (fun r hr => by
      change r ∈ fullArenaClauseRefsCore s'.core; rw [hrefs]; exact List.mem_append_left _ hr),
    hl0, h.2.2.2.2.2.2⟩

theorem addGarbageClause_preserves_witness {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {len : Nat}
    {arena' wvec' wstk' : List (BitVec 32)} {wlen' : Nat} {wusable' ag' oom' : BitVec 64}
    (hlen' : ({ s with
      core := { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len,
                            wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable',
                            arena_garbage := ag', oom := oom' } } : FullState).LengthsOk c)
    (hge3 : 3 ≤ len)
    (hhold_arena : ∀ k < s.core.arena_len, arena'[k]? = s.core.arena[k]?)
    (hnew_noshrk : (arena'[s.core.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32)
    (hnew_garb : (arena'[s.core.arena_len]?.getD 0#32 &&& 0x00080000#32) ≠ 0#32)
    (hnew_sz : (arena'[s.core.arena_len + 2]?.getD 0#32).toNat = len)
    (hwat : ModeWatchesInv F_cur
      { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len,
                    wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable',
                    arena_garbage := ag', oom := oom' }) :
    FullDenseInvW c F0 F_cur
      { s with
        core := { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len,
                              wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable',
                              arena_garbage := ag', oom := oom' } } := by
  let s' : FullState :=
    { s with
      core := { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len,
                            wvec := wvec', wstk := wstk', wlen := wlen', wusable := wusable',
                            arena_garbage := ag', oom := oom' } }
  let hw := h.2.1
  have hnxt_hold := hw.arena.arenaNextOff_extend (alen' := s.core.arena_len + 3 + len)
    (by omega) hhold_arena
  have hrefs :
      fullArenaClauseRefsCore s'.core = fullArenaClauseRefsCore s.core ++ [s.core.arena_len] :=
    fullArenaClauseRefsCore_append hw.arena hge3 rfl hhold_arena hnew_noshrk hnew_sz
  have hold_garb : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := fun r hr => by
    have := (hw.arena.refs_wf r hr).1
    unfold fullArenaClauseGarbCore fullArenaHdrCore s'; simp [hhold_arena r (by omega)]
  have hold_sz : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := fun r hr => by
    have := (hw.arena.refs_wf r hr).1
    unfold fullArenaClauseSizeCore s'; simp [hhold_arena (r + 2) (by omega)]
  have hold_lits : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := fun r hr => by
    have hwf := hw.arena.refs_wf r hr
    have h1l := h.1.core_ok.arena_len_arr; have h1e := h.1.core_ok.arena_len_le
    have h2l : arena'.length = c.arena_cap := hlen'.core_ok.arena_len_arr
    have h2e : s.core.arena_len + 3 + len ≤ c.arena_cap := hlen'.core_ok.arena_len_le
    have hbd_ar : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena_len := by omega
    exact fullArenaClauseLitsCore_eq_of_hold (by omega) (by dsimp only [s']; omega)
      (hold_sz r hr) fun j hj => hhold_arena (r + 3 + j) (by omega)
  have hnew_garb_s' : fullArenaClauseGarbCore s'.core s.core.arena_len = true := by
    unfold fullArenaClauseGarbCore fullArenaHdrCore s'; simp [hnew_garb]
  have harena' : FullArenaClausesInv c F_cur s'.core := by
    refine ⟨Or.inr (by dsimp [s']; omega), ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · have hwf := hw.arena.refs_wf r hr
        rw [hnxt_hold r hr, hold_sz r hr]
        refine ⟨by dsimp [s']; omega, hwf.2.1, hwf.2.2.1, by dsimp [s']; omega, ?_⟩
        rcases hwf.2.2.2.2 with he | h3 <;> right <;> dsimp [s'] <;> omega
      · have hnxt_new : fullArenaNextOff s'.core.arena s'.core.arena_len s.core.arena_len =
            s.core.arena_len + 3 + len := by unfold fullArenaNextOff s'; simp [hnew_sz, hnew_noshrk]
        rw [hnxt_new, show fullArenaClauseSizeCore s'.core s.core.arena_len = len from hnew_sz]
        refine ⟨by dsimp [s']; omega, hge3, by omega, by dsimp [s']; omega, Or.inl (by dsimp [s'])⟩
    · intro r hr hsh; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · have hr3 := (hw.arena.refs_wf r hr).1
        have hsh0 : (fullArenaHdrCore s.core r &&& 0x00800000#32) ≠ 0#32 := by
          unfold fullArenaHdrCore at hsh ⊢; dsimp only [s'] at hsh
          rwa [hhold_arena r (by omega)] at hsh
        obtain ⟨t, ht1, ht2, hsent⟩ := hw.arena.shrk_term r hr hsh0
        exact ⟨t, by rw [hold_sz r hr]; exact ht1, by dsimp only [s']; omega,
          by dsimp only [s']; rw [hhold_arena t ht2]; exact hsent⟩
      · unfold fullArenaHdrCore at hsh; dsimp only [s'] at hsh; exact absurd hnew_noshrk hsh
    · intro r hr hng; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · rw [hold_garb r hr] at hng; rw [hold_lits r hr]; exact hw.arena.lits_lt r hr hng
      · rw [hnew_garb_s'] at hng; cases hng
    · intro r hr hng; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · rw [hold_garb r hr] at hng; rw [hold_lits r hr]; exact hw.arena.entails r hr hng
      · rw [hnew_garb_s'] at hng; cases hng
  have hnd' : FullArenaVarsNodup s' := by
    intro r hr hng
    change r ∈ fullArenaClauseRefsCore s'.core at hr
    rw [hrefs, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · change fullArenaClauseGarbCore s'.core r = false at hng
      rw [hold_garb r hr] at hng
      unfold fullArenaClauseLits; rw [hold_lits r hr]; exact h.2.2.2.1 r hr hng
    · change fullArenaClauseGarbCore s'.core s.core.arena_len = false at hng
      rw [hnew_garb_s'] at hng; cases hng
  have hl0 : s.core.cur_level = 0 := h.2.2.2.2.2.1
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := harena', watches := hwat
      reason_inv := fun idx hi hne =>
        absurd (hw.level0_rsn_none idx hi (by have := hw.lvl_le idx hi; omega)) hne
      reason_lit_mem := fun idx hi hne _ =>
        absurd (hw.level0_rsn_none idx hi (by have := hw.lvl_le idx hi; omega)) hne }
  exact ⟨hlen', hw', h.2.2.1, hnd',
    FullExtScratchOk.of_pres h.2.2.2.2.1 ⟨rfl, rfl⟩ (fun r hr => by
      change r ∈ fullArenaClauseRefsCore s'.core; rw [hrefs]; exact List.mem_append_left _ hr),
    hl0, h.2.2.2.2.2.2⟩

theorem FullResBufOkW.with_state {F_cur : List (List Nat)} {s s' : FullState} {r_end : Nat}
    (hvars : s'.core.cur_vars = s.core.cur_vars)
    (hbuf : ∀ idx < r_end, s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?) :
    ∀ {p : Nat}, FullResBufOkW F_cur s r_end p → FullResBufOkW F_cur s' r_end p
  | _, .nil => .nil
  | p, .cons (sz := sz) hbd hsz hlts hnd hent htail => by
    have hpeq : s'.scratch.scratch_buf[p]?.getD 0#32 = s.scratch.scratch_buf[p]?.getD 0#32 := by
      rw [hbuf p (by omega)]
    have hleq : ∀ k < sz,
        (s'.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat =
        (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat := fun k hk => by
      rw [hbuf (p + 1 + k) (by omega)]
    refine .cons (sz := sz) hbd (by simpa [hpeq] using hsz) (fun k hk => by
      rw [hleq k hk, hvars]; exact hlts k hk) ?_ ?_ (with_state hvars hbuf htail)
    · have hm : ((List.range sz).map fun k =>
          (s'.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat / 2) =
          ((List.range sz).map fun k =>
          (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat / 2) :=
        List.map_congr_left fun k hk => by
          rw [List.mem_range] at hk; rw [hleq k hk]
      rw [hm]; exact hnd
    · have hm : ((List.range sz).map fun k =>
          (s'.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat) =
          ((List.range sz).map fun k =>
          (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat) :=
        List.map_congr_left fun k hk => by
          rw [List.mem_range] at hk; exact hleq k hk
      rw [hm]; exact hent

theorem FullResBufOkW.append_block {F_cur : List (List Nat)} {s s' : FullState}
    {r0 r1 sz : Nat} (hvars : s'.core.cur_vars = s.core.cur_vars)
    (hbuf : ∀ idx < r1, s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?)
    (hsz : (s'.scratch.scratch_buf[r1]?.getD 0#32).toNat = sz)
    (hlts : ∀ k < sz, (s'.scratch.scratch_buf[r1 + 1 + k]?.getD 0#32).toNat < 2 * s'.core.cur_vars)
    (hnodup : ((List.range sz).map fun k =>
      (s'.scratch.scratch_buf[r1 + 1 + k]?.getD 0#32).toNat / 2).Nodup)
    (hent : (cnfOfClauses F_cur).EntailsClause (cnfClause ((List.range sz).map fun k =>
      (s'.scratch.scratch_buf[r1 + 1 + k]?.getD 0#32).toNat))) :
    ∀ {p : Nat}, FullResBufOkW F_cur s r1 p → FullResBufOkW F_cur s' (r1 + 1 + sz) p
  | _, .nil => .cons (Nat.le_refl _) hsz hlts hnodup hent .nil
  | p, .cons (sz := sz0) hbd hpsz hplts hpnd hpent htail => by
    have hpeq : s'.scratch.scratch_buf[p]?.getD 0#32 = s.scratch.scratch_buf[p]?.getD 0#32 := by
      rw [hbuf p (by omega)]
    have hleq : ∀ k < sz0,
        (s'.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat =
        (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat := fun k hk => by
      rw [hbuf (p + 1 + k) (by omega)]
    refine .cons (sz := sz0) (by omega) (by simpa [hpeq] using hpsz)
      (fun k hk => by rw [hleq k hk, hvars]; exact hplts k hk) ?_ ?_
      (append_block hvars hbuf hsz hlts hnodup hent htail (r0 := r0))
    · have hm : ((List.range sz0).map fun k =>
          (s'.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat / 2) =
          ((List.range sz0).map fun k =>
          (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat / 2) :=
        List.map_congr_left fun k hk => by rw [List.mem_range] at hk; rw [hleq k hk]
      rw [hm]; exact hpnd
    · have hm : ((List.range sz0).map fun k =>
          (s'.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat) =
          ((List.range sz0).map fun k =>
          (s.scratch.scratch_buf[p + 1 + k]?.getD 0#32).toNat) :=
        List.map_congr_left fun k hk => by rw [List.mem_range] at hk; exact hleq k hk
      rw [hm]; exact hpent

theorem FullBveEntryOkW.to_weak {F_cur : List (List Nat)} {s : FullState} {lit : Nat}
    {w : BitVec 32} (h : FullBveEntryOkW F_cur s lit w) : FullBveWeakItemOk s w := by
  unfold FullBveEntryOkW at h; unfold FullBveWeakItemOk
  by_cases hb : (w &&& 0x80000000#32) ≠ 0#32
  · simp [hb] at h ⊢; exact h.1
  · simp [hb] at h ⊢; exact h.1

theorem FullBveEntryOkW.with_state {F_cur : List (List Nat)} {s s' : FullState} {lit : Nat}
    {w : BitVec 32} (hvars : s.core.cur_vars ≤ s'.core.cur_vars)
    (har : s'.core.arena = s.core.arena) (hal : s'.core.arena_len = s.core.arena_len)
    (h : FullBveEntryOkW F_cur s lit w) : FullBveEntryOkW F_cur s' lit w := by
  unfold FullBveEntryOkW at h ⊢
  by_cases hb : (w &&& 0x80000000#32) ≠ 0#32
  · simp [hb] at h ⊢; exact ⟨by omega, h.2⟩
  · simp only [hb, ↓reduceIte] at h ⊢
    unfold fullArenaClauseRefs fullArenaClauseRefsCore fullArenaClauseGarb
      fullArenaClauseGarbCore fullArenaHdrCore at h ⊢
    rw [har, hal]; exact h

theorem FullBveEntryOkW.to_tryBceEntry {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {lit : Nat} {w : BitVec 32} (h : FullDenseInvW c F0 F_cur s)
    (he : FullBveEntryOkW F_cur s lit w) : FullBveTryBceEntryOk c s w := by
  unfold FullBveEntryOkW at he; unfold FullBveTryBceEntryOk
  have hcv := h.1.core_ok.cur_vars_le
  by_cases hb : (w &&& 0x80000000#32) ≠ 0#32
  · simp [hb] at he ⊢; omega
  · simp only [hb, ↓reduceIte] at he ⊢
    have hwf := h.2.1.arena.refs_wf w.toNat he.1
    refine ⟨he.1, by unfold fullArenaClauseSize; omega, fun l hl => ?_, h.2.2.2.1 w.toNat he.1 he.2⟩
    exact Nat.lt_of_lt_of_le (h.2.1.arena.lits_lt w.toNat he.1 he.2 l hl) (by omega)

theorem FullBveEntryOkW.to_tryBceOpp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} {lit : Nat} {w : BitVec 32} (h : FullDenseInvW c F0 F_cur s)
    (he : FullBveEntryOkW F_cur s lit w) : FullBveTryBceOppOk c s w := by
  have he' := FullBveEntryOkW.to_tryBceEntry h he
  unfold FullBveTryBceEntryOk at he'; unfold FullBveTryBceOppOk
  by_cases hb : (w &&& 0x80000000#32) ≠ 0#32
  · simp [hb] at he' ⊢; exact he'
  · simp [hb] at he' ⊢; exact ⟨he'.1, he'.2.1, he'.2.2.1⟩

end FullBveVarHelpers

end LeanQbe.T.Examples.Kissat.Full
