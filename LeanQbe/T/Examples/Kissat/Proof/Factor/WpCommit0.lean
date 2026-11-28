/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Factor
public import LeanQbe.T.Examples.Kissat.Proof.Factor.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Factor.Helpers
public import LeanQbe.T.Examples.Kissat.Proof.Factor.Wp0
public import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts4
import LeanQbe.T.Examples.Kissat.Proof.Spec.MemBridges
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Logic.Bytes
import LeanQbe.T.Logic.Cells
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# BVA Commit Helpers, Invariants & Exit-Phase WP (`Proof.Factor.WpCommit0`)

Zero-legacy (`0` `Full*` imports, `0` placeholders, `XPost`-polymorphic) foundation for
`full_bva_commit_wp` (`13/15`):
1. `u32 <-> u64` pair packing bridges for `full_fill_u64_m7` (`wsort`) and `u64` clause copy
   (`tmp` -> `arena`).
2. `CommitArenaExt`, `Step7BvaCompactInv`, `FullDenseInvW` transition helpers, and
   `cmt_ext_fresh_var` (`bvaExtendGen`).
3. Pure AST extractors for `full_bva_commit_body` and `cmt_p2_exit_wp` covering the failure exit,
   Phase 3 reverse compaction, Phase 4 old-clause deletion/garbage-marking, and epilogue.
-/

set_option autoImplicit false

local macro "fid_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

namespace LeanQbe.T.Examples.Kissat.Proof.Factor

public section

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.ProofUtil LeanQbe.T.C0Step LeanQbe.T.C0HeadStep
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Factor
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullBvaHeapHelpers
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullBvaHeapTactics
open LeanQbe.T.Examples.Kissat.Proof.Factor.Spec
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics

@[local bv_c0] private theorem cmt_bv64_one : (1 : BitVec 64).toNat = 1 := rfl
@[local bv_c0] private theorem cmt_bv32_one : (1 : BitVec 32).toNat = 1 := rfl
@[local bv_c0] private theorem cmt_bv32_two : (2 : BitVec 32).toNat = 2 := rfl
@[local bv_c0] private theorem cmt_bv32_three : (3 : BitVec 32).toNat = 3 := rfl

/-! ## 1. `u32 <-> u64` Pair Packing & Memory Bridges -/

@[expose] def cmtPackPair64 (lo hi : BitVec 32) : BitVec 64 :=
  (hi.setWidth 64 <<< 32) ||| lo.setWidth 64

@[expose] def cmtPackPairs64 : List (BitVec 32) → List (BitVec 64)
  | lo :: hi :: rest => cmtPackPair64 lo hi :: cmtPackPairs64 rest
  | _ => []

@[expose] def cmtUnpackPairs32 : List (BitVec 64) → List (BitVec 32)
  | [] => []
  | w :: rest => w.setWidth 32 :: (w >>> 32).setWidth 32 :: cmtUnpackPairs32 rest

theorem cmtPackPairs64_length : ∀ xs : List (BitVec 32), (cmtPackPairs64 xs).length = xs.length / 2
  | [] => rfl
  | [_] => by simp [cmtPackPairs64]
  | _ :: _ :: rest => by
    simp only [cmtPackPairs64, List.length_cons, cmtPackPairs64_length rest]; omega

theorem cmtUnpackPairs32_length (ys : List (BitVec 64)) :
    (cmtUnpackPairs32 ys).length = 2 * ys.length := by
  induction ys with
  | nil => rfl
  | cons _ _ ih => simp only [cmtUnpackPairs32, List.length_cons, ih]; omega

theorem cmtPackPair64_lo (lo hi : BitVec 32) : (cmtPackPair64 lo hi).setWidth 32 = lo := by
  unfold cmtPackPair64; apply BitVec.eq_of_getElem_eq; intro k hk; simp

theorem cmtPackPair64_hi (lo hi : BitVec 32) : ((cmtPackPair64 lo hi) >>> 32).setWidth 32 = hi := by
  unfold cmtPackPair64; apply BitVec.eq_of_getElem_eq; intro k hk
  have hk64 : k < 64 := by omega
  have h32 : 32 + k < 64 := by omega
  have hnot : ¬ (32 + k < 32) := by omega
  simp [BitVec.getElem_setWidth, BitVec.getElem_ushiftRight, BitVec.getElem_or,
    BitVec.getElem_shiftLeft, BitVec.getLsbD_eq_getElem, hk, hk64, h32, hnot]

private theorem cmt_toBytes_8_split (w : BitVec 64) :
    Int.toBytes 8 (w.toNat : Int) =
      Int.toBytes 4 ((w.setWidth 32).toNat : Int) ++
        Int.toBytes 4 (((w >>> 32).setWidth 32).toNat : Int) := by
  have hw0 : ((w.setWidth 32).toNat : Int) = (w.toNat : Int) % (2 : Int) ^ (8 * 4) := by
    simp only [BitVec.toNat_setWidth]; omega
  have hw1 : (((w >>> 32).setWidth 32).toNat : Int) =
      ((w.toNat : Int) / (2 : Int) ^ 32) % (2 : Int) ^ (8 * 4) := by
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
  rw [hw0, hw1, Int.toBytes_emod (n := 4) (x := (w.toNat : Int)),
    Int.toBytes_emod (n := 4) (x := (w.toNat : Int) / (2 : Int) ^ 32)]
  have hd : ∀ k : Int, (((k / 256) / 256) / 256) / 256 = k / (2 : Int) ^ 32 := fun k => by omega
  simp only [Int.toBytes, Int.take, List.cons_append, List.nil_append, hd]

private theorem cmt_cell_i32_eq_int4 (a : BitVec 64) (v : BitVec 32) :
    cell (t := i32) a v = int4 a (v.setWidth 64) := by
  unfold cell int4
  simp only [Ty.bytes, Ty.size, toBits, BitVec.setWidth_eq]
  congr 2
  rw [← Int.toBytes_emod, ← Int.toBytes_emod (x := ((v.setWidth 64).toNat : Int))]
  congr 1; dsimp only [Int.take]
  simp only [Nat.reduceAdd, Nat.reduceDiv, Nat.reduceMul, BitVec.toInt_eq_msb_cond,
    BitVec.toNat_setWidth]
  have hlt : 0 ≤ (v.toNat : Int) ∧ (v.toNat : Int) < (2 ^ 32 : Int) :=
    ⟨Int.natCast_nonneg _, by exact_mod_cast v.isLt⟩
  have hlt64 : v.toNat < 2 ^ 64 := Nat.lt_trans v.isLt (by decide)
  rw [Nat.mod_eq_of_lt hlt64]
  cases v.msb
  · simp
  · simp only [↓reduceIte, Int.natCast_pow, Int.cast_ofNat_Int]; omega

private theorem cmt_cell64_eq_i32_pair (a w : BitVec 64) :
    cell64 a w =
      (cell (t := i32) a (w.setWidth 32) ⋆ cell (t := i32) (a + 4) ((w >>> 32).setWidth 32)) := by
  rw [cell64_eq_word8, word8_eq_int4_sep, cmt_cell_i32_eq_int4, cmt_cell_i32_eq_int4,
    int4_setWidth32, int4_setWidth32]
  have hdrop : (Int.toBytes 8 (w.toNat : Int)).drop 4 =
      Int.toBytes 4 ((w >>> 32).toNat : Int) := by
    have h1 : (((w >>> 32).setWidth 32).toNat : Int) =
        ((w >>> 32).toNat : Int) % (2 : Int) ^ (8 * 4) := by
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
    rw [cmt_toBytes_8_split, List.drop_left' (by simp [Int.toBytes_length]), h1, Int.toBytes_emod]
  unfold int4; rw [hdrop]

theorem cmt_array_i32_eq_array64_pack (a : BitVec 64) (xs : List (BitVec 32))
    (heven : xs.length % 2 = 0) :
    array (t := i32) a xs = array64 a (cmtPackPairs64 xs) := by
  match xs with
  | [] => rfl
  | [_] => simp at heven
  | lo :: hi :: rest =>
    have hrest : rest.length % 2 = 0 := by simp at heven; omega
    have hstep : a + BitVec.ofNat 64 (Ty.bytes i32) + BitVec.ofNat 64 (Ty.bytes i32) = a + 8 := by
      change a + 4#64 + 4#64 = a + 8#64; bv_omega
    have h4 : a + BitVec.ofNat 64 (Ty.bytes i32) = a + 4 := by
      change a + 4#64 = a + 4; rfl
    rw [array_cons, array_cons, cmtPackPairs64, array64_cons,
      cmt_cell64_eq_i32_pair, cmtPackPair64_lo, cmtPackPair64_hi, ← h4, hstep,
      cmt_array_i32_eq_array64_pack (a + 8) rest hrest, sep_assoc]

theorem cmt_array64_eq_array_i32_unpack (a : BitVec 64) (ys : List (BitVec 64)) :
    array64 a ys = array (t := i32) a (cmtUnpackPairs32 ys) := by
  induction ys generalizing a with
  | nil => rfl
  | cons w rest ih =>
    have hstep : a + BitVec.ofNat 64 (Ty.bytes i32) + BitVec.ofNat 64 (Ty.bytes i32) = a + 8 := by
      change a + 4#64 + 4#64 = a + 8#64; bv_omega
    have h4 : a + BitVec.ofNat 64 (Ty.bytes i32) = a + 4 := by
      change a + 4#64 = a + 4; rfl
    rw [array64_cons, cmt_cell64_eq_i32_pair, cmtUnpackPairs32, array_cons, array_cons,
      ← h4, hstep, ih (a + 8), sep_assoc]

private theorem cmt_array32_pair_eq (a : BitVec 64) (xs : List (BitVec 32)) {off : Nat}
    (h : off + 2 ≤ xs.length) :
    array (t := i32) a xs =
      (cell64 (a + BitVec.ofNat 64 (4 * off))
          (cmtPackPair64 (xs[off]'(by omega)) (xs[off + 1]'(by omega))) ⋆
        (array (t := i32) a (xs.take off) ⋆
          array (t := i32) (a + BitVec.ofNat 64 (4 * (off + 2))) (xs.drop (off + 2)))) := by
  have h1 := Proof.Spec.array_slice_focus (t := i32) a xs (off := off) (sz := 2) h
  have htake : (xs.drop off).take 2 = [xs[off]'(by omega), xs[off + 1]'(by omega)] := by
    rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_getElem_cons (by omega)]
    rfl
  rw [htake, show i32.bytes = 4 from rfl] at h1
  rw [h1]; congr 1
  rw [array_cons, array_cons, array_nil, sep_emp, cmt_cell64_eq_i32_pair,
    cmtPackPair64_lo, cmtPackPair64_hi]
  rfl

theorem cmt_load_tmp_u64 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {i : BitVec 64} (hi : i.toNat + 2 ≤ s.core.tmp.length) (hm : (FullMem c s ⋆ R) m) :
    loadVal m i64 (c.pTmp + i * 4) =
      some (cmtPackPair64 (s.core.tmp[i.toNat]'(by omega))
        (s.core.tmp[i.toNat + 1]'(by omega))) := by
  have haddr : c.pTmp + i * 4 = c.pTmp + BitVec.ofNat 64 (4 * i.toNat) := by
    rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
  rw [haddr]
  have hf := ArrayField.tmp.focus hm
  change (array (t := i32) c.pTmp s.core.tmp ⋆ _) m at hf
  rw [cmt_array32_pair_eq c.pTmp s.core.tmp hi, sep_assoc] at hf
  exact loadVal_cell64 hf

theorem cmt_store_arena_u64 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {i : BitVec 64} (v : BitVec 64) (hi : i.toNat + 2 ≤ s.core.arena.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i64 (c.pArena + i * 4) ∧
      (FullMem c { s with core := { s.core with
          arena := (s.core.arena.set i.toNat (v.setWidth 32)).set (i.toNat + 1)
            ((v >>> 32).setWidth 32) } } ⋆ R)
        (storeMem m i64 (c.pArena + i * 4) v) := by
  have haddr : c.pArena + i * 4 = c.pArena + BitVec.ofNat 64 (4 * i.toNat) := by
    rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
  rw [haddr]
  have hf := ArrayField.arena.focus hm
  change (array (t := i32) c.pArena s.core.arena ⋆ _) m at hf
  rw [cmt_array32_pair_eq c.pArena s.core.arena hi, sep_assoc] at hf
  obtain ⟨hok, hst⟩ := store_cell64 v hf
  refine ⟨hok, ?_⟩
  let ar' := (s.core.arena.set i.toNat (v.setWidth 32)).set (i.toNat + 1) ((v >>> 32).setWidth 32)
  have har'_l : ar'.length = s.core.arena.length := by simp [ar']
  have hhi' : i.toNat + 2 ≤ ar'.length := by omega
  have h0 : ar'[i.toNat]'(by omega) = v.setWidth 32 := by
    dsimp only [ar']
    rw [List.getElem_set_ne (by omega), List.getElem_set_self]
  have h1 : ar'[i.toNat + 1]'(by omega) = (v >>> 32).setWidth 32 := by
    dsimp only [ar']
    rw [List.getElem_set_self]
  have hpack : cmtPackPair64 (ar'[i.toNat]'(by omega)) (ar'[i.toNat + 1]'(by omega)) = v := by
    rw [h0, h1]; unfold cmtPackPair64; apply BitVec.eq_of_getElem_eq; intro k hk
    by_cases h32 : k < 32
    · simp [h32, hk]
    · simp [h32, hk, show k - 32 < 32 by omega, show 32 + (k - 32) = k by omega]
  have htk : ar'.take i.toNat = s.core.arena.take i.toNat := by
    dsimp only [ar']
    rw [List.take_set_of_le (by omega), List.take_set_of_le (by omega)]
  have hdr : ar'.drop (i.toNat + 2) = s.core.arena.drop (i.toNat + 2) := by
    dsimp only [ar']
    rw [List.drop_set_of_lt (by omega), List.drop_set_of_lt (by omega)]
  have hrew : array (t := i32) c.pArena ar' =
      (cell64 (c.pArena + BitVec.ofNat 64 (4 * i.toNat)) v ⋆
        (array (t := i32) c.pArena (s.core.arena.take i.toNat) ⋆
          array (t := i32) (c.pArena + BitVec.ofNat 64 (4 * (i.toNat + 2)))
            (s.core.arena.drop (i.toNat + 2)))) := by
    rw [cmt_array32_pair_eq c.pArena ar' hhi', hpack, htk, hdr]
  rw [← sep_assoc, ← hrew] at hst
  exact ArrayField.arena.unfocus hst

theorem cmt_fill_wsort_spec {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {Q : Post []} {X : XPost} (hslen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hPost : ∀ ws' m', ws'.length = 2 * c.max_vars →
      (FullMem c { s with scratch := { s.scratch with wsort := ws' } } ⋆ R) m' → Q () m') :
    Limits.Spec.m7FillU64Spec (c.pWsort, BitVec.ofNat 64 s.core.cur_vars, 0#64, ()) m Q X := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  have hcv := hslen.core_ok.cur_vars_le
  have hws_l := hslen.scratch_ok.wsort_len
  have hf := ArrayField.wsort.focus hm
  change (array (t := i32) c.pWsort s.scratch.wsort ⋆ _) m at hf
  rw [cmt_array_i32_eq_array64_pack c.pWsort s.scratch.wsort (by omega)] at hf
  refine ⟨cmtPackPairs64 s.scratch.wsort, _, ?_, ?_, hf, fun m' hm' => ?_⟩
  · rw [cmtPackPairs64_length, hws_l, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
  · rw [cmt_array64_eq_array_i32_unpack] at hm'
    have hlen' : (cmtUnpackPairs32 (List.replicate (BitVec.ofNat 64 s.core.cur_vars).toNat 0#64 ++
        (cmtPackPairs64 s.scratch.wsort).drop (BitVec.ofNat 64 s.core.cur_vars).toNat)).length =
        2 * c.max_vars := by
      rw [cmtUnpackPairs32_length, List.length_append, List.length_replicate, List.length_drop,
        cmtPackPairs64_length, hws_l, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    exact hPost _ m' hlen' (ArrayField.wsort.unfocus hm')

/-! ## 2. `CommitArenaExt`, `FullDenseInvW` Transitions & `Step7BvaCompactInv` -/

/-- Arena extension relation during Phase 2: prefix `< s0.core.arena_len` is untouched and every
original clause ref remains in `fullArenaClauseRefs`. -/
@[expose] def CommitArenaExt (s0 s : FullState) : Prop :=
  s0.core.arena_len ≤ s.core.arena_len ∧
  (∀ i < s0.core.arena_len, s.core.arena[i]? = s0.core.arena[i]?) ∧
  (∀ r ∈ fullArenaClauseRefs s0, r ∈ fullArenaClauseRefs s)

theorem CommitArenaExt.refl (s : FullState) : CommitArenaExt s s :=
  ⟨Nat.le_refl _, fun _ _ => rfl, fun _ h => h⟩

theorem CommitArenaExt.trans {s0 s1 s2 : FullState}
    (h1 : CommitArenaExt s0 s1) (h2 : CommitArenaExt s1 s2) : CommitArenaExt s0 s2 :=
  ⟨Nat.le_trans h1.1 h2.1, fun i hi => (h2.2.1 i (Nat.lt_of_lt_of_le hi h1.1)).trans (h1.2.1 i hi),
   fun r hr => h2.2.2 r (h1.2.2 r hr)⟩

theorem CommitArenaExt.of_eq {s0 s1 s2 : FullState} (h : CommitArenaExt s0 s1)
    (hal : s2.core.arena_len = s1.core.arena_len) (har : s2.core.arena = s1.core.arena) :
    CommitArenaExt s0 s2 := by
  refine ⟨hal ▸ h.1, fun i hi => by rw [har]; exact h.2.1 i hi, fun r hr => ?_⟩
  unfold fullArenaClauseRefs fullArenaClauseRefsCore; rw [har, hal]; exact h.2.2 r hr

theorem CommitArenaExt.old_garb {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 s : FullState} (hw0 : FullWitnessInv c F0 F_cur s0.core) (hext : CommitArenaExt s0 s)
    {r : Nat} (hr : r ∈ fullArenaClauseRefs s0) :
    fullArenaClauseGarb s r = fullArenaClauseGarb s0 r := by
  have := (hw0.arena.refs_wf r hr).1
  unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
  rw [hext.2.1 r (by omega)]

theorem CommitArenaExt.old_size {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 s : FullState} (hw0 : FullWitnessInv c F0 F_cur s0.core) (hext : CommitArenaExt s0 s)
    {r : Nat} (hr : r ∈ fullArenaClauseRefs s0) :
    fullArenaClauseSize s r = fullArenaClauseSize s0 r := by
  have := (hw0.arena.refs_wf r hr).1
  unfold fullArenaClauseSize fullArenaClauseSizeCore
  rw [hext.2.1 (r + 2) (by omega)]

theorem CommitArenaExt.old_lits {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 s : FullState} (hl0 : s0.LengthsOk c) (hl : s.LengthsOk c)
    (hw0 : FullWitnessInv c F0 F_cur s0.core) (hext : CommitArenaExt s0 s)
    {r : Nat} (hr : r ∈ fullArenaClauseRefs s0) :
    fullArenaClauseLits s r = fullArenaClauseLits s0 r := by
  have hwf := hw0.arena.refs_wf r hr
  have hbd0 : r + 3 + fullArenaClauseSizeCore s0.core r ≤ s0.core.arena.length := by
    have := hl0.core_ok.arena_len_le; have := hl0.core_ok.arena_len_arr; omega
  have hbd : r + 3 + fullArenaClauseSizeCore s0.core r ≤ s.core.arena.length := by
    have := hl.core_ok.arena_len_le; have := hl.core_ok.arena_len_arr
    have := hext.1; omega
  exact fullArenaClauseLitsCore_eq_of_hold hbd0 hbd (hext.old_size hw0 hr)
    fun j hj => hext.2.1 (r + 3 + j) (by omega)

theorem cmt_fullDenseInvW_set_flags {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {fl' : List (BitVec 32)}
    (hfl : fl'.length = c.max_vars) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with flags := fl' } } :=
  fullDenseInv_with_core_aux (tc' := s.core.tmp_cnt) (tl' := s.core.tmp_len) (sc' := s.scratch)
    h h.1.core_ok.repr_len h.1.core_ok.min_clr_len_arr h.1.core_ok.tmp_len_arr hfl
    h.1.core_ok.tmp_len_le h.1.scratch_ok rfl rfl

theorem cmt_fullDenseInvW_set_tmp {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {tmp' : List (BitVec 32)}
    (htmp : tmp'.length = c.max_vars) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with tmp := tmp' } } :=
  fullDenseInv_with_core_aux (tc' := s.core.tmp_cnt) (tl' := s.core.tmp_len) (sc' := s.scratch)
    h h.1.core_ok.repr_len h.1.core_ok.min_clr_len_arr htmp h.1.core_ok.flags_len
    h.1.core_ok.tmp_len_le h.1.scratch_ok rfl rfl

theorem cmt_fullDenseInvW_set_wsort {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {ws' : List (BitVec 32)}
    (hws : ws'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with wsort := ws' } } :=
  ⟨⟨h.1.core_ok, { h.1.scratch_ok with wsort_len := hws }⟩,
   h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem cmt_fullDenseInvW_set_sb {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {sb' : List (BitVec 32)}
    (hsb : sb'.length = c.scratch_cap) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with scratch_buf := sb' } } :=
  ⟨⟨h.1.core_ok, { h.1.scratch_ok with scratch_buf_len := hsb }⟩,
   h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem cmt_fullDenseInvW_set_garb {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) (ag' : BitVec 64) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with arena_garbage := ag' } } :=
  ⟨⟨{ h.1.core_ok with arena_len_le := h.1.core_ok.arena_len_le }, h.1.scratch_ok⟩,
   { h.2.1 with
     arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
     watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem cmt_fullDenseInvW_set_irred {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) (ni' : BitVec 64) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with num_irred := ni' } } :=
  ⟨⟨{ h.1.core_ok with arena_len_le := h.1.core_ok.arena_len_le }, h.1.scratch_ok⟩,
   { h.2.1 with
     arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }
     watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) },
   h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem cmt_fullDenseInvW_set_bva_cnt {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) (bc' : BitVec 64) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with bva_cnt := bc' } } :=
  ⟨⟨h.1.core_ok, { h.1.scratch_ok with wsort_len := h.1.scratch_ok.wsort_len }⟩,
   h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem cmt_fullDenseInvW_defrag {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {wvec' wstk' wsort' : List (BitVec 32)} {wlen' : Nat}
    (hlen' : ({ s with
      core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
      scratch := { s.scratch with wsort := wsort' } } : FullState).LengthsOk c)
    (hlay' : WatchStackLayout
      { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 })
    (hpres : ∀ l < 2 * s.core.cur_vars,
      fullWatchSizeCore
        { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 } l =
        fullWatchSize s l ∧
      ∀ k < fullWatchSize s l,
        wstk'[fullWatchOffCore
          { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 } l + k]? =
        s.core.wstk[fullWatchOff s l + k]?) :
    FullDenseInvW c F0 F_cur
      { s with
        core := { s.core with wvec := wvec', wstk := wstk', wlen := wlen', wusable := 0#64 }
        scratch := { s.scratch with wsort := wsort' } } := by
  have hwat := fullWstackDefrag_preserves_modeWatchesInv h.2.1.watches hlay' rfl rfl
    (fun _ hr => hr) hpres
  exact ⟨hlen',
    { h.2.1 with arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }, watches := hwat },
    h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem cmt_fullDenseInvW_unwatch {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {wvec' wstk' : List (BitVec 32)} {wu' : BitVec 64}
    (hlen' : ({ s with
      core := { s.core with wvec := wvec', wstk := wstk', wusable := wu' } } :
      FullState).LengthsOk c)
    (hwat : ModeWatchesInv F_cur
      { s.core with wvec := wvec', wstk := wstk', wusable := wu' }) :
    FullDenseInvW c F0 F_cur
      { s with core := { s.core with wvec := wvec', wstk := wstk', wusable := wu' } } :=
  ⟨hlen',
   { h.2.1 with arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }, watches := hwat },
   h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem cmt_fullDenseInvW_delBin {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {fl' wvec' wstk' : List (BitVec 32)} {wu' nb' : BitVec 64}
    (hlen' : ({ s with
      core :=
        { s.core with
          flags := fl', wvec := wvec', wstk := wstk', wusable := wu', num_binary := nb' } } :
      FullState).LengthsOk c)
    (hwat : ModeWatchesInv F_cur
      { s.core with
        flags := fl', wvec := wvec', wstk := wstk', wusable := wu', num_binary := nb' }) :
    FullDenseInvW c F0 F_cur
      { s with
        core :=
          { s.core with
            flags := fl', wvec := wvec', wstk := wstk', wusable := wu', num_binary := nb' } } :=
  ⟨hlen',
   { h.2.1 with arena := { h.2.1.arena with len_ok := h.2.1.arena.len_ok }, watches := hwat },
   h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem cmt_fullDenseInvW_addBin {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {vals' : List (BitVec 8)} {fl' lvl' rsns' trl' tp' wvec' wstk' : List (BitVec 32)}
    {te' wlen' : Nat} {unass' unfl' wu' nb' oom' inc' : BitVec 64}
    {ph' : List (BitVec 8)} {ws' : List (BitVec 32)}
    (hlen' : ({ s with
      core :=
        { s.core with
          vals := vals', flags := fl', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
          trail_end := te', unassigned := unass', unflushed := unfl', wvec := wvec', wstk := wstk',
          wlen := wlen', wusable := wu', num_binary := nb', oom := oom', inconsistent := inc' }
      scratch := { s.scratch with phases := ph', wsort := ws' } } : FullState).LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur
      { s.core with
        vals := vals', flags := fl', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
        trail_end := te', unassigned := unass', unflushed := unfl', wvec := wvec', wstk := wstk',
        wlen := wlen', wusable := wu', num_binary := nb', oom := oom', inconsistent := inc' }) :
    FullDenseInvW c F0 F_cur
      { s with
        core :=
          { s.core with
            vals := vals', flags := fl', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
            trail_end := te', unassigned := unass', unflushed := unfl', wvec := wvec',
            wstk := wstk', wlen := wlen', wusable := wu', num_binary := nb', oom := oom',
            inconsistent := inc' }
        scratch := { s.scratch with phases := ph', wsort := ws' } } :=
  ⟨hlen', hw', h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem cmt_fullDenseInvW_markGarb {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {cs : Nat}
    (hcs : cs ∈ fullArenaClauseRefs s) :
    let s' : FullState :=
      { s with core := { s.core with
          arena := s.core.arena.set cs (fullArenaHdr s cs ||| 0x00080000#32) } }
    FullDenseInvW c F0 F_cur s' ∧
    fullArenaClauseRefs s' = fullArenaClauseRefs s ∧
    (∀ r ∈ fullArenaClauseRefs s,
      fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
      fullArenaClauseLits s' r = fullArenaClauseLits s r) := by
  intro s'
  have hcl := h.1.core_ok
  have hmg := h.2.1.arena.markGarb hcl hcs s.core.arena_garbage
  have hrefs : fullArenaClauseRefs s' = fullArenaClauseRefs s := hmg.1
  have hlen' : s'.LengthsOk c :=
    ⟨{ hcl with arena_len_arr := by simp [s', hcl.arena_len_arr] }, h.1.scratch_ok⟩
  have hno_rsn : ∀ idx < s.core.trail_end,
      s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 :=
    fun idx hidx => h.2.1.level0_rsn_none idx hidx
      (by have := h.2.1.lvl_le idx hidx; have := h.2.2.2.2.2.1; omega)
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { h.2.1 with
      arena := hmg.2
      watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl
        (fun _ hr => by change _ ∈ fullArenaClauseRefs s'; rwa [hrefs])
      reason_inv := fun idx hidx hne => absurd (hno_rsn idx hidx) hne
      reason_lit_mem := fun idx hidx hne _ => absurd (hno_rsn idx hidx) hne }
  have hnd' : FullArenaVarsNodup s' :=
    FullArenaVarsNodup.of_markGarb h.toDense.1 h.2.2.2.1 hcs s.core.arena_garbage
  have hext' : FullExtScratchOk c s' :=
    h.2.2.2.2.1.of_pres ⟨rfl, rfl⟩ fun _ hr => hrefs ▸ hr
  have hsz_lits : ∀ r ∈ fullArenaClauseRefs s,
      fullArenaClauseSize s' r = fullArenaClauseSize s r ∧
      fullArenaClauseLits s' r = fullArenaClauseLits s r := fun r hr => by
    have hwf := h.2.1.arena.refs_wf r hr
    have hne2 : cs ≠ r + 2 := by
      rcases Nat.lt_or_ge r cs with hlt | hge
      · have := h.2.1.arena.disjoint hr hcs hlt; omega
      · rcases Nat.eq_or_lt_of_le hge with rfl | hgt
        · omega
        · have := h.2.1.arena.disjoint hcs hr hgt; omega
    have hsz : fullArenaClauseSize s' r = fullArenaClauseSize s r := by
      unfold fullArenaClauseSize fullArenaClauseSizeCore; dsimp only [s']
      rw [List.getElem?_set_ne hne2]
    refine ⟨hsz, ?_⟩
    have hbd : r + 3 + fullArenaClauseSizeCore s.core r ≤ s.core.arena.length := by
      have := hcl.arena_len_le; have := hcl.arena_len_arr; omega
    exact fullArenaClauseLitsCore_eq_of_hold hbd (by simpa [s'] using hbd) hsz fun j hj => by
      dsimp only [s']; apply List.getElem?_set_ne
      rcases Nat.lt_or_ge r cs with hlt | hge
      · have := h.2.1.arena.disjoint hr hcs hlt; omega
      · rcases Nat.eq_or_lt_of_le hge with rfl | hgt
        · omega
        · have := h.2.1.arena.disjoint hcs hr hgt; omega
  exact ⟨⟨hlen', hw', h.2.2.1, hnd', hext', h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩, hrefs, hsz_lits⟩

theorem Step7BvaCommittedOk.of_markGarb {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {bk cs : Nat}
    (hcs : cs ∈ fullArenaClauseRefs s) (hcom : Step7BvaCommittedOk c s bk) :
    Step7BvaCommittedOk c
      { s with core := { s.core with
          arena := s.core.arena.set cs (fullArenaHdr s cs ||| 0x00080000#32) } } bk := by
  obtain ⟨_, hrefs, hsz_lits⟩ := cmt_fullDenseInvW_markGarb h hcs
  obtain ⟨hbk, hrs, hrows⟩ := hcom
  refine ⟨hbk, hrs, fun q hq => ?_⟩
  obtain ⟨hfr, hro, hent⟩ := hrows q hq
  refine ⟨hfr, hro, fun qi hqi => ?_⟩
  have h1 := hent qi hqi
  unfold Step7RowRefOk at h1 ⊢
  split at h1
  · rename_i hb; rw [ite_eq_left hb]; exact h1
  · rename_i hnb; rw [ite_eq_right hnb]
    obtain ⟨hr, hbd, hlts⟩ := h1
    obtain ⟨hsz, hlits⟩ := hsz_lits _ hr
    exact ⟨hrefs ▸ hr, hsz ▸ hbd, hlits ▸ hlts⟩

theorem cmt_fullDenseInvW_addClause {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {len : Nat}
    {arena' : List (BitVec 32)} (hal_arr : arena'.length = c.arena_cap)
    (hal_le : s.core.arena_len + 3 + len ≤ c.arena_cap) (hge3 : 3 ≤ len)
    (hlen_le : len ≤ c.max_vars)
    (hhold : ∀ i < s.core.arena_len, arena'[i]? = s.core.arena[i]?)
    (hnoshrk : (arena'[s.core.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32)
    (_hnogarb : (arena'[s.core.arena_len]?.getD 0#32 &&& 0x00080000#32) = 0#32)
    (hsz : (arena'[s.core.arena_len + 2]?.getD 0#32).toNat = len)
    (hlits_eq : ∀ j < len, arena'[s.core.arena_len + 3 + j]? = s.core.tmp[j]?)
    (hlits_lt : ∀ l ∈ (s.core.tmp.take len).map BitVec.toNat, l < 2 * s.core.cur_vars)
    (hlits_nd : ((s.core.tmp.take len).map fun x => x.toNat / 2).Nodup)
    (hlits_ent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((s.core.tmp.take len).map BitVec.toNat))) :
    let s' : FullState :=
      { s with core := { s.core with arena := arena', arena_len := s.core.arena_len + 3 + len } }
    FullDenseInvW c F0 F_cur s' ∧ CommitArenaExt s s' ∧
    s.core.arena_len ∈ fullArenaClauseRefs s' := by
  intro s'
  have hcl := h.1.core_ok
  have hlen' : s'.LengthsOk c :=
    ⟨{ hcl with arena_len_arr := hal_arr, arena_len_le := hal_le }, h.1.scratch_ok⟩
  have hrefs : fullArenaClauseRefsCore s'.core =
      fullArenaClauseRefsCore s.core ++ [s.core.arena_len] :=
    fullArenaClauseRefsCore_append h.2.1.arena hge3 rfl hhold hnoshrk hsz
  have hsub : ∀ r ∈ fullArenaClauseRefsCore s.core, r ∈ fullArenaClauseRefsCore s'.core :=
    fun r hr => hrefs ▸ List.mem_append_left _ hr
  have hnew_mem : s.core.arena_len ∈ fullArenaClauseRefs s' := by
    change s.core.arena_len ∈ fullArenaClauseRefsCore s'.core
    rw [hrefs]; exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have hnew_lits : fullArenaClauseLitsCore s'.core s.core.arena_len =
      (s.core.tmp.take len).map BitVec.toNat := by
    apply List.ext_getElem
    · unfold fullArenaClauseLitsCore fullArenaClauseSizeCore; dsimp only [s']
      rw [hsz]; simp only [List.length_map, List.length_take, List.length_drop, hal_arr,
        hcl.tmp_len_arr]; omega
    · intro j hj1 hj2
      have hj_lt : j < len := by
        simp only [List.length_map, List.length_take, hcl.tmp_len_arr] at hj2; omega
      have h1 := fullArenaClauseLitsCore_getElem (k := s'.core) (r := s.core.arena_len)
        (j := j) (by unfold fullArenaClauseSizeCore; dsimp only [s']; omega)
        (by dsimp only [s']; rw [hal_arr]; omega)
      rw [List.getElem?_eq_getElem hj1] at h1
      have h2 := Option.some.inj h1
      rw [h2]
      have hj_tmp : j < s.core.tmp.length := by rw [hcl.tmp_len_arr]; omega
      have h3 := hlits_eq j hj_lt
      rw [List.getElem?_eq_getElem (by rw [hal_arr]; omega),
        List.getElem?_eq_getElem hj_tmp] at h3
      have h4 := Option.some.inj h3
      simp only [List.getElem_map, List.getElem_take]
      exact congrArg BitVec.toNat h4
  have hnxt_hold := h.2.1.arena.arenaNextOff_extend (alen' := s.core.arena_len + 3 + len)
    (by omega) hhold
  have hold_garb : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseGarbCore s'.core r = fullArenaClauseGarbCore s.core r := fun r hr => by
    have := (h.2.1.arena.refs_wf r hr).1
    unfold fullArenaClauseGarbCore fullArenaHdrCore s'; simp [hhold r (by omega)]
  have hold_sz : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseSizeCore s'.core r = fullArenaClauseSizeCore s.core r := fun r hr => by
    have := (h.2.1.arena.refs_wf r hr).1
    unfold fullArenaClauseSizeCore s'; simp [hhold (r + 2) (by omega)]
  have hold_lits : ∀ r ∈ fullArenaClauseRefsCore s.core,
      fullArenaClauseLitsCore s'.core r = fullArenaClauseLitsCore s.core r := fun r hr => by
    have hwf := h.2.1.arena.refs_wf r hr
    have h1l := hcl.arena_len_arr; have h1e := hcl.arena_len_le
    exact fullArenaClauseLitsCore_eq_of_hold (by omega) (by dsimp only [s']; omega)
      (hold_sz r hr) fun j hj => hhold (r + 3 + j) (by omega)
  have harena' : FullArenaClausesInv c F_cur s'.core := by
    refine ⟨Or.inr (by dsimp [s']; omega), ?_, ?_, ?_, ?_⟩
    · intro r hr; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · have hwf := h.2.1.arena.refs_wf r hr
        rw [hnxt_hold r hr, hold_sz r hr]
        refine ⟨by dsimp [s']; omega, hwf.2.1, hwf.2.2.1, by dsimp [s']; omega, ?_⟩
        rcases hwf.2.2.2.2 with he | h3 <;> right <;> dsimp [s'] <;> omega
      · have hnxt_new : fullArenaNextOff s'.core.arena s'.core.arena_len s.core.arena_len =
            s.core.arena_len + 3 + len := by unfold fullArenaNextOff s'; simp [hsz, hnoshrk]
        rw [hnxt_new, show fullArenaClauseSizeCore s'.core s.core.arena_len = len from hsz]
        refine ⟨by dsimp [s']; omega, hge3, by omega, by dsimp [s']; omega, Or.inl rfl⟩
    · intro r hr hsh; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · have hr3 := (h.2.1.arena.refs_wf r hr).1
        have hsh0 : (fullArenaHdrCore s.core r &&& 0x00800000#32) ≠ 0#32 := by
          unfold fullArenaHdrCore at hsh ⊢; dsimp only [s'] at hsh
          rwa [hhold r (by omega)] at hsh
        obtain ⟨t, ht1, ht2, hsent⟩ := h.2.1.arena.shrk_term r hr hsh0
        exact ⟨t, by rw [hold_sz r hr]; exact ht1, by dsimp only [s']; omega,
          by dsimp only [s']; rw [hhold t ht2]; exact hsent⟩
      · unfold fullArenaHdrCore at hsh; dsimp only [s'] at hsh; exact absurd hnoshrk hsh
    · intro r hr hng; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · rw [hold_garb r hr] at hng; rw [hold_lits r hr]; exact h.2.1.arena.lits_lt r hr hng
      · rw [hnew_lits]; exact hlits_lt
    · intro r hr hng; rw [hrefs, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · rw [hold_garb r hr] at hng; rw [hold_lits r hr]; exact h.2.1.arena.entails r hr hng
      · rw [hnew_lits]; exact hlits_ent
  have hno_rsn : ∀ idx < s.core.trail_end,
      s.core.rsns[(s.core.trl[idx]?.getD 0#32).toNat / 2]?.getD 0xFFFFFFFF#32 = 0xFFFFFFFF#32 :=
    fun idx hidx => h.2.1.level0_rsn_none idx hidx
      (by have := h.2.1.lvl_le idx hidx; have := h.2.2.2.2.2.1; omega)
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { h.2.1 with
      arena := harena'
      watches := h.2.1.watches.with_wstk rfl rfl rfl rfl rfl hsub
      reason_inv := fun idx hidx hne => absurd (hno_rsn idx hidx) hne
      reason_lit_mem := fun idx hidx hne _ => absurd (hno_rsn idx hidx) hne }
  have hnd' : FullArenaVarsNodup s' := fun r hr hng => by
    change r ∈ fullArenaClauseRefsCore s'.core at hr
    rw [hrefs, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · change fullArenaClauseGarbCore s'.core r = false at hng
      rw [hold_garb r hr] at hng
      unfold fullArenaClauseLits; rw [hold_lits r hr]; exact h.2.2.2.1 r hr hng
    · unfold fullArenaClauseLits; rw [hnew_lits, List.map_map]; exact hlits_nd
  have hext' : FullExtScratchOk c s' := h.2.2.2.2.1.of_pres ⟨rfl, rfl⟩ hsub
  exact ⟨⟨hlen', hw', h.2.2.1, hnd', hext', h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩,
    ⟨by dsimp [s']; omega, hhold, hsub⟩, hnew_mem⟩

/-- Generalized BVA extension witness built from `Step7BvaMatrixInv` upon fresh-variable
initialization (`full_init_fresh_var`). -/
theorem cmt_ext_fresh_var {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s' : FullState} {best_k bump : Nat}
    (hinv : FullDenseInvW c F0 F_cur s) (hcv_lt : s.core.cur_vars < c.max_vars)
    (hmat : Step7BvaMatrixInv c F_cur s (best_k + 1) bump)
    (hlen' : s'.LengthsOk c)
    {vals' mrk' : List (BitVec 8)} {flags' lvl' rsns' wvec' : List (BitVec 32)}
    {unass' : BitVec 64}
    (hcore' : s'.core = { s.core with
      cur_vars := s.core.cur_vars + 1, vals := vals', mrk := mrk', flags := flags',
      lvl := lvl', rsns := rsns', wvec := wvec', unassigned := unass' })
    (hv0 : vals'[2 * s.core.cur_vars]?.getD 1#8 = 0#8)
    (hv1 : vals'[2 * s.core.cur_vars + 1]?.getD 1#8 = 0#8)
    (hv_oth : ∀ l < 2 * c.max_vars, l / 2 ≠ s.core.cur_vars → vals'[l]? = s.core.vals[l]?)
    (hmrk_fv : mrk'[s.core.cur_vars]?.getD 1#8 = 0#8)
    (hmrk_oth : ∀ v < c.max_vars, v ≠ s.core.cur_vars → mrk'[v]? = s.core.mrk[v]?)
    (hlvl_oth : ∀ v < c.max_vars, v ≠ s.core.cur_vars → lvl'[v]? = s.core.lvl[v]?)
    (hrsns_oth : ∀ v < c.max_vars, v ≠ s.core.cur_vars → rsns'[v]? = s.core.rsns[v]?)
    (hwvec_0 : ∀ k < 4, wvec'[4 * s.core.cur_vars + k]?.getD 1#32 = 0#32)
    (hwvec_oth : ∀ i < 4 * c.max_vars, i / 4 ≠ s.core.cur_vars → wvec'[i]? = s.core.wvec[i]?)
    (hll' : s'.scratch.last_learned = s.scratch.last_learned)
    (hext' : s'.scratch.extend_len = s.scratch.extend_len) :
    let sc := fidStepsCap c.scratch_cap
    let sb := s.scratch.scratch_buf
    let brow_off := (sb[sc + best_k]?.getD 0#32).toNat
    let mn := (sb[2 * sc + best_k]?.getD 0#32).toNat
    ∃ F_next : List (List Nat),
      FullDenseInvW c F0 F_next s' ∧
      (∀ t ≤ best_k,
        (cnfOfClauses F_next).EntailsClause
          (cnfClause [2 * s.core.cur_vars, (sb[t]?.getD 0#32).toNat])) ∧
      (∀ m < mn, ∃ res : List Nat,
        (∀ x ∈ res, x < 2 * s.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
        FidBvaRowEntryOk F_cur s (sb[best_k]?.getD 0#32).toNat (sb[brow_off + m]?.getD 0#32) res ∧
        (cnfOfClauses F_next).EntailsClause (cnfClause ((2 * s.core.cur_vars + 1) :: res))) := by
  classical
  let sc := fidStepsCap c.scratch_cap
  let sb := s.scratch.scratch_buf
  let brow_off := (sb[sc + best_k]?.getD 0#32).toNat
  let mn := (sb[2 * sc + best_k]?.getD 0#32).toNat
  have hbk_row := hmat.1.2.2.2.2.2 best_k (by omega)
  let L : List Nat := (List.range (best_k + 1)).map fun t => (sb[t]?.getD 0#32).toNat
  let getRes : Nat → List Nat := fun m =>
    if hm : m < mn then Classical.choose (hbk_row.2.2.2.2.2 m hm) else []
  let Qs : List (List Nat) := (List.range mn).map getRes
  have hgetRes_spec : ∀ m (hm : m < mn),
      (∀ x ∈ getRes m, x < 2 * s.core.cur_vars) ∧ ((getRes m).map (· / 2)).Nodup ∧
      FidBvaRowEntryOk F_cur s (sb[best_k]?.getD 0#32).toNat
        (sb[brow_off + m]?.getD 0#32) (getRes m) ∧
      (∀ t ≤ best_k,
        (cnfOfClauses F_cur).EntailsClause (cnfClause ((sb[t]?.getD 0#32).toNat :: getRes m))) :=
    fun m hm => by
      have hs := Classical.choose_spec (hbk_row.2.2.2.2.2 m hm)
      have heq : getRes m = Classical.choose (hbk_row.2.2.2.2.2 m hm) := dite_eq_left hm
      rw [heq]; exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1⟩
  have hL : ∀ f ∈ L, f < 2 * s.core.cur_vars := fun f hf => by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hf
    rw [List.mem_range] at ht
    exact (hmat.1.2.2.2.2.2 t ht).1
  have hQs : ∀ R ∈ Qs, ∀ q ∈ R, q < 2 * s.core.cur_vars := fun R hR q hq => by
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hR
    rw [List.mem_range] at hm
    exact (hgetRes_spec m hm).1 q hq
  have hprod : ∀ f ∈ L, ∀ R ∈ Qs, (cnfOfClauses F_cur).EntailsClause (cnfClause (f :: R)) :=
    fun f hf R hR => by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hf
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hR
      rw [List.mem_range] at ht hm
      exact (hgetRes_spec m hm).2.2.2 t (by omega)
  have ⟨hw', hd'⟩ := fullDenseInv_add_fresh_var_gen (L := L) (Qs := Qs)
    hinv.1 hinv.2.1 hinv.2.2.1 hinv.2.2.2.1 hinv.2.2.2.2.1 hinv.2.2.2.2.2.1 hinv.2.2.2.2.2.2
    hcv_lt hL hQs hprod hlen' hcore' hv0 hv1 hv_oth hmrk_fv hmrk_oth hlvl_oth hrsns_oth
    hwvec_0 hwvec_oth hll' hext'
  refine ⟨bvaExtendGen s.core.cur_vars L Qs F_cur,
    ⟨hlen', hw', hd'.2.1, hd'.2.2.1, hd'.2.2.2.1, hd'.2.2.2.2.1, hd'.2.2.2.2.2⟩,
    fun t ht => bvaExtendGen_entails_pos
      (List.mem_map.mpr ⟨t, List.mem_range.mpr (by omega), rfl⟩),
    fun m hm => ?_⟩
  have hs := hgetRes_spec m hm
  exact ⟨getRes m, hs.1, hs.2.1, hs.2.2.1,
    bvaExtendGen_entails_neg (List.mem_map.mpr ⟨m, List.mem_range.mpr hm, rfl⟩)⟩

/-- Phase 3 reverse-compaction invariant over `sb` relative to the initial matrix `s0`. -/
@[expose] def Step7BvaCompactInv (c : FullCfg) (s0 s : FullState) (best_k mn fs_i : Nat)
    (sb : List (BitVec 32)) : Prop :=
  let sc := fidStepsCap c.scratch_cap
  let sb0 := s0.scratch.scratch_buf
  sb.length = c.scratch_cap ∧
  (∀ r ≤ best_k, sb[r]? = sb0[r]?) ∧
  (∀ r ≤ best_k, sb[sc + r]? = sb0[sc + r]?) ∧
  (∀ r ≤ best_k, sb[3 * sc + r]? = sb0[3 * sc + r]?) ∧
  (∀ r ≤ best_k,
    sb[2 * sc + r]? = if fs_i ≤ r then some (BitVec.ofNat 32 mn) else sb0[2 * sc + r]?) ∧
  (∀ r ≤ best_k,
    let ro := (sb0[sc + r]?.getD 0#32).toNat
    let qn := (sb0[2 * sc + r]?.getD 0#32).toNat
    let po := (sb0[3 * sc + r]?.getD 0#32).toNat
    (∀ m < qn, Step7RowRefOk s (sb[ro + m]?.getD 0#32)) ∧
    (0 < r → ∀ m < qn,
      (sb[po + m]?.getD 0#32).toNat < (sb0[2 * sc + (r - 1)]?.getD 0#32).toNat))

theorem step7BvaCompactInv_init {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 s : FullState} {best_k bump : Nat}
    (hl0 : s0.LengthsOk c) (hl : s.LengthsOk c)
    (hw0 : FullWitnessInv c F0 F_cur s0.core) (hext : CommitArenaExt s0 s)
    (hcv : s0.core.cur_vars ≤ s.core.cur_vars)
    (hbk_sc : best_k < fidStepsCap c.scratch_cap)
    (hmat : Step7BvaMatrixInv c F_cur s0 (best_k + 1) bump) :
    let sc := fidStepsCap c.scratch_cap
    let mn := (s0.scratch.scratch_buf[2 * sc + best_k]?.getD 0#32).toNat
    Step7BvaCompactInv c s0 s best_k mn best_k s0.scratch.scratch_buf := by
  intro sc mn
  have hsb0_l := hl0.scratch_ok.scratch_buf_len
  have h4sc := fidStepsCap_mul4_le c.scratch_cap
  refine ⟨hsb0_l, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun r hr => ?_, fun r hr => ?_⟩
  · by_cases hge : best_k ≤ r
    · have hreq : r = best_k := by omega
      subst hreq; rw [ite_eq_left hge]
      have hlt : 2 * sc + r < s0.scratch.scratch_buf.length := by rw [hsb0_l]; omega
      rw [List.getElem?_eq_getElem hlt]; congr 1
      apply BitVec.eq_of_toNat_eq
      dsimp only [mn]
      rw [List.getElem?_eq_getElem hlt, Option.getD_some, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (BitVec.isLt _)]
    · rw [ite_eq_right hge]
  · have hrow := hmat.1.2.2.2.2.2 r (by omega)
    refine ⟨fun m hm => ?_, fun hr0 m hm => ?_⟩
    · obtain ⟨res, hres_lt, _, hok, _, _⟩ := hrow.2.2.2.2.2 m hm
      unfold Step7RowRefOk; unfold FidBvaRowEntryOk at hok
      split at hok
      · rename_i hb; rw [ite_eq_left hb]; omega
      · rename_i hnb; rw [ite_eq_right hnb]
        have hwf := hw0.arena.refs_wf _ hok.1
        refine ⟨hext.2.2 _ hok.1, ?_, ?_⟩
        · rw [hext.old_size hw0 hok.1]; unfold fullArenaClauseSize
          have := hwf.2.2.1; have := hwf.2.2.2.1; have := hext.1; omega
        · rw [hext.old_lits hl0 hl hw0 hok.1]
          intro l hl_m
          have := hw0.arena.lits_lt _ hok.1 hok.2.1 l hl_m; omega
    · obtain ⟨_, _, _, _, _, hpar⟩ := hrow.2.2.2.2.2 m hm
      exact (hpar hr0).1

theorem step7BvaCompactInv_set_par {c : FullCfg} {F_cur : List (List Nat)}
    {s0 s : FullState} {best_k bump mn fs_i r_prev fi fj : Nat} {sb : List (BitVec 32)}
    (hmat : Step7BvaMatrixInv c F_cur s0 (best_k + 1) bump)
    (hinv : Step7BvaCompactInv c s0 s best_k mn fs_i sb)
    (hr0 : 0 < r_prev) (hr_le : r_prev ≤ best_k)
    (hfi : fi < (s0.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap + r_prev]?.getD 0#32).toNat)
    (hfj : fj < (s0.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap + r_prev]?.getD 0#32).toNat) :
    let sc := fidStepsCap c.scratch_cap
    let po_p := (s0.scratch.scratch_buf[3 * sc + r_prev]?.getD 0#32).toNat
    Step7BvaCompactInv c s0 s best_k mn fs_i
      (sb.set (po_p + fi) (sb[po_p + fj]?.getD 0#32)) := by
  intro sc po_p
  obtain ⟨hsb_l, hf, hro, hpo, hqn, hrows⟩ := hinv
  have hlay := hmat.2; dsimp only [Step7BvaLayout] at hlay
  have hrp_info := hmat.1.2.2.2.2.2 r_prev (by omega)
  have hpo_ge : 4 * sc ≤ po_p := (hrp_info.2.2.2.2.1 hr0).1
  have hpo_hi : po_p + fi < c.scratch_cap := by
    have h1 := (hrp_info.2.2.2.2.1 hr0).2; have h2 := hmat.1.2.2.2.2.1
    dsimp only [po_p, sc] at *; omega
  have hbk_sc : best_k < sc := by have := hmat.1.2.2.1; dsimp only [sc]; omega
  refine ⟨by simp [hsb_l], fun r hr => ?_, fun r hr => ?_, fun r hr => ?_,
    fun r hr => ?_, fun r hr => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact hf r hr
  · rw [List.getElem?_set_ne (by omega)]; exact hro r hr
  · rw [List.getElem?_set_ne (by omega)]; exact hpo r hr
  · rw [List.getElem?_set_ne (by omega)]; exact hqn r hr
  · refine ⟨fun m hm => ?_, fun hr_pos m hm => ?_⟩
    · have hne : po_p + fi ≠ (s0.scratch.scratch_buf[sc + r]?.getD 0#32).toNat + m := by
        rcases Nat.lt_trichotomy r r_prev with hlt | rfl | hgt
        · have h1 := (hlay.2 r r_prev hlt (by omega)).2.1
          have h2 := hlay.1 r_prev (by omega) hr0; dsimp only [po_p, sc] at *; omega
        · have h2 := hlay.1 r (by omega) hr0; dsimp only [po_p, sc] at *; omega
        · have h1 := (hlay.2 r_prev r hgt (by omega)).2.2 hr0; dsimp only [po_p, sc] at *; omega
      rw [List.getElem?_set_ne hne]; exact (hrows r hr).1 m hm
    · by_cases hreq : r = r_prev
      · subst hreq
        by_cases hmfi : m = fi
        · subst hmfi; rw [List.getElem?_set_self (by rw [hsb_l]; omega), Option.getD_some]
          exact (hrows r hr).2 hr0 fj hfj
        · have hne : po_p + fi ≠ (s0.scratch.scratch_buf[3 * sc + r]?.getD 0#32).toNat + m := by
            dsimp only [po_p, sc]; omega
          rw [List.getElem?_set_ne hne]; exact (hrows r hr).2 hr0 m hm
      · have hne : po_p + fi ≠ (s0.scratch.scratch_buf[3 * sc + r]?.getD 0#32).toNat + m := by
          rcases Nat.lt_or_gt_of_ne hreq with hlt | hgt
          · have h1 := (hlay.2 r r_prev hlt (by omega)).2.2 hr_pos
            have h2 := hlay.1 r_prev (by omega) hr0; dsimp only [po_p, sc] at *; omega
          · have h1 := (hlay.2 r_prev r hgt (by omega)).2.2 hr0
            have h2 := hlay.1 r (by omega) hr_pos; dsimp only [po_p, sc] at *; omega
        rw [List.getElem?_set_ne hne]; exact (hrows r hr).2 hr_pos m hm

theorem step7BvaCompactInv_set_row {c : FullCfg} {F_cur : List (List Nat)}
    {s0 s : FullState} {best_k bump mn fs_i r_prev fi fj : Nat} {sb : List (BitVec 32)}
    (hmat : Step7BvaMatrixInv c F_cur s0 (best_k + 1) bump)
    (hinv : Step7BvaCompactInv c s0 s best_k mn fs_i sb)
    (hr_le : r_prev ≤ best_k)
    (hfi : fi < (s0.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap + r_prev]?.getD 0#32).toNat)
    (hfj : fj < (s0.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap + r_prev]?.getD 0#32).toNat) :
    let sc := fidStepsCap c.scratch_cap
    let ro_p := (s0.scratch.scratch_buf[sc + r_prev]?.getD 0#32).toNat
    Step7BvaCompactInv c s0 s best_k mn fs_i
      (sb.set (ro_p + fi) (sb[ro_p + fj]?.getD 0#32)) := by
  intro sc ro_p
  obtain ⟨hsb_l, hf, hro, hpo, hqn, hrows⟩ := hinv
  have hlay := hmat.2; dsimp only [Step7BvaLayout] at hlay
  have hrp_info := hmat.1.2.2.2.2.2 r_prev (by omega)
  have hro_ge : 4 * sc ≤ ro_p := hrp_info.2.1
  have hro_hi : ro_p + fi < c.scratch_cap := by
    have h1 := hrp_info.2.2.2.1; have h2 := hmat.1.2.2.2.2.1
    dsimp only [ro_p, sc] at *; omega
  have hbk_sc : best_k < sc := by have := hmat.1.2.2.1; dsimp only [sc]; omega
  refine ⟨by simp [hsb_l], fun r hr => ?_, fun r hr => ?_, fun r hr => ?_,
    fun r hr => ?_, fun r hr => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact hf r hr
  · rw [List.getElem?_set_ne (by omega)]; exact hro r hr
  · rw [List.getElem?_set_ne (by omega)]; exact hpo r hr
  · rw [List.getElem?_set_ne (by omega)]; exact hqn r hr
  · refine ⟨fun m hm => ?_, fun hr_pos m hm => ?_⟩
    · by_cases hreq : r = r_prev
      · subst hreq
        by_cases hmfi : m = fi
        · subst hmfi; rw [List.getElem?_set_self (by rw [hsb_l]; omega), Option.getD_some]
          exact (hrows r hr).1 fj hfj
        · have hne : ro_p + fi ≠ (s0.scratch.scratch_buf[sc + r]?.getD 0#32).toNat + m := by
            dsimp only [ro_p, sc]; omega
          rw [List.getElem?_set_ne hne]; exact (hrows r hr).1 m hm
      · have hne : ro_p + fi ≠ (s0.scratch.scratch_buf[sc + r]?.getD 0#32).toNat + m := by
          rcases Nat.lt_or_gt_of_ne hreq with hlt | hgt
          · have h1 := (hlay.2 r r_prev hlt (by omega)).2.1; dsimp only [ro_p, sc] at *; omega
          · have h1 := (hlay.2 r_prev r hgt (by omega)).2.1; dsimp only [ro_p, sc] at *; omega
        rw [List.getElem?_set_ne hne]; exact (hrows r hr).1 m hm
    · have hne : ro_p + fi ≠ (s0.scratch.scratch_buf[3 * sc + r]?.getD 0#32).toNat + m := by
        rcases Nat.lt_trichotomy r r_prev with hlt | rfl | hgt
        · have h1 := (hlay.2 r r_prev hlt (by omega)).2.2 hr_pos; dsimp only [ro_p, sc] at *; omega
        · have h2 := hlay.1 r (by omega) hr_pos; dsimp only [ro_p, sc] at *; omega
        · have h1 := (hlay.2 r_prev r hgt (by omega)).2.1
          have h2 := hlay.1 r (by omega) hr_pos; dsimp only [ro_p, sc] at *; omega
      rw [List.getElem?_set_ne hne]; exact (hrows r hr).2 hr_pos m hm

theorem step7BvaCompactInv_set_len {c : FullCfg} {F_cur : List (List Nat)}
    {s0 s : FullState} {best_k bump mn fs_i : Nat} {sb : List (BitVec 32)}
    (hmat : Step7BvaMatrixInv c F_cur s0 (best_k + 1) bump)
    (hinv : Step7BvaCompactInv c s0 s best_k mn fs_i sb)
    (hpos : 0 < fs_i) (hle : fs_i ≤ best_k) :
    let sc := fidStepsCap c.scratch_cap
    Step7BvaCompactInv c s0 s best_k mn (fs_i - 1)
      (sb.set (2 * sc + (fs_i - 1)) (BitVec.ofNat 32 mn)) := by
  intro sc
  obtain ⟨hsb_l, hf, hro, hpo, hqn, hrows⟩ := hinv
  have hbk_sc : best_k < sc := by have := hmat.1.2.2.1; omega
  have h4sc := fidStepsCap_mul4_le c.scratch_cap
  refine ⟨by simp [hsb_l], fun r hr => ?_, fun r hr => ?_, fun r hr => ?_,
    fun r hr => ?_, fun r hr => ?_⟩
  · rw [List.getElem?_set_ne (by omega)]; exact hf r hr
  · rw [List.getElem?_set_ne (by omega)]; exact hro r hr
  · rw [List.getElem?_set_ne (by omega)]; exact hpo r hr
  · by_cases heq : r = fs_i - 1
    · subst heq; rw [ite_eq_left (Nat.le_refl _), List.getElem?_set_self (by rw [hsb_l]; omega)]
    · rw [List.getElem?_set_ne (by omega), hqn r hr]
      have hiff : (fs_i - 1 ≤ r) ↔ (fs_i ≤ r) := by omega
      by_cases h1 : fs_i ≤ r
      · rw [ite_eq_left h1, ite_eq_left (hiff.mpr h1)]
      · rw [ite_eq_right h1, ite_eq_right (fun h => h1 (hiff.mp h))]
  · have hri := hmat.1.2.2.2.2.2 r (by omega)
    refine ⟨fun m hm => ?_, fun hr0 m hm => ?_⟩
    · have := hri.2.1; rw [List.getElem?_set_ne (by omega)]; exact (hrows r hr).1 m hm
    · have := (hri.2.2.2.2.1 hr0).1; rw [List.getElem?_set_ne (by omega)]
      exact (hrows r hr).2 hr0 m hm

theorem step7BvaCompactInv_done {c : FullCfg} {F_cur : List (List Nat)}
    {s0 s : FullState} {best_k bump mn : Nat} {sb : List (BitVec 32)}
    (hmat : Step7BvaMatrixInv c F_cur s0 (best_k + 1) bump)
    (hinv : Step7BvaCompactInv c s0 s best_k mn 0 sb)
    (hcv : s0.core.cur_vars ≤ s.core.cur_vars)
    (hmn_eq : mn = (s0.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap +
      best_k]?.getD 0#32).toNat)
    (hres : s.scratch.res_sz = BitVec.ofNat 64 best_k) :
    Step7BvaCommittedOk c { s with scratch := { s.scratch with scratch_buf := sb } } best_k := by
  let sc := fidStepsCap c.scratch_cap
  obtain ⟨hsb_l, hf, hro, hpo, hqn, hrows⟩ := hinv
  have hbk_sc : best_k < sc := by have := hmat.1.2.2.1; omega
  have hmn_lt : mn < 2 ^ 32 := by rw [hmn_eq]; exact BitVec.isLt _
  refine ⟨hbk_sc, hres, fun q hq => ?_⟩
  dsimp only
  have hri := hmat.1.2.2.2.2.2 q (by omega)
  have hq_fr : (sb[q]?.getD 0#32).toNat < 2 * s.core.cur_vars := by
    rw [hf q hq]; have := hri.1; omega
  have hq_ro : (sb[sc + q]?.getD 0#32).toNat =
      (s0.scratch.scratch_buf[sc + q]?.getD 0#32).toNat := by rw [hro q hq]
  have hq_qn : (sb[2 * sc + q]?.getD 0#32).toNat = mn := by
    rw [hqn q hq, ite_eq_left (Nat.zero_le _), Option.getD_some, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hmn_lt]
  have hmn_le : mn ≤
      (s0.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap + q]?.getD 0#32).toNat := by
    by_cases hqb : q = best_k
    · subst hqb; rw [hmn_eq]; exact Nat.le_refl _
    · rw [hmn_eq]; exact (hmat.2.2 q best_k (by omega) (by omega)).1
  exact ⟨hq_fr, by
    rw [hq_ro, hq_qn]; have h1 := hri.2.2.2.1; have h2 := hmat.1.2.2.2.2.1
    dsimp only [sc] at *; omega,
    fun qi hqi => by
      rw [hq_ro]; rw [hq_qn] at hqi
      exact ((hrows q hq).1 qi (by dsimp only [sc] at *; omega)).congr rfl rfl rfl⟩

/-! ## 3. Pure AST Extractors for `full_bva_commit_body` -/

@[expose] def cmtDummyVal : (t : Ty) → Val t
  | .bits _ => 0 | .bool => false | .float _ => 0
  | .pair a b => (cmtDummyVal a, cmtDummyVal b)

@[expose] def cmtDummyTup : (ts : List Ty) → Tup Val ts
  | [] => () | t :: ts => (cmtDummyVal t, cmtDummyTup ts)

@[expose] def cmtStepE {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .let_ (Op.mk (.add (.bits 32)) args) k => k (args.1.val + args.2.1.val, ())
  | .let_ (Op.mk (.trunc 64 32) args) k => k (args.1.val.setWidth 32, ())
  | .let_ (Op.mk (.shl (.bits 32)) args) k => k (args.1.val <<< args.2.1.val, ())
  | .let_ (ts := ts) _ k => k (cmtDummyTup ts)
  | _ => .hlt

@[expose] def cmtStepsE {rs : List Ty} : Nat → Expr Val Cont rs → Expr Val Cont rs
  | 0, e => e | n + 1, e => cmtStepsE n (cmtStepE e)

@[expose] def cmtLd64 {rs : List Ty} (v : Val i64) : Expr Val Cont rs → Expr Val Cont rs
  | .load (.bits 64) _ k => k v | _ => .hlt

@[expose] def cmtLd32 {rs : List Ty} (v : Val i32) : Expr Val Cont rs → Expr Val Cont rs
  | .load (.bits 32) _ k => k v | _ => .hlt

@[expose] def cmtSt64 {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .store _ _ k => k | _ => .hlt

@[expose] def cmtSt32 {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .store _ _ k => k | _ => .hlt

@[expose] def cmtCall32 {rs : List Ty} (v : Val i32) : Expr Val Cont rs → Expr Val Cont rs
  | .call (bs := [.bits 32]) _ _ k => k (v, ()) | _ => .hlt

@[expose] def cmtCall0 {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .call (bs := []) _ _ k => k () | _ => .hlt

@[expose] def cmtThen {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .jnz _ t _ => t | _ => .hlt

@[expose] def cmtElse {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .jnz _ _ e => e | _ => .hlt

@[expose] def cmtGrpB1b {rs : List Ty} (v : Bool) (J : Cont [.bool]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bool]]) bs _ => match bs (J, ()) with | .cons f .nil => f (v, ())
  | _ => .hlt

@[expose] def cmtGrpK1b {rs : List Ty} (J : Cont [.bool]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bool]]) _ k => k (J, ()) | _ => .hlt

@[expose] def cmtGrpB2 {rs : List Ty} (v : Tup Val [i64, i32]) (J : Cont [i64, i32]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 64, .bits 32]]) bs _ => match bs (J, ()) with | .cons f .nil => f v
  | _ => .hlt

@[expose] def cmtGrpB3_64 {rs : List Ty} (v : Tup Val [i64, i64, i32])
    (J : Cont [i64, i64, i32]) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 64, .bits 64, .bits 32]]) bs _ =>
    match bs (J, ()) with | .cons f .nil => f v
  | _ => .hlt

@[expose] def cmtGrpK3 {rs : List Ty} (J : Cont [i32, .bool, .bool]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bool, .bool]]) _ k => k (J, ()) | _ => .hlt

@[expose] def cmtGrpB3 {rs : List Ty} (v : Tup Val [i32, .bool, .bool])
    (J : Cont [i32, .bool, .bool]) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bool, .bool]]) bs _ =>
    match bs (J, ()) with | .cons f .nil => f v
  | _ => .hlt

@[expose] def cmtGrpK5 {rs : List Ty} (J : Cont [i32, .bool, .bool, i64, i64]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bool, .bool, .bits 64, .bits 64]]) _ k => k (J, ()) | _ => .hlt

@[expose] def cmtGrpB5 {rs : List Ty} (v : Tup Val [i32, .bool, .bool, i64, i64])
    (J : Cont [i32, .bool, .bool, i64, i64]) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bool, .bool, .bits 64, .bits 64]]) bs _ =>
    match bs (J, ()) with | .cons f .nil => f v
  | _ => .hlt

/- Concrete `rfl` rewrite rules for `cmtStepE` (avoiding `Tup` `DiscrTree` mismatch). -/

theorem cmt_stepE_add32 {rs : List Ty} {args : Tup (Arg Val) [i32, i32]}
    {k : Tup Val [i32] → Expr Val Cont rs} :
    cmtStepE (.let_ (Op.mk (.add i32) args) k) = k (args.1.val + args.2.1.val, ()) := by
  rcases args with ⟨a, b, ⟨⟩⟩; rfl

theorem cmt_stepE_trunc {rs : List Ty} {args : Tup (Arg Val) [i64]}
    {k : Tup Val [i32] → Expr Val Cont rs} :
    cmtStepE (.let_ (Op.mk (.trunc 64 32) args) k) = k (args.1.val.setWidth 32, ()) := by
  rcases args with ⟨a, ⟨⟩⟩; rfl

theorem cmt_stepE_shl32 {rs : List Ty} {args : Tup (Arg Val) [i32, i32]}
    {k : Tup Val [i32] → Expr Val Cont rs} :
    cmtStepE (.let_ (Op.mk (.shl i32) args) k) = k (args.1.val <<< args.2.1.val, ()) := by
  rcases args with ⟨a, b, ⟨⟩⟩; rfl

theorem cmt_stepE_add64 {rs : List Ty} {args : Tup (Arg Val) [i64, i64]}
    {k : Tup Val [i64] → Expr Val Cont rs} :
    cmtStepE (.let_ (Op.mk (.add i64) args) k) = k (cmtDummyTup [i64]) := rfl

theorem cmt_stepE_sub64 {rs : List Ty} {args : Tup (Arg Val) [i64, i64]}
    {k : Tup Val [i64] → Expr Val Cont rs} :
    cmtStepE (.let_ (Op.mk (.sub i64) args) k) = k (cmtDummyTup [i64]) := rfl

theorem cmt_stepE_mul64 {rs : List Ty} {args : Tup (Arg Val) [i64, i64]}
    {k : Tup Val [i64] → Expr Val Cont rs} :
    cmtStepE (.let_ (Op.mk (.mul i64) args) k) = k (cmtDummyTup [i64]) := rfl

theorem cmt_stepE_mul32 {rs : List Ty} {args : Tup (Arg Val) [i32, i32]}
    {k : Tup Val [i32] → Expr Val Cont rs} :
    cmtStepE (.let_ (Op.mk (.mul i32) args) k) = k (cmtDummyTup [i32]) := rfl

theorem cmt_stepE_shl64 {rs : List Ty} {args : Tup (Arg Val) [i64, i64]}
    {k : Tup Val [i64] → Expr Val Cont rs} :
    cmtStepE (.let_ (Op.mk (.shl i64) args) k) = k (cmtDummyTup [i64]) := rfl

theorem cmt_stepE_or32 {rs : List Ty} {args : Tup (Arg Val) [i32, i32]}
    {k : Tup Val [i32] → Expr Val Cont rs} :
    cmtStepE (.let_ (Op.mk (.or i32) args) k) = k (cmtDummyTup [i32]) := rfl

theorem cmt_stepE_zext32 {rs : List Ty} {args : Tup (Arg Val) [i32]}
    {k : Tup Val [i64] → Expr Val Cont rs} :
    cmtStepE (.let_ (Op.mk (.zext 32 64) args) k) = k (cmtDummyTup [i64]) := rfl

theorem cmt_stepE_sext32 {rs : List Ty} {args : Tup (Arg Val) [i32]}
    {k : Tup Val [i64] → Expr Val Cont rs} :
    cmtStepE (.let_ (Op.mk (.sext 32 64) args) k) = k (cmtDummyTup [i64]) := rfl

theorem cmt_stepE_cmp64 {rs : List Ty} {o : CmpOp} {args : Tup (Arg Val) [i64, i64]}
    {k : Tup Val [.bool] → Expr Val Cont rs} :
    cmtStepE (.let_ (Op.mk (.cmp o i64) args) k) = k (cmtDummyTup [.bool]) := rfl

theorem cmt_stepE_cmp32 {rs : List Ty} {o : CmpOp} {args : Tup (Arg Val) [i32, i32]}
    {k : Tup Val [.bool] → Expr Val Cont rs} :
    cmtStepE (.let_ (Op.mk (.cmp o i32) args) k) = k (cmtDummyTup [.bool]) := rfl

@[expose] def cmtDefragGrpExpr (h64 : Val i64) (best_k sc : Val i32)
    (pAr pScr pCnt pFl pWv : Val i64) (brow_off mn : Val i32) : Expr Val Cont [.bool] :=
  full_bva_commit_body Val Cont (h64, best_k, ())
    |> cmtStepE |> cmtLd64 0#64 |> cmtStepE |> cmtElse
    |> cmtStepE |> cmtLd64 0#64 |> cmtCall32 sc |> cmtStepE |> cmtElse
    |> cmtStepE |> cmtElse
    |> cmtStepE |> cmtLd64 pAr |> cmtStepE |> cmtLd64 pScr
    |> cmtStepE |> cmtLd64 pCnt |> cmtStepE |> cmtLd64 pFl |> cmtStepE |> cmtLd64 pWv
    |> cmtStepsE 5 |> cmtLd32 brow_off |> cmtStepsE 5 |> cmtLd32 mn
    |> cmtStepsE 6
    |> cmtGrpB2 (0#64, 0#32, ()) (fun _ _ => False) |> cmtStepE |> cmtElse
    |> cmtGrpB3_64 (0#64, 0#64, 0#32, ()) (fun _ _ => False) |> cmtStepE |> cmtElse
    |> cmtStepE |> cmtLd64 0#64 |> cmtStepE |> cmtLd64 0#64 |> cmtStepE |> cmtElse
    |> cmtStepE |> cmtLd64 0#64 |> cmtStepE |> cmtLd64 0#64 |> cmtStepE |> cmtElse
    |> cmtStepE |> cmtLd64 0#64 |> cmtStepE |> cmtLd64 0#64 |> cmtStepsE 2 |> cmtElse

@[expose] def cmtP1GrpExpr (h64 : Val i64) (best_k sc : Val i32)
    (pAr pScr pCnt pFl pWv : Val i64) (brow_off mn : Val i32)
    (dd : Bool) (cv64 pDeg pTmp : Val i64) : Expr Val Cont [.bool] :=
  cmtDefragGrpExpr h64 best_k sc pAr pScr pCnt pFl pWv brow_off mn
    |> cmtGrpB1b dd (fun _ _ => False)
    |> cmtStepE |> cmtLd64 cv64 |> cmtStepE
    |> cmtStepE |> cmtLd64 0#64 |> cmtStepsE 2 |> cmtSt64 |> cmtCall0
    |> cmtStepE |> cmtLd64 pDeg
    |> cmtStepsE 4 |> cmtSt32 |> cmtStepsE 5 |> cmtSt32
    |> cmtStepsE 4 |> cmtSt32 |> cmtStepsE 5 |> cmtSt32
    |> cmtStepsE 2 |> cmtLd64 pTmp

@[expose] def cmtP2GrpExpr (h64 : Val i64) (best_k sc : Val i32)
    (pAr pScr pCnt pFl pWv : Val i64) (brow_off mn : Val i32)
    (dd0 : Bool) (cv64 pDeg pTmp : Val i64)
    (si : Val i32) (dd1 ok1 : Bool) : Expr Val Cont [.bool] :=
  cmtP1GrpExpr h64 best_k sc pAr pScr pCnt pFl pWv brow_off mn dd0 cv64 pDeg pTmp
    |> cmtGrpB3 (si, dd1, ok1, ()) (fun _ _ => False)

@[expose] def cmtP2ExitExpr (h64 : Val i64) (best_k sc : Val i32)
    (pAr pScr pCnt pFl pWv : Val i64) (brow_off mn : Val i32)
    (dd0 : Bool) (cv64 pDeg pTmp : Val i64)
    (si : Val i32) (dd1 ok1 : Bool)
    (m_v : Val i32) (dd2 ok2 : Bool) (garb irred : Val i64) : Expr Val Cont [.bool] :=
  cmtP2GrpExpr h64 best_k sc pAr pScr pCnt pFl pWv brow_off mn dd0 cv64 pDeg pTmp si dd1 ok1
    |> cmtGrpB5 (m_v, dd2, ok2, garb, irred, ()) (fun _ _ => False)

@[expose] def cmtGrpB1_32 {rs : List Ty} (v : Val i32) (J : Cont [i32]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32]]) bs _ => match bs (J, ()) with | .cons f .nil => f (v, ())
  | _ => .hlt

@[expose] def cmtP4Expr (h64 : Val i64) (best_k sc : Val i32)
    (pAr pScr pCnt pFl pWv : Val i64) (brow_off mn : Val i32)
    (dd0 : Bool) (cv64 pDeg pTmp : Val i64)
    (si : Val i32) (dd1 ok1 : Bool)
    (m_v : Val i32) (dd2 ok2 : Bool) (garb irred : Val i64)
    (fs_i : Val i32) : Expr Val Cont [.bool] :=
  cmtThen (cmtP2ExitExpr h64 best_k sc pAr pScr pCnt pFl pWv brow_off mn dd0 cv64 pDeg pTmp
      si dd1 ok1 m_v dd2 ok2 garb irred)
    |> cmtGrpB1_32 fs_i (fun _ _ => False) |> cmtStepE |> cmtElse

theorem cmt_p2_exit_eq_ite (h64 : Val i64) (best_k sc : Val i32)
    (pAr pScr pCnt pFl pWv : Val i64) (brow_off mn : Val i32)
    (dd0 : Bool) (cv64 pDeg pTmp : Val i64)
    (si : Val i32) (dd1 ok1 : Bool)
    (m_v : Val i32) (dd2 ok2 : Bool) (garb irred : Val i64) :
    let e := cmtP2ExitExpr h64 best_k sc pAr pScr pCnt pFl pWv brow_off mn dd0 cv64 pDeg pTmp
      si dd1 ok1 m_v dd2 ok2 garb irred
    e = .jnz (Arg.var ok2) (cmtThen e) (cmtElse e) := rfl

/-! ## 4. Failure Exit WP -/

theorem cmt_fail_exit_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hFill : ∀ a m Q X, Limits.Spec.m7FillU64Spec a m Q X →
      Γ "full_fill_u64_m7" [i64, i64, i64] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_next : List (List Nat)} {s0 s : FullState}
    {R : Mem 64 → Prop} {best_k sc brow_off mn si m_v : Val i32}
    {dd0 dd1 ok1 dd2 ok2 : Bool} {cv64 garb irred : Val i64} {mp : Mem 64}
    (hinv : FullDenseInvW c F0 F_next s)
    (hcv_le : s0.core.cur_vars ≤ s.core.cur_vars)
    (hfuel : s.core.fuel = s0.core.fuel)
    (htm : s.scratch.tarjan_mark = s0.scratch.tarjan_mark)
    (htr : s.scratch.tarjan_reach = s0.scratch.tarjan_reach)
    (hmp : (FullMem c s ⋆ R) mp)
    (hQ : ∀ (ok : Bool) s' m',
      FullDenseInv c F0 s' → s0.core.cur_vars ≤ s'.core.cur_vars →
      (ok = true → s0.core.cur_vars < s'.core.cur_vars) →
      (ok = true → Step7BvaCommittedOk c s' best_k.toNat) →
      s'.core.fuel = s0.core.fuel →
      s'.scratch.tarjan_mark = s0.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s0.scratch.tarjan_reach →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (cmtElse (cmtP2ExitExpr c.hdr best_k sc c.pArena c.pScratchBuf c.pWsort c.pFlags
      c.pWvec brow_off mn dd0 cv64 c.pRepr c.pTmp si dd1 ok1 m_v dd2 ok2 garb irred)) mp := by
  refine wp_join0 (fun m1 => ∃ ag1,
      let s1 := { s with core := { s.core with arena_garbage := ag1 } }
      FullDenseInvW c F0 F_next s1 ∧ (FullMem c s1 ⋆ R) m1)
    (fun _ m1 ⟨ag1, hinv1, hm1⟩ => ?_)
    (fun J1 hJ1 => by
      c0_hfast_nogrp
      · c0_hfast; exact hJ1 m ⟨_, cmt_fullDenseInvW_set_garb hinv _, hm⟩
      · c0_hfast; exact hJ1 mp ⟨s.core.arena_garbage, hinv, hmp⟩)
  let s1 : FullState := { s with core := { s.core with arena_garbage := ag1 } }
  refine wp_join0 (fun m2 => ∃ ni2,
      let s2 := { s1 with core := { s1.core with num_irred := ni2 } }
      FullDenseInvW c F0 F_next s2 ∧ (FullMem c s2 ⋆ R) m2)
    (fun _ m2 ⟨ni2, hinv2, hm2⟩ => ?_)
    (fun J2 hJ2 => by
      c0_hfast_nogrp
      · c0_hfast; exact hJ2 m ⟨_, cmt_fullDenseInvW_set_irred hinv1 _, hm⟩
      · c0_hfast; exact hJ2 m1 ⟨s1.core.num_irred, hinv1, hm1⟩)
  let s2 : FullState := { s1 with core := { s1.core with num_irred := ni2 } }
  refine wp_join0 (fun m3 => ∃ ws3,
      let s3 := { s2 with scratch := { s2.scratch with wsort := ws3 } }
      FullDenseInvW c F0 F_next s3 ∧ (FullMem c s3 ⋆ R) m3)
    (fun _ m3 ⟨ws3, hinv3, hm3⟩ => by
      c0_hfast
      exact hQ false _ m3 hinv3.toDense hcv_le (fun h => by cases h) (fun h => by cases h)
        hfuel htm htr hm3)
    (fun J3 hJ3 => by
      c0_hfast_nogrp
      · fid_call hFill
        refine cmt_fill_wsort_spec hinv2.1 hm2 fun ws3 m3 hws3 hm3 => ?_
        c0_hfast; exact hJ3 m3 ⟨ws3, cmt_fullDenseInvW_set_wsort hinv2 hws3, hm3⟩
      · c0_hfast; exact hJ3 m2 ⟨s2.scratch.wsort, hinv2, hm2⟩)

end

end LeanQbe.T.Examples.Kissat.Proof.Factor
