module

public import LeanQbe.T.Examples.Kissat.FullWalkExtLemmas1
public import LeanQbe.T.Examples.Kissat.FullWalkExtLemmas2
import all Kraken.Mem
import all Kraken.Separation

/-!
# Kissat `D-Full` Walk, Mode, Restart & Extend `Func.wp` Proofs — Part 3 (`Stage 4`)

Proves `full_walk_collect_wp` and `full_walk_wp`, and re-exports all `11` `Func.wp` theorems for
the `Full2.lean` Walk, Mode, Restart & Extend shard.
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.Examples.Kissat.Full

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.ProofUtil
open LeanQbe.T.C0Step
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open Kraken.Bedrock2.Test
open FullWalkExtSpecs
open FullWalkExtHelpers
open scoped FullArenaTactics
open scoped FullWalkExtTactics

/-! ## 1. Arena scan, watch slice & fuel-preservation helpers -/

private theorem wp_let_or32_2 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {a b : Arg Val i32} {k : Tup Val [i32] → Expr Val Cont rs} :
    wp Γ Q X (.let_ { sig := [i32, i32], code := .or i32, args := (a, b, ()) } k) m =
      wp Γ Q X (k (a.val ||| b.val, ())) m := by
  simpa only [lift2] using @wp_let_or_eq Γ rs Q X m i32 (a, b, ()) k

private theorem wp_let_neg32_2 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {a : Arg Val i32} {k : Tup Val [i32] → Expr Val Cont rs} :
    wp Γ Q X (.let_ { sig := [i32], code := .neg i32, args := (a, ()) } k) m =
      wp Γ Q X (k (-a.val, ())) m := by
  simpa only [Ty.hasFloat, Ty.isFloatTree, Bool.false_eq_true, ite_false, lift1] using
    @wp_let_neg_eq Γ rs Q X m i32 (a, ()) k

private theorem wp_let_trunc64_32_2 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {m : Mem 64} {a : Arg Val (.bits 64)} {k : Tup Val [.bits 32] → Expr Val Cont rs} :
    wp Γ Q X (.let_ { sig := [i64], code := .trunc 64 32, args := (a, ()) } k) m =
      wp Γ Q X (k (a.val.setWidth 32, ())) m := by
  simpa using @wp_let_trunc_eq Γ rs Q X m 64 32 (a, ()) k

private theorem fullArenaScanRefs_next {ar : List (BitVec 32)} {alen : Nat} :
    ∀ {fuel pos r : Nat}, r ∈ fullArenaScanRefs ar alen pos fuel →
      (∀ q ∈ fullArenaScanRefs ar alen pos fuel,
        q + 3 ≤ alen ∧ fullArenaNextOff ar alen q ≤ alen ∧
        (fullArenaNextOff ar alen q = alen ∨ fullArenaNextOff ar alen q + 3 ≤ alen)) →
      alen - pos ≤ fuel →
      fullArenaNextOff ar alen r = alen ∨
      fullArenaNextOff ar alen r ∈ fullArenaScanRefs ar alen pos fuel
  | 0, _, _, h, _, _ => by simp [fullArenaScanRefs] at h
  | fuel + 1, pos, r, hr, hchain, hfl => by
    unfold fullArenaScanRefs at hr hchain ⊢
    split at hr
    · rename_i hle
      simp only [hle, ↓reduceIte]
      have hq := hchain pos (by simp [hle])
      have hb := fullArenaNextOff_bounds (ar := ar) (alen := alen) (cref := pos) hle
      rcases List.mem_cons.mp hr with rfl | hrest
      · rcases hq.2.2 with heq | hmore
        · exact Or.inl heq
        · right; apply List.mem_cons_of_mem
          cases fuel with
          | zero => omega
          | succ f' => unfold fullArenaScanRefs; simp [hmore]
      · rcases fullArenaScanRefs_next hrest
          (fun q hqm => hchain q (by simp [hle, hqm])) (by omega) with heq | hm
        · exact Or.inl heq
        · exact Or.inr (List.mem_cons_of_mem _ hm)
    · simp at hr

private theorem fullArenaClauseRefs_next {c : FullCfg} {F_cur : List (List Nat)} {k : FullCoreState}
    (ha : FullArenaClausesInv c F_cur k) {r : Nat} (hr : r ∈ fullArenaClauseRefsCore k) :
    fullArenaNextOff k.arena k.arena_len r = k.arena_len ∨
    fullArenaNextOff k.arena k.arena_len r ∈ fullArenaClauseRefsCore k :=
  fullArenaScanRefs_next hr (fun q hq => by
    have hwf := ha.refs_wf q hq; exact ⟨hwf.1, hwf.2.2.2.1, hwf.2.2.2.2⟩) (by omega)

private theorem zero_mem_fullArenaClauseRefsCore {k : FullCoreState} (h3 : 3 ≤ k.arena_len) :
    0 ∈ fullArenaClauseRefsCore k := by
  unfold fullArenaClauseRefsCore
  obtain ⟨f, hf⟩ : ∃ f, k.arena_len = f + 1 := ⟨k.arena_len - 1, by omega⟩
  rw [hf]; unfold fullArenaScanRefs
  have hle : 0 + 3 ≤ f + 1 := by omega
  simp [hle]

private theorem fullArenaClausesInv_with_fuel {c : FullCfg} {F_cur : List (List Nat)}
    {k : FullCoreState} (ha : FullArenaClausesInv c F_cur k) (fuel' : BitVec 64) :
    FullArenaClausesInv c F_cur { k with fuel := fuel' } :=
  ⟨ha.len_ok, ha.refs_wf, ha.shrk_term, ha.lits_lt, ha.entails⟩

private theorem modeWatchesInv_with_fuel {F_cur : List (List Nat)} {k : FullCoreState}
    (hw : ModeWatchesInv F_cur k) (fuel' : BitVec 64) :
    ModeWatchesInv F_cur { k with fuel := fuel' } :=
  hw.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr)

private theorem fullWalkEntriesOk_push_bin {s : FullState} {n : Nat}
    (hok : FullWalkEntriesOk s n) (hl : s.core.cur_vars < 2 * dimacsBound)
    {l ot : Nat} (hl_lt : l < 2 * s.core.cur_vars) (hot_lt : ot < 2 * s.core.cur_vars)
    (hlen_bd : 2 * n + 1 < s.scratch.scratch_buf.length) :
    let l32 := BitVec.ofNat 32 l ||| 0x80000000#32
    let ot32 := BitVec.ofNat 32 ot
    let buf' := (s.scratch.scratch_buf.set (2 * n) l32).set (2 * n + 1) ot32
    FullWalkEntriesOk { s with scratch := { s.scratch with scratch_buf := buf' } } (n + 1) := by
  intro l32 ot32 buf' idx hidx
  have hdim : 2 * dimacsBound < 2 ^ 30 := by unfold dimacsBound; decide
  have hl32_eq : l32 &&& 0x7FFFFFFF#32 = BitVec.ofNat 32 l := by
    dsimp only [l32]
    rw [BitVec.and_or_distrib_right,
      show (0x80000000#32 &&& 0x7FFFFFFF#32 : BitVec 32) = 0#32 by decide, BitVec.or_zero]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      show (0x7FFFFFFF#32 : BitVec 32).toNat = 2 ^ 31 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
  have hflag : (l32 &&& 0x80000000#32) ≠ 0#32 := bv32_or_ext_blk_flag
  unfold FullWalkEntryOk; dsimp only
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hidx) with hlt | rfl
  · have := hok idx hlt; unfold FullWalkEntryOk at this
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact this
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega),
      List.getElem?_set_self (by rw [List.length_set]; omega), Option.getD_some, Option.getD_some]
    have hl_to : (BitVec.ofNat 32 l).toNat = l := bv32_ofNat_toNat (by omega)
    have hot_to : ot32.toNat = ot := bv32_ofNat_toNat (by omega)
    split
    · rw [hl32_eq, hl_to, hot_to]; exact ⟨hl_lt, hot_lt⟩
    · exact absurd hflag (by assumption)

private theorem fullWalkEntriesOk_push_large {s : FullState} {n : Nat}
    (hok : FullWalkEntriesOk s n) {p : Nat} (hp_ref : p ∈ fullArenaClauseRefs s)
    (hp_ng : fullArenaClauseGarb s p = false) (hp_bd : p < 2 ^ 31)
    (hlen_bd : 2 * n + 1 < s.scratch.scratch_buf.length) :
    let p32 := BitVec.ofNat 32 p
    let buf' := (s.scratch.scratch_buf.set (2 * n) p32).set (2 * n + 1) 0#32
    FullWalkEntriesOk { s with scratch := { s.scratch with scratch_buf := buf' } } (n + 1) := by
  intro p32 buf' idx hidx
  have hflag : (p32 &&& 0x80000000#32) = 0#32 := by
    apply BitVec.eq_of_getElem_eq; intro i hi
    rw [BitVec.getElem_and, BitVec.getElem_zero, BitVec.getElem_eq_testBit_toNat,
      BitVec.getElem_eq_testBit_toNat]
    by_cases hi31 : i = 31
    · subst hi31
      rw [show p32.toNat = p from bv32_ofNat_toNat (by omega),
        Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hp_bd]; rfl
    · have h0 : (0x80000000#32 : BitVec 32).toNat.testBit i = false := by
        rw [show (0x80000000#32 : BitVec 32).toNat = 2 ^ 31 from rfl, Nat.testBit_two_pow]
        have hne : 31 ≠ i := Ne.symm hi31
        simp [hne]
      rw [h0, Bool.and_false]
  unfold FullWalkEntryOk; dsimp only
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hidx) with hlt | rfl
  · have := hok idx hlt; unfold FullWalkEntryOk at this
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]
    exact this
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by omega),
      List.getElem?_set_self (by rw [List.length_set]; omega), Option.getD_some]
    have hp_to : p32.toNat = p := bv32_ofNat_toNat (by omega)
    simp only [hflag, ne_eq, not_true_eq_false, ↓reduceIte, hp_to]
    exact ⟨hp_ref, hp_ng⟩

private theorem watchSlice_step {F_cur : List (List Nat)} {k : FullCoreState} {l p rem : Nat}
    (hdm : k.dense_mode = 0#64 → WatchSliceOk F_cur k l p rem)
    (hdns : k.dense_mode ≠ 0#64 → DenseWatchSliceOk F_cur k l p rem)
    (hpos : 0 < rem) :
    ∃ w0, k.wstk[p]? = some w0 ∧
      ((w0 &&& 0x80000000#32) ≠ 0#32 →
        (w0 &&& 0x7FFFFFFF#32).toNat < 2 * k.cur_vars ∧ 1 ≤ rem ∧
        (if k.dense_mode = 0#64 then WatchSliceOk F_cur k l (p + 1) (rem - 1)
         else DenseWatchSliceOk F_cur k l (p + 1) (rem - 1))) ∧
      ((w0 &&& 0x80000000#32) = 0#32 →
        2 ≤ rem ∧
        (if k.dense_mode = 0#64 then WatchSliceOk F_cur k l (p + 2) (rem - 2)
         else DenseWatchSliceOk F_cur k l (p + 2) (rem - 2))) := by
  by_cases hc : k.dense_mode = 0#64
  · cases hs : hdm hc with
    | empty => omega
    | bin hp hf _ hlt _ hrest =>
      refine ⟨_, hp, fun _ => ⟨hlt, by omega, by simpa [hc] using hrest⟩,
        fun h0 => absurd h0 hf⟩
    | large hp _ hf _ _ hrest =>
      refine ⟨_, hp, fun hne => absurd hf hne,
        fun _ => ⟨by omega, by simpa [hc] using hrest⟩⟩
  · cases hs : hdns hc with
    | empty => omega
    | bin hp hf _ hlt _ hrest =>
      refine ⟨_, hp, fun _ => ⟨hlt, by omega, by simpa [hc] using hrest⟩,
        fun h0 => absurd h0 hf⟩
    | occ hp _ hf _ _ _ hrest =>
      refine ⟨_, hp, fun hne => absurd hf hne,
        fun _ => ⟨by omega, by simpa [hc] using hrest⟩⟩

/-! ## 2. `full_walk_collect` -/

theorem full_walk_collect_wp (Γ : Env)
    (hArenaNext : ∀ a m Q X,
      fullArenaNextSpec a m Q X → Γ "full_arena_next" [i64, i32] [i32] a m Q X) :
    ∀ a m Q X, fullWalkCollectSpec a m Q X → Func.wp Γ full_walk_collect_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, ⟨rfl, F0, hinv⟩, hlen, hm, hQ⟩
  obtain ⟨F_cur, hw_inv⟩ := hinv.witness
  obtain ha := hw_inv.arena
  obtain hw := hw_inv.watches
  dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj, fullSafetySlice_safe] at hlen hm hQ
  obtain hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  obtain haca : c.arena_cap < 2 * dimacsBound := c.harena
  obtain hwc : c.wcap < 2 * dimacsBound := c.hwcap
  obtain hsca : c.scratch_cap < dimacsBound := c.hscr
  unfold dimacsBound at hmax haca hwc hsca
  obtain hcv_le := hlen.core_ok.cur_vars_le
  obtain harl := hlen.core_ok.arena_len_arr
  obtain hale := hlen.core_ok.arena_len_le
  obtain hwvl := hlen.core_ok.wvec_len
  obtain hwsl := hlen.core_ok.wstk_len_arr
  obtain hwll := hlen.core_ok.wlen_le
  obtain hsbl := hlen.scratch_ok.scratch_buf_len
  c0_to_group
  · c0_steps
    exact hQ (0#64, ()) s m rfl hlen ⟨⟨rfl, rfl⟩, by simp, fun _ h => by simp at h⟩ hm
  · have hcap4 : 4 ≤ c.scratch_cap := by bv_omega
    refine wp_join_group
      (fun ((max_cl : BitVec 64), ()) m1 =>
        m1 = m ∧ max_cl.toNat ≤ c.scratch_cap / 2 ∧ max_cl.toNat ≤ 4096)
      (fun J ((max_cl : BitVec 64), ()) m1 ⟨hm1_eq, hmc_cap, hmc_4096⟩ => ?_) (fun J hJ => ?_)
    · subst m1
      c0_to_group
      refine wp_loop_safety_slice (fullSafetySlice c) s R (fun _ => True) trivial
        (fun s1 ((n : BitVec 64), (l : BitVec 64), ()) =>
          l.toNat ≤ 2 * s.core.cur_vars ∧ n.toNat ≤ max_cl.toNat ∧
          FullWalkEntriesOk s1 n.toNat ∧
          s1.scratch.last_learned = s.scratch.last_learned ∧
          s1.scratch.extend_len = s.scratch.extend_len)
        (fun ((_ : BitVec 64), (l : BitVec 64), ()) => 2 * s.core.cur_vars - l.toNat)
        (fun J1 hJ1 => ?_)
        (fun J1 s1 ((n : BitVec 64), (l : BitVec 64), ()) m1 hcore1 hs1 _
            ⟨hlle, hnle, hok1, hll1, hel1⟩ hm1 hJ1 => ?_)
      · c0_steps
        exact hJ1 s (0#64, 0#64, ()) m hm rfl hlen
          ⟨by simp, by simp, fun _ h => by simp at h, rfl, rfl⟩
      · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj, fullSafetySlice_safe] at hs1 hm1
        have heq1 := fullCoreState_agrees_with_scratch hcore1
        obtain hsbl1 := hs1.scratch_ok.scratch_buf_len
        obtain hwvl1 := hs1.core_ok.wvec_len
        refine wp_join_group (fun (_ : Tup Val []) m1' => m1' = m1)
          (fun L4 _ m1' hm1' => ?_) (fun L4 hL4 => ?_)
        · subst m1'
          clear J1 hJ1
          refine wp_loop_safety_slice (fullSafetySlice c) s1 R (fun _ => True) trivial
            (fun s2 ((n1 : BitVec 64), (p : BitVec 64), ()) =>
              p.toNat ≤ s.core.arena_len ∧
              (p.toNat = s.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefsCore s.core) ∧
              n1.toNat ≤ max_cl.toNat ∧ FullWalkEntriesOk s2 n1.toNat ∧
              s2.scratch.last_learned = s.scratch.last_learned ∧
              s2.scratch.extend_len = s.scratch.extend_len)
            (fun ((_ : BitVec 64), (p : BitVec 64), ()) => s.core.arena_len - p.toNat)
            (fun J2 hJ2 => ?_)
            (fun J2 s2 ((n1 : BitVec 64), (p : BitVec 64), ()) m2 hcore2 hs2 _
                ⟨hple, hpref, hn1_le, hok2, hll2, hel2⟩ hm2 hJ2 => ?_)
          · c0_steps
            refine hJ2 s1 (n, 0#64, ()) m1 hm1 rfl hs1 ⟨by simp, ?_, hnle, hok1, hll1, hel1⟩
            rcases ha.len_ok with hz | h3
            · exact Or.inl hz.symm
            · exact Or.inr (zero_mem_fullArenaClauseRefsCore h3)
          · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
              fullSafetySlice_safe] at hs2 hm2
            have heq2 : s2.core = s.core := (fullCoreState_agrees_with_scratch hcore2).trans heq1
            obtain harl2 := hs2.core_ok.arena_len_arr
            obtain hsbl2 := hs2.scratch_ok.scratch_buf_len
            rw [Blocks.get_here]; dsimp only
            rw [wp_let_add64_2]
            refine wp_load_of (by simpa only [Arg.val_var, Arg.val_imm] using
              FullArenaTactics.load_full_arena_len hm2) ?_
            rw [wp_let_ult64_2]; refine wp_jnz_of ?_ ?_
            · intro hp_lt_c
              simp only [Arg.val_var] at hp_lt_c
              have hp_lt : p.toNat < s.core.arena_len := by
                have h1 : p.toNat < (BitVec.ofNat 64 s2.core.arena_len).toNat := by
                  simpa [BitVec.ult] using hp_lt_c
                rw [heq2, bv64_ofNat_toNat (by omega)] at h1; exact h1
              rw [wp_let_ult64_2]; refine wp_jnz_of ?_ ?_
              · intro hn1_lt_c
                simp only [Arg.val_var] at hn1_lt_c
                have hn1_lt : n1.toNat < max_cl.toNat := by simpa [BitVec.ult] using hn1_lt_c
                have hp_mem_ref : p.toNat ∈ fullArenaClauseRefsCore s.core := by
                  rcases hpref with heq | hm_ref
                  · omega
                  · exact hm_ref
                have hwf := ha.refs_wf p.toNat hp_mem_ref
                have hp_ar : p.toNat < s2.core.arena.length := by rw [harl2]; omega
                have hp2_eq : (p + 2).toNat = p.toNat + 2 := by bv_omega
                have hp2_ar : (p + 2).toNat < s2.core.arena.length := by rw [hp2_eq, harl2]; omega
                rw [wp_let_mul64_2, wp_let_add64_2]
                refine wp_load_of (by simpa only [Arg.val_var, Arg.val_imm] using
                  FullArenaTactics.c0_load_full_arena hp_ar hm2) ?_
                rw [wp_let_add64_2, wp_let_mul64_2, wp_let_add64_2]
                refine wp_load_of (by simpa only [Arg.val_var, Arg.val_imm] using
                  FullArenaTactics.c0_load_full_arena hp2_ar hm2) ?_
                refine wp_join_safety_slice (fullSafetySlice c) s2 R (fun _ => True) trivial
                  (fun s3 ((n2 : BitVec 64), ()) =>
                    n2.toNat ≤ max_cl.toNat ∧ FullWalkEntriesOk s3 n2.toNat ∧
                    s3.scratch.last_learned = s.scratch.last_learned ∧
                    s3.scratch.extend_len = s.scratch.extend_len)
                  (fun Jn s3 ((n2 : BitVec 64), ()) m3 hcore3 hs3 _ ⟨hn2_le, hok3, hll3, hel3⟩
                      hm3 => ?_)
                  (fun Jn hJn => ?_)
                · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
                    fullSafetySlice_safe] at hs3 hm3
                  have heq3 : s3.core = s.core :=
                    (fullCoreState_agrees_with_scratch hcore3).trans heq2
                  rw [Blocks.get_here]; dsimp only
                  rw [wp_let_trunc_eq]; dsimp only [Arg.val_var]
                  refine ⟨by decide, ?_⟩
                  c0_call hArenaNext
                  refine ⟨c, s3, R, rfl, hs3, hm3, ?_⟩
                  have hp32_toNat : (p.setWidth 32).toNat = p.toNat := by bv_omega
                  have hnxt_bd := fullArenaNextOff_bounds (ar := s.core.arena)
                    (alen := s.core.arena_len) (cref := p.toNat) hwf.1
                  have hnxt_zext :
                      ((BitVec.ofNat 32 (fullArenaNextOff s3.core.arena s3.core.arena_len
                        (p.setWidth 32).toNat)).setWidth 64).toNat =
                      fullArenaNextOff s.core.arena s.core.arena_len p.toNat := by
                    rw [heq3, hp32_toNat, zext_toNat _ (by decide), bv32_ofNat_toNat (by omega)]
                  refine hJ2 s3 (n2, _, ()) m3 hm3 (by dsimp only; rw [hnxt_zext]; omega)
                    hcore3 hs3 ⟨by rw [hnxt_zext]; exact hnxt_bd.2, ?_, hn2_le, hok3, hll3, hel3⟩
                  rw [hnxt_zext]
                  exact fullArenaClauseRefs_next ha hp_mem_ref
                · c0_steps
                  · rename_i hgarb_eq _
                    have hgarb_f : fullArenaClauseGarb s2 p.toNat = false := by
                      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
                      rw [List.getElem?_eq_getElem hp_ar, Option.getD_some, bne_eq_false_iff_eq]
                      exact hgarb_eq
                    have h2n : (n1 <<< (1 : Nat)).toNat = 2 * n1.toNat := by
                      rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
                    have h2n_lt : (n1 <<< (1 : Nat)).toNat < s2.scratch.scratch_buf.length := by
                      rw [hsbl2, h2n]; omega
                    have h2np1_lt : ((n1 <<< (1 : Nat)) + 1).toNat <
                        (s2.scratch.scratch_buf.set (n1 <<< (1 : Nat)).toNat
                          (p.setWidth 32)).length := by
                      rw [List.length_set, hsbl2, BitVec.toNat_add, h2n]; simp; omega
                    c0_steps
                    have hp32_eq : p.setWidth 32 = BitVec.ofNat 32 p.toNat := by
                      apply BitVec.eq_of_toNat_eq
                      rw [BitVec.toNat_setWidth, bv32_ofNat_toNat (by omega),
                        Nat.mod_eq_of_lt (by omega)]
                    have h2np1_eq : ((n1 <<< (1 : Nat)) + 1).toNat = 2 * n1.toNat + 1 := by
                      rw [BitVec.toNat_add, h2n]; simp; omega
                    have hn11 : (n1 + 1).toNat = n1.toNat + 1 := by bv_omega
                    refine hJn _ (n1 + 1, ()) _ hm rfl
                      ⟨hs2.core_ok, { hs2.scratch_ok with scratch_buf_len := by simp [hsbl2] }⟩
                      ⟨by rw [hn11]; omega, ?_, hll2, hel2⟩
                    have hok2' := fullWalkEntriesOk_push_large hok2
                      (by unfold fullArenaClauseRefs; rw [heq2]; exact hp_mem_ref)
                      hgarb_f (by omega) (by rw [hsbl2]; omega)
                    rw [hn11]
                    simpa only [heq2, h2n, h2np1_eq, hp32_eq,
                      show (0 : BitVec 32) = 0#32 from rfl,
                      Nat.mod_eq_of_lt (by omega : 2 * n1.toNat < 2 ^ 64),
                      Nat.mod_eq_of_lt (by omega : 2 * n1.toNat + 1 < 2 ^ 64)] using hok2'
                  all_goals exact hJn s2 (n1, ()) m2 hm2 rfl hs2 ⟨hn1_le, hok2, hll2, hel2⟩
              · intro _; rw [wp_ret]
                exact hQ (n1, ()) s2 m2 (hcore1.trans hcore2) hs2
                  ⟨⟨hll2, hel2⟩, by dsimp only; omega, hok2⟩ hm2
            · intro _; rw [wp_ret]
              exact hQ (n1, ()) s2 m2 (hcore1.trans hcore2) hs2
                ⟨⟨hll2, hel2⟩, by dsimp only; omega, hok2⟩ hm2
        · c0_to_group
          · rename_i hl_lt_c
            have hl_lt : l.toNat < 2 * s.core.cur_vars := by omega
            have hn_lt : n.toNat < max_cl.toNat := hc
            have hl2 : (l <<< (1 : Nat)).toNat = 2 * l.toNat := by
              rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
            have hl2_lt : (l <<< (1 : Nat)).toNat < s1.core.wvec.length := by
              rw [hwvl1, hl2]; omega
            have hl2p1_lt : ((l <<< (1 : Nat)) + 1).toNat < s1.core.wvec.length := by
              rw [hwvl1, BitVec.toNat_add, hl2]; simp; omega
            let off0 := fullWatchOffCore s.core l.toNat
            let sz0 := fullWatchSizeCore s.core l.toNat
            have hbd0 : off0 + sz0 ≤ s.core.wlen := hw.bounds l.toNat hl_lt
            have hoff_eq : (s1.core.wvec[(l <<< (1 : Nat)).toNat]'hl2_lt).setWidth 64 =
                BitVec.ofNat 64 off0 := by
              apply BitVec.eq_of_toNat_eq
              rw [zext_toNat _ (by decide), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
              unfold off0 fullWatchOffCore
              simp only [heq1, hl2,
                List.getElem?_eq_getElem (by omega : 2 * l.toNat < s.core.wvec.length),
                Option.getD_some]
            have hsz_eq : (s1.core.wvec[((l <<< (1 : Nat)) + 1).toNat]'hl2p1_lt).setWidth 64 =
                BitVec.ofNat 64 sz0 := by
              apply BitVec.eq_of_toNat_eq
              rw [zext_toNat _ (by decide), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
              unfold sz0 fullWatchSizeCore
              have hidx : ((l <<< (1 : Nat)) + 1).toNat = 2 * l.toNat + 1 := by
                rw [BitVec.toNat_add, hl2]; simp; omega
              simp only [heq1, hidx,
                List.getElem?_eq_getElem (by omega : 2 * l.toNat + 1 < s.core.wvec.length),
                Option.getD_some]
            refine wp_loop_safety_slice (fullSafetySlice c) s1 R (fun _ => True) trivial
              (fun s2 ((n1 : BitVec 64), (off : BitVec 64), ()) =>
                off.toNat ≤ off0 + sz0 ∧ n1.toNat ≤ max_cl.toNat ∧
                FullWalkEntriesOk s2 n1.toNat ∧
                (∃ rem, off.toNat + rem = off0 + sz0 ∧
                  (if s.core.dense_mode = 0#64 then WatchSliceOk F_cur s.core l.toNat off.toNat rem
                   else DenseWatchSliceOk F_cur s.core l.toNat off.toNat rem)) ∧
                s2.scratch.last_learned = s.scratch.last_learned ∧
                s2.scratch.extend_len = s.scratch.extend_len)
              (fun ((_ : BitVec 64), (off : BitVec 64), ()) => off0 + sz0 - off.toNat)
              (fun Jw hJw => ?_)
              (fun Jw s2 ((n1 : BitVec 64), (off : BitVec 64), ()) m2 hcore2 hs2 _
                  ⟨hoff_le, hn1_le, hok2, ⟨rem, hrem_eq, hslice⟩, hll2, hel2⟩ hm2 hJw => ?_)
            · c0_steps
              refine hJw s1 (n, _, ()) m1 hm1 rfl hs1 ⟨by rw [hoff_eq]; bv_omega, hnle, hok1,
                ⟨sz0, by rw [hoff_eq]; bv_omega, ?_⟩, hll1, hel1⟩
              by_cases hdm : s.core.dense_mode = 0#64
              · simp only [hdm, ↓reduceIte]; simp only [ModeWatchesInv, hdm, ↓reduceIte] at hw
                rw [hoff_eq, bv64_ofNat_toNat (by omega)]
                exact hw.slices l.toNat hl_lt
              · simp only [hdm, ↓reduceIte]; simp only [ModeWatchesInv, hdm, ↓reduceIte] at hw
                rw [hoff_eq, bv64_ofNat_toNat (by omega)]
                exact hw.slices l.toNat hl_lt
            · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
                fullSafetySlice_safe] at hs2 hm2
              have heq2 : s2.core = s.core := (fullCoreState_agrees_with_scratch hcore2).trans heq1
              obtain hsbl2 := hs2.scratch_ok.scratch_buf_len
              obtain hwsl2 := hs2.core_ok.wstk_len_arr
              refine wp_join_group (fun (_ : Tup Val []) m2' => m2' = m2)
                (fun L8 _ m2' hm2' => ?_) (fun L8 hL8 => ?_)
              · subst m2'
                c0_steps
                have hl1 : (l + 1).toNat = l.toNat + 1 := by bv_omega
                exact hJ1 s2 (n1, l + 1, ()) m2 hm2 (by dsimp only; rw [hl1]; omega)
                  hcore2 hs2 ⟨by rw [hl1]; omega, hn1_le, hok2, hll2, hel2⟩
              · c0_split
                · c0_split
                  · rename_i hoff_lt_c
                    have hoff_lt : off.toNat < off0 + sz0 := by
                      have h1b : (1 : BitVec 64).toNat = 1 := rfl
                      have h1 : (s1.core.wvec[2 * l.toNat % 2 ^ 64]'(by rw [hwvl1]; omega)).toNat =
                          off0 := by
                        unfold off0 fullWatchOffCore
                        simp only [heq1, Nat.mod_eq_of_lt (by omega : 2 * l.toNat < 2 ^ 64),
                          List.getElem?_eq_getElem (by omega : 2 * l.toNat < s.core.wvec.length),
                          Option.getD_some]
                      have h2 : (s1.core.wvec[(2 * l.toNat + BitVec.toNat 1) % 2 ^ 64]'(by
                          rw [hwvl1, h1b]; omega)).toNat = sz0 := by
                        unfold sz0 fullWatchSizeCore
                        simp only [heq1, h1b,
                          Nat.mod_eq_of_lt (by omega : 2 * l.toNat + 1 < 2 ^ 64),
                          List.getElem?_eq_getElem
                            (by omega : 2 * l.toNat + 1 < s.core.wvec.length), Option.getD_some]
                      rw [h1, h2, Nat.mod_eq_of_lt (by omega)] at hoff_lt_c; exact hoff_lt_c
                    have hn1_lt : n1.toNat < max_cl.toNat := hc
                    have hrem_pos : 0 < rem := by omega
                    have hoff_wstk : off.toNat < s2.core.wstk.length := by rw [hwsl2]; omega
                    obtain ⟨w0, hw0_some, hbin_br, hlrg_br⟩ := watchSlice_step
                      (F_cur := F_cur) (k := s.core) (l := l.toNat) (p := off.toNat)
                      (fun hdm => by simpa [hdm] using hslice)
                      (fun hdm => by simpa [hdm] using hslice) hrem_pos
                    have hw0_eq : s2.core.wstk[off.toNat]'hoff_wstk = w0 := by
                      have : s2.core.wstk[off.toNat]? = some w0 := by rw [heq2]; exact hw0_some
                      rw [List.getElem?_eq_getElem hoff_wstk] at this; exact Option.some.inj this
                    refine wp_load_of (FullArenaTactics.c0_load_full_wstk hoff_wstk hm2) ?_
                    refine wp_join_safety_slice (fullSafetySlice c) s2 R (fun _ => True) trivial
                      (fun s3 ((n' : BitVec 64), (off' : BitVec 64), ()) =>
                        off'.toNat ≤ off0 + sz0 ∧ off0 + sz0 - off'.toNat < off0 + sz0 - off.toNat ∧
                        n'.toNat ≤ max_cl.toNat ∧ FullWalkEntriesOk s3 n'.toNat ∧
                        (∃ rem', off'.toNat + rem' = off0 + sz0 ∧
                          (if s.core.dense_mode = 0#64
                           then WatchSliceOk F_cur s.core l.toNat off'.toNat rem'
                           else DenseWatchSliceOk F_cur s.core l.toNat off'.toNat rem')) ∧
                        s3.scratch.last_learned = s.scratch.last_learned ∧
                        s3.scratch.extend_len = s.scratch.extend_len)
                      (fun L10 s3 ((n' : BitVec 64), (off' : BitVec 64), ()) m3 hcore3 hs3 _
                          ⟨hoff', hdec', hn', hok', hrem', hll', hel'⟩ hm3 => ?_)
                      (fun L10 hL10 => ?_)
                    · rw [Blocks.get_here]; dsimp only; rw [wp_jump]
                      exact hJw s3 (n', off', ()) m3 hm3 hdec' hcore3 hs3
                        ⟨hoff', hn', hok', hrem', hll', hel'⟩
                    · rw [wp_let_and32_2, wp_let_ne32_2]; refine wp_jnz_of ?_ ?_
                      · intro hbin_c
                        simp only [Arg.val_var, Arg.val_imm] at hbin_c
                        have hbin_ne : (w0 &&& 0x80000000#32) ≠ 0#32 := by
                          rw [← hw0_eq]; simpa [bne_iff_ne] using hbin_c
                        obtain ⟨hot_lt, hrem1, hslice'⟩ := hbin_br hbin_ne
                        rw [wp_let_and32_2]
                        let ot := (s2.core.wstk[off.toNat]'hoff_wstk) &&& 0x7FFFFFFF#32
                        have hot_lt' : ot.toNat < 2 * s.core.cur_vars := by
                          simpa [ot, hw0_eq] using hot_lt
                        have hoff1 : (off + 1).toNat = off.toNat + 1 := by bv_omega
                        refine wp_join_safety_slice (fullSafetySlice c) s2 R (fun _ => True) trivial
                          (fun s3 ((n'' : BitVec 64), ()) =>
                            n''.toNat ≤ max_cl.toNat ∧ FullWalkEntriesOk s3 n''.toNat ∧
                            s3.scratch.last_learned = s.scratch.last_learned ∧
                            s3.scratch.extend_len = s.scratch.extend_len)
                          (fun L12 s3 ((n'' : BitVec 64), ()) m3 hcore3 hs3 _
                              ⟨hn'', hok'', hll'', hel''⟩ hm3 => ?_)
                          (fun L12 hL12 => ?_)
                        · rw [Blocks.get_here]; dsimp only; rw [wp_let_add64_2, wp_jump]
                          exact hL10 s3 (n'', off + 1, ()) m3 hm3 hcore3 hs3
                            ⟨by rw [hoff1]; omega, by rw [hoff1]; omega, hn'', hok'',
                              ⟨rem - 1, by rw [hoff1]; omega, by rw [hoff1]; exact hslice'⟩,
                              hll'', hel''⟩
                        · rw [wp_let_zext32_2, wp_let_ult64_2]; refine wp_jnz_of ?_ ?_
                          · intro _
                            have h2n : (n1 <<< (1 : Nat)).toNat = 2 * n1.toNat := by
                              rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
                            have h2n_lt : (n1 <<< (1 : Nat)).toNat <
                                s2.scratch.scratch_buf.length := by rw [hsbl2, h2n]; omega
                            have h2np1_lt : ((n1 <<< (1 : Nat)) + 1).toNat <
                                (s2.scratch.scratch_buf.set (n1 <<< (1 : Nat)).toNat
                                  ((l.setWidth 32) ||| 0x80000000#32)).length := by
                              rw [List.length_set, hsbl2, BitVec.toNat_add, h2n]; simp; omega
                            have hsext1 : (BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64 = 1 :=
                              rfl
                            have hmsb : (2147483648 : BitVec 32) = 0x80000000#32 := rfl
                            have hot_eq :
                                (s2.core.wstk[off.toNat]'hoff_wstk &&& (2147483647 : BitVec 32)) =
                                  ot := rfl
                            repeat (first
                              | rw [wp_let_trunc64_32_2] | rw [wp_let_or32_2]
                              | rw [wp_let_sext32_64_2] | rw [wp_let_shl64_2]
                              | rw [wp_let_mul64_2] | rw [wp_let_add64_2])
                            refine wp_store_sep (by
                              simpa only [Arg.val_var, Arg.val_imm, hsext1, hmsb] using
                                FullArenaTactics.c0_store_full_scratch_buf
                                  ((l.setWidth 32) ||| 0x80000000#32) h2n_lt hm2) fun m3 hm3 => ?_
                            repeat (first
                              | rw [wp_let_sext32_64_2] | rw [wp_let_shl64_2]
                              | rw [wp_let_mul64_2] | rw [wp_let_add64_2])
                            refine wp_store_sep (by
                              simpa only [Arg.val_var, Arg.val_imm, hsext1, hot_eq] using
                                FullArenaTactics.c0_store_full_scratch_buf
                                  ot h2np1_lt hm3) fun m4 hm4 => ?_
                            rw [wp_let_add64_2, wp_jump]
                            have hl32_eq : l.setWidth 32 = BitVec.ofNat 32 l.toNat := by
                              apply BitVec.eq_of_toNat_eq
                              rw [BitVec.toNat_setWidth, bv32_ofNat_toNat (by omega),
                                Nat.mod_eq_of_lt (by omega)]
                            have hot32_eq : ot = BitVec.ofNat 32 ot.toNat :=
                              BitVec.eq_of_toNat_eq (by
                                rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ot.isLt])
                            have h2np1_eq : ((n1 <<< (1 : Nat)) + 1).toNat = 2 * n1.toNat + 1 := by
                              rw [BitVec.toNat_add, h2n]; simp; omega
                            have hn11 : (n1 + 1).toNat = n1.toNat + 1 := by bv_omega
                            refine hL12 _ (n1 + 1, ()) m4 hm4 rfl
                              ⟨hs2.core_ok, { hs2.scratch_ok with
                                scratch_buf_len := by simp [hsbl2] }⟩
                              ⟨by rw [hn11]; omega, ?_, hll2, hel2⟩
                            have hok2' := fullWalkEntriesOk_push_bin hok2
                              (by rw [heq2]; unfold dimacsBound; omega)
                              (by rw [heq2]; exact hl_lt) (by rw [heq2]; exact hot_lt')
                              (by rw [hsbl2]; omega)
                            rw [hn11]
                            simpa only [h2n, h2np1_eq, hl32_eq, ← hot32_eq] using hok2'
                          · intro _; rw [wp_jump]
                            exact hL12 s2 (n1, ()) m2 hm2 rfl hs2 ⟨hn1_le, hok2, hll2, hel2⟩
                      · intro hbin_f
                        dsimp only [Arg.val] at hbin_f
                        have hbin_eq : (w0 &&& 0x80000000#32) = 0#32 := by
                          rw [← hw0_eq]; simpa [bne_eq_false_iff_eq] using hbin_f
                        obtain ⟨hrem2, hslice'⟩ := hlrg_br hbin_eq
                        have hoff2 : (off + 2).toNat = off.toNat + 2 := by bv_omega
                        rw [wp_let_add64_2, wp_jump]
                        exact hL10 s2 (n1, off + 2, ()) m2 hm2 rfl hs2
                          ⟨by rw [hoff2]; omega, by rw [hoff2]; omega, hn1_le, hok2,
                            ⟨rem - 2, by rw [hoff2]; omega, by rw [hoff2]; exact hslice'⟩,
                            hll2, hel2⟩
                  · c0_steps; exact hL8 () m2 rfl
                · c0_steps; exact hL8 () m2 rfl
          all_goals exact hL4 () m1 rfl
    · c0_steps
      · have hshr : (BitVec.ofNat 64 c.scratch_cap >>> (1 : Nat)).toNat = c.scratch_cap / 2 := by
          rw [BitVec.toNat_ushiftRight, bv64_ofNat_toNat (by omega)]
          simp [Nat.shiftRight_eq_div_pow]
        refine hJ _ _ ⟨rfl, ?_, by decide⟩
        rw [hshr] at hc; omega
      · have hshr : (BitVec.ofNat 64 c.scratch_cap >>> (1 : Nat)).toNat = c.scratch_cap / 2 := by
          rw [BitVec.toNat_ushiftRight, bv64_ofNat_toNat (by omega)]
          simp [Nat.shiftRight_eq_div_pow]
        refine hJ _ _ ⟨rfl, ?_, ?_⟩
        · rw [hshr]; omega
        · rw [hshr] at hc ⊢; bv_omega

/-! ## 3. `full_walk` -/

theorem full_walk_wp (Γ : Env)
    (hCollect : ∀ a m Q X, fullWalkCollectSpec a m Q X → Γ "full_walk_collect" [i64] [i64] a m Q X)
    (hClSat : ∀ a m Q X, fullWalkClSatSpec a m Q X →
      Γ "full_walk_cl_sat" [i64, i64, i64] [.bool] a m Q X)
    (hRng : ∀ a m Q X, fullRngNextSpec a m Q X → Γ "full_rng_next" [i64] [i64] a m Q X)
    (hPick : ∀ a m Q X, fullWalkPickLitSpec a m Q X →
      Γ "full_walk_pick_lit" [i64, i64, i64] [i32] a m Q X) :
    ∀ a m Q X, fullWalkSpec a m Q X → Func.wp Γ full_walk_body a m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  obtain hlen := hinv.lengths
  obtain ⟨F_cur, hw_inv⟩ := hinv.witness
  obtain ha := hw_inv.arena
  obtain hw := hw_inv.watches
  obtain hmax : c.max_vars < 2 * dimacsBound := c.hmaxv
  obtain hsca : c.scratch_cap < dimacsBound := c.hscr
  unfold dimacsBound at hmax hsca
  obtain hcv_le : s.core.cur_vars ≤ c.max_vars := hlen.core_ok.cur_vars_le
  c0_steps
  c0_call hCollect
  refine ⟨c, s, R, ⟨rfl, F0, hinv⟩, hlen, hm, ?_⟩
  intro ⟨ncl, ⟨⟩⟩ s1 m1 hcore1 hs1 ⟨⟨hll1, hel1⟩, hncl_cap, hok1⟩ hm1
  dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj, fullSafetySlice_safe] at hs1 hm1
  have heq1 := fullCoreState_agrees_with_scratch hcore1
  refine wp_jnz_of ?_ ?_
  · intro _; c0_steps
    have hcore_eq : ({ s.core with fuel := s1.core.fuel } : FullCoreState) = s1.core := by
      rw [heq1]
    have heq_st : FullState.mk { s.core with fuel := s1.core.fuel } s1.scratch = s1 := by
      cases s1; dsimp only at hcore_eq ⊢; congr 1
    exact hQ s1.core.fuel s1.scratch m1
      (by rw [heq_st]; exact hs1) (by rw [heq1]; exact Nat.le_refl _) ⟨hll1, hel1⟩
      (by rw [heq_st]; exact hm1)
  · intro hncl_ne
    have hncl_pos : 0 < ncl.toNat := by
      simp only [Arg.val_var, beq_eq_false_iff_ne] at hncl_ne; bv_omega
    have hcv_le1 := hs1.core_ok.cur_vars_le
    rw [wp_let_add64_2]
    refine wp_load_of (by simpa only [Arg.val_var, Arg.val_imm] using
      FullArenaTactics.load_full_walk_vals_ptr hm1) ?_
    rw [wp_let_add64_2]
    refine wp_load_of (by simpa only [Arg.val_var, Arg.val_imm] using
      FullArenaTactics.load_full_walk_best_ptr hm1) ?_
    rw [wp_let_add64_2]
    refine wp_load_of (by simpa only [Arg.val_var, Arg.val_imm] using
      FullArenaTactics.load_full_phases_ptr hm1) ?_
    rw [wp_let_add64_2]
    refine wp_load_of (by simpa only [Arg.val_var, Arg.val_imm] using
      FullArenaTactics.load_full_scratch_buf_ptr hm1) ?_
    rw [wp_let_add64_2]
    refine wp_load_of (by simpa only [Arg.val_var, Arg.val_imm] using
      FullArenaTactics.load_full_cur_vars hm1) ?_
    refine wp_loop_safety_slice (fullSafetySlice c) s1 R (fun _ => True) trivial
      (fun s2 ((v : BitVec 64), ()) => v.toNat ≤ s.core.cur_vars ∧
        s2.scratch.scratch_buf = s1.scratch.scratch_buf ∧
        s2.scratch.last_learned = s.scratch.last_learned ∧
        s2.scratch.extend_len = s.scratch.extend_len)
      (fun ((v : BitVec 64), ()) => s.core.cur_vars - v.toNat)
      (fun Ji hJi => ?_)
      (fun Ji s2 ((v : BitVec 64), ()) m2 hcore2 hs2 _ ⟨hvle, hsb2, hll2, hel2⟩ hm2 hJi => ?_)
    · rw [wp_jump]; exact hJi s1 (0#64, ()) m1 hm1 rfl hs1 ⟨by simp, rfl, hll1, hel1⟩
    · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj, fullSafetySlice_safe] at hs2 hm2
      have heq2 : s2.core = s.core := (fullCoreState_agrees_with_scratch hcore2).trans heq1
      obtain hphl2 := hs2.scratch_ok.phases_len
      obtain hwvl2 := hs2.scratch_ok.walk_vals_len
      obtain hwbl2 := hs2.scratch_ok.walk_best_len
      rw [Blocks.get_here]; dsimp only
      rw [wp_let_ult64_2]; refine wp_jnz_of ?_ ?_
      · intro hv_lt_c
        simp only [Arg.val_var] at hv_lt_c
        have hv_lt : v.toNat < s.core.cur_vars := by
          have h1 : v.toNat < (BitVec.ofNat 64 s1.core.cur_vars).toNat := by
            simpa [BitVec.ult] using hv_lt_c
          rw [heq1, bv64_ofNat_toNat (by omega)] at h1; exact h1
        have hv_ph : v.toNat < s2.scratch.phases.length := by rw [hphl2]; omega
        refine wp_join_group
          (fun ((p32 : BitVec 32), ()) m2' => m2' = m2)
          (fun Jp ((p32 : BitVec 32), ()) m2' hm2' => ?_) (fun Jp hJp => ?_)
        · subst m2'
          have hv2 : (v <<< (1 : Nat)).toNat = 2 * v.toNat := by
            rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
          have hv2_lt : (v <<< (1 : Nat)).toNat < s2.scratch.walk_vals.length := by
            rw [hwvl2, hv2]; omega
          have hv2p1_lt : ((v <<< (1 : Nat)) + 1).toNat <
              (s2.scratch.walk_vals.set (v <<< (1 : Nat)).toNat (p32.setWidth 8)).length := by
            rw [List.length_set, hwvl2, BitVec.toNat_add, hv2]; simp; omega
          have hv_wb : v.toNat < s2.scratch.walk_best.length := by rw [hwbl2]; omega
          have hsext1 : (BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64 = 1 := rfl
          rw [Blocks.get_here]; dsimp only
          repeat (first
            | rw [wp_let_trunc32_8_2] | rw [wp_let_sext8_32_2] | rw [wp_let_neg32_2]
            | rw [wp_let_sext32_64_2] | rw [wp_let_shl64_2] | rw [wp_let_add64_2])
          refine wp_store_sep (by
            simpa only [Arg.val_var, Arg.val_imm, hsext1] using
              FullArenaTactics.c0_store_full_walk_vals (p32.setWidth 8) hv2_lt hm2) fun m3 hm3 => ?_
          repeat (first
            | rw [wp_let_trunc32_8_2] | rw [wp_let_sext8_32_2] | rw [wp_let_neg32_2]
            | rw [wp_let_sext32_64_2] | rw [wp_let_shl64_2] | rw [wp_let_add64_2])
          refine wp_store_sep (by
            simpa only [Arg.val_var, Arg.val_imm, hsext1] using
              FullArenaTactics.c0_store_full_walk_vals _ hv2p1_lt hm3) fun m4 hm4 => ?_
          rw [wp_let_add64_2]
          refine wp_store_sep (by
            simpa only [Arg.val_var] using
              FullArenaTactics.c0_store_full_walk_best (p32.setWidth 8)
                (show v.toNat < _ by exact hv_wb) hm4) fun m5 hm5 => ?_
          rw [wp_let_add64_2, wp_jump]
          have hv1 : (v + 1).toNat = v.toNat + 1 := by bv_omega
          refine hJi _ (v + 1, ()) m5 hm5 (by dsimp only; rw [hv1]; omega) rfl
            ⟨hs2.core_ok, { hs2.scratch_ok with
              walk_vals_len := by simp [hwvl2], walk_best_len := by simp [hwbl2] }⟩
            ⟨by rw [hv1]; omega, hsb2, hll2, hel2⟩
        · c0_steps
          · exact hJp _ _ rfl
          · exact hJp _ _ rfl
      · intro _
        clear Ji hJi
        rw [wp_let_add64_2]
        refine wp_loop_break_group
          (fun ((_v : BitVec 64), (_best_unsat : BitVec 64), (_flip : BitVec 64), ()) m3 =>
            ∃ s3 : FullState, s3.LengthsOk c ∧
              s3.core = { s.core with fuel := s3.core.fuel } ∧
              s3.core.fuel.toNat ≤ s.core.fuel.toNat ∧
              s3.scratch.last_learned = s.scratch.last_learned ∧
              s3.scratch.extend_len = s.scratch.extend_len ∧
              (FullMem c s3 ⋆ R) m3)
          (fun k ((_v : BitVec 64), (_best_unsat : BitVec 64), (flip : BitVec 64), ()) m3 =>
            k = 256 - flip.toNat ∧ flip.toNat ≤ 256 ∧ ∃ s3 : FullState, s3.LengthsOk c ∧
              s3.core = { s.core with fuel := s3.core.fuel } ∧
              s3.core.fuel.toNat ≤ s.core.fuel.toNat ∧
              s3.scratch.scratch_buf = s1.scratch.scratch_buf ∧
              s3.scratch.last_learned = s.scratch.last_learned ∧
              s3.scratch.extend_len = s.scratch.extend_len ∧
              (FullMem c s3 ⋆ R) m3)
          (fun _ _ m3 ⟨s3, hs3, hcore3, hfuel3, hll3, hel3, hm3⟩ => ?_)
          (fun B L k (v_st, best_unsat, flip, ()) m3 hB hL ⟨hk, hflip_le, s3, hs3, hcore3, hfuel3,
              hsb3, hll3, hel3, hm3⟩ => ?_)
          (fun _ L _ hL => ?_)
        · clear hok1 hsb2 hll2 hel2
          rw [Blocks.get_here]
          refine wp_loop_safety_slice (fullSafetySlice c) s3 R (fun _ => True) trivial
            (fun s4 ((v1 : BitVec 64), ()) => v1.toNat ≤ s.core.cur_vars ∧
              s4.scratch.last_learned = s.scratch.last_learned ∧
              s4.scratch.extend_len = s.scratch.extend_len)
            (fun ((v1 : BitVec 64), ()) => s.core.cur_vars - v1.toNat)
            (fun Jf hJf => ?_)
            (fun Jf s4 ((v1 : BitVec 64), ()) m4 hcore4 hs4 _ ⟨hv1_le, hll4, hel4⟩ hm4
                hJf => ?_)
          · rw [wp_jump]; exact hJf s3 (0#64, ()) m3 hm3 rfl hs3 ⟨by simp, hll3, hel3⟩
          · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
              fullSafetySlice_safe] at hs4 hm4
            have heq4 := fullCoreState_agrees_with_scratch hcore4
            obtain hwbl4 := hs4.scratch_ok.walk_best_len
            obtain hphl4 := hs4.scratch_ok.phases_len
            obtain hcv_le4 := hs4.core_ok.cur_vars_le
            rw [Blocks.get_here]; dsimp only
            rw [wp_let_ult64_2]; refine wp_jnz_of ?_ ?_
            · intro hv1_lt_c
              simp only [Arg.val_var] at hv1_lt_c
              have hv1_lt : v1.toNat < s.core.cur_vars := by
                have h1 : v1.toNat < (BitVec.ofNat 64 s1.core.cur_vars).toNat := by
                  simpa [BitVec.ult] using hv1_lt_c
                rw [heq1, bv64_ofNat_toNat (by omega)] at h1; exact h1
              have hv1_wb : v1.toNat < s4.scratch.walk_best.length := by rw [hwbl4]; omega
              have hv1_ph : v1.toNat < s4.scratch.phases.length := by rw [hphl4]; omega
              rw [wp_let_add64_2, wp_let_add64_2]
              refine wp_load_of (by simpa only [Arg.val_var] using
                FullArenaTactics.c0_load_full_walk_best hv1_wb hm4) ?_
              refine wp_store_sep (by simpa only [Arg.val_var] using
                FullArenaTactics.c0_store_full_phases _ hv1_ph hm4) fun m5 hm5 => ?_
              rw [wp_let_add64_2, wp_jump]
              have hv11 : (v1 + 1).toNat = v1.toNat + 1 := by bv_omega
              exact hJf _ (v1 + 1, ()) m5 hm5 (by dsimp only; rw [hv11]; omega) rfl
                ⟨hs4.core_ok, { hs4.scratch_ok with phases_len := by simp [hphl4] }⟩
                ⟨by rw [hv11]; omega, hll4, hel4⟩
            · intro _; c0_steps
              have hfe :
                  FullState.mk { s.core with fuel := s4.core.fuel }
                    { s4.scratch with walk_cnt_stat := s4.scratch.walk_cnt_stat + 1 } =
                  { s4 with scratch := { s4.scratch with
                    walk_cnt_stat := s4.scratch.walk_cnt_stat + 1 } } := by
                cases s4; dsimp only at heq4 hcore3 ⊢; congr 1
                rw [heq4, hcore3]
              exact hQ s4.core.fuel
                { s4.scratch with walk_cnt_stat := s4.scratch.walk_cnt_stat + 1 } _
                (by
                  rw [hfe]
                  exact ⟨hs4.core_ok,
                    { hs4.scratch_ok with walk_vals_len := hs4.scratch_ok.walk_vals_len }⟩)
                (by rw [heq4, hcore3]; exact hfuel3)
                ⟨hll4, hel4⟩
                (by rw [hfe]; exact hm)
        · subst hk
          have hcv3 : s3.core.cur_vars = s.core.cur_vars := by rw [hcore3]
          have hare3 : s3.core.arena = s.core.arena := by rw [hcore3]
          have harl3 : s3.core.arena_len = s.core.arena_len := by rw [hcore3]
          have hok3 : FullWalkEntriesOk s3 ncl.toNat := by
            intro idx hidx
            have := hok1 idx hidx
            unfold FullWalkEntryOk at this ⊢
            dsimp only [fullArenaClauseRefs, fullArenaClauseRefsCore, fullArenaClauseGarb,
              fullArenaClauseGarbCore, fullArenaHdrCore] at this ⊢
            rw [hsb3, hcv3, hare3, harl3, ← heq1]; exact this
          have hfa3 : FullArenaClausesInv c F_cur s3.core := by
            rw [hcore3]; exact fullArenaClausesInv_with_fuel ha _
          rw [Blocks.get_here]; dsimp only
          rw [wp_let_ult64_2]; refine wp_jnz_of ?_ ?_
          · intro hflip_lt_c
            simp only [Arg.val_var, Arg.val_imm] at hflip_lt_c
            have hflip_lt : flip.toNat < 256 := by simpa [BitVec.ult] using hflip_lt_c
            rw [wp_let_add64_2]
            refine wp_load_of (by simpa only [Arg.val_var, Arg.val_imm] using
              FullArenaTactics.load_full_fuel hm3) ?_
            rw [wp_let_ugt64_2]; refine wp_jnz_of ?_ ?_
            · intro hfuel_gt_c
              simp only [Arg.val_var, Arg.val_imm] at hfuel_gt_c
              have hfuel_pos : 0 < s3.core.fuel.toNat := by simpa [BitVec.ult] using hfuel_gt_c
              have hfuel_sub : (s3.core.fuel - 1).toNat = s3.core.fuel.toNat - 1 := by bv_omega
              rw [wp_let_add64_2]
              refine wp_load_of (by simpa only [Arg.val_var, Arg.val_imm] using
                FullArenaTactics.load_full_fuel hm3) ?_
              rw [wp_let_sub64_2, wp_let_add64_2]
              refine wp_store_sep (by simpa only [Arg.val_var, Arg.val_imm] using
                FullArenaTactics.store_full_fuel _ hm3) fun m4 hm4 => ?_
              let s4 : FullState :=
                { s3 with core := { s3.core with fuel := s3.core.fuel - 1 } }
              have hs4 : s4.LengthsOk c :=
                ⟨{ hs3.core_ok with vals_len := hs3.core_ok.vals_len }, hs3.scratch_ok⟩
              have hcore4 : s4.core = { s.core with fuel := s4.core.fuel } := by
                simp only [s4]; rw [hcore3]
              have hfuel4 : s4.core.fuel.toNat ≤ s.core.fuel.toNat := by
                dsimp only [s4]; rw [hfuel_sub]; omega
              have hfa4 : FullArenaClausesInv c F_cur s4.core := by
                rw [hcore4]; exact fullArenaClausesInv_with_fuel ha _
              have hok4 : FullWalkEntriesOk s4 ncl.toNat := by
                intro idx hidx
                have := hok3 idx hidx
                unfold FullWalkEntryOk at this ⊢
                dsimp only [fullArenaClauseRefs, fullArenaClauseRefsCore, fullArenaClauseGarb,
                  fullArenaClauseGarbCore, fullArenaHdrCore] at this ⊢
                simpa [s4] using this
              refine wp_loop_safety_slice (fullSafetySlice c) s4 R (fun _ => True) trivial
                (fun s5 ((unsat_c : BitVec 64), (picked_idx : BitVec 64), (i : BitVec 64), ()) =>
                  i.toNat ≤ ncl.toNat ∧ unsat_c.toNat ≤ i.toNat ∧
                  picked_idx.toNat < ncl.toNat ∧
                  s5.scratch.scratch_buf = s1.scratch.scratch_buf ∧
                  s5.scratch.last_learned = s.scratch.last_learned ∧
                  s5.scratch.extend_len = s.scratch.extend_len)
                (fun (_, _, (i : BitVec 64), ()) => ncl.toNat - i.toNat)
                (fun Ji hJi => ?_)
                (fun Ji s5 ((unsat_c : BitVec 64), (picked_idx : BitVec 64), (i : BitVec 64), ())
                    m5 hcore5 hs5 _ ⟨hile, hus_le, hp_lt, hsb5, hll5, hel5⟩ hm5 hJi => ?_)
              · rw [wp_jump]
                exact hJi s4 (0#64, 0#64, 0#64, ()) m4 hm4 rfl hs4
                  ⟨by simp, by simp, hncl_pos, hsb3, hll3, hel3⟩
              · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
                  fullSafetySlice_safe] at hs5 hm5
                have heq5 := fullCoreState_agrees_with_scratch hcore5
                rw [Blocks.get_here]; dsimp only
                rw [wp_let_ult64_2]; refine wp_jnz_of ?_ ?_
                · intro hi_lt_c
                  simp only [Arg.val_var] at hi_lt_c
                  have hi_lt : i.toNat < ncl.toNat := by simpa [BitVec.ult] using hi_lt_c
                  have hok5 : FullWalkEntryOk s5 i.toNat := by
                    have := hok3 i.toNat hi_lt
                    unfold FullWalkEntryOk at this ⊢
                    dsimp only [fullArenaClauseRefs, fullArenaClauseRefsCore, fullArenaClauseGarb,
                      fullArenaClauseGarbCore, fullArenaHdrCore] at this ⊢
                    rw [hsb5, ← hsb3, heq5]; exact this
                  refine wp_join_safety_slice (fullSafetySlice c) s5 R (fun _ => True) trivial
                    (fun s7 ((unsat' : BitVec 64), (picked' : BitVec 64), ()) =>
                      unsat'.toNat ≤ i.toNat + 1 ∧ picked'.toNat < ncl.toNat ∧
                      s7.scratch.scratch_buf = s1.scratch.scratch_buf ∧
                      s7.scratch.last_learned = s.scratch.last_learned ∧
                      s7.scratch.extend_len = s.scratch.extend_len)
                    (fun Js s7 ((unsat' : BitVec 64), (picked' : BitVec 64), ())
                        m7 hcore7 hs7 _ ⟨hus', hp', hsb7, hll7, hel7⟩ hm7 => ?_)
                    (fun Js hJs => ?_)
                  · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
                      fullSafetySlice_safe] at hs7 hm7
                    rw [Blocks.get_here]; dsimp only
                    rw [wp_let_add64_2, wp_jump]
                    have hi1 : (i + 1).toNat = i.toNat + 1 := by bv_omega
                    exact hJi s7 (unsat', picked', i + 1, ()) m7 hm7
                      (by dsimp only; rw [hi1]; omega) hcore7 hs7
                      ⟨by rw [hi1]; omega, by rw [hi1]; omega, hp', hsb7, hll7, hel7⟩
                  · have hinv5 : FullCoreInv c F0 s5 := by
                      have hs5_eq : s5 = { core := { s.core with fuel := s5.core.fuel }
                                           scratch := s5.scratch } := by
                        cases s5; dsimp only at heq5 hcore4 ⊢; congr 1; rw [heq5, hcore4]
                      rw [hs5_eq]; exact hinv.walkExt_with_fuel_scratch hs5.scratch_ok
                    c0_call hClSat
                    refine ⟨c, s5, R, ⟨rfl, rfl, ⟨F0, hinv5⟩, by omega, hok5⟩, hs5, hm5, ?_⟩
                    intro ⟨sat, ⟨⟩⟩ s6 m6 hcore6 hs6 heq6 hm6
                    subst s6
                    refine wp_jnz_of ?_ ?_
                    · intro _; rw [wp_jump]
                      exact hJs s5 (unsat_c, picked_idx, ()) m6 hm6 rfl hs5
                        ⟨by omega, hp_lt, hsb5, hll5, hel5⟩
                    · intro _
                      have hus_pos : 0 < (unsat_c + 1).toNat := by bv_omega
                      have hus1_le : (unsat_c + 1).toNat ≤ i.toNat + 1 := by bv_omega
                      try rw [wp_let_add64_2]
                      refine wp_join_safety_slice (fullSafetySlice c) s5 R (fun _ => True) trivial
                        (fun s6 ((picked' : BitVec 64), ()) =>
                          picked'.toNat < ncl.toNat ∧
                          s6.scratch.scratch_buf = s1.scratch.scratch_buf ∧
                          s6.scratch.last_learned = s.scratch.last_learned ∧
                          s6.scratch.extend_len = s.scratch.extend_len)
                        (fun Jp s6 ((picked' : BitVec 64), ()) m6 hcore6 hs6 _
                            ⟨hp', hsb6, hll6, hel6⟩ hm6 => ?_)
                        (fun Jp hJp => ?_)
                      · rw [Blocks.get_here]; dsimp only
                        try rw [wp_let_add64_2]
                        rw [wp_jump]
                        exact hJs s6 (unsat_c + 1, picked', ()) m6 hm6 hcore6 hs6
                          ⟨hus1_le, hp', hsb6, hll6, hel6⟩
                      · c0_call hRng
                        refine ⟨c, s5, R, rfl, hs5, hm6, ?_⟩
                        intro ⟨rngr, ⟨⟩⟩ s6 m6 hcore6 hs6 hsc6 hm6
                        dsimp only
                        try rw [wp_let_add64_2]
                        rw [wp_let_urem64_2 (by simp only [Arg.val_var]; bv_omega),
                          wp_let_eq64_2]
                        refine wp_jnz_of ?_ ?_
                        · intro _; rw [wp_jump]
                          exact hJp s6 (i, ()) m6 hm6 hcore6 hs6
                            ⟨hi_lt, by rw [hsc6]; exact hsb5,
                              by rw [hsc6]; exact hll5, by rw [hsc6]; exact hel5⟩
                        · intro _; rw [wp_jump]
                          exact hJp s6 (picked_idx, ()) m6 hm6 hcore6 hs6
                            ⟨hp_lt, by rw [hsc6]; exact hsb5,
                              by rw [hsc6]; exact hll5, by rw [hsc6]; exact hel5⟩
                · intro _
                  clear Ji hJi
                  refine wp_join_safety_slice (fullSafetySlice c) s5 R (fun _ => True) trivial
                    (fun s6 ((_v' : BitVec 64), (_best' : BitVec 64), ()) =>
                      s6.scratch.scratch_buf = s1.scratch.scratch_buf ∧
                      s6.scratch.last_learned = s.scratch.last_learned ∧
                      s6.scratch.extend_len = s.scratch.extend_len)
                    (fun Jb s6 ((v' : BitVec 64), (best' : BitVec 64), ()) m6 hcore6 hs6 _
                        ⟨hsb6, hll6, hel6⟩ hm6 => ?_)
                    (fun Jb hJb => ?_)
                  · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
                      fullSafetySlice_safe] at hs6 hm6
                    have heq6 := fullCoreState_agrees_with_scratch hcore6
                    have hcore6' : s6.core = { s.core with fuel := s6.core.fuel } := by
                      rw [heq6, heq5, hcore4]
                    have hfuel6 : s6.core.fuel.toNat ≤ s.core.fuel.toNat := by
                      rw [heq6, heq5]; exact hfuel4
                    rw [Blocks.get_here]; dsimp only
                    try rw [wp_let_eq64_2]
                    refine wp_jnz_of ?_ ?_
                    · intro _; rw [wp_jump]
                      exact hB (v', best', flip, ()) m6
                        ⟨s6, hs6, hcore6', hfuel6, hll6, hel6, hm6⟩
                    · intro _
                      have hok6 : FullWalkEntryOk s6 picked_idx.toNat := by
                        have := hok3 picked_idx.toNat hp_lt
                        unfold FullWalkEntryOk at this ⊢
                        dsimp only [fullArenaClauseRefs, fullArenaClauseRefsCore,
                          fullArenaClauseGarb, fullArenaClauseGarbCore, fullArenaHdrCore] at this ⊢
                        rw [hsb6, ← hsb3, heq6, heq5]; exact this
                      have hinv6 : FullCoreInv c F0 s6 := by
                        have hs6_eq : s6 = { core := { s.core with fuel := s6.core.fuel }
                                             scratch := s6.scratch } := by
                          cases s6; dsimp only at hcore6' ⊢; congr 1
                        rw [hs6_eq]; exact hinv.walkExt_with_fuel_scratch hs6.scratch_ok
                      c0_call hPick
                      refine ⟨c, s6, R, ⟨rfl, rfl, ⟨F0, hinv6⟩, by omega, hok6⟩, hs6, hm6, ?_⟩
                      intro ⟨lit, ⟨⟩⟩ s7 m7 hcore7 hs7 ⟨⟨hll7', hel7'⟩, hsb7', hlit_dom⟩ hm7
                      have heq7 := fullCoreState_agrees_with_scratch hcore7
                      have hcore7' : s7.core = { s.core with fuel := s7.core.fuel } := by
                        rw [heq7, hcore6']
                      have hfuel7 : s7.core.fuel.toNat ≤ s.core.fuel.toNat := by
                        rw [heq7]; exact hfuel6
                      have hsb7 : s7.scratch.scratch_buf = s1.scratch.scratch_buf :=
                        hsb7'.trans hsb6
                      have hll7 : s7.scratch.last_learned = s.scratch.last_learned :=
                        hll7'.trans hll6
                      have hel7 : s7.scratch.extend_len = s.scratch.extend_len :=
                        hel7'.trans hel6
                      try rw [wp_let_eq32_2]
                      refine wp_jnz_of ?_ ?_
                      · intro _; rw [wp_jump]
                        exact hB (v', best', flip, ()) m7
                          ⟨s7, hs7, hcore7', hfuel7, hll7, hel7, hm7⟩
                      · intro hlit_ne
                        have hlit_lt : lit.toNat < 2 * s.core.cur_vars := by
                          simp only [Arg.val_var, beq_eq_false_iff_ne] at hlit_ne
                          rcases hlit_dom with rfl | hl
                          · exact absurd rfl hlit_ne
                          · rw [heq6, heq5, hcore4] at hl; exact hl
                        have hcv_le7 := hs7.core_ok.cur_vars_le
                        have hwvl7 := hs7.scratch_ok.walk_vals_len
                        have hlv_lt : (lit >>> (1 : Nat)).toNat < s.core.cur_vars := by
                          rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
                        have hlv2 : ((lit >>> (1 : Nat)).setWidth 64 <<< (1 : Nat)).toNat =
                            2 * (lit >>> (1 : Nat)).toNat := by
                          rw [BitVec.toNat_shiftLeft, zext_toNat _ (by decide)]
                          simp [Nat.shiftLeft_eq]; omega
                        have hlv2_lt : ((lit >>> (1 : Nat)).setWidth 64 <<< (1 : Nat)).toNat <
                            s7.scratch.walk_vals.length := by rw [hwvl7, hlv2]; omega
                        rw [wp_let_lshr32_2]
                        refine wp_join_group
                          (fun ((nv32 : BitVec 32), ()) m7' => m7' = m7)
                          (fun Jn ((nv32 : BitVec 32), ()) m7' hm7' => ?_) (fun Jn hJn => ?_)
                        · subst m7'
                          have hlv2p1_lt :
                              (((lit >>> (1 : Nat)).setWidth 64 <<< (1 : Nat)) + 1).toNat <
                              (s7.scratch.walk_vals.set
                                ((lit >>> (1 : Nat)).setWidth 64 <<< (1 : Nat)).toNat
                                  (nv32.setWidth 8)).length := by
                            rw [List.length_set, hwvl7, BitVec.toNat_add, hlv2]; simp; omega
                          have hsext1 : (BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64 = 1 := rfl
                          have hlshr1 : (1 : BitVec 32).toNat % 32 = 1 := rfl
                          rw [Blocks.get_here]; dsimp only
                          repeat (first
                            | rw [wp_let_trunc32_8_2] | rw [wp_let_sext8_32_2]
                            | rw [wp_let_neg32_2] | rw [wp_let_zext32_2] | rw [wp_let_sext32_64_2]
                            | rw [wp_let_shl64_2] | rw [wp_let_add64_2])
                          refine wp_store_sep (by
                            simpa only [Arg.val_var, Arg.val_imm, hsext1, hlshr1] using
                              FullArenaTactics.c0_store_full_walk_vals
                                (nv32.setWidth 8) hlv2_lt hm7) fun m8 hm8 => ?_
                          repeat (first
                            | rw [wp_let_trunc32_8_2] | rw [wp_let_sext8_32_2]
                            | rw [wp_let_neg32_2] | rw [wp_let_zext32_2] | rw [wp_let_sext32_64_2]
                            | rw [wp_let_shl64_2] | rw [wp_let_add64_2])
                          refine wp_store_sep (by
                            simpa only [Arg.val_var, Arg.val_imm, hsext1, hlshr1] using
                              FullArenaTactics.c0_store_full_walk_vals
                                _ hlv2p1_lt hm8) fun m9 hm9 => ?_
                          rw [wp_let_add64_2, wp_jump]
                          have hflip1 : (flip + 1).toNat = flip.toNat + 1 := by bv_omega
                          refine hL (256 - (flip + 1).toNat) (v', best', flip + 1, ()) m9
                            (by rw [hflip1]; omega)
                            ⟨rfl, by rw [hflip1]; omega, _, ?_, ?_, ?_, ?_, ?_, ?_, hm9⟩
                          · exact ⟨hs7.core_ok, { hs7.scratch_ok with
                              walk_vals_len := by simp [hwvl7] }⟩
                          · exact hcore7'
                          · exact hfuel7
                          · exact hsb7
                          · exact hll7
                          · exact hel7
                        · have hsext1 : (BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64 = 1 := rfl
                          have hlshr1 : (1 : BitVec 32).toNat % 32 = 1 := rfl
                          repeat (first
                            | rw [wp_let_zext32_2] | rw [wp_let_sext32_64_2]
                            | rw [wp_let_shl64_2] | rw [wp_let_add64_2])
                          refine wp_load_of (by
                            simpa only [Arg.val_var, Arg.val_imm, hsext1, hlshr1] using
                              FullArenaTactics.c0_load_full_walk_vals hlv2_lt hm7) ?_
                          c0_steps
                          · exact hJn _ _ rfl
                          · exact hJn _ _ rfl
                  · rw [wp_let_ult64_2]; refine wp_jnz_of ?_ ?_
                    · intro _
                      refine wp_loop_safety_slice (fullSafetySlice c) s5 R (fun _ => True) trivial
                        (fun s6 ((v1 : BitVec 64), ()) => v1.toNat ≤ s.core.cur_vars ∧
                          s6.scratch.scratch_buf = s1.scratch.scratch_buf ∧
                          s6.scratch.last_learned = s.scratch.last_learned ∧
                          s6.scratch.extend_len = s.scratch.extend_len)
                        (fun ((v1 : BitVec 64), ()) => s.core.cur_vars - v1.toNat)
                        (fun Jc hJc => ?_)
                        (fun Jc s6 ((v1 : BitVec 64), ()) m6 hcore6 hs6 _
                            ⟨hv1_le, hsb6, hll6, hel6⟩ hm6 hJc => ?_)
                      · rw [wp_jump]
                        exact hJc s5 (0#64, ()) m5 hm5 rfl hs5 ⟨by simp, hsb5, hll5, hel5⟩
                      · dsimp only [fullSafetySlice_mem, fullSafetySlice_coreProj,
                          fullSafetySlice_safe] at hs6 hm6
                        have heq6 := fullCoreState_agrees_with_scratch hcore6
                        obtain hcv_le6 := hs6.core_ok.cur_vars_le
                        obtain hwvl6 := hs6.scratch_ok.walk_vals_len
                        obtain hwbl6 := hs6.scratch_ok.walk_best_len
                        rw [Blocks.get_here]; dsimp only
                        rw [wp_let_ult64_2]; refine wp_jnz_of ?_ ?_
                        · intro hv1_lt_c
                          simp only [Arg.val_var] at hv1_lt_c
                          have hv1_lt : v1.toNat < s.core.cur_vars := by
                            have h1 : v1.toNat < (BitVec.ofNat 64 s1.core.cur_vars).toNat := by
                              simpa [BitVec.ult] using hv1_lt_c
                            rw [heq1, bv64_ofNat_toNat (by omega)] at h1; exact h1
                          have hv12 : (v1 <<< (1 : Nat)).toNat = 2 * v1.toNat := by
                            rw [BitVec.toNat_shiftLeft]; simp [Nat.shiftLeft_eq]; omega
                          have hv12_lt : (v1 <<< (1 : Nat)).toNat <
                              s6.scratch.walk_vals.length := by rw [hwvl6, hv12]; omega
                          have hv1_wb : v1.toNat < s6.scratch.walk_best.length := by
                            rw [hwbl6]; omega
                          have hsext1 : (BitVec.signExtend 64 (1 : BitVec 32)).toNat % 64 = 1 := rfl
                          repeat (first
                            | rw [wp_let_sext32_64_2] | rw [wp_let_shl64_2] | rw [wp_let_add64_2])
                          refine wp_load_of (by
                            simpa only [Arg.val_var, Arg.val_imm, hsext1] using
                              FullArenaTactics.c0_load_full_walk_vals hv12_lt hm6) ?_
                          refine wp_store_sep (by
                            simpa only [Arg.val_var] using
                              FullArenaTactics.c0_store_full_walk_best _ hv1_wb hm6)
                            fun m7 hm7 => ?_
                          rw [wp_let_add64_2, wp_jump]
                          have hv11 : (v1 + 1).toNat = v1.toNat + 1 := by bv_omega
                          exact hJc _ (v1 + 1, ()) m7 hm7
                            (by dsimp only; rw [hv11]; omega) rfl
                            ⟨hs6.core_ok, { hs6.scratch_ok with
                              walk_best_len := by simp [hwbl6] }⟩
                            ⟨by rw [hv11]; omega, hsb6, hll6, hel6⟩
                        · intro _; rw [wp_jump]
                          exact hJb s6 (v1, unsat_c, ()) m6 hm6 hcore6 hs6 ⟨hsb6, hll6, hel6⟩
                    · intro _; rw [wp_jump]
                      exact hJb s5 (v_st, best_unsat, ()) m5 hm5 rfl hs5 ⟨hsb5, hll5, hel5⟩
            · intro _; rw [wp_jump]
              exact hB (v_st, best_unsat, flip, ()) m3
                ⟨s3, hs3, hcore3, hfuel3, hll3, hel3, hm3⟩
          · intro _; rw [wp_jump]
            exact hB (v_st, best_unsat, flip, ()) m3
              ⟨s3, hs3, hcore3, hfuel3, hll3, hel3, hm3⟩
        · rw [wp_jump]
          exact hL (256 - 0) _ _ ⟨rfl, by simp, s2, hs2,
            by rw [heq2], by rw [heq2]; exact Nat.le_refl _, hsb2, hll2, hel2, hm2⟩
