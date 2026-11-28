/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Factor
public import LeanQbe.T.Examples.Kissat.Proof.Factor.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Factor.Helpers
public import LeanQbe.T.Examples.Kissat.Proof.Factor.Wp0
public import LeanQbe.T.Examples.Kissat.Proof.Factor.WpCommit0
public import LeanQbe.T.Examples.Kissat.Proof.Factor.WpCommit1
public import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts3
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts4
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# BVA Commit Phase 2 WP (`Proof.Factor.WpCommit2`)

Zero-legacy (`0` `Full*` imports, `0` placeholders, `XPost`-polymorphic) Phase 2 WP proofs for
`full_bva_commit`:
1. Pure list/entailment & `u64` copy-step lemmas (`cmt_nodup_lt_le`, `cmt_tmp_build_ok`,
   `cmt_u64_copy_step`).
2. `cmt_phase2_large_tail_wp`: `u64`/`u32` copy loop, `cmt_fullDenseInvW_addClause`,
   `full_watch_push` loop + `full_unwatch_large` / `PH_GARB` rollback + `irred_add`.
3. `cmt_phase2_wp`: Phase 2 loop adding `[2*fv+1, q]` binaries and `[2*fv+1, C \ {flit}]` large
   clauses.
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

@[local bv_c0] private theorem cmt2_bv64_one : (1 : BitVec 64).toNat = 1 := rfl
@[local bv_c0] private theorem cmt2_bv64_two : (2 : BitVec 64).toNat = 2 := rfl
@[local bv_c0] private theorem cmt2_bv64_three : (3 : BitVec 64).toNat = 3 := rfl
@[local bv_c0] private theorem cmt2_bv32_one : (1 : BitVec 32).toNat = 1 := rfl
@[local bv_c0] private theorem cmt2_bv32_two : (2 : BitVec 32).toNat = 2 := rfl
@[local bv_c0] private theorem cmt2_bv32_three : (3 : BitVec 32).toNat = 3 := rfl

private theorem cmt2_getElem_eq {α : Type} {xs : List α} {i j : Nat}
    {hi : i < xs.length} {hj : j < xs.length} (h : i = j) : xs[i]'hi = xs[j]'hj := by
  subst h; rfl

private theorem cmt_store_arena_i32 {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {i : BitVec 64} (v : BitVec 32) (hi : i.toNat < s.core.arena.length)
    (hm : (FullMem c s ⋆ R) m) :
    storeOk m i32 (c.pArena + i * 4) ∧
      (FullMem c { s with core := { s.core with arena := s.core.arena.set i.toNat v } } ⋆ R)
        (storeMem m i32 (c.pArena + i * 4) v) := by
  have haddr : c.pArena + i * 4 = c.pArena + BitVec.ofNat 64 (4 * i.toNat) := by
    rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
  rw [haddr]
  obtain ⟨hok, hst⟩ := store_array (t := i32) v (by decide) hi (ArrayField.arena.focus hm)
  exact ⟨hok, ArrayField.arena.unfocus hst⟩

/-! ## 1. Pure List, Entailment & AST Helpers -/

private theorem cmt_mem_erase_ne :
    ∀ {xs : List Nat} {x n : Nat}, xs.Nodup → x ∈ xs.erase n → x ≠ n ∧ x ∈ xs
  | [], _, _, _, h => by simp at h
  | a :: rest, x, n, hnd, hx => by
    rw [List.nodup_cons] at hnd
    by_cases han : a = n
    · subst han; simp only [List.erase_cons_head] at hx
      exact ⟨fun h => hnd.1 (h ▸ hx), List.mem_cons_of_mem _ hx⟩
    · simp only [List.erase_cons_tail (by simp [han] : ¬ (a == n) = true), List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact ⟨han, List.mem_cons_self⟩
      · obtain ⟨hne, hmem⟩ := cmt_mem_erase_ne hnd.2 hx
        exact ⟨hne, List.mem_cons_of_mem _ hmem⟩

private theorem cmt_nodup_lt_le :
    ∀ {n : Nat} {xs : List Nat}, xs.Nodup → (∀ x ∈ xs, x < n) → xs.length ≤ n
  | 0, [], _, _ => Nat.zero_le _
  | 0, a :: _, _, h => absurd (h a List.mem_cons_self) (Nat.not_lt_zero _)
  | n + 1, xs, hnd, h => by
    by_cases hn : n ∈ xs
    · have hnd' : (xs.erase n).Nodup := hnd.erase n
      have h' : ∀ x ∈ xs.erase n, x < n := fun x hx => by
        obtain ⟨hne, hmem⟩ := cmt_mem_erase_ne hnd hx
        have h2 := h x hmem
        omega
      have hih := cmt_nodup_lt_le hnd' h'
      have hl := List.length_erase_of_mem hn
      omega
    · have h' : ∀ x ∈ xs, x < n := fun x hx => by
        have h1 := h x hx
        have hne : x ≠ n := fun heq => hn (heq ▸ hx)
        omega
      exact Nat.le_trans (cmt_nodup_lt_le hnd h') (Nat.le_succ _)

private theorem cmt_entails_of_perm {F : List (List Nat)} {c1 c2 : List Nat}
    (hp : c1.Perm c2) (he : (cnfOfClauses F).EntailsClause (cnfClause c1)) :
    (cnfOfClauses F).EntailsClause (cnfClause c2) := by
  rw [CNF.entails_clause_def] at he ⊢
  intro α hα
  obtain ⟨l, hl, hev⟩ := (clause_sat_cnfClause_iff α c1).mp (he α hα)
  exact (clause_sat_cnfClause_iff α c2).mpr ⟨l, hp.mem_iff.mp hl, hev⟩

private theorem cmt_take_set_succ {α : Type} (xs : List α) {k : Nat} (v : α)
    (hk : k < xs.length) : (xs.set k v).take (k + 1) = xs.take k ++ [v] := by
  have hk' : k < (xs.set k v).length := by rw [List.length_set]; exact hk
  rw [List.take_succ_eq_append_getElem hk', List.take_set_of_le (Nat.le_refl _),
    List.getElem_set_self]

private theorem cmt_filter_take_succ {α : Type} (p : α → Bool) (xs : List α) {j : Nat}
    (hj : j < xs.length) :
    (xs.take (j + 1)).filter p =
      (xs.take j).filter p ++ (if p (xs[j]'hj) then [xs[j]'hj] else []) := by
  rw [List.take_succ_eq_append_getElem hj, List.filter_append]
  by_cases hp : p (xs[j]'hj) = true <;> simp [hp]

private theorem cmt_tmp_build_ok {c : FullCfg} {F_next : List (List Nat)}
    {s0 : FullState} {c_top : BitVec 32} {flit : Nat} {res : List Nat}
    {tmp : List (BitVec 32)} {tk : Nat}
    (hcv_lt : s0.core.cur_vars < c.max_vars)
    (hres_lt : ∀ x ∈ res, x < 2 * s0.core.cur_vars)
    (hres_nd : (res.map (· / 2)).Nodup)
    (hres_ent : (cnfOfClauses F_next).EntailsClause
      (cnfClause ((2 * s0.core.cur_vars + 1) :: res)))
    (hge3 : 3 ≤ fullArenaClauseSize s0 c_top.toNat)
    (hbd : c_top.toNat + 3 + fullArenaClauseSize s0 c_top.toNat ≤ s0.core.arena.length)
    (hperm_f : res.Perm ((fullArenaClauseLits s0 c_top.toNat).filter (· != flit)))
    (hperm_c : (fullArenaClauseLits s0 c_top.toNat).Perm (flit :: res))
    (htmp_l : tmp.length = c.max_vars)
    (htk_eq : tk = 1 + ((fullArenaClauseLits s0 c_top.toNat).filter (· != flit)).length)
    (htmp_eq : (tmp.take tk).map BitVec.toNat =
      (2 * s0.core.cur_vars + 1) :: ((fullArenaClauseLits s0 c_top.toNat).filter (· != flit))) :
    3 ≤ tk ∧ tk ≤ c.max_vars ∧
    (∀ l ∈ (tmp.take tk).map BitVec.toNat, l < 2 * (s0.core.cur_vars + 1)) ∧
    ((tmp.take tk).map fun x => x.toNat / 2).Nodup ∧
    (cnfOfClauses F_next).EntailsClause (cnfClause ((tmp.take tk).map BitVec.toNat)) := by
  have hlen_f : ((fullArenaClauseLits s0 c_top.toNat).filter (· != flit)).length = res.length :=
    hperm_f.symm.length_eq
  have hlen_c : (fullArenaClauseLits s0 c_top.toNat).length = 1 + res.length := by
    have := hperm_c.length_eq; simp only [List.length_cons] at this; omega
  have hsz_eq :
      (fullArenaClauseLits s0 c_top.toNat).length = fullArenaClauseSize s0 c_top.toNat := by
    unfold fullArenaClauseSize at hbd
    unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSize
    simp only [List.length_map, List.length_take, List.length_drop]; omega
  have hres_len : res.length ≤ s0.core.cur_vars :=
    (List.length_map (f := (· / 2))).symm ▸
      cmt_nodup_lt_le hres_nd (fun v hv => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv; have := hres_lt x hx; omega)
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · intro l hl; rw [htmp_eq, List.mem_cons] at hl
    rcases hl with rfl | hl
    · omega
    · have := hres_lt l (hperm_f.mem_iff.mpr hl); omega
  · have hmap : ((tmp.take tk).map fun x => x.toNat / 2) =
        ((tmp.take tk).map BitVec.toNat).map (· / 2) := by rw [List.map_map]; rfl
    rw [hmap, htmp_eq, List.map_cons, List.nodup_cons]
    refine ⟨?_, (hperm_f.map (· / 2)).nodup hres_nd⟩
    intro hmem
    obtain ⟨x, hx, hdiv⟩ := List.mem_map.mp hmem
    have := hres_lt x (hperm_f.mem_iff.mpr hx); omega
  · rw [htmp_eq]
    exact cmt_entails_of_perm (List.Perm.cons _ hperm_f) hres_ent

private theorem cmt_u64_copy_step {ar tmp : List (BitVec 32)} {ncr j tk : Nat}
    (hj2 : j + 2 ≤ tk) (hbd : ncr + 3 + tk ≤ ar.length) (htmp_bd : tk ≤ tmp.length)
    (hcop : ∀ k < j, ar[ncr + 3 + k]? = tmp[k]?) :
    let v := cmtPackPair64 (tmp[j]'(by omega)) (tmp[j + 1]'(by omega))
    let ar' := (ar.set (ncr + 3 + j) (v.setWidth 32)).set (ncr + 3 + j + 1) ((v >>> 32).setWidth 32)
    ar'.length = ar.length ∧
    (∀ i < ncr + 3, ar'[i]? = ar[i]?) ∧
    (∀ k < j + 2, ar'[ncr + 3 + k]? = tmp[k]?) := by
  intro v ar'
  have hlo : v.setWidth 32 = tmp[j]'(by omega) := cmtPackPair64_lo _ _
  have hhi : (v >>> 32).setWidth 32 = tmp[j + 1]'(by omega) := cmtPackPair64_hi _ _
  refine ⟨by simp [ar'], fun i hi => by
    dsimp only [ar']; rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)],
    fun k hk => ?_⟩
  dsimp only [ar']; rw [hlo, hhi]
  rcases Nat.lt_or_ge k j with hkj | hkj
  · rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega)]; exact hcop k hkj
  · rcases Nat.eq_or_lt_of_le hkj with rfl | hgt
    · rw [List.getElem?_set_ne (by omega),
        List.getElem?_set_self (by omega), List.getElem?_eq_getElem (by omega)]
    · have hk1 : k = j + 1 := by omega
      subst hk1
      rw [show ncr + 3 + (j + 1) = ncr + 3 + j + 1 from by omega,
        List.getElem?_set_self (by rw [List.length_set]; omega),
        List.getElem?_eq_getElem (by omega)]

private inductive CmtNavOp where
  | step
  | ld32 (v : Val i32)
  | st32
  | call64 (v : Val i64)
  | brT
  | brF
  | grpB5 (v : Tup Val [i32, .bool, .bool, i64, i64])
  | grpK4 (J : Cont [.bool, .bool, i64, i64])
  | grpB1b (v : Bool)
  | grpB2_32 (v : Tup Val [i32, i32])

private def cmtNav : List CmtNavOp → Expr Val Cont [.bool] → Expr Val Cont [.bool]
  | [], e => e
  | .step :: rest, .let_ (Op.mk (.add (.bits 32)) args) k =>
      cmtNav rest (k (args.1.val + args.2.1.val, ()))
  | .step :: rest, .let_ (ts := ts) _ k => cmtNav rest (k (cmtDummyTup ts))
  | .ld32 v :: rest, .load (.bits 32) _ k => cmtNav rest (k v)
  | .st32 :: rest, .store (t := .bits 32) _ _ k => cmtNav rest k
  | .call64 v :: rest, .call (bs := [.bits 64]) _ _ k => cmtNav rest (k (v, ()))
  | .brT :: rest, .jnz _ t _ => cmtNav rest t
  | .brF :: rest, .jnz _ _ e => cmtNav rest e
  | .grpB5 v :: rest, .group (sig := [[.bits 32, .bool, .bool, .bits 64, .bits 64]]) bs _ =>
      match bs ((fun _ _ => False), ()) with | .cons f .nil => cmtNav rest (f v)
  | .grpK4 J :: rest, .group (sig := [[.bool, .bool, .bits 64, .bits 64]]) _ k =>
      cmtNav rest (k (J, ()))
  | .grpB1b v :: rest, .group (sig := [[.bool]]) bs _ =>
      match bs ((fun _ _ => False), ()) with | .cons f .nil => cmtNav rest (f (v, ()))
  | .grpB2_32 v :: rest, .group (sig := [[.bits 32, .bits 32]]) bs _ =>
      match bs ((fun _ _ => False), ()) with | .cons f .nil => cmtNav rest (f v)
  | _ :: _, _ => .hlt

private def cmtP2LargeTailExpr (h64 : Val i64) (best_k sc : Val i32)
    (pAr pScr pCnt pFl pWv : Val i64) (brow_off mn : Val i32)
    (dd0 : Bool) (cv64 pDeg pTmp : Val i64) (si : Val i32) (dd1 ok1 : Bool)
    (J_p2 : Cont [i32, .bool, .bool, i64, i64])
    (mi : Val i32) (dd ok : Bool) (ga ir : Val i64) (c_top : Val i32)
    (Jbr : Cont [.bool, .bool, i64, i64]) (csz flit : Val i32) (dd_a : Bool)
    (tk j : Val i32) (ncr64 : Val i64) : Expr Val Cont [.bool] :=
  cmtNav
    [.grpB5 (mi, dd, ok, ga, ir, ()), .step, .brT, .brT,
     .step, .step, .step, .step, .ld32 c_top, .grpK4 Jbr, .step, .step, .brF,
     .step, .step, .step, .step, .ld32 csz, .step, .step, .step, .ld32 flit,
     .grpB1b dd_a, .step, .step, .step, .step, .st32, .grpB2_32 (tk, j, ()),
     .step, .brF, .call64 ncr64, .step, .brF]
    (cmtP2GrpExpr h64 best_k sc pAr pScr pCnt pFl pWv brow_off mn dd0 cv64 pDeg pTmp si dd1 ok1
      |> cmtGrpK5 J_p2)

/-! ## 2. Phase 2 Large-Clause Copy, Watch-Push & Rollback WP -/

private theorem cmt_phase2_large_tail_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hWatchPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hUnwatch : ∀ a m Q X, fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_next : List (List Nat)} {s0 sm_t : FullState}
    {R : Mem 64 → Prop} {best_k sc brow_off mn si mi c_top csz flit tk j : Val i32}
    {dd0 dd1 ok1 dd ok dd_a : Bool} {cv64 ga ir : Val i64}
    {J_p2 : Cont [i32, .bool, .bool, i64, i64]} {Jbr : Cont [.bool, .bool, i64, i64]}
    {ar_a : List (BitVec 32)} {ma : Mem 64}
    (hinv_t : FullDenseInvW c F0 F_next sm_t) (hext_t : CommitArenaExt s0 sm_t)
    (hcv_t : sm_t.core.cur_vars = s0.core.cur_vars + 1)
    (hsb_t : sm_t.scratch.scratch_buf = s0.scratch.scratch_buf)
    (hrs_t : sm_t.scratch.res_sz = BitVec.ofNat 64 best_k.toNat)
    (hfl_t : sm_t.core.fuel = s0.core.fuel)
    (htm_t : sm_t.scratch.tarjan_mark = s0.scratch.tarjan_mark)
    (htr_t : sm_t.scratch.tarjan_reach = s0.scratch.tarjan_reach)
    (htk_ge3 : 3 ≤ tk.toNat) (htk_le_mx : tk.toNat ≤ c.max_vars)
    (htmp_lits_lt : ∀ l ∈ (sm_t.core.tmp.take tk.toNat).map BitVec.toNat,
      l < 2 * (s0.core.cur_vars + 1))
    (htmp_lits_nd : ((sm_t.core.tmp.take tk.toNat).map fun x => x.toNat / 2).Nodup)
    (htmp_lits_ent : (cnfOfClauses F_next).EntailsClause
      (cnfClause ((sm_t.core.tmp.take tk.toNat).map BitVec.toNat)))
    (hal_a_eq : ar_a.length = c.arena_cap)
    (hbd_a : sm_t.core.arena_len + 3 + tk.toNat ≤ c.arena_cap)
    (hhold_a : ∀ i < sm_t.core.arena_len, ar_a[i]? = sm_t.core.arena[i]?)
    (hnoshrk_a : (ar_a[sm_t.core.arena_len]?.getD 0#32 &&& 0x00800000#32) = 0#32)
    (hnogarb_a : (ar_a[sm_t.core.arena_len]?.getD 0#32 &&& 0x00080000#32) = 0#32)
    (hsz_a : (ar_a[sm_t.core.arena_len + 2]?.getD 0#32).toNat = tk.toNat)
    (hma : (FullMem c { sm_t with
      core := { sm_t.core with arena := ar_a,
                               arena_len := sm_t.core.arena_len + 3 + tk.toNat } } ⋆ R) ma)
    (hJbr : ∀ (dd' ok' : Bool) (ga' ir' : BitVec 64) (sm' : FullState) (mm' : Mem 64),
      FullDenseInvW c F0 F_next sm' → CommitArenaExt s0 sm' →
      sm'.core.cur_vars = s0.core.cur_vars + 1 →
      sm'.scratch.scratch_buf = s0.scratch.scratch_buf →
      sm'.scratch.res_sz = BitVec.ofNat 64 best_k.toNat →
      sm'.core.fuel = s0.core.fuel →
      sm'.scratch.tarjan_mark = s0.scratch.tarjan_mark →
      sm'.scratch.tarjan_reach = s0.scratch.tarjan_reach →
      (FullMem c sm' ⋆ R) mm' → Jbr (dd', ok', ga', ir', ()) mm') :
    wp Γ Q X (cmtP2LargeTailExpr c.hdr best_k sc c.pArena c.pScratchBuf c.pWsort c.pFlags
      c.pWvec brow_off mn dd0 cv64 c.pRepr c.pTmp si dd1 ok1 J_p2 mi dd ok ga ir c_top Jbr
      csz flit dd_a tk j (BitVec.ofNat 64 sm_t.core.arena_len)) ma := by
  have har_b := c.harena; have hmx := c.hmaxv; unfold dimacsBound at *
  have htmp_l := hinv_t.1.core_ok.tmp_len_arr
  let tmp_j := sm_t.core.tmp
  have htmp_jl : tmp_j.length = c.max_vars := htmp_l
  let ncr64 := BitVec.ofNat 64 sm_t.core.arena_len
  have hncr_nat : ncr64.toNat = sm_t.core.arena_len := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hinv_t.1.core_ok.arena_len_le; omega)]
  let sm_a : FullState :=
    { sm_t with
      core := { sm_t.core with arena := ar_a,
                               arena_len := sm_t.core.arena_len + 3 + tk.toNat } }
  refine head_wp_add rfl rfl ?_
  refine head_wp_mul rfl rfl ?_
  refine head_wp_add rfl rfl ?_
  refine wp_join_state1 (t := i32) (α := BitVec 32 × List (BitVec 32)) (fun x => x.1)
    (fun (_, ar_c) mc =>
      ar_c.length = c.arena_cap ∧
      (∀ i < sm_t.core.arena_len + 3, ar_c[i]? = ar_a[i]?) ∧
      (∀ k < tk.toNat, ar_c[sm_t.core.arena_len + 3 + k]? = tmp_j[k]?) ∧
      (FullMem c { sm_a with core := { sm_a.core with arena := ar_c } } ⋆ R) mc)
    (fun _ (_, ar_c) mc ⟨har_c_l, hpref_c, hcop_c, hmc⟩ => ?_)
    (fun Jcp hJcp => by
      c0_hfast_nogrp
      · -- `(ncr & 1) != 0`: `u64` pair copy + optional tail `u32`
        refine wp_while_state1 (t := i32) (α := BitVec 32 × List (BitVec 32)) (fun x => x.1)
          (fun x => tk.toNat - x.1.toNat)
          (fun (cj, ar_j) mcj =>
            cj.toNat ≤ tk.toNat ∧ ar_j.length = c.arena_cap ∧
            (∀ i < sm_t.core.arena_len + 3, ar_j[i]? = ar_a[i]?) ∧
            (∀ k < cj.toNat, ar_j[sm_t.core.arena_len + 3 + k]? = tmp_j[k]?) ∧
            (FullMem c { sm_a with core := { sm_a.core with arena := ar_j } } ⋆ R) mcj)
          (fun Jc64 hJc64 => by
            c0_hfast
            exact hJc64 (0#32, ar_a) ma
              ⟨Nat.zero_le _, hal_a_eq, fun _ _ => rfl,
                fun _ hk => absurd hk (Nat.not_lt_zero _), hma⟩)
          (fun Jc64 (cj, ar_j) mcj ⟨hcj_le, har_j_l, hpref_j, hcop_j, hmcj⟩ ih64 => by
            c0_hfast_nogrp
            · have hcj2 : cj.toNat + 2 ≤ tk.toNat := by
                have : (cj + 2#32).toNat ≤ tk.toNat := by assumption
                have h2 : (cj + 2#32).toNat = cj.toNat + 2 := by c0_bound
                omega
              have hload := cmt_load_tmp_u64 (i := BitVec.setWidth 64 cj)
                (by rw [fid_bv64_32]; dsimp only [sm_a]; omega) hmcj
              have hidx_d : (ncr64 + 3 + BitVec.setWidth 64 cj).toNat =
                  sm_t.core.arena_len + 3 + cj.toNat := by c0_bound
              have hst := cmt_store_arena_u64 (i := ncr64 + 3 + BitVec.setWidth 64 cj)
                (cmtPackPair64 (tmp_j[cj.toNat]'(by omega)) (tmp_j[cj.toNat + 1]'(by omega)))
                (by dsimp only [sm_a]; rw [har_j_l, hidx_d]; omega) hmcj
              have hcj2_bv : (cj + 2#32).toNat = cj.toNat + 2 := by c0_bound
              repeat c0_hstep
              refine head_wp_load (addr := c.pTmp + BitVec.setWidth 64 cj * 4)
                (by dsimp only [Arg.val]
                    rw [show BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0) = 0#64 from rfl]
                    bv_omega)
                (by simpa only [sm_a, tmp_j, fid_bv64_32] using hload) ?_
              repeat c0_hstep
              refine head_wp_store rfl
                (by dsimp only [Arg.val]
                    rw [show BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 0) = 0#64 from rfl]
                    bv_omega)
                hst fun m' hst2 => by
                c0_hfast
                dsimp only at hst2; rw [hidx_d] at hst2
                obtain ⟨hl', hp', hc'⟩ := cmt_u64_copy_step hcj2 (by omega) (by omega) hcop_j
                exact ih64 (cj + 2#32, _) _ (by dsimp only; rw [hcj2_bv]; omega)
                  ⟨by rw [hcj2_bv]; omega, by rw [hl', har_j_l],
                   fun i hi => (hp' i hi).trans (hpref_j i hi),
                   by rw [hcj2_bv]; exact hc', hst2⟩
            · -- Optional tail `if (cj < tk)`
              refine wp_join0 (fun mtl => ∃ ar_tl,
                  ar_tl.length = c.arena_cap ∧
                  (∀ i < sm_t.core.arena_len + 3, ar_tl[i]? = ar_a[i]?) ∧
                  (∀ k < tk.toNat, ar_tl[sm_t.core.arena_len + 3 + k]? = tmp_j[k]?) ∧
                  (FullMem c { sm_a with core := { sm_a.core with arena := ar_tl } } ⋆ R) mtl)
                (fun _ mtl ⟨ar_tl, h1, h2, h3, h4⟩ => by
                  c0_hfast; exact hJcp (cj, ar_tl) mtl ⟨h1, h2, h3, h4⟩)
                (fun Jtl hJtl => by
                  have hnot2 : ¬ (cj.toNat + 2 ≤ tk.toNat) := by
                    intro h; apply hc; have h2 : (cj + 2#32).toNat = cj.toNat + 2 := by c0_bound
                    omega
                  c0_hfast_nogrp
                  · have hcj_lt : cj.toNat < tk.toNat := by assumption
                    have hcj_eq : cj.toNat + 1 = tk.toNat := by omega
                    have hidx_d : (ncr64 + 3 + BitVec.setWidth 64 cj).toNat =
                        sm_t.core.arena_len + 3 + cj.toNat := by c0_bound
                    have hcj_tmp : (BitVec.setWidth 64 cj).toNat < tmp_j.length := by
                      rw [fid_bv64_32, htmp_l]; omega
                    have hst32 := cmt_store_arena_i32 (s := { sm_a with core :=
                        { sm_a.core with arena := ar_j } })
                      (i := ncr64 + 3 + BitVec.setWidth 64 cj)
                      (tmp_j[(BitVec.setWidth 64 cj).toNat]'hcj_tmp)
                      (by dsimp only [sm_a]; rw [har_j_l, hidx_d]; omega) hmcj
                    repeat c0_hstep
                    refine head_wp_store rfl (by dsimp only [Arg.val]; bv_omega) hst32
                      fun m' hm32 => by
                      c0_hfast
                      dsimp only at hm32; rw [hidx_d] at hm32
                      refine hJtl _ ⟨_, by simp [har_j_l], fun i hi => by
                        rw [List.getElem?_set_ne (by omega)]; exact hpref_j i hi, fun k hk => ?_,
                        hm32⟩
                      rcases Nat.lt_or_ge k cj.toNat with hkc | hkc
                      · rw [List.getElem?_set_ne (by omega)]; exact hcop_j k hkc
                      · have hkeq : k = cj.toNat := by omega
                        subst hkeq
                        rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem (by omega)]
                        exact congrArg some (cmt2_getElem_eq (fid_bv64_32 cj))
                  · have hcj_eq : cj.toNat = tk.toNat := by omega
                    c0_hfast; exact hJtl mcj ⟨ar_j, har_j_l, hpref_j,
                      fun k hk => hcop_j k (by omega), hmcj⟩))
      · -- `(ncr & 1) == 0`: plain `u32` copy loop
        refine wp_while_state1 (t := i32) (α := BitVec 32 × List (BitVec 32)) (fun x => x.1)
          (fun x => tk.toNat - x.1.toNat)
          (fun (cj, ar_j) mcj =>
            cj.toNat ≤ tk.toNat ∧ ar_j.length = c.arena_cap ∧
            (∀ i < sm_t.core.arena_len + 3, ar_j[i]? = ar_a[i]?) ∧
            (∀ k < cj.toNat, ar_j[sm_t.core.arena_len + 3 + k]? = tmp_j[k]?) ∧
            (FullMem c { sm_a with core := { sm_a.core with arena := ar_j } } ⋆ R) mcj)
          (fun Jc32 hJc32 => by
            c0_hfast
            exact hJc32 (0#32, ar_a) ma
              ⟨Nat.zero_le _, hal_a_eq, fun _ _ => rfl,
                fun _ hk => absurd hk (Nat.not_lt_zero _), hma⟩)
          (fun Jc32 (cj, ar_j) mcj ⟨hcj_le, har_j_l, hpref_j, hcop_j, hmcj⟩ ih32 => by
            c0_hfast_nogrp
            · have hcj_lt : cj.toNat < tk.toNat := by assumption
              have hidx_d : (ncr64 + 3 + BitVec.setWidth 64 cj).toNat =
                  sm_t.core.arena_len + 3 + cj.toNat := by c0_bound
              have hcj_tmp : (BitVec.setWidth 64 cj).toNat < tmp_j.length := by
                rw [fid_bv64_32, htmp_l]; omega
              have hcj1 : (cj + 1#32).toNat = cj.toNat + 1 := by c0_bound
              have hst32 := cmt_store_arena_i32 (s := { sm_a with core :=
                  { sm_a.core with arena := ar_j } })
                (i := ncr64 + 3 + BitVec.setWidth 64 cj)
                (tmp_j[(BitVec.setWidth 64 cj).toNat]'hcj_tmp)
                (by dsimp only [sm_a]; rw [har_j_l, hidx_d]; omega) hmcj
              repeat c0_hstep
              refine head_wp_store rfl (by dsimp only [Arg.val]; bv_omega) hst32
                fun m' hm32 => by
                c0_hfast
                dsimp only at hm32; rw [hidx_d] at hm32
                refine ih32 (cj + 1#32, _) _ (by dsimp only; rw [hcj1]; omega)
                  ⟨by rw [hcj1]; omega, by simp [har_j_l], fun i hi => by
                    rw [List.getElem?_set_ne (by omega)]; exact hpref_j i hi, fun k hk => ?_,
                    hm32⟩
                rw [hcj1] at hk
                rcases Nat.lt_or_ge k cj.toNat with hkc | hkc
                · rw [List.getElem?_set_ne (by omega)]; exact hcop_j k hkc
                · have hkeq : k = cj.toNat := by omega
                  subst hkeq
                  rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem (by omega)]
                  exact congrArg some (cmt2_getElem_eq (fid_bv64_32 cj))
            · have hcj_eq : cj.toNat = tk.toNat := by omega
              c0_hfast
              exact hJcp (cj, ar_j) mcj ⟨har_j_l, hpref_j,
                fun k hk => hcop_j k (by omega), hmcj⟩))
  -- Establish `FullDenseInvW` & `CommitArenaExt` for the newly added clause!
  let sm_c : FullState := { sm_a with core := { sm_a.core with arena := ar_c } }
  obtain ⟨hinv_c, hext_tc, hncr_ref⟩ := cmt_fullDenseInvW_addClause hinv_t har_c_l hbd_a
    htk_ge3 htk_le_mx (fun i hi => (hpref_c i (by omega)).trans (hhold_a i hi))
    (by rw [hpref_c _ (by omega)]; exact hnoshrk_a)
    (by rw [hpref_c _ (by omega)]; exact hnogarb_a)
    (by rw [hpref_c _ (by omega)]; exact hsz_a)
    hcop_c (by rw [hcv_t]; exact htmp_lits_lt) htmp_lits_nd htmp_lits_ent
  have hext_c : CommitArenaExt s0 sm_c := hext_t.trans hext_tc
  -- Watch-push loop `while (j < tk)` with `break` on `!wp_l` rollback
  refine wp_join_state (α := Bool × Bool × BitVec 64 × BitVec 32 × FullState)
    (fun x => (x.1, x.2.1, x.2.2.1, x.2.2.2.1, ()))
    (fun (dd_w, ok_w, ga_w, _, sw) mw =>
      FullDenseInvW c F0 F_next sw ∧ CommitArenaExt s0 sw ∧
      sw.core.cur_vars = s0.core.cur_vars + 1 ∧
      sw.scratch.scratch_buf = s0.scratch.scratch_buf ∧
      sw.scratch.res_sz = BitVec.ofNat 64 best_k.toNat ∧
      sw.core.fuel = s0.core.fuel ∧
      sw.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
      sw.scratch.tarjan_reach = s0.scratch.tarjan_reach ∧
      (FullMem c sw ⋆ R) mw)
    (fun _ (dd_w, ok_w, ga_w, _, sw) mw ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ => by
      refine wp_join_state1 (t := i64) (α := BitVec 64) (fun x => x) (fun _ m' => m' = mw)
        (fun _ ir_w m' hm' => by
          rw [hm']; c0_hfast
          exact hJbr dd_w ok_w ga_w ir_w sw mw h1 h2 h3 h4 h5 h6 h7 h8 h9)
        (fun Jir hJir => by
          c0_hfast_nogrp
          · exact hJir (ir + 1#64) mw rfl
          · exact hJir ir mw rfl))
    (fun Jwp hJwp => ?_)
  refine wp_while_state (α := Bool × BitVec 32 × FullState) (fun x => (x.1, x.2.1, ()))
    (fun x => tk.toNat - x.2.1.toNat)
    (fun (dd_w, wj, sw) mw =>
      wj.toNat ≤ tk.toNat ∧
      FullDenseInvW c F0 F_next sw ∧ CommitArenaExt s0 sw ∧
      sw.core.cur_vars = s0.core.cur_vars + 1 ∧
      sw.core.arena = ar_c ∧ sw.core.arena_len = sm_t.core.arena_len + 3 + tk.toNat ∧
      sw.core.tmp = tmp_j ∧
      sw.scratch.scratch_buf = s0.scratch.scratch_buf ∧
      sw.scratch.res_sz = BitVec.ofNat 64 best_k.toNat ∧
      sw.core.fuel = s0.core.fuel ∧
      sw.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
      sw.scratch.tarjan_reach = s0.scratch.tarjan_reach ∧
      (FullMem c sw ⋆ R) mw)
    (fun Jwl hJwl => by
      c0_hfast
      exact hJwl (dd_a, 0#32, sm_c) mc
        ⟨Nat.zero_le _, hinv_c, hext_c, hcv_t, rfl, rfl, rfl, hsb_t, hrs_t, hfl_t,
          htm_t, htr_t, hmc⟩)
    (fun Jwl (dd_w, wj, sw) mw
        ⟨hwj_le, hinv_w, hext_w, hcv_w, har_w, hal_w, htmp_w, hsb_w, hrs_w, hfl_w,
          htm_w, htr_w, hmw⟩ ihw => ?_)
  c0_hfast_nogrp
  · have hwj_lt : wj.toNat < tk.toNat := by assumption
    have hwj_tmp : (BitVec.setWidth 64 wj).toNat < sw.core.tmp.length := by
      rw [fid_bv64_32, htmp_w, htmp_l]; omega
    have hwj_lit_lt : (sw.core.tmp[(BitVec.setWidth 64 wj).toNat]'hwj_tmp).toNat <
        2 * (s0.core.cur_vars + 1) := by
      apply htmp_lits_lt
      have hi : (BitVec.setWidth 64 wj).toNat = wj.toNat := fid_bv64_32 wj
      have hmem : tmp_j[wj.toNat]'(by omega) ∈ tmp_j.take tk.toNat := by
        rw [List.mem_iff_getElem]; exact ⟨wj.toNat, by simp; omega, by simp⟩
      have heq : sw.core.tmp[(BitVec.setWidth 64 wj).toNat]'hwj_tmp =
          tmp_j[wj.toNat]'(by omega) := by
        apply Option.some.inj
        rw [← List.getElem?_eq_getElem hwj_tmp, hi, htmp_w, List.getElem?_eq_getElem]
      rw [heq]; exact List.mem_map_of_mem hmem
    have hwj1 : (wj + 1#32).toNat = wj.toNat + 1 := by c0_bound
    c0_hfast_nogrp
    have htk_mask : (tk &&& 0x7FFFFFFF#32).toNat = tk.toNat := by
      have : tk.toNat < 2 ^ 31 := by omega
      rw [BitVec.toNat_and, show (0x7FFFFFFF#32 : BitVec 32).toNat = 2 ^ 31 - 1 from rfl]
      rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt this]
    have htk_flag : ((tk &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32 := by
      rw [BitVec.and_assoc, show (0x7FFFFFFF#32 &&& 0x80000000#32) = 0#32 from rfl, BitVec.and_zero]
    have hncr32_nat : (ncr64.setWidth 32).toNat = sm_t.core.arena_len := by
      rw [BitVec.toNat_setWidth, hncr_nat, Nat.mod_eq_of_lt (by omega)]
    fid_call hWatchPush
    refine ⟨c, sw, R, rfl, hinv_w.1, (m6_denseWatchesInv_of_w hinv_w).layout,
      (fun h => absurd h (by decide)),
      fun _ => ⟨fun h => by
          dsimp only [Arg.val] at h
          have := congrArg BitVec.toNat h
          change (tk &&& 0x7FFFFFFF#32).toNat = (0xFFFFFFFF#32 : BitVec 32).toNat at this
          rw [htk_mask, show (0xFFFFFFFF#32 : BitVec 32).toNat = 4294967295 from rfl] at this
          omega,
        fun h => by
          dsimp only [Arg.val] at h
          have := congrArg BitVec.toNat h
          rw [hncr32_nat, show (0xFFFFFFFF#32 : BitVec 32).toNat = 4294967295 from rfl] at this
          omega⟩,
      hmw, fun wp_l wv' ws' wl' wu' wso' mw1 hlen1 hlay1 hoth hok_t hok_f hmw1 => ?_⟩
    let sw1 : FullState :=
      { sw with
        core := { sw.core with wvec := wv', wstk := ws', wlen := wl', wusable := wu' }
        scratch := { sw.scratch with wsort := wso' } }
    have hncr_ref_w : sm_t.core.arena_len ∈ fullArenaClauseRefs sw := by
      unfold fullArenaClauseRefs fullArenaClauseRefsCore
      rw [har_w, hal_w]; exact hncr_ref
    have hinv_w1 : FullDenseInvW c F0 F_next sw1 :=
      m6_fullDenseInvW_of_watchPush_occ hinv_w hlen1 hlay1 htk_flag
        (by rw [htk_mask]; omega) (by rw [hncr32_nat]; omega)
        (by rw [hncr32_nat]; exact hncr_ref_w) hoth
        (fun ht => by
          have h := hok_t ht; exact ⟨h.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2 rfl⟩)
        (fun hf => (hok_f hf).1)
    have hext_w1 : CommitArenaExt s0 sw1 := hext_w.of_eq rfl rfl
    refine wp_join_state1 (t := .bool) (α := Bool) (fun x => x) (fun _ m' => m' = mw1)
      (fun _ dd_w1 m' hm' => ?_)
      (fun Jdw hJdw => by
        c0_hfast_nogrp
        · exact hJdw true mw1 rfl
        · exact hJdw dd_w mw1 rfl)
    rw [hm']
    c0_hfast_nogrp
    · -- `wp_l = true`: update `fl[tmp[wj] >> 1]` and continue
      refine wp_join_state1 (t := i32) (α := BitVec 32) (fun x => x) (fun _ m' => m' = mw1)
        (fun _ fbit m' hm' => ?_)
        (fun Jfb hJfb => by
          c0_hfast_nogrp
          · exact hJfb _ mw1 rfl
          · exact hJfb _ mw1 rfl)
      rw [hm']
      have htv_lt : (BitVec.setWidth 64 ((sw1.core.tmp[(BitVec.setWidth 64 wj).toNat]'hwj_tmp) >>>
          (1 : Nat))).toNat < sw1.core.flags.length := by
        rw [fid_bv64_32, bv32_lshr_1, hinv_w1.1.core_ok.flags_len]
        have := hinv_w1.1.core_ok.cur_vars_le; dsimp only [sw1] at this ⊢; omega
      c0_hfast
      refine ihw (dd_w1, wj + 1#32, _) m (by dsimp only; rw [hwj1]; omega)
        ⟨by rw [hwj1]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hm⟩
      · exact cmt_fullDenseInvW_set_flags hinv_w1
          (by simp only [List.length_set]; exact hinv_w1.1.core_ok.flags_len)
      · exact hext_w1.of_eq rfl rfl
      · exact hcv_w
      · exact har_w
      · exact hal_w
      · exact htmp_w
      · exact hsb_w
      · exact hrs_w
      · exact hfl_w
      · exact htm_w
      · exact htr_w
    · -- `!wp_l`: rollback loop (`while (uk < wj)` `full_unwatch_large`), then `PH_GARB`, `break`
      refine wp_while_state1 (t := i32) (α := BitVec 32 × FullState) (fun x => x.1)
        (fun x => wj.toNat - x.1.toNat)
        (fun (uk, su) mu =>
          uk.toNat ≤ wj.toNat ∧
          FullDenseInvW c F0 F_next su ∧ CommitArenaExt s0 su ∧
          su.core.cur_vars = s0.core.cur_vars + 1 ∧
          su.core.arena = ar_c ∧ su.core.arena_len = sm_t.core.arena_len + 3 + tk.toNat ∧
          su.core.tmp = tmp_j ∧
          su.scratch.scratch_buf = s0.scratch.scratch_buf ∧
          su.scratch.res_sz = BitVec.ofNat 64 best_k.toNat ∧
          su.core.fuel = s0.core.fuel ∧
          su.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
          su.scratch.tarjan_reach = s0.scratch.tarjan_reach ∧
          (FullMem c su ⋆ R) mu)
        (fun Juk hJuk => by
          c0_hfast
          exact hJuk (0#32, sw1) mw1
            ⟨Nat.zero_le _, hinv_w1, hext_w1, hcv_w, har_w, hal_w, htmp_w, hsb_w, hrs_w,
              hfl_w, htm_w, htr_w, hmw1⟩)
        (fun Juk (uk, su) mu
            ⟨huk_le, hinv_u, hext_u, hcv_u, har_u, hal_u, htmp_u, hsb_u, hrs_u, hfl_u,
              htm_u, htr_u, hmu⟩ ihu => by
          c0_hfast_nogrp
          · have huk_lt : uk.toNat < wj.toNat := by assumption
            have huk_tmp : (BitVec.setWidth 64 uk).toNat < su.core.tmp.length := by
              rw [fid_bv64_32, htmp_u, htmp_l]; omega
            have huk1 : (uk + 1#32).toNat = uk.toNat + 1 := by c0_bound
            c0_hfast_nogrp
            fid_call hUnwatch
            refine ⟨c, su, R, rfl, hinv_u.1, (m6_denseWatchesInv_of_w hinv_u).layout, hmu,
              fun wv'' ws'' wu'' mu' hlen'' _ hwat hmu' => ?_⟩
            c0_hfast
            exact ihu (uk + 1#32, _) mu' (by dsimp only; rw [huk1]; omega)
              ⟨by rw [huk1]; omega,
               cmt_fullDenseInvW_unwatch hinv_u hlen'' (hwat F_next hinv_u.2.1.watches),
               hext_u.of_eq rfl rfl, hcv_u, har_u, hal_u, htmp_u, hsb_u, hrs_u, hfl_u,
               htm_u, htr_u, hmu'⟩
          · have hncr_ar_lt : ncr64.toNat < su.core.arena.length := by
              rw [hncr_nat, har_u, har_c_l]; omega
            have hncr_ref_u : sm_t.core.arena_len ∈ fullArenaClauseRefs su := by
              unfold fullArenaClauseRefs fullArenaClauseRefsCore
              rw [har_u, hal_u]; exact hncr_ref
            c0_hfast
            have hset_mg : su.core.arena.set ncr64.toNat
                  (su.core.arena[ncr64.toNat]'hncr_ar_lt ||| 524288) =
                su.core.arena.set sm_t.core.arena_len
                  (fullArenaHdr su sm_t.core.arena_len ||| 0x00080000#32) := by
              have hlt2 : sm_t.core.arena_len < su.core.arena.length := by
                rwa [hncr_nat] at hncr_ar_lt
              have hget : su.core.arena[ncr64.toNat]'hncr_ar_lt =
                  fullArenaHdr su sm_t.core.arena_len := by
                unfold fullArenaHdr fullArenaHdrCore
                rw [List.getElem?_eq_getElem hlt2, Option.getD_some]
                exact cmt2_getElem_eq hncr_nat
              rw [hget, hncr_nat]; rfl
            dsimp only at hm; rw [hset_mg] at hm
            obtain ⟨hinv_mg, hrefs_mg, _⟩ := cmt_fullDenseInvW_markGarb hinv_u hncr_ref_u
            let su_mg : FullState :=
              { su with core := { su.core with
                  arena := su.core.arena.set sm_t.core.arena_len
                    (fullArenaHdr su sm_t.core.arena_len ||| 0x00080000#32) } }
            have hext_mg : CommitArenaExt s0 su_mg := by
              refine ⟨hext_u.1, fun i hi => ?_, fun r hr => hrefs_mg ▸ hext_u.2.2 r hr⟩
              have hlt_t : i < sm_t.core.arena_len := Nat.lt_of_lt_of_le hi hext_t.1
              dsimp only [su_mg]; rw [List.getElem?_set_ne (by omega)]; exact hext_u.2.1 i hi
            exact hJwp (dd_w1, false, ga + 3#64 + BitVec.setWidth 64 tk, wj, su_mg) m
              ⟨hinv_mg, hext_mg, hcv_u, hsb_u, hrs_u, hfl_u, htm_u, htr_u, hm⟩)
  · c0_hfast
    exact hJwp (dd_w, ok, ga, wj, sw) mw
      ⟨hinv_w, hext_w, hcv_w, hsb_w, hrs_w, hfl_w, htm_w, htr_w, hmw⟩

/-! ## 3. Phase 2 Binary-Branch & Outer Loop WP (`[2*fv+1, q]` & `[2*fv+1, C \ {flit}]`) -/

private def cmtP2BinExpr (h64 : Val i64) (best_k sc : Val i32)
    (pAr pScr pCnt pFl pWv : Val i64) (brow_off mn : Val i32)
    (dd0 : Bool) (cv64 pDeg pTmp : Val i64) (si : Val i32) (dd1 ok1 : Bool)
    (J_p2 : Cont [i32, .bool, .bool, i64, i64])
    (mi : Val i32) (dd ok : Bool) (ga ir : Val i64) (c_top : Val i32)
    (Jbr : Cont [.bool, .bool, i64, i64]) : Expr Val Cont [.bool] :=
  cmtNav
    [.grpB5 (mi, dd, ok, ga, ir, ()), .step, .brT, .brT,
     .step, .step, .step, .step, .ld32 c_top, .grpK4 Jbr, .step, .step, .brT]
    (cmtP2GrpExpr h64 best_k sc pAr pScr pCnt pFl pWv brow_off mn dd0 cv64 pDeg pTmp si dd1 ok1
      |> cmtGrpK5 J_p2)

private theorem cmt_phase2_bin_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hAddBin : ∀ a m Q X, fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_next : List (List Nat)} {s0 sm : FullState}
    {R : Mem 64 → Prop} {best_k sc brow_off mn si mi c_top : Val i32}
    {dd0 dd1 ok1 dd ok : Bool} {cv64 ga ir : Val i64}
    {J_p2 : Cont [i32, .bool, .bool, i64, i64]} {Jbr : Cont [.bool, .bool, i64, i64]}
    {mm : Mem 64}
    (hinv_m : FullDenseInvW c F0 F_next sm) (hext_m : CommitArenaExt s0 sm)
    (hcv_m : sm.core.cur_vars = s0.core.cur_vars + 1)
    (hcv64 : cv64 = BitVec.ofNat 64 s0.core.cur_vars)
    (hsb_m : sm.scratch.scratch_buf = s0.scratch.scratch_buf)
    (hrs_m : sm.scratch.res_sz = BitVec.ofNat 64 best_k.toNat)
    (hfl_m : sm.core.fuel = s0.core.fuel)
    (htm_m : sm.scratch.tarjan_mark = s0.scratch.tarjan_mark)
    (htr_m : sm.scratch.tarjan_reach = s0.scratch.tarjan_reach)
    (hq_lt : (c_top &&& 0x7FFFFFFF#32).toNat < 2 * s0.core.cur_vars)
    (hent : (cnfOfClauses F_next).EntailsClause
      (cnfClause [2 * s0.core.cur_vars + 1, (c_top &&& 0x7FFFFFFF#32).toNat]))
    (hmm : (FullMem c sm ⋆ R) mm)
    (hExit : ∀ (mv : BitVec 32) (dd2 ok2 : Bool) (ga' ir' : BitVec 64)
      (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_next s' → CommitArenaExt s0 s' →
      s'.core.cur_vars = s0.core.cur_vars + 1 →
      s'.scratch.scratch_buf = s0.scratch.scratch_buf →
      s'.scratch.res_sz = BitVec.ofNat 64 best_k.toNat →
      s'.core.fuel = s0.core.fuel →
      s'.scratch.tarjan_mark = s0.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s0.scratch.tarjan_reach →
      (FullMem c s' ⋆ R) m' → J_p2 (mv, dd2, ok2, ga', ir', ()) m')
    (hJbr : ∀ (dd' ok' : Bool) (ga' ir' : BitVec 64) (sm' : FullState) (mm' : Mem 64),
      FullDenseInvW c F0 F_next sm' → CommitArenaExt s0 sm' →
      sm'.core.cur_vars = s0.core.cur_vars + 1 →
      sm'.scratch.scratch_buf = s0.scratch.scratch_buf →
      sm'.scratch.res_sz = BitVec.ofNat 64 best_k.toNat →
      sm'.core.fuel = s0.core.fuel →
      sm'.scratch.tarjan_mark = s0.scratch.tarjan_mark →
      sm'.scratch.tarjan_reach = s0.scratch.tarjan_reach →
      (FullMem c sm' ⋆ R) mm' → Jbr (dd', ok', ga', ir', ()) mm') :
    wp Γ Q X (cmtP2BinExpr c.hdr best_k sc c.pArena c.pScratchBuf c.pWsort c.pFlags
      c.pWvec brow_off mn dd0 cv64 c.pRepr c.pTmp si dd1 ok1 J_p2 mi dd ok ga ir c_top Jbr)
      mm := by
  have hmx := c.hmaxv; unfold dimacsBound at *
  have hfv_lt : s0.core.cur_vars < c.max_vars := by have := hinv_m.1.core_ok.cur_vars_le; omega
  have hfresh_nat : ((cv64.setWidth 32) <<< (1 : BitVec 32)).toNat = 2 * s0.core.cur_vars := by
    rw [hcv64]
    change ((BitVec.ofNat 64 s0.core.cur_vars).setWidth 32 <<< (1 : Nat)).toNat = _
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  have hfresh1_nat : (((cv64.setWidth 32) <<< (1 : BitVec 32)) ^^^ 1#32).toNat =
      2 * s0.core.cur_vars + 1 := by
    rw [hcv64]; exact FullBvaFwdHelpers.bva_bv32_shl1_xor1 (by omega)
  have hnf_wv : ((BitVec.setWidth 64 (((cv64.setWidth 32) <<< (1 : BitVec 32)) ^^^ 1#32) <<<
      (1 : Nat)) + 1#64).toNat < sm.core.wvec.length := by
    rw [hinv_m.1.core_ok.wvec_len, BitVec.toNat_add, BitVec.toNat_shiftLeft, fid_bv64_32,
      hfresh1_nat, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  have hq_wv : ((BitVec.setWidth 64 (c_top &&& 0x7FFFFFFF#32) <<< (1 : Nat)) + 1#64).toNat <
      sm.core.wvec.length := by
    rw [hinv_m.1.core_ok.wvec_len, BitVec.toNat_add, BitVec.toNat_shiftLeft, fid_bv64_32,
      show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  refine head_wp_and rfl rfl ?_
  refine wp_join_state1 (t := .bool) (α := Bool) (fun x => x) (fun _ m' => m' = mm)
    (fun _ dd_a m' hm' => ?_)
    (fun Jdd hJdd => by
      c0_hfast_nogrp
      · c0_hfast; exact hJdd dd mm rfl
      · c0_hfast_nogrp
        refine wp_join_state1 (t := i64) (α := BitVec 64) (fun x => x) (fun _ m' => m' = mm)
          (fun _ na m' hm' => by
            rw [hm']
            refine wp_join_state1 (t := i64) (α := BitVec 64) (fun x => x) (fun _ m' => m' = mm)
              (fun _ nb m' hm' => by
                rw [hm']
                refine wp_join_state1 (t := .bool) (α := Bool) (fun x => x) (fun _ m' => m' = mm)
                  (fun _ ddi m' hm' => by rw [hm']; c0_hfast; exact hJdd ddi mm rfl)
                  (fun Jdi hJdi => by
                    c0_hfast_nogrp
                    · c0_hfast; exact hJdi true mm rfl
                    · c0_hfast; exact hJdi true mm rfl
                    · c0_hfast; exact hJdi true mm rfl
                    · c0_hfast; exact hJdi true mm rfl
                    · refine wp_join0 (fun m' => m' = mm)
                        (fun _ m' hm' => by
                          rw [hm']; c0_hfast_nogrp
                          · c0_hfast; exact hJdi true mm rfl
                          · c0_hfast; exact hJdi dd mm rfl)
                        (fun Jef hJef => by
                          c0_hfast_nogrp
                          · c0_hfast; exact hJef mm rfl
                          · c0_hfast; exact hJef mm rfl
                          · c0_hfast; exact hJdi dd mm rfl)))
              (fun Jnb hJnb => by c0_hfast_nogrp <;> (c0_hfast; exact hJnb _ mm rfl)))
          (fun Jna hJna => by c0_hfast_nogrp <;> (c0_hfast; exact hJna _ mm rfl)))
  rw [hm']; c0_hfast_nogrp
  fid_call hAddBin
  refine ⟨c, F0, F_next, sm, R, rfl, hinv_m.1, hinv_m.2.1, hinv_m.2.2.2.2.2.1,
    fun _ _ => by
      change (cnfOfClauses F_next).EntailsClause
        (cnfClause [(((cv64.setWidth 32) <<< (1 : BitVec 32)) ^^^ 1#32).toNat,
          (c_top &&& 0x7FFFFFFF#32).toNat])
      rw [hfresh1_nat]; exact hent,
    hmm, fun br vals' fl' lvl' rsns' trl' tp' te' unass' unfl' wv' ws' wl' wu' nb' oom' inc'
      ph' wso' m2 hlen2 hw2 _ _ _ hm2 => ?_⟩
  let sm2 : FullState :=
    { sm with
      core :=
        { sm.core with
          vals := vals', flags := fl', lvl := lvl', rsns := rsns', trl := trl', trail_pos := tp',
          trail_end := te', unassigned := unass', unflushed := unfl', wvec := wv', wstk := ws',
          wlen := wl', wusable := wu', num_binary := nb', oom := oom', inconsistent := inc' }
      scratch := { sm.scratch with phases := ph', wsort := wso' } }
  have hinv2 : FullDenseInvW c F0 F_next sm2 := cmt_fullDenseInvW_addBin hinv_m hlen2 hw2
  have hext2 : CommitArenaExt s0 sm2 := hext_m.of_eq rfl rfl
  refine wp_join_state1 (t := .bool) (α := Bool) (fun x => x) (fun _ m' => m' = m2)
    (fun _ dd_b m' hm' => ?_)
    (fun Jddb hJddb => by c0_hfast_nogrp <;> (c0_hfast; exact hJddb _ m2 rfl))
  rw [hm']
  refine wp_join_state1 (t := i32) (α := BitVec 32) (fun x => x) (fun _ m' => m' = m2)
    (fun _ fbit m' hm' => ?_)
    (fun Jfb hJfb => by c0_hfast_nogrp <;> (c0_hfast; exact hJfb _ m2 rfl))
  rw [hm']
  have hfr_v : (BitVec.setWidth 64 (((cv64.setWidth 32) <<< (1 : BitVec 32)) >>>
      (1 : Nat))).toNat < sm2.core.flags.length := by
    rw [fid_bv64_32, bv32_lshr_1, hfresh_nat, hinv2.1.core_ok.flags_len]; omega
  have hq_v : (BitVec.setWidth 64 ((c_top &&& 0x7FFFFFFF#32) >>> (1 : Nat))).toNat <
      (sm2.core.flags.set (BitVec.setWidth 64 (((cv64.setWidth 32) <<< (1 : BitVec 32)) >>>
        (1 : Nat))).toNat
        (sm2.core.flags[(BitVec.setWidth 64 (((cv64.setWidth 32) <<< (1 : BitVec 32)) >>>
          (1 : Nat))).toNat]'hfr_v ||| 8 ||| 16 ||| 64)).length := by
    rw [List.length_set, fid_bv64_32, bv32_lshr_1, hinv2.1.core_ok.flags_len]; omega
  c0_hfast_nogrp
  · c0_hfast
    refine hExit mi dd_b false ga ir _ m ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hm
    · exact cmt_fullDenseInvW_set_flags hinv2
        (by simp only [List.length_set]; exact hinv2.1.core_ok.flags_len)
    · exact hext2.of_eq rfl rfl
    · exact hcv_m
    · exact hsb_m
    · exact hrs_m
    · exact hfl_m
    · exact htm_m
    · exact htr_m
  · c0_hfast
    refine hExit mi dd_b false ga ir _ m ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hm
    · exact cmt_fullDenseInvW_set_flags hinv2
        (by simp only [List.length_set]; exact hinv2.1.core_ok.flags_len)
    · exact hext2.of_eq rfl rfl
    · exact hcv_m
    · exact hsb_m
    · exact hrs_m
    · exact hfl_m
    · exact htm_m
    · exact htr_m
  · c0_hfast
    refine hExit mi dd_b false ga ir _ m ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hm
    · exact cmt_fullDenseInvW_set_flags hinv2
        (by simp only [List.length_set]; exact hinv2.1.core_ok.flags_len)
    · exact hext2.of_eq rfl rfl
    · exact hcv_m
    · exact hsb_m
    · exact hrs_m
    · exact hfl_m
    · exact htm_m
    · exact htr_m
  · c0_hfast
    refine hJbr dd_b ok ga ir _ m ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hm
    · exact cmt_fullDenseInvW_set_flags hinv2
        (by simp only [List.length_set]; exact hinv2.1.core_ok.flags_len)
    · exact hext2.of_eq rfl rfl
    · exact hcv_m
    · exact hsb_m
    · exact hrs_m
    · exact hfl_m
    · exact htm_m
    · exact htr_m

theorem cmt_phase2_wp {Γ : Env} {Q : Post [.bool]} {X : XPost}
    (hAddBin : ∀ a m Q X, fullAddBinSpec a m Q X →
      Γ "full_add_bin" [i64, i32, i32] [i64] a m Q X)
    (hAllocCl : ∀ a m Q X, fullAllocClSpec a m Q X →
      Γ "full_alloc_cl" [i64, i32, i32, .bool] [i64] a m Q X)
    (hWatchPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hUnwatch : ∀ a m Q X, fullUnwatchLargeSpec a m Q X →
      Γ "full_unwatch_large" [i64, i32, i32] [] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur F_next : List (List Nat)} {s0 s : FullState}
    {R : Mem 64 → Prop} {best_k sc brow_off mn si : Val i32}
    {dd0 dd1 ok1 : Bool} {cv64 : Val i64}
    {J_p2 : Cont [i32, .bool, .bool, i64, i64]} {bump : Nat} {mp : Mem 64}
    (hl0 : s0.LengthsOk c) (hw0 : FullWitnessInv c F0 F_cur s0.core)
    (hinv : FullDenseInvW c F0 F_next s)
    (hcv_eq : s.core.cur_vars = s0.core.cur_vars + 1)
    (hcv64 : cv64 = BitVec.ofNat 64 s0.core.cur_vars)
    (hbk1 : 1 ≤ best_k.toNat) (hbk_sc : best_k.toNat < fidStepsCap c.scratch_cap)
    (hbro_eq : brow_off.toNat =
      (s0.scratch.scratch_buf[fidStepsCap c.scratch_cap + best_k.toNat]?.getD 0#32).toNat)
    (hmn_eq : mn.toNat =
      (s0.scratch.scratch_buf[2 * fidStepsCap c.scratch_cap + best_k.toNat]?.getD 0#32).toNat)
    (hmat : Step7BvaMatrixInv c F_cur s0 (best_k.toNat + 1) bump)
    (hrow_res : ∀ m < mn.toNat, ∃ res : List Nat,
      (∀ x ∈ res, x < 2 * s0.core.cur_vars) ∧ (res.map (· / 2)).Nodup ∧
      FidBvaRowEntryOk F_cur s0 (s0.scratch.scratch_buf[best_k.toNat]?.getD 0#32).toNat
        (s0.scratch.scratch_buf[brow_off.toNat + m]?.getD 0#32) res ∧
      (cnfOfClauses F_next).EntailsClause (cnfClause ((2 * s0.core.cur_vars + 1) :: res)))
    (har_eq : s.core.arena = s0.core.arena) (hal_eq : s.core.arena_len = s0.core.arena_len)
    (hsb_eq : s.scratch.scratch_buf = s0.scratch.scratch_buf)
    (hres : s.scratch.res_sz = BitVec.ofNat 64 best_k.toNat)
    (hfuel : s.core.fuel = s0.core.fuel)
    (htm : s.scratch.tarjan_mark = s0.scratch.tarjan_mark)
    (htr : s.scratch.tarjan_reach = s0.scratch.tarjan_reach)
    (hmp : (FullMem c s ⋆ R) mp)
    (hExit : ∀ (mv : BitVec 32) (dd2 ok2 : Bool) (ga ir : BitVec 64)
      (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_next s' → CommitArenaExt s0 s' →
      s'.core.cur_vars = s0.core.cur_vars + 1 →
      s'.scratch.scratch_buf = s0.scratch.scratch_buf →
      s'.scratch.res_sz = BitVec.ofNat 64 best_k.toNat →
      s'.core.fuel = s0.core.fuel →
      s'.scratch.tarjan_mark = s0.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s0.scratch.tarjan_reach →
      (FullMem c s' ⋆ R) m' → J_p2 (mv, dd2, ok2, ga, ir, ()) m') :
    wp Γ Q X (cmtP2GrpExpr c.hdr best_k sc c.pArena c.pScratchBuf c.pWsort c.pFlags
      c.pWvec brow_off mn dd0 cv64 c.pRepr c.pTmp si dd1 ok1 |> cmtGrpK5 J_p2) mp := by
  have hscr := c.hscr; have har_b := c.harena; have hmx := c.hmaxv; unfold dimacsBound at *
  have hsc_le := fidStepsCap_le_256 c.scratch_cap
  have h4sc := fidStepsCap_mul4_le c.scratch_cap
  have hfv_lt : s0.core.cur_vars < c.max_vars := by have := hinv.1.core_ok.cur_vars_le; omega
  have hfresh_nat : ((cv64.setWidth 32) <<< (1 : BitVec 32)).toNat = 2 * s0.core.cur_vars := by
    rw [hcv64]
    change ((BitVec.ofNat 64 s0.core.cur_vars).setWidth 32 <<< (1 : Nat)).toNat = _
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  have hfresh1_nat : (((cv64.setWidth 32) <<< (1 : BitVec 32)) ^^^ 1#32).toNat =
      2 * s0.core.cur_vars + 1 := by
    rw [hcv64]; exact FullBvaFwdHelpers.bva_bv32_shl1_xor1 (by omega)
  have hbk_row := hmat.1.2.2.2.2.2 best_k.toNat (by omega)
  have hext0 : CommitArenaExt s0 s := (CommitArenaExt.refl s0).of_eq hal_eq har_eq
  refine wp_while_state (α := BitVec 32 × Bool × Bool × BitVec 64 × BitVec 64 × FullState)
    (fun x => (x.1, x.2.1, x.2.2.1, x.2.2.2.1, x.2.2.2.2.1, ()))
    (fun x => mn.toNat - x.1.toNat)
    (fun (mi, dd, ok, ga, ir, sm) mm =>
      mi.toNat ≤ mn.toNat ∧
      FullDenseInvW c F0 F_next sm ∧ CommitArenaExt s0 sm ∧
      sm.core.cur_vars = s0.core.cur_vars + 1 ∧
      sm.scratch.scratch_buf = s0.scratch.scratch_buf ∧
      sm.scratch.res_sz = BitVec.ofNat 64 best_k.toNat ∧
      sm.core.fuel = s0.core.fuel ∧
      sm.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
      sm.scratch.tarjan_reach = s0.scratch.tarjan_reach ∧
      (FullMem c sm ⋆ R) mm)
    (fun J2 hJ2 => by
      c0_hfast
      exact hJ2 (0#32, dd1, ok1, 0#64, 0#64, s) mp
        ⟨Nat.zero_le _, hinv, hext0, hcv_eq, hsb_eq, hres, hfuel, htm, htr, hmp⟩)
    (fun J2 (mi, dd, ok, ga, ir, sm) mm
        ⟨hmi_le, hinv_m, hext_m, hcv_m, hsb_m, hrs_m, hfl_m, htm_m, htr_m, hmm⟩ ihm => ?_)
  clear hmp
  c0_hfast_nogrp
  rotate_left 1
  · c0_hfast
    exact hExit mi dd ok ga ir sm mm hinv_m hext_m hcv_m hsb_m hrs_m hfl_m htm_m htr_m hmm
  · c0_hfast
    exact hExit mi dd ok ga ir sm mm hinv_m hext_m hcv_m hsb_m hrs_m hfl_m htm_m htr_m hmm
  have hmi_lt : mi.toNat < mn.toNat := by assumption
  have hsm_sb_l := hinv_m.1.scratch_ok.scratch_buf_len
  have hbro_mi : (BitVec.setWidth 64 (brow_off + mi)).toNat < sm.scratch.scratch_buf.length := by
    rw [fid_bv64_32, hsm_sb_l]
    have := hbk_row.2.2.2.1; have := hmat.1.2.2.2.2.1; c0_bound
  have hmi1 : (mi + 1#32).toNat = mi.toNat + 1 := by
    have := hbk_row.2.2.2.1; have := hmat.1.2.2.2.2.1; c0_bound
  c0_hfast_nogrp
  let c_top := sm.scratch.scratch_buf[(BitVec.setWidth 64 (brow_off + mi)).toNat]'hbro_mi
  have hctop_eq : c_top = s0.scratch.scratch_buf[brow_off.toNat + mi.toNat]?.getD 0#32 := by
    have hi : (BitVec.setWidth 64 (brow_off + mi)).toNat = brow_off.toNat + mi.toNat := by
      rw [fid_bv64_32]; have := hbk_row.2.2.2.1; have := hmat.1.2.2.2.2.1; c0_bound
    dsimp only [c_top]
    rw [← hi, List.getElem?_eq_getElem (by rw [← hsb_m]; exact hbro_mi), Option.getD_some]
    simp only [hsb_m]
  obtain ⟨res, hres_lt, hres_nd, hres_ok, hres_ent⟩ := hrow_res mi.toNat hmi_lt
  rw [← hctop_eq] at hres_ok
  refine wp_join_state (α := Bool × Bool × BitVec 64 × BitVec 64 × FullState)
    (fun x => (x.1, x.2.1, x.2.2.1, x.2.2.2.1, ()))
    (fun (_, _, _, _, sm') mm' =>
      FullDenseInvW c F0 F_next sm' ∧ CommitArenaExt s0 sm' ∧
      sm'.core.cur_vars = s0.core.cur_vars + 1 ∧ sm'.scratch.scratch_buf = s0.scratch.scratch_buf ∧
      sm'.scratch.res_sz = BitVec.ofNat 64 best_k.toNat ∧ sm'.core.fuel = s0.core.fuel ∧
      sm'.scratch.tarjan_mark = s0.scratch.tarjan_mark ∧
      sm'.scratch.tarjan_reach = s0.scratch.tarjan_reach ∧ (FullMem c sm' ⋆ R) mm')
    (fun _ (dd', ok', ga', ir', sm') mm' ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ => by
      c0_hfast; exact ihm (mi + 1#32, dd', ok', ga', ir', sm') mm' (by dsimp only; rw [hmi1]; omega)
        ⟨by rw [hmi1]; omega, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩)
    (fun Jbr hJbr => ?_)
  have h1 : (BitVec.setWidth 64 (brow_off + mi)).toNat =
      (brow_off.toNat + mi.toNat) % 2 ^ 32 := by rw [fid_bv64_32, BitVec.toNat_add]
  have hct_hc : c_top = sm.scratch.scratch_buf[(brow_off.toNat + mi.toNat) % 2 ^ 32]'(by
      rw [← h1]; exact hbro_mi) := by dsimp only [c_top]; exact cmt2_getElem_eq h1
  have hnf_wv : ((BitVec.setWidth 64 (((cv64.setWidth 32) <<< (1 : BitVec 32)) ^^^ 1#32) <<<
      (1 : Nat)) + 1#64).toNat < sm.core.wvec.length := by
    rw [hinv_m.1.core_ok.wvec_len, BitVec.toNat_add, BitVec.toNat_shiftLeft, fid_bv64_32,
      hfresh1_nat, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  c0_hfast_nogrp
  · -- Binary branch
    have hbin : (c_top &&& 0x80000000#32) ≠ 0#32 := by rw [hct_hc]; exact hc
    unfold FidBvaRowEntryOk at hres_ok; rw [ite_eq_left hbin] at hres_ok
    obtain ⟨hq_lt, hres_q, _⟩ := hres_ok
    exact cmt_phase2_bin_wp (best_k := best_k) (sc := sc) (brow_off := brow_off) (mn := mn)
      (si := si) (dd0 := dd0) (dd1 := dd1) (ok1 := ok1) (J_p2 := J_p2) (mi := mi) (dd := dd)
      (ok := ok) (ga := ga) (ir := ir) (c_top := c_top) (Jbr := Jbr) hAddBin hinv_m hext_m
      hcv_m hcv64 hsb_m hrs_m hfl_m htm_m htr_m hq_lt (by rwa [hres_q] at hres_ent) hmm hExit
      fun dd' ok' ga' ir' sm' mm' h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
        hJbr (dd', ok', ga', ir', sm') mm' ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  · -- Large clause branch
    have hnb : (c_top &&& 0x80000000#32) = 0#32 := by rw [hct_hc]; exact hc
    unfold FidBvaRowEntryOk at hres_ok; rw [ite_eq_right (fun h => h hnb)] at hres_ok
    obtain ⟨hct_ref0, hct_ng0, hct_ge3, hct_le5, hflit_mem, hperm_f, hperm_c⟩ := hres_ok
    have hct_ref : c_top.toNat ∈ fullArenaClauseRefs sm := hext_m.2.2 _ hct_ref0
    have hct_wf0 := hw0.arena.refs_wf c_top.toNat hct_ref0
    have hct_sz_eq := hext_m.old_size hw0 hct_ref0
    have hct_lits_eq := hext_m.old_lits hl0 hinv_m.1 hw0 hct_ref0
    have hct2_lt : (BitVec.setWidth 64 c_top + 2#64).toNat < sm.core.arena.length := by
      rw [hinv_m.1.core_ok.arena_len_arr]; have := hinv_m.1.core_ok.arena_len_le
      have := hext_m.1; c0_bound
    have hbk_sb_lt : (BitVec.setWidth 64 best_k).toNat < sm.scratch.scratch_buf.length := by
      rw [fid_bv64_32, hsm_sb_l]; omega
    c0_hfast_nogrp
    let csz := sm.core.arena[(BitVec.setWidth 64 c_top + 2#64).toNat]'hct2_lt
    let flit := sm.scratch.scratch_buf[(BitVec.setWidth 64 best_k).toNat]'hbk_sb_lt
    have hcsz_hc_i : (BitVec.setWidth 64 c_top + 2#64).toNat =
        ((sm.scratch.scratch_buf[(brow_off.toNat + mi.toNat) % 2 ^ 32]'(by
          rw [← h1]; exact hbro_mi)).toNat + (2 : BitVec 64).toNat) % 2 ^ 64 := by
      rw [BitVec.toNat_add, fid_bv64_32, hct_hc]; rfl
    have hcsz_hc : csz = sm.core.arena[((sm.scratch.scratch_buf[(brow_off.toNat + mi.toNat) %
        2 ^ 32]'(by rw [← h1]; exact hbro_mi)).toNat + (2 : BitVec 64).toNat) % 2 ^ 64]'(by
          rw [← hcsz_hc_i]; exact hct2_lt) := cmt2_getElem_eq hcsz_hc_i
    have hflit_hc : flit = sm.scratch.scratch_buf[best_k.toNat]'(by
        rw [← fid_bv64_32 best_k]; exact hbk_sb_lt) := cmt2_getElem_eq (fid_bv64_32 best_k)
    have hcsz_eq : csz.toNat = fullArenaClauseSize s0 c_top.toNat := by
      rw [← hct_sz_eq]; unfold fullArenaClauseSize fullArenaClauseSizeCore
      have h2 : (BitVec.setWidth 64 c_top + 2#64).toNat = c_top.toNat + 2 := by
        have := hinv_m.1.core_ok.arena_len_le; have := hext_m.1; c0_bound
      dsimp only [csz]; apply congrArg BitVec.toNat; apply Option.some.inj
      rw [← List.getElem?_eq_getElem hct2_lt, h2,
        List.getElem?_eq_getElem (by rw [hinv_m.1.core_ok.arena_len_arr]
                                     have := hinv_m.1.core_ok.arena_len_le
                                     have := hext_m.1; omega), Option.getD_some]
    have hflit_eq : flit.toNat = (s0.scratch.scratch_buf[best_k.toNat]?.getD 0#32).toNat := by
      dsimp only [flit]; apply congrArg BitVec.toNat; apply Option.some.inj
      rw [← List.getElem?_eq_getElem hbk_sb_lt, fid_bv64_32, hsb_m,
        List.getElem?_eq_getElem (by rw [hl0.scratch_ok.scratch_buf_len]; omega), Option.getD_some]
    have hcsz_lits : (fullArenaClauseLits s0 c_top.toNat).length = csz.toNat := by
      rw [hcsz_eq]; unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSize
      simp only [List.length_map, List.length_take, List.length_drop]
      have := hct_wf0.1; have := hl0.core_ok.arena_len_arr; have := hl0.core_ok.arena_len_le
      omega
    have hcsz_le_cv : csz.toNat ≤ s0.core.cur_vars := by
      have hnd_all := hinv_m.2.2.2.1 c_top.toNat hct_ref
        (by rw [hext_m.old_garb hw0 hct_ref0]; exact hct_ng0)
      rw [hct_lits_eq] at hnd_all
      have hall_lt : ∀ x ∈ fullArenaClauseLits s0 c_top.toNat, x < 2 * s0.core.cur_vars :=
        hw0.arena.lits_lt c_top.toNat hct_ref0 hct_ng0
      have := cmt_nodup_lt_le (n := s0.core.cur_vars) hnd_all (fun v hv => by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hv; have := hall_lt x hx; omega)
      rw [List.length_map, hcsz_lits] at this; exact this
    -- Pure read-only `if (!defrag_dirty)` loop over `dj < csz`
    refine wp_join_state1 (t := .bool) (α := Bool) (fun x => x) (fun _ m' => m' = mm)
      (fun _ dd_a m' hm' => ?_)
      (fun Jdd hJdd => by
        c0_hfast_nogrp
        · c0_hfast; exact hJdd dd mm rfl
        · c0_hfast_nogrp
          refine wp_join_state1 (t := i64) (α := BitVec 64) (fun x => x) (fun _ m' => m' = mm)
            (fun _ sum0 m' hm' => by
              rw [hm']
              refine wp_while_state (α := BitVec 64 × BitVec 32) (fun x => (x.1, x.2, ()))
                (fun x => csz.toNat - x.2.toNat)
                (fun (_, dj) m' => dj.toNat ≤ csz.toNat ∧ m' = mm)
                (fun Jdj hJdj => by c0_hfast; exact hJdj (sum0, 0#32) mm ⟨Nat.zero_le _, rfl⟩)
                (fun Jdj (snw, dj) m' ⟨hdj_le, hm'⟩ ihdj => by
                  rw [hm']; c0_hfast_nogrp
                  · have hdj_lt : dj.toNat < csz.toNat := by rw [hcsz_hc]; exact hc
                    have hdj_ar : (BitVec.setWidth 64 c_top + 3#64 +
                        BitVec.setWidth 64 dj).toNat < sm.core.arena.length := by
                      rw [hinv_m.1.core_ok.arena_len_arr]
                      have := hct_wf0.1; have := hcsz_eq; unfold fullArenaClauseSize at *
                      have := hinv_m.1.core_ok.arena_len_le; have := hext_m.1; c0_bound
                    have hdl_lt : (sm.core.arena[(BitVec.setWidth 64 c_top + 3#64 +
                        BitVec.setWidth 64 dj).toNat]'hdj_ar).toNat < 2 * s0.core.cur_vars := by
                      have hi : (BitVec.setWidth 64 c_top + 3#64 + BitVec.setWidth 64 dj).toNat =
                          c_top.toNat + 3 + dj.toNat := by
                        have := hct_wf0.1; have := hcsz_eq; unfold fullArenaClauseSize at *
                        have := hinv_m.1.core_ok.arena_len_le; have := hext_m.1; c0_bound
                      have h1 := fullArenaClauseLitsCore_getElem (k := sm.core) (r := c_top.toNat)
                        (j := dj.toNat)
                        (by change dj.toNat < fullArenaClauseSize sm c_top.toNat
                            rw [hct_sz_eq, ← hcsz_eq]; exact hdj_lt)
                        (by rw [← hi]; exact hdj_ar)
                      have hmem : (sm.core.arena[(BitVec.setWidth 64 c_top + 3#64 +
                          BitVec.setWidth 64 dj).toNat]'hdj_ar).toNat ∈
                          fullArenaClauseLits s0 c_top.toNat := by
                        rw [← hct_lits_eq]; apply List.mem_of_getElem?
                        rw [show sm.core.arena[(BitVec.setWidth 64 c_top + 3#64 +
                            BitVec.setWidth 64 dj).toNat]'hdj_ar =
                          sm.core.arena[c_top.toNat + 3 + dj.toNat]'(by rw [← hi]; exact hdj_ar)
                          from cmt2_getElem_eq hi]
                        exact h1
                      exact hw0.arena.lits_lt c_top.toNat hct_ref0 hct_ng0 _ hmem
                    have hdl_wv : ((BitVec.setWidth 64 (sm.core.arena[(BitVec.setWidth 64 c_top +
                        3#64 + BitVec.setWidth 64 dj).toNat]'hdj_ar) <<< (1 : Nat)) +
                        1#64).toNat < sm.core.wvec.length := by
                      rw [hinv_m.1.core_ok.wvec_len, BitVec.toNat_add, BitVec.toNat_shiftLeft,
                        fid_bv64_32, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.shiftLeft_eq]
                      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega
                    have hdj1 : (dj + 1#32).toNat = dj.toNat + 1 := by c0_bound
                    c0_hfast_nogrp
                    refine wp_join_state1 (t := i64) (α := BitVec 64) (fun x => x)
                      (fun _ m'' => m'' = mm)
                      (fun _ snw' m'' hm'' => by
                        rw [hm'']; c0_hfast
                        exact ihdj (snw', dj + 1#32) mm (by dsimp only; rw [hdj1]; omega)
                          ⟨by rw [hdj1]; omega, rfl⟩)
                      (fun Jsn hJsn => by
                        c0_hfast_nogrp
                        · refine wp_join_state1 (t := i64) (α := BitVec 64) (fun x => x)
                            (fun _ m'' => m'' = mm)
                            (fun _ addl m'' hm'' => by
                              rw [hm'']
                              exact head_wp_add rfl rfl (head_wp_jump rfl rfl
                                (hJsn (snw + addl) mm rfl)))
                            (fun Jad hJad => by
                              c0_hfast_nogrp
                              · exact hJad 2#64 mm rfl
                              · refine wp_join_state1 (t := i64) (α := BitVec 64) (fun x => x)
                                  (fun _ m'' => m'' = mm)
                                  (fun _ a2 m'' hm'' => by
                                    rw [hm'']; exact head_wp_jump rfl rfl (hJad a2 mm rfl))
                                  (fun Ja2 hJa2 => by
                                    refine head_wp_cmp_eq rfl rfl (head_wp_jnz rfl ?_ ?_)
                                    · intro _; exact head_wp_jump rfl rfl (hJa2 3#64 mm rfl)
                                    · intro _
                                      refine head_wp_sext rfl (by decide) ?_
                                      refine head_wp_shl rfl rfl ?_
                                      exact head_wp_jump rfl rfl (hJa2 _ mm rfl)))
                        · exact hJsn snw mm rfl)
                  · refine wp_join_state1 (t := .bool) (α := Bool) (fun x => x)
                      (fun _ m'' => m'' = mm)
                      (fun _ ddi m'' hm'' => by
                        rw [hm'']; exact head_wp_jump rfl rfl (hJdd ddi mm rfl))
                      (fun Jdi hJdi => by
                        c0_hfast_nogrp
                        · exact hJdi true mm rfl
                        · exact hJdi true mm rfl
                        · exact hJdi true mm rfl
                        · refine wp_join0 (fun m'' => m'' = mm)
                            (fun _ m'' hm'' => by
                              rw [hm'']; c0_hfast_nogrp
                              · exact hJdi true mm rfl
                              · exact hJdi dd mm rfl)
                            (fun Jef hJef => by
                              c0_hfast_nogrp
                              · exact hJef mm rfl
                              · exact hJef mm rfl
                              · exact hJdi dd mm rfl))))
            (fun Js0 hJs0 => by
              c0_hfast_nogrp
              · exact hJs0 2#64 mm rfl
              · refine wp_join_state1 (t := i64) (α := BitVec 64) (fun x => x)
                  (fun _ m' => m' = mm)
                  (fun _ a2 m' hm' => by rw [hm']; exact head_wp_jump rfl rfl (hJs0 a2 mm rfl))
                  (fun Ja2 hJa2 => by
                    c0_hfast_nogrp
                    · exact hJa2 3#64 mm rfl
                    · exact hJa2 _ mm rfl)))
    rw [hm']
    have htmp0 : (0 : Nat) < sm.core.tmp.length := by rw [hinv_m.1.core_ok.tmp_len_arr]; omega
    c0_hfast_nogrp
    -- `tmp[0] = fresh ^ 1` then `while (j < csz)` fill `tmp[1..tk)`
    refine wp_while_state (α := BitVec 32 × BitVec 32 × List (BitVec 32))
      (fun x => (x.1, x.2.1, ()))
      (fun x => csz.toNat - x.2.1.toNat)
      (fun (tk, j, tmp_j) mt =>
        j.toNat ≤ csz.toNat ∧ tmp_j.length = c.max_vars ∧
        tk.toNat = 1 + (((fullArenaClauseLits s0 c_top.toNat).take j.toNat).filter
          (· != flit.toNat)).length ∧
        (tmp_j.take tk.toNat).map BitVec.toNat =
          (2 * s0.core.cur_vars + 1) ::
            (((fullArenaClauseLits s0 c_top.toNat).take j.toNat).filter (· != flit.toNat)) ∧
        (FullMem c { sm with core := { sm.core with tmp := tmp_j } } ⋆ R) mt)
      (fun Jt hJt => by
        c0_hfast
        refine hJt (1#32, 0#32, _) m ⟨Nat.zero_le _, by simp [hinv_m.1.core_ok.tmp_len_arr],
          by simp, ?_, hm⟩
        rw [show (1#32 : BitVec 32).toNat = 1 from rfl,
          show (0#32 : BitVec 32).toNat = 0 from rfl,
          show (BitVec.ofNat 64 0).toNat = 0 from rfl,
          List.take_zero, List.filter_nil,
          cmt_take_set_succ _ _ htmp0, List.take_zero, List.nil_append, List.map_singleton]
        exact congrArg (· :: []) hfresh1_nat)
      (fun Jt (tk, j, tmp_j) mt ⟨hj_le, htmp_l, htk_eq, htmp_eq, hmt⟩ iht => ?_)
    c0_hfast_nogrp
    · have hj_lt : j.toNat < csz.toNat := by rw [hcsz_hc]; exact hc
      have hj_ar : (BitVec.setWidth 64 c_top + 3#64 + BitVec.setWidth 64 j).toNat <
          sm.core.arena.length := by
        rw [hinv_m.1.core_ok.arena_len_arr]
        have := hct_wf0.1; have := hcsz_eq; unfold fullArenaClauseSize at *
        have := hinv_m.1.core_ok.arena_len_le; have := hext_m.1; c0_bound
      have hj1 : (j + 1#32).toNat = j.toNat + 1 := by c0_bound
      have htk_le : tk.toNat ≤ 1 + j.toNat := by
        have hfl := List.length_filter_le (· != flit.toNat)
          ((fullArenaClauseLits s0 c_top.toNat).take j.toNat)
        have htl : ((fullArenaClauseLits s0 c_top.toNat).take j.toNat).length ≤ j.toNat :=
          List.length_take_le _ _
        omega
      c0_hfast_nogrp
      let lj := sm.core.arena[(BitVec.setWidth 64 c_top + 3#64 + BitVec.setWidth 64 j).toNat]'hj_ar
      have hlj_eq : lj.toNat = (fullArenaClauseLits s0 c_top.toNat)[j.toNat]'(by omega) := by
        have hi : (BitVec.setWidth 64 c_top + 3#64 + BitVec.setWidth 64 j).toNat =
            c_top.toNat + 3 + j.toNat := by
          have := hct_wf0.1; have := hcsz_eq; unfold fullArenaClauseSize at *
          have := hinv_m.1.core_ok.arena_len_le; have := hext_m.1; c0_bound
        have h1 := fullArenaClauseLitsCore_getElem (k := sm.core) (r := c_top.toNat)
          (j := j.toNat)
          (by change j.toNat < fullArenaClauseSize sm c_top.toNat
              rw [hct_sz_eq, ← hcsz_eq]; exact hj_lt)
          (by rw [← hi]; exact hj_ar)
        apply Option.some.inj
        rw [← List.getElem?_eq_getElem (by omega), ← hct_lits_eq]
        change some lj.toNat = (fullArenaClauseLitsCore sm.core c_top.toNat)[j.toNat]?
        rw [h1]; dsimp only [lj]; congr 2; exact cmt2_getElem_eq hi
      have hlj_hc_i : (BitVec.setWidth 64 c_top + 3#64 + BitVec.setWidth 64 j).toNat =
          ((sm.scratch.scratch_buf[(brow_off.toNat + mi.toNat) % 2 ^ 32]'(by
            rw [← h1]; exact hbro_mi)).toNat + 3 + j.toNat) % 2 ^ 64 := by
        rw [BitVec.toNat_add, BitVec.toNat_add, fid_bv64_32, fid_bv64_32, hct_hc]; c0_bound
      have hlj_hc : lj = sm.core.arena[((sm.scratch.scratch_buf[(brow_off.toNat + mi.toNat) %
          2 ^ 32]'(by rw [← h1]; exact hbro_mi)).toNat + 3 + j.toNat) % 2 ^ 64]'(by
            rw [← hlj_hc_i]; exact hj_ar) := by
        dsimp only [lj]; exact cmt2_getElem_eq hlj_hc_i
      refine wp_join_state1 (t := i32) (α := BitVec 32 × List (BitVec 32)) (fun x => x.1)
        (fun (tk', tmp') mt' =>
          tmp'.length = c.max_vars ∧
          tk'.toNat = 1 + (((fullArenaClauseLits s0 c_top.toNat).take (j.toNat + 1)).filter
            (· != flit.toNat)).length ∧
          (tmp'.take tk'.toNat).map BitVec.toNat =
            (2 * s0.core.cur_vars + 1) ::
              (((fullArenaClauseLits s0 c_top.toNat).take (j.toNat + 1)).filter (· != flit.toNat)) ∧
          (FullMem c { sm with core := { sm.core with tmp := tmp' } } ⋆ R) mt')
        (fun _ (tk', tmp') mt' ⟨h1, h2, h3, h4⟩ => by
          c0_hfast
          exact iht (tk', j + 1#32, tmp') mt' (by dsimp only; rw [hj1]; omega)
            ⟨by rw [hj1]; omega, h1, by rw [hj1]; exact h2, by rw [hj1]; exact h3, h4⟩)
        (fun Jtk hJtk => by
          c0_hfast_nogrp
          · have hne : lj ≠ flit := by rw [hlj_hc, hflit_hc]; exact hc
            have hne_b : (lj.toNat != flit.toNat) = true := by
              simp [bne_iff_ne]; intro h; exact hne (BitVec.eq_of_toNat_eq h)
            have htk_lt : (BitVec.setWidth 64 tk).toNat < tmp_j.length := by
              rw [fid_bv64_32, htmp_l]; omega
            have htk1 : (tk + 1#32).toNat = tk.toNat + 1 := by c0_bound
            c0_hfast; dsimp only at hm
            have hft := cmt_filter_take_succ (· != flit.toNat) (fullArenaClauseLits s0 c_top.toNat)
              (by omega : j.toNat < _)
            rw [← hlj_eq, hne_b] at hft; simp only [↓reduceIte] at hft
            refine hJtk (tk + 1#32, _) m ⟨by simp [htmp_l], ?_, ?_, hm⟩
            · rw [htk1, hft, List.length_append, List.length_singleton]; omega
            · rw [htk1, hft, fid_bv64_32,
                cmt_take_set_succ tmp_j _ (by rwa [fid_bv64_32] at htk_lt),
                List.map_append, List.map_singleton, htmp_eq]; rfl
          · have heq : lj = flit := by rw [hlj_hc, hflit_hc]; exact hc
            have heq_b : (lj.toNat != flit.toNat) = false := by simp [heq]
            have hft := cmt_filter_take_succ (· != flit.toNat) (fullArenaClauseLits s0 c_top.toNat)
              (by omega : j.toNat < _)
            rw [← hlj_eq, heq_b] at hft
            simp only [Bool.false_eq_true, ↓reduceIte, List.append_nil] at hft
            c0_hfast
            exact hJtk (tk, tmp_j) mt ⟨htmp_l, by rw [hft]; exact htk_eq,
              by rw [hft]; exact htmp_eq, hmt⟩)
    -- Exited `j < csz` loop: `j = csz`
    have hj_eq : j.toNat = csz.toNat := by
      have hnot : ¬ (j.toNat < csz.toNat) := by rw [hcsz_hc]; exact hc
      omega
    rw [hj_eq, ← hcsz_lits, List.take_length] at htk_eq htmp_eq
    rw [← hflit_eq] at hperm_f hperm_c
    obtain ⟨htk_ge3, htk_le_mx, htmp_lits_lt, htmp_lits_nd, htmp_lits_ent⟩ :=
      cmt_tmp_build_ok hfv_lt hres_lt hres_nd hres_ent hct_ge3
        (by unfold fullArenaClauseSize
            have := hct_wf0.1; have := hl0.core_ok.arena_len_arr
            have := hl0.core_ok.arena_len_le; omega)
        hperm_f hperm_c htmp_l htk_eq htmp_eq
    let sm_t : FullState := { sm with core := { sm.core with tmp := tmp_j } }
    have hinv_t : FullDenseInvW c F0 F_next sm_t := cmt_fullDenseInvW_set_tmp hinv_m htmp_l
    have hext_t : CommitArenaExt s0 sm_t := hext_m.of_eq rfl rfl
    fid_call hAllocCl
    refine ⟨c, sm_t, R, rfl, hinv_t.1, hmt, ?_⟩
    split
    · c0_hfast_nogrp
      · c0_hfast
        exact hExit mi dd_a false ga ir sm_t mt hinv_t hext_t hcv_m hsb_m hrs_m hfl_m htm_m
          htr_m hmt
      · exact absurd rfl hc
    · rename_i hcap_ok
      intro ar_a ma; dsimp only; intro hlen_a hhold_a hnoshrk_a hnogarb_a _ hsz_a hma
      have hncr_lt : sm_t.core.arena_len < 0xFFFFFFFF := by
        have := hinv_t.1.core_ok.arena_len_le; omega
      have hncr_ne : BitVec.ofNat 64 sm_t.core.arena_len ≠ 0xFFFFFFFF#64 := by
        intro h; have := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by decide)] at this; omega
      c0_hfast_nogrp
      · exfalso; apply hncr_ne
        (first | assumption | exact Eq.symm (by assumption))
      · exact cmt_phase2_large_tail_wp (best_k := best_k) (sc := sc) (brow_off := brow_off)
          (mn := mn) (si := si) (dd0 := dd0) (cv64 := cv64) (dd1 := dd1) (ok1 := ok1)
          (J_p2 := J_p2) (mi := mi) (dd := dd) (ok := ok) (ga := ga) (ir := ir) (c_top := c_top)
          (Jbr := Jbr) (csz := csz) (flit := flit) (dd_a := dd_a) (tk := tk) (j := j)
          hWatchPush hUnwatch hinv_t hext_t hcv_m hsb_m hrs_m hfl_m htm_m htr_m
          htk_ge3 htk_le_mx htmp_lits_lt htmp_lits_nd htmp_lits_ent
          hlen_a.core_ok.arena_len_arr (by dsimp only [Arg.val] at hcap_ok; omega)
          hhold_a hnoshrk_a hnogarb_a hsz_a hma
          fun dd' ok' ga' ir' sm' mm' h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
            hJbr (dd', ok', ga', ir', sm') mm' ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Factor
