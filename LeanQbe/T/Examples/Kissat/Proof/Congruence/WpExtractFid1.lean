/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.Arena.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Congruence.Inv
public import LeanQbe.T.Examples.Kissat.Proof.Congruence.Spec
public import LeanQbe.T.Examples.Kissat.Src.Congruence
import LeanQbe.T.Logic.ControlComb

/-!
# Congruence Two-Pass Extraction WP Proof (`WpExtractFid1`)

Canonical `Func.wp` proof for `full_cong_extract_from_fid`:
- Pass 1 scans the arena, extracting narrow AND (`≤ 64`), ternary XOR/ITE (`usz = 3`), and
  XOR-k (`k = 4..5`) gates while recording wide (`66 ≤ usz ≤ 1,000,001`) clause refs in `red_refs`.
- Pass 2 extracts wide AND gates (`≤ 1,000,000`) from the recorded `red_refs`.
-/

set_option autoImplicit false

namespace LeanQbe.T.Examples.Kissat.Proof.Congruence

open Std.Sat
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Src.Congruence
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Congruence.Spec
open Kraken.Bedrock2.Test

open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Congruence.CongTactics

/-! ## 1. Local Guard Macros & Pure Helpers -/

local macro "ef_if " t:term : tactic =>
  `(tactic| (c0_hstraight!; c0_hsplit; rotate_left; next => c0_hstraight!; exact $t))

local macro "ef_unless " t:term : tactic =>
  `(tactic| (c0_hstraight!; c0_hsplit; next => c0_hstraight!; exact $t))

private theorem ef_join_inline {Γ : Env} {rs ts : List Ty} {Q : Post rs} {X : XPost} {m : Mem 64}
    {body : Tup Val ts → Expr Val Cont rs} {entry : Tup Cont [ts] → Expr Val Cont rs}
    (h : ∀ J : Cont ts, (∀ xs m', wp Γ Q X (body xs) m' → J xs m') →
      wp Γ Q X (entry (J, ())) m) :
    wp Γ Q X (Expr.group (fun _ => Blocks.cons body Blocks.nil) entry) m :=
  wp_join_group (fun xs m' => wp Γ Q X (body xs) m') (fun _ _ _ hp => hp) h

private theorem ef_core_fields_of_tmp_lm {a b : FullCoreState}
    (h : { a with tmp := b.tmp, lit_mark := b.lit_mark } = b) :
    a.inconsistent = b.inconsistent ∧ a.arena = b.arena ∧ a.arena_len = b.arena_len ∧
    a.cur_vars = b.cur_vars ∧ a.cur_level = b.cur_level ∧ a.dense_mode = b.dense_mode ∧
    a.fuel = b.fuel ∧ a.repr = b.repr ∧
    ({ b with tmp := a.tmp, lit_mark := a.lit_mark } : FullCoreState) = a := by
  cases a; cases b; cases h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem ef_scr_fields_of_buf {a b : FullScratch}
    (h : { a with scratch_buf := b.scratch_buf } = b) :
    a.last_learned = b.last_learned ∧ a.extend_len = b.extend_len ∧ a.red_refs = b.red_refs := by
  cases a; cases b; cases h; exact ⟨rfl, rfl, rfl⟩

private theorem ef_denseInvW_of_xorK {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s s' : FullState} (hd : FullDenseInvW c F0 F_cur s)
    (hlen' : s'.LengthsOk c)
    (hce : { s'.core with tmp := s.core.tmp, lit_mark := s.core.lit_mark } = s.core)
    (hse : { s'.scratch with scratch_buf := s.scratch.scratch_buf } = s.scratch)
    (hmk' : FullLitMarksClear c s') :
    FullDenseInvW c F0 F_cur s' := by
  obtain ⟨_, har, hal, _, hcl, hdm, _, _, hkeq⟩ := ef_core_fields_of_tmp_lm hce
  obtain ⟨hll, hext, _⟩ := ef_scr_fields_of_buf hse
  have hnd' := fullArenaVarsNodup_of_eq hd.2.2.2.1 har hal
  have hext' := fullExtScratchOk_of_eq hd.2.2.2.2.1 har hal hll hext
  have hw_tm : FullWitnessInv c F0 F_cur
      { s.core with tmp := s'.core.tmp, lit_mark := s'.core.lit_mark } :=
    { hd.2.1 with
      arena := { hd.2.1.arena with len_ok := hd.2.1.arena.len_ok }
      watches := hd.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ hr => hr) }
  exact ⟨hlen', hkeq ▸ hw_tm, hmk', hnd', hext', hcl.trans hd.2.2.2.2.2.1, hdm ▸ hd.2.2.2.2.2.2⟩

private theorem ef_nodup_getElem_inj {α : Type _} :
    ∀ {l : List α}, l.Nodup → ∀ i j : Nat, (hi : i < l.length) → (hj : j < l.length) →
      l[i]'hi = l[j]'hj → i = j
  | [], _, i, _, hi, _, _ => absurd hi (Nat.not_lt_zero i)
  | _ :: _, _, 0, 0, _, _, _ => rfl
  | x :: xs, hnd, 0, j + 1, _, hj, heq => by
    have hcons := List.nodup_cons.mp hnd
    have hmem : xs[j]'(by simp at hj; omega) ∈ xs := List.getElem_mem _
    have hx : x = xs[j]'(by simp at hj; omega) := by simpa using heq
    exact absurd (hx ▸ hmem) hcons.1
  | x :: xs, hnd, i + 1, 0, hi, _, heq => by
    have hcons := List.nodup_cons.mp hnd
    have hmem : xs[i]'(by simp at hi; omega) ∈ xs := List.getElem_mem _
    have hx : x = xs[i]'(by simp at hi; omega) := by simpa using heq.symm
    exact absurd (hx ▸ hmem) hcons.1
  | _ :: xs, hnd, i + 1, j + 1, hi, hj, heq => by
    have hcons := List.nodup_cons.mp hnd
    exact congrArg Nat.succ (ef_nodup_getElem_inj hcons.2 i j (by simp at hi; omega)
      (by simp at hj; omega) heq)

private theorem ef_nodup_map_on {α β : Type _} {f : α → β} :
    ∀ {l : List α}, l.Nodup → (∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) → (l.map f).Nodup
  | [], _, _ => .nil
  | a :: xs, hnd, hinj => by
    have hcons := List.nodup_cons.mp hnd
    rw [List.map_cons, List.nodup_cons]
    refine ⟨fun hmem => ?_, ef_nodup_map_on hcons.2 fun x hx y hy hxy =>
      hinj x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) hxy⟩
    rw [List.mem_map] at hmem; obtain ⟨b, hb, hfb⟩ := hmem
    have hba := hinj b (List.mem_cons_of_mem _ hb) a List.mem_cons_self hfb
    exact hcons.1 (hba ▸ hb)

private theorem ef_list_nodup_filter_map (f : Nat → Nat) {idxs : List Nat}
    {ar : List (BitVec 32)} {sz p : Nat}
    (hnd : ((List.range sz).map fun q => (ar[p + 3 + q]?.getD 0#32).toNat / 2).Nodup)
    (hid_nd : idxs.Nodup) (hid_lt : ∀ q ∈ idxs, q < sz)
    (hf : ∀ q, f q = (ar[p + 3 + q]?.getD 0#32).toNat / 2) :
    (idxs.map f).Nodup := by
  refine ef_nodup_map_on hid_nd fun a ha b hb hab => ?_
  rw [hf a, hf b] at hab
  have ha_s := hid_lt a ha; have hb_s := hid_lt b hb
  exact ef_nodup_getElem_inj hnd a b (by simp; omega) (by simp; omega)
    (by simpa [List.getElem_map] using hab)

private theorem ef_nat_xor1_mod2 (n : Nat) : (n ^^^ 1) % 2 = (n % 2) ^^^ 1 := by
  apply Nat.eq_of_testBit_eq; intro k
  cases k with
  | zero => simp [Nat.testBit_zero]
  | succ k =>
    have hlt : (n % 2) ^^^ 1 < 2 := by
      rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]
    simp [Nat.testBit_succ, Nat.div_eq_of_lt hlt]

private theorem ef_bv32_bit1_ne0_mod2 {l neg_p : BitVec 32} :
    ((if (l &&& 1#32) != 0#32 then neg_p ^^^ 1#32 else neg_p) &&& 1#32).toNat =
      (neg_p &&& 1#32).toNat ^^^ (l.toNat % 2) := by
  have hl1 : (l &&& 1#32).toNat = l.toNat % 2 := by
    rw [BitVec.toNat_and, show (1#32 : BitVec 32).toNat = 1 from rfl]
    exact Nat.and_one_is_mod l.toNat
  rcases Nat.mod_two_eq_zero_or_one l.toNat with hm | hm
  · have hb : (l &&& 1#32) = 0#32 := BitVec.eq_of_toNat_eq (by rw [hl1, hm]; rfl)
    simp [hb, hm]
  · have hb : (l &&& 1#32) = 1#32 := BitVec.eq_of_toNat_eq (by rw [hl1, hm]; rfl)
    have hne1 : ((1#32 : BitVec 32) != 0#32) = true := rfl
    simp only [hb, hne1, ↓reduceIte]
    rw [BitVec.toNat_and, BitVec.toNat_and, BitVec.toNat_xor,
      show (1#32 : BitVec 32).toNat = 1 from rfl,
      Nat.and_one_is_mod, Nat.and_one_is_mod, hm, ef_nat_xor1_mod2]

private theorem ef_clause_collect_done {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {sp : FullState} {p sz_n usz_n : Nat} {ws2 : List (BitVec 32)} {idxs : List Nat}
    (hdp : FullDenseInvW c F0 F_cur sp)
    (hp_ref : p ∈ fullArenaClauseRefsCore sp.core)
    (hng : fullArenaClauseGarb sp p = false)
    (hsz_eq : fullArenaClauseSizeCore sp.core p = sz_n)
    (hbd_sz : p + 3 + sz_n ≤ sp.core.arena.length)
    (hws2_le : usz_n ≤ ws2.length)
    (hid_len : idxs.length = usz_n) (hid_nd : idxs.Nodup)
    (hid_lt : ∀ q ∈ idxs, q < sz_n)
    (hws2_map : ∀ j < usz_n, ws2[j]? = sp.core.arena[p + 3 + (idxs[j]?.getD 0)]?)
    (hcov_k : ∀ q < sz_n, q ∈ idxs ∨
      sp.core.vals[(sp.core.arena[p + 3 + q]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8) :
    (∀ j < usz_n, ∀ j2 < usz_n, j ≠ j2 →
      (ws2[j]?.getD 0#32).toNat / 2 ≠ (ws2[j2]?.getD 0#32).toNat / 2) ∧
    (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((List.range usz_n).map fun j => (ws2[j]?.getD 0#32).toNat)) := by
  have hcov_all : ∀ l ∈ fullArenaClauseLits sp p,
      sp.core.vals[l]?.getD 0#8 = 0xFF#8 ∨ l ∈
        ((List.range usz_n).map fun j => (ws2[j]?.getD 0#32).toNat) := by
    intro l hl
    unfold fullArenaClauseLits fullArenaClauseLitsCore at hl; rw [hsz_eq] at hl
    rw [List.mem_map] at hl; obtain ⟨bv, hbv, rfl⟩ := hl
    obtain ⟨q, hq, hget⟩ := List.mem_iff_getElem.mp hbv
    rw [List.length_take, List.length_drop, Nat.min_eq_left (by omega)] at hq
    have hbd_q : p + 3 + q < sp.core.arena.length := by omega
    rw [List.getElem_take, List.getElem_drop] at hget
    rcases hcov_k q hq with hin | hff
    · right; obtain ⟨j, hj, hgetj⟩ := List.mem_iff_getElem.mp hin
      have hj_u : j < usz_n := by omega
      have hm_j := hws2_map j hj_u
      have hid_j : (idxs[j]?.getD 0) = q := by
        rw [List.getElem?_eq_getElem hj, Option.getD_some, hgetj]
      rw [hid_j, List.getElem?_eq_getElem (by omega),
        List.getElem?_eq_getElem hbd_q, hget] at hm_j
      rw [List.mem_map]; refine ⟨j, List.mem_range.mpr hj_u, ?_⟩
      rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact congrArg BitVec.toNat (Option.some.inj hm_j)
    · left; rw [List.getElem?_eq_getElem hbd_q, Option.getD_some, hget] at hff; exact hff
  have hent_u := unassigned_clause_entails hdp.2.1 hdp.2.2.2.2.2.1 hp_ref hng hcov_all
  have hnd_u : (idxs.map fun q => (sp.core.arena[p + 3 + q]?.getD 0#32).toNat / 2).Nodup := by
    have hnd_sp := hdp.2.2.2.1 p hp_ref hng
    have har_lits : fullArenaClauseLits sp p =
        ((List.range sz_n).map fun q => (sp.core.arena[p + 3 + q]?.getD 0#32).toNat) := by
      unfold fullArenaClauseLits fullArenaClauseLitsCore; rw [hsz_eq]
      apply List.ext_getElem
      · simp only [List.length_map, List.length_take, List.length_drop, List.length_range]
        exact Nat.min_eq_left (by omega)
      · intro q hq _
        simp only [List.length_map, List.length_take, List.length_drop] at hq
        rw [Nat.min_eq_left (by omega)] at hq
        have hbd_q : p + 3 + q < sp.core.arena.length := by omega
        simp only [List.getElem_map, List.getElem_take, List.getElem_drop, List.getElem_range]
        rw [List.getElem?_eq_getElem hbd_q, Option.getD_some]
    rw [har_lits, List.map_map] at hnd_sp
    exact ef_list_nodup_filter_map (fun q => (sp.core.arena[p + 3 + q]?.getD 0#32).toNat / 2)
      hnd_sp hid_nd hid_lt (fun _ => rfl)
  refine ⟨fun j hj j2 hj2 hne => ?_, hent_u⟩
  rw [hws2_map j hj, hws2_map j2 hj2]
  have hind := ef_nodup_getElem_inj hnd_u j j2 (by simp [hid_len, hj]) (by simp [hid_len, hj2])
  intro heq
  have hij1 : idxs[j]?.getD 0 = idxs[j]'(by simp [hid_len, hj]) := by
    rw [List.getElem?_eq_getElem (by simp [hid_len, hj]), Option.getD_some]
  have hij2 : idxs[j2]?.getD 0 = idxs[j2]'(by simp [hid_len, hj2]) := by
    rw [List.getElem?_eq_getElem (by simp [hid_len, hj2]), Option.getD_some]
  rw [hij1, hij2] at heq
  exact hne (hind (by simp only [List.getElem_map]; exact heq))

private theorem ef_clause_hdr_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {sp : FullState} {p : BitVec 64}
    (hdp : FullDenseInvW c F0 F_cur sp)
    (hp_ref : p.toNat ∈ fullArenaClauseRefsCore sp.core)
    (hp_arr : p.toNat < sp.core.arena.length)
    (hp2_n : (p + 2#64).toNat = p.toNat + 2)
    (hp2_arr : (p + 2#64).toNat < sp.core.arena.length)
    (hng_red : (sp.core.arena[p.toNat]'hp_arr &&& 0x00480000#32) = 0#32) :
    fullArenaClauseGarb sp p.toNat = false ∧
    fullArenaClauseSizeCore sp.core p.toNat =
      (sp.core.arena[(p + 2#64).toNat]'hp2_arr).toNat ∧
    p.toNat + 3 + (sp.core.arena[(p + 2#64).toNat]'hp2_arr).toNat ≤ sp.core.arena.length := by
  have hp_wf := hdp.2.1.arena.refs_wf p.toNat hp_ref
  have hng : fullArenaClauseGarb sp p.toNat = false := by
    unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
    rw [List.getElem?_eq_getElem hp_arr, Option.getD_some]
    exact garb_false_of_and_480000 hng_red
  have hsz_p2 : sp.core.arena[(p + 2#64).toNat]'hp2_arr =
      sp.core.arena[p.toNat + 2]'(by omega) :=
    list_getElem_congr hp2_n hp2_arr (by omega)
  have hsz_eq : fullArenaClauseSizeCore sp.core p.toNat =
      (sp.core.arena[(p + 2#64).toNat]'hp2_arr).toNat := by
    unfold fullArenaClauseSizeCore
    rw [hsz_p2, List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hbd : p.toNat + 3 + (sp.core.arena[(p + 2#64).toNat]'hp2_arr).toNat ≤
      sp.core.arena.length := by
    have := hp_wf.2.2.1; have := hp_wf.2.2.2.1
    have := hdp.1.core_ok.arena_len_arr; have := hdp.1.core_ok.arena_len_le; omega
  exact ⟨hng, hsz_eq, hbd⟩

private theorem ef_arena_next_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s1 sp : FullState} {p : BitVec 64}
    (hd1 : FullDenseInvW c F0 F_cur s1) (hdp : FullDenseInvW c F0 F_cur sp)
    (har_p : sp.core.arena = s1.core.arena) (hal_p : sp.core.arena_len = s1.core.arena_len)
    (hp_lt : p.toNat < sp.core.arena_len)
    (hp_mem : p.toNat = s1.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefsCore s1.core) :
    let np := (BitVec.ofNat 32 (fullArenaNextOff sp.core.arena sp.core.arena_len
      (p.setWidth 32).toNat)).setWidth 64
    (p.setWidth 32).toNat = p.toNat ∧ np.toNat ≤ s1.core.arena_len ∧
    (np.toNat = s1.core.arena_len ∨ np.toNat ∈ fullArenaClauseRefsCore s1.core) ∧
    p.toNat < np.toNat := by
  intro np
  have hac := c.harena; unfold dimacsBound at hac
  have hale := hdp.1.core_ok.arena_len_le
  have hp_ref : p.toNat ∈ fullArenaClauseRefsCore sp.core := by
    have hmem := hp_mem.resolve_left (by omega)
    unfold fullArenaClauseRefsCore; rw [har_p, hal_p]; exact hmem
  have hp_wf := hdp.2.1.arena.refs_wf p.toNat hp_ref
  have hp_tr : (p.setWidth 32).toNat = p.toNat := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
  have hnp_bd := fullArenaNextOff_bounds (ar := sp.core.arena) (alen := sp.core.arena_len)
    (cref := p.toNat) hp_wf.1
  have hnp_n : np.toNat = fullArenaNextOff sp.core.arena sp.core.arena_len p.toNat := by
    dsimp only [np]; rw [hp_tr, bv_zext32_toNat, bv32_ofNat_toNat_lt (by omega)]
  refine ⟨hp_tr, by rw [hnp_n, ← hal_p]; exact hnp_bd.2, ?_, ?_⟩
  · rw [hnp_n, show fullArenaNextOff sp.core.arena sp.core.arena_len p.toNat =
      fullArenaNextOff s1.core.arena s1.core.arena_len p.toNat by rw [har_p, hal_p]]
    exact fullArenaClauseRefs_next_or_end hd1.2.1 (hp_mem.resolve_left (by omega))
  · rw [hnp_n]; have := hp_wf.2.1; have := hp_wf.2.2.1; omega

private theorem ef_arena_lit_ok {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {sp : FullState} {p : BitVec 64} {sz_bv k : BitVec 32}
    (hdp : FullDenseInvW c F0 F_cur sp)
    (hp_ref : p.toNat ∈ fullArenaClauseRefsCore sp.core)
    (hng : fullArenaClauseGarb sp p.toNat = false)
    (hsz_eq : fullArenaClauseSizeCore sp.core p.toNat = sz_bv.toNat)
    (hbd_sz : p.toNat + 3 + sz_bv.toNat ≤ sp.core.arena.length)
    (hk_lt : k.toNat < sz_bv.toNat)
    (hp3k_n : (p + 3#64 + k.setWidth 64).toNat = p.toNat + 3 + k.toNat)
    (hp3k_arr : (p + 3#64 + k.setWidth 64).toNat < sp.core.arena.length) :
    let lk := sp.core.arena[(p + 3#64 + k.setWidth 64).toNat]'hp3k_arr
    lk = sp.core.arena[p.toNat + 3 + k.toNat]'(by omega) ∧
    lk.toNat < 2 * sp.core.cur_vars ∧
    (lk.setWidth 64).toNat < sp.core.vals.length ∧
    (sp.core.vals[(lk.setWidth 64).toNat]?.getD 0#8 = 0#8 ∨
     sp.core.vals[(lk.setWidth 64).toNat]?.getD 0#8 = 1#8 ∨
     sp.core.vals[(lk.setWidth 64).toNat]?.getD 0#8 = 0xFF#8) := by
  intro lk
  have hlk_eq : lk = sp.core.arena[p.toNat + 3 + k.toNat]'(by omega) :=
    list_getElem_congr hp3k_n hp3k_arr (by omega)
  have hlk_lt : lk.toNat < 2 * sp.core.cur_vars := by
    have hmem_lk : lk.toNat ∈ fullArenaClauseLits sp p.toNat := by
      unfold fullArenaClauseLits fullArenaClauseLitsCore
      simp only [List.mem_map]; refine ⟨lk, ?_, rfl⟩
      have hget : ((sp.core.arena.drop (p.toNat + 3)).take
          (fullArenaClauseSizeCore sp.core p.toNat))[k.toNat]'(by
            simp [List.length_take, List.length_drop, hsz_eq]; omega) = lk := by
        simp [List.getElem_take, List.getElem_drop, hlk_eq]
      rw [← hget]; exact List.getElem_mem _
    exact hdp.2.1.arena.lits_lt p.toNat hp_ref hng lk.toNat hmem_lk
  have hcv_le := hdp.1.core_ok.cur_vars_le
  have hvals_l := hdp.1.core_ok.vals_len
  have hlk_v : (lk.setWidth 64).toNat < sp.core.vals.length := by
    rw [bv_zext32_toNat]; omega
  refine ⟨hlk_eq, hlk_lt, hlk_v, ?_⟩
  rw [bv_zext32_toNat]; exact hdp.2.1.vals_domain lk.toNat hlk_lt

private theorem ef_collect_append_ok {sp : FullState} {p_n k_n usz_n : Nat}
    {ws2 : List (BitVec 32)} {idxs : List Nat} {lk : BitVec 32}
    (hu_ws2 : usz_n < ws2.length) (hbd_k : p_n + 3 + k_n < sp.core.arena.length)
    (hlk_eq : lk = sp.core.arena[p_n + 3 + k_n]'hbd_k)
    (hlk_lt : lk.toNat < 2 * sp.core.cur_vars)
    (hlt_u : ∀ j < usz_n, (ws2[j]?.getD 0#32).toNat < 2 * sp.core.cur_vars)
    (hid_len : idxs.length = usz_n) (hid_nd : idxs.Nodup)
    (hid_lt : ∀ q ∈ idxs, q < k_n)
    (hws2_map : ∀ j < usz_n, ws2[j]? = sp.core.arena[p_n + 3 + (idxs[j]?.getD 0)]?)
    (hcov_k : ∀ q < k_n, q ∈ idxs ∨
      sp.core.vals[(sp.core.arena[p_n + 3 + q]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8) :
    let ws2' := ws2.set usz_n lk
    (∀ j < usz_n + 1, (ws2'[j]?.getD 0#32).toNat < 2 * sp.core.cur_vars) ∧
    (∃ idxs' : List Nat, idxs'.length = usz_n + 1 ∧ idxs'.Nodup ∧
      (∀ q ∈ idxs', q < k_n + 1) ∧
      (∀ j < usz_n + 1, ws2'[j]? = sp.core.arena[p_n + 3 + (idxs'[j]?.getD 0)]?) ∧
      (∀ q < k_n + 1, q ∈ idxs' ∨
        sp.core.vals[(sp.core.arena[p_n + 3 + q]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8)) := by
  intro ws2'; refine ⟨fun j hj => ?_, idxs ++ [k_n], by simp [hid_len], ?_, ?_, ?_, ?_⟩
  · dsimp only [ws2']; by_cases hju : j = usz_n
    · rw [hju, List.getElem?_set_self hu_ws2, Option.getD_some]; exact hlk_lt
    · rw [List.getElem?_set_ne (Ne.symm hju)]; exact hlt_u j (by omega)
  · rw [List.nodup_append]; refine ⟨hid_nd, by simp, fun q hq b hb _ => ?_⟩
    cases hb with
    | head => have := hid_lt q hq; omega
    | tail _ ht => cases ht
  · intro q hq; simp only [List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · have := hid_lt q hq; omega
    · omega
  · intro j hj; dsimp only [ws2']
    by_cases hju : j = usz_n
    · rw [hju, List.getElem?_set_self hu_ws2]
      have hid_e : (idxs ++ [k_n])[usz_n]? = some k_n := by
        rw [List.getElem?_append_right (by omega), hid_len, Nat.sub_self]; simp
      rw [hid_e, Option.getD_some, List.getElem?_eq_getElem hbd_k, hlk_eq]
    · rw [List.getElem?_set_ne (Ne.symm hju), List.getElem?_append_left (by omega)]
      exact hws2_map j (by omega)
  · intro q hq; simp only [List.mem_append, List.mem_singleton]
    by_cases hqk : q = k_n
    · rw [hqk]; exact Or.inl (Or.inr rfl)
    · rcases hcov_k q (by omega) with hin | hff
      · exact Or.inl (Or.inl hin)
      · exact Or.inr hff

private theorem ef_collect_negp_step {ws2 : List (BitVec 32)} {usz_n : Nat}
    {lk neg_p : BitVec 32} (hu_ws2 : usz_n < ws2.length)
    (hneg_u : (neg_p &&& 1#32).toNat = (List.range usz_n).foldl
      (fun acc i => acc ^^^ ((ws2[i]?.getD 0#32).toNat % 2)) 0) :
    ((if (lk &&& 1#32) != 0#32 then neg_p ^^^ 1#32 else neg_p) &&& 1#32).toNat =
      (List.range (usz_n + 1)).foldl
        (fun acc i => acc ^^^ (((ws2.set usz_n lk)[i]?.getD 0#32).toNat % 2)) 0 := by
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hfold_eq : ∀ n ≤ usz_n,
      List.foldl (fun acc i => acc ^^^ (((ws2.set usz_n lk)[i]?.getD 0#32).toNat % 2))
        0 (List.range n) =
      List.foldl (fun acc i => acc ^^^ ((ws2[i]?.getD 0#32).toNat % 2)) 0 (List.range n) := by
    intro n hn; induction n with
    | zero => rfl
    | succ n ih =>
      simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
        ih (by omega)]
      congr 2; rw [List.getElem?_set_ne (by omega)]
  rw [hfold_eq usz_n (Nat.le_refl _), ← hneg_u, List.getElem?_set_self hu_ws2, Option.getD_some]
  exact ef_bv32_bit1_ne0_mod2

private theorem ef_collect_false_ok {sp : FullState} {p_n k_n : Nat} {idxs : List Nat}
    {lk : BitVec 32} (hbd_k : p_n + 3 + k_n < sp.core.arena.length)
    (hlk_eq : lk = sp.core.arena[p_n + 3 + k_n]'hbd_k)
    (hdom : sp.core.vals[(lk.setWidth 64).toNat]?.getD 0#8 = 0#8 ∨
      sp.core.vals[(lk.setWidth 64).toNat]?.getD 0#8 = 1#8 ∨
      sp.core.vals[(lk.setWidth 64).toNat]?.getD 0#8 = 0xFF#8)
    (hnsgt : ¬ (0#32 : BitVec 32).slt
      ((sp.core.vals[(lk.setWidth 64).toNat]?.getD 0#8).signExtend 32) = true)
    (hne0 : (sp.core.vals[(lk.setWidth 64).toNat]?.getD 0#8).signExtend 32 ≠ 0#32)
    (hcov_k : ∀ q < k_n, q ∈ idxs ∨
      sp.core.vals[(sp.core.arena[p_n + 3 + q]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8) :
    ∀ q < k_n + 1, q ∈ idxs ∨
      sp.core.vals[(sp.core.arena[p_n + 3 + q]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8 := by
  intro q hq
  by_cases hqk : q = k_n
  · rw [hqk]; right
    have hk_ar : sp.core.arena[p_n + 3 + k_n]?.getD 0#32 = lk := by
      rw [List.getElem?_eq_getElem hbd_k, Option.getD_some, hlk_eq]
    rw [hk_ar, ← bv_zext32_toNat lk]
    exact bv8_ne0_not_signExtend32_sgt0_eqff hdom (bv8_ne0_of_signExtend32 hdom hne0) hnsgt
  · exact hcov_k q (by omega)

private theorem ef_rr_push_ok {s1 sp : FullState} {wn p : BitVec 64}
    (hwn_rr : wn.toNat < sp.scratch.red_refs.length)
    (hp_tr : (p.setWidth 32).toNat = p.toNat)
    (hp_ref : p.toNat ∈ fullArenaClauseRefsCore s1.core)
    (hrr_p : ∀ idx < wn.toNat,
      (sp.scratch.red_refs[idx]?.getD 0#32).toNat ∈ fullArenaClauseRefsCore s1.core) :
    ∀ idx < wn.toNat + 1,
      ((sp.scratch.red_refs.set wn.toNat (p.setWidth 32))[idx]?.getD 0#32).toNat ∈
        fullArenaClauseRefsCore s1.core := by
  intro idx hidx
  by_cases hidx_w : idx = wn.toNat
  · rw [hidx_w, List.getElem?_set_self hwn_rr, Option.getD_some, hp_tr]; exact hp_ref
  · rw [List.getElem?_set_ne (Ne.symm hidx_w)]; exact hrr_p idx (by omega)

private theorem ef_capture_ws2 {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {c : FullCfg} {sp : FullState} {ws2_new ws2' : List (BitVec 32)} {R : Mem 64 → Prop}
    {m : Mem 64} {e : Expr Val Cont rs}
    (hm : (FullMem c { sp with scratch := { sp.scratch with work_stk2 := ws2_new } } ⋆ R) m)
    (heq : ws2_new = ws2')
    (h : ∀ m_st, (FullMem c { sp with scratch := { sp.scratch with work_stk2 := ws2' } } ⋆ R) m_st →
      wp Γ Q X e m_st) :
    wp Γ Q X e m := h m (heq ▸ hm)

private theorem ef_ws2_get {ws2 ws2' : List (BitVec 32)} {i k : Nat} {hi : i < ws2'.length}
    (h : ws2' = ws2) (hik : i = k) : ws2'[i]'hi = ws2[k]?.getD 0#32 := by
  subst h; subst hik; rw [List.getElem?_eq_getElem hi, Option.getD_some]

private theorem ef_ws2_set_congr {ws2 ar : List (BitVec 32)} {u1 u2 i j : Nat}
    {hi : i < ar.length} (hj : j < ar.length) (hu : u1 = u2) (hij : i = j) :
    ws2.set u1 (ar[i]'hi) = ws2.set u2 (ar[j]'hj) := by
  rw [hu, list_getElem_congr hij hi hj]

private theorem ef_ult_eq {ar : List (BitVec 32)} {i j : Nat} {k : BitVec 32}
    {hi : i < ar.length} (hj : j < ar.length) (hij : i = j)
    (hc : k.toNat < (ar[i]'hi).toNat) : k.toNat < (ar[j]'hj).toNat := by
  rw [← list_getElem_congr hij hi hj]; exact hc

private theorem ef_nult_eq {ar : List (BitVec 32)} {i j : Nat} {k : BitVec 32}
    {hi : i < ar.length} (hj : j < ar.length) (hij : i = j)
    (hle : k.toNat ≤ (ar[j]'hj).toNat)
    (hc : ¬ k.toNat < (ar[i]'hi).toNat) : k.toNat = (ar[j]'hj).toNat := by
  rw [list_getElem_congr hij hi hj] at hc; omega

private theorem ef_arena_val_idx {ar : List (BitVec 32)} {i j : Nat}
    {hi : i < ar.length} (hj : j < ar.length) (hij : i = j) :
    (ar[i]'hi).toNat = ((ar[j]'hj).setWidth 64).toNat := by
  rw [bv_zext32_toNat, list_getElem_congr hij hi hj]

private theorem ef_bit1_true {ar : List (BitVec 32)} {i j : Nat} {hi : i < ar.length}
    (hj : j < ar.length) (hij : i = j) (hc : (ar[i]'hi &&& 1#32) ≠ 0#32) :
    ((ar[j]'hj &&& 1#32) != 0#32) = true := by
  rw [list_getElem_congr hij hi hj] at hc; exact bne_iff_ne.mpr hc

private theorem ef_bit1_false {ar : List (BitVec 32)} {i j : Nat} {hi : i < ar.length}
    (hj : j < ar.length) (hij : i = j) (hc : (ar[i]'hi &&& 1#32) = 0#32) :
    ((ar[j]'hj &&& 1#32) != 0#32) = false := by
  rw [list_getElem_congr hij hi hj] at hc; simp [hc]

private abbrev efPass1Inv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s s1 : FullState) (g_start g_cap : BitVec 64) (R : Mem 64 → Prop)
    (p g_len wn : BitVec 64) (mp : Mem 64) : Prop :=
  ∃ sp : FullState,
    FullDenseInvW c F0 F_cur sp ∧ sp.core.cur_vars = s.core.cur_vars ∧
    sp.core.fuel = s.core.fuel ∧ sp.core.repr = s.core.repr ∧
    sp.core.inconsistent = s.core.inconsistent ∧ sp.core.arena = s1.core.arena ∧
    sp.core.arena_len = s1.core.arena_len ∧ p.toNat ≤ s1.core.arena_len ∧
    (p.toNat = s1.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefsCore s1.core) ∧
    g_start.toNat ≤ g_len.toNat ∧ g_len.toNat ≤ g_cap.toNat ∧ wn.toNat ≤ c.red_cap ∧
    (∀ idx < wn.toNat, (sp.scratch.red_refs[idx]?.getD 0#32).toNat ∈
      fullArenaClauseRefsCore s1.core) ∧
    CongGateSeqOk 64 F_cur s.core.cur_vars sp.scratch.scratch_buf g_len.toNat 0 ∧
    (FullMem c sp ⋆ R) mp

private abbrev efPass1StepPost (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s s1 : FullState) (g_start g_cap : BitVec 64) (R : Mem 64 → Prop)
    (gl' wn' : BitVec 64) (mj : Mem 64) : Prop :=
  ∃ sj : FullState,
    FullDenseInvW c F0 F_cur sj ∧ sj.core.cur_vars = s.core.cur_vars ∧
    sj.core.fuel = s.core.fuel ∧ sj.core.repr = s.core.repr ∧
    sj.core.inconsistent = s.core.inconsistent ∧ sj.core.arena = s1.core.arena ∧
    sj.core.arena_len = s1.core.arena_len ∧ g_start.toNat ≤ gl'.toNat ∧
    gl'.toNat ≤ g_cap.toNat ∧ wn'.toNat ≤ c.red_cap ∧
    (∀ idx < wn'.toNat, (sj.scratch.red_refs[idx]?.getD 0#32).toNat ∈
      fullArenaClauseRefsCore s1.core) ∧
    CongGateSeqOk 64 F_cur s.core.cur_vars sj.scratch.scratch_buf gl'.toNat 0 ∧
    (FullMem c sj ⋆ R) mj

private abbrev efNarrowPost (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s s1 sp : FullState) (ws2 : List (BitVec 32)) (g_start g_cap : BitVec 64)
    (R : Mem 64 → Prop) (gl' : BitVec 64) (mg : Mem 64) : Prop :=
  ∃ sg : FullState,
    FullDenseInvW c F0 F_cur sg ∧ sg.core.cur_vars = s.core.cur_vars ∧
    sg.core.fuel = s.core.fuel ∧ sg.core.repr = s.core.repr ∧
    sg.core.inconsistent = s.core.inconsistent ∧ sg.core.arena = s1.core.arena ∧
    sg.core.arena_len = s1.core.arena_len ∧ sg.scratch.work_stk2 = ws2 ∧
    sg.scratch.red_refs = sp.scratch.red_refs ∧ g_start.toNat ≤ gl'.toNat ∧
    gl'.toNat ≤ g_cap.toNat ∧
    CongGateSeqOk 64 F_cur s.core.cur_vars sg.scratch.scratch_buf gl'.toNat 0 ∧
    (FullMem c sg ⋆ R) mg

private abbrev efPass2Inv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s s1 sp1 : FullState) (g_start g_cap wn : BitVec 64) (R : Mem 64 → Prop)
    (g_len wi : BitVec 64) (mp : Mem 64) : Prop :=
  ∃ sp : FullState,
    FullDenseInvW c F0 F_cur sp ∧ sp.core.cur_vars = s.core.cur_vars ∧
    sp.core.fuel = s.core.fuel ∧ sp.core.repr = s.core.repr ∧
    sp.core.inconsistent = s.core.inconsistent ∧ sp.core.arena = s1.core.arena ∧
    sp.core.arena_len = s1.core.arena_len ∧ sp.scratch.red_refs = sp1.scratch.red_refs ∧
    wi.toNat ≤ wn.toNat ∧ g_start.toNat ≤ g_len.toNat ∧ g_len.toNat ≤ g_cap.toNat ∧
    CongGateSeqOk congAndArityMax F_cur s.core.cur_vars sp.scratch.scratch_buf g_len.toNat 0 ∧
    (FullMem c sp ⋆ R) mp

private abbrev efPass2StepPost (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s s1 sp1 : FullState) (g_start g_cap : BitVec 64) (R : Mem 64 → Prop)
    (gl' : BitVec 64) (mj : Mem 64) : Prop :=
  ∃ sj : FullState,
    FullDenseInvW c F0 F_cur sj ∧ sj.core.cur_vars = s.core.cur_vars ∧
    sj.core.fuel = s.core.fuel ∧ sj.core.repr = s.core.repr ∧
    sj.core.inconsistent = s.core.inconsistent ∧ sj.core.arena = s1.core.arena ∧
    sj.core.arena_len = s1.core.arena_len ∧ sj.scratch.red_refs = sp1.scratch.red_refs ∧
    g_start.toNat ≤ gl'.toNat ∧ gl'.toNat ≤ g_cap.toNat ∧
    CongGateSeqOk congAndArityMax F_cur s.core.cur_vars sj.scratch.scratch_buf gl'.toNat 0 ∧
    (FullMem c sj ⋆ R) mj

private abbrev efCollectBase (c : FullCfg) (sp : FullState)
    (p_n sz_n : Nat) (usz k : BitVec 32) (ws2 : List (BitVec 32)) : Prop :=
  ws2.length = 2 * c.max_vars ∧ k.toNat ≤ sz_n ∧
  usz.toNat ≤ 1000001 ∧ usz.toNat ≤ k.toNat ∧ usz.toNat ≤ sp.core.cur_vars ∧
  (∀ j < usz.toNat, (ws2[j]?.getD 0#32).toNat < 2 * sp.core.cur_vars) ∧
  (∃ idxs : List Nat, idxs.length = usz.toNat ∧ idxs.Nodup ∧
    (∀ q ∈ idxs, q < k.toNat) ∧
    (∀ j < usz.toNat, ws2[j]? = sp.core.arena[p_n + 3 + (idxs[j]?.getD 0)]?) ∧
    (∀ q < k.toNat, q ∈ idxs ∨
      sp.core.vals[(sp.core.arena[p_n + 3 + q]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8))

private abbrev efCollectDone (F_cur : List (List Nat)) (cv : Nat) (usz : BitVec 32)
    (ws2 : List (BitVec 32)) : Prop :=
  usz.toNat ≤ 1000001 ∧ usz.toNat ≤ cv ∧
  (∀ j < usz.toNat, (ws2[j]?.getD 0#32).toNat < 2 * cv) ∧
  (∀ j < usz.toNat, ∀ j2 < usz.toNat, j ≠ j2 →
    (ws2[j]?.getD 0#32).toNat / 2 ≠ (ws2[j2]?.getD 0#32).toNat / 2) ∧
  (cnfOfClauses F_cur).EntailsClause (cnfClause
    ((List.range usz.toNat).map fun j => (ws2[j]?.getD 0#32).toNat))

private theorem ef_collect_init {c : FullCfg} {sp : FullState} {p_n sz_n : Nat}
    (hws2 : sp.scratch.work_stk2.length = 2 * c.max_vars) :
    efCollectBase c sp p_n sz_n 0#32 0#32 sp.scratch.work_stk2 :=
  ⟨hws2, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, (fun _ h => by cases h),
   ⟨[], rfl, .nil, (fun _ h => by cases h), (fun _ h => by cases h), (fun _ h => by cases h)⟩⟩

private theorem ef_xorK_post {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s1 sg sx : FullState} {g_start g_cap wn ret : BitVec 64} {R : Mem 64 → Prop} {mx : Mem 64}
    (hdg : FullDenseInvW c F0 F_cur sg)
    (hcvg : sg.core.cur_vars = s.core.cur_vars) (hflg : sg.core.fuel = s.core.fuel)
    (hrepg : sg.core.repr = s.core.repr) (hincg : sg.core.inconsistent = s.core.inconsistent)
    (harg : sg.core.arena = s1.core.arena) (halg : sg.core.arena_len = s1.core.arena_len)
    (hwn_le : wn.toNat ≤ c.red_cap)
    (hrr_g_ok : ∀ idx < wn.toNat,
      (sg.scratch.red_refs[idx]?.getD 0#32).toNat ∈ fullArenaClauseRefsCore s1.core)
    (hlen_x : sx.LengthsOk c)
    (hce : { sx.core with tmp := sg.core.tmp, lit_mark := sg.core.lit_mark } = sg.core)
    (hse : { sx.scratch with scratch_buf := sg.scratch.scratch_buf } = sg.scratch)
    (hmk_x : FullLitMarksClear c sx)
    (hlo : g_start.toNat ≤ ret.toNat) (hhi : ret.toNat ≤ g_cap.toNat)
    (hseq_x : CongGateSeqOk 64 F_cur sg.core.cur_vars sx.scratch.scratch_buf ret.toNat 0)
    (hmx : (FullMem c sx ⋆ R) mx) :
    efPass1StepPost c F0 F_cur s s1 g_start g_cap R ret wn mx := by
  have hdx := ef_denseInvW_of_xorK hdg hlen_x hce hse hmk_x
  obtain ⟨hinc_x, har_x, hal_x, hcv_x, _, _, hfu_x, hrep_x, _⟩ := ef_core_fields_of_tmp_lm hce
  obtain ⟨_, _, hrr_x⟩ := ef_scr_fields_of_buf hse
  exact ⟨sx, hdx, hcv_x.trans hcvg, hfu_x.trans hflg, hrep_x.trans hrepg, hinc_x.trans hincg,
    har_x.trans harg, hal_x.trans halg, hlo, hhi, hwn_le, by rw [hrr_x]; exact hrr_g_ok,
    by rw [← hcvg]; exact hseq_x, hmx⟩

private theorem ef_vals_nsgt {vals : List (BitVec 8)} {i1 i2 : Nat}
    {hi1 : i1 < vals.length} (hi2 : i2 < vals.length) (heq : i1 = i2)
    (hc : (0#32 : BitVec 32).slt ((vals[i1]'hi1).signExtend 32) = false) :
    ¬ (0#32 : BitVec 32).slt ((vals[i2]?.getD 0#8).signExtend 32) = true := by
  subst heq; rw [List.getElem?_eq_getElem hi2, Option.getD_some, hc]; decide

private theorem ef_vals_ne0 {vals : List (BitVec 8)} {i1 i2 : Nat}
    {hi1 : i1 < vals.length} (hi2 : i2 < vals.length) (heq : i1 = i2)
    (hc : (vals[i1]'hi1).signExtend 32 ≠ 0#32) :
    (vals[i2]?.getD 0#8).signExtend 32 ≠ 0#32 := by
  subst heq; rw [List.getElem?_eq_getElem hi2, Option.getD_some]; exact hc

private theorem ef_rr_push_step {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s s1 sb : FullState} {g_start g_cap g_len wn p : BitVec 64} {R : Mem 64 → Prop} {m : Mem 64}
    (hdb : FullDenseInvW c F0 F_cur sb)
    (hcv_p : sb.core.cur_vars = s.core.cur_vars) (hfl_p : sb.core.fuel = s.core.fuel)
    (hrep_p : sb.core.repr = s.core.repr) (hinc_p : sb.core.inconsistent = s.core.inconsistent)
    (har_p : sb.core.arena = s1.core.arena) (hal_p : sb.core.arena_len = s1.core.arena_len)
    (hgl_lo : g_start.toNat ≤ g_len.toNat) (hgl_hi : g_len.toNat ≤ g_cap.toNat)
    (hwn_lt : wn.toNat < c.red_cap) (hwn1_n : (wn + 1#64).toNat = wn.toNat + 1)
    (hp_tr : (p.setWidth 32).toNat = p.toNat) (hp_ref : p.toNat ∈ fullArenaClauseRefsCore s1.core)
    (hrr_p : ∀ idx < wn.toNat,
      (sb.scratch.red_refs[idx]?.getD 0#32).toNat ∈ fullArenaClauseRefsCore s1.core)
    (hseq_p : CongGateSeqOk 64 F_cur s.core.cur_vars sb.scratch.scratch_buf g_len.toNat 0)
    (hm : (FullMem c { sb with scratch := { sb.scratch with
        red_refs := sb.scratch.red_refs.set wn.toNat (p.setWidth 32) } } ⋆ R) m) :
    efPass1StepPost c F0 F_cur s s1 g_start g_cap R g_len (wn + 1#64) m := by
  let sb' : FullState := { sb with scratch := { sb.scratch with
    red_refs := sb.scratch.red_refs.set wn.toNat (p.setWidth 32) } }
  have hrrl := hdb.1.scratch_ok.red_refs_len
  exact ⟨sb', fullDenseInvW_with_rr hdb (by rw [List.length_set]; exact hrrl),
    hcv_p, hfl_p, hrep_p, hinc_p, har_p, hal_p, hgl_lo, hgl_hi, by omega,
    by rw [hwn1_n]; exact ef_rr_push_ok (by omega) hp_tr hp_ref hrr_p, hseq_p, hm⟩

private theorem ef_extAnd_spec {maxA : Nat} {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {sb : FullState} {usz : BitVec 32} {gl g_cap tk_lim rsz : BitVec 64} {R : Mem 64 → Prop}
    {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hmaxA : maxA ≤ congAndArityMax) (hdb : FullDenseInvW c F0 F_cur sb)
    (hu3 : 3 ≤ usz.toNat) (hum : usz.toNat - 1 ≤ maxA) (hucv : usz.toNat ≤ sb.core.cur_vars)
    (hgl : gl.toNat ≤ g_cap.toNat) (hgcap : g_cap.toNat ≤ c.scratch_cap)
    (hseq : CongGateSeqOk maxA F_cur sb.core.cur_vars sb.scratch.scratch_buf gl.toNat 0)
    (hlt : ∀ j < usz.toNat, (sb.scratch.work_stk2[j]?.getD 0#32).toNat < 2 * sb.core.cur_vars)
    (hdiff : ∀ j < usz.toNat, ∀ j2 < usz.toNat, j ≠ j2 →
      (sb.scratch.work_stk2[j]?.getD 0#32).toNat / 2 ≠
        (sb.scratch.work_stk2[j2]?.getD 0#32).toNat / 2)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((List.range usz.toNat).map fun j => (sb.scratch.work_stk2[j]?.getD 0#32).toNat)))
    (hm : (FullMem c { sb with scratch := { sb.scratch with res_sz := rsz } } ⋆ R) m)
    (hK : ∀ ret lm' scr' rsz' m',
      let s' : FullState :=
        { sb with
          core := { sb.core with lit_mark := lm' }
          scratch := { sb.scratch with scratch_buf := scr', res_sz := rsz' } }
      FullDenseInvW c F0 F_cur s' → gl.toNat ≤ ret.toNat → ret.toNat ≤ g_cap.toNat →
      (∀ idx < gl.toNat, scr'[idx]? = sb.scratch.scratch_buf[idx]?) →
      CongGateSeqOk maxA F_cur sb.core.cur_vars scr' ret.toNat 0 →
      (FullMem c s' ⋆ R) m' → Q (ret, ()) m') :
    Spec.fullCongExtractAndClauseFidSpec (c.hdr, usz, gl, g_cap, tk_lim, ()) m Q X :=
  ⟨maxA, c, F0, F_cur, { sb with scratch := { sb.scratch with res_sz := rsz } }, R, hmaxA, rfl,
   fullDenseInvW_with_rsz hdb rsz, hu3, hum, hucv, hgl, hgcap, hseq, hlt,
   fun j hj j2 hj2 hne heq => hdiff j hj j2 hj2 hne (congrArg (· / 2) heq), hent, hm, hK⟩

private theorem ef_extractXorK_spec {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {sg : FullState} {ws2 : List (BitVec 32)} {usz neg_p : BitVec 32} {gl g_cap : BitVec 64}
    {R : Mem 64 → Prop} {mg : Mem 64} {Q : Post [i64]} {X : XPost} {cv : Nat}
    (hdg : FullDenseInvW c F0 F_cur sg) (hws2g : sg.scratch.work_stk2 = ws2)
    (hcv : sg.core.cur_vars = cv) (hu4 : 4 ≤ usz.toNat) (hu5 : usz.toNat ≤ 5)
    (hucv : usz.toNat ≤ cv) (hgl : gl.toNat ≤ g_cap.toNat) (hgcap : g_cap.toNat ≤ c.scratch_cap)
    (hseq : CongGateSeqOk 64 F_cur sg.core.cur_vars sg.scratch.scratch_buf gl.toNat 0)
    (hlt : ∀ j < usz.toNat, (ws2[j]?.getD 0#32).toNat < 2 * cv)
    (hneg : (neg_p &&& 1#32).toNat = (List.range usz.toNat).foldl
      (fun acc i => acc ^^^ ((ws2[i]?.getD 0#32).toNat % 2)) 0)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((List.range usz.toNat).map fun j => (ws2[j]?.getD 0#32).toNat)))
    (hmg : (FullMem c sg ⋆ R) mg)
    (hK : ∀ ret sx mx, sx.LengthsOk c →
      { sx.core with tmp := sg.core.tmp, lit_mark := sg.core.lit_mark } = sg.core →
      { sx.scratch with scratch_buf := sg.scratch.scratch_buf } = sg.scratch →
      FullLitMarksClear c sx → gl.toNat ≤ ret.toNat → ret.toNat ≤ g_cap.toNat →
      (∀ idx < gl.toNat, sx.scratch.scratch_buf[idx]? = sg.scratch.scratch_buf[idx]?) →
      CongGateSeqOk 64 F_cur sg.core.cur_vars sx.scratch.scratch_buf ret.toNat 0 →
      (FullMem c sx ⋆ R) mx → Q (ret, ()) mx) :
    Spec.fullCongExtractXorKSpec (c.hdr, usz, neg_p, gl, g_cap, ()) mg Q X :=
  ⟨64, c, F0, F_cur, sg, R, by decide, Nat.le_refl _, rfl, hdg.1, hdg.2.1, hdg.2.2.1,
   hdg.2.2.2.1, hdg.2.2.2.2.2.1, by omega, hu5, by rw [hcv]; exact hucv, hgl, hgcap, hseq,
   by rw [hws2g, hcv]; exact hlt, by rw [hws2g]; exact hneg, by rw [hws2g]; exact hent,
   hmg, hK⟩

private theorem ef_tryXorIte_spec {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {sg : FullState} {ws2 : List (BitVec 32)} {usz l0 l1 l2 : BitVec 32} {gl g_cap : BitVec 64}
    {R : Mem 64 → Prop} {mg : Mem 64} {Q : Post [i64]} {X : XPost} {cv : Nat}
    (hdg : FullDenseInvW c F0 F_cur sg) (hcv : sg.core.cur_vars = cv) (hu3 : usz.toNat = 3)
    (hl0 : l0 = ws2[0]?.getD 0#32) (hl1 : l1 = ws2[1]?.getD 0#32) (hl2 : l2 = ws2[2]?.getD 0#32)
    (hlt : ∀ j < usz.toNat, (ws2[j]?.getD 0#32).toNat < 2 * cv)
    (hdiff : ∀ j < usz.toNat, ∀ j2 < usz.toNat, j ≠ j2 →
      (ws2[j]?.getD 0#32).toNat / 2 ≠ (ws2[j2]?.getD 0#32).toNat / 2)
    (hent : (cnfOfClauses F_cur).EntailsClause
      (cnfClause ((List.range usz.toNat).map fun j => (ws2[j]?.getD 0#32).toNat)))
    (hgl5 : gl.toNat + 5 ≤ g_cap.toNat) (hgcap : g_cap.toNat ≤ c.scratch_cap)
    (hseq : CongGateSeqOk 64 F_cur sg.core.cur_vars sg.scratch.scratch_buf gl.toNat 0)
    (hmg : (FullMem c sg ⋆ R) mg)
    (hK : ∀ ret scr' mg',
      scr'.length = c.scratch_cap → gl.toNat ≤ ret.toNat → ret.toNat ≤ g_cap.toNat →
      (∀ idx < gl.toNat, scr'[idx]? = sg.scratch.scratch_buf[idx]?) →
      CongGateSeqOk 64 F_cur sg.core.cur_vars scr' ret.toNat 0 →
      (FullMem c { sg with scratch := { sg.scratch with scratch_buf := scr' } } ⋆ R) mg' →
      Q (ret, ()) mg') :
    Spec.fullCongTryXorIteSpec (c.hdr, l0, l1, l2, gl, g_cap, ()) mg Q X := by
  subst hl0; subst hl1; subst hl2
  exact ⟨64, c, F0, F_cur, sg, R, by decide, Nat.le_refl _, rfl, hdg.1, hdg.2.1, hdg.2.2.2.1,
    hdg.2.2.2.2.2.1, by rw [hcv]; exact hlt 0 (by omega), by rw [hcv]; exact hlt 1 (by omega),
    by rw [hcv]; exact hlt 2 (by omega), hdiff 0 (by omega) 1 (by omega) (by decide),
    hdiff 0 (by omega) 2 (by omega) (by decide), hdiff 1 (by omega) 2 (by omega) (by decide),
    by simpa [hu3, List.range_succ] using hent, hgl5, hgcap, hseq, hmg, hK⟩

/-! ## 2. Canonical WP Theorem -/

public section

theorem full_cong_extract_from_fid_wp {Γ : Env}
    (hNext : Γ.Has "full_arena_next" fullArenaNextSpec)
    (hCountBins : Γ.Has "full_cong_count_bins" Spec.fullCongCountBinsSpec)
    (hExtAnd : Γ.Has "full_cong_extract_and_clause_fid" Spec.fullCongExtractAndClauseFidSpec)
    (hTryXorIte : Γ.Has "full_cong_try_xor_ite" Spec.fullCongTryXorIteSpec)
    (hExtractXorK : Γ.Has "full_cong_extract_xor_k" Spec.fullCongExtractXorKSpec) :
    ∀ args m Q X, Spec.fullCongExtractFromFidSpec args m Q X →
      Func.wp Γ full_cong_extract_from_fid_body args m Q X := by
  rintro ⟨h, g_start, g_cap, tick_lim, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s, R, rfl, hd, hgs_le, hg_cap, hseq0, hm0, hQ⟩
  have hmx := c.hmaxv; have hac := c.harena; have hsc := c.hscr; have hrc := c.hred
  unfold dimacsBound at hmx hac hsc hrc
  dsimp only [Func.wp, full_cong_extract_from_fid_body]; c0_hstraight!; c0_hsplit
  · exfalso; bv_omega
  clear hc; c0_hstraight!
  refine wp_call_of_spec _ _ (hCountBins _ _ _ _
    ⟨c, s, R, rfl, hd.1, fullWatchBounds_of_dense hd, hm0, fun ws1' m1 hws1_l hm1 => ?_⟩)
  let s1 : FullState := { s with scratch := { s.scratch with work_stk1 := ws1' } }
  have hd1 : FullDenseInvW c F0 F_cur s1 := fullDenseInvW_with_ws1 hd hws1_l
  c0_hstraight!
  refine wp_loop_inv (ts := [i64, i64, i64, i64])
    (fun (p, g_len, _, wn, ()) mp => efPass1Inv c F0 F_cur s s1 g_start g_cap R p g_len wn mp)
    (fun (p, _, _, _, ()) _ => s1.core.arena_len - p.toNat)
    (fun J hJ => by
      c0_hstraight!
      have hmem0 : (0#64 : BitVec 64).toNat = s1.core.arena_len ∨
          (0#64 : BitVec 64).toNat ∈ fullArenaClauseRefsCore s1.core := by
        rcases Nat.eq_zero_or_pos s1.core.arena_len with hz | hpos
        · exact Or.inl hz.symm
        · exact Or.inr (fullArenaClauseRefs_zero_mem hd1.2.1 hpos)
      exact hJ (0#64, g_start, 0#64, 0#64, ()) m1
        ⟨s1, hd1, rfl, rfl, rfl, rfl, rfl, rfl, Nat.zero_le _, hmem0, Nat.le_refl _, hgs_le,
         Nat.zero_le _, (fun _ h => absurd h (Nat.not_lt_zero _)), hseq0, hm1⟩)
    (fun J (p, g_len, ticks, wn, ()) mp
      ⟨sp, hdp, hcv_p, hfl_p, hrep_p, hinc_p, har_p, hal_p, hp_le, hp_mem, hgl_lo, hgl_hi,
       hwn_le, hrr_p, hseq_p, hmp⟩ ihp => ?_)
  dsimp only [Blocks.get, Member.here]
  refine wp_join_group (ts := []) (fun () m_p2 => m_p2 = mp) ?_ ?_
  · -- Pass 2: wide AND clauses recorded in `rr[0..wn)`
    rintro _ ⟨⟩ m_p2 hm_p2; rw [hm_p2]; dsimp only [Blocks.get, Member.here]
    let sp1 := sp; let g_len1 := g_len; let ticks1 := ticks
    have hseq1_w : CongGateSeqOk congAndArityMax F_cur s.core.cur_vars
        sp1.scratch.scratch_buf g_len1.toNat 0 :=
      congGateSeqOk_mono (by unfold congAndArityMax; decide) hseq_p
    c0_hstraight!
    refine wp_loop_inv (ts := [i64, i64, i64])
      (fun (gl, _, wi, ()) m2 => efPass2Inv c F0 F_cur s s1 sp1 g_start g_cap wn R gl wi m2)
      (fun (_, _, wi, ()) _ => wn.toNat - wi.toNat)
      (fun J2 hJ2 => by
        c0_hstraight!; exact hJ2 (g_len1, ticks1, 0#64, ()) mp
          ⟨sp1, hdp, hcv_p, hfl_p, hrep_p, hinc_p, har_p, hal_p, rfl, Nat.zero_le _, hgl_lo,
           hgl_hi, hseq1_w, hmp⟩)
      (fun J2 (gl2, tk2, wi, ()) m2
        ⟨sp2, hdp2, hcv2, hfl2, hrep2, hinc2, har2, hal2, hrr2, hwi_le, hgl2_lo, hgl2_hi,
         hseq2, hm2⟩ ih2 => ?_)
    dsimp only [Blocks.get, Member.here]
    have hq_done : Q (gl2, ()) m2 :=
      hQ gl2 sp2 m2 hdp2 hcv2 hfl2 hrep2 hinc2 hgl2_lo hgl2_hi hseq2 hm2
    have hlen2 := hdp2.1; have harl2 := hlen2.core_ok.arena_len_arr
    have hale2 := hlen2.core_ok.arena_len_le; have hcv2_le := hlen2.core_ok.cur_vars_le
    have hws1_2 := hlen2.scratch_ok.work_stk1_len; have hws2_2 := hlen2.scratch_ok.work_stk2_len
    have hrrl2 := hlen2.scratch_ok.red_refs_len
    ef_if hq_done; have hwi_lt : wi.toNat < wn.toNat := (by bv_omega); clear hc
    ef_if hq_done; clear hc; ef_if hq_done; clear hc
    have hwi_rr : wi.toNat < sp2.scratch.red_refs.length := by omega
    let wp := (sp2.scratch.red_refs[wi.toNat]'hwi_rr).setWidth 64
    have hwp_ref : wp.toNat ∈ fullArenaClauseRefsCore sp2.core := by
      have h1 := hrr_p wi.toNat hwi_lt
      rw [← hrr2, List.getElem?_eq_getElem hwi_rr, Option.getD_some] at h1
      unfold fullArenaClauseRefsCore; rw [har2, hal2, bv_zext32_toNat]; exact h1
    have hwp_wf := hdp2.2.1.arena.refs_wf wp.toNat hwp_ref
    have hwp_arr : wp.toNat < sp2.core.arena.length := by omega
    have hwp2_n : (wp + 2#64).toNat = wp.toNat + 2 := by bv_omega
    have hwp2_arr : (wp + 2#64).toNat < sp2.core.arena.length := by omega
    have hwi1_n : (wi + 1#64).toNat = wi.toNat + 1 := bv64_add1_lt (by omega)
    c0_hstraight!
    refine wp_join_group (ts := [i64, i64])
      (fun (gl', _, ()) mj => efPass2StepPost c F0 F_cur s s1 sp1 g_start g_cap R gl' mj)
      (fun _ ⟨gl', tk', ⟨⟩⟩ mj ⟨sj, hdj, hcvj, hflj, hrepj, hincj, harj, halj, hrrj,
        hlo', hhi', hseqj, hmj⟩ => by
        dsimp only [Blocks.get, Member.here]; c0_hstraight!
        exact ih2 (gl', tk', wi + 1#64, ()) mj (by dsimp only; omega)
          ⟨sj, hdj, hcvj, hflj, hrepj, hincj, harj, halj, hrrj, by omega, hlo', hhi',
           hseqj, hmj⟩) ?_
    intro Jw2 hJw2
    have hjw2_same : Jw2 (gl2, tk2 + 1#64, ()) m2 :=
      hJw2 (gl2, tk2 + 1#64, ()) m2
        ⟨sp2, hdp2, hcv2, hfl2, hrep2, hinc2, har2, hal2, hrr2, hgl2_lo, hgl2_hi, hseq2, hm2⟩
    ef_if hjw2_same
    obtain ⟨hng, hsz_eq, hbd_sz⟩ := ef_clause_hdr_ok hdp2 hwp_ref hwp_arr hwp2_n hwp2_arr hc
    clear hc; ef_if hjw2_same; clear hc
    let sz_bv := sp2.core.arena[(wp + 2#64).toNat]'hwp2_arr
    have hbd_sz : wp.toNat + 3 + sz_bv.toNat ≤ sp2.core.arena.length := hbd_sz
    c0_hstraight!
    refine wp_loop_break_group (brkTs := [i32, i32, i32, .bool, i32])
      (lpTs := [i32, i32, i32, i32])
      (fun (usz, _, _, sat, _, ()) mb => ∃ ws2 : List (BitVec 32),
        ws2.length = 2 * c.max_vars ∧
        (sat = false → efCollectDone F_cur sp2.core.cur_vars usz ws2) ∧
        (FullMem c { sp2 with scratch := { sp2.scratch with work_stk2 := ws2 } } ⋆ R) mb)
      (fun rem (usz, _, _, k, ()) mk => ∃ ws2 : List (BitVec 32),
        rem = sz_bv.toNat - k.toNat ∧ efCollectBase c sp2 wp.toNat sz_bv.toNat usz k ws2 ∧
        (FullMem c { sp2 with scratch := { sp2.scratch with work_stk2 := ws2 } } ⋆ R) mk)
      ?_ ?_ ?_
    · rintro _ ⟨usz, _, _, sat, _, ⟨⟩⟩ mb ⟨ws2, hws2_l, hnsat, hmb⟩
      dsimp only [Blocks.get, Member.here]
      let sb : FullState := { sp2 with scratch := { sp2.scratch with work_stk2 := ws2 } }
      have hdb : FullDenseInvW c F0 F_cur sb := fullDenseInvW_with_ws2 hdp2 hws2_l
      have hjb_same : Jw2 (gl2, tk2 + 1#64, ()) mb :=
        hJw2 (gl2, tk2 + 1#64, ()) mb
          ⟨sb, hdb, hcv2, hfl2, hrep2, hinc2, har2, hal2, hrr2, hgl2_lo, hgl2_hi, hseq2, hmb⟩
      refine ef_join_inline fun _ _ => ?_
      ef_unless hjb_same; have hsat_f : sat = false := hc; clear hc
      ef_if hjb_same; have hu66 : 66 ≤ usz.toNat := (by bv_omega); clear hc
      ef_if hjb_same; have hu_max : usz.toNat ≤ 1000001 := (by bv_omega); clear hc
      ef_if hjb_same; clear hc; obtain ⟨_, hu_cv, hlt_u, hdiff_u, hent_u⟩ := hnsat hsat_f
      c0_hstraight!; refine ef_join_inline fun _ _ => ?_
      ef_if hjb_same; clear hc; ef_if hjb_same; clear hc; c0_hstraight!
      refine wp_call_of_spec _ _ (hExtAnd _ _ _ _ ?_)
      change Spec.fullCongExtractAndClauseFidSpec (c.hdr, usz, gl2, g_cap, tick_lim, ()) _ _ _
      refine ef_extAnd_spec (Nat.le_refl _) hdb (by omega) (by unfold congAndArityMax; omega)
        hu_cv hgl2_hi hg_cap (by rw [hcv2]; exact hseq2) hlt_u hdiff_u hent_u (by assumption)
        fun ret lm' scr' rsz' m' hdw' hlo' hhi' _ hseq' hm' => ?_
      c0_hstraight!
      exact hJw2 (ret, rsz', ()) m' ⟨_, hdw', hcv2, hfl2, hrep2, hinc2, har2, hal2, hrr2,
        by omega, hhi', by rw [← hcv2]; exact hseq', hm'⟩
    · rintro B3 L3 rem3 ⟨usz, max_nbc, min_nbc, k, ⟨⟩⟩ mk hB3 hL3
        ⟨ws2, rfl, ⟨hws2_l, hk_le, hu_max, hu_k, hu_cv, hlt_u,
         ⟨idxs, hid_len, hid_nd, hid_lt, hws2_map, hcov_k⟩⟩, hmk⟩
      dsimp only [Blocks.get, Member.here]; c0_hstraight!; c0_hsplit
      · have hk_lt : k.toNat < sz_bv.toNat := ef_ult_eq hwp2_arr (by dsimp only [wp]; bv_omega) hc
        have hk1_n : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
        have hp3k_n : (wp + 3#64 + k.setWidth 64).toNat = wp.toNat + 3 + k.toNat :=
          bv64_add_zext32 (k := 3) (by omega)
        have hp3k_arr : (wp + 3#64 + k.setWidth 64).toNat < sp2.core.arena.length := by omega
        obtain ⟨hlk_eq, hlk_lt, hlk_v, hdom_lk⟩ :=
          ef_arena_lit_ok hdp2 hwp_ref hng hsz_eq hbd_sz hk_lt hp3k_n hp3k_arr
        let lk := sp2.core.arena[(wp + 3#64 + k.setWidth 64).toNat]'hp3k_arr
        have hbrk_t : B3 (usz, max_nbc, min_nbc, true, k, ()) mk :=
          hB3 (usz, max_nbc, min_nbc, true, k, ()) mk ⟨ws2, hws2_l, (fun hf => by cases hf), hmk⟩
        clear hc; ef_unless hbrk_t
        have hnsgt := ef_vals_nsgt hlk_v (ef_arena_val_idx hp3k_arr (by dsimp only [wp]; bv_omega))
          hc
        clear hc; c0_hstraight!; refine ef_join_inline fun _ _ => ?_
        c0_hstraight!; c0_hsplit
        · clear hc; ef_unless hbrk_t; have hu_ltm : usz.toNat < 1000001 := (by bv_omega); clear hc
          ef_unless hbrk_t
          have hu_lt_cv : usz.toNat < sp2.core.cur_vars := by rw [hcv2]; bv_omega
          have hu1_n : (usz + 1#32).toNat = usz.toNat + 1 := by bv_omega
          have hu_ws2 : usz.toNat < ws2.length := by omega
          have hu_ws2_64 : (usz.setWidth 64).toNat < ws2.length := by
            rw [bv_zext32_toNat]; exact hu_ws2
          have hlk_ws1 : (lk.setWidth 64).toNat < sp2.scratch.work_stk1.length := by
            rw [bv_zext32_toNat, hws1_2]; dsimp only [lk]; omega
          clear hc; c0_hstraight!
          let ws2' := ws2.set usz.toNat lk
          refine ef_capture_ws2 (ws2' := ws2') (by assumption)
            (ef_ws2_set_congr hp3k_arr (by bv_omega) (by dsimp only [wp]; bv_omega))
            fun m_st hm2' => ?_
          have hstep := ef_collect_append_ok hu_ws2 (by omega) hlk_eq hlk_lt hlt_u
            hid_len hid_nd hid_lt hws2_map hcov_k
          refine wp_join_group (ts := [i32]) (fun (_, ()) mmx => mmx = m_st) ?_ ?_
          · rintro _ ⟨mx', ⟨⟩⟩ mmx hmmx; rw [hmmx]
            dsimp only [Blocks.get, Member.here]; c0_hstraight!
            refine wp_join_group (ts := [i32]) (fun (_, ()) mmn => mmn = m_st) ?_ ?_
            · rintro _ ⟨mn', ⟨⟩⟩ mmn hmmn; rw [hmmn]
              dsimp only [Blocks.get, Member.here]; c0_hstraight!
              exact hL3 (sz_bv.toNat - (k + 1#32).toNat)
                (usz + 1#32, mx', mn', k + 1#32, ()) m_st (by omega)
                ⟨ws2', rfl, ⟨by simp [ws2', hws2_l], by omega, by omega, by omega, by omega,
                  by rw [hu1_n]; exact hstep.1, by rw [hu1_n, hk1_n]; exact hstep.2⟩, hm2'⟩
            · intro Jmn hJmn; c0_hstraight!; c0_hsplit <;>
                (clear hc; c0_hstraight!; exact hJmn (_, ()) m_st rfl)
          · intro Jmx hJmx; c0_hstraight!; c0_hsplit <;>
              (clear hc; c0_hstraight!; exact hJmx (_, ()) m_st rfl)
        · have hne0 := ef_vals_ne0 hlk_v (ef_arena_val_idx hp3k_arr (by dsimp only [wp]; bv_omega))
            hc
          clear hc; c0_hstraight!
          have hcov_nx := ef_collect_false_ok (by omega) hlk_eq hdom_lk hnsgt hne0 hcov_k
          exact hL3 (sz_bv.toNat - (k + 1#32).toNat)
            (usz, max_nbc, min_nbc, k + 1#32, ()) mk (by omega)
            ⟨ws2, rfl, ⟨hws2_l, by omega, hu_max, by omega, hu_cv, hlt_u,
              ⟨idxs, hid_len, hid_nd, fun q hq => by have := hid_lt q hq; omega, hws2_map,
               by rw [hk1_n]; exact hcov_nx⟩⟩, hmk⟩
      · have hk_e : k.toNat = sz_bv.toNat :=
          ef_nult_eq hwp2_arr (by dsimp only [wp]; bv_omega) hk_le hc
        obtain ⟨hdiff_u, hent_u⟩ := ef_clause_collect_done hdp2 hwp_ref hng hsz_eq
          hbd_sz (by omega) hid_len hid_nd (hk_e ▸ hid_lt) hws2_map (hk_e ▸ hcov_k)
        clear hc; c0_hstraight!
        exact hB3 (usz, max_nbc, min_nbc, false, k, ()) mk
          ⟨ws2, hws2_l, fun _ => ⟨hu_max, hu_cv, hlt_u, hdiff_u, hent_u⟩, hmk⟩
    · intro _ L3 _ hL3; c0_hstraight!
      exact hL3 sz_bv.toNat (0#32, 0#32, 0xFFFFFFFF#32, 0#32, ()) m2
        ⟨sp2.scratch.work_stk2, rfl, ef_collect_init hws2_2, hm2⟩
  · -- Pass 1: arena scan (`narrow AND ≤ 64` + XOR/ITE, recording `66 ≤ usz ≤ 1,000,001` in `rr`)
    intro Jp2 hJp2; have hjp2_now : Jp2 () mp := hJp2 () mp rfl
    have hlen_p := hdp.1; have harl_p := hlen_p.core_ok.arena_len_arr
    have hale_p := hlen_p.core_ok.arena_len_le; have hcv_ple := hlen_p.core_ok.cur_vars_le
    have hws1_pl := hlen_p.scratch_ok.work_stk1_len; have hws2_pl := hlen_p.scratch_ok.work_stk2_len
    have hrrl_p := hlen_p.scratch_ok.red_refs_len
    ef_if hjp2_now; have hp_lt : p.toNat < sp.core.arena_len := (by bv_omega); clear hc
    ef_if hjp2_now; clear hc; ef_if hjp2_now; clear hc
    have hp_ref : p.toNat ∈ fullArenaClauseRefsCore sp.core := by
      have hmem := hp_mem.resolve_left (by omega)
      unfold fullArenaClauseRefsCore; rw [har_p, hal_p]; exact hmem
    have hp_wf := hdp.2.1.arena.refs_wf p.toNat hp_ref
    have hp_arr : p.toNat < sp.core.arena.length := by omega
    have hp2_n : (p + 2#64).toNat = p.toNat + 2 := by bv_omega
    have hp2_arr : (p + 2#64).toNat < sp.core.arena.length := by omega
    c0_hstraight!
    refine wp_call_of_spec _ _ (hNext _ _ _ _ ⟨c, sp, R, rfl, hlen_p, hmp, ?_⟩)
    obtain ⟨hp_tr, hnp_le, hnp_mem, hnp_gt⟩ :=
      ef_arena_next_ok hd1 hdp har_p hal_p hp_lt hp_mem
    let np_bv := (BitVec.ofNat 32 (fullArenaNextOff sp.core.arena sp.core.arena_len
      (p.setWidth 32).toNat)).setWidth 64
    have hnp_gt : p.toNat < np_bv.toNat := hnp_gt
    c0_hstraight!
    refine wp_join_group (ts := [i64, i64, i64])
      (fun (gl', _, wn', ()) mj => efPass1StepPost c F0 F_cur s s1 g_start g_cap R gl' wn' mj)
      (fun _ ⟨gl', tk', wn', ⟨⟩⟩ mj ⟨sj, hdj, hcvj, hflj, hrepj, hincj, harj, halj,
        hlo', hhi', hwnj, hrrj, hseqj, hmj⟩ => by
        dsimp only [Blocks.get, Member.here]; c0_hstraight!
        exact ihp (np_bv, gl', tk', wn', ()) mj (by dsimp only; omega)
          ⟨sj, hdj, hcvj, hflj, hrepj, hincj, harj, halj, hnp_le, hnp_mem, hlo', hhi',
           hwnj, hrrj, hseqj, hmj⟩) ?_
    intro Jnext hJnext
    have hjnext_same : Jnext (g_len, ticks + 1#64, wn, ()) mp :=
      hJnext (g_len, ticks + 1#64, wn, ()) mp
        ⟨sp, hdp, hcv_p, hfl_p, hrep_p, hinc_p, har_p, hal_p, hgl_lo, hgl_hi, hwn_le, hrr_p,
         hseq_p, hmp⟩
    ef_if hjnext_same
    obtain ⟨hng, hsz_eq, hbd_sz⟩ := ef_clause_hdr_ok hdp hp_ref hp_arr hp2_n hp2_arr hc
    clear hc; ef_if hjnext_same; clear hc
    let sz_bv := sp.core.arena[(p + 2#64).toNat]'hp2_arr
    have hbd_sz : p.toNat + 3 + sz_bv.toNat ≤ sp.core.arena.length := hbd_sz
    c0_hstraight!
    refine wp_loop_break_group (brkTs := [i32, i32, i32, i32, .bool, i32])
      (lpTs := [i32, i32, i32, i32, i32])
      (fun (usz, _, _, neg_p, sat, _, ()) mb => ∃ ws2 : List (BitVec 32),
        ws2.length = 2 * c.max_vars ∧
        (sat = false → efCollectDone F_cur sp.core.cur_vars usz ws2 ∧
          (neg_p &&& 1#32).toNat = (List.range usz.toNat).foldl
            (fun acc i => acc ^^^ ((ws2[i]?.getD 0#32).toNat % 2)) 0) ∧
        (FullMem c { sp with scratch := { sp.scratch with work_stk2 := ws2 } } ⋆ R) mb)
      (fun rem (usz, _, _, neg_p, k, ()) mk => ∃ ws2 : List (BitVec 32),
        rem = sz_bv.toNat - k.toNat ∧ efCollectBase c sp p.toNat sz_bv.toNat usz k ws2 ∧
        (neg_p &&& 1#32).toNat = (List.range usz.toNat).foldl
          (fun acc i => acc ^^^ ((ws2[i]?.getD 0#32).toNat % 2)) 0 ∧
        (FullMem c { sp with scratch := { sp.scratch with work_stk2 := ws2 } } ⋆ R) mk)
      ?_ ?_ ?_
    · rintro _ ⟨usz, _, _, neg_p, sat, _, ⟨⟩⟩ mb ⟨ws2, hws2_l, hnsat, hmb⟩
      dsimp only [Blocks.get, Member.here]
      let sb : FullState := { sp with scratch := { sp.scratch with work_stk2 := ws2 } }
      have hdb : FullDenseInvW c F0 F_cur sb := fullDenseInvW_with_ws2 hdp hws2_l
      c0_hstraight!
      refine wp_join_group (ts := [i64, i64, i64])
        (fun (gl', _, wn', ()) mj => efPass1StepPost c F0 F_cur s s1 g_start g_cap R gl' wn' mj)
        (fun _ ⟨gl', tk', wn', ⟨⟩⟩ mj h => by c0_hstraight!; exact hJnext (gl', tk', wn', ()) mj h)
        ?_
      intro Jnext hJnext
      have hjb_same : Jnext (g_len, ticks + 1#64, wn, ()) mb :=
        hJnext (g_len, ticks + 1#64, wn, ()) mb
          ⟨sb, hdb, hcv_p, hfl_p, hrep_p, hinc_p, har_p, hal_p, hgl_lo, hgl_hi, hwn_le, hrr_p,
           hseq_p, hmb⟩
      refine wp_join_group (ts := []) (fun () m_el => m_el = mb) ?_ ?_
      · rintro _ ⟨⟩ m_el hm_el; rw [hm_el]; dsimp only [Blocks.get, Member.here]
        refine ef_join_inline fun _ _ => ?_
        ef_unless hjb_same; clear hc
        ef_if hjb_same; clear hc; ef_if hjb_same; clear hc; ef_if hjb_same; clear hc
        c0_hstraight!; refine ef_join_inline fun _ _ => ?_
        ef_if hjb_same; clear hc; ef_if hjb_same; clear hc; ef_if hjb_same
        have hwn_lt : wn.toNat < c.red_cap := by bv_omega
        have hwn_rr : wn.toNat < sb.scratch.red_refs.length := by dsimp only [sb]; omega
        have hwn1_n : (wn + 1#64).toNat = wn.toNat + 1 := bv64_add1_lt (by omega)
        clear hc; c0_hstraight!
        exact hJnext (g_len, ticks + 1#64, wn + 1#64, ()) _
          (ef_rr_push_step hdb hcv_p hfl_p hrep_p hinc_p har_p hal_p hgl_lo hgl_hi hwn_lt
            hwn1_n hp_tr (hp_mem.resolve_left (by omega)) hrr_p hseq_p (by assumption))
      · intro Jel hJel; have hjel_now : Jel () mb := hJel () mb rfl
        ef_unless hjel_now; have hsat_f : sat = false := hc; clear hc
        ef_if hjel_now; have hu_lt3 : 3 ≤ usz.toNat := (by bv_omega); clear hc
        ef_if hjel_now; have hu_le65 : usz.toNat ≤ 65 := (by bv_omega); clear hc
        ef_if hjel_now; clear hc
        obtain ⟨⟨_, hu_cv, hlt_u, hdiff_u, hent_u⟩, hneg_u⟩ := hnsat hsat_f
        c0_hstraight!
        refine wp_join_group (ts := [i64, i64])
          (fun (gl', _, ()) mg => efNarrowPost c F0 F_cur s s1 sp ws2 g_start g_cap R gl' mg) ?_ ?_
        · rintro _ ⟨gl', tk', ⟨⟩⟩ mg ⟨sg, hdg, hcvg, hflg, hrepg, hincg, harg, halg, hws2g, hrrg,
            hlo', hhi', hseqg, hmg⟩
          dsimp only [Blocks.get, Member.here]
          have hrr_g_ok : ∀ idx < wn.toNat,
              (sg.scratch.red_refs[idx]?.getD 0#32).toNat ∈
                fullArenaClauseRefsCore s1.core := by rw [hrrg]; exact hrr_p
          have hjg_same : Jnext (gl', tk', wn, ()) mg :=
            hJnext (gl', tk', wn, ()) mg
              ⟨sg, hdg, hcvg, hflg, hrepg, hincg, harg, halg, hlo', hhi', hwn_le, hrr_g_ok,
               hseqg, hmg⟩
          refine ef_join_inline fun _ _ => ?_
          refine wp_join_group (ts := []) (fun () m_x => m_x = mg) ?_ ?_
          · rintro _ ⟨⟩ m_x hm_x; rw [hm_x]; dsimp only [Blocks.get, Member.here]
            refine ef_join_inline fun _ _ => ?_
            ef_if hjg_same; have hu4 : 4 ≤ usz.toNat := (by bv_omega); clear hc
            ef_if hjg_same; have hu5 : usz.toNat ≤ 5 := (by bv_omega); clear hc
            ef_if hjg_same; clear hc; c0_hstraight!
            refine wp_call_of_spec _ _ (hExtractXorK _ _ _ _ ?_)
            change Spec.fullCongExtractXorKSpec (c.hdr, usz, neg_p, gl', g_cap, ()) _ _ _
            refine ef_extractXorK_spec hdg hws2g (hcvg.trans hcv_p.symm) hu4 hu5 hu_cv hhi' hg_cap
              (by rw [hcvg]; exact hseqg) hlt_u hneg_u hent_u hmg
              fun ret sx mx hlen_x hce hse hmk_x hret_lo hret_hi _ hseq_x hmx' => ?_
            c0_hstraight!
            exact hJnext (ret, tk' + 8#64, wn, ()) mx (ef_xorK_post hdg hcvg hflg hrepg hincg
              harg halg hwn_le hrr_g_ok hlen_x hce hse hmk_x (by omega) hret_hi hseq_x hmx')
          · intro Jelse hJelse; have hjelse : Jelse () mg := hJelse () mg rfl
            ef_if hjelse; have hu3 : usz = 3#32 := hc; clear hc
            have hu3_n : usz.toNat = 3 := congrArg BitVec.toNat hu3
            ef_if hjelse; have hgl12_le : gl'.toNat + 12 ≤ g_cap.toNat := (by bv_omega); clear hc
            have hws2_0 : (0#64 : BitVec 64).toNat < sg.scratch.work_stk2.length := by
              rw [hws2g, hws2_l]; bv_omega
            have hws2_1 : (1#64 : BitVec 64).toNat < sg.scratch.work_stk2.length := by
              rw [hws2g, hws2_l]; bv_omega
            have hws2_2 : (2#64 : BitVec 64).toNat < sg.scratch.work_stk2.length := by
              rw [hws2g, hws2_l]; bv_omega
            c0_hstraight!
            refine wp_call_of_spec _ _ (hTryXorIte _ _ _ _ ?_)
            change Spec.fullCongTryXorIteSpec (c.hdr, _, _, _, gl', g_cap, ()) _ _ _
            refine ef_tryXorIte_spec hdg (hcvg.trans hcv_p.symm) hu3_n (ef_ws2_get hws2g rfl)
              (ef_ws2_get hws2g rfl) (ef_ws2_get hws2g rfl) hlt_u hdiff_u hent_u (by omega)
              hg_cap (by rw [hcvg]; exact hseqg) hmg
              fun ret scr' mg' hscrl' hret_lo hret_hi _ hseq' hmg' => ?_
            c0_hstraight!
            exact hJnext (ret, tk' + 4#64, wn, ()) mg'
              ⟨{ sg with scratch := { sg.scratch with scratch_buf := scr' } },
               fullDenseInvW_with_scr hdg hscrl', hcvg, hflg, hrepg, hincg, harg, halg,
               by omega, hret_hi, hwn_le, hrr_g_ok, by rw [← hcvg]; exact hseq', hmg'⟩
        · intro Jg hJg
          have hjg0 : Jg (g_len, ticks + 1#64, ()) mb :=
            hJg (g_len, ticks + 1#64, ()) mb
              ⟨sb, hdb, hcv_p, hfl_p, hrep_p, hinc_p, har_p, hal_p, rfl, rfl,
               hgl_lo, hgl_hi, hseq_p, hmb⟩
          ef_if hjg0; clear hc; ef_if hjg0; clear hc; c0_hstraight!
          refine wp_call_of_spec _ _ (hExtAnd _ _ _ _ ?_)
          change Spec.fullCongExtractAndClauseFidSpec (c.hdr, usz, g_len, g_cap, tick_lim, ()) _ _ _
          refine ef_extAnd_spec (maxA := 64) (by unfold congAndArityMax; decide) hdb hu_lt3
            (by omega) hu_cv hgl_hi hg_cap (by rw [hcv_p]; exact hseq_p) hlt_u hdiff_u hent_u
            (by assumption) fun ret lm' scr' rsz' m' hdw' hlo' hhi' _ hseq' hm' => ?_
          c0_hstraight!
          exact hJg (ret, rsz', ()) m'
            ⟨_, hdw', hcv_p, hfl_p, hrep_p, hinc_p, har_p, hal_p, rfl, rfl,
             by omega, hhi', by rw [← hcv_p]; exact hseq', hm'⟩
    · rintro B3 L3 rem3 ⟨usz, max_nbc, min_nbc, neg_p, k, ⟨⟩⟩ mk hB3 hL3
        ⟨ws2, rfl, ⟨hws2_l, hk_le, hu_max, hu_k, hu_cv, hlt_u,
         ⟨idxs, hid_len, hid_nd, hid_lt, hws2_map, hcov_k⟩⟩, hneg_u, hmk⟩
      dsimp only [Blocks.get, Member.here]; c0_hstraight!; c0_hsplit
      · have hk_lt : k.toNat < sz_bv.toNat := ef_ult_eq hp2_arr (by bv_omega) hc
        have hk1_n : (k + 1#32).toNat = k.toNat + 1 := by bv_omega
        have hp3k_n : (p + 3#64 + k.setWidth 64).toNat = p.toNat + 3 + k.toNat :=
          bv64_add_zext32 (k := 3) (by omega)
        have hp3k_arr : (p + 3#64 + k.setWidth 64).toNat < sp.core.arena.length := by omega
        obtain ⟨hlk_eq, hlk_lt, hlk_v, hdom_lk⟩ :=
          ef_arena_lit_ok hdp hp_ref hng hsz_eq hbd_sz hk_lt hp3k_n hp3k_arr
        let lk := sp.core.arena[(p + 3#64 + k.setWidth 64).toNat]'hp3k_arr
        have hbrk_t : B3 (usz, max_nbc, min_nbc, neg_p, true, k, ()) mk :=
          hB3 (usz, max_nbc, min_nbc, neg_p, true, k, ()) mk
            ⟨ws2, hws2_l, (fun hf => by cases hf), hmk⟩
        clear hc; ef_unless hbrk_t
        have hnsgt := ef_vals_nsgt hlk_v (ef_arena_val_idx hp3k_arr (by bv_omega)) hc
        clear hc; c0_hstraight!; refine ef_join_inline fun _ _ => ?_
        c0_hstraight!; c0_hsplit
        · clear hc; ef_unless hbrk_t; have hu_ltm : usz.toNat < 1000001 := (by bv_omega); clear hc
          ef_unless hbrk_t
          have hu_lt_cv : usz.toNat < sp.core.cur_vars := by rw [hcv_p]; bv_omega
          have hu1_n : (usz + 1#32).toNat = usz.toNat + 1 := by bv_omega
          have hu_ws2 : usz.toNat < ws2.length := by omega
          have hu_ws2_64 : (usz.setWidth 64).toNat < ws2.length := by
            rw [bv_zext32_toNat]; exact hu_ws2
          have hlk_ws1 : (lk.setWidth 64).toNat < sp.scratch.work_stk1.length := by
            rw [bv_zext32_toNat, hws1_pl]; dsimp only [lk]; omega
          clear hc; c0_hstraight!
          let ws2' := ws2.set usz.toNat lk
          refine ef_capture_ws2 (ws2' := ws2') (by assumption)
            (ef_ws2_set_congr hp3k_arr (by bv_omega) (by bv_omega))
            fun m_st hm2' => ?_
          have hstep := ef_collect_append_ok hu_ws2 (by omega) hlk_eq hlk_lt hlt_u
            hid_len hid_nd hid_lt hws2_map hcov_k
          have hneg_st := ef_collect_negp_step hu_ws2 hneg_u (lk := lk)
          refine wp_join_group (ts := [i32]) (fun (_, ()) mmx => mmx = m_st) ?_ ?_
          · rintro _ ⟨mx', ⟨⟩⟩ mmx hmmx; rw [hmmx]
            dsimp only [Blocks.get, Member.here]; c0_hstraight!
            refine wp_join_group (ts := [i32]) (fun (_, ()) mmn => mmn = m_st) ?_ ?_
            · rintro _ ⟨mn', ⟨⟩⟩ mmn hmmn; rw [hmmn]
              dsimp only [Blocks.get, Member.here]; c0_hstraight!
              refine wp_join_group (ts := [i32])
                (fun (np', ()) mnp => mnp = m_st ∧
                  np' = if (lk &&& 1#32) != 0#32 then neg_p ^^^ 1#32 else neg_p) ?_ ?_
              · rintro _ ⟨neg_p', ⟨⟩⟩ mnp ⟨hmnp, rfl⟩; rw [hmnp]
                dsimp only [Blocks.get, Member.here]; c0_hstraight!
                exact hL3 (sz_bv.toNat - (k + 1#32).toNat)
                  (usz + 1#32, mx', mn', _, k + 1#32, ()) m_st (by omega)
                  ⟨ws2', rfl, ⟨by simp [ws2', hws2_l], by omega, by omega, by omega, by omega,
                    by rw [hu1_n]; exact hstep.1, by rw [hu1_n, hk1_n]; exact hstep.2⟩,
                   by rw [hu1_n]; exact hneg_st, hm2'⟩
              · intro Jnp hJnp; c0_hstraight!; c0_hsplit
                · have hbnz := ef_bit1_true hp3k_arr (by bv_omega) hc
                  clear hc; c0_hstraight!
                  exact hJnp (neg_p ^^^ 1#32, ()) m_st ⟨rfl, by dsimp only [lk]; rw [hbnz]; rfl⟩
                · have hbz := ef_bit1_false hp3k_arr (by bv_omega) hc
                  clear hc; c0_hstraight!
                  exact hJnp (neg_p, ()) m_st ⟨rfl, by dsimp only [lk]; rw [hbz]; rfl⟩
            · intro Jmn hJmn; c0_hstraight!; c0_hsplit <;>
                (clear hc; c0_hstraight!; exact hJmn (_, ()) m_st rfl)
          · intro Jmx hJmx; c0_hstraight!; c0_hsplit <;>
              (clear hc; c0_hstraight!; exact hJmx (_, ()) m_st rfl)
        · have hne0 := ef_vals_ne0 hlk_v (ef_arena_val_idx hp3k_arr (by bv_omega)) hc
          clear hc; c0_hstraight!
          have hcov_nx := ef_collect_false_ok (by omega) hlk_eq hdom_lk hnsgt hne0 hcov_k
          exact hL3 (sz_bv.toNat - (k + 1#32).toNat)
            (usz, max_nbc, min_nbc, neg_p, k + 1#32, ()) mk (by omega)
            ⟨ws2, rfl, ⟨hws2_l, by omega, hu_max, by omega, hu_cv, hlt_u,
              ⟨idxs, hid_len, hid_nd, fun q hq => by have := hid_lt q hq; omega, hws2_map,
               by rw [hk1_n]; exact hcov_nx⟩⟩, hneg_u, hmk⟩
      · have hk_e : k.toNat = sz_bv.toNat := ef_nult_eq hp2_arr (by bv_omega) hk_le hc
        obtain ⟨hdiff_u, hent_u⟩ := ef_clause_collect_done hdp hp_ref hng hsz_eq
          hbd_sz (by omega) hid_len hid_nd (hk_e ▸ hid_lt) hws2_map (hk_e ▸ hcov_k)
        clear hc; c0_hstraight!
        exact hB3 (usz, max_nbc, min_nbc, neg_p, false, k, ()) mk
          ⟨ws2, hws2_l, fun _ => ⟨⟨hu_max, hu_cv, hlt_u, hdiff_u, hent_u⟩, hneg_u⟩, hmk⟩
    · intro _ L3 _ hL3; c0_hstraight!
      exact hL3 sz_bv.toNat (0#32, 0#32, 0xFFFFFFFF#32, 0#32, 0#32, ()) mp
        ⟨sp.scratch.work_stk2, rfl, ef_collect_init hws2_pl, (by simp), hmp⟩

end

end LeanQbe.T.Examples.Kissat.Proof.Congruence
