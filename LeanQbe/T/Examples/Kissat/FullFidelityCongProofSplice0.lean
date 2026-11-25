/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityCongProof0
public import LeanQbe.T.Examples.Kissat.FullM8CoreParityProofSplice
public import LeanQbe.T.Examples.Kissat.PatchModule
import all LeanQbe.T.Examples.Kissat.FullM8CoreParityProof
import all LeanQbe.T.Examples.Kissat.FullM8CoreParityProofSplice
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof
import all LeanQbe.T.Examples.Kissat.FullM7FidelityAssemblyProof0
import all LeanQbe.T.Examples.Kissat.FullM7Transport0
import all LeanQbe.T.Examples.Kissat.FullM7Transport1
import all LeanQbe.T.Examples.Kissat.FullM8FidV12Proof
import all LeanQbe.T.Examples.Kissat.FullM8SweepV2Proof
import all LeanQbe.T.Examples.Kissat.FullM6CongSubstProof2c
import all LeanQbe.T.Examples.Kissat.FullM6OrchAdaptersProof0
import all LeanQbe.T.Examples.Kissat.FullM6SweepProofSpec
import all LeanQbe.T.Examples.Kissat.FullM7CongIteProof0
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb

/-!
# Kissat Congruence Parity Splice Helpers & Base `ModuleOk` (`FullFidelityCongProofSplice0`)

Certifies `m8SweepV2CoreParity_ofTable_moduleOk : ModuleOk (Env.ofTable ...) m8SweepV2...`
plus reusable `Env.ofTable` / `patchRows` / inactive-`work_step` transport helpers so
`FullFidelityCongProofSplice` stays lean, fast, and free of `import all`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityCong

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open Kraken.Bedrock2.Test
open LeanQbe.T.Examples.LratBytes
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullCongHelpers
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open scoped Full.FullArenaTactics Full.FullCongTactics
open scoped LeanQbe.T.Examples.Kissat.FullM6CongSubst.M6bHeadTactics
open LeanQbe.T.Examples.Kissat.FullM3CongBva
open LeanQbe.T.Examples.Kissat.FullM6
open LeanQbe.T.Examples.Kissat.FullM6Orch
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open LeanQbe.T.Examples.Kissat.FullM6CongSubst
open LeanQbe.T.Examples.Kissat.FullM7CongIte
open LeanQbe.T.Examples.Kissat.FullM7
open LeanQbe.T.Examples.Kissat.FullM7Proof
open LeanQbe.T.Examples.Kissat.FullM7Fidelity
open LeanQbe.T.Examples.Kissat.FullM8FidV12
open LeanQbe.T.Examples.Kissat.FullM8SweepV2
open LeanQbe.T.Examples.Kissat.FullM8CoreParity

/-! ## 1. `Env.ofTable` / `patchRows` Transport & `work_step` Parameterization -/

theorem sp_ofTable_append_left {p t : List SpecEntry} {f : Sym} {as bs : List Ty}
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : Env.ofTable p f as bs xs m Q X) : Env.ofTable (p ++ t) f as bs xs m Q X := by
  induction p with
  | nil => exact False.elim h
  | cons hd tl ih =>
    rw [List.cons_append]
    rcases h with ⟨hs, hc⟩ | ⟨hne, htl⟩
    · exact Or.inl ⟨hs, hc⟩
    · exact Or.inr ⟨hne, ih htl⟩

theorem sp_ofTable_patchRows_of_not_mem {rRows tbl : List SpecEntry}
    {bRows : List (Sym × List SpecEntry)} {f : Sym} {as bs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post bs} {X : XPost}
    (hnr : f ∉ rRows.map SpecEntry.name)
    (hnb : f ∉ (bRows.flatMap Prod.snd).map SpecEntry.name)
    (h : Env.ofTable tbl f as bs xs m Q X) :
    Env.ofTable (PatchModule.patchRows rRows bRows tbl) f as bs xs m Q X := by
  induction tbl with
  | nil => exact False.elim h
  | cons hd tl ih =>
    simp only [PatchModule.patchRows, List.flatMap_cons, List.append_assoc]
    have hnb_hd : ¬ (∃ e ∈ PatchModule.patchRowInsAt bRows hd, e.name = f) := by
      rintro ⟨e, he, hnm⟩
      unfold PatchModule.patchRowInsAt at he
      split at he
      · rename_i tgt ins hfind
        exact hnb (List.mem_map.mpr ⟨e, List.mem_flatMap.mpr
          ⟨(tgt, ins), List.mem_of_find?_eq_some hfind, he⟩, hnm⟩)
      · exact nomatch he
    have hins_lift : ∀ {k : List SpecEntry},
        Env.ofTable k f as bs xs m Q X →
        Env.ofTable (PatchModule.patchRowInsAt bRows hd ++ k) f as bs xs m Q X := by
      intro k hk
      suffices ∀ l : List SpecEntry,
          (∀ e ∈ l, e.name ≠ f) → Env.ofTable (l ++ k) f as bs xs m Q X by
        exact this _ fun e he hnm => hnb_hd ⟨e, he, hnm⟩
      intro l hl
      induction l with
      | nil => exact hk
      | cons a l' ihl =>
        rw [List.cons_append]
        exact Or.inr ⟨fun ⟨hn, _⟩ => hl a List.mem_cons_self hn,
          ihl (fun e he => hl e (List.mem_cons_of_mem _ he))⟩
    refine hins_lift ?_
    rw [List.cons_append, List.nil_append]
    rcases h with ⟨⟨hn, ha, hb⟩, hcast⟩ | ⟨hne, htl⟩
    · have hfind : rRows.find? (·.name == hd.name) = none := by
        rw [List.find?_eq_none]
        intro r hr hbeq
        exact hnr (List.mem_map.mpr ⟨r, hr, (beq_iff_eq.mp hbeq).trans hn⟩)
      simp only [hfind, Option.getD_none]
      exact Or.inl ⟨⟨hn, ha, hb⟩, hcast⟩
    · refine Or.inr ⟨fun hcur => ?_, ih htl⟩
      cases hf : rRows.find? (·.name == hd.name) with
      | none => rw [hf, Option.getD_none] at hcur; exact hne hcur
      | some r =>
        rw [hf, Option.getD_some] at hcur
        exact hnr (List.mem_map.mpr ⟨r, List.mem_of_find?_eq_some hf, hcur.1⟩)

theorem m6CongEvalGateSpec_inactive_to_m8
    {hh g ht_off ht_sz ctrl_off : BitVec 64} {next_ep32 : BitVec 32} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (h : ∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
      (scr0 : List (BitVec 32)) (g_len : Nat) (R : Mem 64 → Prop),
      hh = c.hdr ∧ ctrl_off.toNat = c.scratch_cap ∧ FullDenseInvW c F0 F_cur s ∧
      FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
      0 < ht_sz.toNat ∧ ht_sz.toNat < 2 ^ 30 ∧
      g.toNat < g_len ∧ g_len ≤ ht_off.toNat ∧ ht_off.toNat + ht_sz.toNat ≤ c.scratch_cap ∧
      (∀ idx < g_len, s.scratch.scratch_buf[idx]? = scr0[idx]?) ∧
      M6GateAt F_cur s.core.cur_vars scr0 g_len g.toNat ∧
      M6CongHtInv F_cur s.core.cur_vars scr0 s.scratch.scratch_buf g_len ht_off.toNat ht_sz.toNat ∧
      (FullMem c s ⋆ R) m ∧
      ∀ (r : BitVec 64) s' m',
        FullDenseInvW c F0 F_cur s' →
        s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
        s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
        FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
        (∀ idx < g_len, s'.scratch.scratch_buf[idx]? = scr0[idx]?) →
        M6CongHtInv F_cur s'.core.cur_vars scr0 s'.scratch.scratch_buf
          g_len ht_off.toNat ht_sz.toNat →
        ((r &&& 2#64) = 0#64 →
          ∀ idx < c.scratch_cap, idx < ht_off.toNat →
            s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?) →
        ((r &&& 2#64) ≠ 0#64 → F0.Unsat) →
        (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    m8CongEvalGateSpec (hh, g, ht_off, ht_sz, next_ep32, ctrl_off, ()) m Q X := by
  rcases h with ⟨c, F0, F_cur, s, scr0, g_len, R, rfl, hcap, hdw, hrepr, hht_pos, hht_bnd, hg_lt,
    hg_le_ht, hht_le, hpref, hgat, hht, hm, hQ⟩
  refine ⟨c, F0, F_cur, s, scr0, g_len, R, rfl, hdw, hrepr, hht_pos, hht_bnd, hg_lt, hg_le_ht,
    hht_le, hpref, hgat, hht, Or.inl hcap, hm, ?_⟩
  intro r s' m' hdw' hcv' hfl' har' hal' hrepr' hpref' hht' _hq' hfr' huns' hm'
  exact hQ r s' m' hdw' hcv' hfl' har' hal' hrepr' hpref' hht'
    (fun hr2 idx h1 h2 => (hfr' hr2 idx h1 h2).1 hcap) huns' hm'

private theorem sp_bv32_ult_lt {a b : BitVec 32} (h : a.ult b = true) : a.toNat < b.toNat := by
  simpa [BitVec.ult] using h

private theorem sp_bv64_ult_lt {a b : BitVec 64} (h : a.ult b = true) : a.toNat < b.toNat := by
  simpa [BitVec.ult] using h

private theorem sp_bv32_add1_lt {a : BitVec 32} (h : a.toNat + 1 < 2 ^ 32) :
    (a + 1#32).toNat = a.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#32 : BitVec 32).toNat = 1 from rfl, Nat.mod_eq_of_lt h]

private theorem sp_bv_zext32 (x : BitVec 32) : (x.setWidth 64).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

private theorem sp_bv64_add1_toNat {a : BitVec 64} {n : Nat} (ha : a.toNat < n)
    (hn : n < 2 ^ 64) : (a + 1#64).toNat = a.toNat + 1 := by
  rw [BitVec.toNat_add, show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt (by omega)]

private theorem sp_bv64_add_zext32 {a : BitVec 64} {k : Nat} {b : BitVec 32}
    (h : a.toNat + k + b.toNat < 2 ^ 64) :
    (a + BitVec.ofNat 64 k + b.setWidth 64).toNat = a.toNat + k + b.toNat := by
  have hk : k < 2 ^ 64 := by omega
  rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_ofNat, sp_bv_zext32,
    Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt (show a.toNat + k < 2 ^ 64 from by omega),
    Nat.mod_eq_of_lt h]

private theorem sp_bv32_div2_lt {l : BitVec 32} {n : Nat} (hl : l.toNat < 2 * n) :
    (l >>> 1#32).toNat < n := by
  rw [show (l >>> 1#32 : BitVec 32) = l >>> (1 : Nat) from rfl,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
  omega

private theorem sp_scr_eq_pref {scr scr0 : List (BitVec 32)} {g_len idx : Nat}
    (hpref : ∀ k < g_len, scr[k]? = scr0[k]?) (hidx : idx < g_len)
    (hl : idx < scr.length) {v : BitVec 32} (h0 : scr0[idx]? = some v) :
    scr[idx]'hl = v := by
  have h := (hpref idx hidx).trans h0
  rw [List.getElem?_eq_getElem hl] at h; exact Option.some.inj h

theorem workStep_wp_of_inactive_eval (Γ : Env)
    (hFind : ∀ a m Q X, Full.fullCongFindSpec a m Q X →
      Γ "full_cong_find" [i64, i32] [i32] a m Q X)
    (hEvalInact : ∀ {hh g ht_off ht_sz ctrl_off : BitVec 64} {next_ep32 : BitVec 32}
      {m : Mem 64} {Q : Post [i64]} {X : XPost},
      (∃ (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat)) (s : FullState)
        (scr0 : List (BitVec 32)) (g_len : Nat) (R : Mem 64 → Prop),
        hh = c.hdr ∧ ctrl_off.toNat = c.scratch_cap ∧ FullDenseInvW c F0 F_cur s ∧
        FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr ∧
        0 < ht_sz.toNat ∧ ht_sz.toNat < 2 ^ 30 ∧
        g.toNat < g_len ∧ g_len ≤ ht_off.toNat ∧ ht_off.toNat + ht_sz.toNat ≤ c.scratch_cap ∧
        (∀ idx < g_len, s.scratch.scratch_buf[idx]? = scr0[idx]?) ∧
        M6GateAt F_cur s.core.cur_vars scr0 g_len g.toNat ∧
        M6CongHtInv F_cur s.core.cur_vars scr0 s.scratch.scratch_buf
          g_len ht_off.toNat ht_sz.toNat ∧
        (FullMem c s ⋆ R) m ∧
        ∀ (r : BitVec 64) s' m',
          FullDenseInvW c F0 F_cur s' →
          s'.core.cur_vars = s.core.cur_vars → s'.core.fuel = s.core.fuel →
          s'.core.arena = s.core.arena → s'.core.arena_len = s.core.arena_len →
          FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
          (∀ idx < g_len, s'.scratch.scratch_buf[idx]? = scr0[idx]?) →
          M6CongHtInv F_cur s'.core.cur_vars scr0 s'.scratch.scratch_buf
            g_len ht_off.toNat ht_sz.toNat →
          ((r &&& 2#64) = 0#64 →
            ∀ idx < c.scratch_cap, idx < ht_off.toNat →
              s'.scratch.scratch_buf[idx]? = s.scratch.scratch_buf[idx]?) →
          ((r &&& 2#64) ≠ 0#64 → F0.Unsat) →
          (FullMem c s' ⋆ R) m' → Q (r, ()) m') →
      Γ "full_cong_eval_gate" [i64, i64, i64, i64, i32, i64] [i64]
        (hh, g, ht_off, ht_sz, next_ep32, ctrl_off, ()) m Q X) :
    ∀ a m Q X, FullM6CongSubst.m6CongWorkStepSpec a m Q X →
      Func.wp Γ FullM6CongSubst.full_cong_work_step_body a m Q X := by
  rintro ⟨h, g_len, ht_off, ht_sz, cur_ep, ⟨⟩⟩ m0 Q X
    ⟨c, F0, F_cur, s0, scr0, R, rfl, hdw0, hrepr0, hht_pos, hht_bnd, hg_le_ht, hht_le,
     hseq0, hpref0, hht0, hm0, hQ⟩
  have hsc := c.hscr; have hmx := c.hmaxv; unfold dimacsBound at hsc hmx
  let cv0 := s0.core.cur_vars; let fuel0 := s0.core.fuel
  let ar0 := s0.core.arena; let alen0 := s0.core.arena_len
  m6b_steps
  refine wp_loop_inv (ts := [.bool, i64, i64])
    (fun (changed, work, g, ()) mg => ∃ st : FullState,
      g.toNat ≤ g_len.toNat ∧
      M6WstOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat ht_off.toNat ht_sz.toNat scr0 st ∧
      M6GateSeqOk F_cur cv0 scr0 g_len.toNat g.toNat ∧ (FullMem c st ⋆ R) mg)
    (fun (_ch, _wk, g, ()) _ => g_len.toNat - g.toNat)
    (fun Jg hJg => by
      m6b_steps; exact hJg (false, 0#64, 0#64, ()) m0 ⟨s0, Nat.zero_le _,
        ⟨hdw0, rfl, rfl, rfl, rfl, hrepr0, hpref0, hht0⟩, hseq0, hm0⟩)
    (fun Jg (changed, work, g, ()) mg ⟨st, hg_le, hok_t, hseq_t, hmg⟩ ihg => ?_)
  have ⟨hdw_t, hcv_t, hfl_t, har_t, hal_t, hrepr_t, hpref_t, hht_t⟩ := hok_t
  have hscrl_t := hdw_t.1.scratch_ok.scratch_buf_len
  have hcv_le := hdw_t.1.core_ok.cur_vars_le
  have hcv0_le : cv0 ≤ c.max_vars := hcv_t ▸ hcv_le
  have htmpl_t := hdw_t.1.core_ok.tmp_len_arr
  have hrl_t := hdw_t.1.core_ok.repr_len
  have htmkl_t := hdw_t.1.scratch_ok.tarjan_mark_len
  m6b_to_group
  refine wp_join_group (ts := [])
    (fun () m_ex => ∃ ste : FullState,
      M6WstOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat ht_off.toNat ht_sz.toNat scr0 ste ∧
      (FullMem c ste ⋆ R) m_ex)
    (fun _ ⟨⟩ m_ex ⟨ste, hoke, hme⟩ => by
      m6b_to_group
      refine wp_join_group (ts := [i64])
        (fun (st_v, ()) m_st =>
          st_v = (if ste.core.inconsistent ≠ 0#64 then 2#64
                  else if changed then 1#64 else 0#64) ∧ m_st = m_ex)
        (fun _ ⟨st_v, ⟨⟩⟩ m_st ⟨hst_v, hm_eq⟩ => by
          subst m_st; m6b_steps
          have ⟨hdwe, hcve, hfle, hare, hale, hrepre, hprefe, hhte⟩ := hoke
          have hst_lt : st_v.toNat < 4 := by
            rw [hst_v]
            by_cases hinc : ste.core.inconsistent ≠ 0#64
            · rw [ite_eq_left hinc]; decide
            · rw [ite_eq_right hinc]; cases changed <;> decide
          have hst_dom : (work <<< 2#64 ||| st_v) &&& 3#64 = 0#64 ∨
              (work <<< 2#64 ||| st_v) &&& 3#64 = 1#64 ∨
              (work <<< 2#64 ||| st_v) &&& 3#64 = 2#64 := by
            rw [bv64_shl2_or_and3 work st_v hst_lt, hst_v]
            by_cases hinc : ste.core.inconsistent ≠ 0#64
            · rw [ite_eq_left hinc]; exact Or.inr (Or.inr rfl)
            · rw [ite_eq_right hinc]; cases changed <;> simp
          have hst_unsat : (work <<< 2#64 ||| st_v) &&& 3#64 = 2#64 → F0.Unsat := by
            intro h2; rw [bv64_shl2_or_and3 work st_v hst_lt, hst_v] at h2
            by_cases hinc : ste.core.inconsistent ≠ 0#64
            · exact unsat_of_inconsistent_w hdwe.2.1 hinc
            · rw [ite_eq_right hinc] at h2; cases changed <;> cases h2
          exact hQ (work <<< 2#64 ||| st_v) ste m_ex hdwe hcve hfle hare hale
            (hcve ▸ hrepre) hprefe (hcve ▸ hhte) hst_dom hst_unsat hme)
        (fun Jst hJst => by
          m6b_split
          · have hne : ste.core.inconsistent ≠ 0#64 := bne_iff_ne.mp hc
            m6b_let; exact hJst (2#64, ()) m_ex ⟨by rw [ite_eq_left hne], rfl⟩
          · have heq0 : ¬ ste.core.inconsistent ≠ 0#64 := by simpa using hc
            m6b_to_group
            refine wp_join_group (ts := [i64])
              (fun (vc, ()) mc => vc = (if changed then 1#64 else 0#64) ∧ mc = m_ex)
              (fun _ ⟨vc, ⟨⟩⟩ mc ⟨hvc, hmc⟩ => by
                m6b_let; exact hJst (vc, ()) mc ⟨by rw [ite_eq_right heq0]; exact hvc, hmc⟩)
              (fun Jch hJch => by
                m6b_split
                · m6b_let; exact hJch (1#64, ()) m_ex ⟨by rw [ite_eq_left hc], rfl⟩
                · have hnch : ¬ changed = true := by intro h; rw [h] at hc; cases hc
                  m6b_let; exact hJch (0#64, ()) m_ex ⟨by rw [ite_eq_right hnch], rfl⟩)))
    ?_
  intro Jex hJex
  m6b_split
  · have hg_lt : g.toNat < g_len.toNat := sp_bv64_ult_lt hc
    clear hc; m6b_split
    · clear hc
      obtain ⟨hgat, hseq_next⟩ := m6GateSeqOk_inv_lt hseq_t hg_lt
      have ⟨lhs0, mword, hscr0_g, hscr0_g1, hlhs0_lt, hbd_g, har_cv, _, hrhs0, _⟩ := hgat
      have hg_arr : g.toNat < st.scratch.scratch_buf.length := by omega
      have hg1_n : (g + 1#64).toNat = g.toNat + 1 := sp_bv64_add1_toNat (by omega) (by omega)
      have hg1_arr : (g + 1#64).toNat < st.scratch.scratch_buf.length := by omega
      have hst_g : st.scratch.scratch_buf[g.toNat]'hg_arr = lhs0 :=
        sp_scr_eq_pref hpref_t hg_lt hg_arr hscr0_g
      have hst_g1 : st.scratch.scratch_buf[(g + 1#64).toNat]'hg1_arr = mword :=
        sp_scr_eq_pref hpref_t (by omega) hg1_arr (by rw [hg1_n]; exact hscr0_g1)
      let arity := mword &&& 0xFF#32
      have har_cv' : arity.toNat ≤ cv0 := har_cv
      have hbd_g' : g.toNat + 2 + arity.toNat ≤ g_len.toNat := hbd_g
      have hnext_g : (g + 2#64 + arity.setWidth 64).toNat = g.toNat + 2 + arity.toNat :=
        sp_bv64_add_zext32 (by omega)
      have hseq_next' : M6GateSeqOk F_cur cv0 scr0 g_len.toNat
          (g + 2#64 + arity.setWidth 64).toNat := by
        rw [hnext_g]; simpa [hscr0_g1, arity] using hseq_next
      m6b_steps; m6b_call hFind
      refine ⟨F_cur, 2 * cv0, st.core.repr, FullReprRest c st ⋆ R, hrepr_t,
        by rw [hst_g]; exact hlhs0_lt, focus_full_repr hmg,
        fun lhs repr1 m1 hrl1 hrepr1 _ hlhs_lt _ hm1 => ?_⟩
      have hm1' : (FullMem c (wsState st repr1 st.core.tmp) ⋆ R) m1 := unfocus_full_repr hm1
      clear hm1
      have hrl1' : repr1.length = 2 * c.max_vars := hrl1.trans hrl_t
      have hlhs0_v_lt : ((lhs0 >>> 1#32).setWidth 64).toNat < st.scratch.tarjan_mark.length := by
        rw [sp_bv_zext32]; have := sp_bv32_div2_lt hlhs0_lt; omega
      have hstg_v_lt :
          ((st.scratch.scratch_buf[g.toNat]'hg_arr >>> 1#32).setWidth 64).toNat <
            st.scratch.tarjan_mark.length := by
        rw [hst_g]; exact hlhs0_v_lt
      have hlhs_v_lt : ((lhs >>> 1#32).setWidth 64).toNat < st.scratch.tarjan_mark.length := by
        rw [sp_bv_zext32]; have := sp_bv32_div2_lt hlhs_lt; omega
      m6b_to_group
      refine wp_join_group (ts := [.bool]) (fun _ md => md = m1)
        (fun _ ⟨dty0, ⟨⟩⟩ md hmd => by
          subst md; m6b_to_group
          refine wp_loop_inv (ts := [.bool, i32])
            (fun (_dty, i, ()) mi => ∃ repri : List (BitVec 32),
              repri.length = 2 * c.max_vars ∧ i.toNat ≤ arity.toNat ∧
              FullCongReprInv F_cur (2 * cv0) repri ∧
              (FullMem c (wsState st repri st.core.tmp) ⋆ R) mi)
            (fun (_, i, ()) _ => arity.toNat - i.toNat)
            (fun Ji hJi => by
              m6b_steps; exact hJi (dty0, 0#32, ()) m1 ⟨repr1, hrl1', Nat.zero_le _, hrepr1, hm1'⟩)
            (fun Ji (dty, i, ()) mi ⟨repri, hrli, hi_le, hrepri, hmi⟩ ihi => ?_)
          have hoki := m6WstOk_wsState hok_t hrli htmpl_t hrepri
          m6b_to_group
          refine wp_join_group (ts := [])
            (fun () m_after => ∃ repri' : List (BitVec 32),
              repri'.length = 2 * c.max_vars ∧ FullCongReprInv F_cur (2 * cv0) repri' ∧
              (FullMem c (wsState st repri' st.core.tmp) ⋆ R) m_after)
            (fun _ ⟨⟩ m_after ⟨repri', hrli', hrepri', hma⟩ => by
              have hoki' := m6WstOk_wsState hok_t hrli' htmpl_t hrepri'
              m6b_split
              · clear hc; m6b_steps
                refine wp_call_of_spec _ _ (hEvalInact ?_)
                dsimp only [Arg.val_var, Arg.val_imm]
                refine ⟨c, F0, F_cur, wsState st repri' st.core.tmp, scr0, g_len.toNat, R,
                  rfl, by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)],
                  hoki'.1, hoki'.2.1 ▸ hoki'.2.2.2.2.2.1, hht_pos, hht_bnd, hg_lt, hg_le_ht,
                  hht_le, hoki'.2.2.2.2.2.2.1, hoki'.2.1 ▸ hgat, hoki'.2.1 ▸ hoki'.2.2.2.2.2.2.2,
                  hma, fun er sj mj hdwj hcvj hflj harj halej hreprj hprefj hhtj _ he2_u hmj => ?_⟩
                have hokj : M6WstOk c F0 F_cur fuel0 ar0 alen0 cv0 g_len.toNat ht_off.toNat
                    ht_sz.toNat scr0 sj :=
                  ⟨hdwj, hcvj.trans hcv_t, hflj.trans hfl_t, harj.trans har_t, halej.trans hal_t,
                   (hcvj.trans hcv_t) ▸ hreprj, hprefj, (hcvj.trans hcv_t) ▸ hhtj⟩
                m6b_split
                · have he2_ne : (er &&& 2#64) ≠ 0#64 := bne_iff_ne.mp hc
                  m6b_steps
                  have h2 : ((((work + 4#64) <<< 2#64) ||| 2#64) &&& 3#64) = 2#64 :=
                    bv64_shl2_or_and3 (work + 4#64) 2#64 (by decide)
                  exact hQ _ sj mj hdwj (hcvj.trans hcv_t) (hflj.trans hfl_t)
                    (harj.trans har_t) (halej.trans hal_t)
                    ((hcvj.trans hcv_t) ▸ hreprj) hprefj ((hcvj.trans hcv_t) ▸ hhtj)
                    (Or.inr (Or.inr (by exact h2))) (fun _ => he2_u he2_ne) hmj
                · clear hc; m6b_to_group
                  refine wp_join_group (ts := [.bool]) (fun _ mc => mc = mj)
                    (fun _ ⟨ch', ⟨⟩⟩ mc hmc => by
                      subst mc; m6b_steps; erw [hst_g1]
                      exact ihg (ch', work + 4#64, g + 2#64 + arity.setWidth 64, ()) mj
                        (by dsimp only; rw [hnext_g]; omega)
                        ⟨sj, by rw [hnext_g]; exact hbd_g', hokj, hseq_next', hmj⟩)
                    (fun Jch' hJch' => by
                      m6b_split
                      · m6b_let; exact hJch' (true, ()) mj rfl
                      · m6b_let; exact hJch' (changed, ()) mj rfl)
              · m6b_steps; erw [hst_g1]
                exact ihg (changed, work + 1#64, g + 2#64 + arity.setWidth 64, ()) m_after
                  (by dsimp only; rw [hnext_g]; omega)
                  ⟨wsState st repri' st.core.tmp, by rw [hnext_g]; exact hbd_g', hoki',
                   hseq_next', hma⟩)
            (fun Jexit hJexit => by
              m6b_steps; m6b_split
              · have hi_lt : i.toNat < arity.toNat :=
                  sp_bv32_ult_lt (by erw [hst_g1] at hc; exact hc)
                m6b_split
                · m6b_let; exact hJexit () mi ⟨repri, hrli, hrepri, hmi⟩
                · obtain ⟨ri, hri_get, hri_lt⟩ := hrhs0 i.toNat hi_lt
                  have hg2i_n : (g + 2#64 + i.setWidth 64).toNat = g.toNat + 2 + i.toNat :=
                    sp_bv64_add_zext32 (by omega)
                  have hg2i_arr : (g + 2#64 + i.setWidth 64).toNat <
                      st.scratch.scratch_buf.length := by
                    rw [hg2i_n]; omega
                  have hst_g2i : st.scratch.scratch_buf[(g + 2#64 + i.setWidth 64).toNat]'
                      hg2i_arr = ri :=
                    sp_scr_eq_pref hpref_t (by omega) hg2i_arr (by rw [hg2i_n]; exact hri_get)
                  have hri_tmk : ((ri >>> 1#32).setWidth 64).toNat <
                      st.scratch.tarjan_mark.length := by
                    rw [sp_bv_zext32]; have := sp_bv32_div2_lt hri_lt; omega
                  have hstg2i_tmk :
                      ((st.scratch.scratch_buf[(g + 2#64 + i.setWidth 64).toNat]'hg2i_arr >>>
                        1#32).setWidth 64).toNat < st.scratch.tarjan_mark.length := by
                    rw [hst_g2i]; exact hri_tmk
                  have hi1_n : (i + 1#32).toNat = i.toNat + 1 := sp_bv32_add1_lt (by omega)
                  clear hc; m6b_steps; m6b_call hFind
                  refine ⟨F_cur, 2 * cv0, repri,
                    FullReprRest c (wsState st repri st.core.tmp) ⋆ R, hrepri,
                    by dsimp only [wsState]; erw [hst_g2i]; exact hri_lt, focus_full_repr hmi,
                    fun rval repri' mi' hrl_i' hrepr_i' _ hrval_lt _ hmi' => ?_⟩
                  have hmi'' : (FullMem c (wsState st repri' st.core.tmp) ⋆ R) mi' :=
                    unfocus_full_repr hmi'
                  clear hmi'
                  have hrval_tmk :
                      ((rval >>> 1#32).setWidth 64).toNat < st.scratch.tarjan_mark.length := by
                    rw [sp_bv_zext32]; have := sp_bv32_div2_lt hrval_lt; omega
                  m6b_to_group; refine wp_join_group (ts := [.bool])
                    (fun (_dty', ()) md' => md' = mi')
                    (fun _ ⟨dty', ⟨⟩⟩ md' hmd' => by
                      subst md'; m6b_let
                      exact ihi (dty', i + 1#32, ()) mi' (by dsimp only; omega)
                        ⟨repri', hrl_i'.trans hrli, by omega, hrepr_i', hmi''⟩)
                    (fun Jd' hJd' => by
                      m6b_split
                      · m6b_steps; exact hJd' (true, ()) mi' rfl
                      · m6b_split
                        · m6b_steps; exact hJd' (true, ()) mi' rfl
                        · m6b_let; exact hJd' (dty, ()) mi' rfl)
              · m6b_let; exact hJexit () mi ⟨repri, hrli, hrepri, hmi⟩))
        (fun Jd hJd => by
          m6b_split
          · m6b_let; exact hJd (true, ()) m1 rfl
          · m6b_split
            · m6b_steps; exact hJd (true, ()) m1 rfl
            · m6b_let; exact hJd (false, ()) m1 rfl)
    · m6b_let; exact hJex () mg ⟨st, hok_t, hmg⟩
  · m6b_let; exact hJex () mg ⟨st, hok_t, hmg⟩

private theorem sp_mfExtraBase_sub_m7FidBaseTable :
    ∀ e ∈ mfExtraBaseRows, e ∈ m7FidBaseTable := by
  have hviv0 := m7FidBase_part2_mem
  have sub_hdr0 : ∀ e ∈ FullM7Fidelity.p1Hdr0ExactRows, e ∈ m7FidBaseTable := fun _ h =>
    m7FidBase_part1_mem _ (by
      unfold m7FidRowsPart1
      (iterate 11 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_bcp : ∀ e ∈ FullM7Fidelity.p1BcpHotRows, e ∈ m7FidBaseTable := fun _ h =>
    m7FidBase_part1_mem _ (by
      unfold m7FidRowsPart1
      (iterate 14 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_hb : ∀ e ∈ p2HasBinRows, e ∈ m7FidBaseTable := fun _ h =>
    hviv0 _ (by
      unfold m7RowsPart2
      (iterate 30 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_mm : ∀ e ∈ p2MinMarkRows, e ∈ m7FidBaseTable := fun _ h =>
    hviv0 _ (by
      unfold m7RowsPart2
      (iterate 7 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_ms0 : ∀ e ∈ p2MinShrink0Rows, e ∈ m7FidBaseTable := fun _ h =>
    hviv0 _ (by
      unfold m7RowsPart2
      (iterate 4 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_st : ∀ e ∈ p2SortTmpM7Rows, e ∈ m7FidBaseTable := fun _ h =>
    hviv0 _ (by
      unfold m7RowsPart2
      (iterate 9 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_ms1 : ∀ e ∈ p2MinShrink1Rows, e ∈ m7FidBaseTable := fun _ h =>
    hviv0 _ (by
      unfold m7RowsPart2
      (iterate 10 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_wlk : ∀ e ∈ p2M7Walk13Rows, e ∈ m7FidBaseTable := fun _ h =>
    hviv0 _ (by
      unfold m7RowsPart2
      (iterate 22 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_ab : ∀ e ∈ p2AddBinM6Rows, e ∈ m7FidBaseTable := fun _ h =>
    hviv0 _ (by
      unfold m7RowsPart2
      (iterate 32 apply List.mem_append_right); exact List.mem_append_left _ h)
  have sub_v1 : ∀ e ∈ p2VivBb1Rows, e ∈ m7FidBaseTable := fun _ h =>
    hviv0 _ (by
      unfold m7RowsPart2
      (iterate 40 apply List.mem_append_right); exact List.mem_append_left _ h)
  intro e he
  simp only [mfExtraBaseRows, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | h1) | h2
  · exact sub_hdr0 _ (List.mem_of_getElem? (i := 2) rfl)
  · exact sub_hdr0 _ (List.mem_of_getElem? (i := 4) rfl)
  · exact sub_bcp _ (List.mem_of_getElem? (i := 0) rfl)
  · exact sub_bcp _ (List.mem_of_getElem? (i := 1) rfl)
  · exact sub_hb _ (List.mem_of_getElem? (i := 0) rfl)
  · exact sub_mm _ (List.mem_of_getElem? (i := 0) rfl)
  · exact sub_ms0 _ (List.mem_of_getElem? (i := 0) rfl)
  · exact sub_ms0 _ (List.mem_of_getElem? (i := 1) rfl)
  · exact sub_st _ (List.mem_of_getElem? (i := 1) rfl)
  · exact sub_st _ (List.mem_of_getElem? (i := 2) rfl)
  · exact sub_st _ (List.mem_of_getElem? (i := 3) rfl)
  · exact sub_ms1 _ (List.mem_of_getElem? (i := 0) rfl)
  · exact sub_ms1 _ (List.mem_of_getElem? (i := 2) rfl)
  · exact sub_ms1 _ (List.mem_of_getElem? (i := 3) rfl)
  · exact sub_wlk _ (List.mem_of_getElem? (i := 0) rfl)
  · exact sub_wlk _ (List.mem_of_getElem? (i := 1) rfl)
  · exact sub_wlk _ (List.mem_of_getElem? (i := 2) rfl)
  · exact sub_wlk _ (List.mem_of_getElem? (i := 3) rfl)
  · exact sub_wlk _ (List.mem_of_getElem? (i := 4) rfl)
  · exact sub_wlk _ (List.mem_of_getElem? (i := 5) rfl)
  · exact sub_wlk _ (List.mem_of_getElem? (i := 6) rfl)
  · exact sub_wlk _ (List.mem_of_getElem? (i := 7) rfl)
  · exact sub_wlk _ (List.mem_of_getElem? (i := 8) rfl)
  · exact sub_wlk _ (List.mem_of_getElem? (i := 9) rfl)
  · exact sub_wlk _ (List.mem_of_getElem? (i := 11) rfl)
  · exact sub_ab _ h1
  · exact sub_v1 _ (by
      change e ∈ (FullM6VivBackbone.m6VivBackboneSpecTable.drop 3).take 25 at h2
      have ht25 : (FullM6VivBackbone.m6VivBackboneSpecTable.drop 3).take 25 =
          ((FullM6VivBackbone.m6VivBackboneSpecTable.drop 3).take 26).take 25 := by
        rw [List.take_take]; rfl
      rw [ht25] at h2; exact List.mem_of_mem_take h2)

private theorem sp_m7FidEnv_to_table {f : Sym} {as bs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post bs} {X : XPost}
    (h : m7FidelityEnv f as bs xs m Q X) :
    Env.ofTable m7FidSpecTable f as bs xs m Q X := by
  have hnbBase : ∀ {nm : Sym} {as bs : List Ty} {xs : Tup Val as} {m : Mem 64} {Q : Post bs}
      {X : XPost}, nm ∉ mfExclNames → Env.ofTable m7FidBaseTable nm as bs xs m Q X →
      Env.ofTable m7FidSpecTable nm as bs xs m Q X := by
    intro nm as bs xs m Q X hne hb
    have hnr : nm ∉ m7FidReplRows.map SpecEntry.name := by
      have hsub : ∀ s ∈ m7FidReplRows.map SpecEntry.name, s ∈ mfExclNames := by decide
      exact fun hm => hne (hsub nm hm)
    have hnb : nm ∉ (m7FidBeforeRows.flatMap Prod.snd).map SpecEntry.name := by
      have hsub : ∀ s ∈ (m7FidBeforeRows.flatMap Prod.snd).map SpecEntry.name,
          s ∈ mfExclNames := by
        decide
      exact fun hm => hne (hsub nm hm)
    exact sp_ofTable_patchRows_of_not_mem hnr hnb hb
  cases h with
  | base hne hb => exact hnbBase hne hb
  | extra he =>
    have hmfe : mfExtraRows = mfExtraBaseRows ++
        [ ⟨"full_vivify_tier_m6_hdr", [i64, i64, i64, i64], [i64], m6aVivifyTierSpec, true⟩
        , ⟨"full_compact_needed", [i64], [.bool], FullM4Compact.fullCompactNeededSpec, true⟩
        , ⟨"full_walk_m7", [i64], [], Full.fullWalkSpec, true⟩
        , ⟨"full_bump_analyzed_m6_hdr", [i64], [], m6aBumpAnalyzedSpec, true⟩
        , ⟨"full_walk_warmup_m7", [i64], [], Full.fullWarmupSpec, true⟩
        , ⟨"full_walk", [i64], [], Full.fullWarmupSpec, true⟩
        , ⟨"full_bva_match_large_fid", [i64, i32, i32, i32], [.bool],
            FullM7FidelityCore.fidBvaMatchLargeSpec, true⟩
        , ⟨"full_reorder_sift_fid", [i64, i64, i64], [],
            FullM7FidelityCore.fidReorderSiftSpec, true⟩
        , ⟨"m6_hdr_decide_fid", [i64], [i64], FullM6Hdr.m6HdrDecideSpec, true⟩ ] := rfl
    rw [hmfe] at he
    rcases env_ofTable_append_elim he with hbasex | htop9
    · obtain ⟨e, he_m, rfl, has, hrs, hcast⟩ := env_ofTable_mem_elim hbasex
      have hmem_b : e ∈ m7FidBaseTable := sp_mfExtraBase_sub_m7FidBaseTable e he_m
      have hnot_ex : e.name ∉ mfExclNames := by
        have hdisj : (mfExtraBaseRows.map SpecEntry.name).all
            (fun s => !mfExclNames.contains s) = true := by t_kernel_rfl
        have hc := List.all_eq_true.mp hdisj e.name (List.mem_map_of_mem he_m)
        simp only [Bool.not_eq_true'] at hc; simpa using hc
      exact hnbBase hnot_ex (ofTable_of_cast hmem_b m7FidBaseTable_nodup rfl has hrs hcast)
    · obtain ⟨e, he_m, rfl, has, hrs, hcast⟩ := env_ofTable_mem_elim htop9
      have he_tbl : e ∈ m7FidSpecTable := by
        have hBef : e ∈ (m7FidBeforeRows.flatMap Prod.snd) →
            e ∈ PatchModule.patchRows m7FidReplRows m7FidBeforeRows m7FidBaseTable := by
          intro hbm
          simp only [m7FidBeforeRows, List.flatMap_cons, List.flatMap_nil, List.append_nil,
            List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hbm
          have hBaseMem : ∀ tgt ∈ ["full_bva_filter_row", "full_reorder_queue_m7",
              "full_search_m6"], ∃ e0 ∈ m7FidBaseTable, e0.name = tgt := fun tgt ht => by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
            rcases ht with rfl | rfl | rfl
            · exact ⟨_, m7FidBase_bvaFilterRow_mem, rfl⟩
            · exact ⟨_, (m7FidPart3PfxCallees_of_sub m7FidBase_part3Pfx_mem).reorderQueueM7, rfl⟩
            · exact ⟨_, m7FidBase_searchM6_mem, rfl⟩
          rcases hbm with rfl | rfl | rfl
          · obtain ⟨e0, he0, hnm0⟩ := hBaseMem "full_bva_filter_row" (by decide)
            exact List.mem_flatMap.mpr ⟨e0, he0, List.mem_append_left _
              (by unfold PatchModule.patchRowInsAt m7FidBeforeRows; simp [hnm0])⟩
          · obtain ⟨e0, he0, hnm0⟩ := hBaseMem "full_reorder_queue_m7" (by decide)
            exact List.mem_flatMap.mpr ⟨e0, he0, List.mem_append_left _
              (by unfold PatchModule.patchRowInsAt m7FidBeforeRows; simp [hnm0])⟩
          · obtain ⟨e0, he0, hnm0⟩ := hBaseMem "full_search_m6" (by decide)
            exact List.mem_flatMap.mpr ⟨e0, he0, List.mem_append_left _
              (by unfold PatchModule.patchRowInsAt m7FidBeforeRows; simp [hnm0])⟩
        have hRep : ∀ tgt r, tgt ∈ m7FidBaseTable → tgt.name = r.name → r ∈ m7FidReplRows →
            r ∈ PatchModule.patchRows m7FidReplRows m7FidBeforeRows m7FidBaseTable := by
          intro tgt r htgt hnm hr
          refine List.mem_flatMap.mpr ⟨tgt, htgt, List.mem_append_right _ ?_⟩
          have hsome : m7FidReplRows.find? (·.name == tgt.name) = some r := by
            cases hf : m7FidReplRows.find? (·.name == tgt.name) with
            | none =>
              exfalso
              have ht := List.find?_eq_none.mp hf r hr
              simp [hnm] at ht
            | some r' =>
              have hnd : (m7FidReplRows.map SpecEntry.name).Nodup := by decide
              have hr'_m := List.mem_of_find?_eq_some hf
              have hnm' := beq_iff_eq.mp (List.find?_some (p := fun y : SpecEntry =>
                y.name == tgt.name) hf)
              have heq := m8cp_nodup_name_eq SpecEntry.name hnd hr'_m hr (hnm'.trans hnm)
              rw [heq]
          simp [hsome]
        have hc3p := m7FidPart3PfxCallees_of_sub m7FidBase_part3Pfx_mem
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he_m
        rcases he_m with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact hRep _ _ (m7FidBase_part2_mem _ (by
            unfold m7RowsPart2; (iterate 41 apply List.mem_append_right)
            exact List.mem_append_left _ (List.mem_of_getElem? (i := 0) rfl)))
            rfl (List.mem_of_getElem? (i := 0) rfl)
        · exact hRep _ _ hc3p.compactNeeded rfl (List.mem_of_getElem? (i := 1) rfl)
        · exact hRep _ _ (m7FidBase_part2_mem _ (by
            unfold m7RowsPart2; (iterate 22 apply List.mem_append_right)
            exact List.mem_append_left _ (List.mem_of_getElem? (i := 10) rfl)))
            rfl (List.mem_of_getElem? (i := 2) rfl)
        · exact hRep _ _ (m7FidBase_part2_mem _ (by
            unfold m7RowsPart2; (iterate 5 apply List.mem_append_right)
            exact List.mem_append_left _ (List.mem_of_getElem? (i := 0) rfl)))
            rfl (List.mem_of_getElem? (i := 3) rfl)
        · exact hRep _ _ (m7FidBase_part2_mem _ (by
            unfold m7RowsPart2; (iterate 22 apply List.mem_append_right)
            exact List.mem_append_left _ (List.mem_of_getElem? (i := 12) rfl)))
            rfl (List.mem_of_getElem? (i := 4) rfl)
        · exact hRep _ _ (m7FidBase_part2_mem _ (by
            unfold m7RowsPart2; (iterate 23 apply List.mem_append_right)
            exact List.mem_append_left _ (List.mem_of_getElem? (i := 1) rfl)))
            rfl (List.mem_of_getElem? (i := 5) rfl)
        · exact hBef (List.mem_flatMap.mpr ⟨_, List.mem_cons_self, List.mem_singleton.mpr rfl⟩)
        · exact hBef (List.mem_flatMap.mpr
            ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, List.mem_singleton.mpr rfl⟩)
        · exact hBef (List.mem_flatMap.mpr
            ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
              List.mem_singleton.mpr rfl⟩)
      exact ofTable_of_cast he_tbl m7FidSpecTable_nodup rfl has hrs hcast

private theorem sp_m7Tbl_to_swV12 {f : Sym} {as bs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post bs} {X : XPost}
    (h1 : f ≠ "full_extend_push2") (h2 : f ≠ "full_cong_enq_var")
    (h3 : f ≠ "full_cong_eval_gate") (h4 : f ≠ "full_cong_worklist")
    (h : Env.ofTable m7FidSpecTable f as bs xs m Q X) :
    Env.ofTable m8SwV12SpecTable f as bs xs m Q X := by
  obtain ⟨e, he, rfl, has, hrs, hcast⟩ := env_ofTable_mem_elim h
  have hrow : (if e.name == "full_extend_push2" then
      ⟨"full_extend_push2", [i64, i32, i32], [.bool], m6ExtendPush2Spec, true⟩
      else if e.name == "full_cong_enq_var" then
      ⟨"full_cong_enq_var", [i64, i64, i32], [], m8CongEnqVarSpec, true⟩
      else if e.name == "full_cong_eval_gate" then
      ⟨"full_cong_eval_gate", [i64, i64, i64, i64, i32, i64], [i64], m8CongEvalGateSpec, true⟩
      else if e.name == "full_cong_worklist" then
      ⟨"full_cong_worklist", [i64, i64, i64, i64], [i64], m8CongWorklistSpec, true⟩
      else e) = e := by
    simp [m8cp_sym_ne_beq h1, m8cp_sym_ne_beq h2, m8cp_sym_ne_beq h3, m8cp_sym_ne_beq h4]
  have hmem : e ∈ m8SwV12SpecTable := by
    unfold m8SwV12SpecTable; exact List.mem_map.mpr ⟨e, he, hrow⟩
  have hnd : (m8SwV12SpecTable.map SpecEntry.name).Nodup := by
    have hs := congrArg (List.map Prod.fst) m8cp_sw_v12Table_sigs
    simp only [List.map_map, Function.comp_def, Fn.sig] at hs
    change m8SwV12SpecTable.map SpecEntry.name = m8FidV12Fns.map Fn.name at hs
    rw [hs]; exact m8FidV12Fns_names_nodup
  exact ofTable_of_cast hmem hnd rfl has hrs hcast

private theorem sp_m8SwBase_to_coreParityTbl {f : Sym} {as bs : List Ty} {xs : Tup Val as}
    {m : Mem 64} {Q : Post bs} {X : XPost}
    (hne : f ∉ m8CpExclNames) (h : Env.ofTable m8SwBaseSpecTable f as bs xs m Q X) :
    Env.ofTable m8SweepV2CoreParitySpecTable f as bs xs m Q X := by
  by_cases h5 : f ∈ ["full_bve_var_m7", "full_bve_var", "full_probe_dticks_m6_hdr",
      "full_probe_m6", "full_search_m6"]
  · obtain ⟨e, he, rfl, has, hrs, hcast⟩ := env_ofTable_mem_elim h
    have hndBase : (m8SwBaseSpecTable.map SpecEntry.name).Nodup := by
      have hs := congrArg (List.map Prod.fst) m8cp_swBase_sigs
      simp only [List.map_map, Function.comp_def, Fn.sig] at hs
      change m8SwBaseSpecTable.map SpecEntry.name = m8FidV123t2Fns.map Fn.name at hs
      rw [hs]; exact m8FidV123t2Fns_names_nodup
    have hRepl : ∀ {nm : Sym} {as0 bs0 : List Ty} {sp0 : Spec as0 bs0}
        (_hmem0 : (⟨nm, as0, bs0, sp0, true⟩ : SpecEntry) ∈ m8SwBaseSpecTable)
        (_hmemR : (⟨nm, as0, bs0, sp0, true⟩ : SpecEntry) ∈
          m8CoreParityReplRows m8BveHook ++ m8cpRewireRows m8BveHook),
        e.name = nm →
        Env.ofTable m8SweepV2CoreParitySpecTable e.name as bs xs m Q X := by
      intro nm as0 bs0 sp0 hmem0 hmemR hnm
      have heq := m8cp_nodup_name_eq SpecEntry.name hndBase he hmem0 hnm
      subst heq
      have hfind : (m8CoreParityReplRows m8BveHook ++ m8cpRewireRows m8BveHook).find?
          (·.name == nm) = some ⟨nm, as0, bs0, sp0, true⟩ := by
        cases hf : (m8CoreParityReplRows m8BveHook ++ m8cpRewireRows m8BveHook).find?
            (·.name == nm) with
        | none =>
          exfalso
          have ht := List.find?_eq_none.mp hf _ hmemR
          simp at ht
        | some r' =>
          have hndR : ((m8CoreParityReplRows m8BveHook ++
              m8cpRewireRows m8BveHook).map SpecEntry.name).Nodup := by
            decide
          have hr'_m := List.mem_of_find?_eq_some hf
          have hnm' := beq_iff_eq.mp (List.find?_some (p := fun y : SpecEntry => y.name == nm) hf)
          have heq' := m8cp_nodup_name_eq SpecEntry.name hndR hr'_m hmemR hnm'
          rw [heq']
      have hmemT : (⟨nm, as0, bs0, sp0, true⟩ : SpecEntry) ∈ m8SweepV2CoreParitySpecTable :=
        List.mem_flatMap.mpr ⟨_, hmem0, List.mem_append_right _ (by simp [hfind])⟩
      exact ofTable_of_cast hmemT m8SweepV2CoreParitySpecTable_nodup rfl has hrs hcast
    have hsw : ∀ tgt, tgt ∈ m7FidBaseTable → tgt.name ∉ ["full_extend_push2", "full_cong_enq_var",
        "full_cong_eval_gate", "full_cong_worklist"] →
        tgt.name ∉ mfExclNames → tgt ∈ m8SwBaseSpecTable := by
      intro tgt htgt hn4 hnEx
      have ht1 : tgt ∈ m7FidSpecTable := by
        have hnr : tgt.name ∉ m7FidReplRows.map SpecEntry.name := by
          have hs : ∀ s ∈ m7FidReplRows.map SpecEntry.name, s ∈ mfExclNames := by decide
          exact fun hm => hnEx (hs _ hm)
        refine List.mem_flatMap.mpr ⟨tgt, htgt, List.mem_append_right _ ?_⟩
        rw [List.find?_eq_none.mpr (fun r hr hbeq =>
          hnr (List.mem_map.mpr ⟨r, hr, beq_iff_eq.mp hbeq⟩))]
        exact List.mem_singleton.mpr rfl
      have ht2 : tgt ∈ m8SwV12SpecTable := by
        unfold m8SwV12SpecTable
        refine List.mem_map.mpr ⟨tgt, ht1, ?_⟩
        have hn4' : tgt.name ≠ "full_extend_push2" ∧ tgt.name ≠ "full_cong_enq_var" ∧
            tgt.name ≠ "full_cong_eval_gate" ∧ tgt.name ≠ "full_cong_worklist" :=
          ⟨fun h => hn4 (by rw [h]; decide), fun h => hn4 (by rw [h]; decide),
            fun h => hn4 (by rw [h]; decide), fun h => hn4 (by rw [h]; decide)⟩
        simp [m8cp_sym_ne_beq hn4'.1, m8cp_sym_ne_beq hn4'.2.1,
          m8cp_sym_ne_beq hn4'.2.2.1, m8cp_sym_ne_beq hn4'.2.2.2]
      refine List.mem_flatMap.mpr ⟨tgt, ht2, List.mem_append_right _ (List.mem_singleton.mpr rfl)⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h5
    rcases h5 with h5a | h5b | h5c | h5d | h5e
    · exact hRepl (hsw _ m7FidBase_bveVar_mem (by decide) (by decide))
        (List.mem_append_left _ (by simp [m8CoreParityReplRows])) h5a
    · exact hRepl (hsw _ (m7FidBase_bve_mem _ (List.mem_of_getElem? (i := 33) rfl))
        (by decide) (by decide)) (List.mem_append_left _ (by simp [m8CoreParityReplRows])) h5b
    · exact hRepl (hsw _ (m7FidPart3PfxCallees_of_sub m7FidBase_part3Pfx_mem).probeDticks
        (by decide) (by decide)) (List.mem_append_left _ (by simp [m8CoreParityReplRows])) h5c
    · exact hRepl (hsw _ m7FidBase_probeM6_mem (by decide) (by decide))
        (List.mem_append_left _ (by simp [m8CoreParityReplRows])) h5d
    · exact hRepl (hsw _ m7FidBase_searchM6_mem (by decide) (by decide))
        (List.mem_append_left _ (by simp [m8CoreParityReplRows])) h5e
  · refine sp_ofTable_patchRows_of_not_mem (fun hm => ?_) (fun hb => ?_) h
    · simp only [m8CoreParityReplRows, m8cpRewireRows, List.map_cons,
        List.map_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
        or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hne (by decide)
      · exact h5 (by decide)
      · exact h5 (by decide)
      · exact hne (by decide)
      · exact h5 (by decide)
      · exact h5 (by decide)
      · exact h5 (by decide)
      · exact hne (by decide)
      · exact hne (by decide)
    · obtain ⟨e, he, hfe, _, _, _⟩ := env_ofTable_mem_elim h
      have hdisj : ∀ b ∈ (m8CoreParityBeforeRows m8BveHook).flatMap Prod.snd,
          b.name ∉ m8SwBaseSpecTable.map SpecEntry.name := by
        have hs := congrArg (List.map Prod.fst) m8cp_swBase_sigs
        simp only [List.map_map, Function.comp_def, Fn.sig] at hs
        change m8SwBaseSpecTable.map SpecEntry.name = m8FidV123t2Fns.map Fn.name at hs
        rw [hs]
        intro b hb
        simp only [m8CoreParityBeforeRows, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.mem_append] at hb
        rcases hb with h1 | h2
        · exact m8cp_min_help_not_in_sw b h1
        · exact m8cp_bve_help_not_in_sw m8BveHook b h2
      rcases List.mem_map.mp hb with ⟨b, hb_m, hb_eq⟩
      exact hdisj b hb_m (by rw [hb_eq, ← hfe]; exact List.mem_map_of_mem he)

theorem sp_m8SwParityEnv_to_table_of_not_bad {f : Sym} {as bs : List Ty}
    {xs : Tup Val as} {m : Mem 64} {Q : Post bs} {X : XPost}
    (hnb : f ∉ ["full_cong_enq_var", "full_cong_eval_gate", "full_cong_worklist"])
    (h : m8SweepV2CoreParityEnv f as bs xs m Q X) :
    Env.ofTable m8SweepV2CoreParitySpecTable f as bs xs m Q X := by
  have hnb4 : f ≠ "full_cong_enq_var" ∧ f ≠ "full_cong_eval_gate" ∧ f ≠ "full_cong_worklist" :=
    ⟨fun he => hnb (by subst he; decide), fun he => hnb (by subst he; decide),
      fun he => hnb (by subst he; decide)⟩
  have hndSw := m8SweepV2CoreParitySpecTable_nodup
  have hHelpMem : ∀ {e : SpecEntry}, e ∈ (m8CoreParityBeforeRows m8BveHook).flatMap Prod.snd →
      e ∈ m8SweepV2CoreParitySpecTable := by
    intro e he
    have hex : ∃ p ∈ m8CoreParityBeforeRows m8BveHook,
        ∃ e0 ∈ m8SwBaseSpecTable, e0.name = p.1 ∧ e ∈ p.2 := by
      simp only [m8CoreParityBeforeRows, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.mem_append] at he
      have hm1 : ∃ e0 ∈ m8SwBaseSpecTable, e0.name = "full_min_shrink_m6" := by
        have h1 : (⟨"full_min_shrink_m6", [i64], [], FullM7SpecBridges.m7MinShrinkSpec,
            true⟩ : SpecEntry) ∈ m7FidBaseTable :=
          (m7Part2PfxCallees_of_sub m7FidBase_part2_mem).minShrinkM6
        have h2 : (⟨"full_min_shrink_m6", [i64], [], FullM7SpecBridges.m7MinShrinkSpec,
            true⟩ : SpecEntry) ∈ m7FidSpecTable := by
          refine List.mem_flatMap.mpr ⟨_, h1, List.mem_append_right _ ?_⟩
          have hf : m7FidReplRows.find? (·.name == "full_min_shrink_m6") = none := by t_kernel_rfl
          simp [hf]
        have h3 : (⟨"full_min_shrink_m6", [i64], [], FullM7SpecBridges.m7MinShrinkSpec,
            true⟩ : SpecEntry) ∈ m8SwV12SpecTable := by
          unfold m8SwV12SpecTable; exact List.mem_map.mpr ⟨_, h2, rfl⟩
        exact ⟨_, List.mem_flatMap.mpr
            ⟨_, h3, List.mem_append_right _ (List.mem_singleton.mpr rfl)⟩, rfl⟩
      have hm2 : ∃ e0 ∈ m8SwBaseSpecTable, e0.name = "full_bve_var_m7" := by
        have h1 : (⟨"full_bve_var_m7", [i64, i32], [i64], FullFastBveBudgets.fullBveVarDefSpec,
            true⟩ : SpecEntry) ∈ m7FidBaseTable := m7FidBase_bveVar_mem
        have h2 : (⟨"full_bve_var_m7", [i64, i32], [i64], FullFastBveBudgets.fullBveVarDefSpec,
            true⟩ : SpecEntry) ∈ m7FidSpecTable := by
          refine List.mem_flatMap.mpr ⟨_, h1, List.mem_append_right _ ?_⟩
          have hf : m7FidReplRows.find? (·.name == "full_bve_var_m7") = none := by t_kernel_rfl
          simp [hf]
        have h3 : (⟨"full_bve_var_m7", [i64, i32], [i64], FullFastBveBudgets.fullBveVarDefSpec,
            true⟩ : SpecEntry) ∈ m8SwV12SpecTable := by
          unfold m8SwV12SpecTable; exact List.mem_map.mpr ⟨_, h2, rfl⟩
        exact ⟨_, List.mem_flatMap.mpr
            ⟨_, h3, List.mem_append_right _ (List.mem_singleton.mpr rfl)⟩, rfl⟩
      rcases he with h1 | h2
      · obtain ⟨e0, he0, hn0⟩ := hm1; exact ⟨_, List.mem_cons_self, e0, he0, hn0, h1⟩
      · obtain ⟨e0, he0, hn0⟩ := hm2
        exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, e0, he0, hn0, h2⟩
    obtain ⟨p, hp, e0, he0, hn0, hep⟩ := hex
    refine List.mem_flatMap.mpr ⟨e0, he0, List.mem_append_left _ ?_⟩
    unfold PatchModule.patchRowInsAt
    simp only [m8CoreParityBeforeRows, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> simp [m8CoreParityBeforeRows, hn0] <;> exact hep
  cases h with
  | base hne hsw =>
    refine sp_m8SwBase_to_coreParityTbl hne ?_
    cases hsw with
    | base hne1 hv12 =>
      have hv12_tbl : Env.ofTable m8SwV12SpecTable f as bs xs m Q X := by
        cases hv12 with
        | base hm7 =>
          exact sp_m7Tbl_to_swV12 (fun he => hne1 (by subst he; decide))
            hnb4.1 hnb4.2.1 hnb4.2.2 (sp_m7FidEnv_to_table hm7)
        | enqVar => exact absurd rfl hnb4.1
        | evalGate => exact absurd rfl hnb4.2.1
        | worklist => exact absurd rfl hnb4.2.2
      exact sp_ofTable_patchRows_of_not_mem (fun h => nomatch h) (fun hb => by
        obtain ⟨e, he, hfe, _, _, _⟩ := env_ofTable_mem_elim hv12_tbl
        have hdisj : (m8SweepEnvRows.map SpecEntry.name).all
            (fun s => !((m7FidelityFns.map Fn.name).contains s)) = true := by t_kernel_rfl
        have hn : m8SwV12SpecTable.map SpecEntry.name = m7FidelityFns.map Fn.name := by
          have hnm : m8SwV12SpecTable.map SpecEntry.name = m7FidSpecTable.map SpecEntry.name := by
            unfold m8SwV12SpecTable
            rw [List.map_map]
            apply List.map_congr_left
            intro row _
            dsimp only [Function.comp_def]
            split
            · rename_i hs1; exact (beq_iff_eq.mp hs1).symm
            · split
              · rename_i hs2; exact (beq_iff_eq.mp hs2).symm
              · split
                · rename_i hs3; exact (beq_iff_eq.mp hs3).symm
                · split
                  · rename_i hs4; exact (beq_iff_eq.mp hs4).symm
                  · rfl
          have hs := congrArg (List.map Prod.fst) m7FidSpecTable_sigs
          simp only [List.map_map, Function.comp_def, Fn.sig] at hs
          exact hnm.trans hs
        rcases List.mem_map.mp hb with ⟨b, hb_m, hb_eq⟩
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hb_m
        have hc := List.all_eq_true.mp hdisj b.name (List.mem_map_of_mem hb_m)
        simp only [Bool.not_eq_true'] at hc
        have hbm : b.name ∈ m7FidelityFns.map Fn.name := by
          rw [hb_eq, ← hfe, ← hn]; exact List.mem_map_of_mem he
        rw [List.contains_iff_mem.mpr hbm] at hc
        exact Bool.noConfusion hc) hv12_tbl
    | extPush2 hs =>
      have h1 : (⟨"full_extend_push2", [i64, i32, i32], [.bool],
          FullFastBveBudgets.fullExtendPush2TmkSpec, true⟩ : SpecEntry) ∈ m7FidBaseTable :=
        (m7Part2Callees_of_sub m7FidBase_part2_mem).extendPush2
      have h2 : (⟨"full_extend_push2", [i64, i32, i32], [.bool],
          FullFastBveBudgets.fullExtendPush2TmkSpec, true⟩ : SpecEntry) ∈ m7FidSpecTable := by
        refine List.mem_flatMap.mpr ⟨_, h1, List.mem_append_right _ ?_⟩
        have hf : m7FidReplRows.find? (·.name == "full_extend_push2") = none := by t_kernel_rfl
        simp [hf]
      have h3 : (⟨"full_extend_push2", [i64, i32, i32], [.bool], m6ExtendPush2Spec,
          true⟩ : SpecEntry) ∈ m8SwV12SpecTable := by
        unfold m8SwV12SpecTable; exact List.mem_map.mpr ⟨_, h2, rfl⟩
      have h4 : (⟨"full_extend_push2", [i64, i32, i32], [.bool], m6ExtendPush2Spec,
          true⟩ : SpecEntry) ∈ m8SwBaseSpecTable :=
        List.mem_flatMap.mpr ⟨_, h3, List.mem_append_right _ (List.mem_singleton.mpr rfl)⟩
      have hndB : (m8SwBaseSpecTable.map SpecEntry.name).Nodup := by
        have hs0 := congrArg (List.map Prod.fst) m8cp_swBase_sigs
        simp only [List.map_map, Function.comp_def, Fn.sig] at hs0
        change m8SwBaseSpecTable.map SpecEntry.name = m8FidV123t2Fns.map Fn.name at hs0
        rw [hs0]; exact m8FidV123t2Fns_names_nodup
      exact ofTable_of_cast h4 hndB rfl rfl rfl hs
    | sweep hs =>
      obtain ⟨e, he, rfl, has, hrs, hcast⟩ := env_ofTable_mem_elim hs
      have h3 : (⟨"full_sweep_dense_m6", [i64, i64, i64], [i64], FullDefSweep.fullSweepDenseSpec,
          true⟩ : SpecEntry) ∈ m8SwV12SpecTable := by
        have h1 : (⟨"full_sweep_dense_m6", [i64, i64, i64], [i64], FullDefSweep.fullSweepDenseSpec,
            true⟩ : SpecEntry) ∈ m7FidBaseTable :=
          m7FidBase_sweepDenseM6_mem
        have h2 : (⟨"full_sweep_dense_m6", [i64, i64, i64], [i64], FullDefSweep.fullSweepDenseSpec,
            true⟩ : SpecEntry) ∈ m7FidSpecTable := by
          refine List.mem_flatMap.mpr ⟨_, h1, List.mem_append_right _ ?_⟩
          have hf : m7FidReplRows.find? (·.name == "full_sweep_dense_m6") = none := by
            t_kernel_rfl
          simp [hf]
        unfold m8SwV12SpecTable; exact List.mem_map.mpr ⟨_, h2, rfl⟩
      have hmemB : e ∈ m8SwBaseSpecTable :=
        List.mem_flatMap.mpr ⟨_, h3, List.mem_append_left _
          (by unfold PatchModule.patchRowInsAt; simp [he])⟩
      have hndB : (m8SwBaseSpecTable.map SpecEntry.name).Nodup := by
        have hs0 := congrArg (List.map Prod.fst) m8cp_swBase_sigs
        simp only [List.map_map, Function.comp_def, Fn.sig] at hs0
        change m8SwBaseSpecTable.map SpecEntry.name = m8FidV123t2Fns.map Fn.name at hs0
        rw [hs0]; exact m8FidV123t2Fns_names_nodup
      exact ofTable_of_cast hmemB hndB rfl has hrs hcast
  | minShrinkM6 hs =>
    have h1 : (⟨"full_min_shrink_m6", [i64], [], FullM7SpecBridges.m7MinShrinkSpec, true⟩ :
        SpecEntry) ∈ m7FidBaseTable := (m7Part2PfxCallees_of_sub m7FidBase_part2_mem).minShrinkM6
    have h2 : (⟨"full_min_shrink_m6", [i64], [], FullM7SpecBridges.m7MinShrinkSpec, true⟩ :
        SpecEntry) ∈ m7FidSpecTable := by
      refine List.mem_flatMap.mpr ⟨_, h1, List.mem_append_right _ ?_⟩
      have hf : m7FidReplRows.find? (·.name == "full_min_shrink_m6") = none := by t_kernel_rfl
      simp [hf]
    have h3 : (⟨"full_min_shrink_m6", [i64], [], FullM7SpecBridges.m7MinShrinkSpec, true⟩ :
        SpecEntry) ∈ m8SwV12SpecTable := by
      unfold m8SwV12SpecTable; exact List.mem_map.mpr ⟨_, h2, rfl⟩
    have h4 : (⟨"full_min_shrink_m6", [i64], [], FullM7SpecBridges.m7MinShrinkSpec, true⟩ :
        SpecEntry) ∈ m8SwBaseSpecTable :=
      List.mem_flatMap.mpr ⟨_, h3, List.mem_append_right _ (List.mem_singleton.mpr rfl)⟩
    have hmem : (⟨"full_min_shrink_m6", [i64], [], m8MinShrinkSpec, true⟩ : SpecEntry) ∈
        m8SweepV2CoreParitySpecTable := by
      refine List.mem_flatMap.mpr ⟨_, h4, List.mem_append_right _ ?_⟩
      have hf : (m8CoreParityReplRows m8BveHook ++ m8cpRewireRows m8BveHook).find?
          (·.name == "full_min_shrink_m6") =
          some ⟨"full_min_shrink_m6", [i64], [], m8MinShrinkSpec, true⟩ := by
        t_kernel_rfl
      simp [hf]
    exact ofTable_of_cast hmem hndSw rfl rfl rfl (m8MinShrinkSpec_monoX hs)
  | minShrink hs =>
    have h1 : (⟨"full_min_shrink", [i64], [], FullM7SpecBridges.m7MinShrinkSpec, true⟩ :
        SpecEntry) ∈ m7FidBaseTable :=
      m7FidBase_pfx_mem _ m7FidOrchPfxRows_specs.minShrink
    have h2 : (⟨"full_min_shrink", [i64], [], FullM7SpecBridges.m7MinShrinkSpec, true⟩ :
        SpecEntry) ∈ m7FidSpecTable := by
      refine List.mem_flatMap.mpr ⟨_, h1, List.mem_append_right _ ?_⟩
      have hf : m7FidReplRows.find? (·.name == "full_min_shrink") = none := by t_kernel_rfl
      simp [hf]
    have h3 : (⟨"full_min_shrink", [i64], [], FullM7SpecBridges.m7MinShrinkSpec, true⟩ :
        SpecEntry) ∈ m8SwV12SpecTable := by
      unfold m8SwV12SpecTable; exact List.mem_map.mpr ⟨_, h2, rfl⟩
    have h4 : (⟨"full_min_shrink", [i64], [], FullM7SpecBridges.m7MinShrinkSpec, true⟩ :
        SpecEntry) ∈ m8SwBaseSpecTable :=
      List.mem_flatMap.mpr ⟨_, h3, List.mem_append_right _ (List.mem_singleton.mpr rfl)⟩
    have hmem : (⟨"full_min_shrink", [i64], [], m8MinShrinkSpec, true⟩ : SpecEntry) ∈
        m8SweepV2CoreParitySpecTable := by
      refine List.mem_flatMap.mpr ⟨_, h4, List.mem_append_right _ ?_⟩
      have hf : (m8CoreParityReplRows m8BveHook ++ m8cpRewireRows m8BveHook).find?
          (·.name == "full_min_shrink") =
          some ⟨"full_min_shrink", [i64], [], m8MinShrinkSpec, true⟩ := by
        t_kernel_rfl
      simp [hf]
    exact ofTable_of_cast hmem hndSw rfl rfl rfl (m8MinShrinkSpec_monoX hs)
  | varKey hs =>
    have h1 : (⟨"full_bve_var_key_m7", [i64, i32], [i64],
        FullM6BveFwd.fullBveVarKeyM6Spec, true⟩ : SpecEntry) ∈ m7FidBaseTable :=
      m7FidBase_bve_mem _ (List.mem_of_getElem? (i := 34) rfl)
    have h2 : (⟨"full_bve_var_key_m7", [i64, i32], [i64],
        FullM6BveFwd.fullBveVarKeyM6Spec, true⟩ : SpecEntry) ∈ m7FidSpecTable := by
      refine List.mem_flatMap.mpr ⟨_, h1, List.mem_append_right _ ?_⟩
      have hf : m7FidReplRows.find? (·.name == "full_bve_var_key_m7") = none := by t_kernel_rfl
      simp [hf]
    have h3 : (⟨"full_bve_var_key_m7", [i64, i32], [i64],
        FullM6BveFwd.fullBveVarKeyM6Spec, true⟩ : SpecEntry) ∈ m8SwV12SpecTable := by
      unfold m8SwV12SpecTable; exact List.mem_map.mpr ⟨_, h2, rfl⟩
    have h4 : (⟨"full_bve_var_key_m7", [i64, i32], [i64],
        FullM6BveFwd.fullBveVarKeyM6Spec, true⟩ : SpecEntry) ∈ m8SwBaseSpecTable :=
      List.mem_flatMap.mpr ⟨_, h3, List.mem_append_right _ (List.mem_singleton.mpr rfl)⟩
    have hmem : (⟨"full_bve_var_key_m7", [i64, i32], [i64], m8BveHook.varKeySpec, true⟩ :
        SpecEntry) ∈ m8SweepV2CoreParitySpecTable := by
      refine List.mem_flatMap.mpr ⟨_, h4, List.mem_append_right _ ?_⟩
      have hf : (m8CoreParityReplRows m8BveHook ++ m8cpRewireRows m8BveHook).find?
          (·.name == "full_bve_var_key_m7") =
          some ⟨"full_bve_var_key_m7", [i64, i32], [i64], m8BveHook.varKeySpec, true⟩ := by
        t_kernel_rfl
      simp [hf]
    exact ofTable_of_cast hmem hndSw rfl rfl rfl (m8BveHook.varKey_noExit _ _ _ _ _ hs)
  | heapPush hs =>
    have h1 : (⟨"full_bve_heap_push_m7", [i64, i64, i32], [i64],
        FullM6BveFwd.fullBveHeapPushM6Spec, true⟩ : SpecEntry) ∈ m7FidBaseTable :=
      m7FidBase_bveHeapPush_mem
    have h2 : (⟨"full_bve_heap_push_m7", [i64, i64, i32], [i64],
        FullM6BveFwd.fullBveHeapPushM6Spec, true⟩ : SpecEntry) ∈ m7FidSpecTable := by
      refine List.mem_flatMap.mpr ⟨_, h1, List.mem_append_right _ ?_⟩
      have hf : m7FidReplRows.find? (·.name == "full_bve_heap_push_m7") = none := by t_kernel_rfl
      simp [hf]
    have h3 : (⟨"full_bve_heap_push_m7", [i64, i64, i32], [i64],
        FullM6BveFwd.fullBveHeapPushM6Spec, true⟩ : SpecEntry) ∈ m8SwV12SpecTable := by
      unfold m8SwV12SpecTable; exact List.mem_map.mpr ⟨_, h2, rfl⟩
    have h4 : (⟨"full_bve_heap_push_m7", [i64, i64, i32], [i64],
        FullM6BveFwd.fullBveHeapPushM6Spec, true⟩ : SpecEntry) ∈ m8SwBaseSpecTable :=
      List.mem_flatMap.mpr ⟨_, h3, List.mem_append_right _ (List.mem_singleton.mpr rfl)⟩
    have hmem : (⟨"full_bve_heap_push_m7", [i64, i64, i32], [i64], m8BveHook.heapPushSpec, true⟩ :
        SpecEntry) ∈ m8SweepV2CoreParitySpecTable := by
      refine List.mem_flatMap.mpr ⟨_, h4, List.mem_append_right _ ?_⟩
      have hf : (m8CoreParityReplRows m8BveHook ++ m8cpRewireRows m8BveHook).find?
          (·.name == "full_bve_heap_push_m7") =
          some ⟨"full_bve_heap_push_m7", [i64, i64, i32], [i64],
            m8BveHook.heapPushSpec, true⟩ := by
        t_kernel_rfl
      simp [hf]
    exact ofTable_of_cast hmem hndSw rfl rfl rfl (m8BveHook.heapPush_noExit _ _ _ _ _ hs)
  | minHelp hm =>
    obtain ⟨e, he, rfl, has, hrs, hcast⟩ := env_ofTable_mem_elim hm
    exact ofTable_of_cast (hHelpMem (by simp [m8CoreParityBeforeRows, he])) hndSw rfl has hrs hcast
  | bveHelp hm =>
    obtain ⟨e, he, rfl, has, hrs, hcast⟩ := env_ofTable_mem_elim hm
    exact ofTable_of_cast (hHelpMem (by simp [m8CoreParityBeforeRows, he])) hndSw rfl has hrs hcast

private theorem sp_cpReplRows_names :
    (m8CoreParityReplRows m8BveHook ++ m8cpRewireRows m8BveHook).map SpecEntry.name =
      [ "full_min_shrink_m6", "full_bve_var_m7", "full_bve_var", "full_bve_var_key_m7"
      , "full_probe_dticks_m6_hdr", "full_probe_m6", "full_search_m6"
      , "full_min_shrink", "full_bve_heap_push_m7" ] := by
  decide

theorem sp_u64Sort_noExit :
    ∀ xs m Q X, FullM7CongIte.m7U64SortSpec xs m Q X →
      FullM7CongIte.m7U64SortSpec xs m Q (fun _ _ _ _ => False) :=
  fun _ _ _ _ h => h

theorem sp_untouched_m7_mem_swTbl {e : SpecEntry} (he : e ∈ m7FidBaseTable)
    (h1 : e.name ∉ mfExclNames)
    (h2 : e.name ∉ ["full_extend_push2", "full_cong_enq_var",
      "full_cong_eval_gate", "full_cong_worklist"])
    (h3 : e.name ∉ ["full_min_shrink_m6", "full_bve_var_m7", "full_bve_var",
      "full_bve_var_key_m7", "full_probe_dticks_m6_hdr", "full_probe_m6",
      "full_search_m6", "full_min_shrink", "full_bve_heap_push_m7"]) :
    e ∈ m8SweepV2CoreParitySpecTable := by
  have hm1 : e ∈ m7FidSpecTable := by
    have hnr : e.name ∉ m7FidReplRows.map SpecEntry.name := by
      have hs : ∀ s ∈ m7FidReplRows.map SpecEntry.name, s ∈ mfExclNames := by decide
      exact fun hm => h1 (hs _ hm)
    refine List.mem_flatMap.mpr ⟨e, he, List.mem_append_right _ ?_⟩
    rw [List.find?_eq_none.mpr (fun r hr hbeq =>
      hnr (List.mem_map.mpr ⟨r, hr, beq_iff_eq.mp hbeq⟩))]
    exact List.mem_singleton.mpr rfl
  have hm2 : e ∈ m8SwV12SpecTable := by
    unfold m8SwV12SpecTable; refine List.mem_map.mpr ⟨e, hm1, ?_⟩
    have h2' : e.name ≠ "full_extend_push2" ∧ e.name ≠ "full_cong_enq_var" ∧
        e.name ≠ "full_cong_eval_gate" ∧ e.name ≠ "full_cong_worklist" :=
      ⟨fun h => h2 (by rw [h]; decide), fun h => h2 (by rw [h]; decide),
        fun h => h2 (by rw [h]; decide), fun h => h2 (by rw [h]; decide)⟩
    simp [m8cp_sym_ne_beq h2'.1, m8cp_sym_ne_beq h2'.2.1,
      m8cp_sym_ne_beq h2'.2.2.1, m8cp_sym_ne_beq h2'.2.2.2]
  have hm3 : e ∈ m8SwBaseSpecTable :=
    List.mem_flatMap.mpr ⟨e, hm2, List.mem_append_right _ (List.mem_singleton.mpr rfl)⟩
  have h3' : e.name ∉ (m8CoreParityReplRows m8BveHook ++ m8cpRewireRows m8BveHook).map
      SpecEntry.name := by
    rw [sp_cpReplRows_names]; exact h3
  refine List.mem_flatMap.mpr ⟨e, hm3, List.mem_append_right _ ?_⟩
  rw [List.find?_eq_none.mpr (fun r hr hbeq =>
    h3' (List.mem_map.mpr ⟨r, hr, beq_iff_eq.mp hbeq⟩))]
  exact List.mem_singleton.mpr rfl

theorem sp_m8SwV12_row_mem_swTbl {nm : Sym} {as bs : List Ty}
    {sp_old sp_new : Spec as bs}
    (he : (⟨nm, as, bs, sp_old, true⟩ : SpecEntry) ∈ m7FidBaseTable)
    (h1 : nm ∉ mfExclNames)
    (h3 : nm ∉ ["full_min_shrink_m6", "full_bve_var_m7", "full_bve_var",
      "full_bve_var_key_m7", "full_probe_dticks_m6_hdr", "full_probe_m6",
      "full_search_m6", "full_min_shrink", "full_bve_heap_push_m7"])
    (hm : ((if nm == "full_extend_push2" then
        (⟨"full_extend_push2", [i64, i32, i32], [.bool], m6ExtendPush2Spec, true⟩ : SpecEntry)
        else if nm == "full_cong_enq_var" then
        (⟨"full_cong_enq_var", [i64, i64, i32], [], m8CongEnqVarSpec, true⟩ : SpecEntry)
        else if nm == "full_cong_eval_gate" then
        (⟨"full_cong_eval_gate", [i64, i64, i64, i64, i32, i64], [i64], m8CongEvalGateSpec, true⟩ :
          SpecEntry)
        else if nm == "full_cong_worklist" then
        (⟨"full_cong_worklist", [i64, i64, i64, i64], [i64], m8CongWorklistSpec, true⟩ : SpecEntry)
        else (⟨nm, as, bs, sp_old, true⟩ : SpecEntry)) : SpecEntry) =
        ⟨nm, as, bs, sp_new, true⟩ := by rfl) :
    (⟨nm, as, bs, sp_new, true⟩ : SpecEntry) ∈ m8SweepV2CoreParitySpecTable := by
  have hm1 : (⟨nm, as, bs, sp_old, true⟩ : SpecEntry) ∈ m7FidSpecTable := by
    have hnr : nm ∉ m7FidReplRows.map SpecEntry.name := by
      have hs : ∀ s ∈ m7FidReplRows.map SpecEntry.name, s ∈ mfExclNames := by decide
      exact fun h => h1 (hs _ h)
    refine List.mem_flatMap.mpr ⟨_, he, List.mem_append_right _ ?_⟩
    rw [List.find?_eq_none.mpr (fun r hr hbeq =>
      hnr (List.mem_map.mpr ⟨r, hr, beq_iff_eq.mp hbeq⟩))]
    exact List.mem_singleton.mpr rfl
  have hm2 : (⟨nm, as, bs, sp_new, true⟩ : SpecEntry) ∈ m8SwV12SpecTable := by
    unfold m8SwV12SpecTable; exact List.mem_map.mpr ⟨_, hm1, hm⟩
  have hm3 : (⟨nm, as, bs, sp_new, true⟩ : SpecEntry) ∈ m8SwBaseSpecTable :=
    List.mem_flatMap.mpr ⟨_, hm2, List.mem_append_right _ (List.mem_singleton.mpr rfl)⟩
  have h3' : nm ∉ (m8CoreParityReplRows m8BveHook ++ m8cpRewireRows m8BveHook).map
      SpecEntry.name := by
    rw [sp_cpReplRows_names]; exact h3
  refine List.mem_flatMap.mpr ⟨_, hm3, List.mem_append_right _ ?_⟩
  rw [List.find?_eq_none.mpr (fun r hr hbeq =>
    h3' (List.mem_map.mpr ⟨r, hr, beq_iff_eq.mp hbeq⟩))]
  exact List.mem_singleton.mpr rfl

theorem sp_sw_base_at {e : SpecEntry} (hmem : e ∈ m8SweepV2CoreParitySpecTable)
    (hne : e.noExit = true := by rfl)
    {xs : Tup Val e.as} {m : Mem 64} {Q : Post e.rs} {X : XPost}
    (hs : e.spec xs m Q (fun _ _ _ _ => False)) :
    Env.ofTable m8SweepV2CoreParitySpecTable e.name e.as e.rs xs m Q X :=
  Env.ofTable_of_mem hmem m8SweepV2CoreParitySpecTable_nodup
    (by unfold SpecEntry.eff; rw [hne]; simp; exact hs)

theorem sp_sw_base_noExit {nm : Sym} {as bs : List Ty} {sp : Spec as bs}
    (hmem : (⟨nm, as, bs, sp, true⟩ : SpecEntry) ∈ m8SweepV2CoreParitySpecTable)
    (hno : ∀ xs m Q X, sp xs m Q X → sp xs m Q (fun _ _ _ _ => False) := by
      exact fun _ _ _ _ h => h) :
    ∀ a m Q X, sp a m Q X → Env.ofTable m8SweepV2CoreParitySpecTable nm as bs a m Q X :=
  fun a m Q X hs => sp_sw_base_at hmem rfl (hno a m Q X hs)

private theorem sp_m8Sw_batch4 :
    [m8SweepV2CoreParityFns[261]?, m8SweepV2CoreParityFns[262]?,
     m8SweepV2CoreParityFns[263]?, m8SweepV2CoreParityFns[278]?] =
    [some FullM6CongSubst.full_cong_eval_gate, some FullM6CongSubst.full_cong_work_step,
     some FullM6CongSubst.full_cong_worklist, some FullM8FidV12.m8CongruenceDenseFn] := by
  t_kernel_rfl

theorem sp_m8Sw_fn262 :
    m8SweepV2CoreParityFns[262]? = some FullM6CongSubst.full_cong_work_step := by
  have h := congrArg (·[1]?) sp_m8Sw_batch4; simpa using h

theorem m8SweepV2CoreParity_ofTable_moduleOk :
    ModuleOk (Env.ofTable m8SweepV2CoreParitySpecTable) m8SweepV2CoreParityModule := by
  have hM := m8SweepV2CoreParity_moduleOk
  have hc1 := m7FidPart1Callees_of_sub m7FidBase_part1_mem
  have hc2 := m7Part2Callees_of_sub m7FidBase_part2_mem
  have hc2p := m7Part2PfxCallees_of_sub m7FidBase_part2_mem
  have hc2c := m7Part2CongCallees_of_sub m7FidBase_part2_mem
  have hFind_b : (⟨"full_cong_find", [i64, i32], [i32], fullCongFindSpec, true⟩ : SpecEntry) ∈
      m7FidBaseTable :=
    m7FidBase_part2_mem _ (by
      unfold m7RowsPart2; (iterate 49 apply List.mem_append_right)
      exact List.mem_append_left _ (List.mem_of_getElem? (i := 0) rfl))
  have hSortU32_b : (⟨"full_sort_u32", [i64, i32], [], fullSortU32Spec, true⟩ : SpecEntry) ∈
      m7FidBaseTable :=
    m7FidBase_part2_mem _ (by
      unfold m7RowsPart2; (iterate 53 apply List.mem_append_right)
      exact List.mem_append_left _ (List.mem_of_getElem? (i := 0) rfl))
  have hUnitFold_b : (⟨"full_cong_unit_fold", [i64, i32, i32], [i64], m3CongUnitFoldSpec,
      true⟩ : SpecEntry) ∈ m7FidBaseTable :=
    m7FidBase_part2_mem _ (by
      unfold m7RowsPart2; (iterate 51 apply List.mem_append_right)
      exact List.mem_append_left _ (List.mem_of_getElem? (i := 1) rfl))
  have hEquivFold_b : (⟨"full_cong_equiv_fold", [i64, i32, i32, i32], [i64],
      m3CongEquivFoldSpec, true⟩ : SpecEntry) ∈ m7FidBaseTable :=
    m7FidBase_part2_mem _ (by
      unfold m7RowsPart2; (iterate 51 apply List.mem_append_right)
      exact List.mem_append_left _ (List.mem_of_getElem? (i := 2) rfl))
  have hAndM_b : (⟨"full_cong_and_match", [i64, i32, i32], [.bool], m6CongAndMatchSpec,
      true⟩ : SpecEntry) ∈ m7FidBaseTable :=
    m7FidBase_part2_mem _ (by
      unfold m7RowsPart2; (iterate 54 apply List.mem_append_right)
      exact List.mem_append_left _ (List.mem_of_getElem? (i := 10) rfl))
  have hXorM_b : (⟨"full_cong_xor_match", [i64, i32, i32], [i32], m6CongXorMatchSpec,
      true⟩ : SpecEntry) ∈ m7FidBaseTable :=
    m7FidBase_part2_mem _ (by
      unfold m7RowsPart2; (iterate 54 apply List.mem_append_right)
      exact List.mem_append_left _ (List.mem_of_getElem? (i := 11) rfl))
  have hEnqVar_b : (⟨"full_cong_enq_var", [i64, i64, i32], [], m6CongEnqVarSpec,
      true⟩ : SpecEntry) ∈ m7FidBaseTable :=
    m7FidBase_part2_mem _ (by
      unfold m7RowsPart2; (iterate 54 apply List.mem_append_right)
      exact List.mem_append_left _ (List.mem_of_getElem? (i := 12) rfl))
  have hEvalG_b : (⟨"full_cong_eval_gate", [i64, i64, i64, i64, i32, i64], [i64],
      m6CongEvalGateSpec, true⟩ : SpecEntry) ∈ m7FidBaseTable :=
    m7FidBase_part2_mem _ (by
      unfold m7RowsPart2; (iterate 54 apply List.mem_append_right)
      exact List.mem_append_left _ (List.mem_of_getElem? (i := 13) rfl))
  have hWork_b : (⟨"full_cong_worklist", [i64, i64, i64, i64], [i64], m6CongWorklistSpec,
      true⟩ : SpecEntry) ∈ m7FidBaseTable :=
    m7FidBase_part2_mem _ (by
      unfold m7RowsPart2; (iterate 54 apply List.mem_append_right)
      exact List.mem_append_left _ (List.mem_of_getElem? (i := 15) rfl))
  have hFind := sp_sw_base_noExit (sp_untouched_m7_mem_swTbl hFind_b (by decide) (by decide)
    (by decide))
  have hSort := sp_sw_base_noExit (sp_untouched_m7_mem_swTbl hSortU32_b (by decide) (by decide)
    (by decide))
  have hUnit := sp_sw_base_noExit (sp_untouched_m7_mem_swTbl hUnitFold_b (by decide) (by decide)
    (by decide))
  have hEquiv := sp_sw_base_noExit (sp_untouched_m7_mem_swTbl hEquivFold_b (by decide) (by decide)
    (by decide))
  have hAnd := sp_sw_base_noExit (sp_untouched_m7_mem_swTbl hAndM_b (by decide) (by decide)
    (by decide))
  have hXor := sp_sw_base_noExit (sp_untouched_m7_mem_swTbl hXorM_b (by decide) (by decide)
    (by decide))
  have hEnq := sp_sw_base_noExit (sp_m8SwV12_row_mem_swTbl hEnqVar_b (by decide) (by decide) rfl)
  have hEv8 := sp_sw_base_noExit (sp_m8SwV12_row_mem_swTbl hEvalG_b (by decide) (by decide) rfl)
  have hWk8 := sp_sw_base_noExit (sp_m8SwV12_row_mem_swTbl hWork_b (by decide) (by decide) rfl)
  have hExtBin := sp_sw_base_noExit (sp_untouched_m7_mem_swTbl hc2c.extBin (by decide) (by decide)
    (by decide))
  have hFindUE := sp_sw_base_noExit (sp_untouched_m7_mem_swTbl hc2c.findUE (by decide) (by decide)
    (by decide))
  have hExt := sp_sw_base_noExit (sp_untouched_m7_mem_swTbl hc2c.extract (by decide) (by decide)
    (by decide))
  have hIteAll := sp_sw_base_noExit (sp_untouched_m7_mem_swTbl hc2c.iteAll (by decide) (by decide)
    (by decide))
  have hFwdSub := sp_sw_base_noExit (sp_untouched_m7_mem_swTbl hc2c.fwdSub (by decide) (by decide)
    (by decide))
  have hNoBad : PatchModule.checkNoCallBad
      ["full_cong_eval_gate", "full_cong_work_step", "full_cong_worklist", "full_congruence_dense"]
      ["full_cong_enq_var", "full_cong_eval_gate", "full_cong_worklist"]
      m8SweepV2CoreParityModule.fns = true := by
    t_kernel_rfl
  refine ⟨hM.nodup, fun pre fn post hsplit => ?_⟩
  have hOk := hM.fnsOk pre fn post hsplit
  refine ⟨hOk.1, hOk.2.1, fun xs m Q X hlookup => ?_⟩
  by_cases hskip : fn.name ∈
      ["full_cong_eval_gate", "full_cong_work_step", "full_cong_worklist", "full_congruence_dense"]
  · have hfn_mem : fn ∈ m8SweepV2CoreParityFns := by
      change fn ∈ m8SweepV2CoreParityModule.fns; rw [hsplit]; simp
    have hf261 : m8SweepV2CoreParityFns[261]? = some FullM6CongSubst.full_cong_eval_gate := by
      have h := congrArg (·[0]?) sp_m8Sw_batch4; simpa using h
    have hf262 := sp_m8Sw_fn262
    have hf263 : m8SweepV2CoreParityFns[263]? = some FullM6CongSubst.full_cong_worklist := by
      have h := congrArg (·[2]?) sp_m8Sw_batch4; simpa using h
    have hf278 : m8SweepV2CoreParityFns[278]? = some m8CongruenceDenseFn := by
      have h := congrArg (·[3]?) sp_m8Sw_batch4; simpa using h
    have hElim : ∀ {sp : Spec fn.as fn.rs},
        (⟨fn.name, fn.as, fn.rs, sp, true⟩ : SpecEntry) ∈ m8SweepV2CoreParitySpecTable →
        sp xs m Q (fun _ _ _ _ => False) := fun {sp} hmem => by
      obtain ⟨_, _, hcast⟩ := m8cp_ofTable_sig_elim m8SweepV2CoreParitySpecTable_nodup hmem hlookup
      exact hcast
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hskip
    rcases hskip with hn | hn | hn | hn
    · have hfnEq := m8cp_nodup_name_eq Fn.name m8SweepV2CoreParityFns_names_nodup hfn_mem
        (List.mem_of_getElem? hf261) hn
      subst hfnEq
      have hs := hElim (sp_m8SwV12_row_mem_swTbl hEvalG_b (by decide) (by decide) rfl)
      exact full_cong_eval_gate_m8_wp _ hFind hSort hUnit hEquiv hAnd hXor hEnq xs m Q X hs
    · have hfnEq := m8cp_nodup_name_eq Fn.name m8SweepV2CoreParityFns_names_nodup hfn_mem
        (List.mem_of_getElem? hf262) hn
      subst hfnEq
      have hWs_b : (⟨"full_cong_work_step", [i64, i64, i64, i64, i32], [i64],
          FullM6CongSubst.m6CongWorkStepSpec, true⟩ : SpecEntry) ∈ m7FidBaseTable :=
        m7FidBase_part2_mem _ (by
          unfold m7RowsPart2; (iterate 54 apply List.mem_append_right)
          exact List.mem_append_left _ (List.mem_of_getElem? (i := 14) rfl))
      have hs := hElim (sp_untouched_m7_mem_swTbl hWs_b (by decide) (by decide) (by decide))
      exact workStep_wp_of_inactive_eval _ hFind
        (fun hIn => hEv8 _ _ _ _ (m6CongEvalGateSpec_inactive_to_m8 hIn)) xs m Q X hs
    · have hfnEq := m8cp_nodup_name_eq Fn.name m8SweepV2CoreParityFns_names_nodup hfn_mem
        (List.mem_of_getElem? hf263) hn
      subst hfnEq
      have hs := hElim (sp_m8SwV12_row_mem_swTbl hWork_b (by decide) (by decide) rfl)
      exact full_cong_worklist_m8_wp _ hFind hEv8 xs m Q X hs
    · have hfnEq := m8cp_nodup_name_eq Fn.name m8SweepV2CoreParityFns_names_nodup hfn_mem
        (List.mem_of_getElem? hf278) hn
      subst hfnEq
      have hs := hElim (sp_untouched_m7_mem_swTbl hc2p.congruenceDense (by decide) (by decide)
        (by decide))
      exact m8_congruence_dense_wp _ hExtBin hFindUE hExt hIteAll hWk8 hFwdSub xs m Q X hs
  · have hno : PatchModule.noCallInFn
        ["full_cong_enq_var", "full_cong_eval_gate", "full_cong_worklist"] fn = true := by
      have hc := List.all_eq_true.mp hNoBad fn
        (by change fn ∈ m8SweepV2CoreParityModule.fns; rw [hsplit]; simp)
      rcases (Bool.or_eq_true _ _).mp hc with hmem | hok
      · exact absurd (List.contains_iff_mem.mp hmem) hskip
      · exact hok
    have hwp := hOk.2.2 xs m Q X (m8SweepV2CoreParityEnv_of_specTable hlookup)
    exact PatchModule.fn_wp_env_agree_of_noCallIn hOk.1 hOk.2.1 hno
      (fun f as bs _ hnb xs m P E hf => sp_m8SwParityEnv_to_table_of_not_bad hnb hf) hwp

end LeanQbe.T.Examples.Kissat.FullFidelityCong

end
