/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityVivFlag
public import LeanQbe.T.Examples.Kissat.FullFidelityVivK6Proof0b
public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof3a
public import LeanQbe.T.Examples.Kissat.FullM6VivBackboneProof3b
public import LeanQbe.T.Examples.Kissat.FullM6OrchAdaptersProof0
public import LeanQbe.T.Examples.Kissat.FullM6HdrProof0
public import LeanQbe.T.Examples.Kissat.FullSpec
import LeanQbe.T.Examples.Kissat.FullVivTopLemmas1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Step-11 `S11-8` Flag Collect & Sort2 Proofs (`FullFidelityVivFlagProof0`)

UNSAT-only `Func.wp` proofs (`public section`, `0 @[expose]`, `0` new `import all`, `std3`,
`XPost`-polymorphic) aligning `PH_VIV` (`0x00100000u`) with upstream `vivify.c`:
1. `fid11VivCollectSpec` + `fid11_viv_collect_fid_wp`: pushes `PH_VIV == 0` first, then
   `PH_VIV != 0`; when `0` prioritized clauses were pushed, marks `ar[rr[k]] |= PH_VIV` across
   `0 <= k < bn`, preserving `FullSparseInv`, `fullArenaClauseRefs`, and non-arena `core` fields.
2. `fid11_viv_sort2_fid_wp` & `fid11_viv_sort_fid_wp`: sort `PH_VIV != 0` before `PH_VIV == 0`
   (`if (pv0 && !v0) { break; }`) for forward `rr[bi]` vivification scan.
3. `fid11_viv_clause_m6_wp`: clears `ar[cref] &= (~PH_VIV)` after trying a candidate when
   `fr != 2ULL && fr != 20ULL && (ar[cref] & PH_GARB) == 0u`.
-/

set_option autoImplicit false

local elab "fvt_steps_np" : tactic => LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 10000

local elab "fvt_to_group_np" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityVivFlag

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat LeanQbe.T.Examples.Kissat.Full
open FullVivTopTactics FullVivTop
open LeanQbe.T.Examples.Kissat.FullM6VivBackbone
open LeanQbe.T.Examples.Kissat.FullM6OrchAdapters
open LeanQbe.T.Examples.Kissat.FullM6Hdr
open LeanQbe.T.Examples.Kissat.FullFidelityVivK6
open scoped FullArenaTactics FullVivTopTactics

/-! ## 1. `fid11VivCollectSpec` & Strict Bridge -/

/-- Step-11 `full_viv_collect_fid(h, tier_mode)` specification: allows header-only `arena`
mutation preserving `FullSparseInv`, `fullArenaClauseRefs`, and all non-arena `core` fields
(used when `0` prioritized clauses exist and all `bn` scheduled clauses receive `PH_VIV`). -/
def fid11VivCollectSpec : Spec [i64, i64] [i64] := fun (h, _tier_mode, ()) m Q _ =>
  ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
    h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
    ∀ bn arena' rr' m',
      let s' : FullState :=
        { core := { s.core with arena := arena' }
          scratch := { s.scratch with red_refs := rr' } }
      bn.toNat ≤ c.red_cap → rr'.length = c.red_cap →
      FullSparseInv c F0 s' → fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (∀ k < bn.toNat, (rr'[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s') →
      (FullMem c s' ⋆ R) m' → Q (bn, ()) m'

theorem fid11VivCollectSpec_monoX {xs : Tup Val [i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X X' : XPost} (h : fid11VivCollectSpec xs m Q X) :
    fid11VivCollectSpec xs m Q X' := by rcases xs with ⟨_, _, ⟨⟩⟩; exact h

theorem fid11VivCollectSpec_intro {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {R : Mem 64 → Prop} {h tier_mode : BitVec 64} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hh : h = c.hdr) (hsp : FullSparseInv c F0 s) (hm : (FullMem c s ⋆ R) m)
    (hQ : ∀ bn arena' rr' m',
      let s' : FullState :=
        { core := { s.core with arena := arena' }
          scratch := { s.scratch with red_refs := rr' } }
      bn.toNat ≤ c.red_cap → rr'.length = c.red_cap →
      FullSparseInv c F0 s' → fullArenaClauseRefs s' = fullArenaClauseRefs s →
      (∀ k < bn.toNat, (rr'[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s') →
      (FullMem c s' ⋆ R) m' → Q (bn, ()) m') :
    fid11VivCollectSpec (h, tier_mode, ()) m Q X :=
  ⟨c, F0, s, R, hh, hsp, hm, hQ⟩

theorem fid11VivCollectSpec_elim {h tier_mode : BitVec 64} {m : Mem 64}
    {Q : Post [i64]} {X : XPost}
    (hsp0 : fid11VivCollectSpec (h, tier_mode, ()) m Q X) :
    ∃ (c : FullCfg) (F0 : CNF Nat) (s : FullState) (R : Mem 64 → Prop),
      h = c.hdr ∧ FullSparseInv c F0 s ∧ (FullMem c s ⋆ R) m ∧
      ∀ bn arena' rr' m',
        let s' : FullState :=
          { core := { s.core with arena := arena' }
            scratch := { s.scratch with red_refs := rr' } }
        bn.toNat ≤ c.red_cap → rr'.length = c.red_cap →
        FullSparseInv c F0 s' → fullArenaClauseRefs s' = fullArenaClauseRefs s →
        (∀ k < bn.toNat, (rr'[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s') →
        (FullMem c s' ⋆ R) m' → Q (bn, ()) m' :=
  hsp0

private theorem fid11_sparse_with_rr {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    (h : FullSparseInv c F0 s) {rr' : List (BitVec 32)} (hrr : rr'.length = c.red_cap) :
    FullSparseInv c F0 { s with scratch := { s.scratch with red_refs := rr' } } :=
  ⟨⟨⟨h.1.lengths.core_ok, { h.1.lengths.scratch_ok with red_refs_len := hrr }⟩, h.1.witness⟩,
    h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

theorem fullVivCollectFidSpec_of_fid11 {xs : Tup Val [i64, i64]} {m : Mem 64}
    {Q : Post [i64]} {X : XPost} (h : fid11VivCollectSpec xs m Q X) :
    fullVivCollectFidSpec xs m Q X := by
  rcases xs with ⟨hdr, tier_mode, ⟨⟩⟩
  obtain ⟨c, F0, s, R, rfl, hsp, hm, hQ⟩ := h
  exact fullVivCollectFidSpec_intro rfl hsp hm fun bn rr' m' hbn hrr hok hm' =>
    hQ bn s.core.arena rr' m' hbn hrr (fid11_sparse_with_rr hsp hrr) rfl hok hm'

/-! ## 2. `fid11_viv_collect_fid_wp` (`fid11VivCollectSpec`) -/

local macro "fid11_collect_post_mark"
    hsp0:ident hbn_le:ident hrr_len:ident hoko:ident hQ:ident
    c:ident F0:ident s:ident R:ident bn:ident rro:ident : tactic =>
  `(tactic| (
    have hrc := ($c).hred; have har_cap := ($c).harena
    unfold dimacsBound at hrc har_cap
    fvt_to_group
    refine wp_loop_inv (ts := [i64])
      (fun (k, ()) mk => ∃ ar_k : List (BitVec 32),
        k.toNat ≤ ($bn).toNat ∧
        FullSparseInv ($c) ($F0)
          { ($s) with core := { ($s).core with arena := ar_k }
                      scratch := { ($s).scratch with red_refs := ($rro) } } ∧
        fullArenaClauseRefs
          { ($s) with core := { ($s).core with arena := ar_k }
                      scratch := { ($s).scratch with red_refs := ($rro) } } =
          fullArenaClauseRefs ($s) ∧
        (FullMem ($c)
          { ($s) with core := { ($s).core with arena := ar_k }
                      scratch := { ($s).scratch with red_refs := ($rro) } } ⋆ ($R)) mk)
      (fun (k, ()) _ => ($bn).toNat - k.toNat)
      (fun Jk hJk => by
        fvt_steps
        exact hJk (0#64, ()) _ ⟨($s).core.arena, Nat.zero_le _,
          fid11_sparse_with_rr ($hsp0) ($hrr_len), rfl,
          (by assumption : (FullMem ($c) _ ⋆ ($R)) _)⟩)
      (fun Jk ⟨k, ⟨⟩⟩ mk ⟨ar_k, hk_le, hsp_k, hrefs_k, hmk⟩ ihk => by
        fvt_steps
        · have hk_lt : k.toNat < ($bn).toNat := by c0_bound
          have hk1 : (k + 1#64).toNat = k.toNat + 1 := by bv_omega
          have hk_rr : k.toNat < ($rro).length := by rw [($hrr_len)]; omega
          let cref := ($rro)[k.toNat]'hk_rr
          let sk : FullState :=
            { ($s) with core := { ($s).core with arena := ar_k }
                        scratch := { ($s).scratch with red_refs := ($rro) } }
          obtain ⟨F_cur_k, hsw_k⟩ := hsp_k.exists_witness
          have href_k : cref.toNat ∈ fullArenaClauseRefs sk := by
            rw [hrefs_k]
            have h := ($hoko) k.toNat hk_lt
            rwa [List.getElem?_eq_getElem hk_rr, Option.getD_some] at h
          have hwf_k := hsw_k.2.1.arena.refs_wf cref.toNat href_k
          have hcr_nat : (cref.setWidth 64).toNat = cref.toNat := bv32_setWidth64_toNat cref
          have har_len : ar_k.length = ($c).arena_cap := hsp_k.1.lengths.core_ok.arena_len_arr
          have hal_le : sk.core.arena_len ≤ ($c).arena_cap :=
            hsp_k.1.lengths.core_ok.arena_len_le
          have hcr_ar : cref.toNat < ar_k.length := by
            have h1 : cref.toNat + 3 ≤ sk.core.arena_len := hwf_k.1
            have h2 : sk.core.arena_len ≤ ($c).arena_cap := hal_le
            omega
          have hcr_bv : (cref.setWidth 64).toNat < ar_k.length := by omega
          let hdr_k := ar_k[cref.toNat]'hcr_ar
          have hhdr_k : fullArenaHdr sk cref.toNat = hdr_k := by
            unfold fullArenaHdr fullArenaHdrCore
            change sk.core.arena[cref.toNat]?.getD 0#32 = hdr_k
            rw [List.getElem?_eq_getElem hcr_ar, Option.getD_some]
          let hdr_v := hdr_k ||| 0x00100000#32
          obtain ⟨hsw_v, hrefs_v, _⟩ :=
            fullSparseInvW_set_hdr_non_gs hsw_k href_k hdr_v
              sk.core.num_irred sk.core.num_redundant
              (by rw [hhdr_k]; exact bv32_or_viv_garb hdr_k)
              (by rw [hhdr_k]; exact bv32_or_viv_shrk hdr_k)
          fvt_steps
          refine ihk (k + 1#64, ()) _ (by dsimp only; rw [hk1]; omega)
            ⟨ar_k.set cref.toNat hdr_v, by rw [hk1]; omega, hsw_v.toSparse,
             hrefs_v.trans hrefs_k, ?_⟩
          simpa only [hdr_v, hdr_k, hcr_nat,
            show (1048576 : BitVec 32) = 0x00100000#32 from rfl] using
            (by assumption : (FullMem ($c) _ ⋆ ($R)) _)
        · exact ($hQ) ($bn) ar_k ($rro) mk ($hbn_le) ($hrr_len) hsp_k hrefs_k
            (fun j hj => hrefs_k ▸ ($hoko) j hj) hmk)))

theorem fid11_viv_collect_fid_wp (Γ : Env)
    (hNext : ∀ a m Q X, Full.fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hTierMatch : ∀ a m Q X, fullVivTierMatchM6Spec a m Q X →
      Γ "full_viv_tier_match_m6" [i64, i32, i64] [.bool] a m Q X) :
    ∀ a m Q X, fid11VivCollectSpec a m Q X →
      Func.wp Γ fid11_viv_collect_fid_body a m Q X := by
  rintro ⟨h, tier_mode, ⟨⟩⟩ m0 Q X ⟨c, F0, s, R, rfl, hsp0, hm0, hQ⟩
  have har_cap := c.harena; have hmx := c.hmaxv; have hrc := c.hred
  unfold dimacsBound at har_cap hmx hrc
  obtain ⟨F_cur0, hsw0⟩ := hsp0.exists_witness
  have hal0 : s.core.arena_len ≤ c.arena_cap := hsp0.1.lengths.core_ok.arena_len_le
  have har0_len : s.core.arena.length = c.arena_cap := hsp0.1.lengths.core_ok.arena_len_arr
  have hrr0_len : s.scratch.red_refs.length = c.red_cap := hsp0.1.lengths.scratch_ok.red_refs_len
  have h0_mem : 0 = s.core.arena_len ∨ 0 ∈ fullArenaClauseRefs s := by
    rcases Nat.eq_zero_or_pos s.core.arena_len with h0 | hpos
    · exact Or.inl h0.symm
    · exact Or.inr (fullArenaClauseRefs_zero_mem hsw0.2.1.arena hpos)
  unfold Func.wp fid11_viv_collect_fid_body
  fvt_steps
  refine wp_loop_inv (ts := [i64, .bool, i64])
    (fun (bn, _any_p, pass, ()) mo => ∃ rro : List (BitVec 32),
      pass.toNat ≤ 2 ∧ bn.toNat ≤ c.red_cap ∧ rro.length = c.red_cap ∧
      (∀ k < bn.toNat, (rro[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
      (FullMem c { s with scratch := { s.scratch with red_refs := rro } } ⋆ R) mo)
    (fun (_, _, pass, ()) _ => 2 - pass.toNat)
    (fun Jo hJo => by
      fvt_steps
      exact hJo (0#64, false, 0#64, ()) m0 ⟨s.scratch.red_refs, Nat.zero_le _, Nat.zero_le _,
        hrr0_len, fun _ hk => by simp at hk, hm0⟩)
    (fun Jo ⟨bn0, any_po, pass, ⟨⟩⟩ mo ⟨rro, hpass_le, hbn0_le, hrro_len, hoko, hmo⟩ iho => ?_)
  fvt_steps
  · have hpass_lt : pass.toNat < 2 := by c0_bound
    have hpass1 : (pass + 1#64).toNat = pass.toNat + 1 := by bv_omega
    refine wp_loop_inv (ts := [i64, .bool, i64])
      (fun (bn, _any_p, p, ()) mp => ∃ rrp : List (BitVec 32),
        p.toNat ≤ s.core.arena_len ∧
        (p.toNat = s.core.arena_len ∨ p.toNat ∈ fullArenaClauseRefs s) ∧
        bn.toNat ≤ c.red_cap ∧ rrp.length = c.red_cap ∧
        (∀ k < bn.toNat, (rrp[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
        (FullMem c { s with scratch := { s.scratch with red_refs := rrp } } ⋆ R) mp)
      (fun (_, _, p, ()) _ => s.core.arena_len - p.toNat)
      (fun J1 hJ1 => by
        fvt_steps
        exact hJ1 (bn0, any_po, 0#64, ()) mo
          ⟨rro, Nat.zero_le _, h0_mem, hbn0_le, hrro_len, hoko, hmo⟩)
      (fun J1 ⟨bn, any_p, p, ⟨⟩⟩ mp ⟨rrp, hp_le, hp_mem, hbn_le, hrrp_len, hokp, hmp⟩ ih1 => ?_)
    fvt_steps
    · have hp_lt : p.toNat < s.core.arena_len := by c0_bound
      have hp_ref : p.toNat ∈ fullArenaClauseRefs s := hp_mem.resolve_left (by omega)
      have hwfp := hsw0.2.1.arena.refs_wf p.toNat hp_ref
      have hp_lt_ar : p.toNat < s.core.arena.length := by omega
      have hp32 : (p.setWidth 32).toNat = p.toNat := by bv_omega
      fvt_steps
      c0_call hNext
      refine ⟨c, { s with scratch := { s.scratch with red_refs := rrp } },
        R, rfl, ⟨hsp0.1.lengths.core_ok,
          { hsp0.1.lengths.scratch_ok with red_refs_len := hrrp_len }⟩,
        hmp, ?_⟩
      let np_nat := fullArenaNextOff s.core.arena s.core.arena_len (p.setWidth 32).toNat
      have hnb : p.toNat < np_nat ∧ np_nat ≤ s.core.arena_len := by
        dsimp only [np_nat]; rw [hp32]; exact fullArenaNextOff_bounds hwfp.1
      have hnp_mem : np_nat = s.core.arena_len ∨ np_nat ∈ fullArenaClauseRefs s := by
        dsimp only [np_nat]; rw [hp32]
        exact fullArenaClauseRefs_next_mem_or_end hsw0.2.1.arena hp_ref
      have hnp_bv : ((BitVec.ofNat 32 np_nat).setWidth 64).toNat = np_nat := by
        rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
          Nat.mod_eq_of_lt (by omega)]
      dsimp only; fvt_to_group
      refine wp_join_group (ts := [i64, .bool])
        (fun (bn', _any_n, ()) mn => ∃ rrn : List (BitVec 32),
          bn'.toNat ≤ c.red_cap ∧ rrn.length = c.red_cap ∧
          (∀ k < bn'.toNat, (rrn[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
          (FullMem c { s with scratch := { s.scratch with red_refs := rrn } } ⋆ R) mn) ?_ ?_
      · rintro _ ⟨bn', any_n, ⟨⟩⟩ mn ⟨rrn, hbn'_le, hrrn_len, hokn, hmn⟩
        fvt_steps
        exact ih1 (bn', any_n, (BitVec.ofNat 32 np_nat).setWidth 64, ()) mn
          (by dsimp only; rw [hnp_bv]; omega)
          ⟨rrn, by rw [hnp_bv]; exact hnb.2, by rw [hnp_bv]; exact hnp_mem,
            hbn'_le, hrrn_len, hokn, hmn⟩
      · intro Jn hJn
        c0_hsplit
        · fvt_to_group
          refine wp_join_group (ts := [i32]) (fun _ mw => mp = mw) ?_
            (fun Jw hJw => by fvt_steps <;> exact hJw _ mp rfl)
          rintro _ ⟨want, ⟨⟩⟩ _ rfl
          fvt_to_group
          refine wp_join_group (ts := [i64, .bool])
            (fun (bn', _any_n, ()) mn => ∃ rrn : List (BitVec 32),
              bn'.toNat ≤ c.red_cap ∧ rrn.length = c.red_cap ∧
              (∀ k < bn'.toNat, (rrn[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
              (FullMem c { s with scratch := { s.scratch with red_refs := rrn } } ⋆ R) mn)
            (fun _ x mn hx => hJn x mn hx)
            (fun Jt hJt => by
              c0_hsplit
              · c0_call hTierMatch
                refine ⟨c, { s with scratch := { s.scratch with red_refs := rrp } }, R, rfl, hmp,
                  fun matched => ?_⟩
                fvt_steps
                · have hbn_lt : bn.toNat < c.red_cap := by c0_bound
                  have hbn1 : (bn + 1#64).toNat = bn.toNat + 1 := by bv_omega
                  have hoks : ∀ k < (bn + 1#64).toNat,
                      ((rrp.set bn.toNat (p.setWidth 32))[k]?.getD 0#32).toNat ∈
                        fullArenaClauseRefs s := by
                    intro k hk; rw [hbn1] at hk
                    by_cases hke : k = bn.toNat
                    · subst hke; rw [List.getElem?_set_self (by omega), Option.getD_some, hp32]
                      exact hp_ref
                    · rw [List.getElem?_set_ne (by omega)]; exact hokp k (by omega)
                  exact hJt (bn + 1#64, true, ()) m
                    ⟨_, by rw [hbn1]; omega, by simp [hrrp_len], hoks, hm⟩
                · have hbn_lt : bn.toNat < c.red_cap := by c0_bound
                  have hbn1 : (bn + 1#64).toNat = bn.toNat + 1 := by bv_omega
                  have hoks : ∀ k < (bn + 1#64).toNat,
                      ((rrp.set bn.toNat (p.setWidth 32))[k]?.getD 0#32).toNat ∈
                        fullArenaClauseRefs s := by
                    intro k hk; rw [hbn1] at hk
                    by_cases hke : k = bn.toNat
                    · subst hke; rw [List.getElem?_set_self (by omega), Option.getD_some, hp32]
                      exact hp_ref
                    · rw [List.getElem?_set_ne (by omega)]; exact hokp k (by omega)
                  exact hJt (bn + 1#64, any_p, ()) m
                    ⟨_, by rw [hbn1]; omega, by simp [hrrp_len], hoks, hm⟩
                · exact hJt (bn, any_p, ()) mp ⟨rrp, hbn_le, hrrp_len, hokp, hmp⟩
                · exact hJt (bn, any_p, ()) mp ⟨rrp, hbn_le, hrrp_len, hokp, hmp⟩
              · fvt_steps; exact hJt (bn, any_p, ()) mp ⟨rrp, hbn_le, hrrp_len, hokp, hmp⟩)
        · fvt_steps; exact hJn (bn, any_p, ()) mp ⟨rrp, hbn_le, hrrp_len, hokp, hmp⟩
    · fvt_steps
      exact iho (bn, any_p, pass + 1#64, ()) mp (by dsimp only; rw [hpass1]; omega)
        ⟨rrp, by rw [hpass1]; omega, hbn_le, hrrp_len, hokp, hmp⟩
  all_goals first
    | exact hQ bn0 s.core.arena rro mo hbn0_le hrro_len
        (fid11_sparse_with_rr hsp0 hrro_len) rfl hoko hmo
    | fid11_collect_post_mark hsp0 hbn0_le hrro_len hoko hQ c F0 s R bn0 rro

/-! ## 3. `fid11_viv_sort2_fid_wp` & `fid11_viv_sort_fid_wp` (`PV` First) -/

theorem fid11_sort_set_rr_ok {rr : List (BitVec 32)} {cap bn idx : Nat}
    {v : BitVec 32} {refs : List Nat}
    (hlen : rr.length = cap) (_hbn : bn ≤ cap) (hidx : idx < cap)
    (hok : ∀ k < bn, (rr[k]?.getD 0#32).toNat ∈ refs)
    (hv : idx < bn → v.toNat ∈ refs) :
    (rr.set idx v).length = cap ∧
    ∀ k < bn, ((rr.set idx v)[k]?.getD 0#32).toNat ∈ refs := by
  refine ⟨by simp [hlen], fun k hk => ?_⟩
  by_cases hke : k = idx
  · subst hke; rw [List.getElem?_set_self (by omega), Option.getD_some]; exact hv hk
  · rw [List.getElem?_set_ne (by omega)]; exact hok k hk

theorem fid11_bv64_shl1 {x : BitVec 64} (hx : x.toNat < 2 ^ 60) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm,
    Nat.mod_eq_of_lt (by omega)]

theorem fid11_bv64_shl1_add1 {x : BitVec 64} (hx : x.toNat < 2 ^ 60) :
    ((x <<< (1 : Nat)) + 1#64).toNat = 2 * x.toNat + 1 := by
  rw [BitVec.toNat_add, fid11_bv64_shl1 hx, show (1#64 : BitVec 64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega)]

theorem fid11_knuth_gap_step {gap bn : BitVec 64}
    (hgap1 : 1 ≤ gap.toNat) (hglt : gap.toNat < bn.toNat / 3) (hbd : bn.toNat < 2 ^ 28) :
    (gap * 3#64 + 1#64).toNat = 3 * gap.toNat + 1 ∧
      1 ≤ (gap * 3#64 + 1#64).toNat ∧ (gap * 3#64 + 1#64).toNat ≤ bn.toNat ∧
      bn.toNat - (gap * 3#64 + 1#64).toNat < bn.toNat - gap.toNat := by
  have h264 : bn.toNat < 2 ^ 64 := Nat.lt_trans hbd (by decide)
  have h1 : gap.toNat * 3 < 2 ^ 64 := by omega
  have h2 : gap.toNat * 3 + 1 < 2 ^ 64 := by omega
  have hg3 : (gap * 3#64 + 1#64).toNat = 3 * gap.toNat + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_mul, show (3#64 : BitVec 64).toNat = 3 from rfl,
      show (1#64 : BitVec 64).toNat = 1 from rfl, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]
    omega
  rw [hg3]; exact ⟨rfl, by omega, by omega, by omega⟩

theorem fid11_knuth_gap_div3 {gap : BitVec 64} {bnNat : Nat}
    (hpos : 0 < gap.toNat) (hle : gap.toNat ≤ bnNat) :
    (gap / 3#64).toNat = gap.toNat / 3 ∧
      (gap / 3#64).toNat < gap.toNat ∧ (gap / 3#64).toNat ≤ bnNat := by
  have hd : (gap / 3#64).toNat = gap.toNat / 3 := by
    rw [BitVec.toNat_udiv, show (3#64 : BitVec 64).toNat = 3 from rfl]
  rw [hd]; exact ⟨rfl, by omega, by omega⟩

theorem fid11_viv_sort2_fid_wp (Γ : Env) :
    ∀ a m Q X, fullVivSort2FidSpec a m Q X →
      Func.wp Γ fid11_viv_sort2_fid_body a m Q X := by
  rintro ⟨h, bn, md, ⟨⟩⟩ m0 Q X hs
  obtain ⟨c, F0, s, R, rfl, hsp0, hbn_le, hmd12, hok0, hm0, hQ⟩ := fullVivSort2FidSpec_elim hs
  have har_cap := c.harena; have hmx := c.hmaxv; have hrc := c.hred; have hsc := c.hscr
  unfold dimacsBound at har_cap hmx hrc hsc
  obtain ⟨F_cur0, hsw0⟩ := hsp0.exists_witness
  have hcv_le := hsp0.1.lengths.core_ok.cur_vars_le
  have har_le := hsp0.1.lengths.core_ok.arena_len_le
  have har_len := hsp0.1.lengths.core_ok.arena_len_arr
  have hrr_len := hsp0.1.lengths.scratch_ok.red_refs_len
  have htr_len := hsp0.1.lengths.scratch_ok.tarjan_reach_len
  have hscr_len := hsp0.1.lengths.scratch_ok.scratch_buf_len
  have hnlits : (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat = 2 * s.core.cur_vars := by
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.shiftLeft_eq, Nat.pow_one, Nat.mod_eq_of_lt (by omega)]; omega
  let KeysState (rr scr : List (BitVec 32)) : Prop :=
    rr.length = c.red_cap ∧ scr.length = c.scratch_cap ∧
    ∀ k < bn.toNat, (rr[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s
  let KeyPtr (kp : BitVec 64) : Prop :=
    (md = 1#64 ∧ kp = c.pRedRefs + bn * 4 ∧ 3 * bn.toNat ≤ c.red_cap) ∨
    (md = 2#64 ∧ kp = c.pScratchBuf ∧ 2 * bn.toNat ≤ c.scratch_cap)
  have hkey_load : ∀ {kp idx : BitVec 64} {rr scr : List (BitVec 32)} {mk : Mem 64},
      KeyPtr kp → KeysState rr scr → idx.toNat < 2 * bn.toNat →
      (FullMem c { s with scratch := { s.scratch with red_refs := rr, scratch_buf := scr } }
        ⋆ R) mk →
      ∃ v, loadVal mk i32 (kp + idx * 4) = some v := by
    intro kp idx rr scr mk hkp hks hidx hmk
    rcases hkp with ⟨_, rfl, h3⟩ | ⟨_, rfl, h2⟩
    · have haddr : c.pRedRefs + bn * 4 + idx * 4 =
          c.pRedRefs + BitVec.ofNat 64 (4 * (bn.toNat + idx.toNat)) := by
        apply BitVec.eq_of_toNat_eq
        have h4 : (4 : BitVec 64).toNat = 4 := rfl
        simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h4]
        rw [Nat.mul_add]; omega
      have hlt : bn.toNat + idx.toNat < rr.length := by rw [hks.1]; omega
      refine ⟨rr[bn.toNat + idx.toNat]'hlt, ?_⟩
      rw [haddr]
      have hF : (array (t := i32) c.pRedRefs rr ⋆
          (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur
            s.core.d_val ⋆ array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
            FullCoreArrays c s.core ⋆
            (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
             FullScrWksArrs c s.scratch ⋆ FullScrMetaArrs c s.scratch ⋆
             (array (t := i32) c.pDelayed s.scratch.delayed ⋆
              array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
              array (t := i32) c.pScratchBuf scr)) ⋆ c.pad ⋆ R)) mk := by
        unfold FullMem FullScratchArrays FullScrDynArrs at hmk; exact sep_cast hmk (by ac_rfl)
      exact loadVal_array (t := i32) (by decide) hlt hF
    · have haddr : c.pScratchBuf + idx * 4 = c.pScratchBuf + BitVec.ofNat 64 (4 * idx.toNat) := by
        rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
      have hlt : idx.toNat < scr.length := by rw [hks.2.1]; omega
      refine ⟨scr[idx.toNat]'hlt, ?_⟩
      rw [haddr]
      have hF : (array (t := i32) c.pScratchBuf scr ⋆
          (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur
            s.core.d_val ⋆ array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
            FullCoreArrays c s.core ⋆
            (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
             FullScrWksArrs c s.scratch ⋆ FullScrMetaArrs c s.scratch ⋆
             (array (t := i32) c.pDelayed s.scratch.delayed ⋆
              array (t := i32) c.pRedRefs rr ⋆
              array (t := i32) c.pExtendStk s.scratch.extend_stk)) ⋆ c.pad ⋆ R)) mk := by
        unfold FullMem FullScratchArrays FullScrDynArrs at hmk; exact sep_cast hmk (by ac_rfl)
      exact loadVal_array (t := i32) (by decide) hlt hF
  have hkey_store : ∀ {kp idx : BitVec 64} (v : BitVec 32) {rr scr : List (BitVec 32)}
      {mk : Mem 64}, KeyPtr kp → KeysState rr scr → idx.toNat < 2 * bn.toNat →
      (FullMem c { s with scratch := { s.scratch with red_refs := rr, scratch_buf := scr } }
        ⋆ R) mk →
      storeOk mk i32 (kp + idx * 4) ∧
      ∃ rr' scr', KeysState rr' scr' ∧
        (FullMem c { s with scratch := { s.scratch with red_refs := rr', scratch_buf := scr' } }
          ⋆ R) (storeMem mk i32 (kp + idx * 4) v) := by
    intro kp idx v rr scr mk hkp hks hidx hmk
    rcases hkp with ⟨_, rfl, h3⟩ | ⟨_, rfl, h2⟩
    · have haddr : c.pRedRefs + bn * 4 + idx * 4 =
          c.pRedRefs + BitVec.ofNat 64 (4 * (bn.toNat + idx.toNat)) := by
        apply BitVec.eq_of_toNat_eq
        have h4 : (4 : BitVec 64).toNat = 4 := rfl
        simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h4]
        rw [Nat.mul_add]; omega
      have hlt : bn.toNat + idx.toNat < rr.length := by rw [hks.1]; omega
      have hF : (array (t := i32) c.pRedRefs rr ⋆
          (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur
            s.core.d_val ⋆ array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
            FullCoreArrays c s.core ⋆
            (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
             FullScrWksArrs c s.scratch ⋆ FullScrMetaArrs c s.scratch ⋆
             (array (t := i32) c.pDelayed s.scratch.delayed ⋆
              array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
              array (t := i32) c.pScratchBuf scr)) ⋆ c.pad ⋆ R)) mk := by
        unfold FullMem FullScratchArrays FullScrDynArrs at hmk; exact sep_cast hmk (by ac_rfl)
      obtain ⟨hok, hst⟩ := store_array (t := i32) v (by decide) hlt hF
      rw [show (i32 : Ty).bytes = 4 from rfl, ← haddr] at hok hst
      refine ⟨hok, rr.set (bn.toNat + idx.toNat) v, scr,
        ⟨by simp [hks.1], hks.2.1, fun k hk => by
          rw [List.getElem?_set_ne (by omega)]; exact hks.2.2 k hk⟩, ?_⟩
      unfold FullMem FullScratchArrays FullScrDynArrs; exact sep_cast hst (by ac_rfl)
    · have haddr : c.pScratchBuf + idx * 4 = c.pScratchBuf + BitVec.ofNat 64 (4 * idx.toNat) := by
        rw [show (4 : BitVec 64) = BitVec.ofNat 64 4 from rfl, c0_mul_ofNat]
      have hlt : idx.toNat < scr.length := by rw [hks.2.1]; omega
      have hF : (array (t := i32) c.pScratchBuf scr ⋆
          (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur
            s.core.d_val ⋆ array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
            FullCoreArrays c s.core ⋆
            (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
             FullScrWksArrs c s.scratch ⋆ FullScrMetaArrs c s.scratch ⋆
             (array (t := i32) c.pDelayed s.scratch.delayed ⋆
              array (t := i32) c.pRedRefs rr ⋆
              array (t := i32) c.pExtendStk s.scratch.extend_stk)) ⋆ c.pad ⋆ R)) mk := by
        unfold FullMem FullScratchArrays FullScrDynArrs at hmk; exact sep_cast hmk (by ac_rfl)
      obtain ⟨hok, hst⟩ := store_array (t := i32) v (by decide) hlt hF
      rw [show (i32 : Ty).bytes = 4 from rfl, ← haddr] at hok hst
      refine ⟨hok, rr, scr.set idx.toNat v,
        ⟨hks.1, by simp [hks.2.1], hks.2.2⟩, ?_⟩
      unfold FullMem FullScratchArrays FullScrDynArrs; exact sep_cast hst (by ac_rfl)
  unfold Func.wp fid11_viv_sort2_fid_body
  c0_hsplit
  · fvt_steps_np
    exact hQ s.scratch.red_refs s.scratch.scratch_buf m0 hrr_len hscr_len hok0 hm0
  have h1_bn : 1 < bn.toNat := by c0_bound
  fvt_to_group_np
  refine wp_join_group (ts := [i64]) (fun (kp, ()) mk => m0 = mk ∧ KeyPtr kp) ?_
    (fun Jk hJk => by
      c0_hsplit
      · fvt_steps_np
        have h1 : md = 1#64 := by c0_bound
        rcases hmd12 with ⟨_, h3⟩ | ⟨h2, _⟩
        · exact hJk _ m0 ⟨rfl, Or.inl ⟨h1, rfl, h3⟩⟩
        · exact absurd (h1.symm.trans h2) (by decide)
      · fvt_steps_np
        have hne1 : md ≠ 1#64 := by c0_bound
        rcases hmd12 with ⟨h1, _⟩ | ⟨h2, h2b⟩
        · exact absurd h1 hne1
        · exact hJk _ m0 ⟨rfl, Or.inr ⟨h2, rfl, h2b⟩⟩)
  rintro _ ⟨kp, ⟨⟩⟩ _ ⟨rfl, hkp⟩
  refine wp_loop_inv (ts := [i64])
    (fun (bi, ()) mbi => ∃ rr scr, bi.toNat ≤ bn.toNat ∧ KeysState rr scr ∧
      (FullMem c { s with scratch := { s.scratch with red_refs := rr, scratch_buf := scr } }
        ⋆ R) mbi)
    (fun (bi, ()) _ => bn.toNat - bi.toNat)
    (fun Jb hJb => by
      fvt_steps_np
      exact hJb (0#64, ()) m0 ⟨s.scratch.red_refs, s.scratch.scratch_buf, Nat.zero_le _,
        ⟨hrr_len, hscr_len, hok0⟩, hm0⟩)
    (fun Jb ⟨bi, ⟨⟩⟩ mbi ⟨rr, scr, hbi_le, hks, hmbi⟩ ihb => ?_)
  c0_hsplit
  · have hbi_lt : bi.toNat < bn.toNat := by c0_bound
    have hbi1 : (bi + 1#64).toNat = bi.toNat + 1 := by bv_omega
    have hbi_rr : bi.toNat < rr.length := by rw [hks.1]; omega
    let cr := rr[bi.toNat]'hbi_rr
    have hcr_ref : cr.toNat ∈ fullArenaClauseRefs s := by
      have h := hks.2.2 bi.toNat hbi_lt
      rwa [List.getElem?_eq_getElem hbi_rr, Option.getD_some] at h
    have hwfc := hsw0.2.1.arena.refs_wf cr.toNat hcr_ref
    have hcr2_nat : (cr.setWidth 64 + 2#64).toNat = cr.toNat + 2 := by
      rw [BitVec.toNat_add, zext_toNat cr (by decide), show (2#64).toNat = 2 from rfl,
        Nat.mod_eq_of_lt (by omega)]
    have hcr2_lt : (cr.setWidth 64 + 2#64).toNat < s.core.arena.length := by
      rw [hcr2_nat]; omega
    let sz := s.core.arena[(cr.setWidth 64 + 2#64).toNat]'hcr2_lt
    have hsz_eq : sz.toNat = fullArenaClauseSizeCore s.core cr.toNat := by
      dsimp only [sz]; unfold fullArenaClauseSizeCore
      rw [List.getElem?_eq_getElem (by omega : cr.toNat + 2 < s.core.arena.length),
        Option.getD_some]
      exact congrArg BitVec.toNat (by simp only [hcr2_nat])
    have hsz_bd : cr.toNat + 3 + sz.toNat ≤ s.core.arena_len := by
      rw [hsz_eq]; exact Nat.le_trans hwfc.2.2.1 hwfc.2.2.2.1
    fvt_steps_np
    refine wp_loop_inv (ts := [i32, i32, i32, i32, i32])
      (fun (_k0, _d0, _k1, _d1, j, ()) mj => mbi = mj ∧ j.toNat ≤ sz.toNat)
      (fun (_, _, _, _, j, ()) _ => sz.toNat - j.toNat)
      (fun Jj hJj => by fvt_steps_np; exact hJj _ mbi ⟨rfl, Nat.zero_le _⟩)
      (fun Jj ⟨k0, d0, k1, d1, j, ⟨⟩⟩ mj ⟨rfl, hj_le⟩ ihj => ?_)
    c0_hsplit
    · have hj_lt : j.toNat < sz.toNat := by c0_bound
      have hj1 : (j + 1#32).toNat = j.toNat + 1 := by bv_omega
      have hj_idx : (cr.setWidth 64 + 3#64 + j.setWidth 64).toNat =
          cr.toNat + 3 + j.toNat := by
        rw [BitVec.toNat_add, BitVec.toNat_add, zext_toNat cr (by decide),
          zext_toNat j (by decide), show (3#64).toNat = 3 from rfl,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      have hj_ar : (cr.setWidth 64 + 3#64 + j.setWidth 64).toNat < s.core.arena.length := by
        rw [hj_idx]; omega
      fvt_to_group_np
      refine wp_join_group (ts := [i32]) (fun _ md => mbi = md) ?_
        (fun Jd hJd => by
          c0_hsplit
          · have hl_lt : (s.core.arena[(cr.setWidth 64 + 3#64 + j.setWidth 64).toNat]'hj_ar).toNat
                < 2 * s.core.cur_vars := by
              have hc' : ((s.core.arena[(cr.setWidth 64 + 3#64 +
                  j.setWidth 64).toNat]'hj_ar).setWidth 64).toNat <
                  (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat := by c0_bound
              rwa [zext_toNat _ (by decide), hnlits] at hc'
            fvt_steps_np; exact hJd _ mbi rfl
          · try fvt_steps_np; exact hJd _ mbi rfl)
      rintro _ ⟨dl, ⟨⟩⟩ _ rfl
      fvt_to_group_np
      refine wp_join_group (ts := [i32, i32, i32, i32]) (fun _ mu => mbi = mu)
        (fun _ ⟨k0', d0', k1', d1', ⟨⟩⟩ mu hmu => by
          subst hmu; fvt_steps_np
          exact ihj (k0', d0', k1', d1', j + 1#32, ()) mbi
            (by dsimp only; rw [hj1]; omega) ⟨rfl, by rw [hj1]; omega⟩)
        (fun Ju hJu => by fvt_steps_np <;> exact hJu _ mbi rfl)
    · have hbi2 : (bi <<< (1 : Nat)).toNat = 2 * bi.toNat := fid11_bv64_shl1 (by omega)
      have hbi21 : ((bi <<< (1 : Nat)) + 1#64).toNat = 2 * bi.toNat + 1 :=
        fid11_bv64_shl1_add1 (by omega)
      fvt_to_group_np
      obtain ⟨hok_k0, rr1, scr1, hks1, hm1⟩ := hkey_store (idx := bi <<< (1 : Nat)) k0
        hkp hks (by rw [hbi2]; omega) hmbi
      refine wp_store_sep ⟨hok_k0, hm1⟩ fun mbi1 hmbi1 => ?_
      obtain ⟨hok_k1, rr2, scr2, hks2, hm2⟩ := hkey_store (idx := (bi <<< (1 : Nat)) + 1#64) k1
        hkp hks1 (by rw [hbi21]; omega) hmbi1
      try fvt_to_group_np
      refine wp_store_sep ⟨hok_k1, hm2⟩ fun mbi2 hmbi2 => ?_
      fvt_steps_np
      exact ihb (bi + 1#64, ()) mbi2 (by dsimp only; rw [hbi1]; omega)
        ⟨rr2, scr2, by rw [hbi1]; omega, hks2, hmbi2⟩
  · have hbn3 : (bn / 3#64).toNat = bn.toNat / 3 := by
      rw [BitVec.toNat_udiv, show (3#64 : BitVec 64).toNat = 3 from rfl]
    fvt_to_group_np
    refine wp_loop_inv (ts := [i64])
      (fun (gap, ()) mg => mbi = mg ∧ 1 ≤ gap.toNat ∧ gap.toNat ≤ bn.toNat)
      (fun (gap, ()) _ => bn.toNat - gap.toNat)
      (fun Jk hJk => by
        fvt_steps_np
        exact hJk (1#64, ()) mbi ⟨rfl, by decide, by bv_omega⟩)
      (fun Jk ⟨gap, ⟨⟩⟩ mg ⟨rfl, hgap1, hgap_le⟩ ihk => by
        c0_hsplit
        · have hglt : gap.toNat < bn.toNat / 3 := by
            have hc' : gap.toNat < (bn / 3#64).toNat := by c0_bound
            rwa [hbn3] at hc'
          obtain ⟨_, hge1, hle_bn, hdec⟩ := fid11_knuth_gap_step hgap1 hglt (by omega)
          fvt_steps_np
          exact ihk (gap * 3#64 + 1#64, ()) mbi hdec ⟨rfl, hge1, hle_bn⟩
        · fvt_to_group_np
          refine wp_loop_inv (ts := [i64])
            (fun (gap, ()) mg => ∃ rrg scrg, gap.toNat ≤ bn.toNat ∧ KeysState rrg scrg ∧
              (FullMem c { s with
                scratch := { s.scratch with red_refs := rrg, scratch_buf := scrg } } ⋆ R) mg)
            (fun (gap, ()) _ => gap.toNat)
            (fun Jg hJg => by
              fvt_steps_np
              exact hJg (gap, ()) mbi ⟨rr, scr, hgap_le, hks, hmbi⟩)
            (fun Jg ⟨gap, ⟨⟩⟩ mg ⟨rrg, scrg, hgap_le, hksg, hmg⟩ ihg => ?_)
          c0_hsplit
          · have hgap_pos : 0 < gap.toNat := by c0_bound
            obtain ⟨hgap3, _, _⟩ := fid11_knuth_gap_div3 (bnNat := bn.toNat) hgap_pos hgap_le
            fvt_to_group_np
            refine wp_loop_inv (ts := [i64])
              (fun (si, ()) msi => ∃ rrs scrs, gap.toNat ≤ si.toNat ∧ si.toNat ≤ bn.toNat ∧
                KeysState rrs scrs ∧
                (FullMem c { s with
                  scratch := { s.scratch with red_refs := rrs, scratch_buf := scrs } } ⋆ R) msi)
              (fun (si, ()) _ => bn.toNat - si.toNat)
              (fun Js hJs => by fvt_steps_np; exact hJs (gap, ()) mg ⟨rrg, scrg, Nat.le_refl _,
                hgap_le, hksg, hmg⟩)
              (fun Js ⟨si, ⟨⟩⟩ msi ⟨rrs, scrs, hsi_lo, hsi_le, hkss, hmsi⟩ ihs => ?_)
            c0_hsplit
            · have hsi_lt : si.toNat < bn.toNat := by c0_bound
              have hsi1 : (si + 1#64).toNat = si.toNat + 1 := by bv_omega
              have hsi_rr : si.toNat < rrs.length := by rw [hkss.1]; omega
              let cr := rrs[si.toNat]'hsi_rr
              have hcr_ref : cr.toNat ∈ fullArenaClauseRefs s := by
                have h := hkss.2.2 si.toNat hsi_lt
                rwa [List.getElem?_eq_getElem hsi_rr, Option.getD_some] at h
              have hwfc := hsw0.2.1.arena.refs_wf cr.toNat hcr_ref
              have hsi2 : (si <<< (1 : Nat)).toNat = 2 * si.toNat := fid11_bv64_shl1 (by omega)
              have hsi21 : ((si <<< (1 : Nat)) + 1#64).toNat = 2 * si.toNat + 1 :=
                fid11_bv64_shl1_add1 (by omega)
              fvt_to_group_np
              obtain ⟨k0, hlk0⟩ := hkey_load (idx := si <<< (1 : Nat)) hkp hkss
                (by rw [hsi2]; omega) hmsi
              obtain ⟨k1, hlk1⟩ := hkey_load (idx := (si <<< (1 : Nat)) + 1#64) hkp hkss
                (by rw [hsi21]; omega) hmsi
              refine wp_load_of (by dsimp only [Arg.val]; exact hlk0) ?_
              try fvt_to_group_np
              refine wp_load_of (by dsimp only [Arg.val]; exact hlk1) ?_
              have hcr_ar : (cr.setWidth 64).toNat < s.core.arena.length := by
                rw [zext_toNat cr (by decide)]; omega
              fvt_to_group_np
              refine wp_join_group (ts := [i32]) (fun _ m1 => msi = m1) ?_
                (fun Jd0 hJd0 => by
                  c0_hsplit
                  · have hlt : (k0.setWidth 64).toNat < s.scratch.tarjan_reach.length := by
                      have hc' : (k0.setWidth 64).toNat <
                          (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat := by c0_bound
                      rw [hnlits] at hc'; omega
                    fvt_steps_np; exact hJd0 _ msi rfl
                  · try fvt_steps_np; exact hJd0 _ msi rfl)
              rintro _ ⟨dk0, ⟨⟩⟩ _ rfl
              fvt_to_group_np
              refine wp_join_group (ts := [i32]) (fun _ m2 => msi = m2) ?_
                (fun Jd1 hJd1 => by
                  c0_hsplit
                  · have hlt : (k1.setWidth 64).toNat < s.scratch.tarjan_reach.length := by
                      have hc' : (k1.setWidth 64).toNat <
                          (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat := by c0_bound
                      rw [hnlits] at hc'; omega
                    fvt_steps_np; exact hJd1 _ msi rfl
                  · try fvt_steps_np; exact hJd1 _ msi rfl)
              rintro _ ⟨dk1, ⟨⟩⟩ _ rfl
              refine wp_loop_break_group (brkTs := [i64]) (lpTs := [i64])
                (fun (sj_f, ()) msf => ∃ rrf scrf, sj_f.toNat < bn.toNat ∧ KeysState rrf scrf ∧
                  (FullMem c { s with
                    scratch := { s.scratch with red_refs := rrf, scratch_buf := scrf } } ⋆ R) msf)
                (fun rem (sj, ()) msj => ∃ rrj scrj, sj.toNat < bn.toNat ∧ rem = sj.toNat ∧
                  KeysState rrj scrj ∧
                  (FullMem c { s with
                    scratch := { s.scratch with red_refs := rrj, scratch_buf := scrj } } ⋆ R) msj)
                ?_ ?_ ?_
              · rintro _ ⟨sj_f, ⟨⟩⟩ msf ⟨rrf, scrf, hsjf_lt, hksf, hmsf⟩
                have hsjf_rr : sj_f.toNat < rrf.length := by rw [hksf.1]; omega
                have hsjf2 : (sj_f <<< (1 : Nat)).toNat = 2 * sj_f.toNat :=
                  fid11_bv64_shl1 (by omega)
                have hsjf21 : ((sj_f <<< (1 : Nat)) + 1#64).toNat = 2 * sj_f.toNat + 1 :=
                  fid11_bv64_shl1_add1 (by omega)
                fvt_to_group_np
                have hksf0 : KeysState (rrf.set sj_f.toNat cr) scrf :=
                  ⟨by simp [hksf.1], hksf.2.1,
                    (fid11_sort_set_rr_ok hksf.1 hbn_le (by omega) hksf.2.2 (fun _ => hcr_ref)).2⟩
                obtain ⟨hok_f0, rrf1, scrf1, hksf1, hmf1⟩ := hkey_store
                  (idx := sj_f <<< (1 : Nat)) k0 hkp hksf0 (by rw [hsjf2]; omega) hm
                refine wp_store_sep ⟨hok_f0, hmf1⟩ fun mf1 hmf1' => ?_
                obtain ⟨hok_f1, rrf2, scrf2, hksf2, hmf2⟩ := hkey_store
                  (idx := (sj_f <<< (1 : Nat)) + 1#64) k1 hkp hksf1 (by rw [hsjf21]; omega) hmf1'
                try fvt_to_group_np
                refine wp_store_sep ⟨hok_f1, hmf2⟩ fun mf2 hmf2' => ?_
                fvt_steps_np
                exact ihs (si + 1#64, ()) mf2 (by dsimp only; rw [hsi1]; omega)
                  ⟨rrf2, scrf2, by rw [hsi1]; omega, by rw [hsi1]; omega, hksf2, hmf2'⟩
              · intro B L rem ⟨sj, ⟨⟩⟩ msj hB hL ⟨rrj, scrj, hsj_lt, hrem, hksj, hmsj⟩
                subst hrem
                c0_hsplit
                · have hge : gap.toNat ≤ sj.toNat := by c0_bound
                  have hpj_nat : (sj - gap).toNat = sj.toNat - gap.toNat := by
                    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hge)]
                  have hpj_lt : (sj - gap).toNat < bn.toNat := by omega
                  have hpj_rr : (sj - gap).toNat < rrj.length := by rw [hksj.1]; omega
                  let pcr := rrj[(sj - gap).toNat]'hpj_rr
                  have hpcr_ref : pcr.toNat ∈ fullArenaClauseRefs s := by
                    have h := hksj.2.2 (sj - gap).toNat hpj_lt
                    rwa [List.getElem?_eq_getElem hpj_rr, Option.getD_some] at h
                  have hwfp := hsw0.2.1.arena.refs_wf pcr.toNat hpcr_ref
                  have hpj2 : ((sj - gap) <<< (1 : Nat)).toNat = 2 * (sj - gap).toNat :=
                    fid11_bv64_shl1 (by have := hrc; have := hsc; have := hbn_le; omega)
                  have hpj21 : (((sj - gap) <<< (1 : Nat)) + 1#64).toNat =
                      2 * (sj - gap).toNat + 1 :=
                    fid11_bv64_shl1_add1 (by have := hrc; have := hsc; have := hbn_le; omega)
                  fvt_to_group_np
                  obtain ⟨pk0, hlpk0⟩ := hkey_load (idx := (sj - gap) <<< (1 : Nat)) hkp hksj
                    (by rw [hpj2]; omega) hmsj
                  obtain ⟨pk1, hlpk1⟩ := hkey_load (idx := ((sj - gap) <<< (1 : Nat)) + 1#64)
                    hkp hksj (by rw [hpj21]; omega) hmsj
                  try fvt_to_group_np
                  refine wp_load_of (by dsimp only [Arg.val]; exact hlpk0) ?_
                  try fvt_to_group_np
                  refine wp_load_of (by dsimp only [Arg.val]; exact hlpk1) ?_
                  have hpcr_ar : (pcr.setWidth 64).toNat < s.core.arena.length := by
                    rw [zext_toNat pcr (by decide)]; omega
                  fvt_to_group_np
                  refine wp_join_group (ts := [i32]) (fun _ m3 => msj = m3) ?_
                    (fun Jdp0 hJdp0 => by
                      c0_hsplit
                      · have hlt : (pk0.setWidth 64).toNat < s.scratch.tarjan_reach.length := by
                          have hc' : (pk0.setWidth 64).toNat <
                              (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat := hc
                          rw [hnlits] at hc'; omega
                        fvt_steps_np; exact hJdp0 _ msj rfl
                      · try fvt_steps_np; exact hJdp0 _ msj rfl)
                  rintro _ ⟨dpk0, ⟨⟩⟩ _ rfl
                  fvt_to_group_np
                  refine wp_join_group (ts := [i32]) (fun _ m4 => msj = m4) ?_
                    (fun Jdp1 hJdp1 => by
                      c0_hsplit
                      · have hlt : (pk1.setWidth 64).toNat < s.scratch.tarjan_reach.length := by
                          have hc' : (pk1.setWidth 64).toNat <
                              (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat := hc
                          rw [hnlits] at hc'; omega
                        fvt_steps_np; exact hJdp1 _ msj rfl
                      · try fvt_steps_np; exact hJdp1 _ msj rfl)
                  rintro _ ⟨dpk1, ⟨⟩⟩ _ rfl
                  refine wp_join_group (ts := []) (fun () mc => msj = mc)
                    (fun _ () mc hmc => by
                      subst hmc
                      refine wp_join_group (ts := []) (fun () mc2 => msj = mc2)
                        (fun _ () mc2 hmc2 => by
                          subst hmc2
                          have hsj_rr : sj.toNat < rrj.length := by rw [hksj.1]; omega
                          have hsj2 : (sj <<< (1 : Nat)).toNat = 2 * sj.toNat :=
                            fid11_bv64_shl1 (by omega)
                          have hsj21 : ((sj <<< (1 : Nat)) + 1#64).toNat = 2 * sj.toNat + 1 :=
                            fid11_bv64_shl1_add1 (by omega)
                          fvt_to_group_np
                          have hksj0 : KeysState (rrj.set sj.toNat pcr) scrj :=
                            ⟨by simp [hksj.1], hksj.2.1,
                              (fid11_sort_set_rr_ok hksj.1 hbn_le (by omega) hksj.2.2
                                (fun _ => hpcr_ref)).2⟩
                          obtain ⟨hok_s0, rrj1, scrj1, hksj1, hms1⟩ := hkey_store
                            (idx := sj <<< (1 : Nat)) pk0 hkp hksj0 (by rw [hsj2]; omega) hm
                          refine wp_store_sep ⟨hok_s0, hms1⟩ fun ms1 hms1' => ?_
                          obtain ⟨hok_s1, rrj2, scrj2, hksj2, hms2⟩ := hkey_store
                            (idx := (sj <<< (1 : Nat)) + 1#64) pk1 hkp hksj1
                            (by rw [hsj21]; omega) hms1'
                          try fvt_to_group_np
                          refine wp_store_sep ⟨hok_s1, hms2⟩ fun ms2 hms2' => ?_
                          fvt_steps_np
                          exact hL (sj - gap).toNat (sj - gap, ()) ms2 (by rw [hpj_nat]; omega)
                            ⟨rrj2, scrj2, hpj_lt, rfl, hksj2, hms2'⟩)
                        (fun Jc2 hJc2 => by
                          c0_hsplit
                          · c0_hsplit
                            · try fvt_to_group_np
                              exact hB (sj, ()) msj ⟨rrj, scrj, hsj_lt, hksj, hmsj⟩
                            · refine wp_join_group (ts := []) (fun () m1 => msj = m1)
                                (fun _ () m1 hm1 => by subst hm1; exact hJc2 () msj rfl)
                                fun J1 hJ1 => by
                                  c0_hsplit
                                  · c0_hsplit
                                    · try fvt_to_group_np
                                      exact hB (sj, ()) msj ⟨rrj, scrj, hsj_lt, hksj, hmsj⟩
                                    · refine wp_join_group (ts := []) (fun () m2 => msj = m2)
                                        (fun _ () m2 hm2 => by subst hm2; exact hJ1 () msj rfl)
                                        fun J2 hJ2 => by
                                          c0_hsplit
                                          · c0_hsplit
                                            · try fvt_to_group_np
                                              exact hB (sj, ()) msj
                                                ⟨rrj, scrj, hsj_lt, hksj, hmsj⟩
                                            · fvt_steps_np <;> first
                                                | exact hB (sj, ()) msj
                                                    ⟨rrj, scrj, hsj_lt, hksj, hmsj⟩
                                                | exact hJ2 () msj rfl
                                          · try fvt_to_group_np
                                            exact hJ2 () msj rfl
                                  · try fvt_to_group_np
                                    exact hJ1 () msj rfl
                          · try fvt_to_group_np
                            exact hJc2 () msj rfl))
                    (fun Jc hJc => by
                      fvt_steps_np
                      all_goals first
                        | exact hB (sj, ()) msj ⟨rrj, scrj, hsj_lt, hksj, hmsj⟩
                        | exact hJc () msj rfl)
                · try fvt_steps_np
                  exact hB (sj, ()) msj ⟨rrj, scrj, hsj_lt, hksj, hmsj⟩
              · intro B L _ hL; fvt_steps_np
                exact hL si.toNat (si, ()) msi ⟨rrs, scrs, hsi_lt, rfl, hkss, hmsi⟩
            · fvt_steps_np
              exact ihg (gap / 3#64, ()) msi (by dsimp only; rw [hgap3]; omega)
                ⟨rrs, scrs, by rw [hgap3]; omega, hkss, hmsi⟩
          · fvt_steps_np
            exact hQ rrg scrg mg hksg.1 hksg.2.1 hksg.2.2 hmg)

end LeanQbe.T.Examples.Kissat.FullFidelityVivFlag

end
