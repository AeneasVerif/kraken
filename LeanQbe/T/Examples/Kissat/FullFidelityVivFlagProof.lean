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
# Kissat Step-11 `S11-8` Upstream `c->vivify` Flag Semantics Proofs (`FullFidelityVivFlagProof`)

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

private theorem fid11_sort_set_rr_ok {rr : List (BitVec 32)} {cap bn idx : Nat}
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

private theorem fid11_bv64_shl1 {x : BitVec 64} (hx : x.toNat < 2 ^ 60) :
    (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm,
    Nat.mod_eq_of_lt (by omega)]

private theorem fid11_bv64_shl1_add1 {x : BitVec 64} (hx : x.toNat < 2 ^ 60) :
    ((x <<< (1 : Nat)) + 1#64).toNat = 2 * x.toNat + 1 := by
  rw [BitVec.toNat_add, fid11_bv64_shl1 hx, show (1#64 : BitVec 64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega)]

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
  · fvt_to_group_np
    refine wp_loop_inv (ts := [i64])
      (fun (gap, ()) mg => ∃ rrg scrg, gap.toNat ≤ bn.toNat ∧ KeysState rrg scrg ∧
        (FullMem c { s with scratch := { s.scratch with red_refs := rrg, scratch_buf := scrg } }
          ⋆ R) mg)
      (fun (gap, ()) _ => gap.toNat)
      (fun Jg hJg => by
        fvt_steps_np
        have hbn2 : (bn >>> (1 : Nat)).toNat = bn.toNat / 2 := by
          rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
        exact hJg (bn >>> (1 : Nat), ()) mbi ⟨rr, scr, by rw [hbn2]; omega, hks, hmbi⟩)
      (fun Jg ⟨gap, ⟨⟩⟩ mg ⟨rrg, scrg, hgap_le, hksg, hmg⟩ ihg => ?_)
    c0_hsplit
    · have hgap_pos : 0 < gap.toNat := by c0_bound
      have hgap_half : (gap >>> (1 : Nat)).toNat = gap.toNat / 2 := by
        rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
      fvt_to_group_np
      refine wp_loop_inv (ts := [i64])
        (fun (si, ()) msi => ∃ rrs scrs, gap.toNat ≤ si.toNat ∧ si.toNat ≤ bn.toNat ∧
          KeysState rrs scrs ∧
          (FullMem c { s with scratch := { s.scratch with red_refs := rrs, scratch_buf := scrs } }
            ⋆ R) msi)
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
            (FullMem c { s with scratch := { s.scratch with red_refs := rrf, scratch_buf := scrf } }
              ⋆ R) msf)
          (fun rem (sj, ()) msj => ∃ rrj scrj, sj.toNat < bn.toNat ∧ rem = sj.toNat ∧
            KeysState rrj scrj ∧
            (FullMem c { s with scratch := { s.scratch with red_refs := rrj, scratch_buf := scrj } }
              ⋆ R) msj) ?_ ?_ ?_
        · rintro _ ⟨sj_f, ⟨⟩⟩ msf ⟨rrf, scrf, hsjf_lt, hksf, hmsf⟩
          have hsjf_rr : sj_f.toNat < rrf.length := by rw [hksf.1]; omega
          have hsjf2 : (sj_f <<< (1 : Nat)).toNat = 2 * sj_f.toNat := fid11_bv64_shl1 (by omega)
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
                      (idx := (sj <<< (1 : Nat)) + 1#64) pk1 hkp hksj1 (by rw [hsj21]; omega)
                      hms1'
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
                                        exact hB (sj, ()) msj ⟨rrj, scrj, hsj_lt, hksj, hmsj⟩
                                      · fvt_steps_np <;> first
                                          | exact hB (sj, ()) msj ⟨rrj, scrj, hsj_lt, hksj, hmsj⟩
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
        exact ihg (gap >>> (1 : Nat), ()) msi (by dsimp only; rw [hgap_half]; omega)
          ⟨rrs, scrs, by rw [hgap_half]; omega, hkss, hmsi⟩
    · fvt_steps_np
      exact hQ rrg scrg mg hksg.1 hksg.2.1 hksg.2.2 hmg

theorem fid11_viv_sort_fid_wp (Γ : Env)
    (hSort2 : ∀ a m Q X, fullVivSort2FidSpec a m Q X →
      Γ "full_viv_sort2_fid" [i64, i64, i64] [] a m Q X) :
    ∀ a m Q X, fullVivSortFidSpec a m Q X →
      Func.wp Γ fid11_viv_sort_fid_body a m Q X := by
  rintro ⟨h, bn, ⟨⟩⟩ m0 Q X hs
  obtain ⟨c, F0, s, R, rfl, hsp0, hbn_le, hok0, hm0, hQ⟩ := fullVivSortFidSpec_elim hs
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
  have hret0 : Q () m0 := hQ s.scratch.red_refs s.scratch.scratch_buf m0 hrr_len hscr_len hok0 hm0
  have hmode_rcap3 : (BitVec.ofNat 64 c.red_cap / 3#64).toNat = c.red_cap / 3 := by
    rw [BitVec.toNat_udiv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      show (3#64 : BitVec 64).toNat = 3 from rfl]
  have hmode_scap2 : (BitVec.ofNat 64 c.scratch_cap >>> (1 : Nat)).toNat = c.scratch_cap / 2 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.shiftRight_eq_div_pow, Nat.pow_one]
  have hmode_rcap2 : (BitVec.ofNat 64 c.red_cap >>> (1 : Nat)).toNat = c.red_cap / 2 := by
    rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.shiftRight_eq_div_pow, Nat.pow_one]
  unfold Func.wp fid11_viv_sort_fid_body
  fvt_steps
  · exact hret0
  · have hle : bn.toNat ≤ c.red_cap / 3 := by
      have hc' : bn.toNat ≤ (BitVec.ofNat 64 c.red_cap / 3#64).toNat := by c0_bound
      rwa [hmode_rcap3] at hc'
    c0_call hSort2
    exact fullVivSort2FidSpec_intro rfl hsp0 hbn_le (Or.inl ⟨rfl, by omega⟩) hok0 hm0 hQ
  · have hle : bn.toNat ≤ c.scratch_cap / 2 := by
      have hc' : bn.toNat ≤ (BitVec.ofNat 64 c.scratch_cap >>> (1 : Nat)).toNat := by c0_bound
      rwa [hmode_scap2] at hc'
    c0_call hSort2
    exact fullVivSort2FidSpec_intro rfl hsp0 hbn_le (Or.inr ⟨rfl, by omega⟩) hok0 hm0 hQ
  · exact hret0
  · have h2bn : 2 * bn.toNat ≤ c.red_cap := by
      have hc' : ¬ (BitVec.ofNat 64 c.red_cap >>> (1 : Nat)).toNat < bn.toNat := by c0_bound
      rw [hmode_rcap2] at hc'; omega
    have hrr_load1 : ∀ {idx : BitVec 64} {rr : List (BitVec 32)} {mk : Mem 64},
        rr.length = c.red_cap → idx.toNat < bn.toNat →
        (FullMem c { s with scratch := { s.scratch with red_refs := rr } } ⋆ R) mk →
        ∃ v, loadVal mk i32 (c.pRedRefs + bn * 4 + idx * 4) = some v := by
      intro idx rr mk hlen hidx hmk
      have haddr : c.pRedRefs + bn * 4 + idx * 4 =
          c.pRedRefs + BitVec.ofNat 64 (4 * (bn.toNat + idx.toNat)) := by
        apply BitVec.eq_of_toNat_eq
        have h4 : (4 : BitVec 64).toNat = 4 := rfl
        simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h4]
        rw [Nat.mul_add]; omega
      have hlt : bn.toNat + idx.toNat < rr.length := by rw [hlen]; omega
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
              array (t := i32) c.pScratchBuf s.scratch.scratch_buf)) ⋆ c.pad ⋆ R)) mk := by
        unfold FullMem FullScratchArrays FullScrDynArrs at hmk; exact sep_cast hmk (by ac_rfl)
      exact loadVal_array (t := i32) (by decide) hlt hF
    have hrr_store1 : ∀ {idx : BitVec 64} (v : BitVec 32) {rr : List (BitVec 32)}
        {mk : Mem 64}, rr.length = c.red_cap →
        (∀ k < bn.toNat, (rr[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) →
        idx.toNat < bn.toNat →
        (FullMem c { s with scratch := { s.scratch with red_refs := rr } } ⋆ R) mk →
        storeOk mk i32 (c.pRedRefs + bn * 4 + idx * 4) ∧
        ∃ rr', rr'.length = c.red_cap ∧
          (∀ k < bn.toNat, (rr'[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
          (FullMem c { s with scratch := { s.scratch with red_refs := rr' } } ⋆ R)
            (storeMem mk i32 (c.pRedRefs + bn * 4 + idx * 4) v) := by
      intro idx v rr mk hlen hok hidx hmk
      have haddr : c.pRedRefs + bn * 4 + idx * 4 =
          c.pRedRefs + BitVec.ofNat 64 (4 * (bn.toNat + idx.toNat)) := by
        apply BitVec.eq_of_toNat_eq
        have h4 : (4 : BitVec 64).toNat = 4 := rfl
        simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, h4]
        rw [Nat.mul_add]; omega
      have hlt : bn.toNat + idx.toNat < rr.length := by rw [hlen]; omega
      have hF : (array (t := i32) c.pRedRefs rr ⋆
          (dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur
            s.core.d_val ⋆ array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆
            FullCoreArrays c s.core ⋆
            (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
             FullScrWksArrs c s.scratch ⋆ FullScrMetaArrs c s.scratch ⋆
             (array (t := i32) c.pDelayed s.scratch.delayed ⋆
              array (t := i32) c.pExtendStk s.scratch.extend_stk ⋆
              array (t := i32) c.pScratchBuf s.scratch.scratch_buf)) ⋆ c.pad ⋆ R)) mk := by
        unfold FullMem FullScratchArrays FullScrDynArrs at hmk; exact sep_cast hmk (by ac_rfl)
      obtain ⟨hso, hst⟩ := store_array (t := i32) v (by decide) hlt hF
      rw [show (i32 : Ty).bytes = 4 from rfl, ← haddr] at hso hst
      refine ⟨hso, rr.set (bn.toNat + idx.toNat) v, by simp [hlen],
        fun k hk => by rw [List.getElem?_set_ne (by omega)]; exact hok k hk, ?_⟩
      unfold FullMem FullScratchArrays FullScrDynArrs; exact sep_cast hst (by ac_rfl)
    refine wp_loop_inv (ts := [i64])
      (fun (bi, ()) mbi => ∃ rr, bi.toNat ≤ bn.toNat ∧ rr.length = c.red_cap ∧
        (∀ k < bn.toNat, (rr[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
        (FullMem c { s with scratch := { s.scratch with red_refs := rr } } ⋆ R) mbi)
      (fun (bi, ()) _ => bn.toNat - bi.toNat)
      (fun Jb hJb => by fvt_steps; exact hJb (0#64, ()) m0 ⟨s.scratch.red_refs, Nat.zero_le _,
        hrr_len, hok0, hm0⟩)
      (fun Jb ⟨bi, ⟨⟩⟩ mbi ⟨rr, hbi_le, hlen_r, hok_r, hmbi⟩ ihb => ?_)
    fvt_steps
    · have hbi_lt : bi.toNat < bn.toNat := by c0_bound
      have hbi1 : (bi + 1#64).toNat = bi.toNat + 1 := by bv_omega
      have hbi_rr : bi.toNat < rr.length := by rw [hlen_r]; omega
      let cr := rr[bi.toNat]'hbi_rr
      have hcr_ref : cr.toNat ∈ fullArenaClauseRefs s := by
        have h := hok_r bi.toNat hbi_lt
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
      fvt_steps
      refine wp_loop_inv (ts := [i32, i32, i32])
        (fun (_k0, _d0, j, ()) mj => mbi = mj ∧ j.toNat ≤ sz.toNat)
        (fun (_, _, j, ()) _ => sz.toNat - j.toNat)
        (fun Jj hJj => by fvt_steps; exact hJj _ mbi ⟨rfl, Nat.zero_le _⟩)
        (fun Jj ⟨k0, d0, j, ⟨⟩⟩ mj ⟨rfl, hj_le⟩ ihj => ?_)
      fvt_steps
      · have hj_lt : j.toNat < sz.toNat := by c0_bound
        have hj1 : (j + 1#32).toNat = j.toNat + 1 := by bv_omega
        have hj_idx : (cr.setWidth 64 + 3#64 + j.setWidth 64).toNat =
            cr.toNat + 3 + j.toNat := by
          rw [BitVec.toNat_add, BitVec.toNat_add, zext_toNat cr (by decide),
            zext_toNat j (by decide), show (3#64).toNat = 3 from rfl,
            Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        have hj_ar : (cr.setWidth 64 + 3#64 + j.setWidth 64).toNat < s.core.arena.length := by
          rw [hj_idx]; omega
        fvt_to_group
        refine wp_join_group (ts := [i32]) (fun _ md => mbi = md) ?_
          (fun Jd hJd => by
            fvt_steps
            · have hl_lt : (s.core.arena[(cr.setWidth 64 + 3#64 + j.setWidth 64).toNat]'hj_ar).toNat
                  < 2 * s.core.cur_vars := by
                have hc' : ((s.core.arena[(cr.setWidth 64 + 3#64 +
                    j.setWidth 64).toNat]'hj_ar).setWidth 64).toNat <
                    (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat := by c0_bound
                rwa [zext_toNat _ (by decide), hnlits] at hc'
              fvt_steps; exact hJd _ mbi rfl
            · exact hJd _ mbi rfl)
        rintro _ ⟨dl, ⟨⟩⟩ _ rfl
        fvt_to_group
        refine wp_join_group (ts := [i32, i32]) (fun _ mu => mbi = mu)
          (fun _ ⟨k0', d0', ⟨⟩⟩ mu hmu => by
            subst hmu; fvt_steps
            exact ihj (k0', d0', j + 1#32, ()) mbi
              (by dsimp only; rw [hj1]; omega) ⟨rfl, by rw [hj1]; omega⟩)
          (fun Ju hJu => by fvt_steps_np <;> exact hJu _ mbi rfl)
      · obtain ⟨hok_k, rr1, hlen1, hok1, hm1⟩ := hrr_store1 (idx := bi) k0 hlen_r hok_r
          hbi_lt hmbi
        refine wp_store_sep ⟨hok_k, hm1⟩ fun mbi1 hmbi1 => ?_
        fvt_steps
        exact ihb (bi + 1#64, ()) mbi1 (by dsimp only; rw [hbi1]; omega)
          ⟨rr1, by rw [hbi1]; omega, hlen1, hok1, hmbi1⟩
    · refine wp_loop_inv (ts := [i64])
        (fun (gap, ()) mg => ∃ rrg, gap.toNat ≤ bn.toNat ∧ rrg.length = c.red_cap ∧
          (∀ k < bn.toNat, (rrg[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
          (FullMem c { s with scratch := { s.scratch with red_refs := rrg } } ⋆ R) mg)
        (fun (gap, ()) _ => gap.toNat)
        (fun Jg hJg => by
          fvt_steps
          have hbn2 : (bn >>> (1 : Nat)).toNat = bn.toNat / 2 := by
            rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
          exact hJg (bn >>> (1 : Nat), ()) mbi ⟨rr, by rw [hbn2]; omega, hlen_r, hok_r, hmbi⟩)
        (fun Jg ⟨gap, ⟨⟩⟩ mg ⟨rrg, hgap_le, hlen_g, hok_g, hmg⟩ ihg => ?_)
      fvt_steps
      · have hgap_pos : 0 < gap.toNat := by c0_bound
        have hgap_half : (gap >>> (1 : Nat)).toNat = gap.toNat / 2 := by
          rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
        refine wp_loop_inv (ts := [i64])
          (fun (si, ()) msi => ∃ rrs, gap.toNat ≤ si.toNat ∧ si.toNat ≤ bn.toNat ∧
            rrs.length = c.red_cap ∧
            (∀ k < bn.toNat, (rrs[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
            (FullMem c { s with scratch := { s.scratch with red_refs := rrs } } ⋆ R) msi)
          (fun (si, ()) _ => bn.toNat - si.toNat)
          (fun Js hJs => by fvt_steps; exact hJs (gap, ()) mg ⟨rrg, Nat.le_refl _, hgap_le,
            hlen_g, hok_g, hmg⟩)
          (fun Js ⟨si, ⟨⟩⟩ msi ⟨rrs, hsi_lo, hsi_le, hlen_s, hok_s, hmsi⟩ ihs => ?_)
        fvt_steps
        · have hsi_lt : si.toNat < bn.toNat := by c0_bound
          have hsi1 : (si + 1#64).toNat = si.toNat + 1 := by bv_omega
          have hsi_rr : si.toNat < rrs.length := by rw [hlen_s]; omega
          let cr := rrs[si.toNat]'hsi_rr
          have hcr_ref : cr.toNat ∈ fullArenaClauseRefs s := by
            have h := hok_s si.toNat hsi_lt
            rwa [List.getElem?_eq_getElem hsi_rr, Option.getD_some] at h
          have hwfc := hsw0.2.1.arena.refs_wf cr.toNat hcr_ref
          obtain ⟨k0, hlk0⟩ := hrr_load1 (idx := si) hlen_s hsi_lt hmsi
          refine wp_load_of (by dsimp only [Arg.val]; exact hlk0) ?_
          have hcr_ar : (cr.setWidth 64).toNat < s.core.arena.length := by
            rw [zext_toNat cr (by decide)]; omega
          c0_hsteps_nogrp
          refine wp_join_group (ts := [i32]) (fun _ m1 => msi = m1) ?_
            (fun Jd0 hJd0 => by
              fvt_steps
              · have hlt : (k0.setWidth 64).toNat < s.scratch.tarjan_reach.length := by
                  have hc' : (k0.setWidth 64).toNat <
                      (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat := by c0_bound
                  rw [hnlits] at hc'; omega
                fvt_steps; exact hJd0 _ msi rfl
              · exact hJd0 _ msi rfl)
          rintro _ ⟨dk0, ⟨⟩⟩ _ rfl
          refine wp_loop_break_group (brkTs := [i64]) (lpTs := [i64])
            (fun (sj_f, ()) msf => ∃ rrf, sj_f.toNat < bn.toNat ∧ rrf.length = c.red_cap ∧
              (∀ k < bn.toNat, (rrf[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
              (FullMem c { s with scratch := { s.scratch with red_refs := rrf } } ⋆ R) msf)
            (fun rem (sj, ()) msj => ∃ rrj, sj.toNat < bn.toNat ∧ rem = sj.toNat ∧
              rrj.length = c.red_cap ∧
              (∀ k < bn.toNat, (rrj[k]?.getD 0#32).toNat ∈ fullArenaClauseRefs s) ∧
              (FullMem c { s with scratch := { s.scratch with red_refs := rrj } } ⋆ R) msj)
            ?_ ?_ ?_
          · rintro _ ⟨sj_f, ⟨⟩⟩ msf ⟨rrf, hsjf_lt, hlen_f, hok_f, hmsf⟩
            have hsjf_rr : sj_f.toNat < rrf.length := by rw [hlen_f]; omega
            c0_hsteps_nogrp
            have hok_f0 := fid11_sort_set_rr_ok (idx := sj_f.toNat) hlen_f hbn_le (by omega) hok_f
              (fun _ => hcr_ref)
            obtain ⟨hok_fk, rrf1, hlen_f1, hok_f1, hmf1⟩ := hrr_store1 (idx := sj_f) k0
              hok_f0.1 hok_f0.2 hsjf_lt hm
            refine wp_store_sep ⟨hok_fk, hmf1⟩ fun mf1 hmf1' => ?_
            fvt_steps
            exact ihs (si + 1#64, ()) mf1 (by dsimp only; rw [hsi1]; omega)
              ⟨rrf1, by rw [hsi1]; omega, by rw [hsi1]; omega, hlen_f1, hok_f1, hmf1'⟩
          · intro B L rem ⟨sj, ⟨⟩⟩ msj hB hL ⟨rrj, hsj_lt, hrem, hlen_j, hok_j, hmsj⟩
            subst hrem
            c0_hsplit
            · have hge : gap.toNat ≤ sj.toNat := by c0_bound
              have hpj_nat : (sj - gap).toNat = sj.toNat - gap.toNat := by
                rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact hge)]
              have hpj_lt : (sj - gap).toNat < bn.toNat := by omega
              have hpj_rr : (sj - gap).toNat < rrj.length := by rw [hlen_j]; omega
              let pcr := rrj[(sj - gap).toNat]'hpj_rr
              have hpcr_ref : pcr.toNat ∈ fullArenaClauseRefs s := by
                have h := hok_j (sj - gap).toNat hpj_lt
                rwa [List.getElem?_eq_getElem hpj_rr, Option.getD_some] at h
              have hwfp := hsw0.2.1.arena.refs_wf pcr.toNat hpcr_ref
              obtain ⟨pk0, hlpk0⟩ := hrr_load1 (idx := sj - gap) hlen_j hpj_lt hmsj
              c0_hsteps_nogrp
              refine wp_load_of (by dsimp only [Arg.val]; exact hlpk0) ?_
              have hpcr_ar : (pcr.setWidth 64).toNat < s.core.arena.length := by
                rw [zext_toNat pcr (by decide)]; omega
              c0_hsteps_nogrp
              refine wp_join_group (ts := [i32]) (fun _ m3 => msj = m3) ?_
                (fun Jdp0 hJdp0 => by
                  c0_hsplit
                  · have hlt : (pk0.setWidth 64).toNat < s.scratch.tarjan_reach.length := by
                      have hc' : (pk0.setWidth 64).toNat <
                          (BitVec.ofNat 64 s.core.cur_vars <<< (1 : Nat)).toNat := hc
                      rw [hnlits] at hc'; omega
                    c0_hsteps!; exact hJdp0 _ msj rfl
                  · c0_hsteps!; exact hJdp0 _ msj rfl)
              rintro _ ⟨dpk0, ⟨⟩⟩ _ rfl
              refine wp_join_group (ts := []) (fun () mc => msj = mc)
                (fun _ () mc hmc => by
                  subst hmc
                  refine wp_join_group (ts := []) (fun () mc2 => msj = mc2)
                    (fun _ () mc2 hmc2 => by
                      subst hmc2
                      have hsj_rr : sj.toNat < rrj.length := by rw [hlen_j]; omega
                      c0_hsteps_nogrp
                      have hok_j0 := fid11_sort_set_rr_ok (idx := sj.toNat) hlen_j hbn_le (by omega)
                        hok_j (fun _ => hpcr_ref)
                      obtain ⟨hok_jk, rrj1, hlen_j1, hok_j1, hmj1⟩ := hrr_store1 (idx := sj) pk0
                        hok_j0.1 hok_j0.2 hsj_lt hm
                      refine wp_store_sep ⟨hok_jk, hmj1⟩ fun mj1 hmj1' => ?_
                      fvt_steps_np
                      exact hL (sj - gap).toNat (sj - gap, ()) mj1 (by rw [hpj_nat]; omega)
                        ⟨rrj1, hpj_lt, rfl, hlen_j1, hok_j1, hmj1'⟩)
                    (fun Jc2 hJc2 => by
                      fvt_steps_np
                      all_goals first
                        | exact hB (sj, ()) msj ⟨rrj, hsj_lt, hlen_j, hok_j, hmsj⟩
                        | exact hJc2 () msj rfl))
                (fun Jc hJc => by
                  fvt_steps_np
                  all_goals first
                    | exact hB (sj, ()) msj ⟨rrj, hsj_lt, hlen_j, hok_j, hmsj⟩
                    | exact hJc () msj rfl)
            · exact hB (sj, ()) msj ⟨rrj, hsj_lt, hlen_j, hok_j, hmsj⟩
          · intro B L _ hL; fvt_steps
            exact hL si.toNat (si, ()) msi ⟨rrs, hsi_lt, rfl, hlen_s, hok_s, hmsi⟩
        · exact ihg (gap >>> (1 : Nat), ()) msi (by dsimp only; rw [hgap_half]; omega)
            ⟨rrs, by rw [hgap_half]; omega, hlen_s, hok_s, hmsi⟩
      · exact hQ rrg s.scratch.scratch_buf mg hlen_g hscr_len hok_g hmg

/-! ## 4. `fid11_viv_clause_m6_wp` (Clear `PH_VIV` After Trying) -/

section ClauseFlagProof

private theorem fid11_sparseInvW_of_prop_canon {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hsp : FullSparseInvW c F0 F_cur s)
    {vals' : List (BitVec 8)} {flags' lvl' rsns' trl' tp' : List (BitVec 32)}
    {te' prop' : Nat} {unass' unfl' : BitVec 64} {wvec' arena' wstk' : List (BitVec 32)}
    {wlen' : Nat} {wu' fuel' ctype' cref' c0' c1' oom' ticks' : BitVec 64}
    {wsort' : List (BitVec 32)} {phases' : List (BitVec 8)} {delayed' : List (BitVec 32)}
    (hlen' : ({ s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                            unassigned := unass', unflushed := unfl', wvec := wvec',
                            arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                            fuel := fuel', confl_type := ctype', confl_ref := cref',
                            confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
      scratch := { s.scratch with search_ticks := ticks', wsort := wsort',
                                  phases := phases', delayed := delayed' } } :
      FullState).LengthsOk c)
    (hw' : FullWitnessInv c F0 F_cur
      { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                    trail_pos := tp', trail_end := te', propagated := prop',
                    unassigned := unass', unflushed := unfl', wvec := wvec', arena := arena',
                    wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                    confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                    confl_lit1 := c1', oom := oom' })
    (hperm : FullArenaPermEq s.core
      { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns', trl := trl',
                    trail_pos := tp', trail_end := te', propagated := prop',
                    unassigned := unass', unflushed := unfl', wvec := wvec', arena := arena',
                    wstk := wstk', wlen := wlen', wusable := wu', fuel := fuel',
                    confl_type := ctype', confl_ref := cref', confl_lit0 := c0',
                    confl_lit1 := c1', oom := oom' }) :
    FullSparseInvW c F0 F_cur
      { s with
        core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                              trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                              unassigned := unass', unflushed := unfl', wvec := wvec',
                              arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                              fuel := fuel', confl_type := ctype', confl_ref := cref',
                              confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
        scratch := { s.scratch with
          search_ticks := ticks', wsort := wsort', phases := phases', delayed := delayed' } } := by
  let s' : FullState :=
    { s with
      core := { s.core with vals := vals', flags := flags', lvl := lvl', rsns := rsns',
                            trl := trl', trail_pos := tp', trail_end := te', propagated := prop',
                            unassigned := unass', unflushed := unfl', wvec := wvec',
                            arena := arena', wstk := wstk', wlen := wlen', wusable := wu',
                            fuel := fuel', confl_type := ctype', confl_ref := cref',
                            confl_lit0 := c0', confl_lit1 := c1', oom := oom' }
      scratch := { s.scratch with search_ticks := ticks', wsort := wsort',
                                  phases := phases', delayed := delayed' } }
  have hnd' : FullArenaVarsNodup s' := fun ref href hng => by
    have href0 : ref ∈ fullArenaClauseRefsCore s.core := hperm.2.1 ▸ href
    obtain ⟨_, hgb, hp⟩ := hperm.2.2 ref href0
    exact (hp.map (· / 2)).nodup_iff.mpr (hsp.2.2.2.1 ref href0 (hgb.symm.trans hng))
  have hrefs : ∀ ref ∈ fullArenaClauseRefs s, ref ∈ fullArenaClauseRefs s' := fun ref hr => by
    change ref ∈ fullArenaClauseRefsCore s'.core; rw [hperm.2.1]; exact hr
  exact FullVivTop.fullSparseInvW_of_prop_state hsp hlen' hw' hnd'
    ⟨⟨rfl, rfl⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ hrefs

private theorem fid11_viv_clause_prop_step (Γ : Env)
    (hPropIgn : ∀ a m Q X, Full.fullPropagateIgnoreDelSpec a m Q X →
      Γ "full_propagate_ignore" [i64, i64] [i64] a m Q X)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hBestImpl : ∀ a m Q X, fullVivBestImpliedM6Spec a m Q X →
      Γ "full_viv_best_implied_m6" [i64, i32] [i32] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s s5 sp s_as : FullState}
    {R : Mem 64 → Prop} {Q : Post [i64]} {X : XPost}
    {B : Cont [i32, .bool, i32]} {J_jn : Cont [.bool, i32]}
    {cref i lit sz : BitVec 32} {tmp5 : List (BitVec 32)} {lits2 : List Nat} {m_as : Mem 64}
    (hQ : ∀ (r : BitVec 64) (s' : FullState) (m' : Mem 64),
      FullSparseInvW c F0 F_cur s' → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      s'.core.arena_len = s.core.arena_len → fullArenaClauseRefs s' = fullArenaClauseRefs s →
      s'.scratch.red_refs = s.scratch.red_refs →
      r = 1#64 ∨ r = 2#64 ∨ r = 20#64 → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m')
    (hB : ∀ (r : Tup Val [i32, .bool, i32]) (m' : Mem 64),
      (match r with
      | (ib, confl, implied, ()) => ∃ sb : FullState,
        FullSparseInvW c F0 F_cur sb ∧
        sb.core.cur_vars = s5.core.cur_vars ∧ sb.core.arena_len = s5.core.arena_len ∧
        sb.core.probing = s5.core.probing ∧ sb.core.tmp = tmp5 ∧
        sb.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        fullArenaClauseRefs sb = fullArenaClauseRefs s ∧
        sb.scratch.red_refs = s.scratch.red_refs ∧
        cref.toNat ∈ fullArenaClauseRefs sb ∧
        fullArenaClauseGarb sb cref.toNat = false ∧
        fullArenaClauseSize sb cref.toNat = sz.toNat ∧
        (fullArenaClauseLits sb cref.toNat).Perm lits2 ∧
        (confl = true → FullConflictOkW F_cur sb) ∧
        (confl = false → implied ≠ 0xFFFFFFFF#32 →
          implied.toNat < 2 * sb.core.cur_vars ∧
          sb.core.vals[implied.toNat]?.getD 0#8 = 1#8) ∧
        (confl = false → implied = 0xFFFFFFFF#32 → ib = sz →
          sb.core.confl_type = 0#64 ∧
          ∀ l ∈ fullArenaClauseLits sb cref.toNat, sb.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
        (FullMem c sb ⋆ R) m') → B r m')
    (hJ_jn : ∀ (xs : Tup Val [.bool, i32]) (m : Mem 64),
      (∃ s_jn : FullState,
        FullSparseInvW c F0 F_cur s_jn ∧
        s_jn.core.cur_vars = s5.core.cur_vars ∧
        s_jn.core.arena_len = s5.core.arena_len ∧
        s_jn.core.probing = s5.core.probing ∧ s_jn.core.tmp = tmp5 ∧
        s_jn.core.fuel.toNat ≤ s.core.fuel.toNat ∧
        fullArenaClauseRefs s_jn = fullArenaClauseRefs s ∧
        s_jn.scratch.red_refs = s.scratch.red_refs ∧
        cref.toNat ∈ fullArenaClauseRefs s_jn ∧
        fullArenaClauseGarb s_jn cref.toNat = false ∧
        fullArenaClauseSize s_jn cref.toNat = sz.toNat ∧
        (fullArenaClauseLits s_jn cref.toNat).Perm lits2 ∧
        s_jn.core.confl_type = 0#64 ∧
        (∀ k < (i + 1#32).toNat,
          s_jn.core.vals[(tmp5[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8) ∧
        (FullMem c s_jn ⋆ R) m) → J_jn xs m)
    (hsp_as : FullSparseInvW c F0 F_cur s_as)
    (hsz_le_mv : sz.toNat ≤ c.max_vars)
    (hcvp : sp.core.cur_vars = s5.core.cur_vars)
    (hcv_as : s_as.core.cur_vars = sp.core.cur_vars)
    (halp : sp.core.arena_len = s5.core.arena_len)
    (hal_as : s_as.core.arena_len = sp.core.arena_len)
    (hprp : sp.core.probing = s5.core.probing)
    (hpr_as : s_as.core.probing = sp.core.probing)
    (hflp : sp.core.fuel.toNat ≤ s.core.fuel.toNat)
    (hfl_as : s_as.core.fuel = sp.core.fuel)
    (hal5 : s5.core.arena_len = s.core.arena_len)
    (hrefsp : fullArenaClauseRefs sp = fullArenaClauseRefs s)
    (hrefs_as : fullArenaClauseRefs s_as = fullArenaClauseRefs sp)
    (hrr_as : s_as.scratch.red_refs = s.scratch.red_refs)
    (hrefp : cref.toNat ∈ fullArenaClauseRefs sp)
    (hng_as : fullArenaClauseGarb s_as cref.toNat = false)
    (hsz_as : fullArenaClauseSize s_as cref.toNat = sz.toNat)
    (hpermp : (fullArenaClauseLits sp cref.toNat).Perm lits2)
    (hlits_as : fullArenaClauseLits s_as cref.toNat = fullArenaClauseLits sp cref.toNat)
    (hct_as : s_as.core.confl_type = 0#64)
    (htmp_as : s_as.core.tmp = tmp5)
    (hlits2_lt : ∀ l ∈ lits2, l < 2 * s5.core.cur_vars)
    (hlits2_mem : ∀ k < sz.toNat, (tmp5[k]?.getD 0#32).toNat ∈ lits2)
    (hi_lt : i.toNat < sz.toNat)
    (hlit_eq : lit = tmp5[i.toNat]?.getD 0#32)
    (hlit_lt : lit.toNat < 2 * sp.core.cur_vars)
    (hfalp : ∀ k < i.toNat, sp.core.vals[(tmp5[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8)
    (hfal_as : ∀ l < 2 * sp.core.cur_vars,
      sp.core.vals[l]?.getD 0#8 = 0xFF#8 → s_as.core.vals[l]?.getD 0#8 = 0xFF#8)
    (hlit_as_ff : s_as.core.vals[lit.toNat]?.getD 0#8 = 0xFF#8)
    (hm_as : (FullMem c s_as ⋆ R) m_as) :
    wp Γ Q X
      (Expr.call (as := [i64, i64]) (bs := [i64]) "full_propagate_ignore"
        (Arg.var c.hdr, Arg.var (cref.setWidth 64), ()) fun p =>
        Expr.let_
          { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
            args := (Arg.var p.fst, Arg.imm 2, ()) }
          fun p_1 =>
        Expr.jnz (Arg.var p_1.fst)
          (Expr.call (as := [i64, i64]) (bs := []) "full_backtrack"
            (Arg.var c.hdr, Arg.imm 0, ()) fun _ =>
            Expr.ret (Arg.imm 2, ()))
          (Expr.let_
            { sig := [i64, i64], code := OpCode.cmp CmpOp.eq i64 Ty.bool rfl,
              args := (Arg.var p.fst, Arg.imm 1, ()) }
            fun p =>
            Expr.jnz (Arg.var p.fst)
              (Expr.jump B (Arg.var i, Arg.imm true, Arg.imm 4294967295, ()))
              (Expr.call (as := [i64, i32]) (bs := [i32]) "full_viv_best_implied_m6"
                (Arg.var c.hdr, Arg.var sz, ()) fun p =>
                Expr.let_
                  { sig := [i32, i32], code := OpCode.cmp CmpOp.ne i32 Ty.bool rfl,
                    args := (Arg.var p.fst, Arg.imm 4294967295, ()) }
                  fun p_1 =>
                Expr.jnz (Arg.var p_1.fst)
                  (Expr.jump B (Arg.var i, Arg.imm false, Arg.var p.fst, ()))
                  (Expr.jump J_jn (Arg.imm false, Arg.imm 4294967295, ())))))
      m_as := by
  have hmx := c.hmaxv; unfold dimacsBound at hmx
  c0_call hPropIgn
  refine ⟨c, F0, F_cur, s_as, R, rfl, hsp_as.1, hsp_as.2.1, hsp_as.2.2.2.2.2, hm_as,
    fun pr vals_p flags_p lvl_p rsns_p trl_p tp_p te_p prop_p unass_p unfl_p
      wvec_p arena_p wstk_p wlen_p wu_p fuel_p ctype_p cref_p c0_p c1_p oom_p
      ticks_p wsort_p phases_p delayed_p m_p hlen_p hw_p htr_p hperm_p hfl_p hpr_disj hpr0 hpr1
      _ _ hm_p => ?_⟩
  let s_p : FullState :=
    { s_as with
      core := { s_as.core with
        vals := vals_p, flags := flags_p, lvl := lvl_p, rsns := rsns_p,
        trl := trl_p, trail_pos := tp_p, trail_end := te_p, propagated := prop_p,
        unassigned := unass_p, unflushed := unfl_p, wvec := wvec_p,
        arena := arena_p, wstk := wstk_p, wlen := wlen_p, wusable := wu_p,
        fuel := fuel_p, confl_type := ctype_p, confl_ref := cref_p,
        confl_lit0 := c0_p, confl_lit1 := c1_p, oom := oom_p }
      scratch := { s_as.scratch with
        search_ticks := ticks_p, wsort := wsort_p, phases := phases_p, delayed := delayed_p } }
  have hsp_p : FullSparseInvW c F0 F_cur s_p :=
    fid11_sparseInvW_of_prop_canon hsp_as hlen_p hw_p hperm_p
  have hrefs_p : fullArenaClauseRefs s_p = fullArenaClauseRefs s_as := hperm_p.2.1
  have hcv_p : s_p.core.cur_vars = s5.core.cur_vars := hcv_as.trans hcvp
  have hal_p : s_p.core.arena_len = s5.core.arena_len := hal_as.trans halp
  have hpr_p : s_p.core.probing = s5.core.probing := hpr_as.trans hprp
  have hfl_p' : s_p.core.fuel.toNat ≤ s.core.fuel.toNat := Nat.le_trans hfl_p (hfl_as ▸ hflp)
  have hrefs_p' : fullArenaClauseRefs s_p = fullArenaClauseRefs s :=
    hrefs_p.trans (hrefs_as.trans hrefsp)
  have hrr_p : s_p.scratch.red_refs = s.scratch.red_refs := hrr_as
  have href_p : cref.toNat ∈ fullArenaClauseRefs s_p := hrefs_p ▸ hrefs_as ▸ hrefp
  have hprops_p := hperm_p.2.2 cref.toNat (by
    change cref.toNat ∈ fullArenaClauseRefs s_as; rw [hrefs_as]; exact hrefp)
  have hng_p : fullArenaClauseGarb s_p cref.toNat = false := hprops_p.2.1.trans hng_as
  have hsz_p : fullArenaClauseSize s_p cref.toNat = sz.toNat := hprops_p.1.trans hsz_as
  have hlits_p : (fullArenaClauseLits s_p cref.toNat).Perm lits2 :=
    hprops_p.2.2.trans (by
      change (fullArenaClauseLits s_as cref.toNat).Perm lits2; rw [hlits_as]; exact hpermp)
  have hm_p' : (FullMem c s_p ⋆ R) m_p := hm_p
  have hcv_p_as : s_p.core.cur_vars = s_as.core.cur_vars := rfl
  have htmp_p : s_p.core.tmp = tmp5 := htmp_as
  have hte_p' : s_as.core.trail_end ≤ s_p.core.trail_end := htr_p.1
  have htrl_p' : ∀ idx < s_as.core.trail_end, s_p.core.trl[idx]? = s_as.core.trl[idx]? := htr_p.2.1
  have hcok_p_fn : pr = 1#64 → FullConflictOkW F_cur s_p := fun h => (hpr1 h).2.2.1
  have hct_p0_fn : pr = 0#64 → s_p.core.confl_type = 0#64 := fun h => (hpr0 h).2.1.trans hct_as
  clear_value s_p; clear hm_p hm_as hprops_p hperm_p htr_p
  fvt_steps
  · have hp_cl_lt : s_p.core.cur_level < 2 ^ 64 := by
      have := hsp_p.2.1.cur_level_le; have := hsp_p.1.core_ok.trail_end_le
      have := hsp_p.1.core_ok.cur_vars_le; omega
    c0_call hBacktrack
    refine ⟨c, s_p, R, rfl, hsp_p.1, hp_cl_lt,
      (by have h0n : BitVec.toNat (0 : BitVec 64) = 0 := rfl; rw [h0n]; intro;
          have := hsp_p.2.1.cur_level_le; have := hsp_p.1.core_ok.trail_end_le
          have := hsp_p.1.core_ok.cur_vars_le; omega),
      hsp_p.2.1.trail_lits_lt, hm_p',
      fun vals_b lvl_b rsns_b trl_b tp_b te_b prop_b cl_b unass_b sc_b m_b
        hlen_b _ _ _ hpres_b hsc_b _ _ hw_b _ hm_b => ?_⟩
    have hsp_b : FullSparseInvW c F0 F_cur _ :=
      FullVivTop.FullSparseInvW.of_backtrack hsp_p (Nat.zero_le _) hlen_b hpres_b
        (hw_b F0 F_cur hsp_p.2.1 (Nat.zero_le _))
    rcases hsc_b with ⟨_, _, _, _, _, _, _, _, _, rfl⟩
    fvt_steps
    exact hQ 2#64 _ m_b hsp_b hfl_p' (hal_p.trans hal5) hrefs_p' hrr_p
      (Or.inr (Or.inl rfl)) (fun h => by cases h) hm_b
  · have hpr_eq1 : pr = 1#64 := by c0_bound
    fvt_steps
    exact hB (i, true, 0xFFFFFFFF#32, ()) _ ⟨s_p, hsp_p, hcv_p, hal_p, hpr_p, htmp_p,
      hfl_p', hrefs_p', hrr_p, href_p, hng_p, hsz_p, hlits_p, fun _ => hcok_p_fn hpr_eq1,
      (fun h => by cases h), (fun h => by cases h), hm_p'⟩
  · have hpr_eq0 : pr = 0#64 := by
      rcases hpr_disj with rfl | rfl | rfl
      · rfl
      · exact absurd rfl (by c0_bound)
      · exact absurd rfl (by c0_bound)
    have hct_p0 : s_p.core.confl_type = 0#64 := hct_p0_fn hpr_eq0
    have htmp_p_lt : ∀ k < sz.toNat, (s_p.core.tmp[k]?.getD 0#32).toNat < 2 * s_p.core.cur_vars :=
      fun k hk => by rw [htmp_p, hcv_p]; exact hlits2_lt _ (hlits2_mem k hk)
    c0_call hBestImpl
    refine ⟨c, F0, F_cur, s_p, R, rfl, hsp_p, hsz_le_mv, htmp_p_lt, hm_p', fun bi hbi => ?_⟩
    fvt_steps
    · have hbi_ne : bi ≠ 0xFFFFFFFF#32 := by c0_bound
      exact hB (i, false, bi, ()) _ ⟨s_p, hsp_p, hcv_p, hal_p, hpr_p, htmp_p, hfl_p', hrefs_p',
        hrr_p, href_p, hng_p, hsz_p, hlits_p, (fun h => by cases h), fun _ _ => hbi hbi_ne,
        fun _ h => absurd h hbi_ne, hm_p'⟩
    · have hi1_nat : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
      have hfal_p1 : ∀ k < (i + 1#32).toNat,
          s_p.core.vals[(tmp5[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8 := by
        intro k hk; rw [hi1_nat] at hk
        rcases (by omega : k < i.toNat ∨ k = i.toNat) with hk' | rfl
        · have hk_lt_sp : (tmp5[k]?.getD 0#32).toNat < 2 * sp.core.cur_vars := by
            rw [hcvp]; exact hlits2_lt _ (hlits2_mem k (by omega))
          exact falsified_preserved_of_trailExt hsp_as.2.1 hsp_p.2.1 hcv_p_as hte_p' htrl_p'
            (hcv_as ▸ hk_lt_sp) (hfal_as _ hk_lt_sp (hfalp k hk'))
        · rw [← hlit_eq]
          exact falsified_preserved_of_trailExt hsp_as.2.1 hsp_p.2.1 hcv_p_as hte_p' htrl_p'
            (hcv_as ▸ hlit_lt) hlit_as_ff
      exact hJ_jn _ _ ⟨s_p, hsp_p, hcv_p, hal_p, hpr_p, htmp_p, hfl_p', hrefs_p', hrr_p,
        href_p, hng_p, hsz_p, hlits_p, hct_p0, hfal_p1, hm_p'⟩

theorem fid11_viv_clause_m6_wp (Γ : Env)
    (hL0Simp : ∀ a m Q X, fullVivL0SimpM6Spec a m Q X →
      Γ "full_viv_l0_simp_m6" [i64, i32, i32] [i64] a m Q X)
    (hSort : ∀ a m Q X, fullVivSortCountsM6Spec a m Q X →
      Γ "full_viv_sort_counts_m6" [i64, i32] [] a m Q X)
    (hReuse : ∀ a m Q X, fullVivReusePrefixM6Spec a m Q X →
      Γ "full_viv_reuse_prefix_m6" [i64, i32, i32] [] a m Q X)
    (hBestImpl : ∀ a m Q X, fullVivBestImpliedM6Spec a m Q X →
      Γ "full_viv_best_implied_m6" [i64, i32] [i32] a m Q X)
    (hAssign : ∀ a m Q X, Full.fullAssignSpec a m Q X →
      Γ "full_assign" [i64, i32, i32] [] a m Q X)
    (hPropIgn : ∀ a m Q X, Full.fullPropagateIgnoreSpec a m Q X →
      Γ "full_propagate_ignore" [i64, i64] [i64] a m Q X)
    (hBacktrack : ∀ a m Q X, Full.fullBacktrackSpec a m Q X →
      Γ "full_backtrack" [i64, i64] [] a m Q X)
    (hFinish : ∀ a m Q X, fullVivFinishM6Spec a m Q X →
      Γ "full_viv_finish_m6" [i64, i32, i32, .bool, i32, .bool] [i64] a m Q X) :
    ∀ a m Q X, fullVivClauseM6Spec a m Q X → Func.wp Γ fid11_viv_clause_m6_body a m Q X := by
  rintro ⟨h, cref, ⟨⟩⟩ m0 Q X ⟨c, F0, F_cur, s, R, rfl, hsp0, href0, hm0, hQ⟩
  have hmx := c.hmaxv; have har_cap := c.harena; unfold dimacsBound at hmx har_cap
  have hwf0 := hsp0.2.1.arena.refs_wf cref.toNat href0
  have hcl0 := hsp0.1.core_ok
  have hcr0_nat : (cref.setWidth 64).toNat = cref.toNat := bv32_setWidth64_toNat cref
  have hcr0_lt0 : cref.toNat < s.core.arena.length := by
    have := hcl0.arena_len_arr; have := hcl0.arena_len_le; omega
  have hcr0_bv0 : (cref.setWidth 64).toNat < s.core.arena.length := by omega
  have hcr2_nat : (cref.setWidth 64 + 2#64).toNat = cref.toNat + 2 := by bv_omega
  have hcr2_lt0 : cref.toNat + 2 < s.core.arena.length := by
    have := hcl0.arena_len_arr; have := hcl0.arena_len_le; omega
  have hcr2_bv0 : (cref.setWidth 64 + 2#64).toNat < s.core.arena.length := by omega
  unfold Func.wp fid11_viv_clause_m6_body
  fvt_steps
  · exact hQ 1#64 s m0 hsp0 (Nat.le_refl _) rfl rfl rfl (Or.inl rfl) (fun h => by cases h) hm0
  · exact hQ 1#64 s m0 hsp0 (Nat.le_refl _) rfl rfl rfl (Or.inl rfl) (fun h => by cases h) hm0
  · exact hQ 1#64 s m0 hsp0 (Nat.le_refl _) rfl rfl rfl (Or.inl rfl) (fun h => by cases h) hm0
  · have hgb_eq : (s.core.arena[(cref.setWidth 64).toNat]'hcr0_bv0 &&& 0x00080000#32) = 0#32 := by
      c0_bound
    have hng0 : fullArenaClauseGarb s cref.toNat = false := by
      unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
      have hg : s.core.arena[cref.toNat]? =
          some (s.core.arena[(cref.setWidth 64).toNat]'hcr0_bv0) := by
        rw [← hcr0_nat, List.getElem?_eq_getElem hcr0_bv0]
      rw [hg, Option.getD_some, hgb_eq]; rfl
    let sz0 := s.core.arena[(cref.setWidth 64 + 2#64).toNat]'hcr2_bv0
    have hsz0_eq : sz0 = s.core.arena[cref.toNat + 2]'hcr2_lt0 :=
      Option.some.inj (by
        rw [← List.getElem?_eq_getElem hcr2_bv0, hcr2_nat, List.getElem?_eq_getElem hcr2_lt0])
    have hsz0_nat : sz0.toNat = fullArenaClauseSize s cref.toNat := by
      rw [hsz0_eq]; unfold fullArenaClauseSize fullArenaClauseSizeCore
      rw [List.getElem?_eq_getElem hcr2_lt0, Option.getD_some]
    c0_call hL0Simp
    refine ⟨c, F0, F_cur, s, R, rfl, hsp0, href0, hng0, hsz0_nat, hm0,
      fun l0r s1 m1 hsp1 hfl1_eq hal1 hrefs1 hrr1 hl0r h20_1 h0_1 hm1 => ?_⟩
    have hfl1 : s1.core.fuel.toNat ≤ s.core.fuel.toNat := by rw [hfl1_eq]; exact Nat.le_refl _
    by_cases hl0 : l0r ≠ 0#64
    · rcases hl0r with rfl | rfl | rfl | rfl
      · exact absurd rfl hl0
      · fvt_steps
        exact hQ 1#64 s1 m1 hsp1 hfl1 hal1 hrefs1 hrr1 (Or.inl rfl) (fun h => by cases h) hm1
      · fvt_steps
        exact hQ 2#64 s1 m1 hsp1 hfl1 hal1 hrefs1 hrr1 (Or.inr (Or.inl rfl))
          (fun h => by cases h) hm1
      · fvt_steps
        exact hQ 20#64 s1 m1 hsp1 hfl1 hal1 hrefs1 hrr1 (Or.inr (Or.inr rfl))
          (fun _ => h20_1 rfl) hm1
    obtain rfl : l0r = 0#64 := Classical.not_not.mp hl0
    fvt_steps
    · contradiction
    obtain ⟨href1, hng1⟩ := h0_1 rfl
    have hwf1 := hsp1.2.1.arena.refs_wf cref.toNat href1
    have hcl1 := hsp1.1.core_ok
    have hcr2_lt1 : cref.toNat + 2 < s1.core.arena.length := by
      have := hcl1.arena_len_arr; have := hcl1.arena_len_le; omega
    have hcr2_bv1 : (cref.setWidth 64 + 2#64).toNat < s1.core.arena.length := by omega
    fvt_steps
    · exact hQ 1#64 s1 m1 hsp1 hfl1 hal1 hrefs1 hrr1 (Or.inl rfl) (fun h => by cases h) hm1
    · exact hQ 1#64 s1 m1 hsp1 hfl1 hal1 hrefs1 hrr1 (Or.inl rfl) (fun h => by cases h) hm1
    let sz := s1.core.arena[(cref.setWidth 64 + 2#64).toNat]'hcr2_bv1
    have hsz_eq : sz = s1.core.arena[cref.toNat + 2]'hcr2_lt1 :=
      Option.some.inj (by
        rw [← List.getElem?_eq_getElem hcr2_bv1, hcr2_nat, List.getElem?_eq_getElem hcr2_lt1])
    have hsz_nat : sz.toNat = fullArenaClauseSize s1 cref.toNat := by
      rw [hsz_eq]; unfold fullArenaClauseSize fullArenaClauseSizeCore
      rw [List.getElem?_eq_getElem hcr2_lt1, Option.getD_some]
    have hsz_le_cv : sz.toNat ≤ s1.core.cur_vars := by
      have hcv_lt : s1.core.cur_vars < 2 ^ 64 := by have := hcl1.cur_vars_le; omega
      have hc0 : ¬ (BitVec.ofNat 64 s1.core.cur_vars).toNat < (sz.setWidth 64).toNat := by
        c0_bound
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv_lt, bv32_setWidth64_toNat] at hc0
      omega
    have hsz_le_mv : sz.toNat ≤ c.max_vars := by have := hcl1.cur_vars_le; omega
    let s2 : FullState := s1
    have hsp2 : FullSparseInvW c F0 F_cur s2 := hsp1
    have hrefs2 : fullArenaClauseRefs s2 = fullArenaClauseRefs s1 := rfl
    have href2 : cref.toNat ∈ fullArenaClauseRefs s2 := href1
    have hng2 : fullArenaClauseGarb s2 cref.toNat = false := hng1
    have hsz2 : fullArenaClauseSize s2 cref.toNat = sz.toNat := hsz_nat.symm
    have har2_len : s2.core.arena.length = c.arena_cap := hsp2.1.core_ok.arena_len_arr
    have htmp2_len : s2.core.tmp.length = c.max_vars := hsp2.1.core_ok.tmp_len_arr
    have hbd2 : cref.toNat + 3 + sz.toNat ≤ s2.core.arena.length := by
      have := hwf1.2.2.1; have := hwf1.2.2.2.1; have := hcl1.arena_len_le
      rw [hsz_nat]
      change cref.toNat + 3 + fullArenaClauseSizeCore s1.core cref.toNat ≤ s2.core.arena.length
      omega
    clear hL0Simp hwf0 hcl0 hcr0_lt0 hgb_eq hfl1_eq h20_1 h0_1
    fvt_steps
    refine wp_loop_inv (ts := [i32])
      (fun (i, ()) mc => ∃ tmpc : List (BitVec 32),
        i.toNat ≤ sz.toNat ∧ tmpc.length = c.max_vars ∧
        (∀ k < i.toNat, tmpc[k]? = s2.core.arena[cref.toNat + 3 + k]?) ∧
        (FullMem c { s2 with core := { s2.core with tmp := tmpc } } ⋆ R) mc)
      (fun (i, ()) _ => sz.toNat - i.toNat)
      (fun Jc hJc => by
        fvt_steps
        exact hJc (0#32, ()) _ ⟨s2.core.tmp, Nat.zero_le _, htmp2_len,
          fun _ hk => by simp at hk, hm1⟩)
      (fun Jc ⟨i, ⟨⟩⟩ mc ⟨tmpc, hi_le, htc_len, hcp, hmc⟩ ihc => ?_)
    fvt_steps
    · have hi_lt : i.toNat < sz.toNat := by c0_bound
      have hidx_nat : (cref.setWidth 64 + 3 + i.setWidth 64).toNat =
          cref.toNat + 3 + i.toNat := by bv_omega
      have hi64_nat : (i.setWidth 64).toNat = i.toNat := bv32_setWidth64_toNat i
      have hi_lt_ar :
          (cref.setWidth 64 + 3 + i.setWidth 64).toNat < s2.core.arena.length := by omega
      have hi_lt_tmp : i.toNat < tmpc.length := by omega
      have hi1_nat : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
      fvt_steps
      let tmpc' := tmpc.set i.toNat (s2.core.arena[cref.toNat + 3 + i.toNat]'(by omega))
      have har_eq :
          s2.core.arena[(cref.setWidth 64 + 3 + i.setWidth 64).toNat]'hi_lt_ar =
            s2.core.arena[cref.toNat + 3 + i.toNat]'(by omega) :=
        Option.some.inj (by
          rw [← List.getElem?_eq_getElem hi_lt_ar, hidx_nat, List.getElem?_eq_getElem (by omega)])
      refine ihc (i + 1#32, ()) _ (by dsimp only; omega)
        ⟨tmpc', by omega, by simp [tmpc', htc_len], fun k hk => ?_, ?_⟩
      · rcases (by omega : k < i.toNat ∨ k = i.toNat) with hk' | rfl
        · dsimp only [tmpc']; rw [List.getElem?_set_ne (by omega)]; exact hcp k hk'
        · dsimp only [tmpc']
          rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem (by omega)]
      · simpa only [tmpc', hi64_nat, har_eq] using hm
    · have hi_eq : i.toNat = sz.toNat := by dsimp only [sz] at hi_le ⊢; c0_bound
      rw [hi_eq] at hcp
      have htmpc_lits_lt : ∀ k < sz.toNat, (tmpc[k]?.getD 0#32).toNat < 2 * c.max_vars := by
        intro k hk
        have hmem : (tmpc[k]?.getD 0#32).toNat ∈ fullArenaClauseLits s2 cref.toNat := by
          have := (vivTmp_mem_of_perm (by omega)
            (vivCopy_perm_lits (by omega) hbd2 hcp
              (List.Perm.refl (tmpc.take sz.toNat)) (by omega))).1 k hk
          simpa [fullArenaClauseLits, fullArenaClauseLitsCore, hsz2] using this
        have := hsp2.2.1.arena.lits_lt cref.toNat href2 hng2 _ hmem
        have := hsp2.1.core_ok.cur_vars_le; omega
      c0_call hSort
      refine ⟨c, { s2 with core := { s2.core with tmp := tmpc } }, R,
        rfl, ⟨{ hsp2.1.core_ok with tmp_len_arr := htc_len }, hsp2.1.scratch_ok⟩,
        hsz_le_mv, htmpc_lits_lt, hmc, fun tmp4 m4 htmp4_len hperm4 _ hm4 => ?_⟩
      have hperm_lits4 : ((tmp4.take sz.toNat).map BitVec.toNat).Perm
          (fullArenaClauseLits s2 cref.toNat) := by
        have := vivCopy_perm_lits (by omega) hbd2 hcp hperm4 (by omega)
        simpa [fullArenaClauseLits, fullArenaClauseLitsCore, hsz2] using this
      let s4 : FullState := { s2 with core := { s2.core with tmp := tmp4 } }
      have hsp4 : FullSparseInvW c F0 F_cur s4 :=
        FullVivTop.FullSparseInvW.with_tmp hsp2 htmp4_len
      have htmp4_lt_cv : ∀ k < sz.toNat, (tmp4[k]?.getD 0#32).toNat < 2 * s4.core.cur_vars := by
        intro k hk
        have hmem := (vivTmp_mem_of_perm (by omega) hperm_lits4).1 k hk
        exact hsp2.2.1.arena.lits_lt cref.toNat href2 hng2 _ hmem
      fvt_steps
      c0_call hReuse
      refine ⟨c, F0, F_cur, s4, R, rfl, hsp4, hsz_le_mv, htmp4_lt_cv, hm4,
        fun s4r m4r hsp4r hcv4r har4r hal4r hpr4r hfl4r htmp4r hrr4r hm4r => ?_⟩
      let tmp5 := s4r.core.tmp
      let lits2 := fullArenaClauseLits s2 cref.toNat
      have hperm_lits5 : ((tmp5.take sz.toNat).map BitVec.toNat).Perm lits2 := by
        dsimp only [tmp5, lits2]; rw [htmp4r]; exact hperm_lits4
      obtain ⟨htmp5_mem, hlits5_inv⟩ := vivTmp_mem_of_perm
        (by rw [show tmp5.length = c.max_vars from hsp4r.1.core_ok.tmp_len_arr]; omega)
        hperm_lits5
      fvt_to_group
      let s5 : FullState :=
        { s4r with core := { s4r.core with confl_type := 0#64, confl_ref := 0xFFFFFFFF#64 } }
      have hsp5 : FullSparseInvW c F0 F_cur s5 :=
        FullVivTop.FullSparseInvW.with_confl hsp4r 0#64 0xFFFFFFFF#64
      have hfl5 : s5.core.fuel.toNat ≤ s.core.fuel.toNat := by
        change s4r.core.fuel.toNat ≤ s.core.fuel.toNat; rw [hfl4r]; exact hfl1
      have hal5 : s5.core.arena_len = s.core.arena_len := hal4r.trans hal1
      have hrefs_eq4r : fullArenaClauseRefs s5 = fullArenaClauseRefs s2 := by
        unfold fullArenaClauseRefs fullArenaClauseRefsCore; change _ = _; rw [har4r, hal4r]
      have hrefs5 : fullArenaClauseRefs s5 = fullArenaClauseRefs s :=
        hrefs_eq4r.trans (hrefs2.trans hrefs1)
      have hrr5 : s5.scratch.red_refs = s.scratch.red_refs := hrr4r.trans hrr1
      have href5 : cref.toNat ∈ fullArenaClauseRefs s5 := hrefs_eq4r ▸ href2
      have hng5 : fullArenaClauseGarb s5 cref.toNat = false := by
        unfold fullArenaClauseGarb fullArenaClauseGarbCore fullArenaHdrCore
        change (s4r.core.arena[cref.toNat]?.getD 0#32 &&& 0x00080000#32 != 0#32) = false
        rw [har4r]; exact hng2
      have hsz5 : fullArenaClauseSize s5 cref.toNat = sz.toNat := by
        unfold fullArenaClauseSize fullArenaClauseSizeCore
        change (s4r.core.arena[cref.toNat + 2]?.getD 0#32).toNat = sz.toNat
        rw [har4r]; exact hsz2
      have hperm5 : (fullArenaClauseLits s5 cref.toNat).Perm lits2 := by
        have heq : fullArenaClauseLits s5 cref.toNat = lits2 := by
          unfold fullArenaClauseLits fullArenaClauseLitsCore fullArenaClauseSizeCore lits2
          change ((s4r.core.arena.drop (cref.toNat + 3)).take
            (s4r.core.arena[cref.toNat + 2]?.getD 0#32).toNat).map BitVec.toNat = _
          rw [har4r]; rfl
        rw [heq]
      have hlits2_lt : ∀ l ∈ lits2, l < 2 * s5.core.cur_vars := fun l hl => by
        change l < 2 * s4r.core.cur_vars; rw [hcv4r]
        exact hsp2.2.1.arena.lits_lt cref.toNat href2 hng2 l hl
      have hlits2_mem : ∀ k < sz.toNat, (tmp5[k]?.getD 0#32).toNat ∈ lits2 := htmp5_mem
      have hlits2_inv : ∀ l ∈ lits2, ∃ k < sz.toNat, (tmp5[k]?.getD 0#32).toNat = l := hlits5_inv
      have hct5 : s5.core.confl_type = 0#64 := rfl
      have htmp5 : s5.core.tmp = tmp5 := rfl
      have htmp5_len : tmp5.length = c.max_vars := hsp4r.1.core_ok.tmp_len_arr
      have hm5 : (FullMem c s5 ⋆ R) m := hm
      clear_value s5 s4 s2 tmp5 lits2
      clear hSort hReuse har_cap hm hwf1 hperm4 hperm_lits4 htmp5_mem hlits5_inv hsp4 hsp2
        s4 hrefs2 href2 hng2 hsz2 har2_len htmp2_len hbd2 htmpc_lits_lt hsp1
        hfl1 hal1 hrefs1 hrr1 href1 hng1 hcl1 hsz_nat hsz_le_cv hsp0 href0
        hng0 hm0 hsp4r hcv4r har4r hal4r hpr4r hfl4r htmp4r hrr4r hrefs_eq4r htmp4_lt_cv
      try clear hi_eq ihc hmc hcp htc_len hi_le tmpc mc Jc i s2 s4r
      refine wp_loop_break_group (brkTs := [i32, .bool, i32]) (lpTs := [i32])
        (fun (i, confl, implied, ()) mb => ∃ sb : FullState,
          FullSparseInvW c F0 F_cur sb ∧
          sb.core.cur_vars = s5.core.cur_vars ∧ sb.core.arena_len = s5.core.arena_len ∧
          sb.core.probing = s5.core.probing ∧ sb.core.tmp = tmp5 ∧
          sb.core.fuel.toNat ≤ s.core.fuel.toNat ∧
          fullArenaClauseRefs sb = fullArenaClauseRefs s ∧
          sb.scratch.red_refs = s.scratch.red_refs ∧
          cref.toNat ∈ fullArenaClauseRefs sb ∧
          fullArenaClauseGarb sb cref.toNat = false ∧
          fullArenaClauseSize sb cref.toNat = sz.toNat ∧
          (fullArenaClauseLits sb cref.toNat).Perm lits2 ∧
          (confl = true → FullConflictOkW F_cur sb) ∧
          (confl = false → implied ≠ 0xFFFFFFFF#32 →
            implied.toNat < 2 * sb.core.cur_vars ∧
            sb.core.vals[implied.toNat]?.getD 0#8 = 1#8) ∧
          (confl = false → implied = 0xFFFFFFFF#32 → i = sz →
            sb.core.confl_type = 0#64 ∧
            ∀ l ∈ fullArenaClauseLits sb cref.toNat, sb.core.vals[l]?.getD 0#8 = 0xFF#8) ∧
          (FullMem c sb ⋆ R) mb)
        (fun rem (i, ()) mp => ∃ sp : FullState,
          i.toNat ≤ sz.toNat ∧ rem = sz.toNat - i.toNat ∧
          FullSparseInvW c F0 F_cur sp ∧
          sp.core.cur_vars = s5.core.cur_vars ∧ sp.core.arena_len = s5.core.arena_len ∧
          sp.core.probing = s5.core.probing ∧ sp.core.tmp = tmp5 ∧
          sp.core.fuel.toNat ≤ s.core.fuel.toNat ∧
          fullArenaClauseRefs sp = fullArenaClauseRefs s ∧
          sp.scratch.red_refs = s.scratch.red_refs ∧
          cref.toNat ∈ fullArenaClauseRefs sp ∧
          fullArenaClauseGarb sp cref.toNat = false ∧
          fullArenaClauseSize sp cref.toNat = sz.toNat ∧
          (fullArenaClauseLits sp cref.toNat).Perm lits2 ∧
          sp.core.confl_type = 0#64 ∧
          (∀ k < i.toNat, sp.core.vals[(tmp5[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8) ∧
          (FullMem c sp ⋆ R) mp)
        ?_ ?_ ?_
      · rintro _ ⟨i_b, confl_b, impl_b, ⟨⟩⟩ mb
          ⟨sb, hspb, _, halb, _, htmpb, hflb, hrefsb, hrrb, hrefb, hngb, hszb, hpermb,
           hcokb, himplb, hfalb, hmb⟩
        fvt_steps
        c0_call hFinish
        refine ⟨c, F0, F_cur, sb, R, rfl, hspb, hsz_le_mv, hrefb, hngb, hszb,
          (by rw [htmpb]; exact hperm_lits5.trans hpermb.symm),
          hcokb, himplb,
          fun hc hi hall => hfalb hc hi (by
            revert hall; cases Decidable.em (i_b = sz) <;> simp [*]),
          hmb, fun r_f s_f m_f hspf hflf half hrefsf hrrf hrf h20f hm_f => ?_⟩
        clear hFinish hBestImpl hAssign hPropIgn hBacktrack hsz_le_mv hspb hcokb himplb hfalb hmb
        have href_f : cref.toNat ∈ fullArenaClauseRefs s_f := hrefsf ▸ hrefb
        have hwf_f := hspf.2.1.arena.refs_wf cref.toNat href_f
        have hcr_f_lt : cref.toNat < s_f.core.arena.length := by
          have := hspf.1.core_ok.arena_len_arr; have := hspf.1.core_ok.arena_len_le; omega
        have hcr_f_bv : (cref.setWidth 64).toNat < s_f.core.arena.length := by omega
        fvt_steps
        · let hdr_f := s_f.core.arena[cref.toNat]'hcr_f_lt
          have hhdr_f : fullArenaHdr s_f cref.toNat = hdr_f := by
            unfold fullArenaHdr fullArenaHdrCore
            rw [List.getElem?_eq_getElem hcr_f_lt, Option.getD_some]
          let hdr_v := hdr_f &&& ~~~0x00100000#32
          obtain ⟨hsp_v, hrefs_v, _⟩ :=
            fullSparseInvW_set_hdr_non_gs hspf href_f hdr_v
              s_f.core.num_irred s_f.core.num_redundant
              (by rw [hhdr_f]; exact bv32_clr_viv_garb hdr_f)
              (by rw [hhdr_f]; exact bv32_clr_viv_shrk hdr_f)
          have hm_v : (FullMem c
              { s_f with core := { s_f.core with arena := s_f.core.arena.set cref.toNat hdr_v } }
              ⋆ R) m := by
            dsimp only [hdr_v, hdr_f]
            rw [← show (1048576#32 : BitVec 32) = 0x00100000#32 from rfl,
              ← show (1048576 : BitVec 32) = 1048576#32 from rfl]
            simpa only [hcr0_nat] using hm
          exact hQ r_f _ m hsp_v (Nat.le_trans hflf hflb)
            (half.trans (halb.trans hal5)) (hrefs_v.trans (hrefsf.trans hrefsb))
            (hrrf.trans hrrb) hrf h20f hm_v
        · exact hQ r_f s_f m_f hspf (Nat.le_trans hflf hflb) (half.trans (halb.trans hal5))
            (hrefsf.trans hrefsb) (hrrf.trans hrrb) hrf h20f hm_f
        · exact hQ r_f s_f m_f hspf (Nat.le_trans hflf hflb) (half.trans (halb.trans hal5))
            (hrefsf.trans hrefsb) (hrrf.trans hrrb) hrf h20f hm_f
        · exact hQ r_f s_f m_f hspf (Nat.le_trans hflf hflb) (half.trans (halb.trans hal5))
            (hrefsf.trans hrefsb) (hrrf.trans hrrb) hrf h20f hm_f
      · intro B L rem ⟨i, ⟨⟩⟩ mp hB hL
          ⟨sp, hi_le, hrem, hspp, hcvp, halp, hprp, htmpp, hflp, hrefsp, hrrp, hrefp, hngp, hszp,
           hpermp, hct0, hfalp, hmp⟩
        clear hFinish
        fvt_steps
        · have hi_lt : i.toNat < sz.toNat := by c0_bound
          have hi_ne_sz : i ≠ sz := fun heq => by rw [heq] at hi_lt; exact Nat.lt_irrefl _ hi_lt
          have hsp_len := hspp.1.core_ok
          have hi_lt_tmp : i.toNat < sp.core.tmp.length := by rw [hsp_len.tmp_len_arr]; omega
          have hlit_lt_cv : (tmp5[i.toNat]?.getD 0#32).toNat < 2 * sp.core.cur_vars := by
            rw [hcvp]; exact hlits2_lt _ (hlits2_mem i.toNat hi_lt)
          have hlit_lt_vals : (tmp5[i.toNat]?.getD 0#32).toNat < sp.core.vals.length := by
            rw [hsp_len.vals_len]; have := hsp_len.cur_vars_le; omega
          have hi64_nat : (i.setWidth 64).toNat = i.toNat := bv32_setWidth64_toNat i
          have hi_lt_tmp64 : (i.setWidth 64).toNat < sp.core.tmp.length := by
            rw [hi64_nat]; exact hi_lt_tmp
          have htmp_i_eq : sp.core.tmp[(i.setWidth 64).toNat]'hi_lt_tmp64 =
              tmp5[i.toNat]?.getD 0#32 :=
            Option.some.inj (by
              rw [← List.getElem?_eq_getElem hi_lt_tmp64, htmpp, hi64_nat,
                List.getElem?_eq_getElem (by omega), Option.getD_some])
          have htmp_i_lt' : (sp.core.tmp[(i.setWidth 64).toNat].setWidth 64).toNat <
              sp.core.vals.length := by
            rw [bv32_setWidth64_toNat, htmp_i_eq]; exact hlit_lt_vals
          let lit := sp.core.tmp[i.toNat]'hi_lt_tmp
          have hlit_eq : lit = tmp5[i.toNat]?.getD 0#32 :=
            Option.some.inj (by
              dsimp only [lit]
              rw [← List.getElem?_eq_getElem hi_lt_tmp, htmpp,
                List.getElem?_eq_getElem (by omega), Option.getD_some])
          have hlit_i64 : sp.core.tmp[(i.setWidth 64).toNat]'hi_lt_tmp64 = lit := by
            rw [htmp_i_eq, hlit_eq]
          have hlit_lt : lit.toNat < 2 * sp.core.cur_vars := hlit_eq ▸ hlit_lt_cv
          have hlit_lt_vals' : lit.toNat < sp.core.vals.length := hlit_eq ▸ hlit_lt_vals
          fvt_to_group
          · have htmp_sp_lt : ∀ k < sz.toNat,
                (sp.core.tmp[k]?.getD 0#32).toNat < 2 * sp.core.cur_vars := fun k hk => by
              rw [htmpp, hcvp]; exact hlits2_lt _ (hlits2_mem k hk)
            c0_call hBestImpl
            refine ⟨c, F0, F_cur, sp, R, rfl, hspp, hsz_le_mv, htmp_sp_lt, hmp, fun bi hbi => ?_⟩
            fvt_steps
            exact hB (i, false, bi, ()) mp ⟨sp, hspp, hcvp, halp, hprp, htmpp, hflp, hrefsp, hrrp,
              hrefp, hngp, hszp, hpermp, (fun h => by cases h), fun _ hne => hbi hne,
              fun _ _ heq => absurd heq hi_ne_sz, hmp⟩
          · refine wp_join_group (ts := [.bool, i32])
              (fun (_, _, ()) m_jn => ∃ s_jn : FullState,
                FullSparseInvW c F0 F_cur s_jn ∧
                s_jn.core.cur_vars = s5.core.cur_vars ∧ s_jn.core.arena_len = s5.core.arena_len ∧
                s_jn.core.probing = s5.core.probing ∧ s_jn.core.tmp = tmp5 ∧
                s_jn.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                fullArenaClauseRefs s_jn = fullArenaClauseRefs s ∧
                s_jn.scratch.red_refs = s.scratch.red_refs ∧
                cref.toNat ∈ fullArenaClauseRefs s_jn ∧
                fullArenaClauseGarb s_jn cref.toNat = false ∧
                fullArenaClauseSize s_jn cref.toNat = sz.toNat ∧
                (fullArenaClauseLits s_jn cref.toNat).Perm lits2 ∧
                s_jn.core.confl_type = 0#64 ∧
                (∀ k < (i + 1#32).toNat,
                  s_jn.core.vals[(tmp5[k]?.getD 0#32).toNat]?.getD 0#8 = 0xFF#8) ∧
                (FullMem c s_jn ⋆ R) m_jn) ?_ ?_
            · rintro _ ⟨_, _, ⟨⟩⟩ m_jn ⟨s_jn, hsp_jn, hcv_jn, hal_jn, hpr_jn, htmp_jn, hfl_jn,
                hrefs_jn, hrr_jn, href_jn, hng_jn, hsz_jn, hperm_jn, hct_jn, hfal_jn, hm_jn⟩
              have hi1_nat : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
              fvt_steps
              exact hL (sz.toNat - (i + 1#32).toNat) (i + 1#32, ()) _
                (by (try dsimp only); (try rw [hi1_nat]); omega)
                ⟨s_jn, by omega, rfl, hsp_jn, hcv_jn, hal_jn, hpr_jn, htmp_jn, hfl_jn,
                 hrefs_jn, hrr_jn, href_jn, hng_jn, hsz_jn, hperm_jn, hct_jn, hfal_jn, hm_jn⟩
            · intro J_jn hJ_jn
              fvt_steps
              · exfalso
                have hlv0 : sp.core.vals[lit.toNat]?.getD 0#8 = 0#8 := by
                  rw [List.getElem?_eq_getElem hlit_lt_vals', Option.getD_some]
                  exact (bv8_sext32_eq0_iff _).mp (by first | assumption | c0_bound)
                have hte_lt := hspp.2.1.trail_end_lt_of_unassigned hlit_lt hlv0
                have hnlvl_le : sp.core.cur_level + 1 ≤ c.max_vars := by
                  have := hspp.2.1.cur_level_le; have := hsp_len.cur_vars_le; omega
                have hc0 : c.max_vars % 2 ^ 64 <
                    (sp.core.cur_level + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64 := by assumption
                have h1n : BitVec.toNat (1 : BitVec 64) = 1 := rfl
                rw [h1n] at hc0; omega
              · have hlv0 : sp.core.vals[lit.toNat]?.getD 0#8 = 0#8 := by
                  rw [List.getElem?_eq_getElem hlit_lt_vals', Option.getD_some]
                  exact (bv8_sext32_eq0_iff _).mp (by first | assumption | c0_bound)
                have hte_lt := hspp.2.1.trail_end_lt_of_unassigned hlit_lt hlv0
                have hnlvl_le : sp.core.cur_level + 1 ≤ c.max_vars := by
                  have := hspp.2.1.cur_level_le; have := hsp_len.cur_vars_le; omega
                have hnlvl_nat : (BitVec.ofNat 64 sp.core.cur_level + 1).toNat =
                    sp.core.cur_level + 1 := by bv_omega
                have hnlvl_lt_ft : (BitVec.ofNat 64 sp.core.cur_level + 1).toNat <
                    sp.core.frame_trail.length := by
                  rw [hnlvl_nat, hsp_len.frame_trail_len]; omega
                have hnlvl_lt_fd : (BitVec.ofNat 64 sp.core.cur_level + 1).toNat <
                    sp.core.frame_dec.length := by
                  rw [hnlvl_nat, hsp_len.frame_dec_len]; omega
                fvt_steps
                let nlvl := sp.core.cur_level + 1
                let dlit := lit ^^^ 1#32
                let ftrl' := sp.core.frame_trail.set nlvl (BitVec.ofNat 32 sp.core.trail_end)
                let fdec' := sp.core.frame_dec.set nlvl dlit
                let s_pre : FullState :=
                  { sp with core :=
                    { sp.core with frame_trail := ftrl', frame_dec := fdec', cur_level := nlvl } }
                have hlen_pre : s_pre.LengthsOk c :=
                  ⟨{ hsp_len with
                       frame_trail_len := by simp [s_pre, ftrl', hsp_len.frame_trail_len],
                       frame_dec_len := by simp [s_pre, fdec', hsp_len.frame_dec_len] },
                   hspp.1.scratch_ok⟩
                have hdlit_nat : dlit.toNat = lit.toNat ^^^ 1 := bv32_xor1_toNat lit
                have hdlit_lt : dlit.toNat < 2 * sp.core.cur_vars :=
                  hdlit_nat ▸ bv32_xor1_lt_even hlit_lt
                have hdlit_zero : sp.core.vals[dlit.toNat]?.getD 0#8 = 0#8 :=
                  hdlit_nat ▸ vals_xor1_eq_zero hspp.2.1 hlit_lt hlv0
                have hnot_guard : ¬ (s_pre.core.cur_vars ≤ dlit.toNat / 2 ∨
                    c.max_vars ≤ s_pre.core.trail_end ∨
                    s_pre.core.vals[dlit.toNat]?.getD 0#8 ≠ 0#8) := by
                  intro hor; rcases hor with h1 | h2 | h3
                  · dsimp only [s_pre] at h1; omega
                  · have := hsp_len.cur_vars_le; dsimp only [s_pre] at h2; omega
                  · exact h3 hdlit_zero
                have hte_bv : BitVec.setWidth 32 (BitVec.ofNat 64 sp.core.trail_end) =
                    BitVec.ofNat 32 sp.core.trail_end := by apply BitVec.eq_of_toNat_eq; simp
                rw [hlit_i64]
                c0_call hAssign
                refine ⟨c, s_pre, R, rfl, hlen_pre, by dsimp [s_pre, nlvl]; omega,
                  (by simp only [s_pre, nlvl, ftrl', fdec', ← hnlvl_nat, ← hte_bv]
                      exact (by assumption)),
                  ?_⟩
                by_cases hguard : s_pre.core.cur_vars ≤ (lit ^^^ 1).toNat / 2 ∨
                    c.max_vars ≤ s_pre.core.trail_end ∨
                    s_pre.core.vals[(lit ^^^ 1).toNat]?.getD 0#8 ≠ 0#8
                · exact absurd hguard hnot_guard
                simp only [hguard, ↓reduceIte]
                intro flags' unass' phases' m_as hfll' hphl' hm_as
                have hnlvl_ne0 : nlvl ≠ 0 := by omega
                simp only [show s_pre.core.cur_level ≠ 0 from hnlvl_ne0, ↓reduceIte] at hm_as ⊢
                obtain ⟨_, hsp_as, hfal_as, hlit_as_ff⟩ :=
                  vivDecideAssign_preserves_sparseW hspp hlit_lt hlv0 hfll' hphl'
                let s_as : FullState :=
                  { sp with
                    core :=
                      { sp.core with
                        vals := (sp.core.vals.set dlit.toNat 1#8).set (dlit.toNat ^^^ 1) 0xFF#8
                        flags := flags',
                        lvl := sp.core.lvl.set (dlit.toNat / 2) (BitVec.ofNat 32 nlvl),
                        rsns := sp.core.rsns.set (dlit.toNat / 2) 0xFFFFFFFF#32,
                        trl := sp.core.trl.set sp.core.trail_end dlit,
                        trail_pos := sp.core.trail_pos.set (dlit.toNat / 2)
                          (BitVec.ofNat 32 sp.core.trail_end),
                        frame_trail := ftrl', frame_dec := fdec',
                        trail_end := sp.core.trail_end + 1, cur_level := nlvl,
                        unassigned := unass' }
                    scratch := { sp.scratch with phases := phases' } }
                have hsp_as' : FullSparseInvW c F0 F_cur s_as := hsp_as
                have hrefs_as : fullArenaClauseRefs s_as = fullArenaClauseRefs sp := rfl
                have hrr_as : s_as.scratch.red_refs = s.scratch.red_refs := hrrp
                have hng_as : fullArenaClauseGarb s_as cref.toNat = false := hngp
                have hsz_as : fullArenaClauseSize s_as cref.toNat = sz.toNat := hszp
                have hlits_as : fullArenaClauseLits s_as cref.toNat =
                    fullArenaClauseLits sp cref.toNat := rfl
                have hcv_as : s_as.core.cur_vars = sp.core.cur_vars := rfl
                have hal_as : s_as.core.arena_len = sp.core.arena_len := rfl
                have hpr_as : s_as.core.probing = sp.core.probing := rfl
                have hfl_as : s_as.core.fuel = sp.core.fuel := rfl
                have hct_as : s_as.core.confl_type = 0#64 := hct0
                have htmp_as : s_as.core.tmp = tmp5 := htmpp
                have hfal_as' : ∀ l < 2 * sp.core.cur_vars,
                    sp.core.vals[l]?.getD 0#8 = 0xFF#8 →
                    s_as.core.vals[l]?.getD 0#8 = 0xFF#8 := hfal_as
                have hlit_as_ff' : s_as.core.vals[lit.toNat]?.getD 0#8 = 0xFF#8 := hlit_as_ff
                have hm_as' : (FullMem c s_as ⋆ R) m_as := hm_as
                clear_value s_as
                try clear hsp_as hfal_as hlit_as_ff hm_as hlen_pre hguard hnot_guard
                fvt_steps
                exact fid11_viv_clause_prop_step Γ
                  (fun a m Q X h => hPropIgn a m Q X (Full.fullPropagateIgnoreSpec_of_del h))
                  hBacktrack hBestImpl hQ hB hJ_jn
                  hsp_as' hsz_le_mv hcvp hcv_as halp hal_as hprp hpr_as hflp hfl_as hal5
                  hrefsp hrefs_as hrr_as hrefp hng_as hsz_as hpermp hlits_as hct_as htmp_as
                  hlits2_lt hlits2_mem hi_lt hlit_eq hlit_lt hfalp hfal_as' hlit_as_ff' hm_as'
              · have hdom := hspp.2.1.vals_domain lit.toNat hlit_lt
                have hlv_eq : sp.core.vals[lit.toNat]? =
                    some (sp.core.vals[lit.toNat]'hlit_lt_vals') :=
                  List.getElem?_eq_getElem hlit_lt_vals'
                have hne1 : sp.core.vals[lit.toNat]'hlit_lt_vals' ≠ 1#8 := fun heq => by
                  have hgt : (0#32).slt ((sp.core.vals[lit.toNat]'hlit_lt_vals').signExtend 32) =
                      true := by rw [heq]; decide
                  have hflt : (0#32).slt ((sp.core.vals[lit.toNat]'hlit_lt_vals').signExtend 32) =
                      false := by assumption
                  exact Bool.false_ne_true (hflt.symm.trans hgt)
                have hne0 : sp.core.vals[lit.toNat]'hlit_lt_vals' ≠ 0#8 := fun heq => by
                  have heq0 : (sp.core.vals[lit.toNat]'hlit_lt_vals').signExtend 32 = 0#32 := by
                    rw [heq]; decide
                  have hne0_raw : (sp.core.vals[lit.toNat]'hlit_lt_vals').signExtend 32 ≠ 0#32 :=
                    by assumption
                  exact hne0_raw heq0
                have hlv_ff : sp.core.vals[lit.toNat]?.getD 0#8 = 0xFF#8 := by
                  rw [hlv_eq, Option.getD_some]
                  rcases (by simpa [hlv_eq] using hdom) with h | h | h
                  · exact absurd h hne0
                  · exact absurd h hne1
                  · exact h
                have hi1_nat : (i + 1#32).toNat = i.toNat + 1 := by bv_omega
                fvt_steps
                exact hJ_jn _ _ ⟨sp, hspp, hcvp, halp, hprp, htmpp, hflp, hrefsp, hrrp, hrefp,
                  hngp, hszp, hpermp, hct0, fun k hk => by
                    rw [hi1_nat] at hk
                    rcases (by omega : k < i.toNat ∨ k = i.toNat) with hk' | rfl
                    · exact hfalp k hk'
                    · rw [← hlit_eq]; exact hlv_ff,
                  hmp⟩
        · have hi_eq : i.toNat = sz.toNat := by dsimp only [sz] at hi_le ⊢; c0_bound
          have hfal_all : ∀ l ∈ fullArenaClauseLits sp cref.toNat,
              sp.core.vals[l]?.getD 0#8 = 0xFF#8 := by
            intro l hl
            obtain ⟨k, hk, hget⟩ := hlits2_inv l (hpermp.mem_iff.mp hl)
            rw [← hget]; exact hfalp k (by omega)
          fvt_steps
          exact hB (i, false, 0xFFFFFFFF#32, ()) _ ⟨sp, hspp, hcvp, halp, hprp, htmpp, hflp,
            hrefsp, hrrp, hrefp, hngp, hszp, hpermp, (fun h => by cases h),
            fun _ h => absurd rfl h, fun _ _ _ => ⟨hct0, hfal_all⟩, hmp⟩
      · intro B L _ hL
        fvt_steps
        exact hL sz.toNat (0#32, ()) _ ⟨s5, Nat.zero_le _, by simp, hsp5, rfl, rfl, rfl,
          htmp5, hfl5, hrefs5, hrr5, href5, hng5, hsz5, hperm5, hct5,
          fun _ hk => by simp at hk, hm5⟩

end ClauseFlagProof

end LeanQbe.T.Examples.Kissat.FullFidelityVivFlag

end
