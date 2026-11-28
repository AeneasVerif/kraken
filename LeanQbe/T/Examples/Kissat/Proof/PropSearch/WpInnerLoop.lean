/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.BcpWatchHelpers
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.BcpFlushHelpers
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.BcpPropHelpers
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.WpOvfFlush
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.WpInnerHelpers
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.WpInnerBin
public import LeanQbe.T.Examples.Kissat.Proof.PropSearch.WpInnerLarge
public import LeanQbe.T.Examples.Kissat.Src.PropSearch
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Examples.Kissat.Proof.Spec.WitnessInv1
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat PropSearch Replacement-Scan, Large-Step, and Main Inner-Loop WP (`WpInnerLoop`)

Proves WP theorems for `s13LpScanExpr`, `s13LpLargeStepExpr`, and `s13LpLoopExpr`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.Proof.PropSearch

open Std Std.Sat Std.ExtHashMap Kraken.Bedrock2.Test
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.Kissat.Ref
open LeanQbe.T.Examples.Kissat.Proof.Spec
open LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open LeanQbe.T.Examples.Kissat.Proof.PropSearch.Spec

local macro "s13_hstraight" : tactic =>
  `(tactic| (
    try first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _
    try dsimp only [opI64, opCmp64, opCmp32, opI32]
    c0_hstraight))

local macro "s13_hsplit" : tactic =>
  `(tactic| ((try (first | change Func.wp _ _ _ _ _ _ | change wp _ _ _ _ _)); c0_hsplit))

private theorem s13_with_mem {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    {e : Expr Val Cont rs} {m : Mem 64} {P : Mem 64 → Prop}
    (hp : P m) (hk : P m → wp Γ Q X e m) : wp Γ Q X e m := hk hp

private theorem s13_arena_lit_mem {k : FullCoreState} {cref r : Nat}
    (hr : r < fullArenaClauseSizeCore k cref)
    (hle : cref + 3 + fullArenaClauseSizeCore k cref ≤ k.arena.length) :
    (k.arena[cref + 3 + r]?.getD 0#32).toNat ∈ fullArenaClauseLitsCore k cref := by
  have h1 : cref + 3 + r < k.arena.length := by omega
  have h2 : r < (List.take (fullArenaClauseSizeCore k cref)
      (List.drop (cref + 3) k.arena)).length := by
    simp [List.length_take, List.length_drop]; omega
  refine List.mem_map.mpr ⟨k.arena[cref + 3 + r]'h1, ?_, ?_⟩
  · have := List.getElem_mem h2
    simp only [List.getElem_take, List.getElem_drop] at this
    exact this
  · simp [List.getElem?_eq_getElem h1]

private theorem s13_fastPropMem_with_arena (s0 sem : FullState) (a' : List (BitVec 32)) :
    { fastPropMem s0 sem with
      core := { (fastPropMem s0 sem).core with arena := a' } } =
      fastPropMem s0 { core := { sem.core with arena := a' }, scratch := sem.scratch } := by
  simp [fastPropMem]

private theorem s13_fastPropMem_with_wstk (s0 sem : FullState) (ws' : List (BitVec 32)) :
    { fastPropMem s0 sem with
      core := { (fastPropMem s0 sem).core with wstk := ws' } } =
      fastPropMem s0 { core := { sem.core with wstk := ws' }, scratch := sem.scratch } := by
  simp [fastPropMem]

theorem s13_nl_lvl_of_trail_ext {s_pi0 : FullState} {not_lit nl_lvl : BitVec 32}
    (hnl_trl : ∃ idx, idx < s_pi0.core.trail_end ∧
      (s_pi0.core.trl[idx]?.getD 0#32).toNat / 2 = not_lit.toNat / 2)
    (hnl_pi : s_pi0.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl) :
    ∀ k : FullCoreState, FullTrailExt s_pi0.core k →
      k.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl := by
  intro k htr
  rcases hnl_trl with ⟨idx, hidx, hvar⟩
  have h1 := htr.2.2 idx hidx
  rw [hvar] at h1
  rw [h1, hnl_pi]

theorem s13_lp_scan_wp {isBeyond : Bool} {Γ : Env} {rs : List Ty} {c : FullCfg}
    {F0 : CNF Nat} {F_cur : List (List Nat)} {ignore_ref : BitVec 64}
    {ignore_arg : Arg Val i64} {s_disk s_pi0 sem0 sem1 : FullState}
    {del0 : List (BitVec 32)} {dlen : Nat}
    {not_lit nl_lvl w0 cref other l0 l1 : BitVec 32} {vo : BitVec 8}
    {cbase3 te un uf tk1 p2 q di dlim : BitVec 64} {cur_lvl32 : BitVec 32}
    {rec_ph nonchrono : Bool} {off_v end_v brk0 : BitVec 64} {brk_arg : Arg Val i64}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post rs} {X : XPost}
    {J_lp : Cont s13LpSig} {J_ovf : Cont (s13OvfSig isBeyond)}
    (hign_eval : ignore_arg = Arg.imm ignore_ref ∨ ignore_arg = Arg.var ignore_ref)
    (hbrk_eval : brk_arg = Arg.imm brk0 ∨ brk_arg = Arg.var brk0)
    (hsd_len : s_disk.LengthsOk c) (hsd_cv : s_disk.core.cur_vars = sem1.core.cur_vars)
    (hsd_pr : sem1.core.propagated ≤ s_disk.core.trail_end)
    (hs0_cv : sem1.core.cur_vars = sem0.core.cur_vars)
    (hs0_pr : sem1.core.propagated = sem0.core.propagated)
    (hs0_dl : sem1.scratch.delayed_len = sem0.scratch.delayed_len)
    (hs0_tk : sem1.scratch.search_ticks = sem0.scratch.search_ticks)
    (hs0_oom : sem1.core.oom = sem0.core.oom)
    (hs0_ct : S13ConflEq sem0.core sem1.core)
    (hdel_ok : Spec.DelayedWatchesOk sem1.core del0 dlen not_lit.toNat)
    (hdel_eq : c.delayed_cap = 0 → del0 = s_pi0.scratch.delayed)
    (hdi_eq : di.toNat = 3 * dlen) (hdlen_le : dlen ≤ c.delayed_cap)
    (hdlim : dlim.toNat = 3 * c.delayed_cap)
    (hpi1 : PropLitInv c F0 F_cur { s_pi0 with scratch := { s_pi0.scratch with delayed := del0 } }
      sem1 not_lit.toNat off_v.toNat q.toNat p2.toNat end_v.toNat)
    (hp2_eq : ∃ p0 : BitVec 64, p2 = p0 + 2#64 ∧ p0.toNat + 2 = p2.toNat ∧ q.toNat ≤ p0.toNat)
    (hnot_lt : not_lit.toNat < 2 * sem1.core.cur_vars)
    (hnl_lvl : nl_lvl = sem1.core.lvl[not_lit.toNat / 2]?.getD 0#32)
    (hcur_lvl : cur_lvl32.toNat = sem1.core.cur_level)
    (hw0_msb : w0 &&& 2147483648#32 = 0#32)
    (hcref_31 : cref.toNat < 2147483648)
    (hcref_ref : cref.toNat ∈ fullArenaClauseRefsCore sem1.core)
    (hcref_ng : fullArenaClauseGarbCore sem1.core cref.toNat = false)
    (hcsz3 : 3 ≤ fullArenaClauseSizeCore sem1.core cref.toNat)
    (hcref_end :
      cref.toNat + 3 + fullArenaClauseSizeCore sem1.core cref.toNat ≤ sem1.core.arena_len)
    (hcbase : cbase3.toNat = cref.toNat + 3)
    (hl0 : sem1.core.arena[cref.toNat + 3]? = some l0)
    (hl1 : sem1.core.arena[cref.toNat + 4]? = some l1)
    (hnl_or : l0 = not_lit ∨ l1 = not_lit)
    (hoth : other = l0 ^^^ l1 ^^^ not_lit)
    (hvo_eq : vo = sem1.core.vals[other.toNat]?.getD 0#8)
    (hvo_ng : (0#32).slt (BitVec.signExtend 32 vo) = false)
    (hte : te.toNat = sem1.core.trail_end) (hun : sem1.core.unassigned = un)
    (huf : sem1.core.unflushed = uf) (hbrk0 : brk0 = 0#64)
    (hm : (FullMem c (fastPropMem s_disk sem1) ⋆ R) m)
    (hJ_lp : ∀ (te' un' uf' tk' p' q' di' : BitVec 64) (sem' : FullState) (m' : Mem 64),
      S13LpInv c F0 F_cur s_disk s_pi0 sem0 sem' not_lit off_v end_v te' un' uf' tk' p' q' di'
        m' R → p' = p2 →
      wp Γ Q X (Expr.jump J_lp (Arg.var te', Arg.var un', Arg.var uf', Arg.var tk',
        Arg.var p', Arg.var q', Arg.var di', ())) m')
    (hJ_ovf : ∀ (xs : Tup Val (s13OvfSig isBeyond)) (m' : Mem 64),
      S13OvfExitPred isBeyond c F0 F_cur ignore_ref s_disk s_pi0 sem0
        not_lit off_v end_v brk0 R xs m' → s13OvfP xs = p2 → J_ovf xs m') :
    wp Γ Q X (s13LpScanExpr isBeyond c.hdr ignore_arg J_lp J_ovf c.pVals c.pWstk c.pArena
      c.pLevel c.pReason c.pTrail c.pTrailPos c.pFlags c.pPhases c.pDelayed dlim cur_lvl32
      rec_ph nonchrono not_lit nl_lvl w0 cref other vo cbase3 tk1 te un uf p2 q di brk_arg) m := by
  have hmaxv : c.max_vars < 2 * dimacsBound := c.hmaxv
  have haren : c.arena_cap < 2 * dimacsBound := c.harena
  have hdelc : c.delayed_cap < dimacsBound := c.hdel
  have hdim : dimacsBound = 268435456 := rfl
  have hcv_le : sem1.core.cur_vars ≤ c.max_vars := hpi1.len.core_ok.cur_vars_le
  have har_len : sem1.core.arena.length = c.arena_cap := hpi1.len.core_ok.arena_len_arr
  have har_le : sem1.core.arena_len ≤ c.arena_cap := hpi1.len.core_ok.arena_len_le
  have hfp_len : (fastPropMem s_disk sem1).LengthsOk c :=
    fastPropMem_lengthsOk hsd_len hpi1.len hsd_cv hsd_pr rfl
  have hlits_lt : ∀ r0, r0 < fullArenaClauseSizeCore sem1.core cref.toNat →
      (sem1.core.arena[cref.toNat + 3 + r0]?.getD 0#32).toNat < 2 * sem1.core.cur_vars := by
    intro r0 hr0
    have hm_ar : (sem1.core.arena[cref.toNat + 3 + r0]?.getD 0#32).toNat ∈
        fullArenaClauseLitsCore (withEmptyWatchesCore c sem1.core) cref.toNat := by
      dsimp only [withEmptyWatchesCore]
      exact s13_arena_lit_mem hr0 (har_len ▸ Nat.le_trans hcref_end har_le)
    exact hpi1.nw.arena.lits_lt cref.toNat hcref_ref hcref_ng _ hm_ar
  have hcr2_n : (BitVec.setWidth 64 cref + 2#64).toNat = cref.toNat + 2 := by
    rw [m7_bv64_add_toNat (by simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega)]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
  have hcr1_n : (BitVec.setWidth 64 cref + 1#64).toNat = cref.toNat + 1 := by
    rw [m7_bv64_add1_toNat (by simp only [BitVec.toNat_setWidth]; omega)]
    simp only [BitVec.toNat_setWidth]; omega
  have hcr2_m : (BitVec.setWidth 64 cref + 2#64).toNat <
      (fastPropMem s_disk sem1).core.arena.length := by
    rw [BcpPropTactics.fastPropMem_arena, har_len, hcr2_n]; omega
  have hcr1_m : (BitVec.setWidth 64 cref + 1#64).toNat <
      (fastPropMem s_disk sem1).core.arena.length := by
    rw [BcpPropTactics.fastPropMem_arena, har_len, hcr1_n]; omega
  have hcr2_ar : ∀ h_pf, (fastPropMem s_disk sem1).core.arena[(BitVec.setWidth 64 cref +
        2#64).toNat]'h_pf =
      sem1.core.arena[cref.toNat + 2]'(by rw [har_len]; omega) := by
    intro h_pf; exact fc_getElem_eq_of_idx (BcpPropTactics.fastPropMem_arena s_disk sem1) hcr2_n _ _
  have hcr1_ar : ∀ h_pf, (fastPropMem s_disk sem1).core.arena[(BitVec.setWidth 64 cref +
        1#64).toNat]'h_pf =
      sem1.core.arena[cref.toNat + 1]'(by rw [har_len]; omega) := by
    intro h_pf; exact fc_getElem_eq_of_idx (BcpPropTactics.fastPropMem_arena s_disk sem1) hcr1_n _ _
  have hcr2_bv : (BitVec.setWidth 64 cref + 2 : BitVec 64).toNat = cref.toNat + 2 := hcr2_n
  have hcr1_bv : (BitVec.setWidth 64 cref + 1 : BitVec 64).toNat = cref.toNat + 1 := hcr1_n
  have hcr2_mod : (cref.toNat + 2) % 2 ^ 64 = cref.toNat + 2 := Nat.mod_eq_of_lt (by omega)
  have hcr1_mod : (cref.toNat + 1) % 2 ^ 64 = cref.toNat + 1 := Nat.mod_eq_of_lt (by omega)
  have hcsz_fst : ∀ {h_pf}, (BitVec.setWidth 64 ((fastPropMem s_disk sem1).core.arena[
      (BitVec.setWidth 64 cref + 2).toNat]'h_pf), ()).fst.toNat =
      fullArenaClauseSizeCore sem1.core cref.toNat := by
    intro h_pf
    change (BitVec.setWidth 64 ((fastPropMem s_disk sem1).core.arena[(BitVec.setWidth 64 cref +
      2).toNat]'h_pf)).toNat = _
    rw [BitVec.toNat_setWidth, fc_getElem_eq_of_idx
      (BcpPropTactics.fastPropMem_arena s_disk sem1) hcr2_bv _ (by rw [har_len]; omega)]
    unfold fullArenaClauseSizeCore
    rw [List.getElem?_eq_getElem (by rw [har_len]; omega), Option.getD_some]
    exact Nat.mod_eq_of_lt (by omega)
  have hpos_fst : ∀ {h_pf}, (BitVec.setWidth 64 ((fastPropMem s_disk sem1).core.arena[
      (BitVec.setWidth 64 cref + 1).toNat]'h_pf), ()).fst.toNat =
      (sem1.core.arena[cref.toNat + 1]'(by rw [har_len]; omega)).toNat := by
    intro h_pf
    change (BitVec.setWidth 64 ((fastPropMem s_disk sem1).core.arena[(BitVec.setWidth 64 cref +
      1).toNat]'h_pf)).toNat = _
    rw [BitVec.toNat_setWidth, fc_getElem_eq_of_idx
      (BcpPropTactics.fastPropMem_arena s_disk sem1) hcr1_bv _ (by rw [har_len]; omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have hpos_mod : ∀ {h_pf},
      ((fastPropMem s_disk sem1).core.arena[(cref.toNat + 1) % 2 ^ 64]'h_pf).toNat =
      (sem1.core.arena[cref.toNat + 1]'(by rw [har_len]; omega)).toNat := by
    intro h_pf
    rw [fc_getElem_eq_of_idx (BcpPropTactics.fastPropMem_arena s_disk sem1) hcr1_mod _
      (by rw [har_len]; omega)]
  have hcsz_mod : ∀ {h_pf},
      ((fastPropMem s_disk sem1).core.arena[(cref.toNat + 2) % 2 ^ 64]'h_pf).toNat =
      fullArenaClauseSizeCore sem1.core cref.toNat := by
    intro h_pf
    rw [fc_getElem_eq_of_idx (BcpPropTactics.fastPropMem_arena s_disk sem1) hcr2_mod _
      (by rw [har_len]; omega)]
    unfold fullArenaClauseSizeCore
    rw [List.getElem?_eq_getElem (by rw [har_len]; omega), Option.getD_some]
  have hdlim_eq : dlim = BitVec.ofNat 64 (3 * c.delayed_cap) := by
    apply BitVec.eq_of_toNat_eq
    rw [hdlim, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  subst dlim
  dsimp only [s13LpScanExpr]
  s13_hstraight
  refine wp_join_group (fun (xs : Tup Val [i64]) m' =>
    m' = m ∧ 2 ≤ xs.1.toNat ∧ xs.1.toNat < fullArenaClauseSizeCore sem1.core cref.toNat) ?_ ?_
  · intro _ ⟨st, ⟨⟩⟩ m' ⟨hm'_eq, hst2, hst_lt⟩
    subst m'
    refine wp_join_group (fun (xs : Tup Val [i64, i32, Ty.bool]) m' =>
      m' = m ∧
        ((xs.2.2.1 = true ∧ 2 ≤ xs.1.toNat ∧
          xs.1.toNat < fullArenaClauseSizeCore sem1.core cref.toNat ∧
          sem1.core.arena[cref.toNat + 3 + xs.1.toNat]? = some xs.2.1 ∧
          xs.2.1.toNat < 2 * sem1.core.cur_vars ∧
          (BitVec.signExtend 32 (sem1.core.vals[xs.2.1.toNat]?.getD 0#8)).slt 0#32 = false) ∨
        (xs.2.2.1 = false ∧ ∀ r0, st.toNat ≤ r0 →
          r0 < fullArenaClauseSizeCore sem1.core cref.toNat →
          (BitVec.signExtend 32 (sem1.core.vals[(sem1.core.arena[cref.toNat + 3 + r0]?.getD
            0#32).toNat]?.getD 0#8)).slt 0#32 = true))) ?_ ?_
    · intro _ ⟨ri1, repl1, found1, ⟨⟩⟩ m' ⟨hm'_eq, hres1⟩
      subst m'
      refine wp_join_group (fun (xs : Tup Val [i64, i32, Ty.bool]) m' =>
        m' = m ∧
          ((xs.2.2.1 = true ∧ 2 ≤ xs.1.toNat ∧
            xs.1.toNat < fullArenaClauseSizeCore sem1.core cref.toNat ∧
            sem1.core.arena[cref.toNat + 3 + xs.1.toNat]? = some xs.2.1 ∧
            xs.2.1.toNat < 2 * sem1.core.cur_vars ∧
            (BitVec.signExtend 32 (sem1.core.vals[xs.2.1.toNat]?.getD 0#8)).slt 0#32 = false) ∨
          (xs.2.2.1 = false ∧ ∀ r0, 2 ≤ r0 →
            r0 < fullArenaClauseSizeCore sem1.core cref.toNat →
            (BitVec.signExtend 32 (sem1.core.vals[(sem1.core.arena[cref.toNat + 3 + r0]?.getD
              0#32).toNat]?.getD 0#8)).slt 0#32 = true))) ?_ ?_
      · intro _ ⟨ri, repl, found, ⟨⟩⟩ m' ⟨hm'_eq, hres⟩
        subst m'
        s13_hsplit
        · rcases hres with ⟨-, hri2, hri_lt, har_ri, hrepl_lt, hrepl_nneg⟩ | ⟨hf, -⟩
          · have hc1_m : (cref.toNat + 1) % 2 ^ 64 = cref.toNat + 1 :=
              Nat.mod_eq_of_lt (by omega)
            have hc1_bv : (BitVec.setWidth 64 cref + 1).toNat = cref.toNat + 1 := hcr1_n
            have hc1_ar_lt : (cref.toNat + 1) < (fastPropMem s_disk sem1).core.arena.length := by
              rw [BcpPropTactics.fastPropMem_arena, har_len]; omega
            s13_hstraight
            dsimp only at hm
            rw [BcpPropTactics.fastPropMem_arena] at hm
            try rw [hc1_m] at hm
            try rw [hc1_bv] at hm
            rw [← s13_fastPropMem_with_arena] at hm
            dsimp only at hm
            let sem2 : FullState := {
              core := { sem1.core with
                arena := sem1.core.arena.set (cref.toNat + 1) (BitVec.setWidth 32 ri) },
              scratch := sem1.scratch }
            have hsr : PropLitInv c F0 F_cur
                  { s_pi0 with scratch := { s_pi0.scratch with delayed := del0 } }
                  sem2 not_lit.toNat off_v.toNat q.toNat p2.toNat end_v.toNat ∧
                sem2.LengthsOk c ∧ cref.toNat ∈ fullArenaClauseRefsCore sem2.core ∧
                fullArenaClauseSizeCore sem2.core cref.toNat =
                  fullArenaClauseSizeCore sem1.core cref.toNat ∧
                sem2.core.arena[cref.toNat + 3]? = some l0 ∧
                sem2.core.arena[cref.toNat + 4]? = some l1 ∧
                sem2.core.arena[cref.toNat + 3 + ri.toNat]? = some repl := by
              rcases hp2_eq with ⟨p0, rfl, hp0_2, hqp0⟩
              have hpi1' : PropLitInv c F0 F_cur
                  { s_pi0 with scratch := { s_pi0.scratch with delayed := del0 } }
                  sem1 not_lit.toNat off_v.toNat q.toNat (p0.toNat + 2) end_v.toNat :=
                hp0_2 ▸ hpi1
              have hs := s13_setSrch_step hpi1' hcref_ref hl0 hl1 har_ri
                (ri32 := BitVec.setWidth 32 ri)
              exact ⟨hp0_2 ▸ hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1,
                hs.2.2.2.2.2.1, hs.2.2.2.2.2.2⟩
            have hng2 : fullArenaClauseGarbCore sem2.core cref.toNat = false := by
              unfold fullArenaClauseGarbCore fullArenaHdrCore at hcref_ng ⊢
              simpa [sem2, List.getElem?_set_ne (by omega : cref.toNat + 1 ≠ cref.toNat)]
                using hcref_ng
            have hrefs_eq :
                fullArenaClauseRefsCore sem2.core = fullArenaClauseRefsCore sem1.core :=
              hsr.1.perm.2.1.trans hpi1.perm.2.1.symm
            have hdel2 : Spec.DelayedWatchesOk sem2.core del0 dlen not_lit.toNat := by
              intro j hj
              simpa [Spec.DelayedWatchesOk, sem2, hrefs_eq] using hdel_ok j hj
            exact s13_lp_repl_del_wp hbrk_eval hsd_len (by simpa [sem2] using hsd_cv)
              (by simpa [sem2] using hsd_pr) (by simpa [sem2] using hs0_cv)
              (by simpa [sem2] using hs0_pr) (by simpa [sem2] using hs0_dl)
              (by simpa [sem2] using hs0_tk) (by simpa [sem2] using hs0_oom)
              (by simpa [sem2] using hs0_ct) hdel2 hdel_eq hdi_eq hdlen_le hsr.1 hp2_eq
              (by simpa [sem2] using hnot_lt) hcref_31 hsr.2.2.1 hng2
              (hsr.2.2.2.1.symm ▸ hcsz3) (by rw [hsr.2.2.2.1]; exact hcref_end) hcbase
              hsr.2.2.2.2.1 hsr.2.2.2.2.2.1 hnl_or hoth hri2 (hsr.2.2.2.1.symm ▸ hri_lt)
              hsr.2.2.2.2.2.2 (by simpa [sem2] using hrepl_lt)
              (by simpa [sem2] using hrepl_nneg) (by simpa [sem2] using hte)
              (by simpa [sem2] using hun) (by simpa [sem2] using huf) hm hJ_lp hJ_ovf
          · dsimp only at hf hc; rw [hf] at hc; exact Bool.noConfusion hc
        · have hf_eq : found = false := by cases found; rfl; exact Bool.noConfusion hc
          rcases hres with ⟨hf, -⟩ | ⟨-, hall_bad⟩
          · exact absurd (hf_eq.symm.trans hf) (by decide)
          · exact s13_lp_no_repl_wp hign_eval hsd_len hsd_cv hsd_pr hs0_cv hs0_pr hs0_dl hs0_tk
              hs0_oom hs0_ct hdel_ok hdel_eq hdi_eq hdlen_le hpi1 hp2_eq hnot_lt hnl_lvl
              hcur_lvl hw0_msb hcref_31 hcref_ref hcref_ng hcsz3 hcref_end hcbase hcsz_fst hl0 hl1
              hnl_or hoth hvo_eq hvo_ng hall_bad hte hun huf hbrk0 hm hJ_lp hJ_ovf
      · intro J152 hJ152
        s13_hsplit
        · s13_hstraight
          rcases hres1 with ⟨hf, hri2, hri_lt, har_eq, hrepl_lt, hrepl_nneg⟩ | ⟨hf, -⟩
          · exact hJ152 (ri1, repl1, found1, ()) m
              ⟨rfl, Or.inl ⟨hf, hri2, hri_lt, har_eq, hrepl_lt, hrepl_nneg⟩⟩
          · dsimp only at hf hc; rw [hf] at hc; exact Bool.noConfusion hc
        · have hf1 : found1 = false := by cases found1; rfl; exact Bool.noConfusion hc
          rcases hres1 with ⟨hf, -⟩ | ⟨-, hbad_hi⟩
          · exact absurd (hf1.symm.trans hf) (by decide)
          · refine wp_join_group (fun (xs : Tup Val [i64, i32, Ty.bool]) m' =>
              m' = m ∧
                ((xs.2.2.1 = true ∧ 2 ≤ xs.1.toNat ∧
                  xs.1.toNat < fullArenaClauseSizeCore sem1.core cref.toNat ∧
                  sem1.core.arena[cref.toNat + 3 + xs.1.toNat]? = some xs.2.1 ∧
                  xs.2.1.toNat < 2 * sem1.core.cur_vars ∧
                  (BitVec.signExtend 32 (sem1.core.vals[xs.2.1.toNat]?.getD
                    0#8)).slt 0#32 = false) ∨
                (xs.2.2.1 = false ∧ ∀ r0, 2 ≤ r0 →
                  r0 < fullArenaClauseSizeCore sem1.core cref.toNat →
                  (BitVec.signExtend 32 (sem1.core.vals[(sem1.core.arena[cref.toNat + 3 +
                    r0]?.getD 0#32).toNat]?.getD 0#8)).slt 0#32 = true))) ?_ ?_
            · intro _ ⟨wri, wrepl, wf, ⟨⟩⟩ m' ⟨hm'_eq, hres⟩
              subst m'; s13_hstraight
              exact hJ152 (wri, wrepl, wf, ()) m ⟨rfl, hres⟩
            · intro J286 hJ286
              exact s13_lp_repl_scan_sub_wp (r_init := 2#64) (def_lit := repl1) (def_ok := found1)
                (Or.inl rfl) (Or.inr rfl) (Or.inr rfl) hfp_len hpi1.len hcbase hst2
                (le_of_lt hst_lt) hcref_end (fun r0 _ hr0 => hlits_lt r0 (Nat.lt_trans hr0 hst_lt))
                hm
                (fun r cand hr2 hrl har_r hclt hnneg _ => by
                  s13_hstraight
                  exact hJ286 (r, cand, true, ()) m
                    ⟨rfl, Or.inl ⟨rfl, hr2, Nat.lt_trans hrl hst_lt, har_r, hclt, hnneg⟩⟩)
                (fun hbad_lo => by
                  s13_hstraight; rw [hf1]
                  exact hJ286 (st, repl1, false, ()) m
                    ⟨rfl, Or.inr ⟨rfl, fun r0 hr2 hrc => by
                      by_cases hlt : r0 < st.toNat
                      · exact hbad_lo r0 hr2 hlt
                      · exact hbad_hi r0 (Nat.le_of_not_lt hlt) hrc⟩⟩)
    · intro J150 hJ150
      have hcr2_m' : (BitVec.setWidth 64 cref + 2).toNat <
          (fastPropMem s_disk sem1).core.arena.length :=
        (hcr2_bv.trans hcr2_n.symm) ▸ hcr2_m
      exact s13_lp_repl_scan_sub_wp (r_init := st) (def_lit := 0#32) (def_ok := false)
        (Or.inr rfl) (Or.inl rfl) (Or.inl rfl) hfp_len hpi1.len hcbase
        (by rw [hcsz_fst]; exact le_of_lt hst_lt) (by rw [hcsz_fst]; exact Nat.le_refl _)
        hcref_end (fun r0 _ hr0 => hlits_lt r0 (by rw [hcsz_fst] at hr0; exact hr0)) hm
        (fun r cand hst_r hrl har_r hclt hnneg _ => by
          s13_hstraight
          rw [hcsz_fst] at hrl
          exact hJ150 (r, cand, true, ()) m
            ⟨rfl, Or.inl ⟨rfl, le_trans hst2 hst_r, hrl, har_r, hclt, hnneg⟩⟩)
        (fun hbad_hi => by
          s13_hstraight
          exact hJ150 (_, 0#32, false, ()) m
            ⟨rfl, Or.inr ⟨rfl, fun r0 hst_r hrc => by
              rw [← hcsz_fst (h_pf := hcr2_m')] at hrc; exact hbad_hi r0 hst_r hrc⟩⟩)
  · intro J148 hJ148
    have h2_lt : 2 < fullArenaClauseSizeCore sem1.core cref.toNat := by omega
    s13_hsplit
    · s13_hstraight; exact hJ148 (2#64, ()) m ⟨rfl, by decide, h2_lt⟩
    · have hpos_ge2 := hc; clear hc
      s13_hsplit
      · s13_hstraight; exact hJ148 (2#64, ()) m ⟨rfl, by decide, h2_lt⟩
      · have hpos_lt := hc; clear hc
        simp only [show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
          show BitVec.toNat (2 : BitVec 64) = 2 from rfl] at hpos_ge2 hpos_lt
        rw [hpos_mod] at hpos_ge2
        rw [hpos_mod, hcsz_mod] at hpos_lt
        s13_hstraight
        exact hJ148 _ m ⟨rfl, by rw [hpos_fst]; exact Nat.le_of_not_lt hpos_ge2,
          by rw [hpos_fst]; exact Nat.lt_of_not_le hpos_lt⟩

theorem s13_lp_large_step_wp {isBeyond : Bool} {Γ : Env} {rs : List Ty} {c : FullCfg}
    {F0 : CNF Nat} {F_cur : List (List Nat)} {ignore_ref : BitVec 64}
    {ignore_arg : Arg Val i64} {s_disk s_pi0 sem0 sem : FullState}
    {not_lit nl_lvl w0 : BitVec 32}
    {two_cv te un uf tk p q di dlim off_v end_v brk0 : BitVec 64}
    {cur_lvl32 : BitVec 32} {rec_ph nonchrono : Bool} {brk_arg : Arg Val i64}
    {R : Mem 64 → Prop} {m : Mem 64} {Q : Post rs} {X : XPost}
    {J_lp : Cont s13LpSig} {J_ovf : Cont (s13OvfSig isBeyond)}
    (hign_eval : ignore_arg = Arg.imm ignore_ref ∨ ignore_arg = Arg.var ignore_ref)
    (hbrk_eval : brk_arg = Arg.imm brk0 ∨ brk_arg = Arg.var brk0)
    (hinv : S13LpInv c F0 F_cur s_disk s_pi0 sem0 sem not_lit off_v end_v te un uf tk p q di m R)
    (hnot_lt : not_lit.toNat < 2 * sem.core.cur_vars)
    (htwo_cv : two_cv.toNat = 2 * sem.core.cur_vars)
    (hcur_lvl : cur_lvl32.toNat = sem.core.cur_level)
    (hnl : sem.core.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl)
    (hdlim : dlim.toNat = 3 * c.delayed_cap)
    (hp_lt : p.toNat < end_v.toNat) (hp_w : sem.core.wstk[p.toNat]? = some w0)
    (hw0_msb : w0 &&& 2147483648#32 = 0#32)
    (hbrk0 : brk0 = 0#64)
    (hJ_lp : ∀ (te' un' uf' tk' p' q' di' : BitVec 64) (sem' : FullState) (m' : Mem 64),
      S13LpInv c F0 F_cur s_disk s_pi0 sem0 sem' not_lit off_v end_v
        te' un' uf' tk' p' q' di' m' R → p' = p + 2#64 →
      wp Γ Q X (Expr.jump J_lp (Arg.var te', Arg.var un', Arg.var uf', Arg.var tk',
        Arg.var p', Arg.var q', Arg.var di', ())) m')
    (hJ_ovf : ∀ (xs : Tup Val (s13OvfSig isBeyond)) (m' : Mem 64),
      S13OvfExitPred isBeyond c F0 F_cur ignore_ref s_disk s_pi0 sem0 not_lit off_v end_v
        brk0 R xs m' → s13OvfP xs = p + 2#64 → J_ovf xs m') :
    wp Γ Q X (s13LpLargeStepExpr isBeyond c.hdr ignore_arg J_lp J_ovf c.pVals c.pWstk c.pArena
      c.pLevel c.pReason c.pTrail c.pTrailPos c.pFlags c.pPhases c.pDelayed dlim two_cv
      cur_lvl32 rec_ph nonchrono not_lit nl_lvl w0 te un uf tk p q di brk_arg) m := by
  rcases hinv with ⟨del0, dlen, hm, hpi, hdel_ok, hdel_eq, hte, rfl, rfl, hdi_eq, hdlen_le,
    hs0_cv, hs0_pr, hs0_dl, hs0_tk, hs0_oom, hs0_ct, hsd_len, hsd_s0, hsd_pr⟩
  have hsd_cv : s_disk.core.cur_vars = sem.core.cur_vars := hsd_s0.trans hs0_cv.symm
  have hmaxv : c.max_vars < 2 * dimacsBound := c.hmaxv
  have haren : c.arena_cap < 2 * dimacsBound := c.harena
  have hwcap : c.wcap < 2 * dimacsBound := c.hwcap
  have hdim : dimacsBound = 268435456 := rfl
  unfold dimacsBound at hmaxv haren hwcap
  have hcv_le : sem.core.cur_vars ≤ c.max_vars := hpi.len.core_ok.cur_vars_le
  have har_len : sem.core.arena.length = c.arena_cap := hpi.len.core_ok.arena_len_arr
  have har_le : sem.core.arena_len ≤ c.arena_cap := hpi.len.core_ok.arena_len_le
  have hvals_len : sem.core.vals.length = 2 * c.max_vars := hpi.len.core_ok.vals_len
  have hwstk_len : sem.core.wstk.length = c.wcap := hpi.len.core_ok.wstk_len_arr
  have ⟨hend_le, hwlen_le⟩ := hpi.end_lt_wcap hnot_lt
  have hq_ge := hpi.sw.q_ge
  have hq_le := hpi.sw.q_le_p
  obtain ⟨_, cref, hcr_get, hcr_31, hcr_ref, hrem2⟩ :=
    watchSlice_inv_large hpi.sw.rem_slice (Nat.sub_pos_of_lt hp_lt) hp_w hw0_msb
  have h2_le_end : p.toNat + 2 ≤ end_v.toNat := by omega
  have hp1_n : (p + 1#64).toNat = p.toNat + 1 := m7_bv64_add1_toNat (by omega)
  have hp2_n : (p + 2#64).toNat = p.toNat + 2 := m7_bv64_add2_toNat (by omega)
  have hq1_n : (q + 1#64).toNat = q.toNat + 1 := m7_bv64_add1_toNat (by omega)
  have hq2_n : (q + 2#64).toNat = q.toNat + 2 := m7_bv64_add2_toNat (by omega)
  have hp1_ws : (p + 1#64).toNat < (fastPropMem s_disk sem).core.wstk.length := by
    rw [BcpPropTactics.fastPropMem_wstk, hwstk_len, hp1_n]; omega
  have hq_ws : q.toNat < (fastPropMem s_disk sem).core.wstk.length := by
    rw [BcpPropTactics.fastPropMem_wstk, hwstk_len]; omega
  have hq1_ws : (q + 1#64).toNat < (fastPropMem s_disk sem).core.wstk.length := by
    rw [BcpPropTactics.fastPropMem_wstk, hwstk_len, hq1_n]; omega
  have hcr_eq : (fastPropMem s_disk sem).core.wstk[(p + 1#64).toNat]'hp1_ws = cref := by
    rw [fc_getElem_wstk s_disk sem _ (by rw [hwstk_len, hp1_n]; omega)]
    exact Option.some.inj ((List.getElem?_eq_getElem (by rw [hwstk_len, hp1_n]; omega)).symm.trans
      (hp1_n ▸ hcr_get))
  have hpi_drop : PropLitInv c F0 F_cur
      { s_pi0 with scratch := { s_pi0.scratch with delayed := del0 } }
      sem not_lit.toNat off_v.toNat q.toNat (p + 2#64).toNat end_v.toNat := by
    have h1 := propLit_inv_drop hpi (Nat.le_add_right p.toNat 2) h2_le_end
      (by simpa [Nat.sub_sub] using hrem2)
    exact hp2_n ▸ h1
  have hcr_wf := hpi.nw.arena.refs_wf cref.toNat hcr_ref
  have hcsz3 : 3 ≤ fullArenaClauseSizeCore sem.core cref.toNat := hcr_wf.2.1
  have hcr_fit : cref.toNat + 3 + fullArenaClauseSizeCore sem.core cref.toNat ≤
      sem.core.arena_len := Nat.le_trans hcr_wf.2.2.1 hcr_wf.2.2.2.1
  have hcr_eq' : ∀ {h_pf}, (fastPropMem s_disk sem).core.wstk[(p + 1).toNat]'h_pf = cref := by
    intro h_pf
    change (fastPropMem s_disk sem).core.wstk[(p + 1#64).toNat]'h_pf = cref
    exact hcr_eq
  have hp2_eq : ∃ p0 : BitVec 64, p + 2#64 = p0 + 2#64 ∧ p0.toNat + 2 = (p + 2#64).toNat ∧
      q.toNat ≤ p0.toNat := ⟨p, rfl, hp2_n.symm, hq_le⟩
  dsimp only [s13LpLargeStepExpr]
  refine wp_join_group (fun (_ : Tup Val []) mc => (FullMem c (fastPropMem s_disk sem) ⋆ R) mc)
    ?_ ?_
  · intro _ ⟨⟩ mc hmc
    s13_hstraight
    have hcr_ar_lt : (BitVec.setWidth 64 cref).toNat <
        (fastPropMem s_disk sem).core.arena.length := by
      simp only [BcpPropTactics.fastPropMem_arena, har_len, BitVec.toNat_setWidth,
        Nat.mod_eq_of_lt (by omega : cref.toNat < 2 ^ 64)]
      omega
    s13_hsplit
    · s13_hstraight
      refine hJ_lp _ _ _ _ _ _ _ sem mc ?_ rfl
      exact ⟨del0, dlen, hmc, hpi_drop, hdel_ok, hdel_eq, hte, rfl, rfl, hdi_eq, hdlen_le,
        hs0_cv, hs0_pr, hs0_dl, hs0_tk, hs0_oom, hs0_ct, hsd_len, hsd_s0, hsd_pr⟩
    · have hng0 : fullArenaClauseGarbCore sem.core cref.toNat = false := by
        unfold fullArenaClauseGarbCore fullArenaHdrCore
        have hg : sem.core.arena[cref.toNat]? =
            some (sem.core.arena[cref.toNat]'(by rw [har_len]; omega)) :=
          List.getElem?_eq_getElem _
        have hfl_eq := fc_getElem_arena s_disk sem (i := cref.toNat)
          (by rw [BcpPropTactics.fastPropMem_arena, har_len]; omega) (by rw [har_len]; omega)
        have hp1_mod : (p.toNat + 1) % 2 ^ 64 = (p + 1#64).toNat := by
          rw [hp1_n, Nat.mod_eq_of_lt (by omega)]
        have hcr_mod : (fastPropMem s_disk sem).core.wstk[(p.toNat + 1) % 2 ^ 64]'(by
            rw [BcpPropTactics.fastPropMem_wstk, hwstk_len, hp1_mod, hp1_n]; omega) = cref :=
          (fc_getElem_eq_of_idx (by rfl) hp1_mod _ _).trans hcr_eq
        have h524 : (sem.core.arena[cref.toNat]'(by rw [har_len]; omega) &&& 524288#32) = 0#32 := by
          rw [← hfl_eq]
          simpa only [show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
            show (524288 : BitVec 32) = 524288#32 from rfl,
            show (0 : BitVec 32) = 0#32 from rfl, hcr_mod] using hc
        rw [hg, Option.getD_some, h524]; decide
      have hcbase_n : (BitVec.setWidth 64 cref + 3#64).toNat = cref.toNat + 3 := by
        rw [m7_bv64_add_toNat (by simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega)]
        simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
      have hcbase1_n : (BitVec.setWidth 64 cref + 3#64 + 1#64).toNat = cref.toNat + 4 := by
        rw [m7_bv64_add1_toNat (by rw [hcbase_n]; omega), hcbase_n]
      have hcr3_bv : (BitVec.setWidth 64 cref + 3, ()).fst.toNat = cref.toNat + 3 := hcbase_n
      have hcr4_bv :
          ((BitVec.setWidth 64 cref + 3, ()).fst + 1, ()).fst.toNat = cref.toNat + 4 := hcbase1_n
      have hcr3_m' : (BitVec.setWidth 64 cref + 3, ()).fst.toNat <
          (fastPropMem s_disk sem).core.arena.length := by
        rw [BcpPropTactics.fastPropMem_arena, har_len, hcr3_bv]; omega
      have hcr4_m' : ((BitVec.setWidth 64 cref + 3, ()).fst + 1, ()).fst.toNat <
          (fastPropMem s_disk sem).core.arena.length := by
        rw [BcpPropTactics.fastPropMem_arena, har_len, hcr4_bv]; omega
      try simp only [hcr_eq']
      s13_hstraight
      let l0 := (fastPropMem s_disk sem).core.arena[
        (BitVec.setWidth 64 cref + 3, ()).fst.toNat]'hcr3_m'
      let l1 := (fastPropMem s_disk sem).core.arena[
        ((BitVec.setWidth 64 cref + 3, ()).fst + 1, ()).fst.toNat]'hcr4_m'
      have hl0_eq : l0 = sem.core.arena[cref.toNat + 3]'(by rw [har_len]; omega) :=
        (fc_getElem_arena s_disk sem hcr3_m' (by rw [har_len, hcr3_bv]; omega)).trans
          (fc_getElem_eq_of_idx (by rfl) hcr3_bv _ _)
      have hl1_eq : l1 = sem.core.arena[cref.toNat + 4]'(by rw [har_len]; omega) :=
        (fc_getElem_arena s_disk sem hcr4_m' (by rw [har_len, hcr4_bv]; omega)).trans
          (fc_getElem_eq_of_idx (by rfl) hcr4_bv _ _)
      have hl0_get : sem.core.arena[cref.toNat + 3]? = some l0 :=
        hl0_eq ▸ List.getElem?_eq_getElem (by rw [har_len]; omega)
      have hl1_get : sem.core.arena[cref.toNat + 4]? = some l1 :=
        hl1_eq ▸ List.getElem?_eq_getElem (by rw [har_len]; omega)
      refine wp_join_group (fun (_ : Tup Val []) mchk =>
        (FullMem c (fastPropMem s_disk sem) ⋆ R) mchk ∧ (l0 = not_lit ∨ l1 = not_lit)) ?_ ?_
      · intro _ ⟨⟩ mchk ⟨hmchk, hwatch⟩
        let other := l0 ^^^ l1 ^^^ not_lit
        have hbd0 : cref.toNat + 3 + fullArenaClauseSizeCore sem.core cref.toNat ≤
            sem.core.arena.length := har_len ▸ Nat.le_trans hcr_fit har_le
        have hoth_lt : other.toNat < 2 * sem.core.cur_vars := by
          rcases hwatch with rfl | rfl
          · have h1 : other = l1 := fid_xor_cancel_l l0 l1
            rw [h1]
            have hm1 : (sem.core.arena[cref.toNat + 3 + 1]?.getD 0#32).toNat ∈
                fullArenaClauseLitsCore (withEmptyWatchesCore c sem.core) cref.toNat := by
              dsimp only [withEmptyWatchesCore]
              exact s13_arena_lit_mem (Nat.lt_of_lt_of_le (by decide) hcsz3) hbd0
            have := hpi.nw.arena.lits_lt cref.toNat hcr_ref hng0 _ hm1
            simpa [withEmptyWatchesCore, hl1_get] using this
          · have h1 : other = l0 := fid_xor_cancel_r l0 l1
            rw [h1]
            have hm0 : (sem.core.arena[cref.toNat + 3 + 0]?.getD 0#32).toNat ∈
                fullArenaClauseLitsCore (withEmptyWatchesCore c sem.core) cref.toNat := by
              dsimp only [withEmptyWatchesCore]
              exact s13_arena_lit_mem (Nat.lt_of_lt_of_le (by decide) hcsz3) hbd0
            have := hpi.nw.arena.lits_lt cref.toNat hcr_ref hng0 _ hm0
            simpa [withEmptyWatchesCore, hl0_get] using this
        have hoth_mask : other &&& 2147483647#32 = other := m7_bv32_mask7f_eq (by omega)
        have hoth_flag0 : other &&& 2147483648#32 = 0#32 := by
          rw [← hoth_mask, BitVec.and_assoc,
            (by decide : (2147483647#32 &&& 2147483648#32) = 0#32), BitVec.and_zero]
        have hoth_vals_m : (BitVec.setWidth 64 other).toNat <
            (fastPropMem s_disk sem).core.vals.length := by
          rw [BcpPropTactics.fastPropMem_vals, hvals_len, BitVec.toNat_setWidth,
            Nat.mod_eq_of_lt (by omega)]
          omega
        let ov := (fastPropMem s_disk sem).core.vals[(BitVec.setWidth 64 other).toNat]'hoth_vals_m
        have hov_eq : ov = sem.core.vals[other.toNat]?.getD 0#8 := by
          rw [List.getElem?_eq_getElem (by rw [hvals_len]; omega), Option.getD_some]
          exact (fc_getElem_vals s_disk sem hoth_vals_m
            (by rw [hvals_len, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; omega)).trans
            (fc_getElem_eq_of_idx (by rfl) (by simp [BitVec.toNat_setWidth]; omega) _ _)
        s13_hstraight
        s13_hsplit
        · s13_hstraight
          let sem_k : FullState := {
            core := { sem.core with
              wstk := (sem.core.wstk.set q.toNat other).set (q + 1#64).toNat cref },
            scratch := sem.scratch }
          have hkeep : PropLitInv c F0 F_cur
              { s_pi0 with scratch := { s_pi0.scratch with delayed := del0 } }
              sem_k not_lit.toNat off_v.toNat (q + 2#64).toNat (p + 2#64).toNat end_v.toNat := by
            have hp2_m : (p.toNat + 2) % 2 ^ 64 = p.toNat + 2 := Nat.mod_eq_of_lt (by omega)
            have hq2_m : (q.toNat + 2) % 2 ^ 64 = q.toNat + 2 := Nat.mod_eq_of_lt (by omega)
            have h1 := propLit_inv_keep_large (hp2_n ▸ hpi_drop) hnot_lt hq_le
              (by rw [hwstk_len]; omega) (by rw [hwstk_len]; omega) hoth_flag0 hcr_31 hcr_ref
            simpa [sem_k, hq1_n, hq2_n, hq2_m, hp2_n, hp2_m] using h1
          have hdel_k : Spec.DelayedWatchesOk sem_k.core del0 dlen not_lit.toNat := by
            intro j hj
            simpa [Spec.DelayedWatchesOk, sem_k, fullArenaClauseRefsCore] using hdel_ok j hj
          have hl0_rw : ∀ {h_pf}, sem.core.arena[(BitVec.setWidth 64 cref + 3).toNat]'h_pf = l0 :=
            fun {_} => (fc_getElem_eq_of_idx (by rfl) hcbase_n _ _).trans hl0_eq.symm
          have hl1_rw : ∀ {h_pf},
              sem.core.arena[(BitVec.setWidth 64 cref + 3 + 1).toNat]'h_pf = l1 :=
            fun {_} => (fc_getElem_eq_of_idx (by rfl) hcbase1_n _ _).trans hl1_eq.symm
          have hq1_bv : (q + 1 : BitVec 64).toNat = q.toNat + 1 := hq1_n
          refine hJ_lp _ _ _ _ _ _ _ sem_k _ ?_ rfl
          exact ⟨del0, dlen, by
            simp only [fastPropMem] at hm ⊢
            simp only [sem_k, hq1_n, hq1_bv, hl0_rw, hl1_rw, other] at hm ⊢
            exact hm, hkeep, hdel_k, hdel_eq,
            by simpa [sem_k] using hte, rfl, rfl, hdi_eq, hdlen_le,
            by simpa [sem_k] using hs0_cv, by simpa [sem_k] using hs0_pr, hs0_dl, hs0_tk,
            by simpa [sem_k] using hs0_oom, by simpa [sem_k] using hs0_ct, hsd_len, hsd_s0,
            by simpa [sem_k] using hsd_pr⟩
        · have hov_ng : (0#32).slt (BitVec.signExtend 32 ov) = false := by
            have hcb_m : (cref.toNat + 3) % 2 ^ 64 = (BitVec.setWidth 64 cref + 3, ()).fst.toNat :=
              by rw [hcr3_bv, Nat.mod_eq_of_lt (by omega)]
            have hcb1_m : (cref.toNat + 3 + 1) % 2 ^ 64 =
                ((BitVec.setWidth 64 cref + 3, ()).fst + 1, ()).fst.toNat :=
              by rw [hcr4_bv, Nat.mod_eq_of_lt (by omega)]
            have hl0_m : ∀ {h_pf},
                (fastPropMem s_disk sem).core.arena[(cref.toNat + 3) % 2 ^ 64]'h_pf = l0 :=
              fun {_} => fc_getElem_eq_of_idx (by rfl) hcb_m _ _
            have hl1_m : ∀ {h_pf},
                (fastPropMem s_disk sem).core.arena[(cref.toNat + 3 + 1) % 2 ^ 64]'h_pf = l1 :=
              fun {_} => fc_getElem_eq_of_idx (by rfl) hcb1_m _ _
            have hx_eq : other.toNat = (BitVec.setWidth 64 other).toNat := by
              rw [BitVec.toNat_setWidth]
              exact (Nat.mod_eq_of_lt (by omega)).symm
            simp only [show BitVec.toNat (3 : BitVec 64) = 3 from rfl,
              show BitVec.toNat (1 : BitVec 64) = 1 from rfl] at hc
            have hidx_eq : ∀ h1 h2,
                ((fastPropMem s_disk sem).core.arena[(cref.toNat + 3) % 2 ^ 64]'h1 ^^^
                 (fastPropMem s_disk sem).core.arena[(cref.toNat + 3 + 1) % 2 ^ 64]'h2 ^^^
                 not_lit).toNat = (BitVec.setWidth 64 other).toNat := by
              intro h1 h2; rw [hl0_m, hl1_m]; exact hx_eq
            have hres := (congrArg (fun v =>
              (BitVec.ofNat 32 0).slt (BitVec.signExtend 32 v))
              (fc_getElem_eq_of_idx (by rfl) (hidx_eq _ _) _ hoth_vals_m)).symm.trans hc
            simpa only [show BitVec.ofNat 32 0 = 0#32 from rfl] using hres
          exact s13_lp_scan_wp hign_eval hbrk_eval hsd_len hsd_cv hsd_pr hs0_cv hs0_pr hs0_dl
            hs0_tk hs0_oom hs0_ct hdel_ok hdel_eq hdi_eq hdlen_le hdlim hpi_drop hp2_eq hnot_lt
            hnl.symm hcur_lvl hw0_msb hcr_31 hcr_ref hng0 hcsz3 hcr_fit hcbase_n hl0_get hl1_get
            hwatch rfl hov_eq hov_ng hte.symm rfl rfl hbrk0 hmchk hJ_lp hJ_ovf
      · intro J119 hJ119
        s13_hsplit
        · s13_hsplit
          · s13_hstraight
            refine hJ_lp _ _ _ _ _ _ _ sem mc ?_ rfl
            exact ⟨del0, dlen, hmc, hpi_drop, hdel_ok, hdel_eq, hte, rfl, rfl, hdi_eq, hdlen_le,
              hs0_cv, hs0_pr, hs0_dl, hs0_tk, hs0_oom, hs0_ct, hsd_len, hsd_s0, hsd_pr⟩
          · have hl1_eq_not : l1 = not_lit := by simpa [l1] using hc
            s13_hstraight; exact hJ119 () mc ⟨hmc, Or.inr hl1_eq_not⟩
        · have hl0_eq_not : l0 = not_lit := by simpa [l0] using hc
          s13_hstraight; exact hJ119 () mc ⟨hmc, Or.inl hl0_eq_not⟩
  · intro J96 hJ96
    s13_hstraight
    s13_hsplit
    · have hw0_lt : w0.toNat < 2 * sem.core.cur_vars := by
        rw [htwo_cv] at hc; simpa [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)] using hc
      have hw0_vals_m : (BitVec.setWidth 64 w0).toNat <
          (fastPropMem s_disk sem).core.vals.length := by
        rw [BcpPropTactics.fastPropMem_vals, hvals_len, BitVec.toNat_setWidth,
          Nat.mod_eq_of_lt (by omega)]
        omega
      have hp1_ws' : (p + 1).toNat < (fastPropMem s_disk sem).core.wstk.length :=
        hp1_n ▸ hp1_ws
      s13_hsplit
      · have hq_ws' : q.toNat < (fastPropMem s_disk sem).core.wstk.length := hq_ws
        s13_hstraight
        try simp only [@hcr_eq'] at hm ⊢
        rw [BcpPropTactics.fastPropMem_wstk] at hm
        let sem_k : FullState := {
          core := { sem.core with
            wstk := (sem.core.wstk.set q.toNat w0).set (q + 1#64).toNat cref },
          scratch := sem.scratch }
        have hkeep : PropLitInv c F0 F_cur
            { s_pi0 with scratch := { s_pi0.scratch with delayed := del0 } }
            sem_k not_lit.toNat off_v.toNat (q + 2#64).toNat (p + 2#64).toNat end_v.toNat := by
          have hp2_m : (p.toNat + 2) % 2 ^ 64 = p.toNat + 2 := Nat.mod_eq_of_lt (by omega)
          have hq2_m : (q.toNat + 2) % 2 ^ 64 = q.toNat + 2 := Nat.mod_eq_of_lt (by omega)
          have h1 := propLit_inv_keep_large (hp2_n ▸ hpi_drop) hnot_lt hq_le
            (by rw [hwstk_len]; omega) (by rw [hwstk_len]; omega) hw0_msb hcr_31 hcr_ref
          simpa [sem_k, hq1_n, hq2_n, hq2_m, hp2_n, hp2_m] using h1
        have hdel_k : Spec.DelayedWatchesOk sem_k.core del0 dlen not_lit.toNat := by
          intro j hj
          simpa [Spec.DelayedWatchesOk, sem_k, fullArenaClauseRefsCore] using hdel_ok j hj
        have hq1_m : (q.toNat + 1) % 2 ^ 64 = q.toNat + 1 := Nat.mod_eq_of_lt (by omega)
        refine hJ_lp _ _ _ _ _ _ _ sem_k _ ?_ rfl
        exact ⟨del0, dlen, by simpa [fastPropMem, sem_k, hq1_n, hq1_m] using hm, hkeep, hdel_k,
          hdel_eq, by simpa [sem_k] using hte, rfl, rfl, hdi_eq, hdlen_le,
          by simpa [sem_k] using hs0_cv, by simpa [sem_k] using hs0_pr, hs0_dl, hs0_tk,
          by simpa [sem_k] using hs0_oom, by simpa [sem_k] using hs0_ct, hsd_len, hsd_s0,
          by simpa [sem_k] using hsd_pr⟩
      · s13_hstraight; exact hJ96 () m hm
    · s13_hstraight; exact hJ96 () m hm

theorem s13_lp_loop_wp {isBeyond : Bool} {Γ : Env} {rs : List Ty} {c : FullCfg}
    {F0 : CNF Nat} {F_cur : List (List Nat)} {ignore_ref : BitVec 64}
    {ignore_arg : Arg Val i64} {s_disk s_pi0 sem0 : FullState}
    {cur_lvl32 not_lit nl_lvl : BitVec 32}
    {two_cv te0 un0 uf0 tk0 p0 q0 end_v di0 dlim off_v brk0 : BitVec 64}
    {brk_arg : Arg Val i64} {rec_ph nonchrono : Bool}
    {R : Mem 64 → Prop} {m0 : Mem 64} {Q : Post rs} {X : XPost}
    {J_ovf : Cont (s13OvfSig isBeyond)}
    (hign_eval : ignore_arg = Arg.imm ignore_ref ∨ ignore_arg = Arg.var ignore_ref)
    (hbrk_eval : brk_arg = Arg.imm brk0 ∨ brk_arg = Arg.var brk0)
    (hinv0 : S13LpInv c F0 F_cur s_disk s_pi0 sem0 sem0 not_lit off_v end_v
      te0 un0 uf0 tk0 p0 q0 di0 m0 R)
    (hnot_lt : not_lit.toNat < 2 * sem0.core.cur_vars)
    (htwo_cv : two_cv.toNat = 2 * sem0.core.cur_vars)
    (hcur_lvl : cur_lvl32.toNat = sem0.core.cur_level)
    (hnl : ∀ k : FullCoreState, FullTrailExt s_pi0.core k →
      k.lvl[not_lit.toNat / 2]?.getD 0#32 = nl_lvl)
    (hdlim : dlim.toNat = 3 * c.delayed_cap)
    (hbrk0 : brk0 = 0#64)
    (hJ_ovf : ∀ (xs : Tup Val (s13OvfSig isBeyond)) (m' : Mem 64),
      S13OvfExitPred isBeyond c F0 F_cur ignore_ref s_disk s_pi0 sem0
        not_lit off_v end_v brk0 R xs m' →
      p0.toNat ≤ (s13OvfP xs).toNat →
      (s13OvfFlag xs = true → p0.toNat < (s13OvfP xs).toNat) →
      J_ovf xs m') :
    wp Γ Q X (s13LpLoopExpr isBeyond c.hdr ignore_arg c.pVals c.pWstk c.pArena c.pLevel
      c.pReason c.pTrail c.pTrailPos c.pFlags c.pPhases c.pDelayed dlim two_cv cur_lvl32
      rec_ph nonchrono not_lit nl_lvl te0 un0 uf0 tk0 p0 q0 end_v di0 brk_arg J_ovf) m0 := by
  have hwcap : c.wcap < 2 * dimacsBound := c.hwcap
  have hdim : dimacsBound = 268435456 := rfl
  unfold dimacsBound at hwcap
  dsimp only [s13LpLoopExpr]
  refine wp_loop_group (fun n (xs : Tup Val s13LpSig) m' =>
    ∃ sem', n = end_v.toNat - xs.2.2.2.2.1.toNat ∧ p0.toNat ≤ xs.2.2.2.2.1.toNat ∧
      S13LpInv c F0 F_cur s_disk s_pi0 sem0 sem' not_lit off_v end_v
        xs.1 xs.2.1 xs.2.2.1 xs.2.2.2.1 xs.2.2.2.2.1 xs.2.2.2.2.2.1 xs.2.2.2.2.2.2.1 m' R)
    ?_ ?_
  · intro J0 n ⟨te, un, uf, tk, p, q, di, ⟨⟩⟩ m' ih ⟨sem, hn_eq, hp0_le, hinv⟩
    dsimp only at hn_eq hp0_le hinv
    subst hn_eq
    rcases hinv with ⟨del, dlen, hm, hpi, hdel_ok, hdel_eq, hte, rfl, rfl, hdi_eq, hdlen_le,
      hs0_cv, hs0_pr, hs0_dl, hs0_tk, hs0_oom, hs0_ct, hsd_len, hsd_s0, hsd_pr⟩
    have hinv_re : S13LpInv c F0 F_cur s_disk s_pi0 sem0 sem not_lit off_v end_v
        te sem.core.unassigned sem.core.unflushed tk p q di m' R :=
      ⟨del, dlen, hm, hpi, hdel_ok, hdel_eq, hte, rfl, rfl, hdi_eq, hdlen_le,
        hs0_cv, hs0_pr, hs0_dl, hs0_tk, hs0_oom, hs0_ct, hsd_len, hsd_s0, hsd_pr⟩
    have hnot_p : not_lit.toNat < 2 * sem.core.cur_vars := hs0_cv.symm ▸ hnot_lt
    have htwo_p : two_cv.toNat = 2 * sem.core.cur_vars := by rw [htwo_cv, hs0_cv]
    have hcl_eq : sem.core.cur_level = sem0.core.cur_level := by
      rcases hinv0 with ⟨_, _, _, hpi0, _⟩
      have h1 := hpi.ag.get FullCoreState.cur_level
      have h2 := hpi0.ag.get FullCoreState.cur_level
      dsimp only at h1 h2
      exact h1.trans h2.symm
    s13_hstraight
    s13_hsplit
    · have hp_lt : p.toNat < end_v.toNat := hc
      have ⟨hend_le, hwlen_le⟩ := hpi.end_lt_wcap hnot_p
      have hp_ws : p.toNat < (fastPropMem s_disk sem).core.wstk.length := by
        rw [BcpPropTactics.fastPropMem_wstk, hpi.len.core_ok.wstk_len_arr]
        exact Nat.lt_of_lt_of_le hp_lt (Nat.le_trans hend_le hwlen_le)
      have hw0_raw : p.toNat < sem.core.wstk.length := by
        rw [hpi.len.core_ok.wstk_len_arr]
        exact Nat.lt_of_lt_of_le hp_lt (Nat.le_trans hend_le hwlen_le)
      let w0 := (fastPropMem s_disk sem).core.wstk[p.toNat]'hp_ws
      have hw0_get : sem.core.wstk[p.toNat]? = some w0 := by
        simpa only [w0, fc_getElem_wstk s_disk sem hp_ws hw0_raw] using
          List.getElem?_eq_getElem hw0_raw
      have hnl_p := hnl sem.core hpi.tr
      s13_hstraight
      s13_hsplit
      · have hp1_n : (p + 1#64).toNat = p.toNat + 1 := m7_bv64_add1_toNat (by omega)
        exact s13_lp_bin_wp hinv_re hnot_p hnl_p hp_lt hw0_get (by simpa [w0] using hc) hbrk0
          (fun te' un' uf' tk' p' q' di' sem' m'' hinv' hp' => by
            subst hp'
            exact ih (end_v.toNat - (p + 1#64).toNat)
              (te', un', uf', tk', p + 1#64, q', di', ()) m'' (by rw [hp1_n]; omega)
              ⟨sem', rfl, by rw [hp1_n]; omega, hinv'⟩)
          (fun xs m'' hexit hp' =>
            hJ_ovf xs m'' hexit (by rw [hp', hp1_n]; omega)
              (fun _ => by rw [hp', hp1_n]; omega))
      · have hw0_msb : w0 &&& 2147483648#32 = 0#32 := hc
        have hp2_n : (p + 2#64).toNat = p.toNat + 2 := m7_bv64_add2_toNat (by omega)
        exact s13_lp_large_step_wp hign_eval hbrk_eval hinv_re hnot_p htwo_p
          (by rw [hcur_lvl, hcl_eq]) hnl_p hdlim hp_lt hw0_get hw0_msb hbrk0
          (fun te' un' uf' tk' p' q' di' sem' m'' hinv' hp' => by
            subst hp'
            have ⟨_, _, _, hpi', _⟩ := hinv'
            have hp2_end := hpi'.sw.p_le_end
            rw [hp2_n] at hp2_end
            exact ih (end_v.toNat - (p + 2#64).toNat)
              (te', un', uf', tk', p + 2#64, q', di', ()) m'' (by rw [hp2_n]; omega)
              ⟨sem', rfl, by rw [hp2_n]; omega, hinv'⟩)
          (fun xs m'' hexit hp' =>
            hJ_ovf xs m'' hexit (by rw [hp', hp2_n]; omega)
              (fun _ => by rw [hp', hp2_n]; omega))
    · have hp_end : p = end_v :=
        BitVec.eq_of_toNat_eq (Nat.le_antisymm hpi.sw.p_le_end (Nat.le_of_not_lt hc))
      cases isBeyond <;> rcases hbrk_eval with rfl | rfl <;>
        · s13_hstraight
          refine hJ_ovf _ m' ?_ hp0_le (fun h => Bool.noConfusion h)
          exact ⟨sem, del, dlen, hm, hpi, hdel_ok, hdel_eq,
            (by simpa only [Arg.val] using hte : sem.core.trail_end = (Arg.var te).val.toNat),
            rfl, rfl, hdi_eq, hdlen_le, hs0_cv, hs0_pr, hs0_dl, hs0_tk, hs0_oom, hsd_len, hsd_s0,
            hsd_pr, by simpa [hbrk0] using And.intro hp_end hs0_ct⟩
  · intro J0 hP0
    s13_hstraight
    exact hP0 (end_v.toNat - p0.toNat) (te0, un0, uf0, tk0, p0, q0, di0, ()) m0
      ⟨sem0, rfl, Nat.le_refl _, hinv0⟩

end LeanQbe.T.Examples.Kissat.Proof.PropSearch
