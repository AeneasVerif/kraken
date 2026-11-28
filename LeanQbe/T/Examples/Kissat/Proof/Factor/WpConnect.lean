/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.Src.Factor
public import LeanQbe.T.Examples.Kissat.Proof.Factor.Spec
public import LeanQbe.T.Examples.Kissat.Proof.Forward.Spec
import LeanQbe.T.Examples.Kissat.Proof.Factor.Helpers
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena
import LeanQbe.T.Examples.Kissat.Proof.Spec.Arena1
import LeanQbe.T.Examples.Kissat.Proof.Spec.Contracts4
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics
import LeanQbe.T.Examples.Kissat.Proof.Spec.Tactics1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Clause-Connection WP Proof for `Src.Factor` (`full_bva_connect_clauses_fid`)

Proves `full_bva_connect_clauses_fid_wp` (`fidBvaConnectClausesSpec`) using
`Forward.Spec.fullFwdFlushLargeM7Spec`, `Arena.Spec.fullArenaNextSpec`,
`Watch.Spec.fullWatchPushSpec`, and `full_bva_count_lit_deg_fid_wp` (`0` legacy imports,
`0` placeholders, `XPost`-polymorphic).
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
open LeanQbe.T.Examples.Kissat.Proof.Factor.Spec

open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullArenaTactics
open scoped LeanQbe.T.Examples.Kissat.Proof.Spec.FullBvaHeapTactics

section ConnHelpers

private def ConnStateOk (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s0 st : FullState) : Prop :=
  FullDenseInvW c F0 F_cur st ∧
  st.core.cur_vars = s0.core.cur_vars ∧
  st.core.fuel = s0.core.fuel ∧
  st.core.arena = s0.core.arena ∧
  st.core.arena_len = s0.core.arena_len ∧
  st.scratch.scratch_buf = s0.scratch.scratch_buf

private def connSetScr (st : FullState) (tm ws1 ws2 : List (BitVec 32)) : FullState :=
  { st with scratch :=
    { st.scratch with tarjan_mark := tm, work_stk1 := ws1, work_stk2 := ws2 } }

private theorem connStateOk_set_scr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} (h : ConnStateOk c F0 F_cur s0 st) {tm ws1 ws2 : List (BitVec 32)}
    (htm : tm.length = 2 * c.max_vars) (hws1 : ws1.length = 2 * c.max_vars)
    (hws2 : ws2.length = 2 * c.max_vars) :
    ConnStateOk c F0 F_cur s0 (connSetScr st tm ws1 ws2) :=
  ⟨fullDenseInvW_set_scr_arrs h.1 htm hws1 hws2, h.2⟩

private theorem connStateOk_set_repr {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} (h : ConnStateOk c F0 F_cur s0 st) {rp : List (BitVec 32)}
    (hrp : rp.length = 2 * c.max_vars) :
    ConnStateOk c F0 F_cur s0 { st with core := { st.core with repr := rp } } :=
  ⟨fullDenseInvW_set_repr h.1 hrp, h.2⟩

private theorem connStateOk_set_oom {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s0 st : FullState} (h : ConnStateOk c F0 F_cur s0 st) (v : BitVec 64) :
    ConnStateOk c F0 F_cur s0 { st with core := { st.core with oom := v } } :=
  ⟨fullDenseInvW_set_oom h.1 v, h.2⟩

private theorem conn_zero_mem_refs {c : FullCfg} {F_cur : List (List Nat)} {k : FullCoreState}
    (ha : FullArenaClausesInv c F_cur k) (hpos : 0 < k.arena_len) :
    0 ∈ fullArenaClauseRefsCore k := by
  have hlen_ok : 3 ≤ k.arena_len := by
    rcases ha.len_ok with h0 | h3
    · omega
    · exact h3
  unfold fullArenaClauseRefsCore
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k.arena_len ≠ 0)
  rw [hm]
  unfold fullArenaScanRefs
  have h3m : 0 + 3 ≤ m + 1 := by omega
  simp [h3m]

private theorem conn_next_ref {c : FullCfg} {F_cur : List (List Nat)} {k : FullCoreState}
    (ha : FullArenaClausesInv c F_cur k) {p : BitVec 64}
    (_hp_lt : p.toNat < k.arena_len) (hp_ref : p.toNat ∈ fullArenaClauseRefsCore k)
    (hal_lt : k.arena_len < 2 ^ 31) :
    let np32 := BitVec.ofNat 32 (fullArenaNextOff k.arena k.arena_len p.toNat)
    let np := BitVec.setWidth 64 np32
    p.toNat < np.toNat ∧ np.toNat ≤ k.arena_len ∧
    (np.toNat < k.arena_len → np.toNat ∈ fullArenaClauseRefsCore k) := by
  have hwf := ha.refs_wf p.toNat hp_ref
  have hbd := fullArenaNextOff_bounds (ar := k.arena) (alen := k.arena_len) (cref := p.toNat)
    hwf.1
  have hmem := fullArenaClauseRefs_next_mem ha hp_ref
  have hnp_nat : (BitVec.setWidth 64
      (BitVec.ofNat 32 (fullArenaNextOff k.arena k.arena_len p.toNat))).toNat =
      fullArenaNextOff k.arena k.arena_len p.toNat := by
    rw [fid_bv64_32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  dsimp only
  rw [hnp_nat]
  refine ⟨hbd.1, hbd.2, fun hlt => ?_⟩
  rcases hmem with heq | hmem'
  · omega
  · exact hmem'

private theorem conn_clause_lit_lt {c : FullCfg} {F_cur : List (List Nat)} {k : FullCoreState}
    (ha : FullArenaClausesInv c F_cur k) (hal_arr : k.arena.length = c.arena_cap)
    (hal_le : k.arena_len ≤ c.arena_cap) {p : BitVec 64} {j : BitVec 32}
    (hp_ref : p.toNat ∈ fullArenaClauseRefsCore k) (hng : fullArenaClauseGarbCore k p.toNat = false)
    (hj_lt : j.toNat < fullArenaClauseSizeCore k p.toNat) :
    (k.arena[p.toNat + 3 + j.toNat]'(by
      have hwf := ha.refs_wf p.toNat hp_ref; omega)).toNat < 2 * k.cur_vars := by
  have hwf := ha.refs_wf p.toNat hp_ref
  have hlt := ha.lits_lt p.toNat hp_ref hng _ (List.mem_of_getElem?
    (fullArenaClauseLitsCore_getElem hj_lt (by omega)))
  exact hlt

private theorem conn_bv32_garb_false_of_and_480000 {k : FullCoreState} {p : Nat}
    (hp_lt : p < k.arena.length)
    (hand : (k.arena[p]'hp_lt &&& 0x00480000#32) = 0#32) :
    fullArenaClauseGarbCore k p = false := by
  unfold fullArenaClauseGarbCore fullArenaHdrCore
  rw [List.getElem?_eq_getElem hp_lt, Option.getD_some]
  simp [fid_bv32_garb_zero_of_and_480000 hand]

private def cDummyV : (t : Ty) → Val t
  | .bits _ => 0 | .bool => true | .float _ => 0 | .pair a b => (cDummyV a, cDummyV b)
private def cDummyT : (ts : List Ty) → Tup Val ts
  | [] => () | t :: ts => (cDummyV t, cDummyT ts)
private def cStep {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .let_ (Op.mk (.copy _) (a, ())) k => k (a.val, ())
  | .let_ (Op.mk (.zext _ m) (a, ())) k => k (BitVec.setWidth m a.val, ())
  | .let_ (Op.mk (.sext _ m) (a, ())) k => k (BitVec.signExtend m a.val, ())
  | .let_ (Op.mk (.add (.bits 64)) (a, b, ())) k => k (a.val + b.val, ())
  | .let_ (Op.mk (.shl (.bits 64)) (a, b, ())) k => k (a.val <<< b.val, ())
  | .let_ (ts := ts) _ k => k (cDummyT ts)
  | .load t _ k => k (cDummyV t)
  | .store _ _ k => k
  | .call (bs := bs) _ _ k => k (cDummyT bs)
  | e => e
private def cSteps {rs : List Ty} : Nat → Expr Val Cont rs → Expr Val Cont rs
  | 0, e => e | n + 1, e => cSteps n (cStep e)
private def cLd64 {rs : List Ty} (v : Val i64) : Expr Val Cont rs → Expr Val Cont rs
  | .load (.bits 64) _ k => k v | _ => .hlt
private def cElse {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs
  | .jnz _ _ e => e | _ => .hlt
private def cSkipL1At {rs : List Ty} (v : BitVec 64) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 64]]) bs _ =>
    match bs ((fun _ _ => True), ()) with
    | .cons f .nil => (cStep (f (v, ()))) |> cElse
  | _ => .hlt
private def cSkipL1 {rs : List Ty} : Expr Val Cont rs → Expr Val Cont rs := cSkipL1At 0#64
private def cSkipL3 {rs : List Ty} (p ca : BitVec 64) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 64, .bits 64]]) bs _ =>
    match bs ((fun _ _ => True), ()) with
    | .cons f .nil => (cSteps 3 (f (p, ca, ()))) |> cElse
  | _ => .hlt

private theorem conn_bv64_ushr1_lt {x : BitVec 64} {n : Nat} (hx : x.toNat < 2 * n) :
    (x >>> BitVec.signExtend 64 (1 : BitVec 32)).toNat < n := by
  rw [show BitVec.signExtend 64 (1 : BitVec 32) = 1#64 from rfl]
  change (x >>> (1 : Nat)).toNat < n
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
  omega

private theorem conn_bv64_shl1_eq {x : BitVec 64} {n : Nat} (hx : x.toNat < 2 * n)
    (hn : 4 * n < 2 ^ 64) :
    (x <<< BitVec.signExtend 64 (1 : BitVec 32)).toNat = 2 * x.toNat := by
  rw [show BitVec.signExtend 64 (1 : BitVec 32) = 1#64 from rfl]
  change (x <<< (1 : Nat)).toNat = 2 * x.toNat
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one, Nat.mod_eq_of_lt (by omega)]
  omega

private def connInitExpr (h cv tm ws1 ws2 wv ws ar fl va rp : BitVec 64) : Expr Val Cont [] :=
  full_bva_connect_clauses_fid_body (V := Val) (L := Cont) (h, ())
    |> cSteps 2
    |> cLd64 cv |> cSteps 3
    |> cLd64 tm |> cStep
    |> cLd64 ws1 |> cStep
    |> cLd64 ws2 |> cStep
    |> cLd64 wv |> cStep
    |> cLd64 ws |> cStep
    |> cLd64 ar |> cStep
    |> cLd64 fl |> cStep
    |> cLd64 va |> cStep
    |> cLd64 rp

private def connL2Expr (h cv tm ws1 ws2 wv ws ar fl va rp : BitVec 64) : Expr Val Cont [] :=
  connInitExpr h cv tm ws1 ws2 wv ws ar fl va rp |> cSkipL1

private def connL3Expr (h cv tm ws1 ws2 wv ws ar fl va rp ci : BitVec 64) : Expr Val Cont [] :=
  connL2Expr h cv tm ws1 ws2 wv ws ar fl va rp |> cSkipL1At ci

private def connL4Expr (h cv tm ws1 ws2 wv ws ar fl va rp ci pL3 caL3 : BitVec 64) :
    Expr Val Cont [] :=
  connL3Expr h cv tm ws1 ws2 wv ws ar fl va rp ci |> cSkipL3 pL3 caL3

private def connL56Expr (h cv tm ws1 ws2 wv ws ar fl va rp x0 x1 x2 : BitVec 64)
    (x3 : BitVec 32) : Expr Val Cont [] :=
  match connL4Expr h cv tm ws1 ws2 wv ws ar fl va rp 0#64 0#64 0#64 with
  | .group (sig := [[.bits 64, .bits 64, .bits 64, .bits 32]]) bs _ =>
    match bs ((fun _ _ => True), ()) with
    | .cons f .nil => f (x0, x1, x2, x3, ())
  | _ => .hlt

end ConnHelpers

section ConnSubProofs

private theorem conn_loop56_wp {Γ : Env} {Q : Post []} {X : XPost}
    (hNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hDeg : ∀ a m Q X, fidBvaCountLitDegSpec a m Q X →
      Γ "full_bva_count_lit_deg_fid" [i64, i32] [i32] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s0 st : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {x0 x1 x2 : BitVec 64} {x3 : BitVec 32}
    (hst : ConnStateOk c F0 F_cur s0 st) (hm : (FullMem c st ⋆ R) m)
    (hQ : ∀ s' m', ConnStateOk c F0 F_cur s0 s' → (FullMem c s' ⋆ R) m' → Q () m') :
    wp Γ Q X (connL56Expr c.hdr (BitVec.ofNat 64 st.core.cur_vars) c.pTarjanMark
      c.pWorkStk1 c.pWorkStk2 c.pWvec c.pWstk c.pArena c.pFlags c.pVals c.pRepr
      x0 x1 x2 x3) m := by
  have hmx := c.hmaxv; have har_b := c.harena; have hwcap := c.hwcap
  unfold dimacsBound at hmx har_b hwcap
  have hl0 := hst.1.1; have hcl0 := hl0.core_ok
  have hcv_le := hcl0.cur_vars_le; have hal_le := hcl0.arena_len_le
  have hnl_eq : (BitVec.ofNat 64 st.core.cur_vars <<< BitVec.signExtend 64 (1 : BitVec 32)).toNat =
      2 * st.core.cur_vars := by
    change (BitVec.ofNat 64 st.core.cur_vars <<< (1 : Nat)).toNat = _
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  unfold connL56Expr connL4Expr connL3Expr connL2Expr connInitExpr
  dsimp only [cSkipL1, cSkipL1At, cSkipL3, cSteps, cStep, cLd64, cElse, cDummyV, cDummyT]
  refine wp_while_state1 (α := BitVec 64 × FullState) (fun (p, _) => p)
    (fun (p, st5) => st5.core.arena_len - p.toNat)
    (fun (p, st5) mp =>
      ConnStateOk c F0 F_cur s0 st5 ∧ p.toNat ≤ st5.core.arena_len ∧
      (p.toNat < st5.core.arena_len → p.toNat ∈ fullArenaClauseRefsCore st5.core) ∧
      (FullMem c st5 ⋆ R) mp)
    (fun J5 hJ5 => by
      c0_hfast
      refine hJ5 (0#64, st) m ⟨hst, Nat.zero_le _, fun hpos =>
        conn_zero_mem_refs hst.1.2.1.arena hpos, hm⟩)
    (fun J5 (p, st5) m5 ⟨hst5, hp_le, hp_ref_f, hm5⟩ ih5 => ?_)
  have hsl5 := hst5.1.1; have hcl5 := hsl5.core_ok; have hw5 := hst5.1.2.1
  have hal5_le := hcl5.arena_len_le; have har5_len := hcl5.arena_len_arr
  refine wp_join_state0 (α := FullState)
    (fun st6 m6 => ConnStateOk c F0 F_cur s0 st6 ∧ (FullMem c st6 ⋆ R) m6)
    (fun _ st6 m6 ⟨hst6, hm6⟩ => by
      have hcv6 := hst6.1.1.core_ok.cur_vars_le
      c0_hfast_nogrp
      refine wp_while_state1 (α := BitVec 64 × FullState) (fun (dl, _) => dl)
        (fun (dl, _) => 2 * st6.core.cur_vars - dl.toNat)
        (fun (dl, stL) mL =>
          ConnStateOk c F0 F_cur s0 stL ∧ stL.core.cur_vars = st6.core.cur_vars ∧
          dl.toNat ≤ 2 * st6.core.cur_vars ∧ (FullMem c stL ⋆ R) mL)
        (fun J6 hJ6 => by
          c0_hfast; exact hJ6 (0#64, st6) m6 ⟨hst6, rfl, Nat.zero_le _, hm6⟩)
        (fun J6 (dl, stL) mL ⟨hstL, hcvL, hdl_le, hmL⟩ ih6 => ?_)
      have hrpL := hstL.1.1.core_ok.repr_len
      c0_hfast
      · have hdl_lt : dl.toNat < 2 * st6.core.cur_vars := by
          rw [hnl_eq, hst.2.1, ← hst6.2.1] at hc; exact hc
        have hdl32 : (BitVec.setWidth 32 dl).toNat = dl.toNat := by c0_bound
        fid_call hDeg
        refine ⟨c, F0, F_cur, stL, R, rfl, hstL.1, ?_, hmL, fun degv => ?_⟩
        · change (BitVec.setWidth 32 dl).toNat < 2 * stL.core.cur_vars
          rw [hdl32, hcvL]; exact hdl_lt
        have hdl1 : (dl + 1#64).toNat = dl.toNat + 1 := by c0_bound
        have hdl_rp : dl.toNat < stL.core.repr.length := by rw [hrpL]; omega
        c0_hfast
        let stL' : FullState :=
          { stL with core := { stL.core with repr := stL.core.repr.set dl.toNat degv } }
        exact ih6 (dl + 1#64, stL') _ (by dsimp only; rw [hdl1]; omega)
          ⟨connStateOk_set_repr hstL (by simp [hrpL]), hcvL, by rw [hdl1]; omega, by assumption⟩
      · c0_hfast; exact hQ stL mL hstL hmL)
    (fun Jexit hJexit => by
      c0_hfast_nogrp
      rotate_left 1
      · c0_hfast; exact hJexit st5 m5 ⟨hst5, hm5⟩
      · c0_hfast; exact hJexit st5 m5 ⟨hst5, hm5⟩
      have hp_lt : p.toNat < st5.core.arena_len := by c0_bound
      have hp_ref : p.toNat ∈ fullArenaClauseRefsCore st5.core := hp_ref_f hp_lt
      have hwf := hw5.arena.refs_wf p.toNat hp_ref
      have hp2_mod : (p.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 = p.toNat + 2 := by
        rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl]; omega
      have hp32 : (BitVec.setWidth 32 p).toNat = p.toNat := by c0_bound
      c0_hfast_nogrp
      fid_call hNext
      refine ⟨c, st5, R, rfl, hsl5, hm5, ?_⟩
      dsimp only
      c0_hfast_nogrp
      let np32 := BitVec.ofNat 32 (fullArenaNextOff st5.core.arena st5.core.arena_len p.toNat)
      let np := BitVec.setWidth 64 np32
      have hnxt := conn_next_ref hw5.arena hp_lt hp_ref (by omega)
      refine wp_join0 (fun mnext => ∃ st', ConnStateOk c F0 F_cur s0 st' ∧
          st'.core.arena = st5.core.arena ∧ st'.core.arena_len = st5.core.arena_len ∧
          (FullMem c st' ⋆ R) mnext)
        (fun _ mnext ⟨st', hst', har', hal', hmn⟩ => by
          c0_hfast
          change J5 (BitVec.setWidth 64 (BitVec.ofNat 32
            (fullArenaNextOff st5.core.arena st5.core.arena_len
              (BitVec.setWidth 32 p).toNat)), ()) mnext
          rw [hp32]
          have hnxt' : np.toNat ≤ st'.core.arena_len ∧
              (np.toNat < st'.core.arena_len → np.toNat ∈ fullArenaClauseRefsCore st'.core) := by
            unfold fullArenaClauseRefsCore; rw [har', hal']; exact hnxt.2
          exact ih5 (np, st') mnext
            (by dsimp only; rw [hal']; exact Nat.sub_lt_sub_left hp_lt hnxt.1)
            ⟨hst', hnxt'.1, hnxt'.2, hmn⟩)
        (fun Jnxt hJnxt => by
          have hsz_eq : (st5.core.arena[p.toNat + 2]'(by omega)).toNat =
              fullArenaClauseSizeCore st5.core p.toNat := by
            unfold fullArenaClauseSizeCore
            rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
          have hsz_mod : (st5.core.arena[(p.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
              simp only [hp2_mod]; omega)).toNat = fullArenaClauseSizeCore st5.core p.toNat := by
            simp only [hp2_mod]; exact hsz_eq
          c0_hfast_nogrp
          rotate_left 1
          · c0_hfast; exact hJnxt m5 ⟨st5, hst5, rfl, rfl, hm5⟩
          c0_hfast_nogrp
          rotate_left 1
          · c0_hfast; exact hJnxt m5 ⟨st5, hst5, rfl, rfl, hm5⟩
          have hsz_ge3 : 3 ≤ fullArenaClauseSizeCore st5.core p.toNat := by
            rw [← hsz_mod]; exact by assumption
          c0_hfast_nogrp
          rotate_left 1
          · c0_hfast; exact hJnxt m5 ⟨st5, hst5, rfl, rfl, hm5⟩
          have hsz_le5 : fullArenaClauseSizeCore st5.core p.toNat ≤ 5 := by
            rw [← hsz_mod]; exact by assumption
          c0_hfast_nogrp
          refine wp_while_break_state (β := Bool × BitVec 32) (α := BitVec 32)
                (fun (kp, k) => (kp, k, ()))
                (fun (_, k) mk => k.toNat ≤ fullArenaClauseSizeCore st5.core p.toNat ∧
                  (FullMem c st5 ⋆ R) mk)
                (fun k => (k, ()))
                (fun k => fullArenaClauseSizeCore st5.core p.toNat - k.toNat)
                (fun k mk => k.toNat ≤ fullArenaClauseSizeCore st5.core p.toNat ∧
                  (FullMem c st5 ⋆ R) mk)
                (fun Jbrk_out (_kp, _k) mk ⟨_, hmk⟩ => by
                  c0_hfast_nogrp
                  refine wp_join_state1 (α := BitVec 32 × FullState) (fun (k2, _) => k2)
                    (fun (_, stp) mp2 =>
                      ConnStateOk c F0 F_cur s0 stp ∧ stp.core.arena = st5.core.arena ∧
                      stp.core.arena_len = st5.core.arena_len ∧ (FullMem c stp ⋆ R) mp2)
                    (fun _ (_k2, _stp) mp2 ⟨hst_o, har_o, hal_o, hmp2⟩ => by
                      c0_hfast; exact hJnxt mp2 ⟨_stp, hst_o, har_o, hal_o, hmp2⟩)
                    (fun Jpush_out hJpush_out => by
                      c0_hfast_nogrp
                      · refine wp_while_break_state (β := BitVec 32 × FullState)
                          (α := BitVec 32 × FullState)
                          (fun (k2, _) => (k2, ()))
                          (fun (_, stp) mp2 =>
                            ConnStateOk c F0 F_cur s0 stp ∧ stp.core.arena = st5.core.arena ∧
                            stp.core.arena_len = st5.core.arena_len ∧ (FullMem c stp ⋆ R) mp2)
                          (fun (k2, _) => (k2, ()))
                          (fun (k2, _) => fullArenaClauseSizeCore st5.core p.toNat - k2.toNat)
                          (fun (k2, stp) mp2 =>
                            ConnStateOk c F0 F_cur s0 stp ∧ stp.core.arena = st5.core.arena ∧
                            stp.core.arena_len = st5.core.arena_len ∧
                            stp.core.cur_vars = st5.core.cur_vars ∧
                            k2.toNat ≤ fullArenaClauseSizeCore st5.core p.toNat ∧
                            (FullMem c stp ⋆ R) mp2)
                          (fun _ _ mp2 hI => by c0_hfast; exact hJpush_out (_, _) mp2 hI)
                          (fun Jp_brk Jp (k2, stp) mp2 hBp ihp
                            ⟨hstp, har_p, hal_p, hcv_p, hk2_le, hmp2⟩ => by
                            have hsl_p := hstp.1.1; have hcl_p := hsl_p.core_ok
                            have hw_p := hstp.1.2.1; have hdw_p := m6_denseWatchesInv_of_w hstp.1
                            have har_pl := hcl_p.arena_len_arr
                            have hp_ref_p : p.toNat ∈ fullArenaClauseRefsCore stp.core := by
                              unfold fullArenaClauseRefsCore; rw [har_p, hal_p]; exact hp_ref
                            c0_hfast_nogrp
                            · have hk2_lt : k2.toNat <
                                  fullArenaClauseSizeCore st5.core p.toNat := by
                                rw [← hsz_mod]; exact by assumption
                              have hk2_idx : (p + 3#64 + BitVec.setWidth 64 k2).toNat =
                                  p.toNat + 3 + k2.toNat := by c0_bound
                              have hk2_lt_ar : (p + 3#64 + BitVec.setWidth 64 k2).toNat <
                                  stp.core.arena.length := by rw [hk2_idx, har_pl]; omega
                              c0_hfast_nogrp
                              let sz_bv := st5.core.arena[p.toNat + 2]'(by omega)
                              have hsz_bv_nat : sz_bv.toNat =
                                  fullArenaClauseSizeCore st5.core p.toNat := by
                                dsimp only [sz_bv]; exact hsz_eq
                              have hsz_and_lt : (sz_bv &&& 0x7FFFFFFF#32).toNat < 2 ^ 31 :=
                                fid_bv32_and_7fff_lt sz_bv
                              have hsz_and_ne : (sz_bv &&& 0x7FFFFFFF#32) ≠ 0xFFFFFFFF#32 :=
                                fid_bv32_ne_sent hsz_and_lt
                              have hsz_and_ge3 : 3 ≤ (sz_bv &&& 0x7FFFFFFF#32).toNat := by
                                have heq : (sz_bv &&& 0x7FFFFFFF#32).toNat = sz_bv.toNat := by
                                  rw [BitVec.toNat_and,
                                    show (0x7FFFFFFF#32 : BitVec 32).toNat = 2 ^ 31 - 1 from rfl,
                                    Nat.and_two_pow_sub_one_eq_mod,
                                    Nat.mod_eq_of_lt (by rw [hsz_bv_nat]; omega)]
                                rw [heq, hsz_bv_nat]; exact hsz_ge3
                              have hsz_and_nbin :
                                  ((sz_bv &&& 0x7FFFFFFF#32) &&& 0x80000000#32) = 0#32 :=
                                fid_bv32_bin_flag_zero_of_lt hsz_and_lt
                              have hp32_lt : (BitVec.setWidth 32 p).toNat < 2 ^ 31 := by
                                rw [hp32]; omega
                              have hp32_ne : BitVec.setWidth 32 p ≠ 0xFFFFFFFF#32 :=
                                fid_bv32_ne_sent hp32_lt
                              have hp32_ref :
                                  (BitVec.setWidth 32 p).toNat ∈ fullArenaClauseRefs stp := by
                                rw [hp32]; exact hp_ref_p
                              have hp2_ar_eq : st5.core.arena[(p + 2).toNat]'(by
                                  have h1 : (p + 2).toNat = p.toNat + 2 := by c0_bound
                                  rw [h1, har5_len]; omega) = sz_bv := by
                                have h1 : (p + 2).toNat = p.toNat + 2 := by c0_bound
                                dsimp only [sz_bv]; simp only [h1]
                              fid_call hPush
                              refine ⟨c, stp, R, rfl, hsl_p, hdw_p.layout,
                                fun h => absurd h (by decide), ?_, hmp2,
                                fun ok wvec' wstk' wlen' wu' wsort' mp3 hlp3 hlay3
                                  h2_1 h2_2 h3 hmp3 => ?_⟩
                              · intro _; dsimp only; rw [hp2_ar_eq]; exact ⟨hsz_and_ne, hp32_ne⟩
                              let stp' : FullState :=
                                { stp with
                                  core := { stp.core with
                                    wvec := wvec', wstk := wstk', wlen := wlen', wusable := wu' }
                                  scratch := { stp.scratch with wsort := wsort' } }
                              have hinv' : FullDenseInvW c F0 F_cur stp' :=
                                m6_fullDenseInvW_of_watchPush_occ hstp.1 hlp3 hlay3 hsz_and_nbin
                                  hsz_and_ge3 hp32_lt hp32_ref h2_1
                                  (fun ht => by
                                    have hok := h2_2 ht
                                    refine ⟨hok.1, hok.2.2.1, hok.2.2.2.1, ?_,
                                      hok.2.2.2.2.2 rfl⟩
                                    have h4 := hok.2.2.2.2.1
                                    dsimp only at h4; rw [hp2_ar_eq] at h4; exact h4)
                                  (fun hf => (h3 hf).1)
                              have hstp' : ConnStateOk c F0 F_cur s0 stp' :=
                                ⟨hinv', hstp.2.1, hstp.2.2.1, hstp.2.2.2.1,
                                 hstp.2.2.2.2.1, hstp.2.2.2.2.2⟩
                              have hk21 : (k2 + 1#32).toNat = k2.toNat + 1 := by c0_bound
                              c0_hfast
                              · exact ihp (k2 + 1#32, stp') mp3 (by dsimp only; rw [hk21]; omega)
                                  ⟨hstp', har_p, hal_p, hcv_p, by rw [hk21]; omega, hmp3⟩
                              · exact hBp (k2, { stp' with core := { stp'.core with oom := 1#64 } })
                                  _ ⟨connStateOk_set_oom hstp' 1#64, har_p, hal_p, by assumption⟩
                            · c0_hfast; exact hBp (k2, stp) mp2 ⟨hstp, har_p, hal_p, hmp2⟩)
                          (fun _Jp_brk _Jp _hB hLp => by
                            c0_hfast; exact hLp (0#32, st5) mk ⟨hst5, rfl, rfl, rfl, Nat.zero_le _,
                              hmk⟩)
                      · c0_hfast; exact hJpush_out (_, st5) mk ⟨hst5, rfl, rfl, hmk⟩))
                (fun Jbrk_out Jk k mk hB ihk ⟨hk_le, hmk⟩ => by
                  have hk_idx : (p + 3#64 + BitVec.setWidth 64 k).toNat =
                      p.toNat + 3 + k.toNat := by
                    c0_bound
                  c0_hfast_nogrp
                  · have hk_lt : k.toNat < fullArenaClauseSizeCore st5.core p.toNat := by
                      rw [← hsz_mod]; exact by assumption
                    have hgarb : fullArenaClauseGarbCore st5.core p.toNat = false :=
                      conn_bv32_garb_false_of_and_480000 (by omega) (by assumption)
                    have hl_lt : (st5.core.arena[p.toNat + 3 + k.toNat]'(by omega)).toNat <
                        2 * st5.core.cur_vars :=
                      conn_clause_lit_lt hw5.arena har5_len hal5_le hp_ref hgarb hk_lt
                    have hcv5 := hcl5.cur_vars_le
                    have hl_sw_vals : (BitVec.setWidth 64
                        (st5.core.arena[(p + 3#64 + BitVec.setWidth 64 k).toNat]'(by
                          rw [hk_idx]; omega))).toNat < st5.core.vals.length := by
                      rw [fid_bv64_32, hcl5.vals_len]; simp only [hk_idx]; omega
                    have hl_sw_tm : (BitVec.setWidth 64
                        (st5.core.arena[(p + 3#64 + BitVec.setWidth 64 k).toNat]'(by
                          rw [hk_idx]; omega))).toNat < st5.scratch.tarjan_mark.length := by
                      rw [fid_bv64_32, hsl5.scratch_ok.tarjan_mark_len]; simp only [hk_idx]; omega
                    have hl_sw_ws1 : (BitVec.setWidth 64
                        (st5.core.arena[(p + 3#64 + BitVec.setWidth 64 k).toNat]'(by
                          rw [hk_idx]; omega))).toNat < st5.scratch.work_stk1.length := by
                      rw [fid_bv64_32, hsl5.scratch_ok.work_stk1_len]; simp only [hk_idx]; omega
                    have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
                    c0_hfast
                    · exact hB (false, k) mk ⟨hk_le, hmk⟩
                    · exact hB (false, k) mk ⟨hk_le, hmk⟩
                    · exact ihk (k + 1#32) mk (by rw [hk1]; omega)
                        ⟨by rw [hk1]; omega, hmk⟩
                  · c0_hfast; exact hB (true, k) mk ⟨hk_le, hmk⟩)
                (fun _Jk _Jk0 _hB hL => by
                  c0_hfast; exact hL 0#32 m5 ⟨Nat.zero_le _, hm5⟩)))

private theorem conn_loop4_wp {Γ : Env} {Q : Post []} {X : XPost}
    (hNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hDeg : ∀ a m Q X, fidBvaCountLitDegSpec a m Q X →
      Γ "full_bva_count_lit_deg_fid" [i64, i32] [i32] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s0 st : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {ci pL3 caL3 : BitVec 64}
    (hst : ConnStateOk c F0 F_cur s0 st) (hm : (FullMem c st ⋆ R) m)
    (hQ : ∀ s' m', ConnStateOk c F0 F_cur s0 s' → (FullMem c s' ⋆ R) m' → Q () m') :
    wp Γ Q X (connL4Expr c.hdr (BitVec.ofNat 64 st.core.cur_vars) c.pTarjanMark
      c.pWorkStk1 c.pWorkStk2 c.pWvec c.pWstk c.pArena c.pFlags c.pVals c.pRepr
      ci pL3 caL3) m := by
  have hmx := c.hmaxv; have har_b := c.harena; have hwcap := c.hwcap
  unfold dimacsBound at hmx har_b hwcap
  have hl0 := hst.1.1; have hcl0 := hl0.core_ok
  have hcv_le := hcl0.cur_vars_le; have hal_le := hcl0.arena_len_le
  have hnl_eq : (BitVec.ofNat 64 st.core.cur_vars <<< BitVec.signExtend 64 (1 : BitVec 32)).toNat =
      2 * st.core.cur_vars := by
    change (BitVec.ofNat 64 st.core.cur_vars <<< (1 : Nat)).toNat = _
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  unfold connL4Expr connL3Expr connL2Expr connInitExpr
  dsimp only [cSkipL1, cSkipL1At, cSkipL3, cSteps, cStep, cLd64, cElse, cDummyV, cDummyT]
  refine wp_while_break_state
    (β := FullState × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 32)
    (α := FullState × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 32)
    (fun (_, x0, x1, x2, rnd) => (x0, x1, x2, rnd, ()))
    (fun (sb, _, _, _, _) mb => ConnStateOk c F0 F_cur s0 sb ∧ (FullMem c sb ⋆ R) mb)
    (fun (_, x0, x1, x2, rnd) => (x0, x1, x2, rnd, ()))
    (fun (_, _, _, _, rnd) => 2 - rnd.toNat)
    (fun (sl, _, _, _, rnd) ml =>
      ConnStateOk c F0 F_cur s0 sl ∧ rnd.toNat ≤ 2 ∧ (FullMem c sl ⋆ R) ml)
    (fun _ (sb, x0', x1', x2', x3') mb ⟨hsb, hmb⟩ => by
      have h56 := conn_loop56_wp (X := X) hNext hPush hDeg (x0 := x0') (x1 := x1')
        (x2 := x2') (x3 := x3') hsb hmb hQ
      rw [hsb.2.1, ← hst.2.1] at h56
      unfold connL56Expr connL4Expr connL3Expr connL2Expr connInitExpr at h56
      dsimp only [cSkipL1, cSkipL1At, cSkipL3, cSteps, cStep, cLd64, cElse, cDummyV, cDummyT] at h56
      exact h56)
    (fun J4brk J4 (sl, x0, x1, x2, rnd) ml hB4 ih4 ⟨hsl, hrnd_le, hml⟩ => by
      c0_hfast_nogrp
      rotate_left 1
      · c0_hfast; exact hB4 (sl, x0, x1, x2, rnd) ml ⟨hsl, hml⟩
      · c0_hfast; exact hB4 (sl, x0, x1, x2, rnd) ml ⟨hsl, hml⟩
      have hrnd_lt : rnd.toNat < 2 := by assumption
      refine wp_while_state1 (α := BitVec 64 × FullState) (fun (ti, _) => ti)
        (fun (ti, _) => 2 * sl.core.cur_vars - ti.toNat)
        (fun (ti, stT) mt =>
          ConnStateOk c F0 F_cur s0 stT ∧ stT.core.cur_vars = sl.core.cur_vars ∧
          ti.toNat ≤ 2 * sl.core.cur_vars ∧ (FullMem c stT ⋆ R) mt)
        (fun JT hJT => by
          c0_hfast; exact hJT (0#64, sl) ml ⟨hsl, rfl, Nat.zero_le _, hml⟩)
        (fun JT (ti, stT) mt ⟨hstT, hcvT, hti_le, hmt⟩ ihT => ?_)
      have hslT := hstT.1.1; have hclT := hslT.core_ok; have hscT := hslT.scratch_ok
      have htmT := hscT.tarjan_mark_len; have hws1T := hscT.work_stk1_len
      have hws2T := hscT.work_stk2_len
      c0_hfast_nogrp
      · have hti_lt : ti.toNat < 2 * sl.core.cur_vars := by
          rw [hnl_eq, hst.2.1, ← hsl.2.1] at hc; exact hc
        have hti_ws2 : ti.toNat < stT.scratch.work_stk2.length := by
          rw [hws2T]; have := hclT.cur_vars_le; omega
        have hti1 : (ti + 1#64).toNat = ti.toNat + 1 := by c0_bound
        c0_hfast
        exact ihT (ti + 1#64, connSetScr stT stT.scratch.tarjan_mark
            stT.scratch.work_stk1 (stT.scratch.work_stk2.set ti.toNat 0#32)) _
          (by dsimp only; rw [hti1]; omega)
          ⟨connStateOk_set_scr hstT htmT hws1T (by simp [hws2T]), hcvT, by rw [hti1]; omega,
           by assumption⟩
      · c0_hfast
        refine wp_while_state (α := BitVec 64 × BitVec 64 × FullState)
          (fun (p, nc, _) => (p, nc, ()))
          (fun (p, _, stA) => stA.core.arena_len - p.toNat)
          (fun (p, nc, stA) ma =>
            ConnStateOk c F0 F_cur s0 stA ∧ p.toNat ≤ stA.core.arena_len ∧
            (p.toNat < stA.core.arena_len → p.toNat ∈ fullArenaClauseRefsCore stA.core) ∧
            (FullMem c stA ⋆ R) ma)
          (fun JA hJA => by
            c0_hfast
            exact hJA (0#64, 0#64, stT) mt ⟨hstT, Nat.zero_le _, fun hpos =>
              conn_zero_mem_refs hstT.1.2.1.arena hpos, hmt⟩)
          (fun JA (p, nc, stA) ma ⟨hstA, hp_le, hp_ref_f, hma⟩ ihA => ?_)
        have hslA := hstA.1.1; have hclA := hslA.core_ok; have hwA := hstA.1.2.1
        have halA_le := hclA.arena_len_le; have harA_len := hclA.arena_len_arr
        have hscA := hslA.scratch_ok
        c0_hfast_nogrp
        rotate_left 1
        · c0_hfast
          refine wp_while_state1 (α := BitVec 64 × FullState) (fun (ci, _) => ci)
            (fun (ci, _) => 2 * stA.core.cur_vars - ci.toNat)
            (fun (ci, stC) mc =>
              ConnStateOk c F0 F_cur s0 stC ∧ stC.core.cur_vars = stA.core.cur_vars ∧
              ci.toNat ≤ 2 * stA.core.cur_vars ∧ (FullMem c stC ⋆ R) mc)
            (fun JC hJC => by
              c0_hfast; exact hJC (0#64, stA) ma ⟨hstA, rfl, Nat.zero_le _, hma⟩)
            (fun JC (ci, stC) mc ⟨hstC, hcvC, hci_le, hmc⟩ ihC => ?_)
          have hslC := hstC.1.1; have hclC := hslC.core_ok; have hscC := hslC.scratch_ok
          have htmC := hscC.tarjan_mark_len; have hws1C := hscC.work_stk1_len
          have hws2C := hscC.work_stk2_len
          c0_hfast_nogrp
          · have hci_lt : ci.toNat < 2 * stA.core.cur_vars := by
              rw [hnl_eq, hst.2.1, ← hstA.2.1] at hc; exact hc
            have hci_ws1 : ci.toNat < stC.scratch.work_stk1.length := by
              rw [hws1C]; have := hclC.cur_vars_le; omega
            have hci_ws2 : ci.toNat < stC.scratch.work_stk2.length := by
              rw [hws2C]; have := hclC.cur_vars_le; omega
            have hci1 : (ci + 1#64).toNat = ci.toNat + 1 := by c0_bound
            c0_hfast
            exact ihC (ci + 1#64, connSetScr stC stC.scratch.tarjan_mark
                (stC.scratch.work_stk1.set ci.toNat (stC.scratch.work_stk2[ci.toNat]'hci_ws2))
                stC.scratch.work_stk2) _
              (by dsimp only; rw [hci1]; omega)
              ⟨connStateOk_set_scr hstC htmC (by simp [hws1C]) hws2C, hcvC, by rw [hci1]; omega,
               by assumption⟩
          · c0_hfast; exact hB4 (stC, ci, x1, p, rnd) mc ⟨hstC, hmc⟩
          · have hrnd1 : (rnd + 1#32).toNat = rnd.toNat + 1 := by c0_bound
            c0_hfast
            exact ih4 (stC, ci, nc, p, rnd + 1#32) mc (by dsimp only; rw [hrnd1]; omega)
              ⟨hstC, by rw [hrnd1]; omega, hmc⟩
        have hp_lt : p.toNat < stA.core.arena_len := by c0_bound
        have hp_ref : p.toNat ∈ fullArenaClauseRefsCore stA.core := hp_ref_f hp_lt
        have hwf := hwA.arena.refs_wf p.toNat hp_ref
        have hp2_mod : (p.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 = p.toNat + 2 := by
          rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl]; omega
        have hp32 : (BitVec.setWidth 32 p).toNat = p.toNat := by c0_bound
        c0_hfast_nogrp
        fid_call hNext
        refine ⟨c, stA, R, rfl, hslA, hma, ?_⟩
        dsimp only
        c0_hfast_nogrp
        let np32 := BitVec.ofNat 32 (fullArenaNextOff stA.core.arena stA.core.arena_len p.toNat)
        let np := BitVec.setWidth 64 np32
        have hnxt := conn_next_ref hwA.arena hp_lt hp_ref (by omega)
        refine wp_join_state1 (α := BitVec 64 × FullState) (fun (nc', _) => nc')
          (fun (_, stJ) mnext =>
            ConnStateOk c F0 F_cur s0 stJ ∧ stJ.core.arena = stA.core.arena ∧
            stJ.core.arena_len = stA.core.arena_len ∧ (FullMem c stJ ⋆ R) mnext)
          (fun _ (nc', stJ) mnext ⟨hstJ, harJ, halJ, hmn⟩ => by
            c0_hfast
            change JA (BitVec.setWidth 64 (BitVec.ofNat 32
              (fullArenaNextOff stA.core.arena stA.core.arena_len
                (BitVec.setWidth 32 p).toNat)), nc', ()) mnext
            rw [hp32]
            have hnxtJ : np.toNat ≤ stJ.core.arena_len ∧
                (np.toNat < stJ.core.arena_len → np.toNat ∈ fullArenaClauseRefsCore stJ.core) := by
              unfold fullArenaClauseRefsCore; rw [harJ, halJ]; exact hnxt.2
            exact ihA (np, nc', stJ) mnext
              (by dsimp only; rw [halJ]; exact Nat.sub_lt_sub_left hp_lt hnxt.1)
              ⟨hstJ, hnxtJ.1, hnxtJ.2, hmn⟩)
          (fun Jnxt hJnxt => by
            have hsz_eq : (stA.core.arena[p.toNat + 2]'(by omega)).toNat =
                fullArenaClauseSizeCore stA.core p.toNat := by
              unfold fullArenaClauseSizeCore
              rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
            have hsz_mod : (stA.core.arena[(p.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
                simp only [hp2_mod]; omega)).toNat = fullArenaClauseSizeCore stA.core p.toNat := by
              simp only [hp2_mod]; exact hsz_eq
            c0_hfast_nogrp
            rotate_left 1
            · c0_hfast; exact hJnxt (nc, stA) ma ⟨hstA, rfl, rfl, hma⟩
            c0_hfast_nogrp
            rotate_left 1
            · c0_hfast; exact hJnxt (nc, stA) ma ⟨hstA, rfl, rfl, hma⟩
            have hsz_ge3 : 3 ≤ fullArenaClauseSizeCore stA.core p.toNat := by
              rw [← hsz_mod]; exact by assumption
            c0_hfast_nogrp
            rotate_left 1
            · c0_hfast; exact hJnxt (nc, stA) ma ⟨hstA, rfl, rfl, hma⟩
            have hsz_le5 : fullArenaClauseSizeCore stA.core p.toNat ≤ 5 := by
              rw [← hsz_mod]; exact by assumption
            c0_hfast_nogrp
            refine wp_while_break_state (β := Bool × BitVec 32) (α := BitVec 32)
              (fun (kp, k) => (kp, k, ()))
              (fun (_, k) mk => k.toNat ≤ fullArenaClauseSizeCore stA.core p.toNat ∧
                (FullMem c stA ⋆ R) mk)
              (fun k => (k, ()))
              (fun k => fullArenaClauseSizeCore stA.core p.toNat - k.toNat)
              (fun k mk => k.toNat ≤ fullArenaClauseSizeCore stA.core p.toNat ∧
                (FullMem c stA ⋆ R) mk)
              (fun Jbrk (_kp, _k) mk ⟨_, hmk⟩ => by
                c0_hfast_nogrp
                refine wp_join_state (α := BitVec 64 × BitVec 32 × FullState)
                  (fun (nc', k2, _) => (nc', k2, ()))
                  (fun (nc', _, stK) mk2 =>
                    ConnStateOk c F0 F_cur s0 stK ∧ stK.core.arena = stA.core.arena ∧
                    stK.core.arena_len = stA.core.arena_len ∧ (FullMem c stK ⋆ R) mk2)
                  (fun _ (nc', _k2, stK) mk2 ⟨hstK, harK, halK, hmk2⟩ => by
                    c0_hfast; exact hJnxt (nc', stK) mk2 ⟨hstK, harK, halK, hmk2⟩)
                  (fun Jadd hJadd => by
                    c0_hfast_nogrp
                    rotate_left 1
                    · c0_hfast; exact hJadd (nc, _k, stA) mk ⟨hstA, rfl, rfl, hmk⟩
                    refine wp_while_state1 (α := BitVec 32 × FullState) (fun (k2, _) => k2)
                      (fun (k2, _) => fullArenaClauseSizeCore stA.core p.toNat - k2.toNat)
                      (fun (k2, stK) mk2 =>
                        ConnStateOk c F0 F_cur s0 stK ∧ stK.core.arena = stA.core.arena ∧
                        stK.core.arena_len = stA.core.arena_len ∧
                        stK.core.cur_vars = stA.core.cur_vars ∧
                        k2.toNat ≤ fullArenaClauseSizeCore stA.core p.toNat ∧
                        (FullMem c stK ⋆ R) mk2)
                      (fun JK hJK => by
                        c0_hfast
                        exact hJK (0#32, stA) mk ⟨hstA, rfl, rfl, rfl, Nat.zero_le _, hmk⟩)
                      (fun JK (k2, stK) mk2 ⟨hstK, harK, halK, hcvK, hk2_le, hmk2⟩ ihK => by
                        have hslK := hstK.1.1; have hclK := hslK.core_ok
                        have hscK := hslK.scratch_ok
                        have htmK := hscK.tarjan_mark_len; have hws1K := hscK.work_stk1_len
                        have hws2K := hscK.work_stk2_len
                        have hp_ref_K : p.toNat ∈ fullArenaClauseRefsCore stK.core := by
                          unfold fullArenaClauseRefsCore; rw [harK, halK]; exact hp_ref
                        have hgarbK : fullArenaClauseGarbCore stK.core p.toNat = false := by
                          have hgA : fullArenaClauseGarbCore stA.core p.toNat = false :=
                            conn_bv32_garb_false_of_and_480000 (by omega) (by assumption)
                          unfold fullArenaClauseGarbCore fullArenaHdrCore at hgA ⊢
                          rw [harK]; exact hgA
                        have hk2_idx : (p + 3 + BitVec.setWidth 64 k2).toNat =
                            p.toNat + 3 + k2.toNat := by
                          change (p + 3#64 + BitVec.setWidth 64 k2).toNat = _; c0_bound
                        c0_hfast_nogrp
                        rotate_left 1
                        · c0_hfast; exact hJadd (nc + 1#64, k2, stK) mk2 ⟨hstK, harK, halK, hmk2⟩
                        have hk2_lt : k2.toNat < fullArenaClauseSizeCore stA.core p.toNat := by
                          rw [← hsz_mod]; exact by assumption
                        have hgarbA : fullArenaClauseGarbCore stA.core p.toNat = false := by
                          unfold fullArenaClauseGarbCore fullArenaHdrCore at hgarbK ⊢
                          simp only [harK] at hgarbK; exact hgarbK
                        have hl_ltA := conn_clause_lit_lt hwA.arena harA_len halA_le hp_ref
                          hgarbA hk2_lt
                        have hl_lt : (stK.core.arena[p.toNat + 3 + k2.toNat]'(by
                            rw [harK, harA_len]; omega)).toNat < 2 * stK.core.cur_vars := by
                          simp only [harK, hcvK]; exact hl_ltA
                        have hcvK_le := hclK.cur_vars_le
                        have hk2_ar : (p + 3 + BitVec.setWidth 64 k2).toNat <
                            stK.core.arena.length := by
                          rw [hk2_idx, harK, harA_len]; omega
                        have hl_ws2 : (BitVec.setWidth 64 (stK.core.arena[(p + 3 +
                            BitVec.setWidth 64 k2).toNat]'hk2_ar)).toNat <
                            stK.scratch.work_stk2.length := by
                          rw [fid_bv64_32, hws2K]; simp only [hk2_idx]; omega
                        have hk21 : (k2 + 1#32).toNat = k2.toNat + 1 := by c0_bound
                        c0_hfast
                        · refine ihK (k2 + 1#32, connSetScr stK stK.scratch.tarjan_mark
                              stK.scratch.work_stk1 (stK.scratch.work_stk2.set
                              (stK.core.arena[p.toNat + 3 + k2.toNat]'(by
                                rw [harK, harA_len]; omega)).toNat
                              ((stK.scratch.work_stk2[(stK.core.arena[p.toNat + 3 +
                                k2.toNat]'(by rw [harK, harA_len]; omega)).toNat]'(by
                                rw [hws2K]; omega)) + 1#32))) _
                              (by dsimp only; rw [hk21]; omega)
                            ⟨connStateOk_set_scr hstK htmK hws1K (by simp [hws2K]),
                             harK, halK, hcvK, by rw [hk21]; omega, ?_⟩
                          simp only [hk2_idx] at hm; exact hm
                        · exact ihK (k2 + 1#32, stK) mk2 (by dsimp only; rw [hk21]; omega)
                            ⟨hstK, harK, halK, hcvK, by rw [hk21]; omega, hmk2⟩)))
              (fun Jbrk Jk k mk hB ihk ⟨hk_le, hmk⟩ => by
                have hk_idx : (p + 3 + BitVec.setWidth 64 k).toNat = p.toNat + 3 + k.toNat := by
                  change (p + 3#64 + BitVec.setWidth 64 k).toNat = _; c0_bound
                c0_hfast_nogrp
                rotate_left 1
                · c0_hfast; exact hB (true, k) mk ⟨hk_le, hmk⟩
                have hk_lt : k.toNat < fullArenaClauseSizeCore stA.core p.toNat := by
                  rw [← hsz_mod]; exact by assumption
                have hgarb : fullArenaClauseGarbCore stA.core p.toNat = false :=
                  conn_bv32_garb_false_of_and_480000 (by omega) (by assumption)
                have hl_lt : (stA.core.arena[p.toNat + 3 + k.toNat]'(by omega)).toNat <
                    2 * stA.core.cur_vars :=
                  conn_clause_lit_lt hwA.arena harA_len halA_le hp_ref hgarb hk_lt
                have hcvA := hclA.cur_vars_le
                have hl_sw_vals : (BitVec.setWidth 64
                    (stA.core.arena[(p + 3 + BitVec.setWidth 64 k).toNat]'(by
                      rw [hk_idx]; omega))).toNat < stA.core.vals.length := by
                  rw [fid_bv64_32, hclA.vals_len]; simp only [hk_idx]; omega
                have hl_sw_tm : (BitVec.setWidth 64
                    (stA.core.arena[(p + 3 + BitVec.setWidth 64 k).toNat]'(by
                      rw [hk_idx]; omega))).toNat < stA.scratch.tarjan_mark.length := by
                  rw [fid_bv64_32, hscA.tarjan_mark_len]; simp only [hk_idx]; omega
                have hl_sw_ws1 : (BitVec.setWidth 64
                    (stA.core.arena[(p + 3 + BitVec.setWidth 64 k).toNat]'(by
                      rw [hk_idx]; omega))).toNat < stA.scratch.work_stk1.length := by
                  rw [fid_bv64_32, hscA.work_stk1_len]; simp only [hk_idx]; omega
                have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
                c0_hfast
                · exact hB (false, k) mk ⟨hk_le, hmk⟩
                · exact hB (false, k) mk ⟨hk_le, hmk⟩
                · exact ihk (k + 1#32) mk (by rw [hk1]; omega) ⟨by rw [hk1]; omega, hmk⟩)
              (fun _Jk _Jk0 _hB hL => by
                c0_hfast; exact hL 0#32 ma ⟨Nat.zero_le _, hma⟩)))
    (fun _J4brk _J4 _hB hL => by
      c0_hfast; exact hL (st, _, _, _, 0#32) m ⟨hst, Nat.zero_le _, hm⟩)

private theorem conn_loop3_wp {Γ : Env} {Q : Post []} {X : XPost}
    (hNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hDeg : ∀ a m Q X, fidBvaCountLitDegSpec a m Q X →
      Γ "full_bva_count_lit_deg_fid" [i64, i32] [i32] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s0 st : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {ci : BitVec 64}
    (hst : ConnStateOk c F0 F_cur s0 st) (hm : (FullMem c st ⋆ R) m)
    (hQ : ∀ s' m', ConnStateOk c F0 F_cur s0 s' → (FullMem c s' ⋆ R) m' → Q () m') :
    wp Γ Q X (connL3Expr c.hdr (BitVec.ofNat 64 st.core.cur_vars) c.pTarjanMark
      c.pWorkStk1 c.pWorkStk2 c.pWvec c.pWstk c.pArena c.pFlags c.pVals c.pRepr ci) m := by
  have hmx := c.hmaxv; have har_b := c.harena; have hwcap := c.hwcap
  unfold dimacsBound at hmx har_b hwcap
  have hl0 := hst.1.1; have hcl0 := hl0.core_ok
  have hcv_le := hcl0.cur_vars_le; have hal_le := hcl0.arena_len_le
  unfold connL3Expr connL2Expr connInitExpr
  dsimp only [cSkipL1, cSkipL1At, cSteps, cStep, cLd64, cElse, cDummyV, cDummyT]
  refine wp_while_state (α := BitVec 64 × BitVec 64 × FullState)
    (fun (ca, p, _) => (ca, p, ()))
    (fun (_, p, st3) => st3.core.arena_len - p.toNat)
    (fun (ca, p, st3) m3 =>
      ConnStateOk c F0 F_cur s0 st3 ∧ p.toNat ≤ st3.core.arena_len ∧
      (p.toNat < st3.core.arena_len → p.toNat ∈ fullArenaClauseRefsCore st3.core) ∧
      (FullMem c st3 ⋆ R) m3)
    (fun J3 hJ3 => by
      c0_hfast
      exact hJ3 (0#64, 0#64, st) m ⟨hst, Nat.zero_le _, fun hpos =>
        conn_zero_mem_refs hst.1.2.1.arena hpos, hm⟩)
    (fun J3 (ca, p, st3) m3 ⟨hst3, hp_le, hp_ref_f, hm3⟩ ih3 => ?_)
  have hsl3 := hst3.1.1; have hcl3 := hsl3.core_ok; have hw3 := hst3.1.2.1
  have hal3_le := hcl3.arena_len_le; have har3_len := hcl3.arena_len_arr
  c0_hfast_nogrp
  rotate_left 1
  · have h4 := conn_loop4_wp (X := X) hNext hPush hDeg (ci := ci) (pL3 := ca) (caL3 := p)
      hst3 hm3 hQ
    rw [hst3.2.1, ← hst.2.1] at h4
    unfold connL4Expr connL3Expr connL2Expr connInitExpr at h4
    dsimp only [cSkipL1, cSkipL1At, cSkipL3, cSteps, cStep, cLd64, cElse, cDummyV, cDummyT] at h4
    exact h4
  have hp_lt : p.toNat < st3.core.arena_len := by c0_bound
  have hp_ref : p.toNat ∈ fullArenaClauseRefsCore st3.core := hp_ref_f hp_lt
  have hwf := hw3.arena.refs_wf p.toNat hp_ref
  have hp2_mod : (p.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64 = p.toNat + 2 := by
    rw [show BitVec.toNat (2 : BitVec 64) = 2 from rfl]; omega
  have hp32 : (BitVec.setWidth 32 p).toNat = p.toNat := by c0_bound
  c0_hfast_nogrp
  fid_call hNext
  refine ⟨c, st3, R, rfl, hsl3, hm3, ?_⟩
  dsimp only
  c0_hfast_nogrp
  let np32 := BitVec.ofNat 32 (fullArenaNextOff st3.core.arena st3.core.arena_len p.toNat)
  let np := BitVec.setWidth 64 np32
  have hnxt := conn_next_ref hw3.arena hp_lt hp_ref (by omega)
  refine wp_join_state1 (α := BitVec 64 × FullState) (fun (ca', _) => ca')
    (fun (_, stJ) mnext =>
      ConnStateOk c F0 F_cur s0 stJ ∧ stJ.core.arena = st3.core.arena ∧
      stJ.core.arena_len = st3.core.arena_len ∧ (FullMem c stJ ⋆ R) mnext)
    (fun _ (ca', stJ) mnext ⟨hstJ, harJ, halJ, hmn⟩ => by
      c0_hfast
      change J3 (ca', BitVec.setWidth 64 (BitVec.ofNat 32
        (fullArenaNextOff st3.core.arena st3.core.arena_len
          (BitVec.setWidth 32 p).toNat)), ()) mnext
      rw [hp32]
      have hnxtJ : np.toNat ≤ stJ.core.arena_len ∧
          (np.toNat < stJ.core.arena_len → np.toNat ∈ fullArenaClauseRefsCore stJ.core) := by
        unfold fullArenaClauseRefsCore; rw [harJ, halJ]; exact hnxt.2
      exact ih3 (ca', np, stJ) mnext
        (by dsimp only; rw [halJ]; exact Nat.sub_lt_sub_left hp_lt hnxt.1)
        ⟨hstJ, hnxtJ.1, hnxtJ.2, hmn⟩)
    (fun Jnxt hJnxt => by
      have hsz_eq : (st3.core.arena[p.toNat + 2]'(by omega)).toNat =
          fullArenaClauseSizeCore st3.core p.toNat := by
        unfold fullArenaClauseSizeCore
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
      have hsz_mod : (st3.core.arena[(p.toNat + BitVec.toNat (2 : BitVec 64)) % 2 ^ 64]'(by
          simp only [hp2_mod]; omega)).toNat = fullArenaClauseSizeCore st3.core p.toNat := by
        simp only [hp2_mod]; exact hsz_eq
      c0_hfast_nogrp
      rotate_left 1
      · c0_hfast; exact hJnxt (ca, st3) m3 ⟨hst3, rfl, rfl, hm3⟩
      c0_hfast_nogrp
      rotate_left 1
      · c0_hfast; exact hJnxt (ca, st3) m3 ⟨hst3, rfl, rfl, hm3⟩
      have hsz_ge3 : 3 ≤ fullArenaClauseSizeCore st3.core p.toNat := by
        rw [← hsz_mod]; exact by assumption
      c0_hfast_nogrp
      rotate_left 1
      · c0_hfast; exact hJnxt (ca, st3) m3 ⟨hst3, rfl, rfl, hm3⟩
      have hsz_le5 : fullArenaClauseSizeCore st3.core p.toNat ≤ 5 := by
        rw [← hsz_mod]; exact by assumption
      c0_hfast_nogrp
      refine wp_while_break_state (β := Bool × BitVec 32) (α := BitVec 32)
        (fun (kp, k) => (kp, k, ()))
        (fun (_, k) mk => k.toNat ≤ fullArenaClauseSizeCore st3.core p.toNat ∧
          (FullMem c st3 ⋆ R) mk)
        (fun k => (k, ()))
        (fun k => fullArenaClauseSizeCore st3.core p.toNat - k.toNat)
        (fun k mk => k.toNat ≤ fullArenaClauseSizeCore st3.core p.toNat ∧
          (FullMem c st3 ⋆ R) mk)
        (fun Jbrk (_kp, _k) mk ⟨_, hmk⟩ => by
          c0_hfast_nogrp
          refine wp_join_state (α := BitVec 64 × BitVec 32 × FullState)
            (fun (ca', k2, _) => (ca', k2, ()))
            (fun (ca', _, stK) mk2 =>
              ConnStateOk c F0 F_cur s0 stK ∧ stK.core.arena = st3.core.arena ∧
              stK.core.arena_len = st3.core.arena_len ∧ (FullMem c stK ⋆ R) mk2)
            (fun _ (ca', _k2, stK) mk2 ⟨hstK, harK, halK, hmk2⟩ => by
              c0_hfast; exact hJnxt (ca', stK) mk2 ⟨hstK, harK, halK, hmk2⟩)
            (fun Jadd hJadd => by
              c0_hfast_nogrp
              · c0_hfast; exact hJadd (ca, _k, st3) mk ⟨hst3, rfl, rfl, hmk⟩
              refine wp_while_state1 (α := BitVec 32 × FullState) (fun (k2, _) => k2)
                (fun (k2, _) => fullArenaClauseSizeCore st3.core p.toNat - k2.toNat)
                (fun (k2, stK) mk2 =>
                  ConnStateOk c F0 F_cur s0 stK ∧ stK.core.arena = st3.core.arena ∧
                  stK.core.arena_len = st3.core.arena_len ∧
                  stK.core.cur_vars = st3.core.cur_vars ∧
                  k2.toNat ≤ fullArenaClauseSizeCore st3.core p.toNat ∧
                  (FullMem c stK ⋆ R) mk2)
                (fun JK hJK => by
                  c0_hfast; exact hJK (0#32, st3) mk ⟨hst3, rfl, rfl, rfl, Nat.zero_le _, hmk⟩)
                (fun JK (k2, stK) mk2 ⟨hstK, harK, halK, hcvK, hk2_le, hmk2⟩ ihK => by
                  have hslK := hstK.1.1; have hclK := hslK.core_ok; have hscK := hslK.scratch_ok
                  have htmK := hscK.tarjan_mark_len; have hws1K := hscK.work_stk1_len
                  have hws2K := hscK.work_stk2_len
                  have hp_ref_K : p.toNat ∈ fullArenaClauseRefsCore stK.core := by
                    unfold fullArenaClauseRefsCore; rw [harK, halK]; exact hp_ref
                  have hgarbK : fullArenaClauseGarbCore stK.core p.toNat = false := by
                    have hg3 : fullArenaClauseGarbCore st3.core p.toNat = false :=
                      conn_bv32_garb_false_of_and_480000 (by omega) (by assumption)
                    unfold fullArenaClauseGarbCore fullArenaHdrCore at hg3 ⊢
                    rw [harK]; exact hg3
                  have hk2_idx : (p + 3 + BitVec.setWidth 64 k2).toNat =
                      p.toNat + 3 + k2.toNat := by
                    change (p + 3#64 + BitVec.setWidth 64 k2).toNat = _; c0_bound
                  c0_hfast_nogrp
                  rotate_left 1
                  · c0_hfast; exact hJadd (ca + 1#64, k2, stK) mk2 ⟨hstK, harK, halK, hmk2⟩
                  have hk2_lt : k2.toNat < fullArenaClauseSizeCore st3.core p.toNat := by
                    rw [← hsz_mod]; exact by assumption
                  have hgarb3 : fullArenaClauseGarbCore st3.core p.toNat = false := by
                    unfold fullArenaClauseGarbCore fullArenaHdrCore at hgarbK ⊢
                    simp only [harK] at hgarbK; exact hgarbK
                  have hl_lt3 := conn_clause_lit_lt hw3.arena har3_len hal3_le hp_ref
                    hgarb3 hk2_lt
                  have hl_lt : (stK.core.arena[p.toNat + 3 + k2.toNat]'(by
                      rw [harK, har3_len]; omega)).toNat < 2 * stK.core.cur_vars := by
                    simp only [harK, hcvK]; exact hl_lt3
                  have hcvK_le := hclK.cur_vars_le
                  have hk2_ar : (p + 3 + BitVec.setWidth 64 k2).toNat <
                      stK.core.arena.length := by
                    rw [hk2_idx, harK, har3_len]; omega
                  have hl_ws1 : (BitVec.setWidth 64 (stK.core.arena[(p + 3 +
                      BitVec.setWidth 64 k2).toNat]'hk2_ar)).toNat <
                      stK.scratch.work_stk1.length := by
                    rw [fid_bv64_32, hws1K]; simp only [hk2_idx]; omega
                  have hk21 : (k2 + 1#32).toNat = k2.toNat + 1 := by c0_bound
                  c0_hfast
                  · refine ihK (k2 + 1#32, connSetScr stK stK.scratch.tarjan_mark
                        (stK.scratch.work_stk1.set
                          (stK.core.arena[p.toNat + 3 + k2.toNat]'(by
                            rw [harK, har3_len]; omega)).toNat
                          ((stK.scratch.work_stk1[(stK.core.arena[p.toNat + 3 +
                            k2.toNat]'(by rw [harK, har3_len]; omega)).toNat]'(by
                            rw [hws1K]; omega)) + 1#32))
                        stK.scratch.work_stk2) _ (by dsimp only; rw [hk21]; omega)
                      ⟨connStateOk_set_scr hstK htmK (by simp [hws1K]) hws2K,
                       harK, halK, hcvK, by rw [hk21]; omega, ?_⟩
                    simp only [hk2_idx] at hm; exact hm
                  · exact ihK (k2 + 1#32, stK) mk2 (by dsimp only; rw [hk21]; omega)
                      ⟨hstK, harK, halK, hcvK, by rw [hk21]; omega, hmk2⟩)))
        (fun Jbrk Jk k mk hB ihk ⟨hk_le, hmk⟩ => by
          have hk_idx : (p + 3 + BitVec.setWidth 64 k).toNat = p.toNat + 3 + k.toNat := by
            change (p + 3#64 + BitVec.setWidth 64 k).toNat = _; c0_bound
          c0_hfast_nogrp
          rotate_left 1
          · c0_hfast; exact hB (false, k) mk ⟨hk_le, hmk⟩
          have hk_lt : k.toNat < fullArenaClauseSizeCore st3.core p.toNat := by
            rw [← hsz_mod]; exact by assumption
          have hgarb : fullArenaClauseGarbCore st3.core p.toNat = false :=
            conn_bv32_garb_false_of_and_480000 (by omega) (by assumption)
          have hl_lt : (st3.core.arena[p.toNat + 3 + k.toNat]'(by omega)).toNat <
              2 * st3.core.cur_vars :=
            conn_clause_lit_lt hw3.arena har3_len hal3_le hp_ref hgarb hk_lt
          have hcv3 := hcl3.cur_vars_le
          have hl_sw_vals : (BitVec.setWidth 64
              (st3.core.arena[(p + 3 + BitVec.setWidth 64 k).toNat]'(by
                rw [hk_idx]; omega))).toNat < st3.core.vals.length := by
            rw [fid_bv64_32, hcl3.vals_len]; simp only [hk_idx]; omega
          have hk1 : (k + 1#32).toNat = k.toNat + 1 := by c0_bound
          c0_hfast
          · exact hB (true, k) mk ⟨hk_le, hmk⟩
          · exact ihk (k + 1#32) mk (by rw [hk1]; omega) ⟨by rw [hk1]; omega, hmk⟩)
        (fun _Jk _Jk0 _hB hL => by
          c0_hfast; exact hL 0#32 m3 ⟨Nat.zero_le _, hm3⟩))

private theorem conn_loop12_wp {Γ : Env} {Q : Post []} {X : XPost}
    (hNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hDeg : ∀ a m Q X, fidBvaCountLitDegSpec a m Q X →
      Γ "full_bva_count_lit_deg_fid" [i64, i32] [i32] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s0 st : FullState}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hst : ConnStateOk c F0 F_cur s0 st) (hm : (FullMem c st ⋆ R) m)
    (hQ : ∀ s' m', ConnStateOk c F0 F_cur s0 s' → (FullMem c s' ⋆ R) m' → Q () m') :
    wp Γ Q X (connInitExpr c.hdr (BitVec.ofNat 64 st.core.cur_vars) c.pTarjanMark
      c.pWorkStk1 c.pWorkStk2 c.pWvec c.pWstk c.pArena c.pFlags c.pVals c.pRepr) m := by
  have hmx := c.hmaxv; have har_b := c.harena; have hwcap := c.hwcap
  unfold dimacsBound at hmx har_b hwcap
  have hl0 := hst.1.1; have hcl0 := hl0.core_ok
  have hcv_le := hcl0.cur_vars_le; have hal_le := hcl0.arena_len_le
  have hnl_eq : (BitVec.ofNat 64 st.core.cur_vars <<< BitVec.signExtend 64 (1 : BitVec 32)).toNat =
      2 * st.core.cur_vars := by
    change (BitVec.ofNat 64 st.core.cur_vars <<< (1 : Nat)).toNat = _
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  unfold connInitExpr
  dsimp only [cSteps, cStep, cLd64, cDummyV, cDummyT]
  refine wp_while_state1 (α := BitVec 64 × FullState) (fun (zi, _) => zi)
    (fun (zi, _) => 2 * st.core.cur_vars - zi.toNat)
    (fun (zi, st1) m1 =>
      ConnStateOk c F0 F_cur s0 st1 ∧ st1.core.cur_vars = st.core.cur_vars ∧
      zi.toNat ≤ 2 * st.core.cur_vars ∧ (FullMem c st1 ⋆ R) m1)
    (fun J1 hJ1 => by
      c0_hfast; exact hJ1 (0#64, st) m ⟨hst, rfl, Nat.zero_le _, hm⟩)
    (fun J1 (zi, st1) m1 ⟨hst1, hcv1, hzi_le, hm1⟩ ih1 => ?_)
  have hsl1 := hst1.1.1; have hcl1 := hsl1.core_ok; have hsc1 := hsl1.scratch_ok
  have htm1 := hsc1.tarjan_mark_len; have hws11 := hsc1.work_stk1_len
  have hws21 := hsc1.work_stk2_len
  c0_hfast_nogrp
  · have hzi_lt : zi.toNat < 2 * st.core.cur_vars := by rw [hnl_eq] at hc; exact hc
    have hzi_tm : zi.toNat < st1.scratch.tarjan_mark.length := by
      rw [htm1]; have := hcl1.cur_vars_le; omega
    have hzi_ws1 : zi.toNat < st1.scratch.work_stk1.length := by
      rw [hws11]; have := hcl1.cur_vars_le; omega
    have hzi1 : (zi + 1#64).toNat = zi.toNat + 1 := by c0_bound
    c0_hfast
    exact ih1 (zi + 1#64, connSetScr st1 (st1.scratch.tarjan_mark.set zi.toNat 0#32)
        (st1.scratch.work_stk1.set zi.toNat 0#32) st1.scratch.work_stk2) _
      (by dsimp only; rw [hzi1]; omega)
      ⟨connStateOk_set_scr hst1 (by simp [htm1]) (by simp [hws11]) hws21, hcv1,
       by rw [hzi1]; omega, by assumption⟩
  · c0_hfast
    refine wp_while_state1 (α := BitVec 64 × FullState) (fun (ci, _) => ci)
      (fun (ci, _) => 2 * st1.core.cur_vars - ci.toNat)
      (fun (ci, st2) m2 =>
        ConnStateOk c F0 F_cur s0 st2 ∧ st2.core.cur_vars = st1.core.cur_vars ∧
        ci.toNat ≤ 2 * st1.core.cur_vars ∧ (FullMem c st2 ⋆ R) m2)
      (fun J2 hJ2 => by
        c0_hfast; exact hJ2 (0#64, st1) m1 ⟨hst1, rfl, Nat.zero_le _, hm1⟩)
      (fun J2 (ci, st2) m2 ⟨hst2, hcv2, hci_le, hm2⟩ ih2 => ?_)
    have hsl2 := hst2.1.1; have hcl2 := hsl2.core_ok; have hsc2 := hsl2.scratch_ok
    have htm2 := hsc2.tarjan_mark_len; have hws12 := hsc2.work_stk1_len
    have hws22 := hsc2.work_stk2_len
    c0_hfast_nogrp
    rotate_left 1
    · have h3 := conn_loop3_wp (X := X) hNext hPush hDeg (ci := ci) hst2 hm2 hQ
      rw [hst2.2.1, ← hst.2.1] at h3
      unfold connL3Expr connL2Expr connInitExpr at h3
      dsimp only [cSkipL1, cSkipL1At, cSteps, cStep, cLd64, cElse, cDummyV, cDummyT] at h3
      exact h3
    refine wp_join_state0 (α := FullState)
      (fun stJ mJ =>
        ConnStateOk c F0 F_cur s0 stJ ∧ stJ.core.cur_vars = st1.core.cur_vars ∧
        (FullMem c stJ ⋆ R) mJ)
      (fun _ stJ mJ ⟨hstJ, hcvJ, hmJ⟩ => by
        have hci1 : (ci + 1#64).toNat = ci.toNat + 1 := by c0_bound
        c0_hfast
        exact ih2 (ci + 1#64, stJ) mJ (by dsimp only; rw [hci1]; omega)
          ⟨hstJ, hcvJ, by rw [hci1]; omega, hmJ⟩)
      (fun Jnext hJnext => by
        have hci_lt : ci.toNat < 2 * st2.core.cur_vars := by
          rw [hnl_eq, hst.2.1, ← hst2.2.1] at hc; exact hc
        have hci_shr : (ci >>> BitVec.signExtend 64 (1 : BitVec 32)).toNat <
            st2.core.flags.length := by
          rw [hcl2.flags_len]
          have := conn_bv64_ushr1_lt hci_lt
          have := hcl2.cur_vars_le; omega
        c0_hfast_nogrp
        rotate_left 1
        · c0_hfast; exact hJnext st2 m2 ⟨hst2, hcv2, hm2⟩
        have hci_vals : ci.toNat < st2.core.vals.length := by
          rw [hcl2.vals_len]; have := hcl2.cur_vars_le; omega
        c0_hfast_nogrp
        rotate_left 1
        · c0_hfast; exact hJnext st2 m2 ⟨hst2, hcv2, hm2⟩
        have hdw := m6_denseWatchesInv_of_w hst2.1
        have hbd := hdw.layout.bounds ci.toNat hci_lt
        have hsl := hdw.slices ci.toNat hci_lt
        have hshl := conn_bv64_shl1_eq hci_lt (by omega)
        have hcv2_le := hcl2.cur_vars_le
        have h2ci_wv : (ci <<< BitVec.signExtend 64 (1 : BitVec 32)).toNat <
            st2.core.wvec.length := by
          rw [hcl2.wvec_len, hshl]; omega
        have h2ci1_wv : ((ci <<< BitVec.signExtend 64 (1 : BitVec 32)) + 1#64).toNat <
            st2.core.wvec.length := by
          have : ((ci <<< BitVec.signExtend 64 (1 : BitVec 32)) + 1#64).toNat =
              2 * ci.toNat + 1 := by
            rw [BitVec.toNat_add, hshl, show (1#64).toNat = 1 from rfl,
              Nat.mod_eq_of_lt (by omega)]
          rw [hcl2.wvec_len, this]; omega
        c0_hfast_nogrp
        let qoff := BitVec.setWidth 64 (st2.core.wvec[2 * ci.toNat]'(by
          rw [hcl2.wvec_len]; omega))
        let qsz := BitVec.setWidth 64 (st2.core.wvec[2 * ci.toNat + 1]'(by
          rw [hcl2.wvec_len]; omega))
        have hqoff_nat : qoff.toNat = fullWatchOffCore st2.core ci.toNat := by
          dsimp only [qoff]; rw [fid_bv64_32]
          unfold fullWatchOffCore
          rw [List.getElem?_eq_getElem (by rw [hcl2.wvec_len]; omega), Option.getD_some]
        have hqsz_nat : qsz.toNat = fullWatchSizeCore st2.core ci.toNat := by
          dsimp only [qsz]; rw [fid_bv64_32]
          unfold fullWatchSizeCore
          rw [List.getElem?_eq_getElem (by rw [hcl2.wvec_len]; omega), Option.getD_some]
        have hwcap2 : st2.core.wlen ≤ c.wcap := hcl2.wlen_le
        have hqend_nat : (qoff + qsz).toNat = qoff.toNat + qsz.toNat := by
          rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by
            rw [hqoff_nat, hqsz_nat]
            exact Nat.lt_of_le_of_lt hbd (Nat.lt_of_le_of_lt hwcap2 (by omega)))]
        have hq_sum_eq :
            (st2.core.wvec[2 * ci.toNat % 2 ^ 64]'(by
              rw [hcl2.wvec_len, Nat.mod_eq_of_lt (by omega)]; omega)).toNat +
              (st2.core.wvec[(2 * ci.toNat + BitVec.toNat (1 : BitVec 64)) % 2 ^ 64]'(by
                rw [hcl2.wvec_len, show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
                  Nat.mod_eq_of_lt (by omega)]; omega)).toNat =
            qoff.toNat + qsz.toNat := by
          simp only [show 2 * ci.toNat % 2 ^ 64 = 2 * ci.toNat from Nat.mod_eq_of_lt (by omega),
            show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
            show (2 * ci.toNat + 1) % 2 ^ 64 = 2 * ci.toNat + 1 from Nat.mod_eq_of_lt (by omega)]
          dsimp only [qoff, qsz]; rw [fid_bv64_32, fid_bv64_32]
        refine wp_while_state (α := BitVec 64 × BitVec 32) (fun (qp, bin) => (qp, bin, ()))
          (fun (qp, _) => qoff.toNat + qsz.toNat - qp.toNat)
          (fun (qp, _) mp =>
            qoff.toNat ≤ qp.toNat ∧ qp.toNat ≤ qoff.toNat + qsz.toNat ∧
            DenseWatchSliceOk F_cur st2.core ci.toNat qp.toNat (qoff.toNat + qsz.toNat - qp.toNat) ∧
            (FullMem c st2 ⋆ R) mp)
          (fun Jp hJp => by
            c0_hfast
            dsimp only
            have hidx_ci : (ci <<< (1 : Nat)).toNat = 2 * ci.toNat := by
              rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one,
                Nat.mod_eq_of_lt (by omega)]; omega
            have hq_eq : BitVec.setWidth 64 (st2.core.wvec[(ci <<< (1 : Nat)).toNat]'(by
                rw [hcl2.wvec_len, hidx_ci]; omega)) = qoff := by
              apply BitVec.eq_of_toNat_eq
              rw [fid_bv64_32, hqoff_nat]
              unfold fullWatchOffCore
              rw [List.getElem?_eq_getElem (by rw [hcl2.wvec_len]; omega), Option.getD_some]
              simp only [hidx_ci]
            refine Eq.mpr (congrArg (fun v => Jp (v, 0#32, ()) m2) hq_eq) ?_
            refine hJp (qoff, 0#32) m2 ⟨Nat.le_refl _, Nat.le_add_right _ _, ?_, hm2⟩
            simpa only [Nat.add_sub_cancel_left, hqoff_nat, hqsz_nat] using hsl)
          (fun Jp (qp, bin) mp ⟨hqp_ge, hqp_le, hslice, hmp⟩ ihp => ?_)
        c0_hfast_nogrp
        rotate_left 1
        · have hci_tm : ci.toNat < st2.scratch.tarjan_mark.length := by
            rw [htm2]; omega
          c0_hfast
          exact hJnext (connSetScr st2 (st2.scratch.tarjan_mark.set ci.toNat bin)
              st2.scratch.work_stk1 st2.scratch.work_stk2) _
            ⟨connStateOk_set_scr hst2 (by simp [htm2]) hws12 hws22, hcv2, by assumption⟩
        have hqp_lt : qp.toNat < qoff.toNat + qsz.toNat := by
          rw [hq_sum_eq, Nat.mod_eq_of_lt (by rw [hqoff_nat, hqsz_nat]; omega)] at hc; exact hc
        have hrem_pos : 0 < qoff.toNat + qsz.toNat - qp.toNat := by omega
        have hqp_ws : qp.toNat < st2.core.wstk.length := by
          rw [hcl2.wstk_len_arr]; rw [hqoff_nat, hqsz_nat] at hqp_lt; omega
        c0_hfast
        · have hbin := bva_slice_bin_info hslice hrem_pos hqp_ws (by assumption)
          have hqp1 : (qp + 1#64).toNat = qp.toNat + 1 := by c0_bound
          have hqp1_inv : qoff.toNat ≤ (qp + 1#64).toNat ∧
              (qp + 1#64).toNat ≤ qoff.toNat + qsz.toNat ∧
              DenseWatchSliceOk F_cur st2.core ci.toNat (qp + 1#64).toNat
                (qoff.toNat + qsz.toNat - (qp + 1#64).toNat) ∧
              (FullMem c st2 ⋆ R) mp :=
            ⟨by rw [hqp1]; omega, by rw [hqp1]; omega,
             by rw [hqp1, show qoff.toNat + qsz.toNat - (qp.toNat + 1) =
               qoff.toNat + qsz.toNat - qp.toNat - 1 from by omega]; exact hbin.2.2, hmp⟩
          have hot_lt : (st2.core.wstk[qp.toNat] &&& 2147483647#32).toNat <
              2 * st2.core.cur_vars := hbin.1
          have hot_vals : (BitVec.setWidth 64
              (st2.core.wstk[qp.toNat] &&& 2147483647#32)).toNat < st2.core.vals.length := by
            rw [fid_bv64_32, hcl2.vals_len]; omega
          have hot_div : (st2.core.wstk[qp.toNat] &&& 2147483647#32).toNat / 2 <
              st2.core.flags.length := by
            rw [hcl2.flags_len]; omega
          have hot_flags : (BitVec.setWidth 64
              ((st2.core.wstk[qp.toNat] &&& 2147483647#32) >>>
                BitVec.signExtend 32 (1 : BitVec 64))).toNat < st2.core.flags.length := by
            rw [fid_bv64_32, hcl2.flags_len]
            change ((st2.core.wstk[qp.toNat] &&& 2147483647#32) >>> (1 : Nat)).toNat <
              c.max_vars
            rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
          c0_hfast
          · exact ihp (qp + 1#64, bin + 1#32) mp (by dsimp only; rw [hqp1]; omega) hqp1_inv
          · exact ihp (qp + 1#64, bin) mp (by dsimp only; rw [hqp1]; omega) hqp1_inv
          · exact ihp (qp + 1#64, bin) mp (by dsimp only; rw [hqp1]; omega) hqp1_inv
          · exact ihp (qp + 1#64, bin) mp (by dsimp only; rw [hqp1]; omega) hqp1_inv
        · have hocc := bva_slice_occ_info hslice hrem_pos hqp_ws (by assumption)
          have hqp2 : (qp + 2#64).toNat = qp.toNat + 2 := by c0_bound
          dsimp only
          refine Eq.mpr (congrArg (fun v => Jp (v, bin, ()) mp) ?_)
            (ihp (qp + 2#64, bin) mp (by dsimp only; rw [hqp2]; omega)
              ⟨by rw [hqp2]; omega, by rw [hqp2]; omega,
               by rw [hqp2, show qoff.toNat + qsz.toNat - (qp.toNat + 2) =
                 qoff.toNat + qsz.toNat - qp.toNat - 2 from by omega]; exact hocc.2, hmp⟩)
          apply BitVec.eq_of_toNat_eq; c0_bound
        · exfalso
          have hocc := bva_slice_occ_info hslice hrem_pos hqp_ws (by assumption)
          have hqp1_lt64 : qp.toNat + 1 < 2 ^ 64 := by
            rw [hqoff_nat, hqsz_nat] at hqp_lt; omega
          have hqend_lt64 : qoff.toNat + qsz.toNat < 2 ^ 64 := by
            rw [hqoff_nat, hqsz_nat]; omega
          rw [hq_sum_eq, show BitVec.toNat (1 : BitVec 64) = 1 from rfl,
            Nat.mod_eq_of_lt hqp1_lt64, Nat.mod_eq_of_lt hqend_lt64] at hc
          omega)

end ConnSubProofs

theorem full_bva_connect_clauses_fid_wp (Γ : Env)
    (hFlush : ∀ a m Q X, Forward.Spec.fullFwdFlushLargeM7Spec a m Q X →
      Γ "full_fwd_flush_large_m7" [i64] [] a m Q X)
    (hNext : ∀ a m Q X, fullArenaNextSpec a m Q X →
      Γ "full_arena_next" [i64, i32] [i32] a m Q X)
    (hPush : ∀ a m Q X, fullWatchPushSpec a m Q X →
      Γ "full_watch_push" [i64, i32, i32, i32, i32] [.bool] a m Q X)
    (hDeg : ∀ a m Q X, fidBvaCountLitDegSpec a m Q X →
      Γ "full_bva_count_lit_deg_fid" [i64, i32] [i32] a m Q X)
    (a : Tup Val [i64]) (m : Mem 64) (Q : Post []) (X : XPost)
    (hspec : fidBvaConnectClausesSpec a m Q X) :
    Func.wp Γ full_bva_connect_clauses_fid_body a m Q X := by
  rcases a with ⟨h, ⟨⟩⟩
  rcases hspec with ⟨c, F0, F_cur, s, R, rfl, hinv, hm, hQ⟩
  unfold Func.wp full_bva_connect_clauses_fid_body
  fid_call hFlush
  refine ⟨c, F0, F_cur, s, R, rfl, hinv.1, hinv.2.1, hinv.2.2.1, hinv.2.2.2.1,
    hinv.2.2.2.2.1, hm, fun s1 m1 h1_l h1_w h1_lm h1_nd h1_es h1_cv h1_cl h1_dm h1_ar h1_al
      _ _ _ h1_fu _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1_sb _ _ _ hm1 => ?_⟩
  have hinv1 : FullDenseInvW c F0 F_cur s1 :=
    ⟨h1_l, h1_w, h1_lm, h1_nd, h1_es, by rw [h1_cl]; exact hinv.2.2.2.2.2.1,
     by rw [h1_dm]; exact hinv.2.2.2.2.2.2⟩
  have hst1 : ConnStateOk c F0 F_cur s s1 := ⟨hinv1, h1_cv, h1_fu, h1_ar, h1_al, h1_sb⟩
  have h12 := conn_loop12_wp (X := X) hNext hPush hDeg hst1 hm1 fun s' m' hst' hm' =>
    hQ s' m' hst'.1 hst'.2.1 hst'.2.2.1 hst'.2.2.2.1 hst'.2.2.2.2.1 hst'.2.2.2.2.2 hm'
  unfold connInitExpr at h12
  dsimp only [cSteps, cStep, cLd64, cDummyV, cDummyT] at h12
  c0_hfast_nogrp
  exact h12

end

end LeanQbe.T.Examples.Kissat.Proof.Factor
