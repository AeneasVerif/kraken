/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1SweepDense
public import LeanQbe.T.Examples.Kissat.FullFidelityStep13S1Spec
import LeanQbe.T.Examples.Kissat.FullFidelitySweepProofVar
import LeanQbe.T.Examples.Kissat.FullCongLemmas1
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullM6ProofUtil
import LeanQbe.T.Examples.Kissat.FullSpec1
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity Step 13 Shard S1-A Proofs — Part 3b (`full_m6_sweep_vars`)

Parametric `(Γ : Env)` `Func.wp` proof (`public section`, `0` `@[expose]` on theorems/lemmas,
`0` `import all`, `<= 100` cols, `< 1,400` LOC, every theorem `<= 420` lines) certifying
`FullM6Sweep.m6SweepVarsSpec` for Step-13 `full_m6_sweep_vars`.
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityStep13S1

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0Step LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.FullM4Sweep
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open LeanQbe.T.Examples.Kissat.FullFidelitySweep
  (bv32_add1_toNat bv64_add1_toNat bv64_shl1_toNat maxVars_lt_2p31
   fid_tmkZero_congr fid_lengthsOk_trc_ws2 fid_denseInvW_set_trc_ws2 fid_denseInvW_set_trc
   fid_denseInvW_set_gu fid_denseInvW_set_flags fid_denseInvW_set_flags_gu
   fid_k11_ptr fid_k11_idx fid_k24_ptr fid_k24_idx fid_gu_idx_lt fid_denseInv_of_W
   fid_call_max_v_cap)
open Kraken.Bedrock2.Test

open scoped FullArenaTactics FullFidelitySweep.FidVarMemTactics

local elab "c0_hsteps_nogrp" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { unrollGroup := false, pruneJnz := false } 10000

local elab "s13_hsteps_to_jmp" : tactic => do
  for _ in [0:100] do
    let g ← Lean.Elab.Tactic.getMainGoal
    let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData.headBeta.consumeMData
    unless ty.isAppOfArity ``LeanQbe.T.wp 6 do break
    unless ← LeanQbe.T.C0HeadStep.headStepOnce { unrollGroup := false, strictMem := true } do
      break

local macro "s13a3b_call" h:term : tactic =>
  `(tactic| refine LeanQbe.T.wp_call_of_spec _ _ ($h _ _ _ _ ?_))

/-! ## 1. Invariant & Callee Helpers -/

private theorem s13_watchLayout_of_denseInvW {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hdw : FullDenseInvW c F0 F_cur s) :
    WatchStackLayout s.core := by
  have hwm := hdw.2.1.watches
  unfold ModeWatchesInv at hwm
  rw [ite_eq_right (fun h0 => hdw.2.2.2.2.2.2 h0)] at hwm
  exact hwm.layout

private theorem s13_denseInvW_set_repr {c : FullCfg} {F0 : CNF Nat}
    {F_cur : List (List Nat)} {s : FullState} (hdw : FullDenseInvW c F0 F_cur s)
    {rp' : List (BitVec 32)} (hrp : rp'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with repr := rp' } } :=
  ⟨⟨{ hdw.1.core_ok with repr_len := hrp }, hdw.1.scratch_ok⟩,
   { hdw.2.1 with
     arena := { hdw.2.1.arena with len_ok := hdw.2.1.arena.len_ok }
     watches := hdw.2.1.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) },
   hdw.2.2.1, hdw.2.2.2.1,
   FullExtScratchOk.of_pres hdw.2.2.2.2.1 ⟨rfl, rfl⟩ (fun _ hr => hr),
   hdw.2.2.2.2.2.1, hdw.2.2.2.2.2.2⟩

private theorem s13_repr_init_inv {F_cur : List (List Nat)} {repri : List (BitVec 32)}
    {cv0 maxv : Nat} (hrl : repri.length = 2 * maxv) (hcv : cv0 ≤ maxv)
    (hmax : maxv < 2 ^ 31)
    (hinit : ∀ k < 2 * cv0, repri[k]? = some (BitVec.ofNat 32 k)) :
    FullCongReprInv F_cur (2 * cv0) repri := by
  refine ⟨⟨by omega, fun l hl => ?_⟩, fun l hl => ?_⟩
  · rw [hinit l hl, Option.getD_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact Nat.le_refl _
  · rw [hinit l hl, Option.getD_some, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact LitEquiv.refl _ _

private theorem s13_hwm_pres_of_gu33 {L : K6Layout} {scr : List (BitVec 32)}
    {gu gu' : List (BitVec 32)}
    (hhwm : K6HwmClean L (gu[33]?.getD 0#32) (k6StateOfScratch L scr))
    (h33 : gu'[33]? = gu[33]?) :
    K6HwmClean L (gu'[33]?.getD 0#32) (k6StateOfScratch L scr) := by
  rwa [h33]

private theorem s13_gu_set_pres33 {gu : List (BitVec 32)} {i : Nat} {v : BitVec 32}
    (hne : i ≠ 33) : (gu.set i v)[33]? = gu[33]? :=
  List.getElem?_set_ne hne

private theorem s13_call_dense_prop {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hDP : ∀ a m Q X, step13DensePropSpec a m Q X →
      Γ "full_m6_dense_prop" [i64] [.bool] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {k : Tup Val [.bool] → Expr Val Cont rs}
    (hdw : FullDenseInvW c F0 F_cur s) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ ok s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → s'.core.repr = s.core.repr →
      s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      s'.scratch.scratch_buf = s.scratch.scratch_buf →
      s'.scratch.glue_used = s.scratch.glue_used →
      (ok = false → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k (ok, ())) m') :
    wp Γ Q X (Expr.call (as := [i64]) (bs := [.bool]) "full_m6_dense_prop"
      (Arg.var c.hdr, ()) k) m :=
  wp_call_of_spec _ k
    (hDP (c.hdr, ()) m (fun r m' => wp Γ Q X (k r) m') X
      ⟨c, F0, F_cur, s, R, rfl, hdw, hm, fun ok s' m' hdw' hcv hfu hrp _ _ htmk htrc hscr _ _
          hgu _ hno hm' => hk ok s' m' hdw' hcv hfu hrp htmk htrc hscr hgu hno hm'⟩)

private theorem s13_call_occ_cnt {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hOcc : ∀ a m Q X, step13DenseOccCntSpec a m Q X →
      Γ "full_dense_occ_cnt_fid" [i64, i32, i64] [i64] a m Q X)
    {c : FullCfg} {s : FullState} {lit : BitVec 32} {cap : BitVec 64}
    {R : Mem 64 → Prop} {m : Mem 64} {k : Tup Val [i64] → Expr Val Cont rs}
    (hlen : s.LengthsOk c) (hlay : WatchStackLayout s.core)
    (hlit : lit.toNat < 2 * s.core.cur_vars) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ r : BitVec 64, wp Γ Q X (k (r, ())) m) :
    wp Γ Q X (Expr.call (as := [i64, i32, i64]) (bs := [i64]) "full_dense_occ_cnt_fid"
      (Arg.var c.hdr, Arg.var lit, Arg.var cap, ()) k) m :=
  wp_call_of_spec _ k
    (hOcc (c.hdr, lit, cap, ()) m (fun r m' => wp Γ Q X (k r) m') X
      ⟨c, s, R, rfl, hlen, hlay, hlit, hm, hk⟩)

private theorem s13_call_collect_cands {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hCol : ∀ a m Q X, step13CollectCandsSpec a m Q X →
      Γ "full_m6_collect_cands" [i64] [i32] a m Q X)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {k : Tup Val [i32] → Expr Val Cont rs}
    (hlen : s.LengthsOk c) (hlay : WatchStackLayout s.core) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ nc trc' ws2' m',
      ({ s with scratch := { s.scratch with tarjan_reach := trc', work_stk2 := ws2' } } :
        FullState).LengthsOk c →
      nc.toNat ≤ s.core.cur_vars →
      (∀ i < nc.toNat, (trc'[i]?.getD 0#32).toNat < s.core.cur_vars) →
      (FullMem c { s with scratch := { s.scratch with tarjan_reach := trc', work_stk2 := ws2' } }
        ⋆ R) m' →
      wp Γ Q X (k (nc, ())) m') :
    wp Γ Q X (Expr.call (as := [i64]) (bs := [i32]) "full_m6_collect_cands"
      (Arg.var c.hdr, ()) k) m :=
  wp_call_of_spec _ k
    (hCol (c.hdr, ()) m (fun r m' => wp Γ Q X (k r) m') X
      ⟨c, s, R, rfl, hlen, hlay, hm, hk⟩)

private theorem s13_call_sweep_var_fl {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hSV : ∀ a m Q X, step13SweepVarSpec a m Q X →
      Γ "full_m6_sweep_var" [i64, i32, i64] [i64] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64}
    {rv : BitVec 32} {tlim : BitVec 64} {k : Tup Val [i64] → Expr Val Cont rs}
    (hdw : FullDenseInvW c F0 F_cur s) (hcap : k6MinScr ≤ c.scratch_cap)
    (hrv : rv.toNat < s.core.cur_vars) (htmk : M6TmkZero s)
    (hrep : FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr)
    (L : K6Layout) (hLscr : L.scrLen = c.scratch_cap) (hLmv : L.maxV = k6MaxV c.scratch_cap)
    (hhwm : K6HwmClean L (s.scratch.glue_used[33]?.getD 0#32)
      (k6StateOfScratch L s.scratch.scratch_buf))
    (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ r s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → M6TmkZero s' →
      FullCongReprInv F_cur (2 * s'.core.cur_vars) s'.core.repr →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      (∀ i < 64, i ≠ 33 → s'.scratch.glue_used[i]? = s.scratch.glue_used[i]?) →
      K6HwmClean L (s'.scratch.glue_used[33]?.getD 0#32)
        (k6StateOfScratch L s'.scratch.scratch_buf) →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X (Expr.call (as := [i64, i32, i64]) (bs := [i64]) "full_m6_sweep_var"
      (Arg.var c.hdr, Arg.var rv, Arg.var tlim, ()) k) m := by
  refine wp_call_of_spec _ k
    (hSV (c.hdr, rv, tlim, ()) m (fun r m' => wp Γ Q X (k r) m') X
      ⟨c, F0, F_cur, s, R, rfl, hdw, hcap, hrv, htmk, hrep, ⟨L, hLscr, hLmv, hhwm⟩, hm, ?_⟩)
  intro r s' m' hdw' hcv hfu htmk' hrep' htrc hgu ⟨L', hLscr', hLmv', hhwm'⟩ hr huns hm'
  have hLeq : L' = L := K6Layout.eq_of_scrLen_maxV (hLscr'.trans hLscr.symm) (hLmv'.trans hLmv.symm)
  exact hk r s' m' hdw' hcv hfu htmk' hrep' htrc hgu (hLeq ▸ hhwm') hr huns hm'

private theorem s13_call_cong_find {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hFind : ∀ a m Q X, fullCongFindSpec a m Q X →
      Γ "full_cong_find" [i64, i32] [i32] a m Q X)
    {c : FullCfg} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {lit : BitVec 32}
    {k : Tup Val [i32] → Expr Val Cont rs}
    (_hlen : s.core.LengthsOk c)
    (hrep : FullCongReprInv F_cur (2 * s.core.cur_vars) s.core.repr)
    (hlit : lit.toNat < 2 * s.core.cur_vars)
    (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ rep repr' m',
      repr'.length = s.core.repr.length →
      FullCongReprInv F_cur (2 * s.core.cur_vars) repr' →
      rep.toNat < 2 * s.core.cur_vars →
      (FullMem c { s with core := { s.core with repr := repr' } } ⋆ R) m' →
      wp Γ Q X (k (rep, ())) m') :
    wp Γ Q X (Expr.call (as := [i64, i32]) (bs := [i32]) "full_cong_find"
      (Arg.var c.pRepr, Arg.var lit, ()) k) m := by
  refine wp_call_of_spec _ k
    (hFind (c.pRepr, lit, ()) m (fun r m' => wp Γ Q X (k r) m') X
      ⟨F_cur, 2 * s.core.cur_vars, s.core.repr, FullCongHelpers.FullReprRest c s ⋆ R, hrep, hlit,
        FullCongHelpers.focus_full_repr hm, ?_⟩)
  intro rep repr' m' hlen' hrep' _ hrep_lt _ hm'
  exact hk rep repr' m' hlen' hrep' hrep_lt (FullCongHelpers.unfocus_full_repr hm')

/-! ## 2. Arithmetic, AST Projections, `need_mark`, & Post-Loop Helpers -/

private theorem s13_bv64_shl1_lit32 {v : BitVec 64} {cv : Nat}
    (hv : v.toNat < cv) (hcv : cv < 2 ^ 31) :
    ((v <<< 1#64).setWidth 32).toNat = 2 * v.toNat ∧
    (((v <<< 1#64) ||| 1#64).setWidth 32).toNat = 2 * v.toNat + 1 := by
  have hs : (v <<< 1#64).toNat = 2 * v.toNat := bv64_shl1_toNat (Nat.lt_trans hv hcv)
  have hor : ((v <<< 1#64) ||| 1#64).toNat = 2 * v.toNat + 1 := by
    rw [BitVec.toNat_or, hs, show (1#64 : BitVec 64).toNat = 1 from rfl]
    apply Nat.eq_of_testBit_eq; intro k
    cases k with
    | zero => simp [Nat.testBit_zero]
    | succ k =>
      rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
      rw [show (1 : Nat) / 2 = 0 from rfl, show (2 * v.toNat) / 2 = v.toNat from by omega,
        show (2 * v.toNat + 1) / 2 = v.toNat from by omega, Nat.zero_testBit, Bool.or_false]
  refine ⟨?_, ?_⟩
  · rw [BitVec.toNat_setWidth, hs, Nat.mod_eq_of_lt (by omega)]
  · rw [BitVec.toNat_setWidth, hor, Nat.mod_eq_of_lt (by omega)]

private theorem s13_bv32_shl1_toNat {x : BitVec 32} {n : Nat}
    (hx : x.toNat < n) (hn : n < 2 ^ 31) :
    (BitVec.setWidth 64 (x <<< (1 : Nat))).toNat = 2 * x.toNat := by
  have hs : (x <<< (1 : Nat)).toNat = 2 * x.toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm,
      Nat.mod_eq_of_lt (by omega)]
  rw [BitVec.toNat_setWidth, hs, Nat.mod_eq_of_lt (by omega)]

private theorem s13_bv32_lshr1_toNat (x : BitVec 32) :
    (x >>> 1#32).toNat = x.toNat / 2 := by
  change (x >>> (1 : Nat)).toNat = x.toNat / 2
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]

private theorem s13_bv64_sub1_toNat {x : BitVec 64} (hx : 0 < x.toNat) :
    (x - 1#64).toNat = x.toNat - 1 := by
  rw [BitVec.toNat_sub, show (1#64 : BitVec 64).toNat = 1 from rfl]; omega

private theorem s13_bv64_add1_toNat {x : BitVec 64} (hx : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := FullFidelitySweep.bv64_add1_toNat hx

private theorem s13_bv32_add1_toNat {x : BitVec 32} (hx : x.toNat + 1 < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 := bv32_add1_toNat hx

private theorem s13_bv64_vals_shl1_lt {v : BitVec 64} {cv mv len : Nat}
    (hv : v.toNat < cv) (hcv : cv < 2 ^ 31) (hle : cv ≤ mv) (hlen : len = 2 * mv) :
    (v <<< (1 : Nat)).toNat < len := by
  rw [hlen, bv64_shl1_toNat (Nat.lt_trans hv hcv)]; omega

private theorem s13_bv32_vals_shl1_lt {v : BitVec 32} {cv mv len : Nat}
    (hv : v.toNat < cv) (hcv : cv < 2 ^ 31) (hle : cv ≤ mv) (hlen : len = 2 * mv) :
    (BitVec.setWidth 64 (v <<< (1 : Nat))).toNat < len := by
  rw [hlen, s13_bv32_shl1_toNat hv hcv]; omega

private theorem s13_sweep_meas_lt {cv rem_b ci ci' : Nat}
    (hrem : 0 < rem_b) (hci' : ci' ≤ 2 * cv) :
    (2 * cv + 1) * (rem_b - 1) + (2 * cv - ci') <
      (2 * cv + 1) * rem_b + (2 * cv - ci) := by
  have h1 : (2 * cv + 1) * (rem_b - 1 + 1) = (2 * cv + 1) * rem_b := by
    congr 1; omega
  rw [← h1, Nat.mul_succ]; omega

private def s13SwDflt : (t : Ty) → Val t
  | .bool => false | .bits _ => 0 | .float _ => 0 | .pair a b => (s13SwDflt a, s13SwDflt b)

private def s13SwDfltT : (ts : List Ty) → Tup Val ts
  | [] => () | t :: r => (s13SwDflt t, s13SwDfltT r)

private def s13SwLet {L rs} : Expr Val L rs → Expr Val L rs
  | .let_ (ts := ts) _ k => k (s13SwDfltT ts) | _ => .hlt

private def s13SwLet64 {L rs} (v : Val i64) : Expr Val L rs → Expr Val L rs
  | .let_ (ts := [.bits 64]) _ k => k (v, ()) | _ => .hlt

private def s13SwLetB {L rs} (v : Bool) : Expr Val L rs → Expr Val L rs
  | .let_ (ts := [.bool]) _ k => k (v, ()) | _ => .hlt

private def s13SwLd8 {L rs} : Expr Val L rs → Expr Val L rs
  | .load (.bits 8) _ k => k 0#8 | _ => .hlt

private def s13SwLd32 {L rs} (v : Val i32) : Expr Val L rs → Expr Val L rs
  | .load (.bits 32) _ k => k v | _ => .hlt

private def s13SwLd64 {L rs} (v : Val i64) : Expr Val L rs → Expr Val L rs
  | .load (.bits 64) _ k => k v | _ => .hlt

private def s13SwSt {L rs} : Expr Val L rs → Expr Val L rs
  | .store _ _ k => k | _ => .hlt

private def s13SwCall64 {L rs} (v : Val i64) : Expr Val L rs → Expr Val L rs
  | .call (bs := [.bits 64]) _ _ k => k (v, ()) | _ => .hlt

private def s13SwCall32 {L rs} (v : Val i32) : Expr Val L rs → Expr Val L rs
  | .call (bs := [.bits 32]) _ _ k => k (v, ()) | _ => .hlt

private def s13SwCallB {L rs} (v : Bool) : Expr Val L rs → Expr Val L rs
  | .call (bs := [.bool]) _ _ k => k (v, ()) | _ => .hlt

private def s13SwJF {L rs} : Expr Val L rs → Expr Val L rs
  | .jnz _ _ e => e | _ => .hlt

private def s13SwJT {L rs} : Expr Val L rs → Expr Val L rs
  | .jnz _ e _ => e | _ => .hlt

private def s13SwGrpB32 {rs} (x : Val i32) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32]]) bs _ =>
    match bs ((fun _ _ => True), ()) with | .cons b _ => b (x, ())
  | _ => .hlt

private def s13SwGrpB64 {rs} (x : Val i64) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 64]]) bs _ =>
    match bs ((fun _ _ => True), ()) with | .cons b _ => b (x, ())
  | _ => .hlt

private def s13SwGrpB0 {rs} : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[]]) bs _ =>
    match bs ((fun _ _ => True), ()) with | .cons b _ => b ()
  | _ => .hlt

private def s13SwGrpB3 {rs} (x : Tup Val [i32, i64, .bool]) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 64, .bool]]) bs _ =>
    match bs ((fun _ _ => True), ()) with | .cons b _ => b x
  | _ => .hlt

private def s13SwGrpB4 {rs} (x : Tup Val [i64, i64, i32, i32]) :
    Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 64, .bits 64, .bits 32, .bits 32]]) bs _ =>
    match bs ((fun _ _ => True), ()) with | .cons b _ => b x
  | _ => .hlt

private def s13SwGrpK0 {rs} (J : Cont []) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[]]) _ k => k (J, ())
  | _ => .hlt

private def s13SwGrpK3 {rs} (J : Cont [i32, i64, .bool]) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32, .bits 64, .bool]]) _ k => k (J, ())
  | _ => .hlt

private def s13SwGrpK32 {rs} (J : Cont [i32]) : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 32]]) _ k => k (J, ())
  | _ => .hlt

private def s13SwGrpK3x {rs} : Expr Val Cont rs → Expr Val Cont rs
  | .group (sig := [[.bits 64, .bits 64, .bits 32]]) _ k => k ((fun _ _ => True), ())
  | _ => .hlt

private def s13SwAtNm (h budget tlim gu mv cv fl vals wvec : Val i64)
    (comp : Val i32) (mo : Val i64) (nm : Bool) : Expr Val Cont [i64] :=
  let e := full_m6_sweep_vars_body Val Cont (h, budget, tlim, ())
    |> s13SwLet |> s13SwLd64 gu |> s13SwLet |> s13SwLet |> s13SwLet |> s13SwSt
    |> s13SwLet |> s13SwLet |> s13SwLet |> s13SwSt
    |> s13SwLet |> s13SwLd64 0#64 |> s13SwCall64 mv
    |> s13SwLet |> s13SwLet |> s13SwJF |> s13SwLet |> s13SwJF |> s13SwLet |> s13SwJF
    |> s13SwCallB true |> s13SwJT |> s13SwLet |> s13SwLd64 cv |> s13SwLet |> s13SwJF
    |> s13SwLet |> s13SwLd64 fl |> s13SwLet |> s13SwLd64 vals |> s13SwLet |> s13SwLd64 wvec
    |> s13SwLet |> s13SwLet |> s13SwLet |> s13SwLd32 0#32
    |> s13SwGrpB32 comp
  e |> s13SwLet |> s13SwLet64 mo |> s13SwLet |> s13SwLet |> s13SwLet
    |> s13SwLd32 0#32 |> s13SwLetB nm

private def s13SwNmBody (h budget tlim gu mv cv fl vals wvec : Val i64)
    (comp : Val i32) (mo : Val i64) (nm : Bool) (J : Cont [i32, i64, .bool]) :
    Expr Val Cont [i64] :=
  s13SwAtNm h budget tlim gu mv cv fl vals wvec comp mo nm |> s13SwGrpK3 J

private def s13SwAtMark (h budget tlim gu mv cv fl vals wvec : Val i64)
    (comp : Val i32) (mo : Val i64) (nm : Bool) : Expr Val Cont [i64] :=
  s13SwAtNm h budget tlim gu mv cv fl vals wvec comp mo nm |> s13SwGrpB3 (comp, mo, nm, ())

private def s13SwMarkBody (h budget tlim gu mv cv fl vals wvec : Val i64)
    (comp : Val i32) (mo : Val i64) (nm : Bool) (J : Cont []) : Expr Val Cont [i64] :=
  s13SwAtMark h budget tlim gu mv cv fl vals wvec comp mo nm |> s13SwGrpK0 J

private def s13SwAfterMark (h budget tlim gu mv cv fl vals wvec : Val i64)
    (comp : Val i32) (mo : Val i64) (nm : Bool) : Expr Val Cont [i64] :=
  s13SwAtMark h budget tlim gu mv cv fl vals wvec comp mo nm |> s13SwGrpB0

private def s13SwAtMainLoop (h budget tlim gu mv cv fl vals wvec : Val i64)
    (comp : Val i32) (mo : Val i64) (nm : Bool)
    (rp nlits cands k eqb rem_ticks : Val i64) (nc : Val i32) : Expr Val Cont [i64] :=
  s13SwAfterMark h budget tlim gu mv cv fl vals wvec comp mo nm
    |> s13SwLet |> s13SwLd64 rp |> s13SwLet |> s13SwLet64 nlits
    |> s13SwGrpB64 0#64
    |> s13SwLet |> s13SwJF |> s13SwLet |> s13SwLd64 cands |> s13SwLet |> s13SwLd64 0#64
    |> s13SwLet |> s13SwLet |> s13SwLet |> s13SwLet |> s13SwLet64 k |> s13SwLet |> s13SwLd64 eqb
    |> s13SwGrpB64 rem_ticks
    |> s13SwCall32 nc

private def s13SwPost (h budget tlim gu mv cv fl vals wvec : Val i64)
    (comp : Val i32) (mo : Val i64) (nm : Bool)
    (rp nlits cands k eqb rem_ticks rem_b : Val i64) (nc ci : Val i32) :
    Expr Val Cont [i64] :=
  s13SwAtMainLoop h budget tlim gu mv cv fl vals wvec comp mo nm rp nlits cands k eqb rem_ticks nc
    |> s13SwGrpB4 (rem_ticks, rem_b, nc, ci, ())
    |> s13SwGrpB0

@[irreducible] private def s13SwRecollectBody (h budget tlim gu mv cv fl vals wvec : Val i64)
    (comp : Val i32) (mo : Val i64) (nm : Bool)
    (rp nlits cands k eqb rem_ticks : Val i64) (nc0 : Val i32)
    (rt_l rb_l : Val i64) (nc_l ci_l : Val i32) (sw0 : Val i64)
    (J : Cont [i32]) : Expr Val Cont [i64] :=
  s13SwAtMainLoop h budget tlim gu mv cv fl vals wvec comp mo nm rp nlits cands k eqb rem_ticks nc0
    |> s13SwGrpB4 (rt_l, rb_l, nc_l, ci_l, ()) |> s13SwGrpK0 ((fun _ _ => True))
    |> s13SwLet |> s13SwJT |> s13SwLet |> s13SwJT |> s13SwLet |> s13SwJT
    |> s13SwLet |> s13SwLd64 0#64 |> s13SwLet |> s13SwJT |> s13SwLet |> s13SwLd64 0#64
    |> s13SwLet |> s13SwJT |> s13SwLet |> s13SwLd64 0#64 |> s13SwLet |> s13SwJT
    |> s13SwLet |> s13SwLet |> s13SwLet |> s13SwLd32 0#32 |> s13SwLet |> s13SwLet |> s13SwLet
    |> s13SwLet |> s13SwGrpB32 0#32 |> s13SwSt |> s13SwGrpK3x
    |> s13SwLet |> s13SwLet |> s13SwLet |> s13SwLd32 0#32 |> s13SwLet |> s13SwLet |> s13SwLet
    |> s13SwLet |> s13SwJT
    |> s13SwLet |> s13SwLet |> s13SwLet |> s13SwLd8 |> s13SwLet |> s13SwLet |> s13SwLet
    |> s13SwLet |> s13SwJT
    |> s13SwLet |> s13SwLet |> s13SwLet |> s13SwLet |> s13SwLet |> s13SwLet |> s13SwLd32 0#32
    |> s13SwLet |> s13SwLet |> s13SwLet |> s13SwLet |> s13SwSt
    |> s13SwLet |> s13SwLet |> s13SwLd64 sw0 |> s13SwCall64 1#64 |> s13SwLet |> s13SwJF
    |> s13SwGrpB0
    |> s13SwLet |> s13SwLet |> s13SwLet |> s13SwLd32 0#32 |> s13SwLet |> s13SwGrpB64 0#64
    |> s13SwGrpK32 J

private theorem s13_sweep_vars_rem_inc_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    (hOcc : ∀ a m Q X, step13DenseOccCntSpec a m Q X →
      Γ "full_dense_occ_cnt_fid" [i64, i32, i64] [i64] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s1 : FullState}
    {budget tlim : BitVec 64} {comp : BitVec 32} {mo : BitVec 64} {nm : Bool}
    {R : Mem 64 → Prop} {m1 : Mem 64} {Ja : Cont [i32, i64, .bool]}
    (hdw1 : FullDenseInvW c F0 F_cur s1) (htmk1 : M6TmkZero s1)
    (hgu33_1 : s1.scratch.glue_used[33]? = some 0xFFFFFFFF#32)
    (hcv1_lt : s1.core.cur_vars < 2 ^ 31) (hm1 : (FullMem c s1 ⋆ R) m1)
    (hJa : ∀ comp_a mo_a nm_a ma s_a,
      FullDenseInvW c F0 F_cur s_a → s_a.core.cur_vars = s1.core.cur_vars →
      s_a.core.fuel = s1.core.fuel → M6TmkZero s_a →
      s_a.scratch.scratch_buf = s1.scratch.scratch_buf →
      s_a.scratch.glue_used[33]? = some 0xFFFFFFFF#32 →
      (FullMem c s_a ⋆ R) ma → Ja (comp_a, mo_a, nm_a, ()) ma) :
    wp Γ Q X (s13SwNmBody c.hdr budget tlim c.pGlueUsed (BitVec.ofNat 64 (k6MaxV c.scratch_cap))
      (BitVec.ofNat 64 s1.core.cur_vars) c.pFlags c.pVals c.pWvec comp mo nm Ja) m1 := by
  dsimp only [s13SwNmBody, s13SwAtNm, s13SwLet, s13SwLet64, s13SwLetB, s13SwLd32, s13SwLd64,
    s13SwSt, s13SwCall64, s13SwCallB, s13SwJF, s13SwJT, s13SwGrpB32, s13SwGrpK3]
  have hlen1 := hdw1.1
  have hcv1_le := hlen1.core_ok.cur_vars_le
  have hcv1_2p64 : s1.core.cur_vars < 2 ^ 64 := by omega
  c0_hsplit
  · c0_hsteps!
    exact hJa comp mo nm m1 s1 hdw1 rfl rfl htmk1 rfl hgu33_1 hm1
  · c0_hsteps_nogrp
    refine wp_loop_inv (ts := [i64, i64])
      (fun (rem_l, v_l, ()) ml => v_l.toNat ≤ s1.core.cur_vars ∧
        ∃ fl_l : List (BitVec 32), fl_l.length = c.max_vars ∧
          (FullMem c { s1 with core := { s1.core with flags := fl_l } } ⋆ R) ml)
      (fun (_, v_l, ()) _ => s1.core.cur_vars - v_l.toNat)
      (fun _ hJ_r => by
        c0_hsteps!
        exact hJ_r (0#64, 0#64, ()) m1
          ⟨Nat.zero_le _, s1.core.flags, hlen1.core_ok.flags_len, hm1⟩)
      (fun _ (rem_l, v_l, ()) ml ⟨hv_le, fl_l, hfl_l_len, hml⟩ hJ_r => by
        c0_hsplit; rotate_left
        · let s_r : FullState := { s1 with core := { s1.core with flags := fl_l } }
          have hdw_r : FullDenseInvW c F0 F_cur s_r := fid_denseInvW_set_flags hdw1 hfl_l_len
          have htmk_r : M6TmkZero s_r := fid_tmkZero_congr htmk1 rfl rfl
          obtain ⟨hgr_28, _, _, hgr_28', _, _⟩ := fid_gu_idx_lt hdw_r.1.scratch_ok.glue_used_len
          refine wp_join_group (ts := [i32, i64, .bool])
            (fun (c24, m24, n24, ()) m_24 =>
              ∃ s_a : FullState, FullDenseInvW c F0 F_cur s_a ∧
                s_a.core.cur_vars = s1.core.cur_vars ∧ s_a.core.fuel = s1.core.fuel ∧
                M6TmkZero s_a ∧ s_a.scratch.scratch_buf = s1.scratch.scratch_buf ∧
                s_a.scratch.glue_used[33]? = some 0xFFFFFFFF#32 ∧ (FullMem c s_a ⋆ R) m_24)
            (fun _ (c24, m24, n24, ()) m_24
                ⟨s_a, hdw_a, hcv_a, hfl_a, htmk_a, hscr_a, hgu33_a, hm24⟩ => by
              c0_hsteps!
              exact hJa c24 m24 n24 m_24 s_a hdw_a hcv_a hfl_a htmk_a hscr_a hgu33_a hm24)
            (fun _ hJ24 => by
              c0_hsplit
              · refine wp_join_group (ts := [])
                  (fun () m_g => ∃ gu_g : List (BitVec 32), gu_g.length = 64 ∧
                    gu_g[33]? = some 0xFFFFFFFF#32 ∧
                    (FullMem c { s_r with scratch := { s_r.scratch with glue_used := gu_g } } ⋆ R)
                      m_g)
                  (fun _ () m_g ⟨gu_g, hgu_g, hgu33_g, hm_g⟩ => by
                    obtain ⟨hgg_28, _, _, hgg_28', _, _⟩ := fid_gu_idx_lt hgu_g
                    c0_hsteps_nogrp
                    refine wp_join_group (ts := [i32]) (fun (_comp', ()) m_c' => m_c' = m_g)
                      (fun _ (comp', ()) m_c' hmc' => by
                        subst m_c'
                        c0_hsteps!
                        exact hJ24 (comp', _, true, ()) m_g ⟨_, fid_denseInvW_set_gu hdw_r hgu_g,
                          rfl, rfl, fid_tmkZero_congr htmk_r rfl rfl, rfl, hgu33_g, hm_g⟩)
                      (fun _ hJc' => by
                        c0_hsplit
                        · c0_hsteps!; exact hJc' (5#32, ()) m_g rfl
                        · c0_hsteps!; exact hJc' (_, ()) m_g rfl))
                  (fun _ hJg => by
                    c0_hsplit
                    · c0_hsteps!
                      refine hJg () _ ⟨_, ?_, ?_, by assumption⟩
                      · simp only [List.length_set, hdw1.1.scratch_ok.glue_used_len]
                      · rw [s13_gu_set_pres33 (by decide)]; exact hgu33_1
                    · c0_hsteps!
                      exact hJg () ml ⟨s_r.scratch.glue_used, hdw_r.1.scratch_ok.glue_used_len,
                        hgu33_1, hml⟩)
              · c0_hsteps!
                exact hJ24 (comp, mo, nm, ()) ml ⟨s_r, hdw_r, rfl, rfl, htmk_r, rfl, hgu33_1, hml⟩)
        · have hv_lt : v_l.toNat < s1.core.cur_vars := by
            have h1 : v_l.toNat < s1.core.cur_vars % 2 ^ 64 := hc
            rwa [Nat.mod_eq_of_lt hcv1_2p64] at h1
          have hv1 : (v_l + 1#64).toNat = v_l.toNat + 1 := s13_bv64_add1_toNat (by omega)
          have hv_fl : v_l.toNat < fl_l.length := by rw [hfl_l_len]; omega
          have hv_vals : (v_l <<< (1 : Nat)).toNat < s1.core.vals.length :=
            s13_bv64_vals_shl1_lt hv_lt hcv1_lt hcv1_le hlen1.core_ok.vals_len
          let s_v : FullState := { s1 with core := { s1.core with flags := fl_l } }
          have hdw_v : FullDenseInvW c F0 F_cur s_v := fid_denseInvW_set_flags hdw1 hfl_l_len
          have hlay_v := s13_watchLayout_of_denseInvW hdw_v
          obtain ⟨hlit_p, hlit_n⟩ := s13_bv64_shl1_lit32 hv_lt hcv1_lt
          refine wp_join_group (ts := [i64])
            (fun (rem', ()) mv1 => ∃ fl' : List (BitVec 32), fl'.length = c.max_vars ∧
              (FullMem c { s1 with core := { s1.core with flags := fl' } } ⋆ R) mv1)
            (fun _ (rem', ()) mv1 ⟨fl', hfl', hmv1⟩ => by
              c0_hsteps!
              exact hJ_r (rem', v_l + 1#64, ()) mv1
                (by dsimp only; rw [hv1]; omega)
                ⟨by rw [hv1]; exact hv_lt, fl', hfl', hmv1⟩)
            (fun _ hJ_v1 => by
              c0_hsplit; rotate_left
              · c0_hsteps!; exact hJ_v1 (rem_l, ()) ml ⟨fl_l, hfl_l_len, hml⟩
              refine wp_join_group (ts := [i64])
                (fun (rem28, ()) m28 => ∃ fl' : List (BitVec 32), fl'.length = c.max_vars ∧
                  (FullMem c { s1 with core := { s1.core with flags := fl' } } ⋆ R) m28)
                (fun _ (rem28, ()) m28 h => by c0_hsteps!; exact hJ_v1 (rem28, ()) m28 h)
                (fun _ hJ28 => by
                  c0_hsplit; rotate_left
                  · c0_hsteps!
                    refine hJ28 (rem_l, ()) _ ⟨_, ?_, by assumption⟩
                    simp only [List.length_set, hfl_l_len]
                  c0_hsteps_nogrp
                  refine s13_call_occ_cnt hOcc hdw_v.1 hlay_v (by
                    change ((v_l <<< 1#64).setWidth 32).toNat < 2 * s1.core.cur_vars; omega) hml
                    (fun dp => ?_)
                  c0_hsteps_nogrp
                  refine s13_call_occ_cnt hOcc hdw_v.1 hlay_v (by
                    change (((v_l <<< 1#64) ||| 1#64).setWidth 32).toNat < 2 * s1.core.cur_vars
                    omega) hml (fun dn => ?_)
                  refine wp_join_group (ts := [i64])
                    (fun (rem32, ()) m32 => ∃ fl' : List (BitVec 32), fl'.length = c.max_vars ∧
                      (FullMem c { s1 with core := { s1.core with flags := fl' } } ⋆ R) m32)
                    (fun _ (rem32, ()) m32 h => by c0_hsteps!; exact hJ28 (rem32, ()) m32 h)
                    (fun _ hJ32 => by
                      refine wp_join_group (ts := []) (fun () m34 => m34 = ml)
                        (fun _ () m34 hm34 => by
                          subst hm34; c0_hsteps!
                          refine hJ32 (rem_l, ()) _ ⟨_, ?_, by assumption⟩
                          simp only [List.length_set, hfl_l_len])
                        (fun _ hJ34 => by
                          c0_hsplit; rotate_left
                          · c0_hsteps!; exact hJ34 () ml rfl
                          c0_hsplit; rotate_left
                          · c0_hsteps!; exact hJ34 () ml rfl
                          c0_hsplit; rotate_left
                          · c0_hsteps!; exact hJ34 () ml rfl
                          c0_hsplit; rotate_left
                          · c0_hsteps!; exact hJ34 () ml rfl
                          c0_hsteps!
                          exact hJ32 (rem_l + 1#64, ()) ml ⟨fl_l, hfl_l_len, hml⟩)))))

private theorem s13_sweep_vars_mark_wp {Γ : Env} {Q : Post [i64]} {X : XPost}
    (hOcc : ∀ a m Q X, step13DenseOccCntSpec a m Q X →
      Γ "full_dense_occ_cnt_fid" [i64, i32, i64] [i64] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s1 s_a : FullState}
    {budget tlim : BitVec 64} {comp : BitVec 32} {mo : BitVec 64} {nm : Bool}
    {R : Mem 64 → Prop} {ma : Mem 64} {Jb : Cont []}
    (hdw_a : FullDenseInvW c F0 F_cur s_a) (hcv_a : s_a.core.cur_vars = s1.core.cur_vars)
    (hfl_a : s_a.core.fuel = s1.core.fuel) (htmk_a : M6TmkZero s_a)
    (hscr_a : s_a.scratch.scratch_buf = s1.scratch.scratch_buf)
    (hgu33_a : s_a.scratch.glue_used[33]? = some 0xFFFFFFFF#32)
    (hcv1_lt : s1.core.cur_vars < 2 ^ 31) (hma : (FullMem c s_a ⋆ R) ma)
    (hJb : ∀ mb s_b,
      FullDenseInvW c F0 F_cur s_b → s_b.core.cur_vars = s1.core.cur_vars →
      s_b.core.fuel = s1.core.fuel → M6TmkZero s_b →
      s_b.scratch.scratch_buf = s1.scratch.scratch_buf →
      s_b.scratch.glue_used[33]? = some 0xFFFFFFFF#32 →
      (FullMem c s_b ⋆ R) mb → Jb () mb) :
    wp Γ Q X (s13SwMarkBody c.hdr budget tlim c.pGlueUsed (BitVec.ofNat 64 (k6MaxV c.scratch_cap))
      (BitVec.ofNat 64 s1.core.cur_vars) c.pFlags c.pVals c.pWvec comp mo nm Jb) ma := by
  dsimp only [s13SwMarkBody, s13SwAtMark, s13SwAtNm, s13SwLet, s13SwLet64, s13SwLetB, s13SwLd32,
    s13SwLd64, s13SwSt, s13SwCall64, s13SwCallB, s13SwJF, s13SwJT, s13SwGrpB32, s13SwGrpB3,
    s13SwGrpK0]
  have hlen_a := hdw_a.1
  have hcv1_le : s1.core.cur_vars ≤ c.max_vars := hcv_a ▸ hlen_a.core_ok.cur_vars_le
  have hcv1_2p64 : s1.core.cur_vars < 2 ^ 64 := by omega
  c0_hsplit
  · c0_hsteps_nogrp
    refine wp_loop_inv (ts := [i64])
      (fun (v_l, ()) ml => v_l.toNat ≤ s1.core.cur_vars ∧
        ∃ fl_l : List (BitVec 32), fl_l.length = c.max_vars ∧
          (FullMem c { s_a with core := { s_a.core with flags := fl_l } } ⋆ R) ml)
      (fun (v_l, ()) _ => s1.core.cur_vars - v_l.toNat)
      (fun _ hJ_m => by
        c0_hsteps!
        exact hJ_m (0#64, ()) ma ⟨Nat.zero_le _, s_a.core.flags, hlen_a.core_ok.flags_len, hma⟩)
      (fun _ (v_l, ()) ml ⟨hv_le, fl_l, hfl_l_len, hml⟩ hJ_m => by
        c0_hsplit; rotate_left
        · let s_m : FullState := { s_a with core := { s_a.core with flags := fl_l } }
          have hdw_m : FullDenseInvW c F0 F_cur s_m := fid_denseInvW_set_flags hdw_a hfl_l_len
          obtain ⟨_, hgm_29, hgm_30, _, hgm_29', hgm_30'⟩ :=
            fid_gu_idx_lt hdw_m.1.scratch_ok.glue_used_len
          c0_hsteps_nogrp
          have hgu_m1 : (s_m.scratch.glue_used.set (29 : BitVec 64).toNat 1#32).length = 64 := by
            simp only [List.length_set, hdw_m.1.scratch_ok.glue_used_len]
          obtain ⟨_, _, hgm1_30, _, _, hgm1_30'⟩ := fid_gu_idx_lt hgu_m1
          c0_hsteps!
          have hgu_m2 : ((s_m.scratch.glue_used.set (29 : BitVec 64).toNat 1#32).set
              (30 : BitVec 64).toNat 0#32).length = 64 := by
            simp only [List.length_set, hdw_m.1.scratch_ok.glue_used_len]
          have hgu33_m2 : ((s_m.scratch.glue_used.set (29 : BitVec 64).toNat 1#32).set
              (30 : BitVec 64).toNat 0#32)[33]? = some 0xFFFFFFFF#32 := by
            rw [s13_gu_set_pres33 (by decide), s13_gu_set_pres33 (by decide)]; exact hgu33_a
          exact hJb _ _ (fid_denseInvW_set_gu hdw_m hgu_m2) hcv_a hfl_a
            (fid_tmkZero_congr htmk_a rfl rfl) hscr_a hgu33_m2 (by assumption)
        · have hv_lt : v_l.toNat < s1.core.cur_vars := by
            have h1 : v_l.toNat < s1.core.cur_vars % 2 ^ 64 := hc
            rwa [Nat.mod_eq_of_lt hcv1_2p64] at h1
          have hv1 : (v_l + 1#64).toNat = v_l.toNat + 1 := s13_bv64_add1_toNat (by omega)
          have hv_fl : v_l.toNat < fl_l.length := by rw [hfl_l_len]; omega
          have hv_vals : (v_l <<< (1 : Nat)).toNat < s_a.core.vals.length :=
            s13_bv64_vals_shl1_lt hv_lt hcv1_lt hcv1_le hlen_a.core_ok.vals_len
          let s_v : FullState := { s_a with core := { s_a.core with flags := fl_l } }
          have hdw_v : FullDenseInvW c F0 F_cur s_v := fid_denseInvW_set_flags hdw_a hfl_l_len
          have hlay_v := s13_watchLayout_of_denseInvW hdw_v
          obtain ⟨hlit_p, hlit_n⟩ := s13_bv64_shl1_lit32 hv_lt hcv1_lt
          refine wp_join_group (ts := [])
            (fun () mv1 => ∃ fl' : List (BitVec 32), fl'.length = c.max_vars ∧
              (FullMem c { s_a with core := { s_a.core with flags := fl' } } ⋆ R) mv1)
            (fun _ () mv1 ⟨fl', hfl', hmv1⟩ => by
              c0_hsteps!
              exact hJ_m (v_l + 1#64, ()) mv1 (by dsimp only; rw [hv1]; omega)
                ⟨by rw [hv1]; exact hv_lt, fl', hfl', hmv1⟩)
            (fun _ hJ_v1 => by
              refine wp_join_group (ts := []) (fun () m30 => m30 = ml)
                (fun _ () m30 hm30 => by
                  subst hm30; c0_hsteps!
                  refine hJ_v1 () _ ⟨_, ?_, by assumption⟩
                  simp only [List.length_set, hfl_l_len])
                (fun _ hJ30 => by
                  c0_hsplit; rotate_left
                  · c0_hsteps!; exact hJ30 () ml rfl
                  c0_hsplit; rotate_left
                  · c0_hsteps!; exact hJ30 () ml rfl
                  c0_hsteps_nogrp
                  refine s13_call_occ_cnt hOcc hdw_v.1 hlay_v (by
                    rw [hcv_a]; change ((v_l <<< 1#64).setWidth 32).toNat < 2 * s1.core.cur_vars
                    omega) hml (fun dp => ?_)
                  c0_hsteps_nogrp
                  refine s13_call_occ_cnt hOcc hdw_v.1 hlay_v (by
                    rw [hcv_a]
                    change (((v_l <<< 1#64) ||| 1#64).setWidth 32).toNat < 2 * s1.core.cur_vars
                    omega) hml (fun dn => ?_)
                  refine wp_join_group (ts := [])
                    (fun () m36 => ∃ fl' : List (BitVec 32), fl'.length = c.max_vars ∧
                      (FullMem c { s_a with core := { s_a.core with flags := fl' } } ⋆ R) m36)
                    (fun _ () m36 h => by c0_hsteps!; exact hJ_v1 () m36 h)
                    (fun _ hJ36 => by
                      refine wp_join_group (ts := []) (fun () m38 => m38 = ml)
                        (fun _ () m38 hm38 => by
                          subst hm38; c0_hsteps!
                          refine hJ36 () _ ⟨_, ?_, by assumption⟩
                          simp only [List.length_set, hfl_l_len])
                        (fun _ hJ38 => by
                          c0_hsplit; rotate_left
                          · c0_hsteps!; exact hJ38 () ml rfl
                          c0_hsplit; rotate_left
                          · c0_hsteps!; exact hJ38 () ml rfl
                          c0_hsplit; rotate_left
                          · c0_hsteps!; exact hJ38 () ml rfl
                          c0_hsplit; rotate_left
                          · c0_hsteps!; exact hJ38 () ml rfl
                          c0_hsteps!
                          refine hJ36 () _ ⟨_, ?_, by assumption⟩
                          simp only [List.length_set, hfl_l_len])))))
  · c0_hsteps!; exact hJb ma s_a hdw_a hcv_a hfl_a htmk_a hscr_a hgu33_a hma

private theorem s13_sweep_vars_post_wp {Γ : Env} (Q : Post [i64]) (X : XPost)
    (hOcc : ∀ a m Q X, step13DenseOccCntSpec a m Q X →
      Γ "full_dense_occ_cnt_fid" [i64, i32, i64] [i64] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s s1 s_e : FullState}
    {budget tlim : BitVec 64} {comp : BitVec 32} {mo : BitVec 64} {nm : Bool}
    {rp nlits cands k eqb rem_ticks rem_b : BitVec 64} {nc ci : BitVec 32}
    {R : Mem 64 → Prop} {mp_ex : Mem 64}
    (hdw_e : FullDenseInvW c F0 F_cur s_e) (hcv_e : s_e.core.cur_vars = s1.core.cur_vars)
    (hfl_e : s_e.core.fuel.toNat ≤ s1.core.fuel.toNat) (htmk_e : M6TmkZero s_e)
    (hcv1 : s1.core.cur_vars = s.core.cur_vars) (hfuel1 : s1.core.fuel = s.core.fuel)
    (hcv1_lt : s1.core.cur_vars < 2 ^ 31) (hm_e : (FullMem c s_e ⋆ R) mp_ex)
    (hQ : ∀ r s' m',
      FullDenseInv c F0 s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → M6TmkZero s' →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → Q (r, ()) m') :
    wp Γ Q X (s13SwPost c.hdr budget tlim c.pGlueUsed
      (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) (BitVec.ofNat 64 s1.core.cur_vars)
      c.pFlags c.pVals c.pWvec comp mo nm rp nlits cands k eqb rem_ticks rem_b nc ci) mp_ex := by
  dsimp only [s13SwPost, s13SwAtMainLoop, s13SwAfterMark, s13SwAtMark, s13SwAtNm,
    s13SwLet, s13SwLet64, s13SwLetB, s13SwLd32, s13SwLd64, s13SwSt, s13SwCall64, s13SwCall32,
    s13SwCallB, s13SwJF, s13SwJT, s13SwGrpB32, s13SwGrpB64, s13SwGrpB0, s13SwGrpB3, s13SwGrpB4]
  have hfuel_all : s_e.core.fuel.toNat ≤ s.core.fuel.toNat := hfuel1 ▸ hfl_e
  have hcv_all : s_e.core.cur_vars = s.core.cur_vars := hcv_e.trans hcv1
  have hlen_e := hdw_e.1
  have hcv1_le : s1.core.cur_vars ≤ c.max_vars := hcv_e ▸ hlen_e.core_ok.cur_vars_le
  have hcv1_2p64 : s1.core.cur_vars < 2 ^ 64 := by omega
  c0_hsteps_nogrp
  c0_hsplit
  · c0_hsteps!
    exact hQ 20#64 s_e mp_ex (fid_denseInv_of_W hdw_e) hcv_all hfuel_all htmk_e
      (Or.inr rfl) (fun _ => (fid_denseInv_of_W hdw_e).inconsistent_unsat (by assumption)) hm_e
  · c0_hsteps_nogrp
    refine wp_join_group (ts := [i64, i64])
      (fun (_li_e, _v_e, ()) m_li => ∃ fl_li : List (BitVec 32), fl_li.length = c.max_vars ∧
        (FullMem c { s_e with core := { s_e.core with flags := fl_li } } ⋆ R) m_li)
      (fun _ (_li_e, _v_e, ()) m_li ⟨fl_li, hfl_li, hm_li⟩ => by
        let s_li : FullState := { s_e with core := { s_e.core with flags := fl_li } }
        have hdw_li : FullDenseInvW c F0 F_cur s_li := fid_denseInvW_set_flags hdw_e hfl_li
        have htmk_li : M6TmkZero s_li := fid_tmkZero_congr htmk_e rfl rfl
        obtain ⟨hge_28, hge_29, hge_30, hge_28', hge_29', hge_30'⟩ :=
          fid_gu_idx_lt hdw_li.1.scratch_ok.glue_used_len
        c0_hsteps_nogrp
        refine wp_join_group (ts := [])
          (fun () m_end => ∃ gu_end : List (BitVec 32), gu_end.length = 64 ∧
            (FullMem c { s_li with scratch := { s_li.scratch with glue_used := gu_end } } ⋆ R)
              m_end)
          (fun _ () m_end ⟨gu_end, hgu_end, hm_end⟩ => by
            have hgu_32 : (32 : BitVec 64).toNat < gu_end.length := by rw [hgu_end]; decide
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i32])
              (fun (_sw32, ()) m_sw => m_sw = m_end)
              (fun _ (sw32, ()) m_sw hmsw => by
                subst m_sw
                c0_hsteps!
                have hgu_sw : (gu_end.set (32 : BitVec 64).toNat sw32).length = 64 := by
                  simp only [List.length_set, hgu_end]
                exact hQ 1#64 _ _ (fid_denseInv_of_W (fid_denseInvW_set_gu hdw_li hgu_sw))
                  hcv_all hfuel_all (fid_tmkZero_congr htmk_li rfl rfl) (Or.inl rfl)
                  (fun h => by cases h) (by assumption))
              (fun _ hJsw => by
                c0_hsplit
                · c0_hsteps!; exact hJsw (0xFFFFFFFF#32, ()) m_end rfl
                · c0_hsteps!; exact hJsw (_, ()) m_end rfl))
          (fun _ hJ_end => by
            c0_hsplit
            · c0_hsteps_nogrp
              let gu_e1 := s_li.scratch.glue_used.set (29 : BitVec 64).toNat 0#32
              let gu_e2 := gu_e1.set (30 : BitVec 64).toNat 0#32
              have hgu_e2_len : gu_e2.length = 64 := by
                simp [gu_e2, gu_e1, hdw_li.1.scratch_ok.glue_used_len]
              obtain ⟨hge2_28, _, _, hge2_28', _, _⟩ := fid_gu_idx_lt hgu_e2_len
              refine wp_join_group (ts := [])
                (fun () m_e2 => ∃ gu_e : List (BitVec 32), gu_e.length = 64 ∧
                  (FullMem c { s_li with scratch := { s_li.scratch with glue_used := gu_e } } ⋆ R)
                    m_e2)
                (fun _ () m_e2 h => by c0_hsteps!; exact hJ_end () m_e2 h)
                (fun _ hJe2 => by
                  c0_hsplit
                  · c0_hsteps!
                    refine hJe2 () _ ⟨_, ?_, by assumption⟩
                    simp only [List.length_set, hdw_e.1.scratch_ok.glue_used_len]
                  · c0_hsteps!
                    refine hJe2 () _ ⟨_, ?_, by assumption⟩
                    simp only [List.length_set, hdw_e.1.scratch_ok.glue_used_len])
            · c0_hsteps!
              exact hJ_end () m_li ⟨s_li.scratch.glue_used, hdw_li.1.scratch_ok.glue_used_len,
                hm_li⟩))
      (fun _ hJ_li => by
        c0_hsteps_nogrp
        refine wp_loop_inv (ts := [i64])
          (fun (v_e, ()) m_li => v_e.toNat ≤ s1.core.cur_vars ∧
            ∃ fl_li : List (BitVec 32), fl_li.length = c.max_vars ∧
              (FullMem c { s_e with core := { s_e.core with flags := fl_li } } ⋆ R) m_li)
          (fun (v_e, ()) _ => s1.core.cur_vars - v_e.toNat)
          (fun _ hJ_vl => by
            c0_hsteps!
            exact hJ_vl (0#64, ()) mp_ex
              ⟨Nat.zero_le _, s_e.core.flags, hlen_e.core_ok.flags_len, hm_e⟩)
          (fun _ (v_e, ()) mli ⟨hv_le, fl_l, hfl_l_len, hmli⟩ hJ_vl => by
            c0_hsplit; rotate_left
            · c0_hsteps!; exact hJ_li (_, v_e, ()) mli ⟨fl_l, hfl_l_len, hmli⟩
            · have hv_lt : v_e.toNat < s1.core.cur_vars := by
                have h1 : v_e.toNat < s1.core.cur_vars % 2 ^ 64 := hc
                rwa [Nat.mod_eq_of_lt hcv1_2p64] at h1
              have hv1 : (v_e + 1#64).toNat = v_e.toNat + 1 := s13_bv64_add1_toNat (by omega)
              have hv_fl : v_e.toNat < fl_l.length := by rw [hfl_l_len]; omega
              have hv_vals : (v_e <<< (1 : Nat)).toNat < s_e.core.vals.length :=
                s13_bv64_vals_shl1_lt hv_lt hcv1_lt hcv1_le hlen_e.core_ok.vals_len
              let s_v : FullState := { s_e with core := { s_e.core with flags := fl_l } }
              have hdw_v : FullDenseInvW c F0 F_cur s_v := fid_denseInvW_set_flags hdw_e hfl_l_len
              have hlay_v := s13_watchLayout_of_denseInvW hdw_v
              obtain ⟨hlit_p, hlit_n⟩ := s13_bv64_shl1_lit32 hv_lt hcv1_lt
              refine wp_join_group (ts := [i64])
                (fun (_li_v, ()) m_v1 => ∃ fl' : List (BitVec 32), fl'.length = c.max_vars ∧
                  (FullMem c { s_e with core := { s_e.core with flags := fl' } } ⋆ R) m_v1)
                (fun _ (_li_v, ()) m_v1 ⟨fl', hfl', hm_v1⟩ => by
                  c0_hsteps!
                  exact hJ_vl (v_e + 1#64, ()) m_v1 (by dsimp only; rw [hv1]; omega)
                    ⟨by rw [hv1]; exact hv_lt, fl', hfl', hm_v1⟩)
                (fun _ hJ_v1 => by
                  c0_hsplit; rotate_left
                  · c0_hsteps!; exact hJ_v1 (_, ()) mli ⟨fl_l, hfl_l_len, hmli⟩
                  refine wp_join_group (ts := [i64]) (fun (_li_v', ()) m20 => m20 = mli)
                    (fun _ (_li_v', ()) m20 hm20 => by
                      subst hm20; c0_hsteps!
                      refine hJ_v1 (_, ()) _ ⟨_, ?_, by assumption⟩
                      simp only [List.length_set, hfl_l_len])
                    (fun _ hJ20 => by
                      c0_hsplit; rotate_left
                      · c0_hsteps!; exact hJ20 (_, ()) mli rfl
                      c0_hsteps_nogrp
                      refine s13_call_occ_cnt hOcc hdw_v.1 hlay_v (by
                        rw [hcv_e]
                        change ((v_e <<< 1#64).setWidth 32).toNat < 2 * s1.core.cur_vars
                        omega) hmli (fun dp => ?_)
                      c0_hsteps_nogrp
                      refine s13_call_occ_cnt hOcc hdw_v.1 hlay_v (by
                        rw [hcv_e]
                        change (((v_e <<< 1#64) ||| 1#64).setWidth 32).toNat <
                          2 * s1.core.cur_vars
                        omega) hmli (fun dn => ?_)
                      c0_hsplit; rotate_left
                      · c0_hsteps!; exact hJ20 (_, ()) mli rfl
                      c0_hsplit; rotate_left
                      · c0_hsteps!; exact hJ20 (_, ()) mli rfl
                      c0_hsplit; rotate_left
                      · c0_hsteps!; exact hJ20 (_, ()) mli rfl
                      c0_hsplit; rotate_left
                      · c0_hsteps!; exact hJ20 (_, ()) mli rfl
                      · c0_hsteps!
                        exact hJ_li (_, _, ()) mli ⟨fl_l, hfl_l_len, hmli⟩))))

/-! ## 3. Re-collection Helper (`s13_sweep_vars_recollect_wp`) -/

private def S13LoopInv (c : FullCfg) (F0 : CNF Nat) (F_cur : List (List Nat))
    (s1 : FullState) (L : K6Layout) (R : Mem 64 → Prop) (nc_nat : Nat) (m : Mem 64) : Prop :=
  ∃ s_l : FullState, FullDenseInvW c F0 F_cur s_l ∧
    s_l.core.cur_vars = s1.core.cur_vars ∧
    s_l.core.fuel.toNat ≤ s1.core.fuel.toNat ∧ M6TmkZero s_l ∧
    FullCongReprInv F_cur (2 * s_l.core.cur_vars) s_l.core.repr ∧
    K6HwmClean L (s_l.scratch.glue_used[33]?.getD 0#32)
      (k6StateOfScratch L s_l.scratch.scratch_buf) ∧
    (∀ i < nc_nat, (s_l.scratch.tarjan_reach[i]?.getD 0#32).toNat < s1.core.cur_vars) ∧
    (FullMem c s_l ⋆ R) m

private theorem s13_bv64_setWidth32_eq {x : BitVec 64} :
    BitVec.setWidth 32 x = BitVec.ofNat 32 x.toNat := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

private theorem s13_bv32_setWidth64_toNat (x : BitVec 32) :
    (BitVec.setWidth 64 x).toNat = x.toNat := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (by decide))]

private theorem s13_trc_set_bd {trc : List (BitVec 32)} {nc cv : Nat} {rv : BitVec 32}
    (hlt : nc < trc.length)
    (hbd : ∀ i < nc, (trc[i]?.getD 0#32).toNat < cv) (hrv : rv.toNat < cv) :
    ∀ i < nc + 1, ((trc.set nc rv)[i]?.getD 0#32).toNat < cv := by
  intro i hi
  rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hlt' | rfl
  · rw [List.getElem?_set_ne (by omega)]; exact hbd i hlt'
  · rw [List.getElem?_set_self hlt, Option.getD_some]; exact hrv

private theorem s13_nlits_toNat {cv : Nat} (hcv : cv < 2 ^ 31) :
    (BitVec.ofNat 64 cv <<< (1 : Nat)).toNat = 2 * cv := by
  have hlt1 : cv < 2 ^ 64 := Nat.lt_trans hcv (by decide)
  have hlt2 : 2 * cv < 2 ^ 64 :=
    Nat.lt_trans (Nat.mul_lt_mul_of_pos_left hcv (by decide)) (by decide)
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt1,
    Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm, Nat.mod_eq_of_lt hlt2]

private theorem s13_kptr_eq (c : FullCfg) {L : K6Layout} (hL_mv : L.maxV = k6MaxV c.scratch_cap) :
    c.pScratchBuf + BitVec.setWidth 64
      ((1280 : BitVec 32) + (BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) <<<
        (1 : Nat))) * 4 = L.kPtr c.pScratchBuf := by
  have hk_mv32 : BitVec.setWidth 32 (BitVec.ofNat 64 L.maxV) = L.mv32 := by
    have hmL := L.hmaxV
    apply BitVec.eq_of_toNat_eq; unfold K6Layout.mv32
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hmL.2 (by decide)),
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hmL.2 (by decide))]
  rw [← hL_mv, hk_mv32]
  simpa only [show (1280 : BitVec 32) = 1280#32 from rfl] using
    k6_ptr_base_k6Base L c.pScratchBuf

private theorem s13_sweep_vars_recollect_wp {Γ : Env} (Q : Post [i64]) (X : XPost)
    (hFind : ∀ a m Q X, fullCongFindSpec a m Q X →
      Γ "full_cong_find" [i64, i32] [i32] a m Q X)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s1 s_d : FullState}
    {budget tlim : BitVec 64} {comp : BitVec 32} {mo : BitVec 64} {nm : Bool}
    {rem_ticks : BitVec 64} {nc0 : BitVec 32} {rt_l rb_l : BitVec 64}
    {nc_l ci_l : BitVec 32} {sw0 : BitVec 64}
    {L : K6Layout} {R : Mem 64 → Prop} {md : Mem 64} {J_nc : Cont [i32]}
    (hL_len : L.scrLen = c.scratch_cap)
    (hdw_d : FullDenseInvW c F0 F_cur s_d) (hcv_d : s_d.core.cur_vars = s1.core.cur_vars)
    (hfl_d : s_d.core.fuel.toNat ≤ s1.core.fuel.toNat) (htmk_d : M6TmkZero s_d)
    (hrep_d : FullCongReprInv F_cur (2 * s_d.core.cur_vars) s_d.core.repr)
    (hhwm_d : K6HwmClean L (s_d.scratch.glue_used[33]?.getD 0#32)
      (k6StateOfScratch L s_d.scratch.scratch_buf))
    (hbd_d : ∀ i < nc_l.toNat, (s_d.scratch.tarjan_reach[i]?.getD 0#32).toNat < s1.core.cur_vars)
    (hnc_le : nc_l.toNat ≤ 2 * s1.core.cur_vars)
    (hcv1_lt : s1.core.cur_vars < 2 ^ 31) (hm_d : (FullMem c s_d ⋆ R) md)
    (hJnc : ∀ nc_n mn, nc_l.toNat ≤ nc_n.toNat → nc_n.toNat ≤ 2 * s1.core.cur_vars →
      S13LoopInv c F0 F_cur s1 L R nc_n.toNat mn → J_nc (nc_n, ()) mn) :
    wp Γ Q X (s13SwRecollectBody c.hdr budget tlim c.pGlueUsed
      (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) (BitVec.ofNat 64 s1.core.cur_vars)
      c.pFlags c.pVals c.pWvec comp mo nm c.pRepr
      (BitVec.ofNat 64 s1.core.cur_vars <<< (1 : Nat)) c.pTarjanReach (L.kPtr c.pScratchBuf)
      c.pWorkStk2 rem_ticks nc0 rt_l rb_l nc_l ci_l sw0 J_nc) md := by
  unfold s13SwRecollectBody
  dsimp only [s13SwAtMainLoop, s13SwAfterMark, s13SwAtMark, s13SwAtNm,
    s13SwLet, s13SwLet64, s13SwLetB, s13SwLd8, s13SwLd32, s13SwLd64, s13SwSt, s13SwCall64,
    s13SwCall32, s13SwCallB, s13SwJF, s13SwJT, s13SwGrpB32, s13SwGrpB64, s13SwGrpB0, s13SwGrpB3,
    s13SwGrpB4, s13SwGrpK0, s13SwGrpK3x, s13SwGrpK32]
  have hk24_idx := fid_k24_idx (c := c) (L := L) hL_len
  have hk24_ptr := fid_k24_ptr (c := c) (L := L) hL_len
  have hcv1_2p64 : s1.core.cur_vars < 2 ^ 64 := Nat.lt_trans hcv1_lt (by decide)
  have hnlits := s13_nlits_toNat hcv1_lt
  have hcv1_le : s1.core.cur_vars ≤ c.max_vars := hcv_d ▸ hdw_d.1.core_ok.cur_vars_le
  c0_hsplit; rotate_left
  · s13_hsteps_to_jmp
    exact hJnc nc_l md (Nat.le_refl _) hnc_le
      ⟨s_d, hdw_d, hcv_d, hfl_d, htmk_d, hrep_d, hhwm_d, hbd_d, hm_d⟩
  · have hscr_d : s_d.scratch.scratch_buf.length = c.scratch_cap :=
      hdw_d.1.scratch_ok.scratch_buf_len
    have hk24_sd : (BitVec.setWidth 64 (BitVec.ofNat 32 (L.k6Base + 24))).toNat <
        s_d.scratch.scratch_buf.length := hscr_d ▸ hk24_idx
    c0_hsteps_nogrp
    try rw [hk24_ptr]
    c0_hsteps_nogrp
    refine wp_loop_inv (ts := [i32, i32])
      (fun (nc_e, ei_l, ()) me => nc_l.toNat ≤ nc_e.toNat ∧
        nc_e.toNat ≤ 2 * s1.core.cur_vars ∧ ei_l.toNat ≤ s1.core.cur_vars ∧
        S13LoopInv c F0 F_cur s1 L R nc_e.toNat me)
      (fun (_, ei_l, ()) _ => s1.core.cur_vars - ei_l.toNat) ?_ ?_
    · intro _ hJ_ei
      s13_hsteps_to_jmp
      exact hJ_ei (nc_l, 0#32, ()) md ⟨Nat.le_refl _, hnc_le, Nat.zero_le _, s_d, hdw_d, hcv_d,
        hfl_d, htmk_d, hrep_d, hhwm_d, hbd_d, hm_d⟩
    · rintro _ ⟨nc_e, ei_l, ⟨⟩⟩ me ⟨hnce_lo, hnce_hi, hei_le, s_e, hdw_e, hcv_e, hfl_e, htmk_e,
          hrep_e, hhwm_e, hbd_ce, hm_e⟩ hJ_ei
      have hex_inv : S13LoopInv c F0 F_cur s1 L R nc_e.toNat me :=
        ⟨s_e, hdw_e, hcv_e, hfl_e, htmk_e, hrep_e, hhwm_e, hbd_ce, hm_e⟩
      c0_hsplit; rotate_left; · s13_hsteps_to_jmp; exact hJnc nc_e me hnce_lo hnce_hi hex_inv
      c0_hsplit; rotate_left; · s13_hsteps_to_jmp; exact hJnc nc_e me hnce_lo hnce_hi hex_inv
      have hei_lt : ei_l.toNat < s1.core.cur_vars := by
        have h1 : ei_l.toNat < s1.core.cur_vars % 2 ^ 64 := hc
        rwa [Nat.mod_eq_of_lt hcv1_2p64] at h1
      have hei1 : (ei_l + 1#32).toNat = ei_l.toNat + 1 := s13_bv32_add1_toNat (by omega)
      have heqb_bd : (BitVec.setWidth 64 (ei_l <<< (1 : BitVec 32))).toNat <
          s_e.scratch.work_stk2.length := by
        rw [hdw_e.1.scratch_ok.work_stk2_len, s13_bv32_setWidth64_toNat]
        change (ei_l <<< (1 : Nat)).toNat < 2 * c.max_vars
        rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm,
          Nat.mod_eq_of_lt (by omega)]
        omega
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i32])
        (fun (nc_e', ()) me' => nc_l.toNat ≤ nc_e'.toNat ∧
          nc_e'.toNat ≤ 2 * s1.core.cur_vars ∧ S13LoopInv c F0 F_cur s1 L R nc_e'.toNat me')
        ?_ ?_
      · rintro _ ⟨nc_e', ⟨⟩⟩ me' ⟨h1, h2, hinv'⟩
        s13_hsteps_to_jmp
        exact hJ_ei (nc_e', ei_l + 1#32, ()) me' (by dsimp only; rw [hei1]; omega)
          ⟨h1, h2, by rw [hei1]; exact hei_lt, hinv'⟩
      · intro _ hJ_lit
        c0_hsplit; rotate_left
        · s13_hsteps_to_jmp; exact hJ_lit (nc_e, ()) me ⟨hnce_lo, hnce_hi, hex_inv⟩
        have hlit_lt : (s_e.scratch.work_stk2[(BitVec.setWidth 64
            (ei_l <<< (1 : BitVec 32))).toNat]'heqb_bd).toNat < 2 * s1.core.cur_vars := by
          have h1 : (s_e.scratch.work_stk2[(BitVec.setWidth 64
              (ei_l <<< (1 : BitVec 32))).toNat]'heqb_bd).toNat <
              (BitVec.ofNat 64 s1.core.cur_vars <<< (1 : Nat)).toNat := hc
          rwa [hnlits] at h1
        c0_hsteps_nogrp
        refine s13_call_cong_find hFind hdw_e.1.core_ok hrep_e (hcv_e ▸ hlit_lt) hm_e
          (fun rep repr' m_f hlen_f hrep_f _hrep_lt hm_f => ?_)
        let s_f : FullState := { s_e with core := { s_e.core with repr := repr' } }
        have hdw_f : FullDenseInvW c F0 F_cur s_f :=
          s13_denseInvW_set_repr hdw_e (hdw_e.1.core_ok.repr_len ▸ hlen_f)
        have htmk_f : M6TmkZero s_f := fid_tmkZero_congr htmk_e rfl rfl
        have hhwm_f : K6HwmClean L (s_f.scratch.glue_used[33]?.getD 0#32)
            (k6StateOfScratch L s_f.scratch.scratch_buf) := hhwm_e
        have hrv_lt : (rep >>> 1#32).toNat < s1.core.cur_vars := by
          rw [s13_bv32_lshr1_toNat]; omega
        have hex_f : nc_l.toNat ≤ nc_e.toNat ∧ nc_e.toNat ≤ 2 * s1.core.cur_vars ∧
            S13LoopInv c F0 F_cur s1 L R nc_e.toNat m_f :=
          ⟨hnce_lo, hnce_hi, s_f, hdw_f, hcv_e, hfl_e, htmk_f, hcv_e ▸ hrep_f,
            hhwm_f, hbd_ce, hm_f⟩
        have hrv_fl : (BitVec.setWidth 64 (rep >>> 1#32)).toNat < s_f.core.flags.length := by
          rw [s13_bv32_setWidth64_toNat, hdw_f.1.core_ok.flags_len]; omega
        have hrv_vals : (BitVec.setWidth 64 ((rep >>> 1#32) <<< (1 : Nat))).toNat <
            s_f.core.vals.length :=
          s13_bv32_vals_shl1_lt hrv_lt hcv1_lt hcv1_le hdw_f.1.core_ok.vals_len
        c0_hsteps_nogrp
        refine wp_join_group (ts := [i32])
          (fun (nc_g, ()) mg => nc_l.toNat ≤ nc_g.toNat ∧
            nc_g.toNat ≤ 2 * s1.core.cur_vars ∧ S13LoopInv c F0 F_cur s1 L R nc_g.toNat mg)
          ?_ ?_
        · rintro _ ⟨nc_g, ⟨⟩⟩ mg hg; s13_hsteps_to_jmp; exact hJ_lit (nc_g, ()) mg hg
        · intro _ hJ_rv
          c0_hsplit; rotate_left; · s13_hsteps_to_jmp; exact hJ_rv (nc_e, ()) m_f hex_f
          c0_hsplit; rotate_left; · s13_hsteps_to_jmp; exact hJ_rv (nc_e, ()) m_f hex_f
          c0_hsplit; rotate_left; · s13_hsteps_to_jmp; exact hJ_rv (nc_e, ()) m_f hex_f
          refine wp_join_group (ts := [i32])
            (fun (nc_a, ()) ma => nc_l.toNat ≤ nc_a.toNat ∧
              nc_a.toNat ≤ 2 * s1.core.cur_vars ∧
              ∃ trc_a : List (BitVec 32), trc_a.length = 2 * c.max_vars ∧
                (∀ i < nc_a.toNat, (trc_a[i]?.getD 0#32).toNat < s1.core.cur_vars) ∧
                (FullMem c { s_f with scratch := { s_f.scratch with tarjan_reach := trc_a } } ⋆ R)
                  ma) ?_ ?_
          · rintro _ ⟨nc_a, ⟨⟩⟩ ma ⟨ha1, ha2, trc_a, htrc_a, hbd_a, hma⟩
            have hrv_fl' : (BitVec.setWidth 64 (rep >>> 1#32)).toNat < s_f.core.flags.length :=
              hrv_fl
            s13_hsteps_to_jmp
            let fl_a := s_f.core.flags.set (BitVec.setWidth 64 (rep >>> 1#32)).toNat
              (s_f.core.flags[(BitVec.setWidth 64 (rep >>> 1#32)).toNat] ||| 1024#32 |||
                536870912#32)
            have hfl_a : fl_a.length = c.max_vars := by simp [fl_a, hdw_f.1.core_ok.flags_len]
            let s_a : FullState :=
              { s_f with
                core := { s_f.core with flags := fl_a }
                scratch := { s_f.scratch with tarjan_reach := trc_a } }
            have hdw_a : FullDenseInvW c F0 F_cur s_a :=
              fid_denseInvW_set_flags (fid_denseInvW_set_trc hdw_f htrc_a) hfl_a
            exact hJ_rv (nc_a, ()) _ ⟨ha1, ha2, s_a, hdw_a, hcv_e, hfl_e,
              fid_tmkZero_congr htmk_f rfl rfl, hcv_e ▸ hrep_f, hhwm_f, hbd_a, by assumption⟩
          · intro _ hJ_ap
            have hno_ap : nc_l.toNat ≤ nc_e.toNat ∧ nc_e.toNat ≤ 2 * s1.core.cur_vars ∧
                ∃ trc_a : List (BitVec 32), trc_a.length = 2 * c.max_vars ∧
                  (∀ i < nc_e.toNat, (trc_a[i]?.getD 0#32).toNat < s1.core.cur_vars) ∧
                  (FullMem c { s_f with scratch :=
                    { s_f.scratch with tarjan_reach := trc_a } } ⋆ R) m_f :=
              ⟨hnce_lo, hnce_hi, s_f.scratch.tarjan_reach, hdw_f.1.scratch_ok.tarjan_reach_len,
                hbd_ce, hm_f⟩
            c0_hsplit; rotate_left; · s13_hsteps_to_jmp; exact hJ_ap (nc_e, ()) m_f hno_ap
            c0_hsplit; rotate_left; · s13_hsteps_to_jmp; exact hJ_ap (nc_e, ()) m_f hno_ap
            have hnc_lt : nc_e.toNat < 2 * s1.core.cur_vars := by
              have h1 : nc_e.toNat < (BitVec.ofNat 64 s1.core.cur_vars <<< (1 : Nat)).toNat := hc
              rwa [hnlits] at h1
            have hnc1 : (nc_e + 1#32).toNat = nc_e.toNat + 1 := s13_bv32_add1_toNat (by omega)
            have hnc_trc : (BitVec.setWidth 64 nc_e).toNat < s_f.scratch.tarjan_reach.length := by
              rw [s13_bv32_setWidth64_toNat, hdw_f.1.scratch_ok.tarjan_reach_len]; omega
            s13_hsteps_to_jmp
            refine hJ_ap (nc_e + 1#32, ()) _ ⟨by omega, by omega, _, ?_, ?_, by assumption⟩
            · simp only [List.length_set, hdw_e.1.scratch_ok.tarjan_reach_len]
            · rw [hnc1, s13_bv32_setWidth64_toNat]
              exact s13_trc_set_bd (by rw [hdw_f.1.scratch_ok.tarjan_reach_len]; omega)
                hbd_ce hrv_lt

/-! ## 4. Main Entry Theorem (`full_m6_sweep_vars_s13_wp`) -/

theorem full_m6_sweep_vars_s13_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hDP : ∀ a m Q X, step13DensePropSpec a m Q X →
      Γ "full_m6_dense_prop" [i64] [.bool] a m Q X)
    (hOcc : ∀ a m Q X, step13DenseOccCntSpec a m Q X →
      Γ "full_dense_occ_cnt_fid" [i64, i32, i64] [i64] a m Q X)
    (hCol : ∀ a m Q X, step13CollectCandsSpec a m Q X →
      Γ "full_m6_collect_cands" [i64] [i32] a m Q X)
    (hSV : ∀ a m Q X, step13SweepVarSpec a m Q X →
      Γ "full_m6_sweep_var" [i64, i32, i64] [i64] a m Q X)
    (hFind : ∀ a m Q X, fullCongFindSpec a m Q X →
      Γ "full_cong_find" [i64, i32] [i32] a m Q X) :
    ∀ args m Q X, m6SweepVarsSpec args m Q X →
      Func.wp Γ full_m6_sweep_vars_body args m Q X := by
  rintro ⟨h, budget, tlim, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, htmk, hm, hQ⟩
  unfold Func.wp full_m6_sweep_vars_body
  have hlen := hinv.lengths
  have hcap_lt : c.scratch_cap < 2 ^ 64 := Nat.lt_trans c.hscr (by unfold dimacsBound; decide)
  obtain ⟨_, _, _, _, _, _⟩ := fid_gu_idx_lt hlen.scratch_ok.glue_used_len
  have hgu_32 : (32 : BitVec 64).toNat < s.scratch.glue_used.length := by
    rw [hlen.scratch_ok.glue_used_len]; decide
  have hgu_33 : (33 : BitVec 64).toNat < s.scratch.glue_used.length := by
    rw [hlen.scratch_ok.glue_used_len]; decide
  c0_hsteps_nogrp
  let gu0 := (s.scratch.glue_used.set (33 : BitVec 64).toNat 0xFFFFFFFF#32).set
    (32 : BitVec 64).toNat 0#32
  have hgu0_len : gu0.length = 64 := by simp [gu0, hlen.scratch_ok.glue_used_len]
  have hgu0_33 : gu0[33]? = some 0xFFFFFFFF#32 := by
    rw [s13_gu_set_pres33 (by decide)]; exact List.getElem?_set_self hgu_33
  obtain ⟨F_cur, hwW⟩ := hinv.exists_witness
  have hdw0 : FullDenseInvW c F0 F_cur
      { s with scratch := { s.scratch with glue_used := gu0 } } :=
    fid_denseInvW_set_gu hwW hgu0_len
  refine fid_call_max_v_cap hMaxV (cap := BitVec.ofNat 64 c.scratch_cap) ?_
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap_lt]
  c0_hsplit
  · c0_hsteps!; exact hQ 1#64 _ _ (fid_denseInv_of_W hdw0) rfl (Nat.le_refl _)
      (fid_tmkZero_congr htmk rfl rfl) (Or.inl rfl) (fun h => by cases h) (by assumption)
  have hcap_ge : k6MinScr ≤ c.scratch_cap := by
    rcases Nat.lt_or_ge c.scratch_cap k6MinScr with hlt | hle
    · have hmv0 : (BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32 = 0#32 := by
        rw [k6MaxV_eq_zero hlt]; rfl
      exact absurd hmv0 hc
    · exact hle
  obtain ⟨L, hL⟩ : ∃ L : K6Layout, L = k6LayoutOfCap c.scratch_cap hcap_ge c.hscr := ⟨_, rfl⟩
  have hL_len : L.scrLen = c.scratch_cap := hL ▸ k6LayoutOfCap_scrLen hcap_ge c.hscr
  have hL_mv : L.maxV = k6MaxV c.scratch_cap := by rw [hL]; rfl
  have hkptr_c0 := s13_kptr_eq c hL_mv
  have hk11_ptr := fid_k11_ptr (c := c) (L := L) hL_len
  have hk11_idx := fid_k11_idx (c := c) (L := L) hL_len
  c0_hsplit
  · c0_hsteps!; exact hQ 1#64 _ _ (fid_denseInv_of_W hdw0) rfl (Nat.le_refl _)
      (fid_tmkZero_congr htmk rfl rfl) (Or.inl rfl) (fun h => by cases h) (by assumption)
  c0_hsplit
  · c0_hsteps!; exact hQ 1#64 _ _ (fid_denseInv_of_W hdw0) rfl (Nat.le_refl _)
      (fid_tmkZero_congr htmk rfl rfl) (Or.inl rfl) (fun h => by cases h) (by assumption)
  refine s13_call_dense_prop hDP hdw0 (by assumption)
    (fun ok s1 m1 hdw1 hcv1 hfuel1 _hrp1 htmk1 _htrc1 _hscr1 hgu1 hno1 hm1 => ?_)
  c0_hsplit; rotate_left
  · have hokf : ok = false := by cases ok <;> first | rfl | exact hc
    c0_hsteps!
    exact hQ 20#64 s1 m1 (fid_denseInv_of_W hdw1) hcv1 (by rw [hfuel1]; exact Nat.le_refl _)
      (fid_tmkZero_congr htmk hcv1 htmk1) (Or.inr rfl) (fun _ => (hno1 hokf).1) hm1
  have hlen1 := hdw1.1
  have htmk1_z : M6TmkZero s1 := fid_tmkZero_congr htmk hcv1 htmk1
  have hcv1_lt : s1.core.cur_vars < 2 ^ 31 :=
    Nat.lt_of_le_of_lt hlen1.core_ok.cur_vars_le (maxVars_lt_2p31 c)
  have hgu1_33 : s1.scratch.glue_used[33]? = some 0xFFFFFFFF#32 := hgu1.symm ▸ hgu0_33
  obtain ⟨_, _, hgu1_30, _, _, hgu1_30'⟩ := fid_gu_idx_lt hlen1.scratch_ok.glue_used_len
  c0_hsteps_nogrp; c0_hsplit
  · c0_hsteps!; exact hQ 1#64 s1 m1 (fid_denseInv_of_W hdw1) hcv1
      (by rw [hfuel1]; exact Nat.le_refl _) htmk1_z (Or.inl rfl) (fun h => by cases h) hm1
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i32]) (fun (_comp, ()) mc => mc = m1) ?_ ?_
  · rintro _ ⟨comp0, ⟨⟩⟩ mc hmc; subst mc; c0_hsteps_nogrp
    refine wp_join_group (ts := [i32, i64, .bool])
      (fun (_comp_a, _mo_a, _nm_a, ()) ma =>
        ∃ s_a : FullState, FullDenseInvW c F0 F_cur s_a ∧
          s_a.core.cur_vars = s1.core.cur_vars ∧ s_a.core.fuel = s1.core.fuel ∧
          M6TmkZero s_a ∧ s_a.scratch.scratch_buf = s1.scratch.scratch_buf ∧
          s_a.scratch.glue_used[33]? = some 0xFFFFFFFF#32 ∧ (FullMem c s_a ⋆ R) ma) ?_ ?_
    · rintro _ ⟨comp_a, mo_a, nm_a, ⟨⟩⟩ ma
        ⟨s_a, hdw_a, hcv_a, hfl_a, htmk_a, hscr_a, hgu33_a, hma⟩
      refine wp_join_group (ts := [])
        (fun () mb =>
          ∃ s_b : FullState, FullDenseInvW c F0 F_cur s_b ∧
            s_b.core.cur_vars = s1.core.cur_vars ∧ s_b.core.fuel = s1.core.fuel ∧
            M6TmkZero s_b ∧ s_b.scratch.scratch_buf = s1.scratch.scratch_buf ∧
            s_b.scratch.glue_used[33]? = some 0xFFFFFFFF#32 ∧ (FullMem c s_b ⋆ R) mb) ?_ ?_
      · rintro _ ⟨⟩ mb ⟨s_b, hdw_b, hcv_b, hfl_b, htmk_b, hscr_b, hgu33_b, hmb⟩
        have hlen_b := hdw_b.1
        have hcv1_le : s1.core.cur_vars ≤ c.max_vars := hcv_b ▸ hlen_b.core_ok.cur_vars_le
        have hnlits := s13_nlits_toNat hcv1_lt
        have hmax_lt : c.max_vars < 2 ^ 31 := maxVars_lt_2p31 c
        c0_hsteps_nogrp
        refine wp_loop_inv (ts := [i64])
          (fun (ri_l, ()) m_ri => ri_l.toNat ≤ 2 * s1.core.cur_vars ∧
            ∃ repr_l : List (BitVec 32), repr_l.length = 2 * c.max_vars ∧
              (∀ k < ri_l.toNat, repr_l[k]? = some (BitVec.ofNat 32 k)) ∧
              (FullMem c { s_b with core := { s_b.core with repr := repr_l } } ⋆ R) m_ri)
          (fun (ri_l, ()) _ => 2 * s1.core.cur_vars - ri_l.toNat) ?_ ?_
        · intro _ hJ_ri; s13_hsteps_to_jmp
          exact hJ_ri (0#64, ()) mb ⟨Nat.zero_le _, s_b.core.repr, hlen_b.core_ok.repr_len,
            fun k hk => absurd hk (Nat.not_lt_zero k), hmb⟩
        · rintro _ ⟨ri_l, ⟨⟩⟩ m_ri ⟨hri_le, repr_l, hrepr_l, hinit, hm_ri⟩ hJ_ri
          c0_hsplit
          · have hri_lt : ri_l.toNat < 2 * s1.core.cur_vars := by
              have h1 : ri_l.toNat < (BitVec.ofNat 64 s1.core.cur_vars <<< (1 : Nat)).toNat := hc
              rwa [hnlits] at h1
            have hri1 : (ri_l + 1#64).toNat = ri_l.toNat + 1 := s13_bv64_add1_toNat (by omega)
            have hri_bd : ri_l.toNat < repr_l.length := by rw [hrepr_l]; omega
            s13_hsteps_to_jmp
            have hrepr_l' : (repr_l.set ri_l.toNat (BitVec.setWidth 32 ri_l)).length =
                2 * c.max_vars := by simp only [List.length_set, hrepr_l]
            refine hJ_ri (ri_l + 1#64, ()) _ (by dsimp only; rw [hri1]; omega)
              ⟨by rw [hri1]; exact hri_lt, _, hrepr_l', fun k hk => ?_, by assumption⟩
            rw [hri1] at hk
            rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hlt' | rfl
            · rw [List.getElem?_set_ne (by omega)]; exact hinit k hlt'
            · rw [List.getElem?_set_self hri_bd, s13_bv64_setWidth32_eq]
          · have hri_eq : ri_l.toNat = 2 * s1.core.cur_vars := by
              have h1 : ¬ ri_l.toNat < (BitVec.ofNat 64 s1.core.cur_vars <<< (1 : Nat)).toNat := hc
              rw [hnlits] at h1; omega
            have hrep_r : FullCongReprInv F_cur (2 * s1.core.cur_vars) repr_l :=
              s13_repr_init_inv hrepr_l hcv1_le hmax_lt (fun k hk => hinit k (hri_eq ▸ hk))
            let s_r : FullState := { s_b with core := { s_b.core with repr := repr_l } }
            have hdw_r : FullDenseInvW c F0 F_cur s_r := s13_denseInvW_set_repr hdw_b hrepr_l
            have hhwm_r : K6HwmClean L (s_r.scratch.glue_used[33]?.getD 0#32)
                (k6StateOfScratch L s_r.scratch.scratch_buf) := by
              change K6HwmClean L (s_b.scratch.glue_used[33]?.getD 0#32) _
              rw [hgu33_b]; exact Or.inl rfl
            c0_hsteps_nogrp; try rw [hkptr_c0]; c0_hsteps_nogrp
            refine wp_join_group (ts := [i64]) (fun (_rt, ()) m_rt => m_rt = m_ri) ?_ ?_
            · rintro _ ⟨rem_ticks, ⟨⟩⟩ m_rt h_mrt; subst h_mrt
              refine s13_call_collect_cands hCol hdw_r.1 (s13_watchLayout_of_denseInvW hdw_r) hm_ri
                (fun nc0 trc_c ws2_c m_c hlen_c hnc_c hbd_c hm_c => ?_)
              let s_c : FullState :=
                { s_r with scratch :=
                    { s_r.scratch with tarjan_reach := trc_c, work_stk2 := ws2_c } }
              have hdw_c : FullDenseInvW c F0 F_cur s_c :=
                fid_denseInvW_set_trc_ws2 hdw_r hlen_c.scratch_ok.tarjan_reach_len
                  hlen_c.scratch_ok.work_stk2_len
              have hnc0 : nc0.toNat ≤ 2 * s1.core.cur_vars := by
                have : s_r.core.cur_vars = s1.core.cur_vars := hcv_b; omega
              c0_hsteps_nogrp
              refine wp_loop_inv (ts := [i64, i64, i32, i32])
                (fun (rt_l, rb_l, nc_l, ci_l, ()) ml =>
                  ci_l.toNat ≤ nc_l.toNat ∧ nc_l.toNat ≤ 2 * s1.core.cur_vars ∧
                  rb_l.toNat ≤ budget.toNat ∧ S13LoopInv c F0 F_cur s1 L R nc_l.toNat ml)
                (fun (_, rb_l, _, ci_l, ()) _ =>
                  (2 * s1.core.cur_vars + 1) * rb_l.toNat +
                    (2 * s1.core.cur_vars - ci_l.toNat)) ?_ ?_
              · intro _ hJ_m
                s13_hsteps_to_jmp
                exact hJ_m (rem_ticks, budget, nc0, 0#32, ()) m_c
                  ⟨Nat.zero_le _, hnc0, Nat.le_refl _, s_c, hdw_c, hcv_b,
                    by rw [hfl_b]; exact Nat.le_refl _, fid_tmkZero_congr htmk_b rfl rfl,
                    hcv_b ▸ hrep_r, hhwm_r, fun i hi => hcv_b ▸ hbd_c i hi, hm_c⟩
              · rintro _ ⟨rt_l, rb_l, nc_l, ci_l, ⟨⟩⟩ ml
                  ⟨hci_le, hnc_le, hrb_le, s_l, hdw_l, hcv_l, hfl_l, htmk_l, hrep_l, hhwm_l,
                    hbd_cands, hm_l⟩ hJ_m
                have hcv1_le' : s1.core.cur_vars ≤ c.max_vars := hcv_l ▸ hdw_l.1.core_ok.cur_vars_le
                refine wp_join_group (ts := [])
                  (fun () mp_ex => ∃ s_e : FullState, FullDenseInvW c F0 F_cur s_e ∧
                    s_e.core.cur_vars = s1.core.cur_vars ∧
                    s_e.core.fuel.toNat ≤ s1.core.fuel.toNat ∧ M6TmkZero s_e ∧
                    (FullMem c s_e ⋆ R) mp_ex) ?_ ?_
                · rintro _ ⟨⟩ mp_ex ⟨s_e, hdw_e, hcv_e, hfl_e, htmk_e, hm_e⟩
                  dsimp only [Blocks.get]
                  have hP := s13_sweep_vars_post_wp Q X (budget := budget) (tlim := tlim)
                    (comp := comp_a) (mo := mo_a) (nm := nm_a) (rp := c.pRepr)
                    (nlits := BitVec.ofNat 64 s1.core.cur_vars <<< (1 : Nat))
                    (cands := c.pTarjanReach) (k := L.kPtr c.pScratchBuf) (eqb := c.pWorkStk2)
                    (rem_ticks := rt_l) (rem_b := rb_l) (nc := nc_l) (ci := ci_l)
                    hOcc hdw_e hcv_e hfl_e htmk_e hcv1 hfuel1 hcv1_lt hm_e hQ
                  dsimp only [s13SwPost, s13SwAtMainLoop, s13SwAfterMark, s13SwAtMark, s13SwAtNm,
                    s13SwLet, s13SwLet64, s13SwLetB, s13SwLd32, s13SwLd64, s13SwSt, s13SwCall64,
                    s13SwCall32, s13SwCallB, s13SwJF, s13SwJT, s13SwGrpB32, s13SwGrpB64, s13SwGrpB0,
                    s13SwGrpB3, s13SwGrpB4] at hP
                  exact hP
                intro _ hJ_ex
                have h_ex : ∃ s_e : FullState, FullDenseInvW c F0 F_cur s_e ∧
                    s_e.core.cur_vars = s1.core.cur_vars ∧
                    s_e.core.fuel.toNat ≤ s1.core.fuel.toNat ∧ M6TmkZero s_e ∧
                    (FullMem c s_e ⋆ R) ml := ⟨s_l, hdw_l, hcv_l, hfl_l, htmk_l, hm_l⟩
                c0_hsplit; rotate_left; · c0_hsteps!; exact hJ_ex () ml h_ex
                have hci_lt : ci_l.toNat < nc_l.toNat := hc
                have hci1 : (ci_l + 1#32).toNat = ci_l.toNat + 1 := s13_bv32_add1_toNat (by omega)
                c0_hsplit; rotate_left; · c0_hsteps!; exact hJ_ex () ml h_ex
                have hrb_pos : 0 < rb_l.toNat := hc
                have hrb1 : (rb_l - 1#64).toNat = rb_l.toNat - 1 := s13_bv64_sub1_toNat hrb_pos
                c0_hsplit; rotate_left; · c0_hsteps!; exact hJ_ex () ml h_ex
                c0_hsplit; rotate_left; · c0_hsteps!; exact hJ_ex () ml h_ex
                c0_hsplit; rotate_left; · c0_hsteps!; exact hJ_ex () ml h_ex
                c0_hsplit; rotate_left; · c0_hsteps!; exact hJ_ex () ml h_ex
                have hlen_l := hdw_l.1
                have hci_trc : (BitVec.setWidth 64 ci_l).toNat <
                    s_l.scratch.tarjan_reach.length := by
                  rw [s13_bv32_setWidth64_toNat, hlen_l.scratch_ok.tarjan_reach_len]; omega
                have hv_lt : (s_l.scratch.tarjan_reach[(BitVec.setWidth 64 ci_l).toNat]'
                    hci_trc).toNat < s1.core.cur_vars := by
                  have h1 := hbd_cands (BitVec.setWidth 64 ci_l).toNat
                    (by rw [s13_bv32_setWidth64_toNat]; exact hci_lt)
                  rw [List.getElem?_eq_getElem hci_trc, Option.getD_some] at h1; exact h1
                let v := s_l.scratch.tarjan_reach[(BitVec.setWidth 64 ci_l).toNat]'hci_trc
                obtain ⟨_, _, hgl_30, _, _, hgl_30'⟩ :=
                  fid_gu_idx_lt hlen_l.scratch_ok.glue_used_len
                c0_hsteps_nogrp
                refine wp_join_group (ts := [i32]) (fun (_cur, ()) m_cur => m_cur = ml) ?_ ?_
                · rintro _ ⟨cur_v, ⟨⟩⟩ m_cur hm_cur
                  subst hm_cur
                  let gu_p := s_l.scratch.glue_used.set (30 : BitVec 64).toNat cur_v
                  have hgu_p : gu_p.length = 64 := by simp [gu_p, hlen_l.scratch_ok.glue_used_len]
                  let s_p : FullState :=
                    { s_l with scratch := { s_l.scratch with glue_used := gu_p } }
                  have hdw_p : FullDenseInvW c F0 F_cur s_p := fid_denseInvW_set_gu hdw_l hgu_p
                  have htmk_p : M6TmkZero s_p := fid_tmkZero_congr htmk_l rfl rfl
                  have hhwm_p : K6HwmClean L (s_p.scratch.glue_used[33]?.getD 0#32)
                      (k6StateOfScratch L s_p.scratch.scratch_buf) :=
                    s13_hwm_pres_of_gu33 hhwm_l (s13_gu_set_pres33 (by decide))
                  have hv_fl : (BitVec.setWidth 64 v).toNat < s_p.core.flags.length := by
                    rw [s13_bv32_setWidth64_toNat, hdw_p.1.core_ok.flags_len]
                    exact Nat.lt_of_lt_of_le hv_lt hcv1_le'
                  have hv_vals : (BitVec.setWidth 64 (v <<< (1 : Nat))).toNat <
                      s_p.core.vals.length :=
                    s13_bv32_vals_shl1_lt hv_lt hcv1_lt hcv1_le' hdw_p.1.core_ok.vals_len
                  c0_hsteps_nogrp
                  refine wp_join_group (ts := [i64, i64, i32])
                    (fun (_rt_n, rb_n, nc_n, ()) mn =>
                      ((rb_n.toNat < rb_l.toNat ∧ ci_l.toNat + 1 ≤ nc_n.toNat ∧
                        nc_n.toNat ≤ 2 * s1.core.cur_vars) ∨ (rb_n = rb_l ∧ nc_n = nc_l)) ∧
                      rb_n.toNat ≤ budget.toNat ∧ S13LoopInv c F0 F_cur s1 L R nc_n.toNat mn) ?_ ?_
                  · rintro _ ⟨rt_n, rb_n, nc_n, ⟨⟩⟩ mn ⟨hord, hrb_n, hinv_n⟩
                    c0_hsteps!
                    refine hJ_m (rt_n, rb_n, nc_n, ci_l + 1#32, ()) mn ?_ ⟨?_, ?_, hrb_n, hinv_n⟩
                    · dsimp only; rw [hci1]
                      rcases hord with ⟨hlt, _, hnc_n⟩ | ⟨rfl, rfl⟩
                      · have hm := s13_sweep_meas_lt (ci := ci_l.toNat) hrb_pos
                          (by omega : ci_l.toNat + 1 ≤ 2 * s1.core.cur_vars)
                        have hmul : (2 * s1.core.cur_vars + 1) * rb_n.toNat ≤
                            (2 * s1.core.cur_vars + 1) * (rb_l.toNat - 1) :=
                          Nat.mul_le_mul_left _ (by omega)
                        omega
                      · omega
                    · rw [hci1]; rcases hord with ⟨_, hci_n, _⟩ | ⟨_, rfl⟩ <;> omega
                    · rcases hord with ⟨_, _, hnc_n⟩ | ⟨_, rfl⟩ <;> omega
                  · intro _ hJ_n
                    have hskip :
                        ((rb_l.toNat < rb_l.toNat ∧ ci_l.toNat + 1 ≤ nc_l.toNat ∧
                          nc_l.toNat ≤ 2 * s1.core.cur_vars) ∨ (rb_l = rb_l ∧ nc_l = nc_l)) ∧
                        rb_l.toNat ≤ budget.toNat ∧ S13LoopInv c F0 F_cur s1 L R nc_l.toNat m :=
                      ⟨Or.inr ⟨rfl, rfl⟩, hrb_le, s_p, hdw_p, hcv_l, hfl_l, htmk_p, hrep_l, hhwm_p,
                        hbd_cands, by assumption⟩
                    c0_hsplit; rotate_left; · c0_hsteps!; exact hJ_n (rt_l, rb_l, nc_l, ()) m hskip
                    c0_hsplit; rotate_left; · c0_hsteps!; exact hJ_n (rt_l, rb_l, nc_l, ()) m hskip
                    c0_hsteps_nogrp
                    let fl_v := s_p.core.flags.set (BitVec.setWidth 64 v).toNat
                      (s_p.core.flags[(BitVec.setWidth 64 v).toNat] &&&
                        ~~~(1024#32 ||| 1073741824#32 ||| 536870912#32))
                    have hfl_v : fl_v.length = c.max_vars := by
                      simp [fl_v, hdw_p.1.core_ok.flags_len]
                    let s_v : FullState := { s_p with core := { s_p.core with flags := fl_v } }
                    have hdw_v : FullDenseInvW c F0 F_cur s_v := fid_denseInvW_set_flags hdw_p hfl_v
                    have htmk_v : M6TmkZero s_v := fid_tmkZero_congr htmk_p rfl rfl
                    refine s13_call_sweep_var_fl hSV hdw_v hcap_ge (hcv_l ▸ hv_lt) htmk_v
                      (hcv_l ▸ hrep_l) L hL_len hL_mv hhwm_p (by assumption)
                      (fun r3 s3 m3 hdw3 hcv3 hfl3 htmk3 hrep3 htrc3 _hgu3 hhwm3 hr3 hunsat3
                        hm3 => ?_)
                    c0_hsplit
                    · c0_hsteps!
                      exact hQ 20#64 s3 m3 (fid_denseInv_of_W hdw3)
                        (hcv3.trans (hcv_l.trans hcv1)) (Nat.le_trans hfl3 (hfuel1 ▸ hfl_l)) htmk3
                        (Or.inr rfl) (fun _ => hunsat3 hc) hm3
                    · refine wp_join_group (ts := [])
                        (fun () md => ∃ s_d : FullState, FullDenseInvW c F0 F_cur s_d ∧
                          s_d.core.cur_vars = s1.core.cur_vars ∧
                          s_d.core.fuel.toNat ≤ s1.core.fuel.toNat ∧ M6TmkZero s_d ∧
                          FullCongReprInv F_cur (2 * s_d.core.cur_vars) s_d.core.repr ∧
                          K6HwmClean L (s_d.scratch.glue_used[33]?.getD 0#32)
                            (k6StateOfScratch L s_d.scratch.scratch_buf) ∧
                          s_d.scratch.tarjan_reach = s_l.scratch.tarjan_reach ∧
                          (FullMem c s_d ⋆ R) md) ?_ ?_
                      · rintro _ ⟨⟩ md ⟨s_d, hdw_d, hcv_d, hfl_d, htmk_d, hrep_d, hhwm_d, htrc_d,
                            hm_d⟩
                        have hscr_d : s_d.scratch.scratch_buf.length = c.scratch_cap :=
                          hdw_d.1.scratch_ok.scratch_buf_len
                        have hk11_sd :
                            (BitVec.setWidth 64 (BitVec.ofNat 32 (L.k6Base + 11))).toNat <
                              s_d.scratch.scratch_buf.length := hscr_d ▸ hk11_idx
                        c0_hsteps_nogrp; try rw [hk11_ptr]; c0_hsteps_nogrp
                        refine wp_join_group (ts := [i64]) (fun (_rt_n, ()) mj' => mj' = md) ?_ ?_
                        · rintro _ ⟨rt_n, ⟨⟩⟩ mj' hmj'; subst mj'; c0_hsteps_nogrp
                          refine wp_join_group (ts := [i32])
                            (fun (nc_n, ()) mn => nc_l.toNat ≤ nc_n.toNat ∧
                              nc_n.toNat ≤ 2 * s1.core.cur_vars ∧
                              S13LoopInv c F0 F_cur s1 L R nc_n.toNat mn) ?_ ?_
                          · rintro _ ⟨nc_n, ⟨⟩⟩ mn ⟨hnc_lo, hnc_hi, hinv_n⟩
                            c0_hsteps!
                            exact hJ_n (rt_n, rb_l - 1#64, nc_n, ()) mn
                              ⟨Or.inl ⟨by omega, by omega, hnc_hi⟩, by omega, hinv_n⟩
                          · intro _ hJ_nc
                            have hRec := s13_sweep_vars_recollect_wp Q X hFind (budget := budget)
                              (tlim := tlim) (comp := comp_a) (mo := mo_a) (nm := nm_a)
                              (rem_ticks := rem_ticks) (nc0 := nc0) (rt_l := rt_l) (rb_l := rb_l)
                              (nc_l := nc_l) (ci_l := ci_l) (sw0 := s_v.scratch.sweep_cnt) hL_len
                              hdw_d hcv_d hfl_d htmk_d hrep_d hhwm_d
                              (fun i hi => htrc_d ▸ hbd_cands i hi) hnc_le hcv1_lt hm_d
                              (fun nc_n mn h1 h2 h3 => hJ_nc (nc_n, ()) mn ⟨h1, h2, h3⟩)
                            unfold s13SwRecollectBody at hRec
                            dsimp only [s13SwAtMainLoop, s13SwAfterMark,
                              s13SwAtMark, s13SwAtNm, s13SwLet, s13SwLet64, s13SwLetB, s13SwLd8,
                              s13SwLd32, s13SwLd64, s13SwSt, s13SwCall64, s13SwCall32, s13SwCallB,
                              s13SwJF, s13SwJT, s13SwGrpB32, s13SwGrpB64, s13SwGrpB0, s13SwGrpB3,
                              s13SwGrpB4, s13SwGrpK0, s13SwGrpK3x, s13SwGrpK32] at hRec
                            exact hRec
                        · intro _ hJ_rt; c0_hsplit
                          · c0_hsteps!; exact hJ_rt (0#64, ()) md rfl
                          · c0_hsteps!; exact hJ_rt (_, ()) md rfl
                      · intro _ hJ_dp
                        c0_hsplit; rotate_left
                        · c0_hsteps!
                          exact hJ_dp () m3 ⟨s3, hdw3, hcv3.trans hcv_l, Nat.le_trans hfl3 hfl_l,
                            htmk3, hrep3, hhwm3, htrc3, hm3⟩
                        · refine s13_call_dense_prop hDP hdw3 hm3
                            (fun ok4 s4 m4 hdw4 hcv4 hfl4 hrp4 htmk4 htrc4 hscr4 hgu4 hno4
                              hm4 => ?_)
                          c0_hsplit; rotate_left
                          · have hokf : ok4 = false := by cases ok4 <;> first | rfl | exact hc
                            c0_hsteps!
                            exact hQ 20#64 s4 m4 (fid_denseInv_of_W hdw4)
                              (hcv4.trans (hcv3.trans (hcv_l.trans hcv1)))
                              (by rw [hfl4]; exact Nat.le_trans hfl3 (hfuel1 ▸ hfl_l))
                              (fid_tmkZero_congr htmk3 hcv4 htmk4) (Or.inr rfl)
                              (fun _ => (hno4 hokf).1) hm4
                          · c0_hsteps!
                            have hrep4 :
                                FullCongReprInv F_cur (2 * s4.core.cur_vars) s4.core.repr := by
                              rw [hcv4, hrp4]; exact hrep3
                            have hhwm4 : K6HwmClean L (s4.scratch.glue_used[33]?.getD 0#32)
                                (k6StateOfScratch L s4.scratch.scratch_buf) := by
                              rw [hgu4, hscr4]; exact hhwm3
                            exact hJ_dp () m4 ⟨s4, hdw4, hcv4.trans (hcv3.trans hcv_l),
                              by rw [hfl4]; exact Nat.le_trans hfl3 hfl_l,
                              fid_tmkZero_congr htmk3 hcv4 htmk4, hrep4, hhwm4,
                              htrc4.trans htrc3, hm4⟩
                · intro _ hJ_cur; c0_hsplit
                  · c0_hsteps!; exact hJ_cur (_, ()) ml rfl
                  · c0_hsteps!; exact hJ_cur (0#32, ()) ml rfl
            · intro _ hJ_rt; c0_hsplit
              · s13_hsteps_to_jmp; exact hJ_rt (0xFFFFFFFF#64, ()) m_ri rfl
              · s13_hsteps_to_jmp; exact hJ_rt (tlim, ()) m_ri rfl
      · intro _ hJb
        have hM := s13_sweep_vars_mark_wp (Q := Q) (X := X) (budget := budget)
          (tlim := tlim) (comp := comp_a) (mo := mo_a) (nm := nm_a)
          hOcc hdw_a hcv_a hfl_a htmk_a hscr_a hgu33_a hcv1_lt hma
          (fun mb s_b h1 h2 h3 h4 h5 h6 h7 => hJb () mb ⟨s_b, h1, h2, h3, h4, h5, h6, h7⟩)
        dsimp only [s13SwMarkBody, s13SwAtMark, s13SwAtNm, s13SwLet, s13SwLet64, s13SwLetB,
          s13SwLd32, s13SwLd64, s13SwSt, s13SwCall64, s13SwCallB, s13SwJF, s13SwJT,
          s13SwGrpB32, s13SwGrpB3, s13SwGrpK0] at hM
        exact hM
    · intro _ hJa
      have hR := s13_sweep_vars_rem_inc_wp (Q := Q) (X := X) (budget := budget) (tlim := tlim)
        (comp := comp0)
        (mo := BitVec.setWidth 64 (1024#32 <<< (comp0.toNat % 32)))
        (nm := (s1.scratch.glue_used[(BitVec.ofNat 64 29).toNat] == 0#32))
        hOcc hdw1 htmk1_z hgu1_33 hcv1_lt hm1
        (fun ca ma na m_a s_a h1 h2 h3 h4 h5 h6 h7 =>
          hJa (ca, ma, na, ()) m_a ⟨s_a, h1, h2, h3, h4, h5, h6, h7⟩)
      dsimp only [s13SwNmBody, s13SwAtNm, s13SwLet, s13SwLet64, s13SwLetB, s13SwLd32, s13SwLd64,
        s13SwSt, s13SwCall64, s13SwCallB, s13SwJF, s13SwJT, s13SwGrpB32, s13SwGrpK3] at hR
      exact hR
  · intro _ hJc
    c0_hsplit
    · c0_hsteps!; exact hJc (5#32, ()) m1 rfl
    · c0_hsteps!; exact hJc (_, ()) m1 rfl

end LeanQbe.T.Examples.Kissat.FullFidelityStep13S1
