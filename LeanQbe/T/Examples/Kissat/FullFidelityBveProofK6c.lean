/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelityBveProofK6c0
import all LeanQbe.T.Examples.Kissat.FullFidelityBveProof0
import all LeanQbe.T.Examples.Kissat.FullFidelityBveProofK6c0
import LeanQbe.T.Examples.Kissat.FullArena
import LeanQbe.T.Examples.Kissat.FullFidelityBveTactics
import LeanQbe.T.Logic.C0Step
import LeanQbe.T.Logic.C0HeadStep
import LeanQbe.T.Logic.ControlComb
import LeanQbe.T.Logic.MemLemmas
import Kraken.Mem
import Kraken.Separation

/-!
# Kissat Fidelity BVE Parity Proofs — `full_k6_extract_and_solve_fid`

Proves `full_k6_extract_and_solve_fid_wp`, dispatching preamble, two-pass clause/var
extraction (`J51` -> `J323`/`J326`), `tmk` cleanup (`J55`), trivial-unit bitmask exit (`J68`/`J70`),
and composition of `fid_k6c_init_solve_wp` with `fid_k6c_watch_solve_wp` (no expose attrs, `std3`).
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelityBve

open LeanQbe.T
open LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full
open LeanQbe.T.Examples.Kissat.Full.FullArenaTactics
open LeanQbe.T.Examples.Kissat.FullFastBveBudgets
open LeanQbe.T.Examples.Kissat.FullM8CoreParity
open LeanQbe.T.Examples.Kissat.FullFidelityBve.FidK6Tactics

private theorem fid_k6c_zext64 (x : BitVec 32) :
    (BitVec.setWidth 64 x).toNat = x.toNat := by bv_omega

/-! ## Compact `FidP6Work` memory tactics -/

namespace FidK6cKTactics

@[scoped c0_load high]
theorem c0_load_fid_w_scr {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {tmp wsort tmk scr : List (BitVec 32)} {i : BitVec 64} (hi : i.toNat < scr.length)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m) :
    loadVal m i32 (c.pScratchBuf + i * 4) = some scr[i.toNat] := by
  simpa [FidP6Work] using c0_load_full_scratch_buf (s := FidP6Work s tmp wsort tmk scr) hi hm

@[scoped c0_load high]
theorem c0_load_fid_w_wsort {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {tmp wsort tmk scr : List (BitVec 32)} {i : BitVec 64} (hi : i.toNat < wsort.length)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m) :
    loadVal m i32 (c.pWsort + i * 4) = some wsort[i.toNat] := by
  simpa [FidP6Work] using c0_load_full_wsort (s := FidP6Work s tmp wsort tmk scr) hi hm

@[scoped c0_load high]
theorem c0_load_fid_w_tmk {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {tmp wsort tmk scr : List (BitVec 32)} {i : BitVec 64} (hi : i.toNat < tmk.length)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m) :
    loadVal m i32 (c.pTarjanMark + i * 4) = some tmk[i.toNat] := by
  simpa [FidP6Work] using c0_load_full_tarjan_mark (s := FidP6Work s tmp wsort tmk scr) hi hm

@[scoped c0_load high]
theorem c0_load_fid_w_tmp {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {tmp wsort tmk scr : List (BitVec 32)} {i : BitVec 64} (hi : i.toNat < tmp.length)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m) :
    loadVal m i32 (c.pTmp + i * 4) = some tmp[i.toNat] := by
  simpa [FidP6Work] using c0_load_full_tmp (s := FidP6Work s tmp wsort tmk scr) hi hm

@[scoped c0_load high]
theorem c0_load_fid_w_vals {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {tmp wsort tmk scr : List (BitVec 32)} {i : BitVec 64} (hi : i.toNat < s.core.vals.length)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m) :
    loadVal m i8 (c.pVals + i) = some s.core.vals[i.toNat] := by
  simpa [FidP6Work] using c0_load_full_vals (s := FidP6Work s tmp wsort tmk scr) hi hm

@[scoped c0_load high]
theorem c0_load_fid_w_arena {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {tmp wsort tmk scr : List (BitVec 32)} {i : BitVec 64} (hi : i.toNat < s.core.arena.length)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m) :
    loadVal m i32 (c.pArena + i * 4) = some s.core.arena[i.toNat] := by
  simpa [FidP6Work] using c0_load_full_arena (s := FidP6Work s tmp wsort tmk scr) hi hm

@[scoped c0_store high]
theorem c0_store_fid_w_scr {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {tmp wsort tmk scr : List (BitVec 32)} {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < scr.length)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m) :
    storeOk m i32 (c.pScratchBuf + i * 4) ∧
      (FullMem c (FidP6Work s tmp wsort tmk (scr.set i.toNat v)) ⋆ R)
        (storeMem m i32 (c.pScratchBuf + i * 4) v) := by
  simpa [FidP6Work] using c0_store_full_scratch_buf (s := FidP6Work s tmp wsort tmk scr) v hi hm

@[scoped c0_store high]
theorem c0_store_fid_w_scr_nat {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {tmp wsort tmk scr : List (BitVec 32)} {n : Nat} (v : BitVec 32)
    (hn : n < scr.length) (hn2 : n < 2 ^ 30)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m) :
    storeOk m i32 (c.pScratchBuf + BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat n) * 4) ∧
      (FullMem c (FidP6Work s tmp wsort tmk (scr.set n v)) ⋆ R)
        (storeMem m i32 (c.pScratchBuf + BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat n) * 4) v) := by
  have hn_lt : n < 2 ^ 64 := Nat.lt_trans hn2 (by decide)
  have hmod : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat n)).toNat = n := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn_lt
  have hlt : (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat n)).toNat < scr.length := by
    rw [hmod]; exact hn
  have hm' := c0_store_fid_w_scr v hlt hm
  rwa [hmod] at hm'

@[scoped c0_store high]
theorem c0_store_fid_w_wsort {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {tmp wsort tmk scr : List (BitVec 32)} {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < wsort.length)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m) :
    storeOk m i32 (c.pWsort + i * 4) ∧
      (FullMem c (FidP6Work s tmp (wsort.set i.toNat v) tmk scr) ⋆ R)
        (storeMem m i32 (c.pWsort + i * 4) v) := by
  simpa [FidP6Work] using c0_store_full_wsort (s := FidP6Work s tmp wsort tmk scr) v hi hm

@[scoped c0_store high]
theorem c0_store_fid_w_tmk {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {tmp wsort tmk scr : List (BitVec 32)} {i : BitVec 64} (v : BitVec 32)
    (hi : i.toNat < tmk.length)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m) :
    storeOk m i32 (c.pTarjanMark + i * 4) ∧
      (FullMem c (FidP6Work s tmp wsort (tmk.set i.toNat v) scr) ⋆ R)
        (storeMem m i32 (c.pTarjanMark + i * 4) v) := by
  simpa [FidP6Work] using c0_store_full_tarjan_mark (s := FidP6Work s tmp wsort tmk scr) v hi hm

end FidK6cKTactics

open FidK6cKTactics

/-! ## Pure arithmetic, `FidK6cClsOk`, and small loop helpers -/

private theorem fid_k6c_maxV_bounds {cap : Nat} (hcap : 16384 ≤ cap) :
    256 ≤ fidK6MaxV cap ∧ fidK6MaxV cap ≤ 8192 ∧ 4224 + 45 * fidK6MaxV cap ≤ cap := by
  unfold fidK6MaxV
  by_cases h1 : cap < 16384
  · omega
  · simp only [h1, ↓reduceIte]
    by_cases h2 : 524288 ≤ cap
    · simp only [h2, ↓reduceIte]; exact ⟨by omega, by omega, by omega⟩
    · simp only [h2, ↓reduceIte]
      have hq : (cap - 4224) / 64 / 64 * 64 ≤ (cap - 4224) / 64 := Nat.div_mul_le_self _ 64
      have hm : 64 * ((cap - 4224) / 64) ≤ cap - 4224 := by
        simpa [Nat.mul_comm] using Nat.div_mul_le_self (cap - 4224) 64
      have hr : (cap - 4224) / 64 / 64 * 64 ≤ (cap - 4224) / 45 := by omega
      have hmin : min 8192 ((cap - 4224) / 64 / 64 * 64) ≤ (cap - 4224) / 45 :=
        Nat.le_trans (Nat.min_le_right _ _) hr
      have hlo : 256 ≤ max 256 (min 8192 ((cap - 4224) / 64 / 64 * 64)) := Nat.le_max_left _ _
      have hhi : max 256 (min 8192 ((cap - 4224) / 64 / 64 * 64)) ≤ 8192 :=
        Nat.max_le.mpr ⟨by omega, Nat.min_le_left _ _⟩
      have hfit_raw : max 256 (min 8192 ((cap - 4224) / 64 / 64 * 64)) ≤ (cap - 4224) / 45 :=
        Nat.max_le.mpr ⟨by omega, hmin⟩
      have hfit : 45 * max 256 (min 8192 ((cap - 4224) / 64 / 64 * 64)) ≤ cap - 4224 := by
        calc 45 * max 256 (min 8192 ((cap - 4224) / 64 / 64 * 64))
          _ ≤ 45 * ((cap - 4224) / 45) := Nat.mul_le_mul_left 45 hfit_raw
          _ ≤ cap - 4224 := by simpa [Nat.mul_comm] using Nat.div_mul_le_self (cap - 4224) 45
      exact ⟨hlo, hhi, by omega⟩

private theorem fid_k6c_bin_clsOk {mv_s nc alen n_units eid cval : BitVec 32}
    {o_arena o_off o_meta o_aux o_units : BitVec 32}
    {scr : List (BitVec 32)} {acap_n : Nat}
    (hmv_lo : 256 ≤ mv_s.toNat) (hmv_hi : mv_s.toNat ≤ 8192)
    (hcap_ar : 4224 + 45 * mv_s.toNat + acap_n ≤ scr.length) (hlen_lt : scr.length < 2 ^ 30)
    (hoff_off : o_off = 4224#32 + 29#32 * mv_s)
    (hoff_meta : o_meta = 4224#32 + 33#32 * mv_s)
    (hoff_aux : o_aux = 4224#32 + 37#32 * mv_s)
    (hoff_units : o_units = 4224#32 + 41#32 * mv_s)
    (hoff_arena : o_arena = 4224#32 + 45#32 * mv_s)
    (hnc : nc.toNat < 2 * mv_s.toNat) (halen : alen.toNat + 1 ≤ acap_n)
    (hnu : n_units.toNat ≤ nc.toNat)
    (heid : eid.toNat < 4096 ∧ (eid &&& 2047#32).toNat < 2001)
    (hcls : FidK6cClsOk mv_s.toNat nc.toNat alen.toNat n_units.toNat scr) :
    let scr1 := scr.set (BitVec.setWidth 64 (o_arena + alen)).toNat cval
    let scr2 := scr1.set (BitVec.setWidth 64 (o_off + nc)).toNat alen
    let scr3 := scr2.set (BitVec.setWidth 64 (o_meta + nc)).toNat 1#32
    let scr4 := scr3.set (BitVec.setWidth 64 (o_aux + nc)).toNat eid
    let scr5 := scr4.set (BitVec.setWidth 64 (o_units + n_units)).toNat nc
    FidK6cClsOk mv_s.toNat (nc + 1#32).toNat (alen + 1#32).toNat (n_units + 1#32).toNat scr5 := by
  have har : (BitVec.setWidth 64 (o_arena + alen)).toNat = 4224 + 45 * mv_s.toNat + alen.toNat :=
    by rw [hoff_arena]; exact fid_k6_off_add hmv_hi (by omega) (by omega)
  have hof : (BitVec.setWidth 64 (o_off + nc)).toNat = 4224 + 29 * mv_s.toNat + nc.toNat := by
    rw [hoff_off]; exact fid_k6_off_add hmv_hi (by omega) (by omega)
  have hmt : (BitVec.setWidth 64 (o_meta + nc)).toNat = 4224 + 33 * mv_s.toNat + nc.toNat := by
    rw [hoff_meta]; exact fid_k6_off_add hmv_hi (by omega) (by omega)
  have hax : (BitVec.setWidth 64 (o_aux + nc)).toNat = 4224 + 37 * mv_s.toNat + nc.toNat := by
    rw [hoff_aux]; exact fid_k6_off_add hmv_hi (by omega) (by omega)
  have hun : (BitVec.setWidth 64 (o_units + n_units)).toNat =
      4224 + 41 * mv_s.toNat + n_units.toNat := by
    rw [hoff_units]; exact fid_k6_off_add hmv_hi (by omega) (by omega)
  have hnc1 : (nc + 1#32).toNat = nc.toNat + 1 := fid_k6c_add1_toNat hnc (by omega)
  have hal1 : (alen + 1#32).toNat = alen.toNat + 1 :=
    fid_k6c_add1_toNat (by omega : alen.toNat < acap_n) (by omega)
  have hnu1 : (n_units + 1#32).toNat = n_units.toNat + 1 :=
    fid_k6c_add1_toNat (by omega : n_units.toNat < 2 * mv_s.toNat) (by omega)
  dsimp only [FidK6cClsOk]
  rw [hnc1, hal1, hnu1]
  refine ⟨by omega, ?_, by omega⟩
  intro cid hcid
  by_cases hlt : cid < nc.toNat
  · have hc := hcls.2.1 cid hlt
    let scr5 := (((scr.set (BitVec.setWidth 64 (o_arena + alen)).toNat cval).set
      (BitVec.setWidth 64 (o_off + nc)).toNat alen).set
      (BitVec.setWidth 64 (o_meta + nc)).toNat 1#32).set
      (BitVec.setWidth 64 (o_aux + nc)).toNat eid |>.set
      (BitVec.setWidth 64 (o_units + n_units)).toNat nc
    have he1 : scr5[4224 + 29 * mv_s.toNat + cid]? = scr[4224 + 29 * mv_s.toNat + cid]? := by
      dsimp only [scr5]; repeat rw [List.getElem?_set_ne (by omega)]
    have he2 : scr5[4224 + 33 * mv_s.toNat + cid]? = scr[4224 + 33 * mv_s.toNat + cid]? := by
      dsimp only [scr5]; repeat rw [List.getElem?_set_ne (by omega)]
    have he3 : scr5[4224 + 37 * mv_s.toNat + cid]? = scr[4224 + 37 * mv_s.toNat + cid]? := by
      dsimp only [scr5]; repeat rw [List.getElem?_set_ne (by omega)]
    change _ ∧ _ ∧ _ ∧ _ at hc
    dsimp only [scr5] at he1 he2 he3
    rw [he1, he2, he3]
    exact ⟨by omega, hc.2.1, hc.2.2⟩
  · have hceq : cid = nc.toNat := by omega
    subst hceq
    let scr5 := (((scr.set (BitVec.setWidth 64 (o_arena + alen)).toNat cval).set
      (BitVec.setWidth 64 (o_off + nc)).toNat alen).set
      (BitVec.setWidth 64 (o_meta + nc)).toNat 1#32).set
      (BitVec.setWidth 64 (o_aux + nc)).toNat eid |>.set
      (BitVec.setWidth 64 (o_units + n_units)).toNat nc
    have hlo1 : scr5[4224 + 29 * mv_s.toNat + nc.toNat]? = some alen := by
      dsimp only [scr5]
      (repeat rw [List.getElem?_set_ne (by omega)])
      rw [← hof]; exact List.getElem?_set_self (by simp only [List.length_set]; omega)
    have hlo2 : scr5[4224 + 33 * mv_s.toNat + nc.toNat]? = some 1#32 := by
      dsimp only [scr5]
      (repeat rw [List.getElem?_set_ne (by omega)])
      rw [← hmt]; exact List.getElem?_set_self (by simp only [List.length_set]; omega)
    have hlo3 : scr5[4224 + 37 * mv_s.toNat + nc.toNat]? = some eid := by
      dsimp only [scr5]
      rw [List.getElem?_set_ne (by omega), ← hax]
      exact List.getElem?_set_self (by simp only [List.length_set]; omega)
    dsimp only [scr5] at hlo1 hlo2 hlo3
    rw [hlo1, hlo2, hlo3]
    simp only [Option.getD_some]
    refine ⟨by rw [show (1#32 &&& 65535#32).toNat = 1 by decide]; omega, by decide, heid⟩

/-- Clear `tarjan_mark[wsort[0..nv)]` (`J55` loop). -/
private theorem fid_k6c_tmk_clear_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost}
    {K_next : Expr Val Cont [Ty.bool]}
    {c : FullCfg} {F0 : Std.Sat.CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {tmp wsort tmk scr : List (BitVec 32)} {nv : BitVec 32}
    (hinv : FullDenseInvW c F0 F_cur s)
    (htmp : tmp.length = c.max_vars) (hwsort : wsort.length = 2 * c.max_vars)
    (htmk : tmk.length = 2 * c.max_vars) (hreg : FidK6cTmkReg nv.toNat s.core.cur_vars wsort tmk)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m)
    (hNext : ∀ tmk' m',
      tmk'.length = 2 * c.max_vars →
      (∀ v, v < s.core.cur_vars → tmk'[v]?.getD 0#32 = 0#32) →
      (FullMem c (FidP6Work s tmp wsort tmk' scr) ⋆ R) m' → wp Γ Q X K_next m') :
    wp Γ Q X
      (Expr.group (fun Js : Tup Cont [[i32]] => Blocks.cons (fun pk : Tup Val [i32] =>
        Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl) (Arg.var pk.fst, Arg.var nv, ()))
          fun p57 =>
        Expr.jnz (Arg.var p57.fst)
          (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var pk.fst, ())) fun p58 =>
          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p58.fst, Arg.imm 4, ())) fun p59 =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pWsort, Arg.var p59.fst, ())) fun p60 =>
          Expr.load i32 (Arg.var p60.fst) fun ld61 =>
          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ld61, ())) fun p62 =>
          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p62.fst, Arg.imm 4, ())) fun p63 =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pTarjanMark, Arg.var p63.fst, ()))
            fun p64 =>
          Expr.store (t := i32) (Arg.imm 0) (Arg.var p64.fst)
            (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pk.fst, Arg.imm 1, ())) fun p65 =>
            Expr.jump Js.fst (Arg.var p65.fst, ())))
          K_next) Blocks.nil)
      fun Js => Expr.jump Js.fst (Arg.imm 0, ())) m := by
  have hcv_mv : s.core.cur_vars ≤ c.max_vars := hinv.1.core_ok.cur_vars_le
  have hcv_lt : 2 * s.core.cur_vars < 2 ^ 30 := by
    have := c.hmaxv; simp only [Examples.LratBytes.dimacsBound] at this; omega
  apply wp_loop_inv
    (Inv := fun (pk : BitVec 32 × Unit) m1 => ∃ tmk1, pk.1.toNat ≤ nv.toNat ∧
      tmk1.length = 2 * c.max_vars ∧
      FidK6cTmkClearInv pk.1.toNat nv.toNat s.core.cur_vars wsort tmk1 ∧
      (FullMem c (FidP6Work s tmp wsort tmk1 scr) ⋆ R) m1)
    (μ := fun (pk : BitVec 32 × Unit) _ => nv.toNat - pk.1.toNat)
  · intro J hJ; c0_hsteps; exact hJ _ _ ⟨tmk, Nat.zero_le _, htmk, fid_k6c_tmkClear_init hreg, hm⟩
  · intro J pk m1 ⟨tmk1, hk_le, htmk1, hcl, hm1⟩ hcont
    dsimp only [Blocks.get, Member.here]
    dsimp only [FidK6cTmkReg] at hreg
    dsimp only [FidK6cTmkClearInv] at hcl
    c0_hsteps
    · have hk_lt : pk.fst.toNat < nv.toNat := by bv_omega
      have hpk64 : (BitVec.setWidth 64 pk.fst).toNat = pk.fst.toNat := by bv_omega
      have hws : (BitVec.setWidth 64 pk.fst).toNat < wsort.length := by
        have := hreg.1; omega
      have hinfo := hcl.2.1 pk.fst.toNat (Nat.le_refl _) hk_lt
      have hws_get : wsort[pk.fst.toNat]?.getD 0#32 = wsort[pk.fst.toNat] := by
        simp [List.getElem?_eq_getElem (by omega : pk.fst.toNat < wsort.length)]
      rw [hws_get] at hinfo
      have hws64 : (BitVec.setWidth 64 wsort[(BitVec.setWidth 64 pk.fst).toNat]).toNat =
          wsort[pk.fst.toNat].toNat := by
        have hv32 : wsort[pk.fst.toNat].toNat < 2 ^ 64 :=
          Nat.lt_trans (BitVec.isLt _) (by decide)
        simp only [BitVec.toNat_setWidth, hpk64]
        exact Nat.mod_eq_of_lt hv32
      have htmk_lt : (BitVec.setWidth 64 wsort[(BitVec.setWidth 64 pk.fst).toNat]).toNat <
          tmk1.length := by
        rw [hws64]; omega
      c0_hsteps
      have hk1 : (pk.fst + 1#32).toNat = pk.fst.toNat + 1 := fid_k6c_add1_toNat hk_lt (by omega)
      refine hcont (pk.fst + 1#32, ()) _ (by dsimp only; omega)
        ⟨tmk1.set (BitVec.setWidth 64 wsort[(BitVec.setWidth 64 pk.fst).toNat]).toNat 0#32,
          by dsimp only; omega, by simp [htmk1], ?_, hm⟩
      rw [hws64, hk1]
      exact fid_k6c_tmkClear_step hcl hk_lt (by omega) (by omega : s.core.cur_vars ≤ tmk1.length)
    · have hkeq : pk.fst.toNat = nv.toNat := by bv_omega
      rw [hkeq] at hcl
      exact hNext tmk1 m1 htmk1 (fid_k6c_tmkClear_done hcl) hm1

/-- Zero `scr[4002..4130)` (`J70` loop). -/
private theorem fid_k6c_zero_mask_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost}
    {K_next : Expr Val Cont [Ty.bool]}
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {tmp wsort tmk scr : List (BitVec 32)}
    (hcap : 16384 ≤ c.scratch_cap) (hscr_len : scr.length = c.scratch_cap)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m)
    (hNext : ∀ scr' m', scr'.length = c.scratch_cap →
      (∀ i, i < 4002 → scr'[i]? = scr[i]?) →
      (∀ i, 4132 ≤ i → i < 4192 → scr'[i]? = scr[i]?) →
      (FullMem c (FidP6Work s tmp wsort tmk scr') ⋆ R) m' → wp Γ Q X K_next m') :
    wp Γ Q X
      (Expr.group (fun Js : Tup Cont [[i32]] => Blocks.cons (fun pu : Tup Val [i32] =>
        Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl) (Arg.var pu.fst, Arg.imm 128, ()))
          fun p72 =>
        Expr.jnz (Arg.var p72.fst)
          (Expr.let_ (Op.mk (OpCode.add i32) (Arg.imm 4002, Arg.var pu.fst, ())) fun p73 =>
          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p73.fst, ())) fun p74 =>
          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p74.fst, Arg.imm 4, ())) fun p75 =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p75.fst, ()))
            fun p76 =>
          Expr.store (t := i32) (Arg.imm 0) (Arg.var p76.fst)
            (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pu.fst, Arg.imm 1, ())) fun p77 =>
            Expr.jump Js.fst (Arg.var p77.fst, ())))
          K_next) Blocks.nil)
      fun Js => Expr.jump Js.fst (Arg.imm 0, ())) m := by
  apply wp_loop_inv
    (Inv := fun (pu : BitVec 32 × Unit) m1 => ∃ scr1, pu.1.toNat ≤ 128 ∧
      scr1.length = c.scratch_cap ∧
      (∀ i, i < 4002 → scr1[i]? = scr[i]?) ∧
      (∀ i, 4132 ≤ i → i < 4192 → scr1[i]? = scr[i]?) ∧
      (FullMem c (FidP6Work s tmp wsort tmk scr1) ⋆ R) m1)
    (μ := fun (pu : BitVec 32 × Unit) _ => 128 - pu.1.toNat)
  · intro J hJ; c0_hsteps
    exact hJ _ _ ⟨scr, Nat.zero_le _, hscr_len, fun _ _ => rfl, fun _ _ _ => rfl, hm⟩
  · intro J pu m1 ⟨scr1, hu_le, hlen1, hp0, hp1, hm1⟩ hcont
    dsimp only [Blocks.get, Member.here]
    c0_hsteps
    · have hu_lt : pu.fst.toNat < 128 := by bv_omega
      have hidx : (BitVec.setWidth 64 ((4002 : Val i32) + pu.fst)).toNat = 4002 + pu.fst.toNat :=
        by bv_omega
      have hlt_scr : (BitVec.setWidth 64 ((4002 : Val i32) + pu.fst)).toNat < scr1.length := by
        omega
      c0_hsteps
      try rw [hidx] at hm
      have hu1 : (pu.fst + 1#32).toNat = pu.fst.toNat + 1 := fid_k6c_add1_toNat hu_lt (by omega)
      refine hcont (pu.fst + 1#32, ()) _ (by dsimp only; omega) ⟨_, by dsimp only; omega,
        by simp [hlen1], ?_, ?_, hm⟩
      · intro i hi; rw [List.getElem?_set_ne (by omega)]; exact hp0 i hi
      · intro i h1 h2; rw [List.getElem?_set_ne (by omega)]; exact hp1 i h1 h2
    · exact hNext scr1 m1 hlen1 hp0 hp1 hm1

/-! ## Post-extraction phase (`J55`: cleanup, trivial-unit exit, or `init_solve` + `watch_solve`) -/

private abbrev fidPostHdrInitWatchExpr (c : FullCfg)
    (nv nc alen acap n_units _trivial_eid tick_lim mv_s mc_s max_orig_s
      o_rsn o_qprev o_qnext o_qst o_flags o_vals o_whead
      o_cl_off o_cl_meta o_cl_aux o_arena : Val i32) : Expr Val Cont [Ty.bool] :=
  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4192, ())) fun p0 =>
        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p0.fst, Arg.imm 4, ())) fun p1 =>
        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p1.fst, ()))
          fun p2 =>
        Expr.store (t := i32) (Arg.var nv) (Arg.var p2.fst)
          (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4193, ())) fun p3 =>
          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p3.fst, Arg.imm 4, ())) fun p4 =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p4.fst, ()))
            fun p5 =>
          Expr.store (t := i32) (Arg.var nc) (Arg.var p5.fst)
            (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4194, ())) fun p6 =>
            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p6.fst, Arg.imm 4, ())) fun p7 =>
            Expr.let_ (Op.mk (OpCode.add i64)
              (Arg.var c.pScratchBuf, Arg.var p7.fst, ())) fun p8 =>
            Expr.store (t := i32) (Arg.var nc) (Arg.var p8.fst)
              (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4195, ())) fun p9 =>
              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p9.fst, Arg.imm 4, ()))
                fun p10 =>
              Expr.let_ (Op.mk (OpCode.add i64)
                (Arg.var c.pScratchBuf, Arg.var p10.fst, ())) fun p11 =>
              Expr.store (t := i32) (Arg.imm 0) (Arg.var p11.fst)
                (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4196, ())) fun p12 =>
                Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p12.fst, Arg.imm 4, ()))
                  fun p13 =>
                Expr.let_ (Op.mk (OpCode.add i64)
                  (Arg.var c.pScratchBuf, Arg.var p13.fst, ())) fun p14 =>
                Expr.store (t := i32) (Arg.imm 0) (Arg.var p14.fst)
                  (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4197, ())) fun p15 =>
                  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p15.fst, Arg.imm 4, ()))
                    fun p16 =>
                  Expr.let_ (Op.mk (OpCode.add i64)
                    (Arg.var c.pScratchBuf, Arg.var p16.fst, ())) fun p17 =>
                  Expr.store (t := i32) (Arg.imm 0) (Arg.var p17.fst)
                    (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4198, ())) fun p18 =>
                    Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p18.fst, Arg.imm 4, ()))
                      fun p19 =>
                    Expr.let_ (Op.mk (OpCode.add i64)
                      (Arg.var c.pScratchBuf, Arg.var p19.fst, ())) fun p20 =>
                    Expr.store (t := i32) (Arg.var nv) (Arg.var p20.fst)
                      (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4199, ()))
                        fun p21 =>
                      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p21.fst, Arg.imm 4, ()))
                        fun p22 =>
                      Expr.let_ (Op.mk (OpCode.add i64)
                        (Arg.var c.pScratchBuf, Arg.var p22.fst, ())) fun p23 =>
                      Expr.store (t := i32) (Arg.imm 4294967295) (Arg.var p23.fst)
                        (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4200, ()))
                          fun p24 =>
                        Expr.let_ (Op.mk (OpCode.mul i64)
                          (Arg.var p24.fst, Arg.imm 4, ())) fun p25 =>
                        Expr.let_ (Op.mk (OpCode.add i64)
                          (Arg.var c.pScratchBuf, Arg.var p25.fst, ())) fun p26 =>
                        Expr.store (t := i32) (Arg.imm 0) (Arg.var p26.fst)
                          (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4201, ()))
                            fun p27 =>
                          Expr.let_ (Op.mk (OpCode.mul i64)
                            (Arg.var p27.fst, Arg.imm 4, ())) fun p28 =>
                          Expr.let_ (Op.mk (OpCode.add i64)
                            (Arg.var c.pScratchBuf, Arg.var p28.fst, ())) fun p29 =>
                          Expr.let_ (Op.mk (OpCode.sub i32) (Arg.var nv, Arg.imm 1, ()))
                            fun p30 =>
                          Expr.store (Arg.var p30.fst) (Arg.var p29.fst)
                            (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4202, ()))
                              fun p31 =>
                            Expr.let_ (Op.mk (OpCode.mul i64)
                              (Arg.var p31.fst, Arg.imm 4, ())) fun p32 =>
                            Expr.let_ (Op.mk (OpCode.add i64)
                              (Arg.var c.pScratchBuf, Arg.var p32.fst, ())) fun p33 =>
                            Expr.let_ (Op.mk (OpCode.sub i32)
                              (Arg.var nv, Arg.imm 1, ())) fun p34 =>
                            Expr.store (Arg.var p34.fst) (Arg.var p33.fst)
                              (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4203, ()))
                                fun p35 =>
                              Expr.let_ (Op.mk (OpCode.mul i64)
                                (Arg.var p35.fst, Arg.imm 4, ())) fun p36 =>
                              Expr.let_ (Op.mk (OpCode.add i64)
                                (Arg.var c.pScratchBuf, Arg.var p36.fst, ())) fun p37 =>
                              Expr.store (t := i32) (Arg.var nv) (Arg.var p37.fst)
                                (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4204, ()))
                                  fun p38 =>
                                Expr.let_ (Op.mk (OpCode.mul i64)
                                  (Arg.var p38.fst, Arg.imm 4, ())) fun p39 =>
                                Expr.let_ (Op.mk (OpCode.add i64)
                                  (Arg.var c.pScratchBuf, Arg.var p39.fst, ())) fun p40 =>
                                Expr.store (t := i32) (Arg.imm 0) (Arg.var p40.fst)
                                  (Expr.let_ (Op.mk (OpCode.zext 32 64)
                                    (Arg.imm 4205, ())) fun p41 =>
                                  Expr.let_ (Op.mk (OpCode.mul i64)
                                    (Arg.var p41.fst, Arg.imm 4, ())) fun p42 =>
                                  Expr.let_ (Op.mk (OpCode.add i64)
                                    (Arg.var c.pScratchBuf, Arg.var p42.fst, ()))
                                    fun p43 =>
                                  Expr.store (t := i32) (Arg.var tick_lim)
                                    (Arg.var p43.fst)
                                    (Expr.let_ (Op.mk (OpCode.zext 32 64)
                                      (Arg.imm 4206, ())) fun p44 =>
                                    Expr.let_ (Op.mk (OpCode.mul i64)
                                      (Arg.var p44.fst, Arg.imm 4, ())) fun p45 =>
                                    Expr.let_ (Op.mk (OpCode.add i64)
                                      (Arg.var c.pScratchBuf, Arg.var p45.fst, ()))
                                      fun p46 =>
                                    Expr.store (t := i32) (Arg.var alen) (Arg.var p46.fst)
                                      (Expr.let_ (Op.mk (OpCode.zext 32 64)
                                        (Arg.imm 4207, ())) fun p47 =>
                                      Expr.let_ (Op.mk (OpCode.mul i64)
                                        (Arg.var p47.fst, Arg.imm 4, ())) fun p48 =>
                                      Expr.let_ (Op.mk (OpCode.add i64)
                                        (Arg.var c.pScratchBuf, Arg.var p48.fst, ()))
                                        fun p49 =>
                                      Expr.store (t := i32) (Arg.var acap)
                                        (Arg.var p49.fst)
                                        (Expr.let_ (Op.mk (OpCode.zext 32 64)
                                          (Arg.imm 4208, ())) fun p50 =>
                                        Expr.let_ (Op.mk (OpCode.mul i64)
                                          (Arg.var p50.fst, Arg.imm 4, ())) fun p51 =>
                                        Expr.let_ (Op.mk (OpCode.add i64)
                                          (Arg.var c.pScratchBuf, Arg.var p51.fst, ()))
                                          fun p52 =>
                                        Expr.store (t := i32) (Arg.imm 0)
                                          (Arg.var p52.fst)
                                          (Expr.let_ (Op.mk (OpCode.zext 32 64)
                                            (Arg.imm 4209, ())) fun p53 =>
                                          Expr.let_ (Op.mk (OpCode.mul i64)
                                            (Arg.var p53.fst, Arg.imm 4, ())) fun p54 =>
                                          Expr.let_ (Op.mk (OpCode.add i64)
                                            (Arg.var c.pScratchBuf, Arg.var p54.fst, ()))
                                            fun p55 =>
                                          Expr.store (t := i32) (Arg.imm 0)
                                            (Arg.var p55.fst)
                                            (Expr.let_ (Op.mk (OpCode.zext 32 64)
                                              (Arg.imm 4210, ())) fun p56 =>
                                            Expr.let_ (Op.mk (OpCode.mul i64)
                                              (Arg.var p56.fst, Arg.imm 4, ())) fun p57 =>
                                            Expr.let_ (Op.mk (OpCode.add i64)
                                              (Arg.var c.pScratchBuf, Arg.var p57.fst,
                                                ())) fun p58 =>
                                            Expr.store (t := i32) (Arg.imm 0)
                                              (Arg.var p58.fst)
                                              (Expr.let_ (Op.mk (OpCode.zext 32 64)
                                                (Arg.imm 4211, ())) fun p59 =>
                                              Expr.let_ (Op.mk (OpCode.mul i64)
                                                (Arg.var p59.fst, Arg.imm 4, ()))
                                                fun p60 =>
                                              Expr.let_ (Op.mk (OpCode.add i64)
                                                (Arg.var c.pScratchBuf, Arg.var p60.fst,
                                                  ())) fun p61 =>
                                              Expr.store (t := i32) (Arg.var n_units)
                                                (Arg.var p61.fst)
                                                (Expr.let_ (Op.mk (OpCode.zext 32 64)
                                                  (Arg.imm 4212, ())) fun p62 =>
                                                Expr.let_ (Op.mk (OpCode.mul i64)
                                                  (Arg.var p62.fst, Arg.imm 4, ()))
                                                  fun p63 =>
                                                Expr.let_ (Op.mk (OpCode.add i64)
                                                  (Arg.var c.pScratchBuf, Arg.var p63.fst,
                                                    ())) fun p64 =>
                                                Expr.store (t := i32) (Arg.imm 0)
                                                  (Arg.var p64.fst)
                                                  (Expr.let_ (Op.mk (OpCode.zext 32 64)
                                                    (Arg.imm 4213, ())) fun p65 =>
                                                  Expr.let_ (Op.mk (OpCode.mul i64)
                                                    (Arg.var p65.fst, Arg.imm 4, ()))
                                                    fun p66 =>
                                                  Expr.let_ (Op.mk (OpCode.add i64)
                                                    (Arg.var c.pScratchBuf,
                                                      Arg.var p66.fst, ())) fun p67 =>
                                                  Expr.store (t := i32) (Arg.imm 0)
                                                    (Arg.var p67.fst)
                                                    (Expr.let_ (Op.mk (OpCode.zext 32 64)
                                                      (Arg.imm 4214, ())) fun p68 =>
                                                    Expr.let_ (Op.mk (OpCode.mul i64)
                                                      (Arg.var p68.fst, Arg.imm 4, ()))
                                                      fun p69 =>
                                                    Expr.let_ (Op.mk (OpCode.add i64)
                                                      (Arg.var c.pScratchBuf,
                                                        Arg.var p69.fst, ())) fun p70 =>
                                                    Expr.store (t := i32) (Arg.var mv_s)
                                                      (Arg.var p70.fst)
                                                      (Expr.let_
                                                        (Op.mk (OpCode.zext 32 64)
                                                          (Arg.imm 4215, ())) fun p71 =>
                                                      Expr.let_ (Op.mk (OpCode.mul i64)
                                                        (Arg.var p71.fst, Arg.imm 4, ()))
                                                        fun p72 =>
                                                      Expr.let_ (Op.mk (OpCode.add i64)
                                                        (Arg.var c.pScratchBuf,
                                                          Arg.var p72.fst, ())) fun p73 =>
                                                      Expr.store (t := i32) (Arg.var mc_s)
                                                        (Arg.var p73.fst)
                                                        (Expr.let_
                                                          (Op.mk (OpCode.zext 32 64)
                                                            (Arg.imm 4216, ())) fun p74 =>
                                                        Expr.let_ (Op.mk (OpCode.mul i64)
                                                          (Arg.var p74.fst, Arg.imm 4,
                                                            ())) fun p75 =>
                                                        Expr.let_ (Op.mk (OpCode.add i64)
                                                          (Arg.var c.pScratchBuf,
                                                            Arg.var p75.fst, ()))
                                                          fun p76 =>
                                                        Expr.store (t := i32)
                                                          (Arg.var max_orig_s)
                                                          (Arg.var p76.fst)
(Expr.group (fun Js : Tup Cont [[i32]] => Blocks.cons (fun pi : Tup Val [i32] =>
Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl) (Arg.var pi.fst, Arg.var nv, ()))
fun p77 =>
Expr.jnz (Arg.var p77.fst)
(Expr.let_ (Op.mk (OpCode.add i32) (Arg.imm 4224, Arg.var pi.fst, ())) fun p78 =>
Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p78.fst, ())) fun p79 =>
Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p79.fst, Arg.imm 4, ())) fun p80 =>
Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p80.fst, ())) fun p81 =>
Expr.store (t := i32) (Arg.imm 0) (Arg.var p81.fst)
  (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_rsn, Arg.var pi.fst, ())) fun p82 =>
  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p82.fst, ())) fun p83 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p83.fst, Arg.imm 4, ())) fun p84 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p84.fst, ()))
    fun p85 =>
  Expr.store (t := i32) (Arg.imm 4294967295) (Arg.var p85.fst)
    (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_flags, Arg.var pi.fst, ())) fun p86 =>
    Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p86.fst, ())) fun p87 =>
    Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p87.fst, Arg.imm 4, ())) fun p88 =>
    Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p88.fst, ()))
      fun p89 =>
    Expr.store (t := i32) (Arg.imm 0) (Arg.var p89.fst)
      (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_qst, Arg.var pi.fst, ())) fun p90 =>
      Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p90.fst, ())) fun p91 =>
      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p91.fst, Arg.imm 4, ())) fun p92 =>
      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p92.fst, ()))
        fun p93 =>
      Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pi.fst, Arg.imm 1, ())) fun p94 =>
      Expr.store (Arg.var p94.fst) (Arg.var p93.fst)
        (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_qprev, Arg.var pi.fst, ()))
          fun p95 =>
        Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p95.fst, ())) fun p96 =>
        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p96.fst, Arg.imm 4, ())) fun p97 =>
        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p97.fst, ()))
          fun p98 =>
        Expr.group (fun _Js_1 : Tup Cont [[i32]] => Blocks.cons (fun pq =>
          Expr.store (Arg.var pq.fst) (Arg.var p98.fst)
            (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_qnext, Arg.var pi.fst, ()))
              fun p99 =>
            Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p99.fst, ())) fun p100 =>
            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p100.fst, Arg.imm 4, ()))
              fun p101 =>
            Expr.let_ (Op.mk (OpCode.add i64)
              (Arg.var c.pScratchBuf, Arg.var p101.fst, ())) fun p102 =>
            Expr.group (fun _Js_2 : Tup Cont [[i32]] => Blocks.cons (fun pqn =>
              Expr.store (Arg.var pqn.fst) (Arg.var p102.fst)
                (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pi.fst, Arg.imm 1, ()))
                  fun p103 => Expr.jump Js.fst (Arg.var p103.fst, ()))) Blocks.nil)
              fun Js_2 =>
            Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pi.fst, Arg.imm 1, ())) fun p103 =>
            Expr.let_ (Op.mk (OpCode.cmp .uge i32 .bool rfl)
              (Arg.var p103.fst, Arg.var nv, ())) fun p104 =>
            Expr.jnz (Arg.var p104.fst)
              (Expr.jump Js_2.fst (Arg.imm 4294967295, ()))
              (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pi.fst, Arg.imm 1, ()))
                fun p105 => Expr.jump Js_2.fst (Arg.var p105.fst, ())))) Blocks.nil)
          fun Js_1 =>
        Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl)
          (Arg.var pi.fst, Arg.imm 0, ())) fun p99 =>
        Expr.jnz (Arg.var p99.fst)
          (Expr.jump Js_1.fst (Arg.imm 4294967295, ()))
          (Expr.let_ (Op.mk (OpCode.sub i32) (Arg.var pi.fst, Arg.imm 1, ())) fun p100 =>
          Expr.jump Js_1.fst (Arg.var p100.fst, ())))))))
(Expr.group (fun Js_1 : Tup Cont [[i32]] => Blocks.cons (fun pi : Tup Val [i32] =>
  Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var nv, Arg.imm 1, ())) fun p78 =>
  Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl) (Arg.var pi.fst, Arg.var p78.fst, ()))
    fun p79 =>
  Expr.jnz (Arg.var p79.fst)
    (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_vals, Arg.var pi.fst, ())) fun p80 =>
    Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p80.fst, ())) fun p81 =>
    Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p81.fst, Arg.imm 4, ())) fun p82 =>
    Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p82.fst, ()))
      fun p83 =>
    Expr.store (t := i32) (Arg.imm 0) (Arg.var p83.fst)
      (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_whead, Arg.var pi.fst, ())) fun p84 =>
      Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p84.fst, ())) fun p85 =>
      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p85.fst, Arg.imm 4, ())) fun p86 =>
      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p86.fst, ()))
        fun p87 =>
      Expr.store (t := i32) (Arg.imm 4294967295) (Arg.var p87.fst)
        (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pi.fst, Arg.imm 1, ())) fun p88 =>
        Expr.jump Js_1.fst (Arg.var p88.fst, ()))))
    (Expr.group (fun Js : Tup Cont [[i32]] => Blocks.cons (fun pw : Tup Val [i32] =>
      Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl) (Arg.var pw.fst, Arg.var nc, ()))
        fun p225 =>
      Expr.jnz (Arg.var p225.fst)
        (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_cl_meta, Arg.var pw.fst, ()))
          fun p226 =>
        Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p226.fst, ())) fun p227 =>
        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p227.fst, Arg.imm 4, ())) fun p228 =>
        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p228.fst, ()))
          fun p229 =>
        Expr.load i32 (Arg.var p229.fst) fun ld230 =>
        Expr.let_ (Op.mk (OpCode.and i32) (Arg.var ld230, Arg.imm 65535, ())) fun p231 =>
        Expr.group (fun _Js_2 : Tup Cont [[]] => Blocks.cons (fun _ : Tup Val [] =>
          Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pw.fst, Arg.imm 1, ())) fun p234 =>
          Expr.jump Js.fst (Arg.var p234.fst, ())) Blocks.nil)
          fun Js_2 =>
        Expr.let_ (Op.mk (OpCode.cmp .uge i32 .bool rfl)
          (Arg.var p231.fst, Arg.imm 2, ()))
          fun p235 =>
        Expr.jnz (Arg.var p235.fst)
          (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_cl_off, Arg.var pw.fst, ()))
            fun p236 =>
          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p236.fst, ())) fun p237 =>
          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p237.fst, Arg.imm 4, ())) fun p238 =>
          Expr.let_ (Op.mk (OpCode.add i64)
            (Arg.var c.pScratchBuf, Arg.var p238.fst, ())) fun p239 =>
          Expr.load i32 (Arg.var p239.fst) fun ld240 =>
          Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_arena, Arg.var ld240, ()))
            fun p241 =>
          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p241.fst, ())) fun p242 =>
          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p242.fst, Arg.imm 4, ())) fun p243 =>
          Expr.let_ (Op.mk (OpCode.add i64)
            (Arg.var c.pScratchBuf, Arg.var p243.fst, ())) fun p244 =>
          Expr.load i32 (Arg.var p244.fst) fun ld245 =>
          Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_arena, Arg.var ld240, ()))
            fun p246 =>
          Expr.let_ (Op.mk (OpCode.add i32) (Arg.var p246.fst, Arg.imm 1, ())) fun p247 =>
          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p247.fst, ())) fun p248 =>
          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p248.fst, Arg.imm 4, ())) fun p249 =>
          Expr.let_ (Op.mk (OpCode.add i64)
            (Arg.var c.pScratchBuf, Arg.var p249.fst, ())) fun p250 =>
          Expr.load i32 (Arg.var p250.fst) fun ld251 =>
          Expr.call (as := [i64, i32, i32, i32, i32]) (bs := []) "full_k6_watch_fid"
            (Arg.var c.hdr, Arg.var pw.fst, Arg.var ld245,
              Arg.var ld251, Arg.var p231.fst, ()) fun _ret252 : Tup Val [] =>
          Expr.jump Js_2.fst ())
          (Expr.jump Js_2.fst ()))
        (Expr.call (as := [i64, i32]) (bs := [i64]) "full_k6_solve_fid"
          (Arg.var c.hdr, Arg.var tick_lim, ())
          fun ret253 : Tup Val [i64] =>
        Expr.let_ (Op.mk (OpCode.cmp .ne i64 .bool rfl)
          (Arg.var ret253.fst, Arg.imm 20, ()))
          fun p254 =>
        Expr.jnz (Arg.var p254.fst)
          (Expr.ret (Arg.imm false, ()))
          (Expr.call (as := [i64]) (bs := []) "full_k6_core_fid"
            (Arg.var c.hdr, ()) fun _ret255 : Tup Val [] =>
          Expr.group (fun Js_2 : Tup Cont [[i32]] =>
            Blocks.cons (fun pz : Tup Val [i32] =>
            Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl)
              (Arg.var pz.fst, Arg.imm 128, ())) fun p258 =>
            Expr.jnz (Arg.var p258.fst)
              (Expr.let_ (Op.mk (OpCode.add i32) (Arg.imm 4002, Arg.var pz.fst, ()))
                fun p259 =>
              Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p259.fst, ())) fun p260 =>
              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p260.fst, Arg.imm 4, ()))
                fun p261 =>
              Expr.let_ (Op.mk (OpCode.add i64)
                (Arg.var c.pScratchBuf, Arg.var p261.fst, ())) fun p262 =>
              Expr.store (t := i32) (Arg.imm 0) (Arg.var p262.fst)
                (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pz.fst, Arg.imm 1, ()))
                  fun p263 => Expr.jump Js_2.fst (Arg.var p263.fst, ())))
              (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4194, ())) fun p264 =>
              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p264.fst, Arg.imm 4, ()))
                fun p265 =>
              Expr.let_ (Op.mk (OpCode.add i64)
                (Arg.var c.pScratchBuf, Arg.var p265.fst, ())) fun p266 =>
              Expr.load i32 (Arg.var p266.fst) fun ld267 =>
              Expr.group (fun Js_3 : Tup Cont [[i32, Ty.bool]] =>
                Blocks.cons (fun ps : Tup Val [i32, Ty.bool] =>
                Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl)
                  (Arg.var ps.fst, Arg.var ld267, ())) fun p270 =>
                Expr.jnz (Arg.var p270.fst)
                  (Expr.group (fun _Js_4 : Tup Cont [[Ty.bool]] =>
                    Blocks.cons (fun pc : Tup Val [Ty.bool] =>
                    Expr.let_ (Op.mk (OpCode.add i32) (Arg.var ps.fst, Arg.imm 1, ()))
                      fun p273 =>
                    Expr.jump Js_3.fst (Arg.var p273.fst, Arg.var pc.fst, ())) Blocks.nil)
                    fun Js_4 =>
                  Expr.let_ (Op.mk (OpCode.add i32)
                    (Arg.var o_cl_meta, Arg.var ps.fst, ()))
                    fun p274 =>
                  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p274.fst, ())) fun p275 =>
                  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p275.fst, Arg.imm 4, ()))
                    fun p276 =>
                  Expr.let_ (Op.mk (OpCode.add i64)
                    (Arg.var c.pScratchBuf, Arg.var p276.fst, ())) fun p277 =>
                  Expr.load i32 (Arg.var p277.fst) fun ld278 =>
                  Expr.let_ (Op.mk (OpCode.and i32)
                    (Arg.var ld278, Arg.imm 2147483648, ())) fun p279 =>
                  Expr.let_ (Op.mk (OpCode.cmp .ne i32 .bool rfl)
                    (Arg.var p279.fst, Arg.imm 0, ())) fun p280 =>
                  Expr.jnz (Arg.var p280.fst)
                    (Expr.let_ (Op.mk (OpCode.add i32)
                      (Arg.var o_cl_aux, Arg.var ps.fst, ())) fun p281 =>
                    Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p281.fst, ()))
                      fun p282 =>
                    Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p282.fst, Arg.imm 4, ()))
                      fun p283 =>
                    Expr.let_ (Op.mk (OpCode.add i64)
                      (Arg.var c.pScratchBuf, Arg.var p283.fst, ())) fun p284 =>
                    Expr.load i32 (Arg.var p284.fst) fun ld285 =>
                    Expr.let_ (Op.mk (OpCode.and i32) (Arg.var ld285, Arg.imm 2047, ()))
                      fun p286 =>
                    Expr.group (fun _Js_5 : Tup Cont [[i32]] =>
                      Blocks.cons (fun pm2 : Tup Val [i32] =>
                      Expr.let_ (Op.mk (OpCode.lshr i32)
                        (Arg.var p286.fst, Arg.imm 5, ())) fun p289 =>
                      Expr.let_ (Op.mk (OpCode.add i32)
                        (Arg.var pm2.fst, Arg.var p289.fst, ()))
                        fun p290 =>
                      Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p290.fst, ()))
                        fun p291 =>
                      Expr.let_ (Op.mk (OpCode.mul i64)
                        (Arg.var p291.fst, Arg.imm 4, ())) fun p292 =>
                      Expr.let_ (Op.mk (OpCode.add i64)
                        (Arg.var c.pScratchBuf, Arg.var p292.fst, ())) fun p293 =>
                      Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p290.fst, ()))
                        fun p294 =>
                      Expr.let_ (Op.mk (OpCode.mul i64)
                        (Arg.var p294.fst, Arg.imm 4, ())) fun p295 =>
                      Expr.let_ (Op.mk (OpCode.add i64)
                        (Arg.var c.pScratchBuf, Arg.var p295.fst, ())) fun p296 =>
                      Expr.load i32 (Arg.var p296.fst) fun ld297 =>
                      Expr.let_ (Op.mk (OpCode.and i32)
                        (Arg.var p286.fst, Arg.imm 31, ())) fun p298 =>
                      Expr.let_ (Op.mk (OpCode.shl i32) (Arg.imm 1, Arg.var p298.fst, ()))
                        fun p299 =>
                      Expr.let_ (Op.mk (OpCode.or i32)
                        (Arg.var ld297, Arg.var p299.fst, ()))
                        fun p300 =>
                      Expr.store (Arg.var p300.fst) (Arg.var p293.fst)
                        (Expr.jump Js_4.fst (Arg.imm true, ()))) Blocks.nil)
                      fun Js_5 =>
                    Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var ld285, Arg.imm 11, ()))
                      fun p301 =>
                    Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl)
                      (Arg.var p301.fst, Arg.imm 0, ())) fun p302 =>
                    Expr.jnz (Arg.var p302.fst)
                      (Expr.jump Js_5.fst (Arg.imm 4002, ()))
                      (Expr.jump Js_5.fst (Arg.imm 4066, ())))
                    (Expr.jump Js_4.fst (Arg.var ps.snd.fst, ())))
                  (Expr.group (fun _Js_4 : Tup Cont [[]] =>
                    Blocks.cons (fun _ : Tup Val [] =>
                    Expr.ret (Arg.var ps.snd.fst, ())) Blocks.nil)
                    fun Js_4 =>
                  Expr.jnz (Arg.var ps.snd.fst)
                    (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4130, ())) fun p305 =>
                    Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p305.fst, Arg.imm 4, ()))
                      fun p306 =>
                    Expr.let_ (Op.mk (OpCode.add i64)
                      (Arg.var c.pScratchBuf, Arg.var p306.fst, ())) fun p307 =>
                    Expr.store (t := i32) (Arg.imm 1) (Arg.var p307.fst)
                      (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4131, ()))
                        fun p308 =>
                      Expr.let_ (Op.mk (OpCode.mul i64)
                        (Arg.var p308.fst, Arg.imm 4, ())) fun p309 =>
                      Expr.let_ (Op.mk (OpCode.add i64)
                        (Arg.var c.pScratchBuf, Arg.var p309.fst, ())) fun p310 =>
                      Expr.store (t := i32) (Arg.imm 1) (Arg.var p310.fst)
                        (Expr.jump Js_4.fst ())))
                    (Expr.jump Js_4.fst ()))) Blocks.nil)
                fun Js_3 : Tup Cont [[i32, Ty.bool]] =>
                  Expr.jump Js_3.fst (Arg.imm 0, Arg.imm false, ()))) Blocks.nil)
            fun Js_2 : Tup Cont [[i32]] =>
              Expr.jump Js_2.fst (Arg.imm 0, ())))) Blocks.nil)
      fun Js : Tup Cont [[i32]] => Expr.jump Js.fst (Arg.imm 0, ()))) Blocks.nil)
    fun Js_1 : Tup Cont [[i32]] => Expr.jump Js_1.fst (Arg.imm 0, ()))) Blocks.nil)
  fun Js : Tup Cont [[i32]] =>
    Expr.jump Js.fst (Arg.imm 0, ()))))))))))))))))))))))))))

private theorem fid_k6c_post_solve_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost}
    {c : FullCfg} {F0 : Std.Sat.CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {tmp wsort tmk scr : List (BitVec 32)}
    {nv nc alen acap n_units trivial_eid tick_lim mv_s mc_s max_orig_s : BitVec 32}
    {o_rsn o_qprev o_qnext o_qst o_flags o_vals o_whead : BitVec 32}
    {o_cl_off o_cl_meta o_cl_aux o_arena : BitVec 32}
    (hwatch : ∀ a m Q X, fidK6WatchSpec a m Q X →
      Γ "full_k6_watch_fid" [i64, i32, i32, i32, i32] [] a m Q X)
    (hsolve : ∀ a m Q X, fidK6SolveSpec a m Q X →
      Γ "full_k6_solve_fid" [i64, i32] [i64] a m Q X)
    (hcore : ∀ a m Q X, fidK6CoreSpec a m Q X →
      Γ "full_k6_core_fid" [i64] [] a m Q X)
    (hinv : FullDenseInvW c F0 F_cur s) (htz : TmkZero (FidP6Work s tmp wsort tmk scr))
    (hcap : 16384 ≤ c.scratch_cap) (hmv_lo : 256 ≤ mv_s.toNat) (hmv_hi : mv_s.toNat ≤ 8192)
    (hmc_s : mc_s = mv_s <<< 2) (hmax_orig_s : max_orig_s = mv_s <<< 1)
    (hoff_rsn : o_rsn = 4224#32 + mv_s) (hoff_qprev : o_qprev = 4224#32 + 2#32 * mv_s)
    (hoff_qnext : o_qnext = 4224#32 + 3#32 * mv_s) (hoff_qst : o_qst = 4224#32 + 4#32 * mv_s)
    (hoff_flags : o_flags = 4224#32 + 6#32 * mv_s) (hoff_vals : o_vals = 4224#32 + 9#32 * mv_s)
    (hoff_whead : o_whead = 4224#32 + 11#32 * mv_s)
    (hoff_off : o_cl_off = 4224#32 + 29#32 * mv_s)
    (hoff_meta : o_cl_meta = 4224#32 + 33#32 * mv_s)
    (hoff_aux : o_cl_aux = 4224#32 + 37#32 * mv_s)
    (hoff_arena : o_arena = 4224#32 + 45#32 * mv_s)
    (hcap_ar : 4224 + 45 * mv_s.toNat + acap.toNat ≤ c.scratch_cap)
    (htmp : tmp.length = c.max_vars) (hwsort : wsort.length = 2 * c.max_vars)
    (htmk : tmk.length = 2 * c.max_vars) (hscr : scr.length = c.scratch_cap)
    (hnv_pos : 1 ≤ nv.toNat) (hnv_le : nv.toNat ≤ mv_s.toNat)
    (hnc_ge : 2 ≤ nc.toNat) (halen_le : alen.toNat ≤ acap.toNat)
    (hcls : FidK6cClsOk mv_s.toNat nc.toNat alen.toNat n_units.toNat scr)
    (hp0 : ∀ i, i < 4002 → scr[i]? = s.scratch.scratch_buf[i]?)
    (hp1 : ∀ i, 4132 ≤ i → i < 4192 → scr[i]? = s.scratch.scratch_buf[i]?)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m)
    (hQ : ∀ ok s' m', FullDenseInvW c F0 F_cur s' → TmkZero s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.arena = s.core.arena →
      s'.core.arena_len = s.core.arena_len → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (∀ i, i < 4002 → s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) →
      (∀ i, 4132 ≤ i → i < 4192 → s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X (fidPostHdrInitWatchExpr c nv nc alen acap n_units trivial_eid tick_lim
      mv_s mc_s max_orig_s o_rsn o_qprev o_qnext o_qst o_flags o_vals o_whead
      o_cl_off o_cl_meta o_cl_aux o_arena) m := by
  have hscr_lt : scr.length < 2 ^ 30 := by
    have := c.hscr; simp only [Examples.LratBytes.dimacsBound] at this; omega
  let sw := FidP6Work s tmp wsort tmk scr
  have hinv_sw : FullDenseInvW c F0 F_cur sw :=
    fid_k6c_fullDenseInvW_work hinv htmp hwsort htmk hscr
  have htz_sw : TmkZero sw := htz
  have hm_sw : (FullMem c (FidP6Scr sw scr) ⋆ R) m := by simpa [FidP6Scr, sw] using hm
  dsimp only [fidPostHdrInitWatchExpr]
  refine fid_k6c_init_solve_wp (s := sw) (scr0 := s.scratch.scratch_buf)
    hinv_sw htz_sw hcap hscr_lt hscr hmv_lo hmv_hi hmc_s hmax_orig_s
    hoff_rsn hoff_qprev hoff_qnext hoff_qst hoff_flags hoff_vals hoff_whead
    hcap_ar hnv_pos hnv_le hnc_ge halen_le hcls hp0 hp1 hm_sw ?_
  intro scr2 m2 h2_len hbuf2 h2_93 h2_94 h2_14 haux2 hp0_2 hp1_2 hm2
  exact fid_k6c_watch_solve_wp hwatch hsolve hcore (s := sw)
    (scr0 := s.scratch.scratch_buf) hinv_sw htz_sw hcap h2_len hmv_lo hmv_hi
    hoff_off hoff_meta hoff_aux hoff_arena hbuf2 h2_93 h2_94 h2_14 haux2
    hp0_2 hp1_2 hm2 (fun ok s' m' hi' ht' hcv ha' hal' hf' hp0' hp1' hm' =>
      hQ ok s' m' hi' ht' hcv ha' hal' hf' hp0' hp1' hm')



private theorem fid_k6c_post_extract_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost}
    {c : FullCfg} {F0 : Std.Sat.CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {tmp wsort tmk scr : List (BitVec 32)}
    {nv nc alen acap n_units trivial_eid tick_lim mv_s mc_s max_orig_s : BitVec 32}
    {o_rsn o_qprev o_qnext o_qst o_flags o_vals o_whead : BitVec 32}
    {o_cl_off o_cl_meta o_cl_aux o_arena : BitVec 32} {abort : Bool}
    (hwatch : ∀ a m Q X, fidK6WatchSpec a m Q X →
      Γ "full_k6_watch_fid" [i64, i32, i32, i32, i32] [] a m Q X)
    (hsolve : ∀ a m Q X, fidK6SolveSpec a m Q X →
      Γ "full_k6_solve_fid" [i64, i32] [i64] a m Q X)
    (hcore : ∀ a m Q X, fidK6CoreSpec a m Q X →
      Γ "full_k6_core_fid" [i64] [] a m Q X)
    (hinv : FullDenseInvW c F0 F_cur s) (hcap : 16384 ≤ c.scratch_cap)
    (hmv_lo : 256 ≤ mv_s.toNat) (hmv_hi : mv_s.toNat ≤ 8192)
    (hmc_s : mc_s = mv_s <<< 2) (hmax_orig_s : max_orig_s = mv_s <<< 1)
    (hoff_rsn : o_rsn = 4224#32 + mv_s) (hoff_qprev : o_qprev = 4224#32 + 2#32 * mv_s)
    (hoff_qnext : o_qnext = 4224#32 + 3#32 * mv_s) (hoff_qst : o_qst = 4224#32 + 4#32 * mv_s)
    (hoff_flags : o_flags = 4224#32 + 6#32 * mv_s) (hoff_vals : o_vals = 4224#32 + 9#32 * mv_s)
    (hoff_whead : o_whead = 4224#32 + 11#32 * mv_s)
    (hoff_off : o_cl_off = 4224#32 + 29#32 * mv_s)
    (hoff_meta : o_cl_meta = 4224#32 + 33#32 * mv_s)
    (hoff_aux : o_cl_aux = 4224#32 + 37#32 * mv_s)
    (hoff_arena : o_arena = 4224#32 + 45#32 * mv_s)
    (hcap_ar : 4224 + 45 * mv_s.toNat + acap.toNat ≤ c.scratch_cap)
    (htmp : tmp.length = c.max_vars) (hwsort : wsort.length = 2 * c.max_vars)
    (htmk : tmk.length = 2 * c.max_vars) (hscr : scr.length = c.scratch_cap)
    (hnv_le : nv.toNat ≤ mv_s.toNat) (_hnc_le : nc.toNat ≤ 2 * mv_s.toNat)
    (halen_le : alen.toNat ≤ acap.toNat) (_hnu_le : n_units.toNat ≤ nc.toNat)
    (htriv : trivial_eid ≠ 4294967295#32 →
      trivial_eid.toNat < 4096 ∧ (trivial_eid &&& 2047#32).toNat < 2001)
    (hreg : FidK6cTmkReg nv.toNat s.core.cur_vars wsort tmk)
    (hcls : FidK6cClsOk mv_s.toNat nc.toNat alen.toNat n_units.toNat scr)
    (hp0 : ∀ i, i < 4002 → scr[i]? = s.scratch.scratch_buf[i]?)
    (hp1 : ∀ i, 4132 ≤ i → i < 4192 → scr[i]? = s.scratch.scratch_buf[i]?)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m)
    (hQ : ∀ ok s' m', FullDenseInvW c F0 F_cur s' → TmkZero s' →
      s'.core.cur_vars = s.core.cur_vars → s'.core.arena = s.core.arena →
      s'.core.arena_len = s.core.arena_len → s'.core.fuel.toNat ≤ s.core.fuel.toNat →
      (∀ i, i < 4002 → s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) →
      (∀ i, 4132 ≤ i → i < 4192 → s'.scratch.scratch_buf[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c s' ⋆ R) m' → Q (ok, ()) m') :
    wp Γ Q X
      (Expr.group (fun Js : Tup Cont [[i32]] => Blocks.cons (fun pk : Tup Val [i32] =>
        Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl) (Arg.var pk.fst, Arg.var nv, ()))
          fun p57 =>
        Expr.jnz (Arg.var p57.fst)
          (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var pk.fst, ())) fun p58 =>
          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p58.fst, Arg.imm 4, ())) fun p59 =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pWsort, Arg.var p59.fst, ())) fun p60 =>
          Expr.load i32 (Arg.var p60.fst) fun ld61 =>
          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ld61, ())) fun p62 =>
          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p62.fst, Arg.imm 4, ())) fun p63 =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pTarjanMark, Arg.var p63.fst, ()))
            fun p64 =>
          Expr.store (t := i32) (Arg.imm 0) (Arg.var p64.fst)
            (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pk.fst, Arg.imm 1, ())) fun p65 =>
            Expr.jump Js.fst (Arg.var p65.fst, ())))
          (Expr.let_ (Op.mk (OpCode.cmp .ne i32 .bool rfl)
            (Arg.var trivial_eid, Arg.imm 4294967295, ())) fun p66 =>
          Expr.jnz (Arg.var p66.fst)
            (Expr.let_ (Op.mk (OpCode.and i32) (Arg.var trivial_eid, Arg.imm 2047, ())) fun p67 =>
            Expr.group (fun _Js_1 : Tup Cont [[i32]] => Blocks.cons (fun pmb : Tup Val [i32] =>
              Expr.group (fun Js_2 : Tup Cont [[i32]] => Blocks.cons (fun pu : Tup Val [i32] =>
                Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl) (Arg.var pu.fst, Arg.imm 128, ()))
                  fun p72 =>
                Expr.jnz (Arg.var p72.fst)
                  (Expr.let_ (Op.mk (OpCode.add i32) (Arg.imm 4002, Arg.var pu.fst, ())) fun p73 =>
                  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p73.fst, ())) fun p74 =>
                  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p74.fst, Arg.imm 4, ())) fun p75 =>
                  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p75.fst, ()))
                    fun p76 =>
                  Expr.store (t := i32) (Arg.imm 0) (Arg.var p76.fst)
                    (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pu.fst, Arg.imm 1, ())) fun p77 =>
                    Expr.jump Js_2.fst (Arg.var p77.fst, ())))
                  (Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var p67.fst, Arg.imm 5, ())) fun p78 =>
                  Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pmb.fst, Arg.var p78.fst, ()))
                    fun p79 =>
                  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p79.fst, ())) fun p80 =>
                  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p80.fst, Arg.imm 4, ())) fun p81 =>
                  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p81.fst, ()))
                    fun p82 =>
                  Expr.let_ (Op.mk (OpCode.and i32) (Arg.var p67.fst, Arg.imm 31, ())) fun p83 =>
                  Expr.let_ (Op.mk (OpCode.shl i32) (Arg.imm 1, Arg.var p83.fst, ())) fun p84 =>
                  Expr.store (Arg.var p84.fst) (Arg.var p82.fst)
                    (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4130, ())) fun p85 =>
                    Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p85.fst, Arg.imm 4, ())) fun p86 =>
                    Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p86.fst, ()))
                      fun p87 =>
                    Expr.store (t := i32) (Arg.imm 1) (Arg.var p87.fst)
                      (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.imm 4131, ())) fun p88 =>
                      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p88.fst, Arg.imm 4, ())) fun p89 =>
                      Expr.let_ (Op.mk (OpCode.add i64)
                        (Arg.var c.pScratchBuf, Arg.var p89.fst, ())) fun p90 =>
                      Expr.store (t := i32) (Arg.imm 1) (Arg.var p90.fst)
                        (Expr.ret (Arg.imm true, ())))))) Blocks.nil)
                fun Js_2 => Expr.jump Js_2.fst (Arg.imm 0, ())) Blocks.nil)
              fun Js_1 =>
            Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var trivial_eid, Arg.imm 11, ())) fun p91 =>
            Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl) (Arg.var p91.fst, Arg.imm 0, ()))
              fun p92 =>
            Expr.jnz (Arg.var p92.fst)
              (Expr.jump Js_1.fst (Arg.imm 4002, ()))
              (Expr.jump Js_1.fst (Arg.imm 4066, ())))
            (Expr.jnz (Arg.var abort)
              (Expr.ret (Arg.imm false, ()))
              (Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl) (Arg.var nv, Arg.imm 0, ()))
                fun p93 =>
              Expr.jnz (Arg.var p93.fst)
                (Expr.ret (Arg.imm false, ()))
                (Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl) (Arg.var nc, Arg.imm 2, ()))
                  fun p94 =>
                Expr.jnz (Arg.var p94.fst)
                  (Expr.ret (Arg.imm false, ()))
                  (fidPostHdrInitWatchExpr c nv nc alen acap n_units trivial_eid tick_lim
                    mv_s mc_s max_orig_s o_rsn o_qprev o_qnext o_qst o_flags o_vals
                    o_whead o_cl_off o_cl_meta o_cl_aux o_arena))))))
      Blocks.nil) fun Js => Expr.jump Js.fst (Arg.imm 0, ())) m := by
  refine fid_k6c_tmk_clear_wp hinv htmp hwsort htmk hreg hm ?_
  intro tmk1 m1 htmk1_len htmk1_z hm1
  have hinv1 : FullDenseInvW c F0 F_cur (FidP6Work s tmp wsort tmk1 scr) :=
    fid_k6c_fullDenseInvW_work hinv htmp hwsort htmk1_len hscr
  have htz1 : TmkZero (FidP6Work s tmp wsort tmk1 scr) := fun v hv => by
    simpa [FidP6Work] using htmk1_z v hv
  c0_hsteps_nogrp
  · -- `trivial_eid ≠ 4294967295`
    have htr : trivial_eid.toNat < 4096 ∧ (trivial_eid &&& 2047#32).toNat < 2001 := by
      apply htriv; exact hc
    c0_hsteps_nogrp
    apply wp_unroll_group
    intro Js_1 hJs_1
    have hJ68 : ∀ mbase : BitVec 32, mbase = 4002#32 ∨ mbase = 4066#32 →
        ∀ m2, (FullMem c (FidP6Work s tmp wsort tmk1 scr) ⋆ R) m2 → Js_1 (mbase, ()) m2 := by
      intro mbase hmb m2 hm2
      apply hJs_1; dsimp only [Blocks.get, Member.here]
      refine fid_k6c_zero_mask_wp hcap hscr hm2 ?_
      intro scr2 m3 hlen2 hp0_2 hp1_2 hm3
      have hw := fid_k6c_mask_widx (eid := trivial_eid &&& 2047#32) hmb htr.2
      have hlt_widx : (BitVec.setWidth 64 (mbase + ((trivial_eid &&& 2047#32) >>> 5))).toNat <
          scr2.length := by rw [hw.2.2]; simp only [BitVec.toNat_ofNat]; omega
      c0_hsteps
      have h5 : (trivial_eid &&& 2047#32) >>> (5 : BitVec 32) =
          (trivial_eid &&& 2047#32) >>> 5 := rfl
      have hwid_range :
          4002 ≤ (BitVec.setWidth 64
            (mbase + (trivial_eid &&& 2047#32) >>> (5 : BitVec 32))).toNat ∧
          (BitVec.setWidth 64
            (mbase + (trivial_eid &&& 2047#32) >>> (5 : BitVec 32))).toNat < 4130 := by
        rw [h5, fid_k6c_zext64]
        omega
      refine hQ true _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hm
      · exact fid_k6c_fullDenseInvW_work hinv htmp hwsort htmk1_len
          (by simp only [List.length_set]; exact hlen2)
      · exact fun v hv => by simpa [FidP6Work] using htmk1_z v hv
      · rfl
      · rfl
      · rfl
      · exact Nat.le_refl _
      · intro i hi
        dsimp only [FidP6Work]
        repeat rw [List.getElem?_set_ne (by
          try change (BitVec.setWidth 64
            (mbase + (trivial_eid &&& 2047#32) >>> (5 : BitVec 32))).toNat ≠ i
          omega)]
        exact (hp0_2 i hi).trans (hp0 i hi)
      · intro i h1 h2
        dsimp only [FidP6Work]
        repeat rw [List.getElem?_set_ne (by
          try change (BitVec.setWidth 64
            (mbase + (trivial_eid &&& 2047#32) >>> (5 : BitVec 32))).toNat ≠ i
          omega)]
        exact (hp1_2 i h1 h2).trans (hp1 i h1 h2)
    clear hJs_1
    c0_hsteps
    · exact hJ68 4002#32 (Or.inl rfl) m1 hm1
    · exact hJ68 4066#32 (Or.inr rfl) m1 hm1
  · exact hQ false _ m1 hinv1 htz1 rfl rfl rfl (Nat.le_refl _) hp0 hp1 hm1
  · exact hQ false _ m1 hinv1 htz1 rfl rfl rfl (Nat.le_refl _) hp0 hp1 hm1
  · exact hQ false _ m1 hinv1 htz1 rfl rfl rfl (Nat.le_refl _) hp0 hp1 hm1
  · -- Enter `init_solve` -> `watch_solve`
    have hnv_pos : 1 ≤ nv.toNat := by bv_omega
    have hnc_ge : 2 ≤ nc.toNat := by bv_omega
    exact fid_k6c_post_solve_wp hwatch hsolve hcore hinv htz1 hcap hmv_lo hmv_hi
      hmc_s hmax_orig_s hoff_rsn hoff_qprev hoff_qnext hoff_qst hoff_flags hoff_vals hoff_whead
      hoff_off hoff_meta hoff_aux hoff_arena hcap_ar htmp hwsort htmk1_len hscr
      hnv_pos hnv_le hnc_ge halen_le hcls hp0 hp1 hm1 hQ

private abbrev fidBinEntryExpr {ret : List Ty} (c : FullCfg)
    (Js_exit : Cont [i32, i32, i32, i32, i32, Ty.bool, i32])
    (Js_cont : Cont [i32, i32, i32, i32, i32, Ty.bool])
    (w nv nc alen n_units ei1 trivial_eid eid_val mv_s max_orig_s acap
      o_arena o_cl_off o_cl_meta o_cl_aux o_units : Val i32) (abort_s : Val .bool) :
    Expr Val Cont ret :=
  Expr.let_ (Op.mk (OpCode.and i32) (Arg.var w, Arg.imm 2147483647, ())) fun p345 =>
  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p345.fst, ())) fun p346 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pVals, Arg.var p346.fst, ())) fun p347 =>
  Expr.load i8 (Arg.var p347.fst) fun ld348 =>
  Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm 0, ())) fun p349 =>
  Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var ld348, ())) fun p350 =>
  Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var p349.fst, ())) fun p351 =>
  Expr.let_ (Op.mk (OpCode.cmp .slt i32 .bool rfl) (Arg.var p350.fst, Arg.var p351.fst, ()))
    fun p352 =>
  Expr.jnz (Arg.var p352.fst)
    (Expr.jump Js_exit (Arg.var nv, Arg.var nc, Arg.var alen, Arg.var n_units,
      Arg.var eid_val, Arg.var abort_s, Arg.var ei1, ()))
    (Expr.group (fun _Js_353 : Tup Cont [[i32, i32, i32, i32, Ty.bool]] =>
      Blocks.cons (fun pb354 : Tup Val [i32, i32, i32, i32, Ty.bool] =>
        Expr.jump Js_cont (Arg.var pb354.fst, Arg.var pb354.snd.fst, Arg.var pb354.snd.snd.fst,
          Arg.var pb354.snd.snd.snd.fst, Arg.var trivial_eid,
          Arg.var pb354.snd.snd.snd.snd.fst, ())) Blocks.nil)
      fun Js_353 =>
      Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm 0, ())) fun p355 =>
      Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var ld348, ())) fun p356 =>
      Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var p355.fst, ())) fun p357 =>
      Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl) (Arg.var p356.fst, Arg.var p357.fst, ()))
        fun p358 =>
      Expr.jnz (Arg.var p358.fst)
        (Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var p345.fst, Arg.imm 1, ())) fun p359 =>
        Expr.group (fun _Js_360 : Tup Cont [[i32, Ty.bool]] =>
          Blocks.cons (fun pb361 : Tup Val [i32, Ty.bool] =>
          Expr.let_ (Op.mk (OpCode.cmp .uge i32 .bool rfl) (Arg.var nc, Arg.var max_orig_s, ()))
            fun p362 =>
          Expr.jnz (Arg.var p362.fst)
            (Expr.jump Js_exit (Arg.var pb361.fst, Arg.var nc, Arg.var alen, Arg.var n_units,
              Arg.var trivial_eid, Arg.imm true, Arg.var ei1, ()))
            (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var alen, Arg.imm 1, ())) fun p363 =>
            Expr.let_ (Op.mk (OpCode.cmp .ugt i32 .bool rfl) (Arg.var p363.fst, Arg.var acap, ()))
              fun p364 =>
            Expr.jnz (Arg.var p364.fst)
              (Expr.jump Js_exit (Arg.var pb361.fst, Arg.var nc, Arg.var alen, Arg.var n_units,
                Arg.var trivial_eid, Arg.imm true, Arg.var ei1, ()))
              (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_arena, Arg.var alen, ())) fun p365 =>
              Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p365.fst, ())) fun p366 =>
              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p366.fst, Arg.imm 4, ())) fun p367 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p367.fst, ()))
                fun p368 =>
              Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p359.fst, ())) fun p369 =>
              Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p369.fst, Arg.imm 4, ())) fun p370 =>
              Expr.let_ (Op.mk (OpCode.add i64)
                (Arg.var c.pTarjanMark, Arg.var p370.fst, ())) fun p371 =>
              Expr.load i32 (Arg.var p371.fst) fun ld372 =>
              Expr.let_ (Op.mk (OpCode.sub i32) (Arg.var ld372, Arg.imm 1, ())) fun p373 =>
              Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var p373.fst, Arg.imm 1, ())) fun p374 =>
              Expr.let_ (Op.mk (OpCode.and i32) (Arg.var p345.fst, Arg.imm 1, ())) fun p375 =>
              Expr.let_ (Op.mk (OpCode.or i32) (Arg.var p374.fst, Arg.var p375.fst, ())) fun p376 =>
              Expr.store (Arg.var p376.fst) (Arg.var p368.fst)
                (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_cl_off, Arg.var nc, ())) fun p377 =>
                Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p377.fst, ())) fun p378 =>
                Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p378.fst, Arg.imm 4, ())) fun p379 =>
                Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p379.fst, ()))
                  fun p380 =>
                Expr.store (Arg.var alen) (Arg.var p380.fst)
                  (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_cl_meta, Arg.var nc, ()))
                    fun p381 =>
                  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p381.fst, ())) fun p382 =>
                  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p382.fst, Arg.imm 4, ())) fun p383 =>
                  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p383.fst, ()))
                    fun p384 =>
                  Expr.store (t := i32) (Arg.imm 1) (Arg.var p384.fst)
                    (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_cl_aux, Arg.var nc, ()))
                      fun p385 =>
                    Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p385.fst, ())) fun p386 =>
                    Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p386.fst, Arg.imm 4, ())) fun p387 =>
                    Expr.let_ (Op.mk (OpCode.add i64)
                      (Arg.var c.pScratchBuf, Arg.var p387.fst, ())) fun p388 =>
                    Expr.store (Arg.var eid_val) (Arg.var p388.fst)
                      (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_units, Arg.var n_units, ()))
                        fun p389 =>
                      Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p389.fst, ())) fun p390 =>
                      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p390.fst, Arg.imm 4, ()))
                        fun p391 =>
                      Expr.let_ (Op.mk (OpCode.add i64)
                        (Arg.var c.pScratchBuf, Arg.var p391.fst, ())) fun p392 =>
                      Expr.store (Arg.var nc) (Arg.var p392.fst)
                        (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var n_units, Arg.imm 1, ()))
                          fun p393 =>
                        Expr.let_ (Op.mk (OpCode.add i32) (Arg.var nc, Arg.imm 1, ())) fun p394 =>
                        Expr.let_ (Op.mk (OpCode.add i32) (Arg.var alen, Arg.imm 1, ())) fun p395 =>
                        Expr.jump Js_353.fst (Arg.var pb361.fst, Arg.var p394.fst,
                          Arg.var p395.fst, Arg.var p393.fst, Arg.var pb361.snd.fst,
                          ()))))))))) Blocks.nil)
          fun Js_360 =>
          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p359.fst, ())) fun p396 =>
          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p396.fst, Arg.imm 4, ())) fun p397 =>
          Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pTarjanMark, Arg.var p397.fst, ()))
            fun p398 =>
          Expr.load i32 (Arg.var p398.fst) fun ld399 =>
          Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl) (Arg.var ld399, Arg.imm 0, ()))
            fun p400 =>
          Expr.jnz (Arg.var p400.fst)
            (Expr.let_ (Op.mk (OpCode.cmp .uge i32 .bool rfl) (Arg.var nv, Arg.var mv_s, ()))
              fun p401 =>
            Expr.jnz (Arg.var p401.fst)
              (Expr.jump Js_exit (Arg.var nv, Arg.var nc, Arg.var alen, Arg.var n_units,
                Arg.var trivial_eid, Arg.imm true, Arg.var ei1, ()))
              (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var nv, ())) fun p402 =>
              Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.hdr, Arg.imm 776, ())) fun p403 =>
              Expr.load i64 (Arg.var p403.fst) fun ld404 =>
              Expr.let_ (Op.mk (OpCode.sext 32 64) (Arg.imm 1, ())) fun p405 =>
              Expr.let_ (Op.mk (OpCode.shl i64) (Arg.var ld404, Arg.var p405.fst, ())) fun p406 =>
              Expr.let_ (Op.mk (OpCode.cmp .uge i64 .bool rfl)
                (Arg.var p402.fst, Arg.var p406.fst, ()))
                fun p407 =>
              Expr.jnz (Arg.var p407.fst)
                (Expr.jump Js_exit (Arg.var nv, Arg.var nc, Arg.var alen, Arg.var n_units,
                  Arg.var trivial_eid, Arg.imm true, Arg.var ei1, ()))
                (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var nv, ())) fun p408 =>
                Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p408.fst, Arg.imm 4, ())) fun p409 =>
                Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pWsort, Arg.var p409.fst, ()))
                  fun p410 =>
                Expr.store (Arg.var p359.fst) (Arg.var p410.fst)
                  (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var nv, Arg.imm 1, ())) fun p411 =>
                  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p359.fst, ())) fun p412 =>
                  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p412.fst, Arg.imm 4, ())) fun p413 =>
                  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pTarjanMark, Arg.var p413.fst, ()))
                    fun p414 =>
                  Expr.store (Arg.var p411.fst) (Arg.var p414.fst)
                    (Expr.jump Js_360.fst (Arg.var p411.fst, Arg.var abort_s, ()))))))
            (Expr.jump Js_360.fst (Arg.var nv, Arg.var abort_s, ())))
        (Expr.jump Js_353.fst
          (Arg.var nv, Arg.var nc, Arg.var alen, Arg.var n_units, Arg.var abort_s, ())))

private abbrev fidLargeEntryExpr {ret : List Ty} (c : FullCfg)
    (Js_exit : Cont [i32, i32, i32, i32, i32, Ty.bool, i32])
    (Js_cont : Cont [i32, i32, i32, i32, i32, Ty.bool])
    (w nv nc alen n_units ei1 trivial_eid eid_val lit_cur mv_s max_orig_s max_csz acap
      o_arena o_cl_off o_cl_meta o_cl_aux o_units : Val i32) (abort_s : Val .bool) :
    Expr Val Cont ret :=
  Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var w, ())) fun p415 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p415.fst, Arg.imm 2, ())) fun p416 =>
  Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p416.fst, Arg.imm 4, ())) fun p417 =>
  Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pArena, Arg.var p417.fst, ())) fun p418 =>
  Expr.load i32 (Arg.var p418.fst) fun ld419 =>
  Expr.group (fun _Js_420 : Tup Cont [[i32, Ty.bool, Ty.bool, i32, i32]] =>
    Blocks.cons (fun pb421 : Tup Val [i32, Ty.bool, Ty.bool, i32, i32] =>
      Expr.jnz (Arg.var pb421.snd.fst)
        (Expr.jump Js_exit (Arg.var pb421.fst, Arg.var nc, Arg.var alen, Arg.var n_units,
          Arg.var trivial_eid, Arg.var pb421.snd.fst, Arg.var ei1, ()))
        (Expr.group (fun _Js_422 : Tup Cont [[i32, i32, i32, i32, Ty.bool, i32]] =>
          Blocks.cons (fun pb423 : Tup Val [i32, i32, i32, i32, Ty.bool, i32] =>
            Expr.jump Js_cont (Arg.var pb421.fst, Arg.var pb423.fst, Arg.var pb423.snd.fst,
              Arg.var pb423.snd.snd.fst, Arg.var pb423.snd.snd.snd.fst,
              Arg.var pb423.snd.snd.snd.snd.fst, ())) Blocks.nil)
          fun Js_422 =>
          Expr.jnz (Arg.var pb421.snd.snd.fst)
            (Expr.jump Js_422.fst (Arg.var nc, Arg.var alen, Arg.var n_units,
              Arg.var trivial_eid, Arg.var pb421.snd.fst, Arg.var pb421.snd.snd.snd.snd.fst, ()))
            (Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl)
              (Arg.var pb421.snd.snd.snd.fst, Arg.imm 0, ())) fun p424 =>
            Expr.jnz (Arg.var p424.fst)
              (Expr.jump Js_exit (Arg.var pb421.fst, Arg.var nc, Arg.var alen, Arg.var n_units,
                Arg.var eid_val, Arg.var pb421.snd.fst, Arg.var ei1, ()))
              (Expr.let_ (Op.mk (OpCode.cmp .uge i32 .bool rfl)
                (Arg.var nc, Arg.var max_orig_s, ())) fun p425 =>
              Expr.jnz (Arg.var p425.fst)
                (Expr.jump Js_exit (Arg.var pb421.fst, Arg.var nc, Arg.var alen,
                  Arg.var n_units, Arg.var trivial_eid, Arg.imm true, Arg.var ei1, ()))
                (Expr.let_ (Op.mk (OpCode.add i32)
                  (Arg.var alen, Arg.var pb421.snd.snd.snd.fst, ())) fun p426 =>
                Expr.let_ (Op.mk (OpCode.cmp .ugt i32 .bool rfl)
                  (Arg.var p426.fst, Arg.var acap, ()))
                  fun p427 =>
                Expr.jnz (Arg.var p427.fst)
                  (Expr.jump Js_exit (Arg.var pb421.fst, Arg.var nc, Arg.var alen,
                    Arg.var n_units, Arg.var trivial_eid, Arg.imm true, Arg.var ei1, ()))
                  (Expr.group (fun Js_428 : Tup Cont [[i32]] =>
                    Blocks.cons (fun pk : Tup Val [i32] =>
                    Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl)
                      (Arg.var pk.fst, Arg.var pb421.snd.snd.snd.fst, ())) fun p430 =>
                    Expr.jnz (Arg.var p430.fst)
                      (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_arena, Arg.var alen, ()))
                        fun p431 =>
                      Expr.let_ (Op.mk (OpCode.add i32) (Arg.var p431.fst, Arg.var pk.fst, ()))
                        fun p432 =>
                      Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p432.fst, ())) fun p433 =>
                      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p433.fst, Arg.imm 4, ()))
                        fun p434 =>
                      Expr.let_ (Op.mk (OpCode.add i64)
                        (Arg.var c.pScratchBuf, Arg.var p434.fst, ()))
                        fun p435 =>
                      Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var pk.fst, ())) fun p436 =>
                      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p436.fst, Arg.imm 4, ()))
                        fun p437 =>
                      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pTmp, Arg.var p437.fst, ()))
                        fun p438 =>
                      Expr.load i32 (Arg.var p438.fst) fun ld439 =>
                      Expr.store (Arg.var ld439) (Arg.var p435.fst)
                        (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pk.fst, Arg.imm 1, ()))
                          fun p440 => Expr.jump Js_428.fst (Arg.var p440.fst, ())))
                      (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_cl_off, Arg.var nc, ()))
                        fun p441 =>
                      Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p441.fst, ())) fun p442 =>
                      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p442.fst, Arg.imm 4, ()))
                        fun p443 =>
                      Expr.let_ (Op.mk (OpCode.add i64)
                        (Arg.var c.pScratchBuf, Arg.var p443.fst, ()))
                        fun p444 =>
                      Expr.store (Arg.var alen) (Arg.var p444.fst)
                        (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_cl_meta, Arg.var nc, ()))
                          fun p445 =>
                        Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p445.fst, ())) fun p446 =>
                        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p446.fst, Arg.imm 4, ()))
                          fun p447 =>
                        Expr.let_ (Op.mk (OpCode.add i64)
                          (Arg.var c.pScratchBuf, Arg.var p447.fst, ())) fun p448 =>
                        Expr.store (Arg.var pb421.snd.snd.snd.fst) (Arg.var p448.fst)
                          (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var o_cl_aux, Arg.var nc, ()))
                            fun p449 =>
                          Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p449.fst, ())) fun p450 =>
                          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p450.fst, Arg.imm 4, ()))
                            fun p451 =>
                          Expr.let_ (Op.mk (OpCode.add i64)
                            (Arg.var c.pScratchBuf, Arg.var p451.fst, ())) fun p452 =>
                          Expr.store (Arg.var eid_val) (Arg.var p452.fst)
                            (Expr.group (fun _Js_453 : Tup Cont [[i32]] =>
                              Blocks.cons (fun pu : Tup Val [i32] =>
                              Expr.let_ (Op.mk (OpCode.add i32) (Arg.var nc, Arg.imm 1, ()))
                                fun p455 =>
                              Expr.let_ (Op.mk (OpCode.add i32)
                                (Arg.var alen, Arg.var pb421.snd.snd.snd.fst, ())) fun p456 =>
                              Expr.jump Js_422.fst (Arg.var p455.fst, Arg.var p456.fst,
                                Arg.var pu.fst, Arg.var trivial_eid, Arg.var pb421.snd.fst,
                                Arg.var pk.fst, ())) Blocks.nil)
                              fun Js_453 =>
                              Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl)
                                (Arg.var pb421.snd.snd.snd.fst, Arg.imm 1, ())) fun p457 =>
                              Expr.jnz (Arg.var p457.fst)
                                (Expr.let_ (Op.mk (OpCode.add i32)
                                  (Arg.var o_units, Arg.var n_units, ())) fun p458 =>
                                Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p458.fst, ()))
                                  fun p459 =>
                                Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p459.fst, Arg.imm 4, ()))
                                  fun p460 =>
                                Expr.let_ (Op.mk (OpCode.add i64)
                                  (Arg.var c.pScratchBuf, Arg.var p460.fst, ())) fun p461 =>
                                Expr.store (Arg.var nc) (Arg.var p461.fst)
                                  (Expr.let_ (Op.mk (OpCode.add i32)
                                    (Arg.var n_units, Arg.imm 1, ())) fun p462 =>
                                  Expr.jump Js_453.fst (Arg.var p462.fst, ())))
                                (Expr.jump Js_453.fst (Arg.var n_units, ())))))))
                    Blocks.nil)
                    fun Js_428 => Expr.jump Js_428.fst (Arg.imm 0, ()))))))) Blocks.nil)
    fun Js_420 =>
    Expr.group (fun Js_463 : Tup Cont [[i32, i32, i32]] =>
      Blocks.cons (fun pl : Tup Val [i32, i32, i32] =>
      Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl) (Arg.var pl.snd.snd.fst, Arg.var ld419, ()))
        fun p465 =>
      Expr.jnz (Arg.var p465.fst)
        (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var w, ())) fun p466 =>
        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p466.fst, Arg.imm 3, ())) fun p467 =>
        Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var pl.snd.snd.fst, ())) fun p468 =>
        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var p467.fst, Arg.var p468.fst, ())) fun p469 =>
        Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p469.fst, Arg.imm 4, ())) fun p470 =>
        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pArena, Arg.var p470.fst, ())) fun p471 =>
        Expr.load i32 (Arg.var p471.fst) fun ld472 =>
        Expr.group (fun _Js_473 : Tup Cont [[i32, Ty.bool, Ty.bool, i32]] =>
          Blocks.cons (fun p474 =>
          Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pl.snd.snd.fst, Arg.imm 1, ())) fun p475 =>
          Expr.jump Js_463.fst (Arg.var p474.fst, Arg.var p474.snd.snd.snd.fst,
            Arg.var p475.fst, ())) Blocks.nil)
          fun Js_473 =>
          Expr.let_ (Op.mk (OpCode.cmp .ne i32 .bool rfl) (Arg.var ld472, Arg.var lit_cur, ()))
            fun p476 =>
          Expr.jnz (Arg.var p476.fst)
            (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var ld472, ())) fun p477 =>
            Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pVals, Arg.var p477.fst, ())) fun p478 =>
            Expr.load i8 (Arg.var p478.fst) fun ld479 =>
            Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm 0, ())) fun p480 =>
            Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var ld479, ())) fun p481 =>
            Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var p480.fst, ())) fun p482 =>
            Expr.let_ (Op.mk (OpCode.cmp .sgt i32 .bool rfl)
              (Arg.var p481.fst, Arg.var p482.fst, ()))
              fun p483 =>
            Expr.jnz (Arg.var p483.fst)
              (Expr.jump Js_420.fst (Arg.var pl.fst, Arg.var abort_s, Arg.imm true,
                Arg.var pl.snd.fst, Arg.var pl.snd.snd.fst, ()))
              (Expr.group (fun _Js_484 : Tup Cont [[i32, Ty.bool, i32]] => Blocks.cons (fun p485 =>
                Expr.jump Js_473.fst (Arg.var p485.fst, Arg.var p485.snd.fst, Arg.imm false,
                  Arg.var p485.snd.snd.fst, ())) Blocks.nil)
                fun Js_484 =>
                Expr.let_ (Op.mk (OpCode.trunc 32 8) (Arg.imm 0, ())) fun p486 =>
                Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var ld479, ())) fun p487 =>
                Expr.let_ (Op.mk (OpCode.sext 8 32) (Arg.var p486.fst, ())) fun p488 =>
                Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl)
                  (Arg.var p487.fst, Arg.var p488.fst, ())) fun p489 =>
                Expr.jnz (Arg.var p489.fst)
                  (Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var ld472, Arg.imm 1, ())) fun p490 =>
                  Expr.group (fun _Js_491 : Tup Cont [[i32, Ty.bool]] =>
                    Blocks.cons (fun p492 : Tup Val [i32, Ty.bool] =>
                    Expr.let_ (Op.mk (OpCode.cmp .uge i32 .bool rfl)
                      (Arg.var pl.snd.fst, Arg.var max_csz, ())) fun p493 =>
                    Expr.jnz (Arg.var p493.fst)
                      (Expr.jump Js_420.fst (Arg.var p492.fst, Arg.imm true, Arg.imm false,
                        Arg.var pl.snd.fst, Arg.var pl.snd.snd.fst, ()))
                      (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var pl.snd.fst, ())) fun p494 =>
                      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p494.fst, Arg.imm 4, ()))
                        fun p495 =>
                      Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pTmp, Arg.var p495.fst, ()))
                        fun p496 =>
                      Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p490.fst, ())) fun p497 =>
                      Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p497.fst, Arg.imm 4, ()))
                        fun p498 =>
                      Expr.let_ (Op.mk (OpCode.add i64)
                        (Arg.var c.pTarjanMark, Arg.var p498.fst, ())) fun p499 =>
                      Expr.load i32 (Arg.var p499.fst) fun ld500 =>
                      Expr.let_ (Op.mk (OpCode.sub i32) (Arg.var ld500, Arg.imm 1, ())) fun p501 =>
                      Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var p501.fst, Arg.imm 1, ()))
                        fun p502 =>
                      Expr.let_ (Op.mk (OpCode.and i32) (Arg.var ld472, Arg.imm 1, ())) fun p503 =>
                      Expr.let_ (Op.mk (OpCode.or i32) (Arg.var p502.fst, Arg.var p503.fst, ()))
                        fun p504 =>
                      Expr.store (Arg.var p504.fst) (Arg.var p496.fst)
                        (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pl.snd.fst, Arg.imm 1, ()))
                          fun p505 =>
                        Expr.jump Js_484.fst (Arg.var p492.fst, Arg.var p492.snd.fst,
                          Arg.var p505.fst, ())))) Blocks.nil)
                    fun Js_491 =>
                    Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p490.fst, ())) fun p506 =>
                    Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p506.fst, Arg.imm 4, ())) fun p507 =>
                    Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pTarjanMark, Arg.var p507.fst, ()))
                      fun p508 =>
                    Expr.load i32 (Arg.var p508.fst) fun ld509 =>
                    Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl) (Arg.var ld509, Arg.imm 0, ()))
                      fun p510 =>
                    Expr.jnz (Arg.var p510.fst)
                      (Expr.let_ (Op.mk (OpCode.cmp .uge i32 .bool rfl)
                        (Arg.var pl.fst, Arg.var mv_s, ())) fun p511 =>
                      Expr.jnz (Arg.var p511.fst)
                        (Expr.jump Js_420.fst (Arg.var pl.fst, Arg.imm true, Arg.imm false,
                          Arg.var pl.snd.fst, Arg.var pl.snd.snd.fst, ()))
                        (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var pl.fst, ())) fun p512 =>
                        Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.hdr, Arg.imm 776, ()))
                          fun p513 =>
                        Expr.load i64 (Arg.var p513.fst) fun ld514 =>
                        Expr.let_ (Op.mk (OpCode.sext 32 64) (Arg.imm 1, ())) fun p515 =>
                        Expr.let_ (Op.mk (OpCode.shl i64) (Arg.var ld514, Arg.var p515.fst, ()))
                          fun p516 =>
                        Expr.let_ (Op.mk (OpCode.cmp .uge i64 .bool rfl)
                          (Arg.var p512.fst, Arg.var p516.fst, ())) fun p517 =>
                        Expr.jnz (Arg.var p517.fst)
                          (Expr.jump Js_420.fst (Arg.var pl.fst, Arg.imm true, Arg.imm false,
                            Arg.var pl.snd.fst, Arg.var pl.snd.snd.fst, ()))
                          (Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var pl.fst, ())) fun p518 =>
                          Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p518.fst, Arg.imm 4, ()))
                            fun p519 =>
                          Expr.let_ (Op.mk (OpCode.add i64)
                            (Arg.var c.pWsort, Arg.var p519.fst, ()))
                            fun p520 =>
                          Expr.store (Arg.var p490.fst) (Arg.var p520.fst)
                            (Expr.let_ (Op.mk (OpCode.add i32) (Arg.var pl.fst, Arg.imm 1, ()))
                              fun p521 =>
                            Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p490.fst, ())) fun p522 =>
                            Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p522.fst, Arg.imm 4, ()))
                              fun p523 =>
                            Expr.let_ (Op.mk (OpCode.add i64)
                              (Arg.var c.pTarjanMark, Arg.var p523.fst, ())) fun p524 =>
                            Expr.store (Arg.var p521.fst) (Arg.var p524.fst)
                              (Expr.jump Js_491.fst (Arg.var p521.fst, Arg.var abort_s, ()))))))
                      (Expr.jump Js_491.fst (Arg.var pl.fst, Arg.var abort_s, ())))
                  (Expr.jump Js_484.fst
                    (Arg.var pl.fst, Arg.var abort_s, Arg.var pl.snd.fst, ()))))
            (Expr.jump Js_473.fst (Arg.var pl.fst, Arg.var abort_s, Arg.imm false,
              Arg.var pl.snd.fst, ())))
        (Expr.jump Js_420.fst (Arg.var pl.fst, Arg.var abort_s, Arg.imm false,
          Arg.var pl.snd.fst, Arg.var pl.snd.snd.fst, ()))) Blocks.nil)
      fun Js_463 => Expr.jump Js_463.fst (Arg.var nv, Arg.imm 0, Arg.imm 0, ())

/-! ## Binary entry handler (`J341` THEN branch) -/

private theorem fid_k6c_bin_entry_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost}
    {Js_exit : Cont [i32, i32, i32, i32, i32, Ty.bool, i32]}
    {Js_cont : Cont [i32, i32, i32, i32, i32, Ty.bool]}
    {c : FullCfg} {F0 : Std.Sat.CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {tmp wsort tmk scr : List (BitVec 32)}
    {nv nc alen n_units trivial_eid mv_s mc_s max_orig_s acap w lit_cur eid_val ei1 : BitVec 32}
    {o_cl_off o_cl_meta o_cl_aux o_units o_arena : BitVec 32} {abort_s : Bool}
    (hinv : FullDenseInvW c F0 F_cur s) (hcap : 16384 ≤ c.scratch_cap)
    (hmv_lo : 256 ≤ mv_s.toNat) (hmv_hi : mv_s.toNat ≤ 8192)
    (_hmc_s : mc_s = mv_s <<< 2) (hmax_orig_s : max_orig_s = mv_s <<< 1)
    (hoff_off : o_cl_off = 4224#32 + 29#32 * mv_s)
    (hoff_meta : o_cl_meta = 4224#32 + 33#32 * mv_s)
    (hoff_aux : o_cl_aux = 4224#32 + 37#32 * mv_s)
    (hoff_units : o_units = 4224#32 + 41#32 * mv_s)
    (hoff_arena : o_arena = 4224#32 + 45#32 * mv_s)
    (hcap_ar : 4224 + 45 * mv_s.toNat + acap.toNat ≤ c.scratch_cap)
    (htmp : tmp.length = c.max_vars) (hwsort : wsort.length = 2 * c.max_vars)
    (htmk : tmk.length = 2 * c.max_vars) (hscr : scr.length = c.scratch_cap)
    (hnv_le : nv.toNat ≤ mv_s.toNat) (hnv_cv : nv.toNat ≤ 2 * s.core.cur_vars)
    (hnc_le : nc.toNat ≤ 2 * mv_s.toNat) (halen_le : alen.toNat ≤ acap.toNat)
    (hnu_le : n_units.toNat ≤ nc.toNat)
    (heid : eid_val.toNat < 4096 ∧ (eid_val &&& 2047#32).toNat < 2001)
    (htriv_in : trivial_eid ≠ 4294967295#32 →
      trivial_eid.toNat < 4096 ∧ (trivial_eid &&& 2047#32).toNat < 2001)
    (hreg : FidK6cTmkReg nv.toNat s.core.cur_vars wsort tmk)
    (hcls : FidK6cClsOk mv_s.toNat nc.toNat alen.toNat n_units.toNat scr)
    (hp0 : ∀ i, i < 4002 → scr[i]? = s.scratch.scratch_buf[i]?)
    (hp1 : ∀ i, 4132 ≤ i → i < 4192 → scr[i]? = s.scratch.scratch_buf[i]?)
    (hent : FullBveEntryOkW F_cur s lit_cur.toNat w)
    (hnbin : w &&& 2147483648#32 ≠ 0#32)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m)
    (hExit : ∀ nv' nc' alen' nu' triv' (ab' : Bool) wsort' tmk' scr' m',
      nv'.toNat ≤ mv_s.toNat → nv'.toNat ≤ 2 * s.core.cur_vars →
      nc'.toNat ≤ 2 * mv_s.toNat → alen'.toNat ≤ acap.toNat → nu'.toNat ≤ nc'.toNat →
      (triv' ≠ 4294967295#32 → triv'.toNat < 4096 ∧ (triv' &&& 2047#32).toNat < 2001) →
      wsort'.length = 2 * c.max_vars → tmk'.length = 2 * c.max_vars → scr'.length = c.scratch_cap →
      FidK6cTmkReg nv'.toNat s.core.cur_vars wsort' tmk' →
      FidK6cClsOk mv_s.toNat nc'.toNat alen'.toNat nu'.toNat scr' →
      (∀ i, i < 4002 → scr'[i]? = s.scratch.scratch_buf[i]?) →
      (∀ i, 4132 ≤ i → i < 4192 → scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c (FidP6Work s tmp wsort' tmk' scr') ⋆ R) m' →
      Js_exit (nv', nc', alen', nu', triv', ab', ei1, ()) m')
    (hCont : ∀ nv' nc' alen' nu' (ab' : Bool) wsort' tmk' scr' m',
      nv'.toNat ≤ mv_s.toNat → nv'.toNat ≤ 2 * s.core.cur_vars →
      nc'.toNat ≤ 2 * mv_s.toNat → alen'.toNat ≤ acap.toNat → nu'.toNat ≤ nc'.toNat →
      wsort'.length = 2 * c.max_vars → tmk'.length = 2 * c.max_vars → scr'.length = c.scratch_cap →
      FidK6cTmkReg nv'.toNat s.core.cur_vars wsort' tmk' →
      FidK6cClsOk mv_s.toNat nc'.toNat alen'.toNat nu'.toNat scr' →
      (∀ i, i < 4002 → scr'[i]? = s.scratch.scratch_buf[i]?) →
      (∀ i, 4132 ≤ i → i < 4192 → scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c (FidP6Work s tmp wsort' tmk' scr') ⋆ R) m' →
      Js_cont (nv', nc', alen', nu', trivial_eid, ab', ()) m') :
    wp Γ Q X (fidBinEntryExpr c Js_exit Js_cont
      w nv nc alen n_units ei1 trivial_eid eid_val mv_s max_orig_s acap
      o_arena o_cl_off o_cl_meta o_cl_aux o_units abort_s) m := by
  have hbb := fid_k6c_entry_bin_bounds hent hnbin
  have hcv_mv : s.core.cur_vars ≤ c.max_vars := hinv.1.core_ok.cur_vars_le
  have hvals_len : s.core.vals.length = 2 * c.max_vars := hinv.1.core_ok.vals_len
  have hcv_lt : 2 * s.core.cur_vars < 2 ^ 30 := by
    have := c.hmaxv; simp only [Examples.LratBytes.dimacsBound] at this; omega
  have hscr_lt : scr.length < 2 ^ 30 := by
    have := c.hscr; simp only [Examples.LratBytes.dimacsBound] at this; omega
  have hoth_lt : (BitVec.setWidth 64 (w &&& 2147483647#32)).toNat < s.core.vals.length := by
    rw [fid_k6c_zext64]; omega
  dsimp only [fidBinEntryExpr]
  c0_hsteps_nogrp
  · exact hExit nv nc alen n_units eid_val abort_s wsort tmk scr m
      hnv_le hnv_cv hnc_le halen_le hnu_le (fun _ => heid) hwsort htmk hscr hreg hcls hp0 hp1 hm
  · apply wp_unroll_group
    intro Js_353 hJs_353
    have hJ353 : ∀ nv1 nc1 alen1 nu1 ab1 wsort1 tmk1 scr1 m1,
        nv1.toNat ≤ mv_s.toNat → nv1.toNat ≤ 2 * s.core.cur_vars →
        nc1.toNat ≤ 2 * mv_s.toNat → alen1.toNat ≤ acap.toNat → nu1.toNat ≤ nc1.toNat →
        wsort1.length = 2 * c.max_vars → tmk1.length = 2 * c.max_vars →
        scr1.length = c.scratch_cap →
        FidK6cTmkReg nv1.toNat s.core.cur_vars wsort1 tmk1 →
        FidK6cClsOk mv_s.toNat nc1.toNat alen1.toNat nu1.toNat scr1 →
        (∀ i, i < 4002 → scr1[i]? = s.scratch.scratch_buf[i]?) →
        (∀ i, 4132 ≤ i → i < 4192 → scr1[i]? = s.scratch.scratch_buf[i]?) →
        (FullMem c (FidP6Work s tmp wsort1 tmk1 scr1) ⋆ R) m1 →
        Js_353 (nv1, nc1, alen1, nu1, ab1, ()) m1 := by
      intro nv1 nc1 alen1 nu1 ab1 wsort1 tmk1 scr1 m1 h1 h2 h3 h4 h5 hw1 ht1 hs1
        hr1 hc1 hp0_1 hp1_1 hm1
      apply hJs_353; try dsimp only [Blocks.get, Member.here]
      exact hCont nv1 nc1 alen1 nu1 ab1 wsort1 tmk1 scr1 m1
        h1 h2 h3 h4 h5 hw1 ht1 hs1 hr1 hc1 hp0_1 hp1_1 hm1
    clear hJs_353
    c0_hsteps_nogrp
    · have hv_lt : ((w &&& 2147483647#32) >>> 1).toNat < s.core.cur_vars := by
        simpa [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] using hbb.2.1
      have htmp_lt : (BitVec.setWidth 64 ((w &&& 2147483647#32) >>> 1)).toNat < tmp.length := by
        rw [fid_k6c_zext64]; omega
      have htmk_lt : (BitVec.setWidth 64 ((w &&& 2147483647#32) >>> 1)).toNat < tmk.length := by
        rw [fid_k6c_zext64]; omega
      apply wp_unroll_group
      intro Js_360 hJs_360
      have hJ360 : ∀ nv1 ab1 wsort1 tmk1 m1,
          nv1.toNat ≤ mv_s.toNat → nv1.toNat ≤ 2 * s.core.cur_vars →
          wsort1.length = 2 * c.max_vars → tmk1.length = 2 * c.max_vars →
          FidK6cTmkReg nv1.toNat s.core.cur_vars wsort1 tmk1 →
          (FullMem c (FidP6Work s tmp wsort1 tmk1 scr) ⋆ R) m1 →
          Js_360 (nv1, ab1, ()) m1 := by
        intro nv1 ab1 wsort1 tmk1 m1 h1 h2 hw1 ht1 hr1 hm1
        apply hJs_360; try dsimp only [Blocks.get, Member.here]
        have hmxs : max_orig_s.toNat = 2 * mv_s.toNat := by
          rw [hmax_orig_s]; exact m8_bv32_shl1_toNat (by omega)
        have htmk1_lt :
            (BitVec.setWidth 64 ((w &&& 2147483647#32) >>> 1)).toNat < tmk1.length := by
          rw [fid_k6c_zext64]; omega
        c0_hsteps
        · exact hExit nv1 nc alen n_units trivial_eid true wsort1 tmk1 scr m1
            h1 h2 hnc_le halen_le hnu_le htriv_in hw1 ht1 hscr hr1 hcls hp0 hp1 hm1
        · exact hExit nv1 nc alen n_units trivial_eid true wsort1 tmk1 scr m1
            h1 h2 hnc_le halen_le hnu_le htriv_in hw1 ht1 hscr hr1 hcls hp0 hp1 hm1
        · have hnc_lt : nc.toNat < 2 * mv_s.toNat := by bv_omega
          have hal_lt : alen.toNat + 1 ≤ acap.toNat := by bv_omega
          have har_eq : (BitVec.setWidth 64 (o_arena + alen)).toNat =
              4224 + 45 * mv_s.toNat + alen.toNat := by
            rw [hoff_arena]; exact fid_k6_off_add hmv_hi (by omega) (by omega)
          have hof_eq : (BitVec.setWidth 64 (o_cl_off + nc)).toNat =
              4224 + 29 * mv_s.toNat + nc.toNat := by
            rw [hoff_off]; exact fid_k6_off_add hmv_hi (by omega) (by omega)
          have hmt_eq : (BitVec.setWidth 64 (o_cl_meta + nc)).toNat =
              4224 + 33 * mv_s.toNat + nc.toNat := by
            rw [hoff_meta]; exact fid_k6_off_add hmv_hi (by omega) (by omega)
          have hax_eq : (BitVec.setWidth 64 (o_cl_aux + nc)).toNat =
              4224 + 37 * mv_s.toNat + nc.toNat := by
            rw [hoff_aux]; exact fid_k6_off_add hmv_hi (by omega) (by omega)
          have hun_eq : (BitVec.setWidth 64 (o_units + n_units)).toNat =
              4224 + 41 * mv_s.toNat + n_units.toNat := by
            rw [hoff_units]; exact fid_k6_off_add hmv_hi (by omega) (by omega)
          have har_lt : (BitVec.setWidth 64 (o_arena + alen)).toNat < scr.length := by
            rw [har_eq]; omega
          have hof_lt : (BitVec.setWidth 64 (o_cl_off + nc)).toNat < c.scratch_cap := by
            rw [hof_eq]; omega
          have hmt_lt : (BitVec.setWidth 64 (o_cl_meta + nc)).toNat < c.scratch_cap := by
            rw [hmt_eq]; omega
          have hax_lt : (BitVec.setWidth 64 (o_cl_aux + nc)).toNat < c.scratch_cap := by
            rw [hax_eq]; omega
          have hun_lt : (BitVec.setWidth 64 (o_units + n_units)).toNat < c.scratch_cap := by
            rw [hun_eq]; omega
          c0_hsteps
          have hnc1 : (nc + 1#32).toNat = nc.toNat + 1 := fid_k6c_add1_toNat hnc_lt (by omega)
          have hal1 : (alen + 1#32).toNat = alen.toNat + 1 :=
            fid_k6c_add1_toNat (by omega : alen.toNat < acap.toNat) (by omega)
          have hnu1 : (n_units + 1#32).toNat = n_units.toNat + 1 :=
            fid_k6c_add1_toNat (by omega : n_units.toNat < 2 * mv_s.toNat) (by omega)
          refine hJ353 nv1 (nc + 1#32) (alen + 1#32) (n_units + 1#32) ab1 wsort1 tmk1 _ _
            h1 h2 (by omega) (by omega) (by omega) hw1 ht1 (by simp [hscr]) hr1 ?_ ?_ ?_ hm
          · exact fid_k6c_bin_clsOk (acap_n := acap.toNat) hmv_lo hmv_hi
              (by dsimp only [FidP6Work]; omega) hscr_lt
              hoff_off hoff_meta hoff_aux hoff_units hoff_arena hnc_lt hal_lt hnu_le heid hcls
          · intro i hi
            dsimp only [FidP6Work]
            repeat rw [List.getElem?_set_ne (by
              try simp only [har_eq, hof_eq, hmt_eq, hax_eq, hun_eq]; omega)]
            exact hp0 i hi
          · intro i hlo hhi
            dsimp only [FidP6Work]
            repeat rw [List.getElem?_set_ne (by
              try simp only [har_eq, hof_eq, hmt_eq, hax_eq, hun_eq]; omega)]
            exact hp1 i hlo hhi
      clear hJs_360
      c0_hsteps
      · exact hExit nv nc alen n_units trivial_eid true wsort tmk scr m
          hnv_le hnv_cv hnc_le halen_le hnu_le htriv_in hwsort htmk hscr hreg hcls hp0 hp1 hm
      · exact hExit nv nc alen n_units trivial_eid true wsort tmk scr m
          hnv_le hnv_cv hnc_le halen_le hnu_le htriv_in hwsort htmk hscr hreg hcls hp0 hp1 hm
      · have hnv_mv : nv.toNat < mv_s.toNat := by bv_omega
        have hnv_cv2 : nv.toNat < 2 * s.core.cur_vars := by bv_omega
        have hws_lt : (BitVec.setWidth 64 nv).toNat < wsort.length := by
          rw [fid_k6c_zext64]; omega
        have htmk_lt2 : (BitVec.setWidth 64 ((w &&& 2147483647#32) >>> 1)).toNat <
            tmk.length := by
          rw [fid_k6c_zext64]; omega
        c0_hsteps
        have hnv1 : (nv + 1#32).toNat = nv.toNat + 1 :=
          fid_k6c_add1_toNat hnv_mv (by omega)
        have htmkz : tmk[((w &&& 2147483647#32) >>> 1).toNat]?.getD 0#32 = 0#32 := by
          rw [List.getElem?_eq_getElem
              (by omega : ((w &&& 2147483647#32) >>> 1).toNat < tmk.length),
            Option.getD_some]
          have hidx : ((w &&& 2147483647#32) >>> 1).toNat = w.toNat % 2 ^ 31 / 2 := by
            simp only [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one,
              BitVec.toNat_and,
              show (2147483647#32 : BitVec 32).toNat = 2 ^ 31 - 1 from rfl,
              Nat.and_two_pow_sub_one_eq_mod]
          simp only [hidx]; assumption
        have hreg1 := fid_k6c_tmkReg_step hreg hnv_cv2 hv_lt htmkz (Or.inr (by omega))
          (by omega : _ < tmk.length) hcv_lt
        have hvn : BitVec.ofNat 32 ((w &&& 2147483647#32) >>> 1).toNat =
            (w &&& 2147483647#32) >>> 1 := by
          apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]
          exact Nat.mod_eq_of_lt (by bv_omega)
        have hnv_eq : BitVec.ofNat 32 (nv.toNat + 1) = nv + 1#32 := by
          apply BitVec.eq_of_toNat_eq; rw [hnv1, BitVec.toNat_ofNat]
          exact Nat.mod_eq_of_lt (by omega)
        rw [hvn, hnv_eq] at hreg1
        refine hJ360 (nv + 1#32) abort_s _ _ _ (by omega) (by omega)
          (by simp [hwsort]) (by simp [htmk]) ?_ hm
        dsimp only [FidP6Work]
        repeat rw [fid_k6c_zext64]
        rw [hnv1]; exact hreg1
      · exact hJ360 nv abort_s wsort tmk m hnv_le hnv_cv hwsort htmk hreg hm
    · exact hJ353 nv nc alen n_units abort_s wsort tmk scr m
        hnv_le hnv_cv hnc_le halen_le hnu_le hwsort htmk hscr hreg hcls hp0 hp1 hm

/-! ## Large entry handler (`J341` ELSE branch) -/

private theorem fid_k6c_large_entry_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost}
    {Js_exit : Cont [i32, i32, i32, i32, i32, Ty.bool, i32]}
    {Js_cont : Cont [i32, i32, i32, i32, i32, Ty.bool]}
    {c : FullCfg} {F0 : Std.Sat.CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {tmp wsort tmk scr : List (BitVec 32)}
    {nv nc alen n_units trivial_eid mv_s mc_s max_orig_s max_csz acap w lit_cur eid_val ei1 :
      BitVec 32}
    {o_cl_off o_cl_meta o_cl_aux o_units o_arena : BitVec 32} {abort_s : Bool}
    (hinv : FullDenseInvW c F0 F_cur s) (hcap : 16384 ≤ c.scratch_cap)
    (hmv_lo : 256 ≤ mv_s.toNat) (hmv_hi : mv_s.toNat ≤ 8192)
    (_hmc_s : mc_s = mv_s <<< 2) (hmax_orig_s : max_orig_s = mv_s <<< 1)
    (hmax_csz : max_csz.toNat ≤ c.max_vars ∧ max_csz.toNat ≤ 65535)
    (hoff_off : o_cl_off = 4224#32 + 29#32 * mv_s)
    (hoff_meta : o_cl_meta = 4224#32 + 33#32 * mv_s)
    (hoff_aux : o_cl_aux = 4224#32 + 37#32 * mv_s)
    (hoff_units : o_units = 4224#32 + 41#32 * mv_s)
    (hoff_arena : o_arena = 4224#32 + 45#32 * mv_s)
    (hcap_ar : 4224 + 45 * mv_s.toNat + acap.toNat ≤ c.scratch_cap)
    (htmp : tmp.length = c.max_vars) (hwsort : wsort.length = 2 * c.max_vars)
    (htmk : tmk.length = 2 * c.max_vars) (hscr : scr.length = c.scratch_cap)
    (hnv_le : nv.toNat ≤ mv_s.toNat) (hnv_cv : nv.toNat ≤ 2 * s.core.cur_vars)
    (hnc_le : nc.toNat ≤ 2 * mv_s.toNat) (halen_le : alen.toNat ≤ acap.toNat)
    (hnu_le : n_units.toNat ≤ nc.toNat)
    (heid : eid_val.toNat < 4096 ∧ (eid_val &&& 2047#32).toNat < 2001)
    (htriv_in : trivial_eid ≠ 4294967295#32 →
      trivial_eid.toNat < 4096 ∧ (trivial_eid &&& 2047#32).toNat < 2001)
    (hreg : FidK6cTmkReg nv.toNat s.core.cur_vars wsort tmk)
    (hcls : FidK6cClsOk mv_s.toNat nc.toNat alen.toNat n_units.toNat scr)
    (hp0 : ∀ i, i < 4002 → scr[i]? = s.scratch.scratch_buf[i]?)
    (hp1 : ∀ i, 4132 ≤ i → i < 4192 → scr[i]? = s.scratch.scratch_buf[i]?)
    (hent : FullBveEntryOkW F_cur s lit_cur.toNat w)
    (hnbin : w &&& 2147483648#32 = 0#32)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m)
    (hExit : ∀ nv' nc' alen' nu' triv' (ab' : Bool) tmp' wsort' tmk' scr' m',
      nv'.toNat ≤ mv_s.toNat → nv'.toNat ≤ 2 * s.core.cur_vars →
      nc'.toNat ≤ 2 * mv_s.toNat → alen'.toNat ≤ acap.toNat → nu'.toNat ≤ nc'.toNat →
      (triv' ≠ 4294967295#32 → triv'.toNat < 4096 ∧ (triv' &&& 2047#32).toNat < 2001) →
      tmp'.length = c.max_vars → wsort'.length = 2 * c.max_vars →
      tmk'.length = 2 * c.max_vars → scr'.length = c.scratch_cap →
      FidK6cTmkReg nv'.toNat s.core.cur_vars wsort' tmk' →
      FidK6cClsOk mv_s.toNat nc'.toNat alen'.toNat nu'.toNat scr' →
      (∀ i, i < 4002 → scr'[i]? = s.scratch.scratch_buf[i]?) →
      (∀ i, 4132 ≤ i → i < 4192 → scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c (FidP6Work s tmp' wsort' tmk' scr') ⋆ R) m' →
      Js_exit (nv', nc', alen', nu', triv', ab', ei1, ()) m')
    (hCont : ∀ nv' nc' alen' nu' (ab' : Bool) tmp' wsort' tmk' scr' m',
      nv'.toNat ≤ mv_s.toNat → nv'.toNat ≤ 2 * s.core.cur_vars →
      nc'.toNat ≤ 2 * mv_s.toNat → alen'.toNat ≤ acap.toNat → nu'.toNat ≤ nc'.toNat →
      tmp'.length = c.max_vars → wsort'.length = 2 * c.max_vars →
      tmk'.length = 2 * c.max_vars → scr'.length = c.scratch_cap →
      FidK6cTmkReg nv'.toNat s.core.cur_vars wsort' tmk' →
      FidK6cClsOk mv_s.toNat nc'.toNat alen'.toNat nu'.toNat scr' →
      (∀ i, i < 4002 → scr'[i]? = s.scratch.scratch_buf[i]?) →
      (∀ i, 4132 ≤ i → i < 4192 → scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c (FidP6Work s tmp' wsort' tmk' scr') ⋆ R) m' →
      Js_cont (nv', nc', alen', nu', trivial_eid, ab', ()) m') :
    wp Γ Q X (fidLargeEntryExpr c Js_exit Js_cont
      w nv nc alen n_units ei1 trivial_eid eid_val lit_cur mv_s max_orig_s max_csz acap
      o_arena o_cl_off o_cl_meta o_cl_aux o_units abort_s) m := by
  have hlb := fid_k6c_entry_large_bounds hinv.1 hinv.2.1.arena hent hnbin
  have har_len : s.core.arena_len ≤ c.arena_cap := hlb.2.2.2.1
  have har_arr : s.core.arena.length = c.arena_cap := hinv.1.core_ok.arena_len_arr
  have har2_lt : (BitVec.setWidth 64 w + 2#64).toNat < s.core.arena.length := by
    have := hlb.1; simp only [BitVec.toNat_add, BitVec.toNat_setWidth]; bv_omega
  dsimp only [fidLargeEntryExpr]
  c0_hsteps_nogrp
  have hsz_eq : (s.core.arena[(BitVec.setWidth 64 w + 2#64).toNat]).toNat =
      fullArenaClauseSizeCore s.core w.toNat := by
    have heq : (BitVec.setWidth 64 w + 2#64).toNat = w.toNat + 2 := by bv_omega
    simp only [fullArenaClauseSizeCore, heq,
      List.getElem?_eq_getElem (by omega : w.toNat + 2 < s.core.arena.length), Option.getD_some]
  apply wp_unroll_group
  intro Js_420 hJs_420
  have hJ420 : ∀ nv' ab' sat' csz' j' tmp' wsort' tmk',
      tmp'.length = c.max_vars → wsort'.length = 2 * c.max_vars → tmk'.length = 2 * c.max_vars →
      nv'.toNat ≤ mv_s.toNat → nv'.toNat ≤ 2 * s.core.cur_vars → csz'.toNat ≤ max_csz.toNat →
      FidK6cTmkReg nv'.toNat s.core.cur_vars wsort' tmk' →
      ∀ m', (FullMem c (FidP6Work s tmp' wsort' tmk' scr) ⋆ R) m' →
      Js_420 (nv', ab', sat', csz', j', ()) m' := by
    intro nv' ab' sat' csz' j' tmp' wsort' tmk' htp' hws' htm' hnv' hnvcv' hcsz' hreg' m' hm'
    apply hJs_420; try dsimp only [Blocks.get, Member.here]
    c0_hsteps_nogrp
    · exact hExit nv' nc alen n_units trivial_eid ab' tmp' wsort' tmk' scr m'
        hnv' hnvcv' hnc_le halen_le hnu_le htriv_in htp' hws' htm' hscr hreg' hcls hp0 hp1 hm'
    · apply wp_unroll_group
      intro Js_422 hJs_422
      have hJ422 : ∀ nc' alen' nu' ab'' k_out scr',
          nc'.toNat ≤ 2 * mv_s.toNat → alen'.toNat ≤ acap.toNat → nu'.toNat ≤ nc'.toNat →
          scr'.length = c.scratch_cap →
          FidK6cClsOk mv_s.toNat nc'.toNat alen'.toNat nu'.toNat scr' →
          (∀ i, i < 4002 → scr'[i]? = s.scratch.scratch_buf[i]?) →
          (∀ i, 4132 ≤ i → i < 4192 → scr'[i]? = s.scratch.scratch_buf[i]?) →
          ∀ m'', (FullMem c (FidP6Work s tmp' wsort' tmk' scr') ⋆ R) m'' →
          Js_422 (nc', alen', nu', trivial_eid, ab'', k_out, ()) m'' := by
        intro nc' alen' nu' ab'' k_out scr' h1 h2 h3 hs' hc' hp0' hp1' m'' hm''
        apply hJs_422; try dsimp only [Blocks.get, Member.here]
        c0_hsteps
        exact hCont nv' nc' alen' nu' ab'' tmp' wsort' tmk' scr' m''
          hnv' hnvcv' h1 h2 h3 htp' hws' htm' hs' hreg' hc' hp0' hp1' hm''
      clear hJs_422
      c0_hsteps_nogrp
      · exact hJ422 nc alen n_units ab' j' scr
          hnc_le halen_le hnu_le hscr hcls hp0 hp1 m' hm'
      · exact hExit nv' nc alen n_units eid_val ab' tmp' wsort' tmk' scr m'
          hnv' hnvcv' hnc_le halen_le hnu_le (fun _ => heid) htp' hws' htm' hscr
          hreg' hcls hp0 hp1 hm'
      · exact hExit nv' nc alen n_units trivial_eid true tmp' wsort' tmk' scr m'
          hnv' hnvcv' hnc_le halen_le hnu_le htriv_in htp' hws' htm' hscr hreg' hcls hp0 hp1 hm'
      · exact hExit nv' nc alen n_units trivial_eid true tmp' wsort' tmk' scr m'
          hnv' hnvcv' hnc_le halen_le hnu_le htriv_in htp' hws' htm' hscr hreg' hcls hp0 hp1 hm'
      · have hmxs : max_orig_s.toNat = 2 * mv_s.toNat := by
          rw [hmax_orig_s]; exact m8_bv32_shl1_toNat (by omega)
        have hnc_lt : nc.toNat < 2 * mv_s.toNat := by bv_omega
        have hal_lt : alen.toNat + csz'.toNat ≤ acap.toNat := by
          have hscr_lt : scr.length < 2 ^ 30 := by
            have := c.hscr; simp only [Examples.LratBytes.dimacsBound] at this; omega
          have h32 : alen.toNat + csz'.toNat < 2 ^ 32 := by omega
          have hadd : (alen + csz').toNat = alen.toNat + csz'.toNat := by bv_omega
          bv_omega
        have hcsz_pos : 1 ≤ csz'.toNat := by bv_omega
        have hscr_lt : scr.length < 2 ^ 30 := by
          have := c.hscr; simp only [Examples.LratBytes.dimacsBound] at this; omega
        refine fid_k6c_copy_clause_wp hmv_lo hmv_hi hcap_ar hscr_lt hscr htp'
          hoff_off hoff_meta hoff_aux hoff_units hoff_arena
          hcsz_pos (Nat.le_trans hcsz' hmax_csz.1) (Nat.le_trans hcsz' hmax_csz.2)
          hnc_lt hnu_le hal_lt heid hcls hm' ?_
        intro scr2 pu k_out m2 hs2 hag2 hc2 hpu2 hm2
        have hnc1 : (nc + 1#32).toNat = nc.toNat + 1 := fid_k6c_add1_toNat hnc_lt (by omega)
        have hal1 : (alen + csz').toNat = alen.toNat + csz'.toNat := by bv_omega
        refine hJ422 (nc + 1#32) (alen + csz') pu ab' k_out scr2
          (by omega) (by omega) ?_ hs2 hc2 ?_ ?_ m2 hm2
        · rw [hpu2]; split <;> omega
        · intro i hi; rw [hag2 i (by omega)]; exact hp0 i hi
        · intro i hlo hhi; rw [hag2 i (by omega)]; exact hp1 i hlo hhi
  clear hJs_420
  dsimp only [FidP6Work] at *
  refine fid_k6c_scan_large_wp (K_done := Js_420) (lit := lit_cur) (off := w)
    (sz := s.core.arena[(BitVec.setWidth 64 w + 2#64).toNat]) (abort_in := abort_s)
    hinv.1 hmv_lo hmv_hi hmax_csz.1 htmp hwsort htmk
    hnv_le hnv_cv ?_ ?_ hreg hm ?_
  · rw [hsz_eq]; omega
  · intro k hk; rw [hsz_eq] at hk; exact (hlb.2.2.2.2 k hk).2
  · intro nv' csz' j' ab' sat' tmp' wsort' tmk' m' h1 h2 h3 h4 h5 h6 h7 hm'
    exact hJ420 nv' ab' sat' csz' j' tmp' wsort' tmk' h1 h2 h3 h4 h5 h6 h7 m' hm'

/-! ## Inner pass loop (`J323` -> `J326`) & main `full_k6_extract_and_solve_fid_wp` -/

private theorem fid_k6c_extract_side_wp {Γ : Env} {Q : Post [Ty.bool]} {X : XPost}
    {Js_outer : Cont [i32, i32, i32, i32, i32, Ty.bool, i32]}
    {c : FullCfg} {F0 : Std.Sat.CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {tmp wsort tmk scr : List (BitVec 32)}
    {nv nc alen n_units trivial_eid step mv_s mc_s max_orig_s max_csz acap : BitVec 32}
    {side side_lim m_off m_base lit_cur o_cl_off o_cl_meta o_cl_aux o_units o_arena : BitVec 32}
    {second_pass abort : Bool}
    (hinv : FullDenseInvW c F0 F_cur s) (hcap : 16384 ≤ c.scratch_cap)
    (hmv_lo : 256 ≤ mv_s.toNat) (hmv_hi : mv_s.toNat ≤ 8192)
    (hmc_s : mc_s = mv_s <<< 2) (hmax_orig_s : max_orig_s = mv_s <<< 1)
    (hmax_csz : max_csz.toNat ≤ c.max_vars ∧ max_csz.toNat ≤ 65535)
    (hoff_off : o_cl_off = 4224#32 + 29#32 * mv_s)
    (hoff_meta : o_cl_meta = 4224#32 + 33#32 * mv_s)
    (hoff_aux : o_cl_aux = 4224#32 + 37#32 * mv_s)
    (hoff_units : o_units = 4224#32 + 41#32 * mv_s)
    (hoff_arena : o_arena = 4224#32 + 45#32 * mv_s)
    (hcap_ar : 4224 + 45 * mv_s.toNat + acap.toNat ≤ c.scratch_cap)
    (hside : side = 0#32 ∨ side = 1#32) (hlim : side_lim.toNat ≤ 2001)
    (hmoff : (side = 0#32 → m_off = 0#32) ∧ (side = 1#32 → m_off = 2001#32))
    (hmbase : m_base = 4002#32 ∨ m_base = 4066#32)
    (_hlit : lit_cur.toNat < 2 * s.core.cur_vars)
    (hent : ∀ idx : Nat, idx < side_lim.toNat →
      FullBveEntryOkW F_cur s lit_cur.toNat (s.scratch.scratch_buf[m_off.toNat + idx]?.getD 0#32))
    (htmp : tmp.length = c.max_vars) (hwsort : wsort.length = 2 * c.max_vars)
    (htmk : tmk.length = 2 * c.max_vars) (hscr : scr.length = c.scratch_cap)
    (hnv_le : nv.toNat ≤ mv_s.toNat) (hnv_cv : nv.toNat ≤ 2 * s.core.cur_vars)
    (hnc_le : nc.toNat ≤ 2 * mv_s.toNat) (halen_le : alen.toNat ≤ acap.toNat)
    (hnu_le : n_units.toNat ≤ nc.toNat) (_hstep : step.toNat < 2)
    (htriv_in : trivial_eid ≠ 4294967295#32 →
      trivial_eid.toNat < 4096 ∧ (trivial_eid &&& 2047#32).toNat < 2001)
    (hreg : FidK6cTmkReg nv.toNat s.core.cur_vars wsort tmk)
    (hcls : FidK6cClsOk mv_s.toNat nc.toNat alen.toNat n_units.toNat scr)
    (hp0 : ∀ i, i < 4002 → scr[i]? = s.scratch.scratch_buf[i]?)
    (hp1 : ∀ i, 4132 ≤ i → i < 4192 → scr[i]? = s.scratch.scratch_buf[i]?)
    (hm : (FullMem c (FidP6Work s tmp wsort tmk scr) ⋆ R) m)
    (hOuter : ∀ nv' nc' alen' nu' triv' (ab' : Bool) tmp' wsort' tmk' scr' m',
      nv'.toNat ≤ mv_s.toNat → nv'.toNat ≤ 2 * s.core.cur_vars →
      nc'.toNat ≤ 2 * mv_s.toNat → alen'.toNat ≤ acap.toNat → nu'.toNat ≤ nc'.toNat →
      (triv' ≠ 4294967295#32 → triv'.toNat < 4096 ∧ (triv' &&& 2047#32).toNat < 2001) →
      tmp'.length = c.max_vars → wsort'.length = 2 * c.max_vars →
      tmk'.length = 2 * c.max_vars → scr'.length = c.scratch_cap →
      FidK6cTmkReg nv'.toNat s.core.cur_vars wsort' tmk' →
      FidK6cClsOk mv_s.toNat nc'.toNat alen'.toNat nu'.toNat scr' →
      (∀ i, i < 4002 → scr'[i]? = s.scratch.scratch_buf[i]?) →
      (∀ i, 4132 ≤ i → i < 4192 → scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c (FidP6Work s tmp' wsort' tmk' scr') ⋆ R) m' →
      Js_outer (nv', nc', alen', nu', triv', ab', step + 1#32, ()) m') :
    wp Γ Q X
      (Expr.group (fun _Js_323 : Tup Cont [[i32, i32, i32, i32, i32, Ty.bool, i32]] =>
        Blocks.cons (fun pb324 =>
          Expr.let_ (Op.mk (OpCode.add i32) (Arg.var step, Arg.imm 1, ())) fun p325 =>
          Expr.jump Js_outer (Arg.var pb324.fst, Arg.var pb324.snd.fst, Arg.var pb324.snd.snd.fst,
            Arg.var pb324.snd.snd.snd.fst, Arg.var pb324.snd.snd.snd.snd.fst,
            Arg.var pb324.snd.snd.snd.snd.snd.fst, Arg.var p325.fst, ())) Blocks.nil)
        fun Js_323 =>
        Expr.group (fun Js_326 : Tup Cont [[i32, i32, i32, i32, Ty.bool, i32]] =>
          Blocks.cons (fun pb327 =>
            Expr.let_ (Op.mk (OpCode.cmp .ult i32 .bool rfl)
              (Arg.var pb327.snd.snd.snd.snd.snd.fst, Arg.var side_lim, ())) fun p328 =>
            Expr.jnz (Arg.var p328.fst)
              (Expr.jnz (Arg.var pb327.snd.snd.snd.snd.fst)
                (Expr.jump Js_323.fst (Arg.var pb327.fst, Arg.var pb327.snd.fst,
                  Arg.var pb327.snd.snd.fst, Arg.var pb327.snd.snd.snd.fst,
                  Arg.var trivial_eid, Arg.var pb327.snd.snd.snd.snd.fst,
                  Arg.var pb327.snd.snd.snd.snd.snd.fst, ()))
                (Expr.group (fun _Js_329 : Tup Cont [[i32]] => Blocks.cons (fun pb330 =>
                  Expr.let_ (Op.mk (OpCode.add i32)
                    (Arg.var pb327.snd.snd.snd.snd.snd.fst, Arg.imm 1, ())) fun p331 =>
                  Expr.group (fun _Js_332 : Tup Cont [[]] => Blocks.cons (fun _ =>
                    Expr.let_ (Op.mk (OpCode.add i32) (Arg.var m_off, Arg.var pb330.fst, ()))
                      fun p334 =>
                    Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p334.fst, ())) fun p335 =>
                    Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p335.fst, Arg.imm 4, ())) fun p336 =>
                    Expr.let_ (Op.mk (OpCode.add i64)
                      (Arg.var c.pScratchBuf, Arg.var p336.fst, ())) fun p337 =>
                    Expr.load i32 (Arg.var p337.fst) fun ld338 =>
                    Expr.let_ (Op.mk (OpCode.shl i32) (Arg.var side, Arg.imm 11, ())) fun p339 =>
                    Expr.let_ (Op.mk (OpCode.or i32) (Arg.var p339.fst, Arg.var pb330.fst, ()))
                      fun p340 =>
                    Expr.group (fun _Js_341 : Tup Cont [[i32, i32, i32, i32, i32, Ty.bool]] =>
                      Blocks.cons (fun pb342 =>
                        Expr.jump Js_326.fst (Arg.var pb342.fst, Arg.var pb342.snd.fst,
                          Arg.var pb342.snd.snd.fst, Arg.var pb342.snd.snd.snd.fst,
                          Arg.var pb342.snd.snd.snd.snd.snd.fst, Arg.var p331.fst, ())) Blocks.nil)
                      fun Js_341 =>
                      Expr.let_ (Op.mk (OpCode.and i32) (Arg.var ld338, Arg.imm 2147483648, ()))
                        fun p343 =>
                      Expr.let_ (Op.mk (OpCode.cmp .ne i32 .bool rfl)
                        (Arg.var p343.fst, Arg.imm 0, ())) fun p344 =>
                      Expr.jnz (Arg.var p344.fst)
                        (fidBinEntryExpr c Js_323.fst Js_341.fst ld338 pb327.fst pb327.snd.fst
                          pb327.snd.snd.fst pb327.snd.snd.snd.fst p331.fst trivial_eid p340.fst
                          mv_s max_orig_s acap o_arena o_cl_off o_cl_meta o_cl_aux o_units
                          pb327.snd.snd.snd.snd.fst)
                        (fidLargeEntryExpr c Js_323.fst Js_341.fst ld338 pb327.fst pb327.snd.fst
                          pb327.snd.snd.fst pb327.snd.snd.snd.fst p331.fst trivial_eid p340.fst
                          lit_cur mv_s max_orig_s max_csz acap
                          o_arena o_cl_off o_cl_meta o_cl_aux o_units
                          pb327.snd.snd.snd.snd.fst)) Blocks.nil)
                  fun Js_332 =>
                  Expr.jnz (Arg.var second_pass)
                    (Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var pb330.fst, Arg.imm 5, ()))
                      fun p525 =>
                    Expr.let_ (Op.mk (OpCode.add i32) (Arg.var m_base, Arg.var p525.fst, ()))
                      fun p526 =>
                    Expr.let_ (Op.mk (OpCode.zext 32 64) (Arg.var p526.fst, ())) fun p527 =>
                    Expr.let_ (Op.mk (OpCode.mul i64) (Arg.var p527.fst, Arg.imm 4, ())) fun p528 =>
                    Expr.let_ (Op.mk (OpCode.add i64) (Arg.var c.pScratchBuf, Arg.var p528.fst, ()))
                      fun p529 =>
                    Expr.load i32 (Arg.var p529.fst) fun ld530 =>
                    Expr.let_ (Op.mk (OpCode.and i32) (Arg.var pb330.fst, Arg.imm 31, ()))
                      fun p531 =>
                    Expr.let_ (Op.mk (OpCode.lshr i32) (Arg.var ld530, Arg.var p531.fst, ()))
                      fun p532 =>
                    Expr.let_ (Op.mk (OpCode.and i32) (Arg.var p532.fst, Arg.imm 1, ())) fun p533 =>
                    Expr.let_ (Op.mk (OpCode.cmp .eq i32 .bool rfl)
                      (Arg.var p533.fst, Arg.imm 0, ())) fun p534 =>
                    Expr.jnz (Arg.var p534.fst)
                      (Expr.jump Js_326.fst (Arg.var pb327.fst, Arg.var pb327.snd.fst,
                        Arg.var pb327.snd.snd.fst, Arg.var pb327.snd.snd.snd.fst,
                        Arg.var pb327.snd.snd.snd.snd.fst, Arg.var p331.fst, ()))
                      (Expr.jump Js_332.fst ()))
                    (Expr.jump Js_332.fst ())) Blocks.nil)
                  fun Js_329 =>
                  Expr.jnz (Arg.var second_pass)
                    (Expr.let_ (Op.mk (OpCode.sub i32) (Arg.var side_lim, Arg.imm 1, ()))
                      fun p535 =>
                    Expr.let_ (Op.mk (OpCode.sub i32)
                      (Arg.var p535.fst, Arg.var pb327.snd.snd.snd.snd.snd.fst, ())) fun p536 =>
                    Expr.jump Js_329.fst (Arg.var p536.fst, ()))
                    (Expr.jump Js_329.fst (Arg.var pb327.snd.snd.snd.snd.snd.fst, ()))))
              (Expr.jump Js_323.fst (Arg.var pb327.fst, Arg.var pb327.snd.fst,
                Arg.var pb327.snd.snd.fst, Arg.var pb327.snd.snd.snd.fst, Arg.var trivial_eid,
                Arg.var pb327.snd.snd.snd.snd.fst, Arg.var pb327.snd.snd.snd.snd.snd.fst, ())))
          Blocks.nil)
        fun Js_326 => Expr.jump Js_326.fst (Arg.var nv, Arg.var nc, Arg.var alen,
          Arg.var n_units, Arg.var abort, Arg.imm 0, ())) m := by
  apply wp_unroll_group
  intro Js_323 hJs_323
  have hJ323 : ∀ nv' nc' alen' nu' triv' ab' ei_out tmp' wsort' tmk' scr' m',
      nv'.toNat ≤ mv_s.toNat → nv'.toNat ≤ 2 * s.core.cur_vars →
      nc'.toNat ≤ 2 * mv_s.toNat → alen'.toNat ≤ acap.toNat → nu'.toNat ≤ nc'.toNat →
      (triv' ≠ 4294967295#32 → triv'.toNat < 4096 ∧ (triv' &&& 2047#32).toNat < 2001) →
      tmp'.length = c.max_vars → wsort'.length = 2 * c.max_vars →
      tmk'.length = 2 * c.max_vars → scr'.length = c.scratch_cap →
      FidK6cTmkReg nv'.toNat s.core.cur_vars wsort' tmk' →
      FidK6cClsOk mv_s.toNat nc'.toNat alen'.toNat nu'.toNat scr' →
      (∀ i, i < 4002 → scr'[i]? = s.scratch.scratch_buf[i]?) →
      (∀ i, 4132 ≤ i → i < 4192 → scr'[i]? = s.scratch.scratch_buf[i]?) →
      (FullMem c (FidP6Work s tmp' wsort' tmk' scr') ⋆ R) m' →
      Js_323 (nv', nc', alen', nu', triv', ab', ei_out, ()) m' := by
    intro nv' nc' alen' nu' triv' ab' ei_out tmp' wsort' tmk' scr' m'
      h1 h2 h3 h4 h5 htr htp' hws' htm' hs' hrg' hcl' hp0' hp1' hm'
    apply hJs_323; try dsimp only [Blocks.get, Member.here]
    c0_hsteps
    exact hOuter nv' nc' alen' nu' triv' ab' tmp' wsort' tmk' scr' m'
      h1 h2 h3 h4 h5 htr htp' hws' htm' hs' hrg' hcl' hp0' hp1' hm'
  clear hJs_323
  apply wp_loop_inv
    (Inv := fun (pb : Tup Val [i32, i32, i32, i32, Ty.bool, i32]) m1 =>
      ∃ tmp1 wsort1 tmk1 scr1,
      pb.2.2.2.2.2.1.toNat ≤ side_lim.toNat ∧
      pb.1.toNat ≤ mv_s.toNat ∧ pb.1.toNat ≤ 2 * s.core.cur_vars ∧
      pb.2.1.toNat ≤ 2 * mv_s.toNat ∧
      pb.2.2.1.toNat ≤ acap.toNat ∧ pb.2.2.2.1.toNat ≤ pb.2.1.toNat ∧
      tmp1.length = c.max_vars ∧ wsort1.length = 2 * c.max_vars ∧
      tmk1.length = 2 * c.max_vars ∧ scr1.length = c.scratch_cap ∧
      FidK6cTmkReg pb.1.toNat s.core.cur_vars wsort1 tmk1 ∧
      FidK6cClsOk mv_s.toNat pb.2.1.toNat pb.2.2.1.toNat pb.2.2.2.1.toNat scr1 ∧
      (∀ i, i < 4002 → scr1[i]? = s.scratch.scratch_buf[i]?) ∧
      (∀ i, 4132 ≤ i → i < 4192 → scr1[i]? = s.scratch.scratch_buf[i]?) ∧
      (FullMem c (FidP6Work s tmp1 wsort1 tmk1 scr1) ⋆ R) m1)
    (μ := fun (pb : Tup Val [i32, i32, i32, i32, Ty.bool, i32]) _ =>
      side_lim.toNat - pb.2.2.2.2.2.1.toNat)
  · intro J hJ; c0_hsteps
    exact hJ _ _ ⟨tmp, wsort, tmk, scr, Nat.zero_le _, hnv_le, hnv_cv, hnc_le, halen_le,
      hnu_le, htmp, hwsort, htmk, hscr, hreg, hcls, hp0, hp1, hm⟩
  · intro J pb m1 ⟨tmp1, wsort1, tmk1, scr1, hei_le, hnv1, hnvcv1, hnc1, hal1, hnu1,
        htp1, hws1, htm1, hs1, hr1, hc1, hp0_1, hp1_1, hm1⟩ hcont
    dsimp only [Blocks.get, Member.here]
    c0_hsteps_nogrp
    · exact hJ323 pb.fst pb.snd.fst pb.snd.snd.fst pb.snd.snd.snd.fst trivial_eid
        pb.snd.snd.snd.snd.fst pb.snd.snd.snd.snd.snd.fst tmp1 wsort1 tmk1 scr1 m1
        hnv1 hnvcv1 hnc1 hal1 hnu1 htriv_in htp1 hws1 htm1 hs1 hr1 hc1 hp0_1 hp1_1 hm1
    · have hei_lt : pb.snd.snd.snd.snd.snd.fst.toNat < side_lim.toNat := by bv_omega
      have hei1 : (pb.snd.snd.snd.snd.snd.fst + 1#32).toNat =
          pb.snd.snd.snd.snd.snd.fst.toNat + 1 := fid_k6c_add1_toNat hei_lt (by omega)
      apply wp_unroll_group
      intro Js_329 hJs_329
      have hJ329 : ∀ idx : BitVec 32, idx.toNat < side_lim.toNat →
          Js_329 (idx, ()) m1 := by
        intro idx hidx_lt
        apply hJs_329; try dsimp only [Blocks.get, Member.here]
        apply wp_unroll_group
        intro Js_332 hJs_332
        have hJ332 : Js_332 () m1 := by
          apply hJs_332; try dsimp only [Blocks.get, Member.here]
          have hm_off_val : m_off.toNat = if side = 0#32 then 0 else 2001 := by
            rcases hside with rfl | rfl
            · simp [hmoff.1 rfl]
            · simp [hmoff.2 rfl]
          have hm_le : m_off.toNat ≤ 2001 := by rw [hm_off_val]; split <;> omega
          have hm_off_lt : (BitVec.setWidth 64 (m_off + idx)).toNat < scr1.length := by
            have : (m_off + idx).toNat = m_off.toNat + idx.toNat := by
              rcases hside with rfl | rfl <;>
                (first | rw [hmoff.1 rfl] | rw [hmoff.2 rfl]) <;> bv_omega
            rw [fid_k6c_zext64, this]; omega
          c0_hsteps_nogrp
          have heid := fid_k6c_eid_bits hside (by omega : idx.toNat < 2001)
          have hmo_add : (BitVec.setWidth 64 (m_off + idx)).toNat =
              m_off.toNat + idx.toNat := by
            rw [fid_k6c_zext64]
            rcases hside with rfl | rfl <;>
                (first | rw [hmoff.1 rfl] | rw [hmoff.2 rfl]) <;> bv_omega
          have hent_idx : FullBveEntryOkW F_cur s lit_cur.toNat
              scr1[(BitVec.setWidth 64 (m_off + idx)).toNat] := by
            have hget := List.getElem?_eq_getElem hm_off_lt
            have hagr := hp0_1 (m_off.toNat + idx.toNat) (by omega)
            conv at hget => lhs; rw [hmo_add]
            simpa [← hagr, hget] using hent idx.toNat hidx_lt
          apply wp_unroll_group
          intro Js_341 hJs_341
          have hJ341 : ∀ nv' nc' alen' nu' triv' (ab' : Bool) tmp' wsort' tmk' scr' m',
              nv'.toNat ≤ mv_s.toNat → nv'.toNat ≤ 2 * s.core.cur_vars →
              nc'.toNat ≤ 2 * mv_s.toNat → alen'.toNat ≤ acap.toNat → nu'.toNat ≤ nc'.toNat →
              tmp'.length = c.max_vars → wsort'.length = 2 * c.max_vars →
              tmk'.length = 2 * c.max_vars → scr'.length = c.scratch_cap →
              FidK6cTmkReg nv'.toNat s.core.cur_vars wsort' tmk' →
              FidK6cClsOk mv_s.toNat nc'.toNat alen'.toNat nu'.toNat scr' →
              (∀ i, i < 4002 → scr'[i]? = s.scratch.scratch_buf[i]?) →
              (∀ i, 4132 ≤ i → i < 4192 → scr'[i]? = s.scratch.scratch_buf[i]?) →
              (FullMem c (FidP6Work s tmp' wsort' tmk' scr') ⋆ R) m' →
              Js_341 (nv', nc', alen', nu', triv', ab', ()) m' := by
            intro nv' nc' alen' nu' triv' ab' tmp' wsort' tmk' scr' m'
              h1 h2 h3 h4 h5 htp' hws' htm' hs' hrg' hcl' hp0' hp1' hm'
            apply hJs_341; try dsimp only [Blocks.get, Member.here]
            exact hcont (nv', nc', alen', nu', ab', pb.snd.snd.snd.snd.snd.fst + 1#32, ()) m'
              (by dsimp only; omega) ⟨tmp', wsort', tmk', scr', by dsimp only; omega,
                h1, h2, h3, h4, h5, htp', hws', htm', hs', hrg', hcl', hp0', hp1', hm'⟩
          clear hJs_341
          c0_hsteps_nogrp
          · exact fid_k6c_bin_entry_wp hinv hcap hmv_lo hmv_hi hmc_s hmax_orig_s
              hoff_off hoff_meta hoff_aux hoff_units hoff_arena hcap_ar htp1 hws1 htm1 hs1
              hnv1 hnvcv1 hnc1 hal1 hnu1 ⟨heid.1, by rw [heid.2.1]; omega⟩
              htriv_in hr1 hc1 hp0_1 hp1_1
              hent_idx hc hm1
              (fun nv' nc' alen' nu' triv' ab' ws' tm' sc' m'
                 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 am =>
                hJ323 nv' nc' alen' nu' triv' ab' (pb.snd.snd.snd.snd.snd.fst + 1#32)
                  tmp1 ws' tm' sc' m' a1 a2 a3 a4 a5 a6 htp1 a7 a8 a9 a10 a11 a12 a13 am)
              (fun nv' nc' alen' nu' ab' ws' tm' sc' m'
                 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 am =>
                hJ341 nv' nc' alen' nu' trivial_eid ab' tmp1 ws' tm' sc' m'
                  a1 a2 a3 a4 a5 htp1 a6 a7 a8 a9 a10 a11 a12 am)
          · exact fid_k6c_large_entry_wp hinv hcap hmv_lo hmv_hi hmc_s hmax_orig_s hmax_csz
              hoff_off hoff_meta hoff_aux hoff_units hoff_arena hcap_ar htp1 hws1 htm1 hs1
              hnv1 hnvcv1 hnc1 hal1 hnu1 ⟨heid.1, by rw [heid.2.1]; omega⟩
              htriv_in hr1 hc1 hp0_1 hp1_1
              hent_idx hc hm1
              (fun nv' nc' alen' nu' triv' ab' tp' ws' tm' sc' m'
                 a1 a2 a3 a4 a5 a6 atp a7 a8 a9 a10 a11 a12 a13 am =>
                hJ323 nv' nc' alen' nu' triv' ab' (pb.snd.snd.snd.snd.snd.fst + 1#32)
                  tp' ws' tm' sc' m' a1 a2 a3 a4 a5 a6 atp a7 a8 a9 a10 a11 a12 a13 am)
              (fun nv' nc' alen' nu' ab' tp' ws' tm' sc' m'
                 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 am =>
                hJ341 nv' nc' alen' nu' trivial_eid ab' tp' ws' tm' sc' m'
                  a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 am)
        clear hJs_332
        c0_hsteps_nogrp
        · have hmb_lt : (BitVec.setWidth 64 (m_base + (idx >>> 5))).toNat < scr1.length := by
            have hw := fid_k6c_mask_widx hmbase (by omega : idx.toNat < 2001)
            rw [hw.2.2]; simp only [BitVec.toNat_ofNat]; omega
          c0_hsteps_nogrp
          · exact hcont (pb.fst, pb.snd.fst, pb.snd.snd.fst, pb.snd.snd.snd.fst,
              pb.snd.snd.snd.snd.fst, pb.snd.snd.snd.snd.snd.fst + 1#32, ()) m1
              (by dsimp only; omega) ⟨tmp1, wsort1, tmk1, scr1, by dsimp only; omega,
                hnv1, hnvcv1, hnc1, hal1, hnu1, htp1, hws1, htm1, hs1, hr1, hc1, hp0_1, hp1_1,
                hm1⟩
          · exact hJ332
        · exact hJ332
      clear hJs_329
      c0_hsteps
      · exact hJ329 _ (by bv_omega)
      · exact hJ329 pb.snd.snd.snd.snd.snd.fst hei_lt
    · exact hJ323 pb.fst pb.snd.fst pb.snd.snd.fst pb.snd.snd.snd.fst trivial_eid
        pb.snd.snd.snd.snd.fst pb.snd.snd.snd.snd.snd.fst tmp1 wsort1 tmk1 scr1 m1
        hnv1 hnvcv1 hnc1 hal1 hnu1 htriv_in htp1 hws1 htm1 hs1 hr1 hc1 hp0_1 hp1_1 hm1

private theorem fid_k6c_acap_bounds {cap : Nat} {mv : BitVec 32}
    (hcap45 : 4224 + 45 * mv.toNat ≤ cap) (hlt : cap < 2 ^ 30) :
    (4224#32 + 45#32 * mv).toNat = 4224 + 45 * mv.toNat ∧
    (BitVec.setWidth 32 (BitVec.ofNat 64 cap -
      BitVec.setWidth 64 (4224#32 + 45#32 * mv))).toNat = cap - (4224 + 45 * mv.toNat) := by
  have h45 : (4224#32 + 45#32 * mv).toNat = 4224 + 45 * mv.toNat := by bv_omega
  exact ⟨h45, by bv_omega⟩

/-- Specification theorem for `full_k6_extract_and_solve_fid_body`. -/
theorem full_k6_extract_and_solve_fid_wp (Γ : Env)
    (hMv : ∀ a m Q X, fidBveK6MvSpec a m Q X →
      Γ "full_bve_k6_mv_fid" [i64] [i64] a m Q X)
    (hwatch : ∀ a m Q X, fidK6WatchSpec a m Q X →
      Γ "full_k6_watch_fid" [i64, i32, i32, i32, i32] [] a m Q X)
    (hsolve : ∀ a m Q X, fidK6SolveSpec a m Q X →
      Γ "full_k6_solve_fid" [i64, i32] [i64] a m Q X)
    (hcore : ∀ a m Q X, fidK6CoreSpec a m Q X →
      Γ "full_k6_core_fid" [i64] [] a m Q X) :
    ∀ a m Q X, fidK6ExtractSolveSpec a m Q X →
      Func.wp Γ full_k6_extract_and_solve_fid_body a m Q X := by
  intro a m Q X hspec
  rcases fidK6ExtractSolveSpec_elim hspec with
    ⟨c, F0, F_cur, s, R, ha_hdr, hinv, htmk, hcap, hv, hnp, hnn, hent_p, hent_n, hm, hQ⟩
  dsimp only [Func.wp, full_k6_extract_and_solve_fid_body]
  rw [ha_hdr]
  c0_hsteps_nogrp
  fid_call hMv
  · dsimp only [fidBveK6MvSpec]
    have hmv_b := fid_k6c_maxV_bounds hcap
    have hscr_lt : c.scratch_cap < 2 ^ 30 := by
      have := c.hscr; simp only [Examples.LratBytes.dimacsBound] at this; omega
    have hmv_eq : (BitVec.setWidth 32 (BitVec.ofNat 64 (fidK6MaxV c.scratch_cap))).toNat =
        fidK6MaxV c.scratch_cap := by
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
    c0_hsteps_nogrp
    · have : (BitVec.setWidth 32 (BitVec.ofNat 64 (fidK6MaxV c.scratch_cap))) = 0#32 := by
        simpa [Nat.mod_eq_of_lt (by omega : c.scratch_cap < 2 ^ 64)] using hc
      have hz := congrArg BitVec.toNat this
      rw [hmv_eq] at hz; simp at hz; omega
    · let mv_s : BitVec 32 := BitVec.setWidth 32 (BitVec.ofNat 64 (fidK6MaxV
        (BitVec.toNat (vals (ts := [i64]) (Arg.var (BitVec.ofNat 64 c.scratch_cap), ())).fst)))
      have hmv_unmod : mv_s =
          BitVec.setWidth 32 (BitVec.ofNat 64 (fidK6MaxV c.scratch_cap)) := by
        dsimp only [mv_s]
        rw [show (vals (ts := [i64]) (Arg.var (BitVec.ofNat 64 c.scratch_cap), ())).fst =
            BitVec.ofNat 64 c.scratch_cap from rfl,
          BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : c.scratch_cap < 2 ^ 64)]
      have hmv_lo : 256 ≤ mv_s.toNat := by rw [hmv_unmod, hmv_eq]; exact hmv_b.1
      have hmv_hi : mv_s.toNat ≤ 8192 := by rw [hmv_unmod, hmv_eq]; exact hmv_b.2.1
      have hcap45 : 4224 + 45 * mv_s.toNat ≤ c.scratch_cap := by
        rw [hmv_unmod, hmv_eq]; exact hmv_b.2.2
      c0_hsteps_nogrp
      apply wp_unroll_group
      intro Js_47 hJs_47
      have hJ47 : ∀ max_csz : BitVec 32,
          max_csz.toNat ≤ c.max_vars ∧ max_csz.toNat ≤ 65535 → Js_47 (max_csz, ()) m := by
        intro max_csz hmax_csz
        apply hJs_47; try dsimp only [Blocks.get, Member.here]
        have hcv_mv : s.core.cur_vars ≤ c.max_vars := hinv.1.core_ok.cur_vars_le
        have hv2_lt : (a.snd.fst <<< 1).toNat = 2 * a.snd.fst.toNat ∧
            (a.snd.fst <<< 1 ||| 1#32).toNat = 2 * a.snd.fst.toNat + 1 :=
          fid_k6c_bv32_shl1_add1_lt hv (by
            have := c.hmaxv; simp only [Examples.LratBytes.dimacsBound] at this; omega)
        have hlt_cv : 2 * s.core.cur_vars < 2 ^ 30 := by
          have := c.hmaxv; simp only [Examples.LratBytes.dimacsBound] at this; omega
        c0_hsteps_nogrp
        apply wp_loop_inv
          (Inv := fun (p : Tup Val [i32, i32, i32, i32, i32, Ty.bool, i32]) m1 =>
            ∃ tmp1 wsort1 tmk1 scr1,
            p.2.2.2.2.2.2.1.toNat ≤ 2 ∧
            p.1.toNat ≤ mv_s.toNat ∧ p.1.toNat ≤ 2 * s.core.cur_vars ∧
            p.2.1.toNat ≤ 2 * mv_s.toNat ∧ p.2.2.1.toNat ≤
              (BitVec.setWidth 32 (BitVec.ofNat 64 c.scratch_cap -
                BitVec.setWidth 64 (4224#32 + 45#32 * mv_s))).toNat ∧
            p.2.2.2.1.toNat ≤ p.2.1.toNat ∧
            (p.2.2.2.2.1 ≠ 4294967295#32 →
              p.2.2.2.2.1.toNat < 4096 ∧ (p.2.2.2.2.1 &&& 2047#32).toNat < 2001) ∧
            tmp1.length = c.max_vars ∧ wsort1.length = 2 * c.max_vars ∧
            tmk1.length = 2 * c.max_vars ∧ scr1.length = c.scratch_cap ∧
            FidK6cTmkReg p.1.toNat s.core.cur_vars wsort1 tmk1 ∧
            FidK6cClsOk mv_s.toNat p.2.1.toNat p.2.2.1.toNat p.2.2.2.1.toNat scr1 ∧
            (∀ i, i < 4002 → scr1[i]? = s.scratch.scratch_buf[i]?) ∧
            (∀ i, 4132 ≤ i → i < 4192 → scr1[i]? = s.scratch.scratch_buf[i]?) ∧
            (FullMem c (FidP6Work s tmp1 wsort1 tmk1 scr1) ⋆ R) m1)
          (μ := fun (p : Tup Val [i32, i32, i32, i32, i32, Ty.bool, i32]) _ =>
            2 - p.2.2.2.2.2.2.1.toNat)
        · intro J hJ; c0_hsteps
          exact hJ _ _ ⟨s.core.tmp, s.scratch.wsort, s.scratch.tarjan_mark,
            s.scratch.scratch_buf, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, Nat.zero_le _,
            Nat.zero_le _, Nat.zero_le _, fun h => absurd rfl h,
            hinv.1.core_ok.tmp_len_arr, hinv.1.scratch_ok.wsort_len,
            hinv.1.scratch_ok.tarjan_mark_len, hinv.1.scratch_ok.scratch_buf_len,
            fid_k6c_tmkReg_init s.core.cur_vars s.scratch.wsort s.scratch.tarjan_mark htmk,
            fid_k6c_clsOk_empty mv_s.toNat s.scratch.scratch_buf,
            fun _ _ => rfl, fun _ _ _ => rfl, by simpa [FidP6Work] using hm⟩
        · intro J p m1 ⟨tmp1, wsort1, tmk1, scr1, hstep_le, hnv, hnvcv, hnc, hal, hnu,
              htriv, htp1, hws1, htm1, hs1, hrg1, hcl1, hp0_1, hp1_1, hm1⟩ hcont
          try dsimp only [Blocks.get, Member.here]
          let acap : BitVec 32 := BitVec.setWidth 32 (BitVec.ofNat 64 c.scratch_cap -
            BitVec.setWidth 64 (4224#32 + 45#32 * mv_s))
          have hacap_eq : acap.toNat = c.scratch_cap - (4224 + 45 * mv_s.toNat) :=
            (fid_k6c_acap_bounds hcap45 hscr_lt).2
          have hcap_ar : 4224 + 45 * mv_s.toNat + acap.toNat ≤ c.scratch_cap := by omega
          apply wp_unroll_group
          intro Js_53 hJs_53
          have hJ53 : Js_53 () m1 := by
            apply hJs_53; try dsimp only [Blocks.get, Member.here]
            exact fid_k6c_post_extract_wp hwatch hsolve hcore hinv hcap hmv_lo hmv_hi rfl rfl
              rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl hcap_ar
              htp1 hws1 htm1 hs1 hnv hnc hal hnu htriv hrg1 hcl1 hp0_1 hp1_1 hm1 hQ
          clear hJs_53
          c0_hsplit
          · c0_hsplit
            · exact hJ53
            · c0_hsplit
              · have hstep_lt : p.snd.snd.snd.snd.snd.snd.fst.toNat < 2 := by assumption
                c0_hsteps_nogrp
                apply wp_unroll_group
                intro Js_313 hJs_313
                have hJ313 : ∀ start_side : BitVec 32,
                    (start_side = 0#32 ∨ start_side = 1#32) → Js_313 (start_side, ()) m1 := by
                  intro start_side hss
                  apply hJs_313; try dsimp only [Blocks.get, Member.here]
                  apply wp_unroll_group
                  intro Js_315 hJs_315
                  have hJ315 : ∀ side_lim : BitVec 32,
                      side_lim.toNat ≤ 2001 →
                      (start_side = 0#32 → side_lim = a.snd.snd.fst) →
                      (start_side = 1#32 → side_lim = a.snd.snd.snd.fst) →
                      Js_315 (side_lim, ()) m1 := by
                    intro side_lim hsl hsl0 hsl1
                    apply hJs_315; try dsimp only [Blocks.get, Member.here]
                    apply wp_unroll_group
                    intro Js_317 hJs_317
                    have hJ317 : ∀ m_off : BitVec 32,
                        (start_side = 0#32 → m_off = 0#32) →
                        (start_side = 1#32 → m_off = 2001#32) → Js_317 (m_off, ()) m1 := by
                      intro m_off hmo0 hmo1
                      apply hJs_317; try dsimp only [Blocks.get, Member.here]
                      apply wp_unroll_group
                      intro Js_319 hJs_319
                      have hJ319 : ∀ m_base : BitVec 32,
                          m_base = 4002#32 ∨ m_base = 4066#32 → Js_319 (m_base, ()) m1 := by
                        intro m_base hmb
                        apply hJs_319; try dsimp only [Blocks.get, Member.here]
                        apply wp_unroll_group
                        intro Js_321 hJs_321
                        have hJ321 : ∀ lit_cur : BitVec 32,
                            lit_cur.toNat < 2 * s.core.cur_vars →
                            (∀ idx : Nat, idx < side_lim.toNat →
                              FullBveEntryOkW F_cur s lit_cur.toNat
                                (s.scratch.scratch_buf[m_off.toNat + idx]?.getD 0#32)) →
                            Js_321 (lit_cur, ()) m1 := by
                          intro lit_cur hlcur hent_l
                          apply hJs_321; simp only [Blocks.get]
                          have hacap_def : acap = BitVec.setWidth 32
                              (BitVec.ofNat 64 c.scratch_cap -
                                BitVec.setWidth 64 (4224#32 + 45#32 * mv_s)) := rfl
                          generalize hmv_g : BitVec.setWidth 32 (BitVec.ofNat 64 (fidK6MaxV
                            (BitVec.toNat (vals (ts := [i64]) (Arg.var
                              (BitVec.ofNat 64 c.scratch_cap), ())).fst))) = mv_g
                          have hmv_eq_g : mv_s = mv_g := hmv_g
                          generalize hacap_g : BitVec.setWidth 32
                            (BitVec.ofNat 64 c.scratch_cap -
                              BitVec.setWidth 64 (4224#32 + 45#32 * mv_g)) = acap_g
                          have hacap_eq_g : acap = acap_g := by
                            rw [hacap_def, hmv_eq_g, hacap_g]
                          clear_value mv_s acap
                          have hmv_lo_g : 256 ≤ mv_g.toNat := hmv_eq_g ▸ hmv_lo
                          have hmv_hi_g : mv_g.toNat ≤ 8192 := hmv_eq_g ▸ hmv_hi
                          have hcap_ar_g : 4224 + 45 * mv_g.toNat + acap_g.toNat ≤ c.scratch_cap :=
                            hmv_eq_g ▸ hacap_eq_g ▸ hcap_ar
                          have hnv_g : p.fst.toNat ≤ mv_g.toNat := hmv_eq_g ▸ hnv
                          have hnc_g : p.snd.fst.toNat ≤ 2 * mv_g.toNat := hmv_eq_g ▸ hnc
                          have hal_g : p.snd.snd.fst.toNat ≤ acap_g.toNat := by
                            rw [← hacap_eq_g, hacap_def]; exact hal
                          have hcl1_g : FidK6cClsOk mv_g.toNat p.snd.fst.toNat
                              p.snd.snd.fst.toNat p.snd.snd.snd.fst.toNat scr1 := hmv_eq_g ▸ hcl1
                          have hside := fid_k6c_extract_side_wp (Γ := Γ) (Q := Q) (X := X)
                            (Js_outer := J) (mv_s := mv_g) (mc_s := mv_g <<< 2)
                            (max_orig_s := mv_g <<< 1) (acap := acap_g)
                            (o_cl_off := 4224 + 29 * mv_g) (o_cl_meta := 4224 + 33 * mv_g)
                            (o_cl_aux := 4224 + 37 * mv_g) (o_units := 4224 + 41 * mv_g)
                            (o_arena := 4224 + 45 * mv_g)
                            (second_pass := a.snd.snd.snd.snd.fst)
                            (abort := p.snd.snd.snd.snd.snd.fst)
                            hinv hcap hmv_lo_g hmv_hi_g rfl rfl
                            hmax_csz rfl rfl rfl rfl rfl hcap_ar_g hss hsl ⟨hmo0, hmo1⟩ hmb
                            hlcur hent_l htp1 hws1 htm1 hs1 hnv_g hnvcv hnc_g hal_g hnu hstep_lt
                            htriv hrg1 hcl1_g hp0_1 hp1_1 hm1
                            (fun nv' nc' alen' nu' triv' ab' tp' ws' tm' sc' m'
                                a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 am => by
                              have hst1 : (p.snd.snd.snd.snd.snd.snd.fst + 1#32).toNat =
                                  p.snd.snd.snd.snd.snd.snd.fst.toNat + 1 :=
                                fid_k6c_add1_toNat hstep_lt (by omega)
                              have ha4 : alen'.toNat ≤ (BitVec.setWidth 32
                                  (BitVec.ofNat 64 c.scratch_cap -
                                    BitVec.setWidth 64 (4224#32 + 45#32 * mv_s))).toNat := by
                                rw [← hacap_def, hacap_eq_g]; exact a4
                              exact hcont (nv', nc', alen', nu', triv', ab',
                                  p.snd.snd.snd.snd.snd.snd.fst + 1#32, ()) m'
                                (by dsimp only; rw [hst1]; omega)
                                ⟨tp', ws', tm', sc', by dsimp only; rw [hst1]; omega,
                                  hmv_eq_g ▸ a1, a2, hmv_eq_g ▸ a3, ha4, a5, a6, a7, a8, a9,
                                  a10, a11, hmv_eq_g ▸ a12, a13, a14, am⟩)
                          dsimp only [fidBinEntryExpr, fidLargeEntryExpr] at hside
                          with_reducible exact hside
                        clear hJs_321
                        c0_hfast
                        · have hsp0 : start_side = 0#32 := by simpa using hc
                          have hlim0 : side_lim = a.snd.snd.fst := hsl0 hsp0
                          have hm0 : m_off = 0#32 := hmo0 hsp0
                          refine hJ321 (a.snd.fst <<< 1) (by
                              rw [hv2_lt.1]
                              exact (Nat.mul_lt_mul_of_pos_left hv (by decide) :
                                2 * a.snd.fst.toNat < 2 * s.core.cur_vars))
                            (fun idx hidx => ?_)
                          rw [hm0]; simp only [BitVec.toNat_ofNat]
                          rw [hlim0] at hidx
                          simpa [hv2_lt.1] using hent_p idx hidx
                        · have hsp1 : start_side = 1#32 := by
                            rcases hss with h | h
                            · exact absurd h (by simpa using hc)
                            · exact h
                          have hlim1 : side_lim = a.snd.snd.snd.fst := hsl1 hsp1
                          have hm1' : m_off = 2001#32 := hmo1 hsp1
                          refine hJ321 (a.snd.fst <<< 1 ||| 1#32) (by
                              rw [hv2_lt.2]
                              have h2 : 2 * a.snd.fst.toNat < 2 * s.core.cur_vars :=
                                Nat.mul_lt_mul_of_pos_left hv (by decide)
                              omega)
                            (fun idx hidx => ?_)
                          rw [hm1']; simp only [BitVec.toNat_ofNat]
                          rw [hlim1] at hidx
                          simpa [hv2_lt.2] using hent_n idx hidx
                      clear hJs_319
                      c0_hfast
                      · exact hJ319 4002#32 (Or.inl rfl)
                      · exact hJ319 4066#32 (Or.inr rfl)
                    clear hJs_317
                    c0_hfast
                    · exact hJ317 0#32 (fun _ => rfl) (fun h => by
                        have h0 : start_side = 0#32 := by simpa using hc
                        exact absurd (h0.symm.trans h) (by decide))
                    · exact hJ317 2001#32 (fun h => absurd h (by simpa using hc)) (fun _ => rfl)
                  clear hJs_315
                  c0_hfast
                  · exact hJ315 a.snd.snd.fst hnp (fun _ => rfl) (fun h => by
                      have h0 : start_side = 0#32 := by simpa using hc
                      exact absurd (h0.symm.trans h) (by decide))
                  · exact hJ315 a.snd.snd.snd.fst hnn
                      (fun h => absurd h (by simpa using hc)) (fun _ => rfl)
                clear hJs_313
                c0_hfast
                · exact hJ313 (1#32 - p.snd.snd.snd.snd.snd.snd.fst) (by
                    have hlt2 : p.snd.snd.snd.snd.snd.snd.fst.toNat = 0 ∨
                        p.snd.snd.snd.snd.snd.snd.fst.toNat = 1 := by omega
                    rcases hlt2 with h0 | h1
                    · have hp0 : p.snd.snd.snd.snd.snd.snd.fst = 0#32 :=
                        BitVec.eq_of_toNat_eq (by simpa using h0)
                      rw [hp0]; exact Or.inr (by decide)
                    · have hp1 : p.snd.snd.snd.snd.snd.snd.fst = 1#32 :=
                        BitVec.eq_of_toNat_eq (by simpa using h1)
                      rw [hp1]; exact Or.inl (by decide))
                · exact hJ313 p.snd.snd.snd.snd.snd.snd.fst (by
                    have hlt2 : p.snd.snd.snd.snd.snd.snd.fst.toNat = 0 ∨
                        p.snd.snd.snd.snd.snd.snd.fst.toNat = 1 := by omega
                    rcases hlt2 with h0 | h1
                    · exact Or.inl (BitVec.eq_of_toNat_eq (by simpa using h0))
                    · exact Or.inr (BitVec.eq_of_toNat_eq (by simpa using h1)))
              · exact hJ53
          · exact hJ53
      clear hJs_47
      c0_hfast
      · have hmv_lt : c.max_vars < 65535 := by
          have : (BitVec.ofNat 64 c.max_vars).toNat < 65535 := by simpa using hc
          have hcm : c.max_vars < 2 ^ 64 := by
            have := c.hmaxv; simp only [Examples.LratBytes.dimacsBound] at this; omega
          rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcm] at this
        refine hJ47 (BitVec.truncate 32 (BitVec.ofNat 64 c.max_vars)) ⟨?_, ?_⟩
        · simp [BitVec.toNat_ofNat]; omega
        · simp [BitVec.toNat_ofNat]; omega
      · refine hJ47 65535#32 ⟨?_, by decide⟩
        have hcm_ge : 65535 ≤ c.max_vars := by
          have hcm : c.max_vars < 2 ^ 64 := by
            have := c.hmaxv; simp only [Examples.LratBytes.dimacsBound] at this; omega
          exact Classical.byContradiction fun hlt =>
            hc (by simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcm] using Nat.not_le.mp hlt)
        exact hcm_ge

end LeanQbe.T.Examples.Kissat.FullFidelityBve
