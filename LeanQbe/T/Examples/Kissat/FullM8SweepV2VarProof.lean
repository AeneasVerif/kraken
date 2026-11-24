/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanQbe Contributors
-/
module

public import LeanQbe.T.Examples.Kissat.FullM8SweepV2ConeProof
public import LeanQbe.T.Examples.Kissat.FullM8SweepV2KittenProof
public import LeanQbe.T.Examples.Kissat.FullM6SweepProofVar1a
public import LeanQbe.T.Examples.Kissat.FullM6SweepProofCands
public import LeanQbe.T.Examples.Kissat.FullM4SweepProof
public import LeanQbe.T.Examples.Kissat.FullDefSweepLemmas1

/-!
# Kissat M8 Sweep V2 — Phase/Flip/Sim/Cands/Vars/Driver (`V3t2`) `Func.wp` Proofs (`6/10`)

Purely additive parametric `(Γ : Env)` `Func.wp` proofs for the remaining 6 modified functions
in `FullM8SweepV2`:
1. `m8_sweep_rand_phases_wp : m6SweepRandPhasesSpec` (`k[25]` isolated xorshift32 PRNG)
2. `m8_sweep_flip_round_wp : m6SweepFlipRoundSpec` (`k[25]` isolated xorshift32 PRNG)
3. `m8_sweep_sim_wp : m6SweepSimSpec` (`2` sim rounds, single flip pass)
4. `m8_collect_cands_wp : m6CollectCandsSpec` (`0 < deg <= 1024` gate, `fl[]` read-only)
5. `m8_sweep_vars_wp : m6SweepVarsSpec` (`per_v = 16384`, `spent = (ticks << 2) + 512`)
6. `m8_sweep_dense_m6_wp : FullM4Sweep.m4SweepDenseSpec` (single-pass outer driver)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM8SweepV2

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full LeanQbe.T.Examples.Kissat.FullM4Sweep
open LeanQbe.T.Examples.Kissat.FullM6Sweep
open Kraken.Bedrock2.Test
open FullArenaTactics K6MemATactics K6PtrTactics
open scoped FullArenaTactics M6SweepTactics K6MemATactics K6PtrTactics

local elab "c0_hfast" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 10000

/-! ## 1. Shared Arithmetic, Memory & Call Helpers -/

private theorem bv32_zext_mul4_eq (idx : BitVec 32) :
    idx.setWidth 64 * 4 = BitVec.ofNat 64 (4 * idx.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have hlt : idx.toNat < 2 ^ 32 := idx.isLt
  simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have h4 : (4 : BitVec 64).toNat = 4 := rfl
  rw [h4, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mul_comm]

private theorem bv32_add1_toNat {x : BitVec 32} (hx : x.toNat + 1 < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 := by bv_omega

private theorem bv32_lshr1_toNat (x : BitVec 32) :
    (x >>> (1 : Nat)).toNat = x.toNat / 2 := by bv_omega

private theorem bv64_add1_toNat {x : BitVec 64} (hx : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by bv_omega

private theorem bv64_shl1_toNat {v : BitVec 64} (hv : v.toNat < 2 ^ 31) :
    (v <<< (1 : Nat)).toNat = 2 * v.toNat := by
  simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [Nat.mul_comm, Nat.mod_eq_of_lt (by omega)]

private theorem nat_two_mul_lor_one (n : Nat) : 2 * n ||| 1 = 2 * n + 1 := by
  apply Nat.eq_of_testBit_eq
  intro k
  cases k with
  | zero => simp [Nat.testBit_zero]
  | succ k =>
    rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
    rw [show 1 / 2 = 0 from rfl, show (2 * n) / 2 = n from by omega,
      show (2 * n + 1) / 2 = n from by omega, Nat.zero_testBit, Bool.or_false]

private theorem bv64_wvec_pos_toNat {v : BitVec 64} (hv : v.toNat < 2 ^ 31) :
    (((v <<< (1 : Nat)) <<< (1 : Nat)) + 1#64).toNat = 4 * v.toNat + 1 := by
  have h0 := bv64_shl1_toNat hv
  have h1 : ((v <<< (1 : Nat)) <<< (1 : Nat)).toNat = 4 * v.toNat := by
    simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, h0]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  rw [BitVec.toNat_add, h1, show (1#64 : BitVec 64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega)]

private theorem bv64_wvec_neg_toNat {v : BitVec 64} (hv : v.toNat < 2 ^ 31) :
    ((((v <<< (1 : Nat)) ||| 1#64) <<< (1 : Nat)) + 1#64).toNat = 4 * v.toNat + 3 := by
  have h0 := bv64_shl1_toNat hv
  have hor : ((v <<< (1 : Nat)) ||| 1#64).toNat = 2 * v.toNat + 1 := by
    rw [BitVec.toNat_or, h0, show (1#64 : BitVec 64).toNat = 1 from rfl]
    exact nat_two_mul_lor_one v.toNat
  have h1 : (((v <<< (1 : Nat)) ||| 1#64) <<< (1 : Nat)).toNat = 4 * v.toNat + 2 := by
    simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hor]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  rw [BitVec.toNat_add, h1, show (1#64 : BitVec 64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega)]

private theorem bv64_shl_bv1_toNat {v : BitVec 64} (hv : v.toNat < 2 ^ 31) :
    (v <<< (1 : BitVec 64)).toNat = 2 * v.toNat := by
  exact bv64_shl1_toNat hv

private theorem bv64_wvec_pos_bv_toNat {v : BitVec 64} (hv : v.toNat < 2 ^ 31) :
    (((v <<< (1 : BitVec 64)) <<< (1 : BitVec 64)) + (1 : BitVec 64)).toNat =
      4 * v.toNat + 1 := by
  exact bv64_wvec_pos_toNat hv

private theorem bv64_wvec_neg_bv_toNat {v : BitVec 64} (hv : v.toNat < 2 ^ 31) :
    ((((v <<< (1 : BitVec 64)) ||| (1 : BitVec 64)) <<< (1 : BitVec 64)) + (1 : BitVec 64)).toNat =
      4 * v.toNat + 3 := by
  exact bv64_wvec_neg_toNat hv

private theorem k6MaxV_lt_2p32 (cap : Nat) : k6MaxV cap < 2 ^ 32 := by
  by_cases hcap : k6MinScr ≤ cap
  · have := (k6MaxV_bounds hcap).2.1; omega
  · rw [k6MaxV_eq_zero (Nat.lt_of_not_le hcap)]; omega

private theorem k6_mv32_zext (L : K6Layout) :
    BitVec.setWidth 32 (BitVec.ofNat 64 L.maxV) = L.mv32 := by
  have hm := L.hmaxV
  apply BitVec.eq_of_toNat_eq
  unfold K6Layout.mv32
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

private theorem maxVars_lt_2p31 (c : FullCfg) : c.max_vars < 2 ^ 31 := by
  have hm := c.hmaxv; unfold dimacsBound at hm; omega

private theorem m8_tmk_step {tmk : List (BitVec 32)} {i : Nat}
    (hlt : i < tmk.length)
    (hprev : ∀ v < i, tmk[v]?.getD 0#32 = 0#32) :
    (tmk.set i 0#32).length = tmk.length ∧
      ∀ v < i + 1, (tmk.set i 0#32)[v]?.getD 0#32 = 0#32 := by
  refine ⟨List.length_set, fun v hv => ?_⟩
  by_cases hvi : v = i
  · subst hvi
    rw [List.getElem?_set_self hlt, Option.getD_some]
  · rw [List.getElem?_set_ne (Ne.symm hvi)]
    exact hprev v (by omega)

namespace M8VarMemTactics

attribute [scoped bv_c0 high] bv_c0_zext32_64

@[scoped bv_c0 high] theorem bv_ofNat64_zero_toNat : (BitVec.ofNat 64 0).toNat = 0 := rfl

@[scoped bv_c0 high] theorem bv_zext32_11_mul4 :
    (BitVec.setWidth 64 (11#32 : BitVec 32)) * 4 = 44#64 := rfl

@[scoped bv_c0 high] theorem bv_ofNat64_11_mul4 :
    BitVec.ofNat 64 11 * 4 = 44#64 := rfl

@[scoped bv_c0 high] theorem bv_zext32_25_mul4 :
    (BitVec.setWidth 64 (25#32 : BitVec 32)) * 4 = BitVec.ofNat 64 25 * 4 := rfl

@[scoped bv_c0 high] theorem bv_ofNat64_25_mul4 :
    BitVec.ofNat 64 25 * 4 = BitVec.ofNat 64 25 * 4 := rfl

@[scoped bv_c0] theorem bv_zext32_mul4 (idx : BitVec 32) :
    idx.setWidth 64 * 4 = BitVec.ofNat 64 (4 * idx.toNat) :=
  bv32_zext_mul4_eq idx

@[scoped c0_load] theorem load_array_i32_ofNat {base : BitVec 64} {xs : List (BitVec 32)}
    {i : Nat} {R : Mem 64 → Prop} {m : Mem 64} (hi : i < xs.length)
    (hm : (array (t := i32) base xs ⋆ R) m) :
    loadVal m i32 (base + BitVec.ofNat 64 (4 * i)) = some xs[i] :=
  loadVal_array (t := i32) (by decide) hi hm

@[scoped c0_load] theorem load_array_i32_zero {base : BitVec 64} {xs : List (BitVec 32)}
    {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < xs.length)
    (hm : (array (t := i32) base xs ⋆ R) m) :
    loadVal m i32 base = some xs[0] := by
  have h := loadVal_array (t := i32) (a := base) (i := 0) (by decide) hi hm
  simpa using h

@[scoped c0_store] theorem store_array_i32_ofNat {base : BitVec 64} {xs : List (BitVec 32)}
    {i : Nat} (v : BitVec 32) {R : Mem 64 → Prop} {m : Mem 64} (hi : i < xs.length)
    (hm : (array (t := i32) base xs ⋆ R) m) :
    storeOk m i32 (base + BitVec.ofNat 64 (4 * i)) ∧
      (array (t := i32) base (xs.set i v) ⋆ R)
        (storeMem m i32 (base + BitVec.ofNat 64 (4 * i)) v) :=
  store_array (t := i32) v (by decide) hi hm

@[scoped c0_store] theorem store_array_i32_zero {base : BitVec 64} {xs : List (BitVec 32)}
    (v : BitVec 32) {R : Mem 64 → Prop} {m : Mem 64} (hi : 0 < xs.length)
    (hm : (array (t := i32) base xs ⋆ R) m) :
    storeOk m i32 base ∧
      (array (t := i32) base (xs.set 0 v) ⋆ R) (storeMem m i32 base v) := by
  have h := store_array (t := i32) v (a := base) (i := 0) (by decide) hi hm
  simpa using h

@[scoped c0_load] theorem load_k6_ticks {c : FullCfg} {L : K6Layout} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} (hL : L.scrLen = c.scratch_cap)
    (hscr : s.scratch.scratch_buf.length = c.scratch_cap)
    (hm : (FullMem c s ⋆ R) m) :
    loadVal m i32 (L.kPtr c.pScratchBuf + 44#64) =
      some (s.scratch.scratch_buf[L.k6Base + 11]'(by
        have := L.hmaxV; have := L.hacap
        rw [hscr, ← hL]; unfold K6Layout.scrLen K6Layout.k6Fixed; omega)) := by
  have hptr : L.kPtr c.pScratchBuf + 44#64 =
      c.pScratchBuf + BitVec.ofNat 64 (4 * (L.k6Base + 11)) := by
    have := L.hmaxV
    rw [K6Layout.kPtr, show (44#64 : BitVec 64) = BitVec.ofNat 64 (4 * 11) from rfl,
      BitVec.add_assoc, ← BitVec.ofNat_add]
    congr 2
  rw [hptr]; exact load_full_scratch_buf _ hm

end M8VarMemTactics

open scoped M8VarMemTactics

private theorem m8_call_max_v_cap {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    {cap : BitVec 64} {m : Mem 64} {k : Tup Val [i64] → Expr Val Cont rs}
    (hk : wp Γ Q X (k (BitVec.ofNat 64 (k6MaxV cap.toNat), ())) m) :
    wp Γ Q X (Expr.call (as := [i64]) (bs := [i64]) "full_m6_max_v" (Arg.var cap, ()) k) m :=
  wp_call_of_spec _ k (hMaxV (cap, ()) m (fun r m' => wp Γ Q X (k r) m') X hk)

private theorem m8_call_dense_prop {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hDP : M6EnvSpec Γ "full_m6_dense_prop" m6DensePropSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {k : Tup Val [.bool] → Expr Val Cont rs}
    (hdw : FullDenseInvW c F0 F_cur s) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ (ok : Bool) (s' : FullState) (m' : Mem 64),
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel = s.core.fuel → s'.scratch.tarjan_mark = s.scratch.tarjan_mark →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      (ok = true ↔ s'.core.inconsistent = 0#64) →
      (ok = false → F0.Unsat ∧ s'.core.inconsistent ≠ 0#64) →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k (ok, ())) m') :
    wp Γ Q X
      (Expr.call (as := [i64]) (bs := [.bool]) "full_m6_dense_prop" (Arg.var c.hdr, ()) k) m := by
  refine wp_call_of_spec _ k ?_
  refine hDP (c.hdr, ()) m (fun r m' => wp Γ Q X (k r) m') X
    ⟨c, F0, F_cur, s, R, rfl, hdw, hm,
      fun ok s' m' hdw' hcv hfl _ _ _ htmk htrc _ _ _ hok hno hm' =>
        hk ok s' m' hdw' hcv hfl htmk htrc hok hno hm'⟩

private theorem m8_call_collect_cands {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hCol : M6EnvSpec Γ "full_m6_collect_cands" m6CollectCandsSpec)
    {c : FullCfg} {s : FullState} {R : Mem 64 → Prop} {m : Mem 64}
    {k : Tup Val [i32] → Expr Val Cont rs}
    (hlen : s.LengthsOk c) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ nc trc' ws2' m',
      let s' : FullState :=
        { s with scratch := { s.scratch with tarjan_reach := trc', work_stk2 := ws2' } }
      s'.LengthsOk c → nc.toNat ≤ s.core.cur_vars →
      (∀ i < nc.toNat, (trc'[i]?.getD 0#32).toNat < s.core.cur_vars) →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k (nc, ())) m') :
    wp Γ Q X
      (Expr.call (as := [i64]) (bs := [i32]) "full_m6_collect_cands" (Arg.var c.hdr, ()) k) m :=
  wp_call_of_spec _ k
    (hCol (c.hdr, ()) m (fun r m' => wp Γ Q X (k r) m') X ⟨c, s, R, rfl, hlen, hm, hk⟩)

private theorem m8_call_sweep_var {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hSV : M6EnvSpec Γ "full_m6_sweep_var" m6SweepVarSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {R : Mem 64 → Prop} {m : Mem 64} {rv : BitVec 32} {tlim : BitVec 64}
    {k : Tup Val [i64] → Expr Val Cont rs}
    (hdw : FullDenseInvW c F0 F_cur s) (hcap : k6MinScr ≤ c.scratch_cap)
    (hrv : rv.toNat < s.core.cur_vars) (htmk : M6TmkZero s) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ r s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → M6TmkZero s' →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X
      (Expr.call (as := [i64, i32, i64]) (bs := [i64]) "full_m6_sweep_var"
        (Arg.var c.hdr, Arg.var rv, Arg.var tlim, ()) k) m :=
  wp_call_of_spec _ k
    (hSV (c.hdr, rv, tlim, ()) m (fun r m' => wp Γ Q X (k r) m') X
      ⟨c, F0, F_cur, s, R, rfl, hdw, hcap, hrv, htmk, hm, hk⟩)

private theorem m8_call_cand_sift {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hSift : M6EnvSpec Γ "full_m6_cand_sift" m6CandSiftSpec)
    {cands_ptr deg_ptr : BitVec 64} (start n : BitVec 32)
    {cands deg : List (BitVec 32)} {bound : Nat} {R : Mem 64 → Prop} {m : Mem 64}
    {k : Tup Val [] → Expr Val Cont rs}
    (hsn : start.toNat < n.toNat) (hnc : n.toNat ≤ cands.length) (hn31 : n.toNat < 2 ^ 31)
    (hbd : bound ≤ deg.length) (hclt : ∀ i < n.toNat, (cands[i]?.getD 0#32).toNat < bound)
    (hm : (array (t := i32) cands_ptr cands ⋆ array (t := i32) deg_ptr deg ⋆ R) m)
    (hk : ∀ cands' m', cands'.length = cands.length →
      (∀ i < n.toNat, (cands'[i]?.getD 0#32).toNat < bound) →
      (array (t := i32) cands_ptr cands' ⋆ array (t := i32) deg_ptr deg ⋆ R) m' →
      wp Γ Q X (k ()) m') :
    wp Γ Q X
      (Expr.call (as := [i64, i64, i32, i32]) (bs := []) "full_m6_cand_sift"
        (Arg.var cands_ptr, Arg.var deg_ptr, Arg.var start, Arg.var n, ()) k) m :=
  wp_call_of_spec _ k
    (hSift (cands_ptr, deg_ptr, start, n, ()) m (fun r m' => wp Γ Q X (k r) m') X
      ⟨cands, deg, bound, R, hsn, hnc, hn31, hbd, hclt, hm, hk⟩)

private theorem m8_call_sweep_vars {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hSVs : M6EnvSpec Γ "full_m6_sweep_vars" m6SweepVarsSpec)
    {c : FullCfg} {F0 : CNF Nat} {s : FullState}
    {budget tlim : Val i64} {R : Mem 64 → Prop} {m : Mem 64}
    {k : Tup Val [i64] → Expr Val Cont rs}
    (hdw : FullDenseInv c F0 s) (htmk : M6TmkZero s) (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ r s' m',
      FullDenseInv c F0 s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → M6TmkZero s' →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X
      (Expr.call (as := [i64, i64, i64]) (bs := [i64]) "full_m6_sweep_vars"
        (Arg.var c.hdr, Arg.var budget, Arg.var tlim, ()) k) m :=
  wp_call_of_spec _ k
    (hSVs (c.hdr, budget, tlim, ()) m (fun r m' => wp Γ Q X (k r) m') X
      ⟨c, F0, s, R, rfl, hdw, htmk, hm, hk⟩)

private theorem m8_call_flip {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hFlip : M6EnvSpec Γ "full_k6_flip" k6FlipSpec)
    {c : FullCfg} {s : FullState} {P : (Nat → Bool) → Prop} {L : K6Layout}
    {lit : Val i32} {R : Mem 64 → Prop} {m : Mem 64}
    {k : Tup Val [.bool] → Expr Val Cont rs}
    (hlen : s.LengthsOk c) (hL_len : L.scrLen = c.scratch_cap)
    (hL_mv : L.maxV = k6MaxV c.scratch_cap)
    (hK : K6Inv L P (k6StateOfScratch L s.scratch.scratch_buf))
    (hlit : lit.toNat < 2 * (k6StateOfScratch L s.scratch.scratch_buf).nv.toNat)
    (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ (ok : Bool) (scr' : List (BitVec 32)) (m' : Mem 64),
      let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
      let ks := k6StateOfScratch L s.scratch.scratch_buf
      let ks' := k6StateOfScratch L scr'
      s'.LengthsOk c → (∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]?) →
      K6Inv L P ks' → ks'.nv = ks.nv → ks'.nassump = ks.nassump →
      k6AssumpLitsS L scr' = k6AssumpLitsS L s.scratch.scratch_buf → ks'.neq = ks.neq →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k (ok, ())) m') :
    wp Γ Q X
      (Expr.call (as := [i64, i32]) (bs := [.bool]) "full_k6_flip"
        (Arg.var c.hdr, Arg.var lit, ()) k) m :=
  wp_call_of_spec _ k
    (hFlip (c.hdr, lit, ()) m (fun r m' => wp Γ Q X (k r) m') X
      ⟨c, s, P, L, R, rfl, hlen, hL_len, hL_mv, hK, hlit, hm, hk⟩)

private theorem m8_call_solve {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hSolve : M6EnvSpec Γ "full_m6_sweep_solve" m6SweepSolveSpec)
    {c : FullCfg} {s : FullState} {P : (Nat → Bool) → Prop} {L : K6Layout}
    {nv : Val i32} {tlim : Val i64} {R : Mem 64 → Prop} {m : Mem 64}
    {k : Tup Val [i64] → Expr Val Cont rs}
    (hlen : s.LengthsOk c) (hL_len : L.scrLen = c.scratch_cap)
    (hL_mv : L.maxV = k6MaxV c.scratch_cap)
    (hK : K6Inv L P (k6StateOfScratch L s.scratch.scratch_buf))
    (hnv : (k6StateOfScratch L s.scratch.scratch_buf).nv = nv)
    (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ (r fuel' rng' : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
      let s' : FullState :=
        { core := { s.core with fuel := fuel' },
          scratch := { s.scratch with rng_state := rng', scratch_buf := scr' } }
      let ks := k6StateOfScratch L s.scratch.scratch_buf
      let ks' := k6StateOfScratch L scr'
      s'.LengthsOk c → fuel'.toNat ≤ s.core.fuel.toNat →
      (∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]?) →
      K6Inv L P ks' → K6TrailSynced ks' → ks'.nv = nv → ks'.nassump = ks.nassump →
      k6AssumpLitsS L scr' = k6AssumpLitsS L s.scratch.scratch_buf → ks'.neq = ks.neq →
      (r = 0#64 ∨ r = 10#64 ∨ r = 20#64) →
      (r = 20#64 → ∀ β, P β → ¬ CNF.Sat β (unitsCnf (k6AssumpLitsS L scr'))) →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X
      (Expr.call (as := [i64, i32, i64]) (bs := [i64]) "full_m6_sweep_solve"
        (Arg.var c.hdr, Arg.var nv, Arg.var tlim, ()) k) m :=
  wp_call_of_spec _ k
    (hSolve (c.hdr, nv, tlim, ()) m (fun r m' => wp Γ Q X (k r) m') X
      ⟨c, s, P, L, R, rfl, hlen, hL_len, hL_mv, hK, hnv, hm, hk⟩)

private theorem m8_call_refine_sig {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hRef : M6EnvSpec Γ "full_m6_sweep_refine_sig" m6SweepRefineSigSpec)
    {c : FullCfg} {s : FullState} {nv bit_idx : Val i32} {R : Mem 64 → Prop} {m : Mem 64}
    {k : Tup Val [] → Expr Val Cont rs}
    (hlen : s.LengthsOk c) (hcap : k6MinScr ≤ c.scratch_cap)
    (hnv_cap : nv.toNat ≤ k6MaxV c.scratch_cap) (hnv_mx : nv.toNat ≤ 2 * c.max_vars)
    (hws : ∀ i < nv.toNat, (s.scratch.work_stk1[i]?.getD 0#32).toNat < s.core.cur_vars)
    (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ sig' m', sig'.length = c.max_vars →
      (FullMem c { s with scratch := { s.scratch with sim_sig := sig' } } ⋆ R) m' →
      wp Γ Q X (k ()) m') :
    wp Γ Q X
      (Expr.call (as := [i64, i32, i32]) (bs := []) "full_m6_sweep_refine_sig"
        (Arg.var c.hdr, Arg.var nv, Arg.var bit_idx, ()) k) m :=
  wp_call_of_spec _ k
    (hRef (c.hdr, nv, bit_idx, ()) m (fun r m' => wp Γ Q X (k r) m') X
      ⟨c, s, R, rfl, hlen, hcap, hnv_cap, hnv_mx, hws, hm, hk⟩)

private theorem m8_call_flip_round {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hFlipR : M6EnvSpec Γ "full_m6_sweep_flip_round" m6SweepFlipRoundSpec)
    {c : FullCfg} {s : FullState} {P : (Nat → Bool) → Prop} {L : K6Layout}
    {nv : Val i32} {R : Mem 64 → Prop} {m : Mem 64}
    {k : Tup Val [i32] → Expr Val Cont rs}
    (hlen : s.LengthsOk c) (hL_len : L.scrLen = c.scratch_cap)
    (hL_mv : L.maxV = k6MaxV c.scratch_cap)
    (hK : K6Inv L P (k6StateOfScratch L s.scratch.scratch_buf))
    (hnv : (k6StateOfScratch L s.scratch.scratch_buf).nv = nv)
    (hm : (FullMem c s ⋆ R) m)
    (hk : ∀ (ret : Val i32) (rng' : BitVec 64) (scr' : List (BitVec 32)) (m' : Mem 64),
      let s' : FullState := { s with scratch := { s.scratch with rng_state := rng', scratch_buf := scr' } }
      let ks := k6StateOfScratch L s.scratch.scratch_buf
      let ks' := k6StateOfScratch L scr'
      s'.LengthsOk c → (∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]?) →
      K6Inv L P ks' → ks'.nv = nv → ks'.nassump = ks.nassump →
      k6AssumpLitsS L scr' = k6AssumpLitsS L s.scratch.scratch_buf → ks'.neq = ks.neq →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k (ret, ())) m') :
    wp Γ Q X
      (Expr.call (as := [i64, i32]) (bs := [i32]) "full_m6_sweep_flip_round"
        (Arg.var c.hdr, Arg.var nv, ()) k) m :=
  wp_call_of_spec _ k
    (hFlipR (c.hdr, nv, ()) m (fun r m' => wp Γ Q X (k r) m') X
      ⟨c, s, P, L, R, rfl, hlen, hL_len, hL_mv, hK, hnv, hm, hk⟩)

private theorem m8_k6_slab_exit {c : FullCfg} {L : K6Layout} {s : FullState}
    {ks' : K6State} {R : Mem 64 → Prop} {m' : Mem 64}
    (hlen : s.LengthsOk c) (hL_len : L.scrLen = c.scratch_cap)
    (hsh' : ks'.ShapesOk L)
    (hm_ka : (K6MemA L (L.kPtr c.pScratchBuf) ks' ⋆ (FullK6Frame c L s ⋆ R)) m') :
    let scr' := s.scratch.scratch_buf.take L.k6Base ++ ks'.toSlab
    let s' : FullState := { s with scratch := { s.scratch with scratch_buf := scr' } }
    s'.LengthsOk c ∧ (∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]?) ∧
      k6StateOfScratch L scr' = ks' ∧ (FullMem c s' ⋆ R) m' := by
  intro scr' s'
  have hscr : s.scratch.scratch_buf.length = c.scratch_cap := hlen.scratch_ok.scratch_buf_len
  have hscr_L : s.scratch.scratch_buf.length = L.scrLen := hscr.trans hL_len.symm
  have hkb : L.k6Base ≤ s.scratch.scratch_buf.length := by
    rw [hscr_L]; unfold K6Layout.scrLen; omega
  have htake : (s.scratch.scratch_buf.take L.k6Base).length = L.k6Base :=
    List.length_take_of_le hkb
  have hlen' : scr'.length = c.scratch_cap := by
    dsimp only [scr']
    rw [List.length_append, htake, ks'.toSlab_length hsh', ← hL_len]
    unfold K6Layout.scrLen; omega
  have hpre : ∀ i < L.k6Base, scr'[i]? = s.scratch.scratch_buf[i]? := fun i hi => by
    dsimp only [scr']
    rw [List.getElem?_append_left (by rw [htake]; exact hi), List.getElem?_take_of_lt hi]
  have hof : k6StateOfScratch L scr' = ks' := by
    unfold k6StateOfScratch; dsimp only [scr']
    rw [k6_slab_drop_exact _ _ htake]
    exact K6State.ofSlab_toSlab hsh'
  obtain ⟨_, hm_k⟩ := k6MemA_to_mem hm_ka
  have hm' : (FullMem c s' ⋆ R) m' :=
    fullMem_join_k6 (c := c) (L := L) (s := s) hkb hsh' (sep_ac hm_k)
  exact ⟨⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hlen' }⟩, hpre, hof, hm'⟩

private theorem k6StateOfScratch_set_hdr25 {L : K6Layout} {scr : List (BitVec 32)}
    (hlen : scr.length = L.scrLen) (v : BitVec 32) :
    k6StateOfScratch L (scr.set (L.k6Base + 25) v) = k6PutHdr25 (k6StateOfScratch L scr) v := by
  have hkbase : L.k6Base ≤ scr.length := by rw [hlen]; unfold K6Layout.scrLen; omega
  have hle : L.k6Fixed ≤ (scr.drop L.k6Base).length := by
    rw [List.length_drop, hlen]; unfold K6Layout.scrLen; omega
  have hsh : (k6StateOfScratch L scr).ShapesOk L :=
    K6State.shapesOk_ofSlab_eq (L := L) (xs := scr.drop L.k6Base)
      (by rw [List.length_drop, hlen]; unfold K6Layout.scrLen; omega)
  have h25 : 25 < (scr.drop L.k6Base).length := by
    rw [List.length_drop, hlen]; unfold K6Layout.scrLen K6Layout.k6Fixed; omega
  have hdrop : (scr.set (L.k6Base + 25) v).drop L.k6Base = (scr.drop L.k6Base).set 25 v := by
    apply List.ext_getElem
    · simp [List.length_drop]
    · intro i hi1 hi2
      rw [List.getElem_drop]
      by_cases hi25 : i = 25
      · subst hi25
        rw [List.getElem_set_self
            (by simp only [List.length_set]; rw [hlen]; unfold K6Layout.scrLen K6Layout.k6Fixed; omega),
          List.getElem_set_self (by simp only [List.length_set]; exact h25)]
      · rw [List.getElem_set_ne (by omega), List.getElem_set_ne (Ne.symm hi25), List.getElem_drop]
  change K6State.ofSlab L ((scr.set (L.k6Base + 25) v).drop L.k6Base) =
    k6PutHdr25 (k6StateOfScratch L scr) v
  rw [hdrop, ← K6State.toSlab_ofSlab hle]
  change K6State.ofSlab L ((k6StateOfScratch L scr).toSlab.set 25 v) = _
  rw [← k6Hdr25_toSlab hsh v]
  exact K6State.ofSlab_toSlab (k6ShapesOk_putHdr25 hsh v)

private theorem m8_k6StateOfScratch_set_hdr15 {L : K6Layout} {scr : List (BitVec 32)}
    (hlen : scr.length = L.scrLen) (v : BitVec 32) :
    k6StateOfScratch L (scr.set (L.k6Base + 15) v) =
      (k6StateOfScratch L scr).putHdr .nassump v := by
  have hkbase : L.k6Base ≤ scr.length := by rw [hlen]; unfold K6Layout.scrLen; omega
  have h15 : 15 < (scr.drop L.k6Base).length := by
    rw [List.length_drop, hlen]; unfold K6Layout.scrLen K6Layout.k6Fixed; omega
  have hdrop : (scr.set (L.k6Base + 15) v).drop L.k6Base = (scr.drop L.k6Base).set 15 v := by
    apply List.ext_getElem
    · simp [List.length_drop]
    · intro i hi1 hi2
      rw [List.getElem_drop]
      by_cases hi15 : i = 15
      · subst hi15
        rw [List.getElem_set_self
            (by simp only [List.length_set]; rw [hlen]; unfold K6Layout.scrLen K6Layout.k6Fixed; omega),
          List.getElem_set_self (by simp only [List.length_set]; exact h15)]
      · rw [List.getElem_set_ne (by omega), List.getElem_set_ne (Ne.symm hi15), List.getElem_drop]
  have hdrop_tail : ∀ k, 15 < k →
      ((scr.drop L.k6Base).set 15 v).drop k = (scr.drop L.k6Base).drop k := fun k hk => by
    apply List.ext_getElem
    · simp [List.length_drop, Nat.sub_sub]
    · intro i hi1 hi2
      rw [List.getElem_drop, List.getElem_drop, List.getElem_set_ne (by omega)]
  have ho_gt : 15 < 25 ∧ 15 < L.oLvl ∧ 15 < L.oRsn ∧ 15 < L.oQPrev ∧ 15 < L.oQNext ∧
      15 < L.oQStamp ∧ 15 < L.oTrl ∧ 15 < L.oFlags ∧ 15 < L.oAna ∧ 15 < L.oKl ∧
      15 < L.oAssump ∧ 15 < L.oVals ∧ 15 < L.oWHead ∧ 15 < L.oWNext ∧ 15 < L.oWBlit ∧
      15 < L.oClOff ∧ 15 < L.oClSz ∧ 15 < L.oArena := by
    unfold K6Layout.oLvl K6Layout.oRsn K6Layout.oQPrev K6Layout.oQNext K6Layout.oQStamp
      K6Layout.oTrl K6Layout.oFlags K6Layout.oAna K6Layout.oKl K6Layout.oAssump K6Layout.oVals
      K6Layout.oWHead K6Layout.oWNext K6Layout.oWBlit K6Layout.oClOff K6Layout.oClSz
      K6Layout.oArena
    have := L.hmaxV; have := L.hacap; omega
  unfold k6StateOfScratch K6State.ofSlab K6State.putHdr
  dsimp only
  rw [hdrop]
  simp only [List.getElem?_set_ne (by decide : (15 : Nat) ≠ 0),
    List.getElem?_set_ne (by decide : (15 : Nat) ≠ 1),
    List.getElem?_set_ne (by decide : (15 : Nat) ≠ 2),
    List.getElem?_set_ne (by decide : (15 : Nat) ≠ 3),
    List.getElem?_set_ne (by decide : (15 : Nat) ≠ 4),
    List.getElem?_set_ne (by decide : (15 : Nat) ≠ 5),
    List.getElem?_set_ne (by decide : (15 : Nat) ≠ 6),
    List.getElem?_set_ne (by decide : (15 : Nat) ≠ 7),
    List.getElem?_set_ne (by decide : (15 : Nat) ≠ 8),
    List.getElem?_set_ne (by decide : (15 : Nat) ≠ 9),
    List.getElem?_set_ne (by decide : (15 : Nat) ≠ 10),
    List.getElem?_set_ne (by decide : (15 : Nat) ≠ 11),
    List.getElem?_set_ne (by decide : (15 : Nat) ≠ 12),
    List.getElem?_set_ne (by decide : (15 : Nat) ≠ 13),
    List.getElem?_set_ne (by decide : (15 : Nat) ≠ 14),
    List.getElem?_set_self h15, Option.getD_some,
    List.getElem?_set_ne (by decide : (15 : Nat) ≠ 16),
    List.getElem?_set_ne (by decide : (15 : Nat) ≠ 17),
    List.getElem?_set_ne (by decide : (15 : Nat) ≠ 18),
    List.getElem?_set_ne (by decide : (15 : Nat) ≠ 19),
    List.getElem?_set_ne (by decide : (15 : Nat) ≠ 20),
    List.getElem?_set_ne (by decide : (15 : Nat) ≠ 21),
    List.getElem?_set_ne (by decide : (15 : Nat) ≠ 22),
    List.getElem?_set_ne (by decide : (15 : Nat) ≠ 23),
    List.getElem?_set_ne (by decide : (15 : Nat) ≠ 24),
    hdrop_tail _ ho_gt.1, hdrop_tail _ ho_gt.2.1, hdrop_tail _ ho_gt.2.2.1,
    hdrop_tail _ ho_gt.2.2.2.1, hdrop_tail _ ho_gt.2.2.2.2.1, hdrop_tail _ ho_gt.2.2.2.2.2.1,
    hdrop_tail _ ho_gt.2.2.2.2.2.2.1, hdrop_tail _ ho_gt.2.2.2.2.2.2.2.1,
    hdrop_tail _ ho_gt.2.2.2.2.2.2.2.2.1, hdrop_tail _ ho_gt.2.2.2.2.2.2.2.2.2.1,
    hdrop_tail _ ho_gt.2.2.2.2.2.2.2.2.2.2.1, hdrop_tail _ ho_gt.2.2.2.2.2.2.2.2.2.2.2.1,
    hdrop_tail _ ho_gt.2.2.2.2.2.2.2.2.2.2.2.2.1, hdrop_tail _ ho_gt.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hdrop_tail _ ho_gt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hdrop_tail _ ho_gt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hdrop_tail _ ho_gt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    hdrop_tail _ ho_gt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2]

private theorem m8_denseInv_of_W {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) : FullDenseInv c F0 s :=
  ⟨⟨h.1, ⟨F_cur, h.2.1⟩⟩, h.2.2⟩

private theorem m8_k6AssumpLitsS_of_eq {L : K6Layout} {scr1 scr2 : List (BitVec 32)}
    (hna : (k6StateOfScratch L scr1).nassump = (k6StateOfScratch L scr2).nassump)
    (has : (k6StateOfScratch L scr1).assump = (k6StateOfScratch L scr2).assump) :
    k6AssumpLitsS L scr1 = k6AssumpLitsS L scr2 := by
  unfold k6AssumpLitsS k6AssumpLits; rw [hna, has]

private theorem m8_k6Shapes_putHdr_nassump {L : K6Layout} {ks : K6State} (v : BitVec 32)
    (h : ks.ShapesOk L) : (ks.putHdr .nassump v).ShapesOk L :=
  ⟨h.hdrTail_len, h.lvlArr_len, h.rsn_len, h.qprev_len, h.qnext_len, h.qstampArr_len,
   h.trl_len, h.flags_len, h.ana_len, h.kl_len, h.assump_len, h.vals_len, h.whead_len,
   h.wnext_len, h.wblit_len, h.clOff_len, h.clSz_len, h.arena_len⟩

private theorem m8_k6Inv_putHdr_nassump_zero {L : K6Layout} {P : (Nat → Bool) → Prop}
    {ks : K6State} (h : K6Inv L P ks) : K6Inv L P (ks.putHdr .nassump 0#32) :=
  ⟨m8_k6Shapes_putHdr_nassump 0#32 h.shapes,
   ⟨h.clauses.acap_eq, h.clauses.max_v_eq, h.clauses.max_orig_eq, h.clauses.max_cl_eq,
    h.clauses.nv_le, h.clauses.nc_le, h.clauses.alen_le, Nat.zero_le _,
    h.clauses.nkl_le, h.clauses.nana_le, h.clauses.cl_wf, h.clauses.cl_mono,
    h.clauses.incons_ok,
    fun _ hi => absurd hi (Nat.not_lt_zero _),
    h.clauses.flags_clean⟩,
   h.watches,
   ⟨h.assign.trl_end_le, h.assign.prop_le, h.assign.unass_eq, h.assign.vals_dom,
    h.assign.vals_neg_iff, h.assign.vals_nz_iff_trl, h.assign.trl_nodup, h.assign.trl_lt,
    h.assign.trl_lvl_le, h.assign.unass_lvl_zero, h.assign.trl_lvl_mono,
    h.assign.dec_earliest, h.assign.lvl0_ok⟩,
   h.reasons⟩

private def FullCandsFrame (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
  (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
    (array (t := i32) c.pWsort s.scratch.wsort ⋆
     array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
     array (t := i32) c.pTarjanMark s.scratch.tarjan_mark) ⋆
    FullScrMetaArrs c s.scratch ⋆ FullScrDynArrs c s.scratch) ⋆
  c.pad

private theorem fullMem_eq_candsFrame (c : FullCfg) (s : FullState) :
    FullMem c s =
      (array (t := i32) c.pTarjanReach s.scratch.tarjan_reach ⋆
        array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
        FullCandsFrame c s) := by
  unfold FullMem FullScratchArrays FullScrWksArrs FullCandsFrame
  ac_rfl

private theorem fullCands_split_array {a : BitVec 64} {xs : List (BitVec 32)} {n : Nat}
    (hn : n ≤ xs.length) :
    array (t := i32) a xs =
      (array (t := i32) a (xs.take n) ⋆
        array (t := i32) (a + BitVec.ofNat 64 (4 * n)) (xs.drop n)) := by
  have htake : (xs.take n).length = n := List.length_take_of_le hn
  conv => lhs; rw [← List.take_append_drop n xs]
  rw [array_append, htake]
  rfl

private theorem m8_cands_split_mem {p1 p2 : BitVec 64} {xs ws : List (BitVec 32)} {k : Nat}
    {F R : Mem 64 → Prop} {m : Mem 64} (hk : k ≤ xs.length)
    (hm : (array (t := i32) p1 xs ⋆ array (t := i32) p2 ws ⋆ F ⋆ R) m) :
    (array (t := i32) p1 (xs.take k) ⋆ array (t := i32) p2 ws ⋆
      (array (t := i32) (p1 + BitVec.ofNat 64 (4 * k)) (xs.drop k) ⋆ F ⋆ R)) m := by
  rw [fullCands_split_array (a := p1) hk] at hm
  exact sep_ac hm

private theorem fullCands_join_array {a : BitVec 64} {pref suff : List (BitVec 32)}
    {n : Nat} (hp : pref.length = n) :
    (array (t := i32) a pref ⋆ array (t := i32) (a + BitVec.ofNat 64 (4 * n)) suff) =
      array (t := i32) a (pref ++ suff) := by
  rw [array_append, hp]; rfl

private theorem m8_tmkZero_congr {s s' : FullState} (h : M6TmkZero s)
    (hcv : s'.core.cur_vars = s.core.cur_vars)
    (ht : s'.scratch.tarjan_mark = s.scratch.tarjan_mark) : M6TmkZero s' := by
  intro v hv; rw [ht]; exact h v (hcv ▸ hv)

private theorem m8_lengthsOk_trc_ws2 {c : FullCfg} {s : FullState} (h : s.LengthsOk c)
    {trc' ws2' : List (BitVec 32)} (htrc : trc'.length = 2 * c.max_vars)
    (hws2 : ws2'.length = 2 * c.max_vars) :
    ({ s with scratch := { s.scratch with tarjan_reach := trc', work_stk2 := ws2' } } :
      FullState).LengthsOk c :=
  ⟨h.core_ok, { h.scratch_ok with tarjan_reach_len := htrc, work_stk2_len := hws2 }⟩

private theorem m8_denseInvW_set_trc_ws2 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {trc' ws2' : List (BitVec 32)}
    (htrc : trc'.length = 2 * c.max_vars) (hws2 : ws2'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur
      { s with scratch := { s.scratch with tarjan_reach := trc', work_stk2 := ws2' } } :=
  ⟨m8_lengthsOk_trc_ws2 h.1 htrc hws2, h.2.1, h.2.2.1, h.2.2.2.1,
   h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

private theorem m8_denseInvW_set_flags {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {flags' : List (BitVec 32)}
    (hfl : flags'.length = c.max_vars) :
    FullDenseInvW c F0 F_cur { s with core := { s.core with flags := flags' } } := by
  let s' : FullState := { s with core := { s.core with flags := flags' } }
  have hw := h.2.1
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
  exact ⟨⟨{ h.1.core_ok with flags_len := hfl }, h.1.scratch_ok⟩, hw',
    h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

private theorem m8_denseInvW_set_sim {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {fuel' rng' : BitVec 64} {sig' : List (BitVec 64)} {scr' : List (BitVec 32)}
    (hsig : sig'.length = c.max_vars) (hscr : scr'.length = c.scratch_cap) :
    FullDenseInvW c F0 F_cur
      { core := { s.core with fuel := fuel' },
        scratch := { s.scratch with rng_state := rng', sim_sig := sig', scratch_buf := scr' } } := by
  let s' : FullState :=
    { core := { s.core with fuel := fuel' },
      scratch := { s.scratch with rng_state := rng', sim_sig := sig', scratch_buf := scr' } }
  have hco := h.1.core_ok
  have hco' : FullCoreState.LengthsOk c s'.core :=
    ⟨hco.vals_len, hco.lit_mark_len, hco.mrk_len, hco.flags_len, hco.lvl_len, hco.rsns_len,
     hco.trl_len, hco.trail_pos_len, hco.tmp_len_arr, hco.min_clr_len_arr, hco.frame_trail_len,
     hco.frame_dec_len, hco.wvec_len, hco.repr_len, hco.min_stk_len, hco.arena_len_arr,
     hco.wstk_len_arr, hco.cur_vars_ge, hco.cur_vars_le, hco.arena_len_le, hco.wlen_le,
     hco.trail_end_le, hco.propagated_le, hco.tmp_len_le, hco.min_clr_len_le⟩
  have hw := h.2.1
  have hw' : FullWitnessInv c F0 F_cur s'.core :=
    { hw with
      arena := { hw.arena with len_ok := hw.arena.len_ok }
      watches := hw.watches.with_wstk rfl rfl rfl rfl rfl (fun _ r => r) }
  exact ⟨⟨hco', { h.1.scratch_ok with sim_sig_len := hsig, scratch_buf_len := hscr }⟩, hw',
    h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

private theorem m8_k6Layout_congr {n m : Nat} (e : n = m) (h1 : k6MinScr ≤ n)
    (h2 : n < dimacsBound) (h1' : k6MinScr ≤ m) (h2' : m < dimacsBound) :
    k6LayoutOfCap n h1 h2 = k6LayoutOfCap m h1' h2' := by
  subst e; rfl

private abbrev m8SimState (s : FullState) (fuel rng : BitVec 64)
    (sig : List (BitVec 64)) (scr : List (BitVec 32)) : FullState :=
  { core := { s.core with fuel := fuel },
    scratch := { s.scratch with rng_state := rng, sim_sig := sig, scratch_buf := scr } }

private theorem m8_k11_ptr {c : FullCfg} {L : K6Layout} (hL_len : L.scrLen = c.scratch_cap) :
    L.kPtr c.pScratchBuf + 11#64 * 4 =
      c.pScratchBuf + BitVec.setWidth 64 (BitVec.ofNat 32 (L.k6Base + 11)) * 4 := by
  have hLkb : L.k6Base + 11 < 2 ^ 32 := by
    have := c.hscr; rw [← hL_len] at this
    unfold K6Layout.scrLen K6Layout.k6Fixed at this; unfold dimacsBound at this; omega
  have hkb_lt : L.k6Base < 2 ^ 32 := by omega
  unfold K6Layout.kPtr; rw [BitVec.add_assoc]; congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt hLkb, Nat.mod_eq_of_lt (by omega : 4 * L.k6Base < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 4 < 2 ^ 64), Nat.mod_eq_of_lt (by omega : 44 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 4 * L.k6Base + 44 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : (L.k6Base + 11) * 4 < 2 ^ 64)]
  omega

private theorem m8_k11_idx {c : FullCfg} {L : K6Layout} (hL_len : L.scrLen = c.scratch_cap) :
    (BitVec.setWidth 64 (BitVec.ofNat 32 (L.k6Base + 11))).toNat < c.scratch_cap := by
  have := c.hscr; rw [← hL_len]; unfold K6Layout.scrLen K6Layout.k6Fixed at *
  have hLkb : L.k6Base + 11 < 2 ^ 32 := by unfold dimacsBound at this; omega
  rw [BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hLkb]; omega),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hLkb]
  omega

private theorem m8_coneOk_of_k6 {F_cur : List (List Nat)} {s : FullState}
    {hge_c : k6MinScr ≤ s.scratch.scratch_buf.length}
    {hlt_c : s.scratch.scratch_buf.length < dimacsBound}
    {nv : Val i32} {scr' : List (BitVec 32)}
    (hcone : M6SweepConeOk F_cur s nv.toNat)
    (hscr_eq : scr'.length = s.scratch.scratch_buf.length)
    (hK : K6Inv (k6LayoutOfCap s.scratch.scratch_buf.length hge_c hlt_c)
      (ConeModelSet F_cur s.scratch.work_stk1 nv.toNat)
      (k6StateOfScratch (k6LayoutOfCap s.scratch.scratch_buf.length hge_c hlt_c) scr'))
    (hnv : (k6StateOfScratch (k6LayoutOfCap s.scratch.scratch_buf.length hge_c hlt_c) scr').nv = nv)
    {fuel' rng' : BitVec 64} {sig' : List (BitVec 64)} :
    M6SweepConeOk F_cur
      { core := { s.core with fuel := fuel' },
        scratch := { s.scratch with rng_state := rng', sim_sig := sig', scratch_buf := scr' } }
      nv.toNat := by
  have hlt_scr : scr'.length < dimacsBound := hscr_eq ▸ hlt_c
  have hge_scr : k6MinScr ≤ scr'.length := hscr_eq ▸ hge_c
  have hLeq := m8_k6Layout_congr hscr_eq hge_scr hlt_scr hge_c hlt_c
  have hnv' : (k6StateOfScratch (k6LayoutOfCap s.scratch.scratch_buf.length hge_c hlt_c) scr').nv =
      BitVec.ofNat 32 nv.toNat :=
    hnv.trans (BitVec.eq_of_toNat_eq (by simp)).symm
  refine ⟨hcone.1, by rw [hscr_eq]; exact hcone.2.1, hcone.2.2.1, hcone.2.2.2.1,
    ⟨hge_scr, hlt_scr, hLeq ▸ hK⟩, ⟨hge_scr, hlt_scr, hLeq ▸ hnv'⟩⟩

private theorem m8_call_sweep_var_fl {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hSV : M6EnvSpec Γ "full_m6_sweep_var" m6SweepVarSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {flags' : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {rv : BitVec 32}
    {tlim : BitVec 64} {k : Tup Val [i64] → Expr Val Cont rs}
    (hm : (FullMem c { s with core := { s.core with flags := flags' } } ⋆ R) m)
    (hdw : FullDenseInvW c F0 F_cur s) (hfl : flags'.length = c.max_vars)
    (hcap : k6MinScr ≤ c.scratch_cap) (hrv : rv.toNat < s.core.cur_vars)
    (htmk : M6TmkZero s)
    (hk : ∀ r s' m',
      FullDenseInvW c F0 F_cur s' → s'.core.cur_vars = s.core.cur_vars →
      s'.core.fuel.toNat ≤ s.core.fuel.toNat → M6TmkZero s' →
      s'.scratch.tarjan_reach = s.scratch.tarjan_reach →
      (r = 1#64 ∨ r = 20#64) → (r = 20#64 → F0.Unsat) →
      (FullMem c s' ⋆ R) m' → wp Γ Q X (k (r, ())) m') :
    wp Γ Q X
      (Expr.call (as := [i64, i32, i64]) (bs := [i64]) "full_m6_sweep_var"
        (Arg.var c.hdr, Arg.var rv, Arg.var tlim, ()) k) m :=
  m8_call_sweep_var hSV (m8_denseInvW_set_flags hdw hfl) hcap hrv
    (m8_tmkZero_congr htmk rfl rfl) hm hk

/-! ## 2. `m8_sweep_rand_phases_wp` (`k[25]` PRNG) -/

theorem m8_sweep_rand_phases_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec) :
    ∀ args m Q X, m6SweepRandPhasesSpec args m Q X →
      Func.wp Γ full_m6_sweep_rand_phases_body args m Q X := by
  rintro ⟨h, nv, ⟨⟩⟩ m Q X ⟨c, s, P, L, R, rfl, hlen, hL_len, hL_mv, hK, hnv, hm, hQ⟩
  unfold Func.wp full_m6_sweep_rand_phases_body
  have hmL := L.hmaxV
  have hscr : s.scratch.scratch_buf.length = c.scratch_cap := hlen.scratch_ok.scratch_buf_len
  have hcap_lt : c.scratch_cap < 2 ^ 64 :=
    Nat.lt_trans c.hscr (by unfold dimacsBound; decide)
  have hmv32_eq : (BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32 = L.mv32 := by
    rw [← hL_mv]; exact k6_mv32_zext L
  have hkptr_c0 : c.pScratchBuf + BitVec.setWidth 64
      ((1280 : BitVec 32) + (BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) <<<
        (1 : Nat))) * 4 = L.kPtr c.pScratchBuf := by
    rw [hmv32_eq]
    simpa only [show (1280 : BitVec 32) = 1280#32 from rfl] using k6_ptr_base_k6Base L c.pScratchBuf
  have hscr_L : s.scratch.scratch_buf.length = L.scrLen := hscr.trans hL_len.symm
  let ks0 := k6StateOfScratch L s.scratch.scratch_buf
  have hm_ka : (K6MemA L (L.kPtr c.pScratchBuf) ks0 ⋆ (FullK6Frame c L s ⋆ R)) m := by
    rw [fullMem_eq_k6Frame hscr_L] at hm
    exact k6Mem_to_amem hK.shapes (sep_ac hm)
  c0_hsteps_nogrp
  refine m8_call_max_v_cap hMaxV (cap := BitVec.ofNat 64 c.scratch_cap) ?_
  have hcap_toNat : (BitVec.ofNat 64 c.scratch_cap).toNat = c.scratch_cap := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap_lt]
  rw [hcap_toNat]
  c0_hsplit
  · exfalso
    have : (BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32 = 0#32 := hc
    rw [hmv32_eq] at this
    have h0 := congrArg BitVec.toNat this
    rw [k6_mv32_toNat] at h0; simp at h0; omega
  c0_hsplit
  · exfalso
    have hnv_le := hK.clauses.nv_le
    rw [hnv] at hnv_le
    have hgt : k6MaxV c.scratch_cap % 2 ^ 64 % 2 ^ 32 < nv.toNat := hc
    rw [← hL_mv, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hgt
    omega
  have hfl_ptr : L.kPtr c.pScratchBuf + BitVec.setWidth 64
      ((32 : BitVec 32) + (6 : BitVec 32) * (BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32) * 4 =
      L.kPtr c.pScratchBuf + BitVec.ofNat 64 (4 * L.oFlags) := by
    rw [hmv32_eq]
    simpa only [show (32 : BitVec 32) = 32#32 from rfl, show (6 : BitVec 32) = 6#32 from rfl,
      K6Layout.oFlags] using k6_ptr_add_mul L (L.kPtr c.pScratchBuf) 6 (by decide)
  have hfl_ptr_ofnat : L.kPtr c.pScratchBuf + BitVec.setWidth 64
      ((32 : BitVec 32) + 6 * (BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32) * 4 =
      L.kPtr c.pScratchBuf + BitVec.ofNat 64 (4 * L.oFlags) := hfl_ptr
  c0_hsteps_nogrp
  dsimp only [Prod.fst]
  try rw [hkptr_c0]
  try rw [hfl_ptr]
  try rw [hfl_ptr_ofnat]
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i32]) (fun (_rs0, ()) m_r => m_r = m) ?_ ?_
  · rintro _ ⟨rs0, ⟨⟩⟩ m_r hm_r
    subst m_r
    c0_hsteps_nogrp
    refine wp_loop_inv (ts := [i32, i64, i32])
      (fun (_rs_l, _rb_l, i, ()) ml => i.toNat ≤ nv.toNat ∧ ∃ ks_l : K6State,
        K6Inv L P ks_l ∧ ks_l.nv = ks0.nv ∧ ks_l.nassump = ks0.nassump ∧
        ks_l.assump = ks0.assump ∧ ks_l.neq = ks0.neq ∧
        (K6MemA L (L.kPtr c.pScratchBuf) ks_l ⋆ (FullK6Frame c L s ⋆ R)) ml)
      (fun (_, _, i, ()) _ => nv.toNat - i.toNat)
      ?_ ?_
    · intro _ hJ_in
      c0_hsteps_nogrp
      try dsimp only [Prod.fst]
      exact hJ_in (_, _, 0#32, ()) m ⟨Nat.zero_le _, ks0, hK, rfl, rfl, rfl, rfl, hm_ka⟩
    · rintro _ ⟨rs_l, rb_l, i_l, ⟨⟩⟩ ml ⟨hi_le, ks_l, hK_l, hnv_l, hna_l, has_l, hnq_l, hm_l⟩ hJ_in
      c0_hsplit; rotate_left
      · have hi_ge : ¬ i_l.toNat < nv.toNat := hc
        c0_hsteps_nogrp
        try rw [show (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 25) : BitVec 64) =
          BitVec.ofNat 64 25 from rfl]
        let ks25 := k6PutHdr25 ks_l rs_l
        have hK25 : K6Inv L P ks25 := k6Set25_preserves_inv hK_l rs_l
        have hK25_nv : ks25.nv = ks0.nv := hnv_l
        have hK25_na : ks25.nassump = ks0.nassump := hna_l
        have hK25_as : ks25.assump = ks0.assump := has_l
        have hK25_nq : ks25.neq = ks0.neq := hnq_l
        let ks_ph := ks25.putHdr .phase ((ks25.phase) ^^^ 1#32)
        have hK_ph : K6Inv L P ks_ph := k6Inv_set_phase _ hK25
        let scr_out := s.scratch.scratch_buf.take L.k6Base ++ ks_ph.toSlab
        c0_hsteps!
        obtain ⟨hlen', hpre', hof', hm'⟩ := m8_k6_slab_exit hlen hL_len hK_ph.shapes
          (by assumption)
        have hna_s : (k6StateOfScratch L scr_out).nassump = ks0.nassump := by
          rw [hof']; exact hK25_na
        have has_s : k6AssumpLitsS L scr_out = k6AssumpLitsS L s.scratch.scratch_buf :=
          m8_k6AssumpLitsS_of_eq hna_s (by rw [hof']; exact hK25_as)
        exact hQ s.scratch.rng_state scr_out _ hlen' hpre' (hof' ▸ hK_ph)
          (by rw [hof']; exact hnv ▸ hK25_nv) hna_s has_s (by rw [hof']; exact hK25_nq) hm'
      · have hi_lt : i_l.toNat < nv.toNat := hc
        have hnv_le : nv.toNat ≤ L.maxV := hnv ▸ hK.clauses.nv_le
        have hi_maxV : i_l.toNat < L.maxV := Nat.lt_of_lt_of_le hi_lt hnv_le
        have hi_z : (BitVec.setWidth 64 i_l).toNat = i_l.toNat := bv_c0_zext32_64 i_l
        have hi1 : (i_l + 1#32).toNat = i_l.toNat + 1 := bv32_add1_toNat (by omega)
        refine wp_join_group (ts := [i32, i64]) (fun (_rs', _rb', ()) mj => mj = ml) ?_ ?_
        · rintro _ ⟨rs', rb', ⟨⟩⟩ mj hmj
          subst mj
          have hfl_len : ks_l.flags.length = L.maxV := hK_l.shapes.flags_len
          have hfl_bd : i_l.toNat < szV L := hi_maxV
          c0_hsteps_nogrp
          have hk_step := k6Inv_set_flags_bit0 hi_maxV (rb'.setWidth 32) hK_l
          refine hJ_in (rs', rb' >>> (1 : Nat), i_l + 1#32, ()) _
            (by dsimp only; rw [hi1]; omega)
            ⟨by rw [hi1]; exact hi_lt, _, hk_step, hnv_l, hna_l, has_l, hnq_l, ?_⟩
          simpa [show (1 : BitVec 32) = 1#32 from rfl] using (by assumption :
            (K6MemA L (L.kPtr c.pScratchBuf) _ ⋆ (FullK6Frame c L s ⋆ R)) _)
        · intro _ hJ_rng
          c0_hsplit
          · c0_hsplit
            · c0_hsteps!; exact hJ_rng (_, _, ()) ml rfl
            · c0_hsteps!; exact hJ_rng (rs_l, rb_l, ()) ml rfl
          · c0_hsteps!; exact hJ_rng (rs_l, rb_l, ()) ml rfl
  · intro _ hJ
    c0_hsplit
    · c0_hsteps!; exact hJ (0x9E3779B9#32, ()) m rfl
    · c0_hsteps!; exact hJ (_, ()) m rfl

/-! ## 3. `m8_sweep_flip_round_wp` (`k[25]` PRNG) -/

theorem m8_sweep_flip_round_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hFlip : M6EnvSpec Γ "full_k6_flip" k6FlipSpec) :
    ∀ args m Q X, m6SweepFlipRoundSpec args m Q X →
      Func.wp Γ full_m6_sweep_flip_round_body args m Q X := by
  rintro ⟨h, nv, ⟨⟩⟩ m Q X ⟨c, s, P, L, R, rfl, hlen, hL_len, hL_mv, hK, hnv, hm, hQ⟩
  unfold Func.wp full_m6_sweep_flip_round_body
  have hmL := L.hmaxV
  have hscr : s.scratch.scratch_buf.length = c.scratch_cap := hlen.scratch_ok.scratch_buf_len
  have hcap_lt : c.scratch_cap < 2 ^ 64 :=
    Nat.lt_trans c.hscr (by unfold dimacsBound; decide)
  have hmv32_eq : (BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32 = L.mv32 := by
    rw [← hL_mv]; exact k6_mv32_zext L
  have hkptr_c0 : c.pScratchBuf + BitVec.setWidth 64
      ((1280 : BitVec 32) + (BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) <<<
        (1 : Nat))) * 4 = L.kPtr c.pScratchBuf := by
    rw [hmv32_eq]
    simpa only [show (1280 : BitVec 32) = 1280#32 from rfl] using k6_ptr_base_k6Base L c.pScratchBuf
  have hscr_L : s.scratch.scratch_buf.length = L.scrLen := hscr.trans hL_len.symm
  let ks0 := k6StateOfScratch L s.scratch.scratch_buf
  have hm_ka : (K6MemA L (L.kPtr c.pScratchBuf) ks0 ⋆ (FullK6Frame c L s ⋆ R)) m := by
    rw [fullMem_eq_k6Frame hscr_L] at hm
    exact k6Mem_to_amem hK.shapes (sep_ac hm)
  c0_hsteps_nogrp
  c0_hsplit
  · c0_hsteps!
    exact hQ 0#32 s.scratch.rng_state s.scratch.scratch_buf m hlen (fun _ _ => rfl)
      hK hnv rfl rfl rfl hm
  refine m8_call_max_v_cap hMaxV (cap := BitVec.ofNat 64 c.scratch_cap) ?_
  have hcap_toNat : (BitVec.ofNat 64 c.scratch_cap).toNat = c.scratch_cap := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap_lt]
  rw [hcap_toNat]
  c0_hsplit
  · exfalso
    have : (BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32 = 0#32 := hc
    rw [hmv32_eq] at this
    have h0 := congrArg BitVec.toNat this
    rw [k6_mv32_toNat] at h0; simp at h0; omega
  c0_hsplit
  · exfalso
    have hnv_le := hK.clauses.nv_le
    rw [hnv] at hnv_le
    have hgt : k6MaxV c.scratch_cap % 2 ^ 64 % 2 ^ 32 < nv.toNat := hc
    rw [← hL_mv, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hgt
    omega
  c0_hsteps_nogrp
  dsimp only [Prod.fst]
  try rw [hkptr_c0]
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i32]) (fun (_rs0, ()) m_r => m_r = m) ?_ ?_
  · rintro _ ⟨rs0, ⟨⟩⟩ m_r hm_r
    subst m_r
    have hvals_ptr : L.kPtr c.pScratchBuf + BitVec.setWidth 64
        ((32 : BitVec 32) + 10 * (BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32) * 4 =
        L.kPtr c.pScratchBuf + BitVec.ofNat 64 (4 * L.oVals) := by
      rw [hmv32_eq]
      simpa only [show (32 : BitVec 32) = 32#32 from rfl, show (10 : BitVec 32) = 10#32 from rfl,
        K6Layout.oVals] using k6_ptr_add_mul L (L.kPtr c.pScratchBuf) 10 (by decide)
    have hnv_le : nv.toNat ≤ L.maxV := hnv ▸ hK.clauses.nv_le
    have hnv_pos : 0 < nv.toNat := by
      have : ¬ nv = 0#32 := by assumption
      have hne : nv.toNat ≠ 0 := fun h0 => this (BitVec.eq_of_toNat_eq (by simpa using h0))
      omega
    c0_hsteps_nogrp
    try rw [hvals_ptr]
    c0_hsteps_nogrp
    refine wp_loop_inv (ts := [i32, i64, i32, i32])
      (fun (rs_l, _rb_l, flp_l, step_l, ()) ml =>
        step_l.toNat ≤ nv.toNat ∧ ∃ scr_l : List (BitVec 32),
          scr_l.length = c.scratch_cap ∧
          (∀ i < L.k6Base, scr_l[i]? = s.scratch.scratch_buf[i]?) ∧
          K6Inv L P (k6StateOfScratch L scr_l) ∧
          (k6StateOfScratch L scr_l).nv = nv ∧
          (k6StateOfScratch L scr_l).nassump = ks0.nassump ∧
          k6AssumpLitsS L scr_l = k6AssumpLitsS L s.scratch.scratch_buf ∧
          (k6StateOfScratch L scr_l).neq = ks0.neq ∧
          (FullMem c { s with scratch := { s.scratch with scratch_buf := scr_l } } ⋆ R) ml)
      (fun (_, _, _, step_l, ()) _ => nv.toNat - step_l.toNat)
      ?_ ?_
    · intro _ hJ_in
      c0_hsteps_nogrp
      try dsimp only [Prod.fst]
      exact hJ_in (_, _, 0#32, 0#32, ()) m ⟨Nat.zero_le _, s.scratch.scratch_buf, hscr,
        fun _ _ => rfl, hK, hnv, rfl, rfl, rfl, hm⟩
    · rintro _ ⟨rs_l, rb_l, flp_l, step_l, ⟨⟩⟩ ml
        ⟨hstep_le, scr_l, hscr_l, hpre_l, hK_l, hnv_l, hna_l, has_l, hnq_l, hm_l⟩ hJ_in
      c0_hsplit; rotate_left
      · have hge : ¬ step_l.toNat < nv.toNat := hc
        have hscr_l_L : scr_l.length = L.scrLen := hscr_l.trans hL_len.symm
        let s_l : FullState := { s with scratch := { s.scratch with scratch_buf := scr_l } }
        have hlen_l : s_l.LengthsOk c :=
          ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hscr_l }⟩
        c0_hsteps_nogrp
        try rw [show (BitVec.ofNat (OfNat.ofNat 64) (OfNat.ofNat 25) : BitVec 64) =
          BitVec.ofNat 64 25 from rfl]
        c0_hsteps!
        let scr_out := scr_l.set (L.k6Base + 25) rs_l
        have hscr_out_len : scr_out.length = c.scratch_cap := by simp [scr_out, hscr_l]
        have hlen' : ({ s with scratch := { s.scratch with scratch_buf := scr_out } } :
            FullState).LengthsOk c :=
          ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hscr_out_len }⟩
        have hof' : k6StateOfScratch L scr_out = k6PutHdr25 (k6StateOfScratch L scr_l) rs_l :=
          k6StateOfScratch_set_hdr25 hscr_l_L rs_l
        have hK_out : K6Inv L P (k6StateOfScratch L scr_out) := by
          rw [hof']; exact k6Set25_preserves_inv hK_l rs_l
        have hpre_out : ∀ i < L.k6Base, scr_out[i]? = s.scratch.scratch_buf[i]? := fun i hi => by
          dsimp only [scr_out]
          rw [List.getElem?_set_ne (by omega)]
          exact hpre_l i hi
        have hna_out : (k6StateOfScratch L scr_out).nassump = ks0.nassump := by
          rw [hof']; exact hna_l
        have has_out : k6AssumpLitsS L scr_out = k6AssumpLitsS L s.scratch.scratch_buf :=
          (m8_k6AssumpLitsS_of_eq (by rw [hof']; rfl) (by rw [hof']; rfl)).trans has_l
        have hnq_out : (k6StateOfScratch L scr_out).neq = ks0.neq := by
          rw [hof']; exact hnq_l
        have hnv_out : (k6StateOfScratch L scr_out).nv = nv := by
          rw [hof']; exact hnv_l
        exact hQ flp_l s.scratch.rng_state scr_out _ hlen' hpre_out hK_out
          hnv_out hna_out has_out hnq_out (by assumption)
      · have hstep_lt : step_l.toNat < nv.toNat := hc
        have hstep1 : (step_l + 1#32).toNat = step_l.toNat + 1 := bv32_add1_toNat (by omega)
        refine wp_join_group (ts := [i32, i64]) (fun (_rs', _rb', ()) mj => mj = ml) ?_ ?_
        · rintro _ ⟨rs', rb', ⟨⟩⟩ mj hmj
          subst mj
          refine wp_join_group (ts := [i32])
            (fun (flp', ()) mf => ∃ scr_f : List (BitVec 32),
              scr_f.length = c.scratch_cap ∧
              (∀ i < L.k6Base, scr_f[i]? = s.scratch.scratch_buf[i]?) ∧
              K6Inv L P (k6StateOfScratch L scr_f) ∧
              (k6StateOfScratch L scr_f).nv = nv ∧
              (k6StateOfScratch L scr_f).nassump = ks0.nassump ∧
              k6AssumpLitsS L scr_f = k6AssumpLitsS L s.scratch.scratch_buf ∧
              (k6StateOfScratch L scr_f).neq = ks0.neq ∧
              (FullMem c { s with scratch := { s.scratch with scratch_buf := scr_f } } ⋆ R) mf)
            (fun _ (flp', ()) mf ⟨scr_f, hscr_f, hpre_f, hK_f, hnv_f, hna_f, has_f, hnq_f, hm_f⟩ => by
              c0_hsteps_nogrp
              exact hJ_in (rs', rb' >>> (1 : Nat), flp', step_l + 1#32, ()) mf
                (by dsimp only; rw [hstep1]; omega)
                ⟨by rw [hstep1]; exact hstep_lt, scr_f, hscr_f, hpre_f, hK_f, hnv_f, hna_f,
                  has_f, hnq_f, hm_f⟩)
            (fun _ hJ_flp => by
              c0_hsplit; rotate_left
              · c0_hsteps!
                exact hJ_flp (flp_l, ()) ml ⟨scr_l, hscr_l, hpre_l, hK_l, hnv_l, hna_l,
                  has_l, hnq_l, hm_l⟩
              · refine wp_join_group (ts := [i32]) (fun (v, ()) mv => v.toNat < nv.toNat ∧ mv = ml)
                  (fun _ (v, ()) mv ⟨hv_nv, hmv⟩ => by
                    subst mv
                    have hv_2max : (v <<< (1 : Nat)).toNat < 2 * L.maxV := by
                      rw [show (v <<< (1 : Nat)).toNat = 2 * v.toNat from by bv_omega]; omega
                    let s_l : FullState := { s with scratch := { s.scratch with scratch_buf := scr_l } }
                    have hlen_l : s_l.LengthsOk c :=
                      ⟨hlen.core_ok, { hlen.scratch_ok with scratch_buf_len := hscr_l }⟩
                    have hscr_l_L : scr_l.length = L.scrLen := hscr_l.trans hL_len.symm
                    have hm_ka_l : (K6MemA L (L.kPtr c.pScratchBuf) (k6StateOfScratch L scr_l) ⋆
                        (FullK6Frame c L s_l ⋆ R)) ml := by
                      rw [fullMem_eq_k6Frame hscr_l_L] at hm_l
                      exact k6Mem_to_amem hK_l.shapes (sep_ac hm_l)
                    have hvals_len : (k6StateOfScratch L scr_l).vals.length = 2 * L.maxV :=
                      hK_l.shapes.vals_len
                    refine wp_join_group (ts := [i32])
                      (fun (lit, ()) mlit => lit.toNat < 2 * nv.toNat ∧ mlit = ml)
                      (fun _ (lit, ()) mlit ⟨hlit_bd, hmlit⟩ => by
                        subst mlit
                        clear hm_ka_l
                        refine wp_join_group (ts := [i32])
                          (fun (flp'', ()) mf => ∃ scr_f : List (BitVec 32),
                            scr_f.length = c.scratch_cap ∧
                            (∀ i < L.k6Base, scr_f[i]? = s.scratch.scratch_buf[i]?) ∧
                            K6Inv L P (k6StateOfScratch L scr_f) ∧
                            (k6StateOfScratch L scr_f).nv = nv ∧
                            (k6StateOfScratch L scr_f).nassump = ks0.nassump ∧
                            k6AssumpLitsS L scr_f = k6AssumpLitsS L s.scratch.scratch_buf ∧
                            (k6StateOfScratch L scr_f).neq = ks0.neq ∧
                            (FullMem c { s with scratch := { s.scratch with scratch_buf := scr_f } } ⋆ R) mf)
                          (fun _ (flp'', ()) mf
                              ⟨scr_f, hscr_f, hpre_f, hK_f, hnv_f, hna_f, has_f, hnq_f, hm_f⟩ => by
                            c0_hsteps!
                            exact hJ_flp (flp'', ()) mf ⟨scr_f, hscr_f, hpre_f, hK_f, hnv_f, hna_f,
                              has_f, hnq_f, hm_f⟩)
                          (fun _ hJ_flp2 => by
                            refine m8_call_flip hFlip hlen_l hL_len hL_mv hK_l
                              (by rw [hnv_l]; exact hlit_bd) hm_l
                              (fun ok scr_f m_f hlen_f hpre_f hK_f hnv_f hna_f has_f hnq_f hm_f => ?_)
                            have hscr_f : scr_f.length = c.scratch_cap := hlen_f.scratch_ok.scratch_buf_len
                            have hpre_full : ∀ i < L.k6Base, scr_f[i]? = s.scratch.scratch_buf[i]? :=
                              fun i hi => (hpre_f i hi).trans (hpre_l i hi)
                            have hnv_full : (k6StateOfScratch L scr_f).nv = nv := hnv_f.trans hnv_l
                            have hna_full : (k6StateOfScratch L scr_f).nassump = ks0.nassump :=
                              hna_f.trans hna_l
                            have has_full : k6AssumpLitsS L scr_f = k6AssumpLitsS L s.scratch.scratch_buf :=
                              has_f.trans has_l
                            have hnq_full : (k6StateOfScratch L scr_f).neq = ks0.neq := hnq_f.trans hnq_l
                            c0_hsplit
                            · c0_hsteps!
                              exact hJ_flp2 (flp_l + 1#32, ()) m_f ⟨scr_f, hscr_f, hpre_full, hK_f,
                                hnv_full, hna_full, has_full, hnq_full, hm_f⟩
                            · c0_hsteps!
                              exact hJ_flp2 (flp_l, ()) m_f ⟨scr_f, hscr_f, hpre_full, hK_f,
                                hnv_full, hna_full, has_full, hnq_full, hm_f⟩))
                      (fun _ hJ_lit => by
                        c0_hsteps_nogrp
                        c0_hsplit
                        · c0_hsteps!
                          exact hJ_lit (v <<< (1 : Nat), ()) ml
                            ⟨by rw [show (v <<< (1 : Nat)).toNat = 2 * v.toNat from by bv_omega]; omega, rfl⟩
                        · c0_hsteps!
                          have h1_lt : ((v <<< (1 : Nat)) ||| 1#32).toNat < 2 * nv.toNat := by
                            have hv_lt31 : v.toNat < 2 ^ 31 := by omega
                            have hsh : (v <<< (1 : Nat)).toNat = 2 * v.toNat := by bv_omega
                            have hor : ((v <<< (1 : Nat)) ||| 1#32).toNat = 2 * v.toNat + 1 := by
                              rw [BitVec.toNat_or, hsh, show (1#32 : BitVec 32).toNat = 1 from rfl]
                              exact nat_two_mul_lor_one v.toNat
                            omega
                          exact hJ_lit ((v <<< (1 : Nat)) ||| 1#32, ()) ml ⟨h1_lt, rfl⟩))
                  (fun _ hJ_v => by
                    let rx1 := rs0 ^^^ rs0 <<< (13 : Nat)
                    let rx2 := rx1 ^^^ rx1 >>> (17 : Nat)
                    let rs0' := rx2 ^^^ rx2 <<< (5 : Nat)
                    have hst_mod : (rs0' % nv).toNat < nv.toNat := by
                      rw [BitVec.toNat_umod]; exact Nat.mod_lt _ hnv_pos
                    have hadd_eq : ((rs0' % nv) + step_l).toNat =
                        (rs0' % nv).toNat + step_l.toNat := by
                      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
                    c0_hsteps_nogrp
                    c0_hsplit
                    · have hsub_eq : (((rs0' % nv) + step_l) - nv).toNat < nv.toNat := by
                        have hge : nv.toNat ≤ ((rs0' % nv) + step_l).toNat := by
                          simpa only [lift2, Arg.val] using (by
                            dsimp only [rs0', rx2, rx1]; exact hc : _)
                        rw [BitVec.toNat_sub, hadd_eq]
                        have hsub_nat : (2^32 - nv.toNat + ((rs0'%nv).toNat + step_l.toNat)) % 2^32 =
                            (rs0'%nv).toNat + step_l.toNat - nv.toNat := by omega
                        omega
                      c0_hsteps!
                      exact hJ_v (_, ()) ml
                        ⟨by dsimp only [rs0', rx2, rx1]; simpa only [lift2, Arg.val] using hsub_eq, rfl⟩
                    · have hlt_nv : ((rs0' % nv) + step_l).toNat < nv.toNat := by
                        have hnot : ¬ nv.toNat ≤ ((rs0' % nv) + step_l).toNat := by
                          dsimp only [rs0', rx2, rx1]
                          simpa only [lift2, Arg.val] using hc
                        omega
                      c0_hsteps!
                      exact hJ_v (_, ()) ml
                        ⟨by dsimp only [rs0', rx2, rx1]; simpa only [lift2, Arg.val] using hlt_nv, rfl⟩))
        · intro _ hJ_rng
          c0_hsplit
          · c0_hsplit
            · c0_hsteps!; exact hJ_rng (_, _, ()) ml rfl
            · c0_hsteps!; exact hJ_rng (rs_l, rb_l, ()) ml rfl
          · c0_hsteps!; exact hJ_rng (rs_l, rb_l, ()) ml rfl
  · intro _ hJ
    c0_hsplit
    · c0_hsteps!; exact hJ (0x9E3779B9#32, ()) m rfl
    · c0_hsteps!; exact hJ (_, ()) m rfl

/-! ## 4. `m8_sweep_sim_wp` (`2` sim rounds, single flip pass) -/

theorem m8_sweep_sim_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hSolve : M6EnvSpec Γ "full_m6_sweep_solve" m6SweepSolveSpec)
    (hRef : M6EnvSpec Γ "full_m6_sweep_refine_sig" m6SweepRefineSigSpec)
    (hFlipR : M6EnvSpec Γ "full_m6_sweep_flip_round" m6SweepFlipRoundSpec) :
    ∀ args m Q X, m6SweepSimSpec args m Q X →
      Func.wp Γ full_m6_sweep_sim_body args m Q X := by
  rintro ⟨h, nv, tlim, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hdw, hcone, hm, hQ⟩
  unfold Func.wp full_m6_sweep_sim_body
  have hlen := hdw.1
  have hcap : k6MinScr ≤ c.scratch_cap := by
    rcases Nat.lt_or_ge c.scratch_cap k6MinScr with hlt | hle
    · have h0 := k6MaxV_eq_zero hlt
      have h1 := hcone.1
      have h2 := hcone.2.1
      rw [hlen.scratch_ok.scratch_buf_len] at h2
      omega
    · exact hle
  have hcap_lt : c.scratch_cap < 2 ^ 64 := Nat.lt_trans c.hscr (by unfold dimacsBound; decide)
  c0_hsteps_nogrp
  refine m8_call_max_v_cap hMaxV (cap := BitVec.ofNat 64 c.scratch_cap) ?_
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap_lt]
  c0_hsplit
  · exfalso
    have := (k6MaxV_bounds hcap).1
    have h0 := congrArg BitVec.toNat (hc : (BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32 = 0#32)
    have hlt := (k6MaxV_bounds hcap).2.1
    rw [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at h0
    simp at h0; omega
  c0_hsplit
  · exfalso
    have hnv_le : nv.toNat ≤ k6MaxV c.scratch_cap := hlen.scratch_ok.scratch_buf_len ▸ hcone.2.1
    have hlt := (k6MaxV_bounds hcap).2.1
    have hgt : k6MaxV c.scratch_cap % 2 ^ 64 % 2 ^ 32 < nv.toNat := hc
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hgt
    omega
  c0_hsteps_nogrp
  have hws1_len := hlen.scratch_ok.work_stk1_len
  have hsig_len := hlen.scratch_ok.sim_sig_len
  have hcv_le := hlen.core_ok.cur_vars_le
  have hnv_le_mv : nv.toNat ≤ c.max_vars := Nat.le_trans hcone.2.2.1 hcv_le
  refine wp_loop_inv (ts := [i32])
    (fun (i_l, ()) mi => i_l.toNat ≤ nv.toNat ∧
      ∃ sig_l : List (BitVec 64), sig_l.length = c.max_vars ∧
        (FullMem c { s with scratch := { s.scratch with sim_sig := sig_l } } ⋆ R) mi)
    (fun (i_l, ()) _ => nv.toNat - i_l.toNat)
    (fun _ hJ_i => by
      c0_hsteps!
      exact hJ_i (0#32, ()) m ⟨Nat.zero_le _, s.scratch.sim_sig, hsig_len, hm⟩)
    (fun _ (i_l, ()) mi ⟨hi_le, sig_l, hsig_l, hmi⟩ hJ_i => by
      c0_hsplit; rotate_left
      · have hi_ge : ¬ i_l.toNat < nv.toNat := hc
        let si : FullState := { s with scratch := { s.scratch with sim_sig := sig_l } }
        have hlen_i : si.LengthsOk c :=
          ⟨hlen.core_ok, { hlen.scratch_ok with sim_sig_len := hsig_l }⟩
        have hdw_i : FullDenseInvW c F0 F_cur si := ⟨hlen_i, hdw.2.1, hdw.2.2⟩
        obtain ⟨hge_c, hlt_c, hKi⟩ := hcone.2.2.2.2.1
        have hscr_buf : s.scratch.scratch_buf.length = c.scratch_cap :=
          hlen.scratch_ok.scratch_buf_len
        let L : K6Layout := k6LayoutOfCap s.scratch.scratch_buf.length hge_c hlt_c
        have hL_len : L.scrLen = c.scratch_cap :=
          (k6LayoutOfCap_scrLen hge_c hlt_c).trans hscr_buf
        have hL_mv : L.maxV = k6MaxV c.scratch_cap := by
          rw [show L.maxV = k6MaxV s.scratch.scratch_buf.length from rfl, hscr_buf]
        have hkptr_c0 : c.pScratchBuf + BitVec.setWidth 64
            ((1280 : BitVec 32) + (BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) <<<
              (1 : Nat))) * 4 = L.kPtr c.pScratchBuf := by
          rw [← hL_mv, k6_mv32_zext]
          simpa only [show (1280 : BitVec 32) = 1280#32 from rfl] using k6_ptr_base_k6Base L c.pScratchBuf
        have hscr_i : si.scratch.scratch_buf.length = c.scratch_cap :=
          hlen_i.scratch_ok.scratch_buf_len
        have hscr_L : si.scratch.scratch_buf.length = L.scrLen := hscr_i.trans hL_len.symm
        let ks_0 := k6StateOfScratch L si.scratch.scratch_buf
        have hm_ka : (K6MemA L (L.kPtr c.pScratchBuf) ks_0 ⋆ (FullK6Frame c L si ⋆ R)) mi := by
          rw [fullMem_eq_k6Frame hscr_L] at hmi
          exact k6Mem_to_amem hKi.shapes (sep_ac hmi)
        c0_hsteps_nogrp
        try rw [hkptr_c0]
        c0_hsteps_nogrp
        let scr0 := si.scratch.scratch_buf.take L.k6Base ++ (ks_0.putHdr .nassump 0#32).toSlab
        let s0 : FullState := { si with scratch := { si.scratch with scratch_buf := scr0 } }
        obtain ⟨hlen0, _hpre0, hks0', hm0⟩ :=
          m8_k6_slab_exit (R := R) hlen_i hL_len (m8_k6Shapes_putHdr_nassump 0#32 hKi.shapes)
            (by assumption)
        have hK0' : K6Inv L (ConeModelSet F_cur s.scratch.work_stk1 nv.toNat)
            (k6StateOfScratch L scr0) := hks0' ▸ m8_k6Inv_putHdr_nassump_zero hKi
        have hcone_nv : ks_0.nv = nv := by
          obtain ⟨h1, h2, hnv_eq⟩ := hcone.2.2.2.2.2
          exact hnv_eq.trans (BitVec.eq_of_toNat_eq (by simp))
        have hnv0' : (k6StateOfScratch L scr0).nv = nv := by rw [hks0']; exact hcone_nv
        have hunsat_solve : ∀ (scr' : List (BitVec 32)),
            (k6StateOfScratch L scr').nassump = 0#32 →
            (∀ β, ConeModelSet F_cur s.scratch.work_stk1 nv.toNat β →
              ¬ CNF.Sat β (unitsCnf (k6AssumpLitsS L scr'))) →
            (cnfOfClauses F_cur).Unsat := fun scr' hna hneg => by
          have hlits : k6AssumpLitsS L scr' = [] := by
            unfold k6AssumpLitsS k6AssumpLits; rw [hna]; rfl
          rw [hlits] at hneg
          intro α
          exact Bool.eq_false_iff.mpr fun hsat =>
            hneg (fun i => α (s.scratch.work_stk1[i]?.getD 0#32).toNat)
              ⟨α, hsat, fun _ _ => rfl⟩ (by unfold unitsCnf; simp [CNF.Sat])
        refine m8_call_solve hSolve hlen0 hL_len hL_mv hK0' hnv0' hm0
          (fun r1 fuel1 rng1 scr1 m1 hlen1 hfuel1 hpre1 hK1 htrl1 hnv1 hna1 has1 hnq1
            hr1 hunsat1 hm1 => ?_)
        have hscr1 : scr1.length = c.scratch_cap := hlen1.scratch_ok.scratch_buf_len
        have hfuel1_le : fuel1.toNat ≤ s.core.fuel.toNat := hfuel1
        have hna1_0 : (k6StateOfScratch L scr1).nassump = 0#32 := by
          rw [hna1, hks0']; rfl
        have hscr1_eq : scr1.length = s.scratch.scratch_buf.length :=
          hscr1.trans hlen.scratch_ok.scratch_buf_len.symm
        have hdw1 : FullDenseInvW c F0 F_cur (m8SimState s fuel1 rng1 sig_l scr1) :=
          m8_denseInvW_set_sim hdw hsig_l hscr1
        have hcone1 : M6SweepConeOk F_cur (m8SimState s fuel1 rng1 sig_l scr1) nv.toNat :=
          m8_coneOk_of_k6 hcone hscr1_eq hK1 hnv1
        c0_hsplit
        · have hr1_20 : r1 = 20#64 := hc
          c0_hsteps!
          exact hQ 4294967295#32 fuel1 rng1 sig_l scr1 m1 hdw1 hfuel1_le hcone1
            (fun _ => hunsat_solve scr1 hna1_0 (hunsat1 hr1_20))
            (fun h => absurd rfl h) hm1
        · have hr1_ne20 : ¬ r1 = 20#64 := hc
          c0_hsplit
          · c0_hsteps!
            exact hQ 0#32 fuel1 rng1 sig_l scr1 m1 hdw1 hfuel1_le hcone1
              (fun h => by simp at h) (fun _ => by simp) hm1
          · have hr1_10 : r1 = 10#64 := hc
            refine m8_call_refine_sig hRef hlen1 hcap
              (by rw [← hL_mv]; exact hnv1 ▸ hK1.clauses.nv_le)
              (Nat.le_trans hnv_le_mv (by omega)) hcone.2.2.2.1 hm1
              (fun sig2 m2 hsig2 hm2 => ?_)
            have hk11_ptr := m8_k11_ptr (c := c) (L := L) hL_len
            have hk11_idx := m8_k11_idx (c := c) (L := L) hL_len
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i64]) (fun (_tl_c, ()) mt => mt = m2)
              (fun _ (tl_c, ()) mt hmt => by
                subst mt
                c0_hsteps_nogrp
                refine wp_join_group (ts := [i32, i32])
                  (fun (r_o, _rd_o, ()) mo => r_o.toNat ≤ 64 ∧
                    ∃ (fuel_o rng_o : BitVec 64) (sig_o : List (BitVec 64))
                      (scr_o : List (BitVec 32)),
                      fuel_o.toNat ≤ s.core.fuel.toNat ∧
                      sig_o.length = c.max_vars ∧ scr_o.length = c.scratch_cap ∧
                      K6Inv L (ConeModelSet F_cur s.scratch.work_stk1 nv.toNat)
                        (k6StateOfScratch L scr_o) ∧
                      (k6StateOfScratch L scr_o).nv = nv ∧
                      (FullMem c (m8SimState s fuel_o rng_o sig_o scr_o) ⋆ R) mo)
                  (fun _ (r_o, _rd_o, ()) mo ⟨hr_o_le, fuel_o, rng_o, sig_o, scr_o,
                      hfl_o, hsig_o, hscr_o, hK_o, hnv_o, hm_o⟩ => by
                    c0_hsteps!
                    exact hQ r_o fuel_o rng_o sig_o scr_o mo
                      (m8_denseInvW_set_sim hdw hsig_o hscr_o) hfl_o
                      (m8_coneOk_of_k6 hcone (hscr_o.trans hlen.scratch_ok.scratch_buf_len.symm)
                        hK_o hnv_o)
                      (fun h => False.elim (by rw [h] at hr_o_le; simp at hr_o_le))
                      (fun _ => hr_o_le) hm_o)
                  (fun _ hJ_ret => by
                    c0_hsteps_nogrp
                    refine wp_loop_inv (ts := [i32, i32])
                      (fun (r_l, rd_l, ()) ml =>
                        rd_l.toNat ≤ 2 ∧ r_l.toNat ≤ 64 ∧
                        ∃ (fuel_l rng_l : BitVec 64) (sig_l' : List (BitVec 64))
                          (scr_l : List (BitVec 32)),
                          fuel_l.toNat ≤ s.core.fuel.toNat ∧
                          sig_l'.length = c.max_vars ∧ scr_l.length = c.scratch_cap ∧
                          K6Inv L (ConeModelSet F_cur s.scratch.work_stk1 nv.toNat)
                            (k6StateOfScratch L scr_l) ∧
                          (k6StateOfScratch L scr_l).nv = nv ∧
                          (k6StateOfScratch L scr_l).nassump = 0#32 ∧
                          (FullMem c (m8SimState s fuel_l rng_l sig_l' scr_l) ⋆ R) ml)
                      (fun (_, rd_l, ()) _ => 2 - rd_l.toNat)
                      (fun _ hJ_rd => by
                        c0_hsteps!
                        exact hJ_rd (1#32, 0#32, ()) m2
                          ⟨by decide, by decide, fuel1, rng1, sig2, scr1,
                            hfuel1_le, hsig2, hscr1, hK1, hnv1, hna1_0, hm2⟩)
                      (fun _ (r_l, rd_l, ()) ml ⟨hrd_le, hr_le, fuel_l, rng_l, sig_l', scr_l,
                          hfl_l, hsig_l', hscr_l, hK_l, hnv_l, hna_l, hm_l⟩ hJ_rd => by
                        let s_l : FullState := m8SimState s fuel_l rng_l sig_l' scr_l
                        have hlen_l : s_l.LengthsOk c :=
                          (m8_denseInvW_set_sim hdw hsig_l' hscr_l).1
                        have hk11_sl : (BitVec.setWidth 64
                            (BitVec.ofNat 32 (L.k6Base + 11))).toNat <
                            s_l.scratch.scratch_buf.length := hscr_l ▸ hk11_idx
                        have h_ret_st :
                            r_l.toNat ≤ 64 ∧ ∃ fuel_o rng_o sig_o scr_o,
                              fuel_o.toNat ≤ s.core.fuel.toNat ∧
                              sig_o.length = c.max_vars ∧ scr_o.length = c.scratch_cap ∧
                              K6Inv L (ConeModelSet F_cur s.scratch.work_stk1 nv.toNat)
                                (k6StateOfScratch L scr_o) ∧
                              (k6StateOfScratch L scr_o).nv = nv ∧
                              (FullMem c (m8SimState s fuel_o rng_o sig_o scr_o) ⋆ R) ml :=
                          ⟨hr_le, fuel_l, rng_l, sig_l', scr_l,
                            hfl_l, hsig_l', hscr_l, hK_l, hnv_l, hm_l⟩
                        c0_hsplit
                        · have hrd_lt : rd_l.toNat < 2 := hc
                          c0_hsplit
                          · have hr_lt : r_l.toNat < 64 := hc
                            c0_hsteps_nogrp
                            try rw [hk11_ptr]
                            c0_hsteps_nogrp <;> (try exact hJ_ret (r_l, rd_l, ()) ml h_ret_st)
                            refine wp_join_group (ts := [i32])
                              (fun (r1_l, ()) m44 => r1_l.toNat ≤ 64 ∧
                                ∃ (rng44 : BitVec 64) (sig44 : List (BitVec 64))
                                  (scr44 : List (BitVec 32)),
                                  sig44.length = c.max_vars ∧ scr44.length = c.scratch_cap ∧
                                  K6Inv L (ConeModelSet F_cur s.scratch.work_stk1 nv.toNat)
                                    (k6StateOfScratch L scr44) ∧
                                  (k6StateOfScratch L scr44).nv = nv ∧
                                  (k6StateOfScratch L scr44).nassump = 0#32 ∧
                                  (FullMem c (m8SimState s fuel_l rng44 sig44 scr44) ⋆ R) m44)
                              (fun _ (r1_l, ()) m44 ⟨hr1_le, rng44, sig44, scr44, hsig44, hscr44,
                                  hK44, hnv44, hna44, hm44⟩ => by
                                let s44 : FullState := m8SimState s fuel_l rng44 sig44 scr44
                                have hlen44 : s44.LengthsOk c :=
                                  (m8_denseInvW_set_sim hdw hsig44 hscr44).1
                                have hk11_s44 : (BitVec.setWidth 64
                                    (BitVec.ofNat 32 (L.k6Base + 11))).toNat <
                                    s44.scratch.scratch_buf.length := hscr44 ▸ hk11_idx
                                have hrd1 : (rd_l + 1#32).toNat = rd_l.toNat + 1 :=
                                  bv32_add1_toNat (by omega)
                                have hrd1_le : (rd_l + 1#32).toNat ≤ 2 := by rw [hrd1]; omega
                                c0_hsteps_nogrp
                                try rw [hk11_ptr]
                                c0_hsteps_nogrp
                                refine wp_join_group (ts := [i32])
                                  (fun (r2_l, ()) m52 => r2_l.toNat ≤ 64 ∧
                                    ∃ (fuel52 rng52 : BitVec 64) (sig52 : List (BitVec 64))
                                      (scr52 : List (BitVec 32)),
                                      fuel52.toNat ≤ s.core.fuel.toNat ∧
                                      sig52.length = c.max_vars ∧ scr52.length = c.scratch_cap ∧
                                      K6Inv L (ConeModelSet F_cur s.scratch.work_stk1 nv.toNat)
                                        (k6StateOfScratch L scr52) ∧
                                      (k6StateOfScratch L scr52).nv = nv ∧
                                      (k6StateOfScratch L scr52).nassump = 0#32 ∧
                                      (FullMem c (m8SimState s fuel52 rng52 sig52 scr52) ⋆ R) m52)
                                  (fun _ (r2_l, ()) m52 ⟨hr2_le, fuel52, rng52, sig52, scr52,
                                      hfl52, hsig52, hscr52, hK52, hnv52, hna52, hm52⟩ => by
                                    c0_hsteps!
                                    exact hJ_rd (r2_l, rd_l + 1#32, ()) m52
                                      (by dsimp only; rw [hrd1]; omega)
                                      ⟨hrd1_le, hr2_le, fuel52, rng52, sig52, scr52,
                                        hfl52, hsig52, hscr52, hK52, hnv52, hna52, hm52⟩)
                                  (fun _ hJ52 => by
                                    have hskip52 : r1_l.toNat ≤ 64 ∧
                                        ∃ fuel52 rng52 sig52 scr52,
                                          fuel52.toNat ≤ s.core.fuel.toNat ∧
                                          sig52.length = c.max_vars ∧
                                          scr52.length = c.scratch_cap ∧
                                          K6Inv L (ConeModelSet F_cur s.scratch.work_stk1 nv.toNat)
                                            (k6StateOfScratch L scr52) ∧
                                          (k6StateOfScratch L scr52).nv = nv ∧
                                          (k6StateOfScratch L scr52).nassump = 0#32 ∧
                                          (FullMem c (m8SimState s fuel52 rng52 sig52 scr52) ⋆
                                            R) m44 :=
                                      ⟨hr1_le, fuel_l, rng44, sig44, scr44,
                                        hfl_l, hsig44, hscr44, hK44, hnv44, hna44, hm44⟩
                                    c0_hsplit
                                    · c0_hsplit
                                      · have hr1_lt : r1_l.toNat < 64 := hc
                                        c0_hsteps_nogrp <;> (try exact hJ52 (r1_l, ()) m44 hskip52)
                                        have hscr44_L : s44.scratch.scratch_buf.length = L.scrLen :=
                                          hscr44.trans hL_len.symm
                                        let ks44 := k6StateOfScratch L scr44
                                        have hm_ka4 : (K6MemA L (L.kPtr c.pScratchBuf) ks44 ⋆
                                            (FullK6Frame c L s44 ⋆ R)) m44 := by
                                          rw [fullMem_eq_k6Frame hscr44_L] at hm44
                                          exact k6Mem_to_amem hK44.shapes (sep_ac hm44)
                                        c0_hsteps_nogrp
                                        let scr44' := scr44.take L.k6Base ++
                                          (ks44.putHdr .nassump 0#32).toSlab
                                        let s44' : FullState :=
                                          { s44 with scratch :=
                                            { s44.scratch with scratch_buf := scr44' } }
                                        obtain ⟨hlen44', _hpre44, hks44', hm44'⟩ :=
                                          m8_k6_slab_exit (R := R) hlen44 hL_len
                                            (m8_k6Shapes_putHdr_nassump 0#32 hK44.shapes)
                                            (by assumption)
                                        have hK44' : K6Inv L (ConeModelSet F_cur s.scratch.work_stk1
                                            nv.toNat) (k6StateOfScratch L scr44') :=
                                          hks44' ▸ m8_k6Inv_putHdr_nassump_zero hK44
                                        have hnv44' : (k6StateOfScratch L scr44').nv = nv := by
                                          rw [hks44']; exact hnv44
                                        refine m8_call_solve hSolve hlen44' hL_len hL_mv hK44'
                                          hnv44' hm44'
                                          (fun r5 fuel5 rng5 scr5 m5 hlen5 hfuel5 hpre5 hK5 htrl5
                                            hnv5 hna5 has5 hnq5 hr5 hunsat5 hm5 => ?_)
                                        have hscr5 : scr5.length = c.scratch_cap :=
                                          hlen5.scratch_ok.scratch_buf_len
                                        have hfuel5_le : fuel5.toNat ≤ s.core.fuel.toNat :=
                                          Nat.le_trans hfuel5 hfl_l
                                        have hna5_0 : (k6StateOfScratch L scr5).nassump = 0#32 := by
                                          rw [hna5, hks44']; rfl
                                        have hscr5_eq : scr5.length = s.scratch.scratch_buf.length :=
                                          hscr5.trans hlen.scratch_ok.scratch_buf_len.symm
                                        c0_hsplit
                                        · have hr5_20 : r5 = 20#64 := hc
                                          c0_hsteps!
                                          exact hQ 4294967295#32 fuel5 rng5 sig44 scr5 m5
                                            (m8_denseInvW_set_sim hdw hsig44 hscr5) hfuel5_le
                                            (m8_coneOk_of_k6 hcone hscr5_eq hK5 hnv5)
                                            (fun _ => hunsat_solve scr5 hna5_0 (hunsat5 hr5_20))
                                            (fun h => absurd rfl h) hm5
                                        · c0_hsplit
                                          · c0_hsteps!
                                            exact hJ_ret (r1_l, rd_l + 1#32, ()) m5
                                              ⟨Nat.le_of_lt hr1_lt, fuel5, rng5, sig44, scr5,
                                                hfuel5_le, hsig44, hscr5, hK5, hnv5, hm5⟩
                                          · refine m8_call_refine_sig hRef hlen5 hcap
                                              (by rw [← hL_mv]; exact hnv5 ▸ hK5.clauses.nv_le)
                                              (Nat.le_trans hnv_le_mv (by omega))
                                              hcone.2.2.2.1 hm5
                                              (fun sig6 m6 hsig6 hm6 => ?_)
                                            have hr1_p1 : (r1_l + 1#32).toNat ≤ 64 := by
                                              rw [bv32_add1_toNat (by omega)]; omega
                                            c0_hsteps!
                                            exact hJ52 (r1_l + 1#32, ()) m6
                                              ⟨hr1_p1, fuel5, rng5, sig6, scr5, hfuel5_le, hsig6,
                                                hscr5, hK5, hnv5, hna5_0, hm6⟩
                                      · c0_hsteps!; exact hJ52 (r1_l, ()) m44 hskip52
                                    · c0_hsteps!; exact hJ52 (r1_l, ()) m44 hskip52))
                              (fun _ hJ44 => by
                                c0_hsteps_nogrp
                                refine m8_call_flip_round hFlipR hlen_l hL_len hL_mv hK_l hnv_l
                                  hm_l (fun rflip rng_f scr_f m_f hlen_f hpre_f hK_f hnv_f
                                    hna_f has_f hnq_f hm_f => ?_)
                                have hscr_f : scr_f.length = c.scratch_cap :=
                                  hlen_f.scratch_ok.scratch_buf_len
                                have hna_f0 : (k6StateOfScratch L scr_f).nassump = 0#32 :=
                                  hna_f.trans hna_l
                                have hr1_p1 : (r_l + 1#32).toNat ≤ 64 := by
                                  rw [bv32_add1_toNat (by omega)]; omega
                                c0_hsplit
                                · c0_hsteps_nogrp
                                  refine m8_call_refine_sig hRef hlen_f hcap
                                    (by rw [← hL_mv]; exact hnv_f ▸ hK_f.clauses.nv_le)
                                    (Nat.le_trans hnv_le_mv (by omega))
                                    hcone.2.2.2.1 hm_f
                                    (fun sig_r m_r hsig_r hm_r => ?_)
                                  c0_hsteps!
                                  exact hJ44 (r_l + 1#32, ()) m_r
                                    ⟨hr1_p1, rng_f, sig_r, scr_f, hsig_r, hscr_f,
                                      hK_f, hnv_f, hna_f0, hm_r⟩
                                · c0_hsteps!
                                  exact hJ44 (r_l, ()) m_f
                                    ⟨Nat.le_of_lt hr_lt, rng_f, sig_l', scr_f, hsig_l', hscr_f,
                                      hK_f, hnv_f, hna_f0, hm_f⟩)
                          · c0_hsteps_nogrp
                            exact hJ_ret (r_l, rd_l, ()) ml h_ret_st
                        · c0_hsteps_nogrp
                          exact hJ_ret (r_l, rd_l, ()) ml h_ret_st)))
              (fun _ hJt => by
                c0_hsplit
                · c0_hsteps!; exact hJt (tlim, ()) m2 rfl
                · c0_hsteps!; exact hJt (2048#64, ()) m2 rfl)
      · have hi_lt : i_l.toNat < nv.toNat := hc
        have hi_ws1 : (i_l.setWidth 64).toNat < s.scratch.work_stk1.length := by
          rw [hws1_len, BitVec.toNat_setWidth,
            Nat.mod_eq_of_lt (by have := maxVars_lt_2p31 c; omega)]
          omega
        let rv := s.scratch.work_stk1[(i_l.setWidth 64).toNat]'hi_ws1
        have hrv_lt : rv.toNat < s.core.cur_vars := by
          have hi_m : (i_l.setWidth 64).toNat = i_l.toNat := by
            rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := maxVars_lt_2p31 c; omega)]
          have hbd := hcone.2.2.2.1 i_l.toNat hi_lt
          rw [← hi_m, List.getElem?_eq_getElem hi_ws1, Option.getD_some] at hbd
          exact hbd
        have hrv_sig : (rv.setWidth 64).toNat < sig_l.length := by
          rw [hsig_l, BitVec.toNat_setWidth,
            Nat.mod_eq_of_lt (by have := maxVars_lt_2p31 c; omega)]
          exact Nat.lt_of_lt_of_le hrv_lt hcv_le
        have hi1 : (i_l + 1#32).toNat = i_l.toNat + 1 :=
          bv32_add1_toNat (by have := maxVars_lt_2p31 c; omega)
        c0_hsteps!
        exact hJ_i (i_l + 1#32, ()) _ (by dsimp only; rw [hi1]; omega)
          ⟨by rw [hi1]; omega, sig_l.set (rv.setWidth 64).toNat 0#64,
            by simp [hsig_l], by assumption⟩)

/-! ## 5. `m8_collect_cands_wp` (`0 < deg <= 1024`, `fl[]` read-only) -/

theorem m8_collect_cands_wp (Γ : Env)
    (hSift : M6EnvSpec Γ "full_m6_cand_sift" m6CandSiftSpec) :
    ∀ args m Q X, m6CollectCandsSpec args m Q X →
      Func.wp Γ full_m6_collect_cands_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  unfold Func.wp full_m6_collect_cands_body
  have hmx := maxVars_lt_2p31 c
  have hcv_le := hlen.core_ok.cur_vars_le
  have hcv_lt : s.core.cur_vars < 2 ^ 31 := Nat.lt_of_le_of_lt hcv_le hmx
  have hcv_2p64 : s.core.cur_vars < 2 ^ 64 := by omega
  have hfl_len := hlen.core_ok.flags_len
  have hwvec_len := hlen.core_ok.wvec_len
  have htrc_len := hlen.scratch_ok.tarjan_reach_len
  have hws2_len := hlen.scratch_ok.work_stk2_len
  c0_hsteps_nogrp
  c0_hsplit
  · c0_hsteps!
    exact hQ 0#32 s.scratch.tarjan_reach s.scratch.work_stk2 m hlen (Nat.zero_le _)
      (fun _ hi => absurd hi (by simp)) hm
  c0_hsteps_nogrp
  refine wp_loop_inv (ts := [i32, i64])
    (fun (nc_l, v_l, ()) ml =>
      v_l.toNat ≤ s.core.cur_vars ∧ nc_l.toNat ≤ v_l.toNat ∧
      ∃ trc_l ws2_l : List (BitVec 32),
        trc_l.length = 2 * c.max_vars ∧ ws2_l.length = 2 * c.max_vars ∧
        (∀ i < nc_l.toNat, (trc_l[i]?.getD 0#32).toNat < v_l.toNat) ∧
        (FullMem c { s with scratch := { s.scratch with
          tarjan_reach := trc_l, work_stk2 := ws2_l } } ⋆ R) ml)
    (fun (_, v_l, ()) _ => s.core.cur_vars - v_l.toNat)
    ?_ ?_
  · intro _ hJ_in
    c0_hsteps!
    refine hJ_in (0#32, 0#64, ()) m ⟨Nat.zero_le _, by simp,
      s.scratch.tarjan_reach, s.scratch.work_stk2, htrc_len, hws2_len,
      fun _ hi => absurd (by simp at hi) False.elim, hm⟩
  · rintro _ ⟨nc_l, v_l, ⟨⟩⟩ ml ⟨hv_le, hnc_le, trc_l, ws2_l, htrc_l, hws2_l, hbd_l, hm_l⟩ hJ_in
    have hnc_bd : nc_l.toNat ≤ s.core.cur_vars := Nat.le_trans hnc_le hv_le
    have hlen_l : ({ s with scratch := { s.scratch with
        tarjan_reach := trc_l, work_stk2 := ws2_l } } : FullState).LengthsOk c :=
      m8_lengthsOk_trc_ws2 hlen htrc_l hws2_l
    c0_hsplit; rotate_left
    · have hge : s.core.cur_vars ≤ v_l.toNat := by
        have hnot : ¬ v_l.toNat < s.core.cur_vars % 2 ^ 64 := hc
        rw [Nat.mod_eq_of_lt hcv_2p64] at hnot; omega
      have hbd_cv : ∀ i < nc_l.toNat, (trc_l[i]?.getD 0#32).toNat < s.core.cur_vars :=
        fun i hi => Nat.lt_of_lt_of_le (hbd_l i hi) hv_le
      c0_hsplit
      · c0_hsteps!
        exact hQ nc_l trc_l ws2_l ml hlen_l hnc_bd hbd_cv hm_l
      · have hnc_ge2 : 2 ≤ nc_l.toNat := by
          have : ¬ nc_l.toNat < 2 := hc; omega
        have hnc_half : (nc_l >>> (1 : Nat)).toNat = nc_l.toNat / 2 := bv32_lshr1_toNat nc_l
        c0_hsteps_nogrp
        refine wp_loop_inv (ts := [i32])
          (fun (st_s, ()) ms => st_s.toNat ≤ nc_l.toNat / 2 ∧
            ∃ trc_s : List (BitVec 32), trc_s.length = 2 * c.max_vars ∧
              (∀ i < nc_l.toNat, (trc_s[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
              (FullMem c { s with scratch := { s.scratch with
                tarjan_reach := trc_s, work_stk2 := ws2_l } } ⋆ R) ms)
          (fun (st_s, ()) _ => st_s.toNat)
          ?_ ?_
        · intro _ hJs
          c0_hsteps!
          exact hJs (nc_l >>> (1 : Nat), ()) ml
            ⟨by rw [hnc_half]; exact Nat.le_refl _, trc_l, htrc_l, hbd_cv, hm_l⟩
        · rintro _ ⟨st_s, ⟨⟩⟩ ms ⟨hst_le, trc_s, htrc_s, hbd_s, hm_s⟩ hJs
          c0_hsplit; rotate_left
          · have hst0 : ¬ 0 < st_s.toNat := hc
            c0_hsteps_nogrp
            refine wp_loop_inv (ts := [i32])
              (fun (end_s, ()) me => end_s.toNat ≤ nc_l.toNat ∧
                ∃ trc_e : List (BitVec 32), trc_e.length = 2 * c.max_vars ∧
                  (∀ i < nc_l.toNat, (trc_e[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
                  (FullMem c { s with scratch := { s.scratch with
                    tarjan_reach := trc_e, work_stk2 := ws2_l } } ⋆ R) me)
              (fun (end_s, ()) _ => end_s.toNat)
              ?_ ?_
            · intro _ hJe
              c0_hsteps!
              exact hJe (nc_l, ()) ms ⟨Nat.le_refl _, trc_s, htrc_s, hbd_s, hm_s⟩
            · rintro _ ⟨end_s, ⟨⟩⟩ me ⟨hend_le, trc_e, htrc_e, hbd_e, hm_e⟩ hJe
              c0_hsplit; rotate_left
              · have h_end_le1 : ¬ 1 < end_s.toNat := hc
                c0_hsteps!
                exact hQ nc_l trc_e ws2_l me (m8_lengthsOk_trc_ws2 hlen htrc_e hws2_l)
                  hnc_bd hbd_e hm_e
              · have h_end_gt1 : 1 < end_s.toNat := hc
                have hend1 : (end_s - 1#32).toNat = end_s.toNat - 1 := by bv_omega
                have hend1_lt : (end_s - 1#32).toNat < trc_e.length := by rw [htrc_e]; omega
                have h0_lt : 0 < trc_e.length := by rw [htrc_e]; omega
                let trc_sw :=
                  (trc_e.set 0 (trc_e[(end_s - 1#32).toNat]'hend1_lt)).set
                    (end_s - 1#32).toNat (trc_e[0]'h0_lt)
                have hsw_len : trc_sw.length = 2 * c.max_vars := by simp [trc_sw, htrc_e]
                have hsw_bd : ∀ i < nc_l.toNat, (trc_sw[i]?.getD 0#32).toNat < s.core.cur_vars := by
                  intro i hi
                  by_cases hi1 : i = (end_s - 1#32).toNat
                  · subst hi1
                    rw [List.getElem?_set_self (by simp; rw [htrc_e]; omega), Option.getD_some]
                    have h0 := hbd_e 0 (by omega)
                    rwa [List.getElem?_eq_getElem h0_lt, Option.getD_some] at h0
                  · rw [List.getElem?_set_ne (Ne.symm hi1)]
                    by_cases hi0 : i = 0
                    · subst hi0
                      rw [List.getElem?_set_self h0_lt, Option.getD_some]
                      have h1 := hbd_e (end_s - 1#32).toNat (by omega)
                      rwa [List.getElem?_eq_getElem hend1_lt, Option.getD_some] at h1
                    · rw [List.getElem?_set_ne (Ne.symm hi0)]
                      exact hbd_e i hi
                rw [fullMem_eq_candsFrame] at hm_e
                c0_hsteps_nogrp
                have h_1eq : end_s - (1 : BitVec 32) = end_s - 1#32 := rfl
                have h_0eq : (BitVec.ofNat 64 0).toNat = 0 := rfl
                have h_seq : (BitVec.setWidth 64 (end_s - 1#32)).toNat = (end_s - 1#32).toNat := by
                  bv_omega
                dsimp only [trc_sw] at *
                rw [h_1eq, h_0eq, h_seq] at *
                let k : Nat := (end_s - 1#32).toNat
                have hk_le : k ≤ trc_sw.length := by rw [hsw_len]; omega
                have h0_lt_end1 : (0#32 : BitVec 32).toNat < k := by
                  change 0 < (end_s - 1#32).toNat; omega
                have htake_len : (trc_sw.take k).length = k := List.length_take_of_le hk_le
                have hsw_bd_end : ∀ i < k,
                    ((trc_sw.take k)[i]?.getD 0#32).toNat < s.core.cur_vars := fun i hi => by
                  rw [List.getElem?_take_of_lt hi]; exact hsw_bd i (by omega)
                refine m8_call_cand_sift hSift 0#32 (end_s - 1#32) h0_lt_end1
                  (by rw [htake_len]; exact Nat.le_refl _) (by omega)
                  (by rw [hws2_l]; omega) hsw_bd_end
                  (R := array (t := i32) (c.pTarjanReach + BitVec.ofNat 64 (4 * k))
                    (trc_sw.drop k) ⋆ FullCandsFrame c s ⋆ (R ⋆ emp))
                  (m8_cands_split_mem (R := R ⋆ emp) hk_le (sep_ac (by assumption)))
                  (fun trc_p m' hlen_p hbd_p hm' => ?_)
                have hlen_pk : trc_p.length = k := hlen_p.trans htake_len
                let trc' := trc_p ++ trc_sw.drop k
                have htrc'_len : trc'.length = 2 * c.max_vars := by
                  dsimp only [trc']
                  rw [List.length_append, hlen_pk, List.length_drop, hsw_len]; omega
                have hbd'_all : ∀ i < nc_l.toNat, (trc'[i]?.getD 0#32).toNat < s.core.cur_vars := by
                  intro i hi
                  dsimp only [trc']
                  by_cases hik : i < k
                  · rw [List.getElem?_append_left (by rw [hlen_pk]; exact hik)]
                    exact hbd_p i hik
                  · rw [List.getElem?_append_right (by rw [hlen_pk]; omega), hlen_pk,
                      List.getElem?_drop]
                    rw [show k + (i - k) = i by omega]
                    exact hsw_bd i hi
                have hjoin_arr := fullCands_join_array (a := c.pTarjanReach)
                  (suff := trc_sw.drop k) hlen_pk
                have hm_joined : (FullMem c { s with scratch := { s.scratch with
                    tarjan_reach := trc', work_stk2 := ws2_l } } ⋆ R) m' := by
                  rw [fullMem_eq_candsFrame]
                  change (array (t := i32) c.pTarjanReach (trc_p ++ trc_sw.drop k) ⋆
                    array (t := i32) c.pWorkStk2 ws2_l ⋆ FullCandsFrame c s) ⋆ R $ m'
                  rw [← hjoin_arr]
                  exact sep_ac hm'
                c0_hsteps!
                exact hJe (end_s - 1#32, ()) m' (by dsimp only; omega)
                  ⟨by rw [hend1]; omega, trc', htrc'_len, hbd'_all, hm_joined⟩
          · have hst_pos : 0 < st_s.toNat := hc
            have hst_sub : (st_s - 1#32).toNat = st_s.toNat - 1 := by bv_omega
            have hst_lt : (st_s - 1#32).toNat < nc_l.toNat := by omega
            rw [fullMem_eq_candsFrame] at hm_s
            have hm_split : (array (t := i32) c.pTarjanReach trc_s ⋆
                array (t := i32) c.pWorkStk2 ws2_l ⋆ (FullCandsFrame c s ⋆ R)) ms := sep_ac hm_s
            c0_hsteps_nogrp
            refine m8_call_cand_sift hSift (st_s - 1#32) nc_l hst_lt
              (by rw [htrc_s]; omega) (by omega) (by rw [hws2_l]; omega) hbd_s hm_split
              (fun trc' m' hlen' hbd' hm' => ?_)
            c0_hsteps!
            have hm_re : (FullMem c { s with scratch := { s.scratch with
                tarjan_reach := trc', work_stk2 := ws2_l } } ⋆ R) m' := by
              rw [fullMem_eq_candsFrame]; exact sep_ac hm'
            exact hJs (st_s - 1#32, ()) m' (by dsimp only; omega)
              ⟨by rw [hst_sub]; omega, trc', hlen'.trans htrc_s, hbd', hm_re⟩
    · have hv_lt : v_l.toNat < s.core.cur_vars := by
        have hlt : v_l.toNat < s.core.cur_vars % 2 ^ 64 := hc
        rwa [Nat.mod_eq_of_lt hcv_2p64] at hlt
      have hv1 : (v_l + 1#64).toNat = v_l.toNat + 1 := bv64_add1_toNat (by omega)
      refine wp_join_group (ts := [i32])
        (fun (nc', ()) mj => nc'.toNat ≤ v_l.toNat + 1 ∧
          ∃ trc' ws2' : List (BitVec 32), trc'.length = 2 * c.max_vars ∧
            ws2'.length = 2 * c.max_vars ∧
            (∀ i < nc'.toNat, (trc'[i]?.getD 0#32).toNat < v_l.toNat + 1) ∧
            (FullMem c { s with scratch := { s.scratch with
              tarjan_reach := trc', work_stk2 := ws2' } } ⋆ R) mj)
        (fun _ (nc', ()) mj ⟨hnc', trc', ws2', htrc', hws2', hbd', hm'⟩ => by
          c0_hsteps!
          exact hJ_in (nc', v_l + 1#64, ()) mj (by dsimp only; rw [hv1]; omega)
            ⟨by rw [hv1]; exact hv_lt, by rw [hv1]; exact hnc', trc', ws2', htrc', hws2',
              by rw [hv1]; exact hbd', hm'⟩)
        (fun _ hJ_v => by
          have hv_fl : v_l.toNat < s.core.flags.length := by rw [hfl_len]; omega
          have hvals_len := hlen.core_ok.vals_len
          have hv_vals : (v_l <<< (1 : Nat)).toNat < s.core.vals.length := by
            rw [bv64_shl1_toNat (by omega), hvals_len]; omega
          have hpos_bd : (((v_l <<< (1 : BitVec 64)) <<< (1 : BitVec 64)) +
              (1 : BitVec 64)).toNat < s.core.wvec.length := by
            rw [bv64_wvec_pos_bv_toNat (by omega), hwvec_len]; omega
          have hneg_bd : ((((v_l <<< (1 : BitVec 64)) ||| (1 : BitVec 64)) <<<
              (1 : BitVec 64)) + (1 : BitVec 64)).toNat < s.core.wvec.length := by
            rw [bv64_wvec_neg_bv_toNat (by omega), hwvec_len]; omega
          c0_hsteps_nogrp <;> try exact hJ_v (nc_l, ()) ml ⟨Nat.le_succ_of_le hnc_le,
            trc_l, ws2_l, htrc_l, hws2_l, fun i hi => Nat.lt_succ_of_lt (hbd_l i hi), hm_l⟩
          refine wp_join_group (ts := [i32])
            (fun (nc', ()) mj => nc'.toNat ≤ v_l.toNat + 1 ∧
              ∃ trc' ws2' : List (BitVec 32), trc'.length = 2 * c.max_vars ∧
                ws2'.length = 2 * c.max_vars ∧
                (∀ i < nc'.toNat, (trc'[i]?.getD 0#32).toNat < v_l.toNat + 1) ∧
                (FullMem c { s with scratch := { s.scratch with
                  tarjan_reach := trc', work_stk2 := ws2' } } ⋆ R) mj)
            (fun _ (nc', ()) mj hinv_j => by
              c0_hsteps_nogrp; exact hJ_v (nc', ()) mj hinv_j)
            (fun _ hJ2 => by
              have h_skip_p : nc_l.toNat ≤ v_l.toNat + 1 ∧
                  ∃ trc' ws2' : List (BitVec 32), trc'.length = 2 * c.max_vars ∧
                    ws2'.length = 2 * c.max_vars ∧
                    (∀ i < nc_l.toNat, (trc'[i]?.getD 0#32).toNat < v_l.toNat + 1) ∧
                    (FullMem c { s with scratch := { s.scratch with
                      tarjan_reach := trc', work_stk2 := ws2' } } ⋆ R) ml :=
                ⟨Nat.le_succ_of_le hnc_le, trc_l, ws2_l, htrc_l, hws2_l,
                  fun i hi => Nat.lt_succ_of_lt (hbd_l i hi), hm_l⟩
              c0_hsteps_nogrp <;> try exact hJ2 (nc_l, ()) ml h_skip_p
              have hnc1 : (nc_l + 1#32).toNat = nc_l.toNat + 1 := bv32_add1_toNat (by omega)
              have hv_ws2 : v_l.toNat < ws2_l.length := by rw [hws2_l]; omega
              have hnc_trc : (nc_l.setWidth 64).toNat < trc_l.length := by
                rw [htrc_l, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; omega
              refine wp_join_group (ts := [i32]) (fun (_, ()) mp => mp = ml)
                (fun _ (sc, ()) mp hmp => by
                  subst mp
                  have hm_f := hm_l
                  rw [fullMem_eq_candsFrame] at hm_f
                  c0_hsteps_nogrp
                  have hws2_s : (ws2_l.set v_l.toNat sc).length = 2 * c.max_vars := by
                    simp [hws2_l]
                  have htrc_s : (trc_l.set (nc_l.setWidth 64).toNat
                      (BitVec.setWidth 32 v_l)).length = 2 * c.max_vars := by
                    simp [htrc_l]
                  have hnc_trc0 : nc_l.toNat < trc_l.length := by rw [htrc_l]; omega
                  have hbd_s : ∀ i < (nc_l + 1#32).toNat,
                      ((trc_l.set (nc_l.setWidth 64).toNat (BitVec.setWidth 32 v_l))[i]?.getD
                        0#32).toNat < v_l.toNat + 1 := fun i hi => by
                    rw [hnc1] at hi
                    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                    by_cases hie : i = nc_l.toNat
                    · subst hie
                      rw [List.getElem?_set_self hnc_trc0, Option.getD_some,
                        BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                      omega
                    · rw [List.getElem?_set_ne (Ne.symm hie)]
                      exact Nat.lt_succ_of_lt (hbd_l i (by omega))
                  refine hJ2 (nc_l + 1#32, ()) _
                    ⟨by rw [hnc1]; omega, _, _, htrc_s, hws2_s, hbd_s, ?_⟩
                  rw [fullMem_eq_candsFrame]; exact sep_ac (by assumption))
                (fun _ hJs1 => by
                  c0_hsteps_nogrp <;> exact hJs1 (_, ()) ml rfl)))

/-! ## 6. `m8_sweep_vars_wp` (`per_v = 16384`, `(ticks << 2) + 512`) -/

theorem m8_sweep_vars_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hDP : M6EnvSpec Γ "full_m6_dense_prop" m6DensePropSpec)
    (hCol : M6EnvSpec Γ "full_m6_collect_cands" m6CollectCandsSpec)
    (hSV : M6EnvSpec Γ "full_m6_sweep_var" m6SweepVarSpec)
    (_hSift : M6EnvSpec Γ "full_m6_cand_sift" m6CandSiftSpec) :
    ∀ args m Q X, m6SweepVarsSpec args m Q X →
      Func.wp Γ full_m6_sweep_vars_body args m Q X := by
  rintro ⟨h, budget, tlim, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, htmk, hm, hQ⟩
  unfold Func.wp full_m6_sweep_vars_body
  have hlen := hinv.lengths
  have hcap_lt : c.scratch_cap < 2 ^ 64 := Nat.lt_trans c.hscr (by unfold dimacsBound; decide)
  c0_hsteps_nogrp
  refine m8_call_max_v_cap hMaxV (cap := BitVec.ofNat 64 c.scratch_cap) ?_
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap_lt]
  c0_hsplit
  · c0_hsteps!; exact hQ 1#64 s m hinv rfl (Nat.le_refl _) htmk (Or.inl rfl) (fun h => by simp at h) hm
  have hcap_ge : k6MinScr ≤ c.scratch_cap := by
    rcases Nat.lt_or_ge c.scratch_cap k6MinScr with hlt | hle
    · have hmv0 : k6MaxV c.scratch_cap = 0 := k6MaxV_eq_zero hlt
      have hmv0_32 : (BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32 = 0#32 := by
        rw [hmv0]; rfl
      have hnot : ¬ (BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32 = 0#32 := hc
      exact absurd hmv0_32 hnot
    · exact hle
  c0_hsplit
  · c0_hsteps!; exact hQ 1#64 s m hinv rfl (Nat.le_refl _) htmk (Or.inl rfl) (fun h => by simp at h) hm
  c0_hsplit
  · c0_hsteps!; exact hQ 1#64 s m hinv rfl (Nat.le_refl _) htmk (Or.inl rfl) (fun h => by simp at h) hm
  obtain ⟨F_cur, hwW⟩ := hinv.exists_witness
  have hdw : FullDenseInvW c F0 F_cur s := hwW
  refine m8_call_dense_prop hDP hdw hm (fun ok s1 m1 hdw1 hcv1 hfuel1 htmk1 htrc1 hok1 hno1 hm1 => ?_)
  c0_hsplit; rotate_left
  · have hokf : ok = false := by cases ok <;> simp_all
    c0_hsteps!
    exact hQ 20#64 s1 m1 (m8_denseInv_of_W hdw1) hcv1 (by rw [hfuel1]; exact Nat.le_refl _)
      (m8_tmkZero_congr htmk hcv1 htmk1) (Or.inr rfl) (fun _ => (hno1 hokf).1) hm1
  have hlen1 := hdw1.1
  have htmk1_z : M6TmkZero s1 := m8_tmkZero_congr htmk hcv1 htmk1
  refine m8_call_collect_cands hCol hlen1 hm1 (fun nc trc2 ws2_2 m2 hlen2 hnc2 hbd2 hm2 => ?_)
  let s2 : FullState := { s1 with scratch := { s1.scratch with tarjan_reach := trc2, work_stk2 := ws2_2 } }
  have hdw2 : FullDenseInvW c F0 F_cur s2 :=
    m8_denseInvW_set_trc_ws2 hdw1 hlen2.scratch_ok.tarjan_reach_len hlen2.scratch_ok.work_stk2_len
  have htmk2 : M6TmkZero s2 := m8_tmkZero_congr htmk1_z rfl rfl
  c0_hsteps_nogrp
  c0_hsplit
  · c0_hsteps!
    exact hQ 1#64 s2 m2 (m8_denseInv_of_W hdw2) hcv1
      (by dsimp only [s2]; rw [hfuel1]; exact Nat.le_refl _)
      htmk2 (Or.inl rfl) (fun h => by simp at h) hm2
  obtain ⟨L, hL⟩ : ∃ L : K6Layout, L = k6LayoutOfCap c.scratch_cap hcap_ge c.hscr := ⟨_, rfl⟩
  have hL_len : L.scrLen = c.scratch_cap := hL ▸ k6LayoutOfCap_scrLen hcap_ge c.hscr
  have hL_mv : L.maxV = k6MaxV c.scratch_cap := by rw [hL]; rfl
  have hkptr_c0 : c.pScratchBuf + BitVec.setWidth 64
      ((1280 : BitVec 32) + (BitVec.setWidth 32 (BitVec.ofNat 64 (k6MaxV c.scratch_cap)) <<<
        (1 : Nat))) * 4 = L.kPtr c.pScratchBuf := by
    rw [← hL_mv, k6_mv32_zext]
    simpa only [show (1280 : BitVec 32) = 1280#32 from rfl] using k6_ptr_base_k6Base L c.pScratchBuf
  have hscr2 : s2.scratch.scratch_buf.length = c.scratch_cap := hlen2.scratch_ok.scratch_buf_len
  c0_hsteps_nogrp
  try rw [hkptr_c0]
  have hk11_ptr := m8_k11_ptr (c := c) (L := L) hL_len
  have hk11_idx := m8_k11_idx (c := c) (L := L) hL_len
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun (tl_c, ()) mt => tl_c.toNat ≤ 0xFFFFFFFF ∧ mt = m2)
    (fun _ (tl_c, ()) mt ⟨htl_le, hmt⟩ => by
      subst mt
      c0_hsteps_nogrp
      refine wp_loop_inv (ts := [i64, i32, i64])
        (fun (tl_l, ci_l, rem_l, ()) ml =>
          ci_l.toNat ≤ nc.toNat ∧
          ∃ s_l : FullState, FullDenseInvW c F0 F_cur s_l ∧
            s_l.core.cur_vars = s2.core.cur_vars ∧
            s_l.core.fuel.toNat ≤ s2.core.fuel.toNat ∧
            M6TmkZero s_l ∧ s_l.scratch.tarjan_reach = trc2 ∧ (FullMem c s_l ⋆ R) ml)
        (fun (_, ci_l, _, ()) _ => nc.toNat - ci_l.toNat)
        (fun _ hJ_in => by
          c0_hsteps!
          exact hJ_in (tl_c, 0#32, budget, ()) m2
            ⟨Nat.zero_le _, s2, hdw2, rfl, Nat.le_refl _, htmk2, rfl, hm2⟩)
        (fun _ (tl_l, ci_l, rem_l, ()) ml ⟨hci_le, s_l, hdw_l, hcv_l, hfl_l, htmk_l,
            htrc_l, hm_l⟩ hJ_in => by
          have hlen_l := hdw_l.1
          have hfuel_all : s_l.core.fuel.toNat ≤ s.core.fuel.toNat := by
            dsimp only [s2] at hfl_l; rw [hfuel1] at hfl_l; exact hfl_l
          have hcv_all : s_l.core.cur_vars = s.core.cur_vars := hcv_l.trans hcv1
          c0_hsteps_nogrp
          refine wp_join_group (ts := []) (fun _ me => me = ml)
            (fun _ _ me hme => by
              subst me
              c0_hsteps_nogrp
              refine wp_unroll_group fun J hJ => ?_
              c0_hsplit
              · c0_hsteps_nogrp
                exact hQ 20#64 s_l ml (m8_denseInv_of_W hdw_l) hcv_all hfuel_all htmk_l
                  (Or.inr rfl) (fun _ => (m8_denseInv_of_W hdw_l).inconsistent_unsat hc) hm_l
              · c0_hsteps_nogrp
                exact hQ 1#64 s_l ml (m8_denseInv_of_W hdw_l) hcv_all hfuel_all htmk_l
                  (Or.inl rfl) (fun h => by simp at h) hm_l)
            (fun _ hJ_ex => by
              c0_hsplit
              · have hci_lt : ci_l.toNat < nc.toNat := hc
                have hmx := maxVars_lt_2p31 c
                have hci_trc : (ci_l.setWidth 64).toNat < s_l.scratch.tarjan_reach.length := by
                  rw [htrc_l, hlen2.scratch_ok.tarjan_reach_len, BitVec.toNat_setWidth,
                    Nat.mod_eq_of_lt (by omega)]
                  have := hnc2; have := hlen.core_ok.cur_vars_le; omega
                c0_hsplit
                · have hrem_pos : 0 < rem_l.toNat := hc
                  c0_hsplit
                  · have htl_pos : 0 < tl_l.toNat := hc
                    c0_hsteps_nogrp <;> try exact hJ_ex () ml rfl
                    have hci1 : (ci_l + 1#32).toNat = ci_l.toNat + 1 :=
                      bv32_add1_toNat (by have := hnc2; have := hlen.core_ok.cur_vars_le; omega)
                    refine wp_join_group (ts := [i64, i64])
                      (fun (tl_n, rem_n, ()) mj =>
                        ∃ s_n : FullState, FullDenseInvW c F0 F_cur s_n ∧
                          s_n.core.cur_vars = s2.core.cur_vars ∧
                          s_n.core.fuel.toNat ≤ s2.core.fuel.toNat ∧
                          M6TmkZero s_n ∧ s_n.scratch.tarjan_reach = trc2 ∧
                          (FullMem c s_n ⋆ R) mj)
                      (fun _ (tl_n, rem_n, ()) mj ⟨s_n, hdw_n, hcv_n, hfl_n, htmk_n,
                          htrc_n, hm_n⟩ => by
                        c0_hsteps_nogrp
                        exact hJ_in (tl_n, ci_l + 1#32, rem_n, ()) mj
                          (by dsimp only; rw [hci1]; omega)
                          ⟨by rw [hci1]; omega, s_n, hdw_n, hcv_n, hfl_n, htmk_n, htrc_n, hm_n⟩)
                      (fun _ hJ_step => by
                        let rv := s_l.scratch.tarjan_reach[(ci_l.setWidth 64).toNat]'hci_trc
                        have hrv_lt : rv.toNat < s_l.core.cur_vars := by
                          have hci_m : (ci_l.setWidth 64).toNat = ci_l.toNat := by
                            rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                          have hbd := hbd2 ci_l.toNat hci_lt
                          rw [← hci_m, List.getElem?_eq_getElem (by rw [← htrc_l]; exact hci_trc),
                            Option.getD_some] at hbd
                          rw [hcv_l]; dsimp only [s2]
                          have hrv_eq : rv = trc2[(ci_l.setWidth 64).toNat]'(htrc_l ▸ hci_trc) := by
                            dsimp only [rv]; simp only [htrc_l]
                          rwa [hrv_eq]
                        have hrv_fl : (BitVec.setWidth 64 rv).toNat < s_l.core.flags.length := by
                          rw [hdw_l.1.core_ok.flags_len, BitVec.toNat_setWidth,
                            Nat.mod_eq_of_lt (by omega)]
                          exact Nat.lt_of_lt_of_le hrv_lt hdw_l.1.core_ok.cur_vars_le
                        have hrv_vals : (BitVec.setWidth 64 (rv <<< (1 : Nat))).toNat <
                            s_l.core.vals.length := by
                          rw [hdw_l.1.core_ok.vals_len]
                          have := hdw_l.1.core_ok.cur_vars_le
                          bv_omega
                        have h_skip_step : ∃ s_n : FullState, FullDenseInvW c F0 F_cur s_n ∧
                            s_n.core.cur_vars = s2.core.cur_vars ∧
                            s_n.core.fuel.toNat ≤ s2.core.fuel.toNat ∧ M6TmkZero s_n ∧
                            s_n.scratch.tarjan_reach = trc2 ∧ (FullMem c s_n ⋆ R) ml :=
                          ⟨s_l, hdw_l, hcv_l, hfl_l, htmk_l, htrc_l, hm_l⟩
                        c0_hsteps_nogrp <;> (try exact hJ_step (tl_l, rem_l, ()) ml h_skip_step)
                        refine wp_join_group (ts := [i64])
                          (fun (_pv, ()) mp =>
                            ∃ fl_l : List (BitVec 32), fl_l.length = c.max_vars ∧
                              (FullMem c { s_l with core := { s_l.core with flags := fl_l } } ⋆
                                R) mp)
                          (fun _ (pv, ()) mp ⟨fl_l, hfl_l_len, hmp⟩ => by
                            refine m8_call_sweep_var_fl hSV hmp hdw_l
                              hfl_l_len hcap_ge hrv_lt htmk_l
                              (fun r3 s3 m3 hdw3 hcv3 hfl3 htmk3 htrc3 hr3 hunsat3 hm3 => ?_)
                            c0_hsteps_nogrp
                            c0_hsplit
                            · c0_hsteps!
                              exact hQ 20#64 s3 m3 (m8_denseInv_of_W hdw3) (hcv3.trans hcv_all)
                                (Nat.le_trans hfl3 hfuel_all) htmk3 (Or.inr rfl)
                                (fun _ => hunsat3 hc) hm3
                            · refine wp_join_group (ts := [])
                                (fun () md => ∃ s_d : FullState, FullDenseInvW c F0 F_cur s_d ∧
                                  s_d.core.cur_vars = s2.core.cur_vars ∧
                                  s_d.core.fuel.toNat ≤ s2.core.fuel.toNat ∧
                                  M6TmkZero s_d ∧ s_d.scratch.tarjan_reach = trc2 ∧
                                  (FullMem c s_d ⋆ R) md)
                                (fun _ () md ⟨s_d, hdw_d, hcv_d, hfl_d, htmk_d, htrc_d, hm_d⟩ => by
                                  have hscr_d : s_d.scratch.scratch_buf.length = c.scratch_cap :=
                                    hdw_d.1.scratch_ok.scratch_buf_len
                                  have hk11_sd : (BitVec.setWidth 64
                                      (BitVec.ofNat 32 (L.k6Base + 11))).toNat <
                                      s_d.scratch.scratch_buf.length := hscr_d ▸ hk11_idx
                                  c0_hsteps_nogrp
                                  try rw [hk11_ptr]
                                  c0_hsteps_nogrp
                                  refine wp_join_group (ts := [i64])
                                    (fun (_tl_n, ()) mj' => mj' = md)
                                    (fun _ (tl_n, ()) mj' hmj' => by
                                      subst mj'
                                      c0_hsteps!
                                      have hstep_d : ∃ s_n : FullState, FullDenseInvW c F0 F_cur s_n ∧
                                          s_n.core.cur_vars = s2.core.cur_vars ∧
                                          s_n.core.fuel.toNat ≤ s2.core.fuel.toNat ∧
                                          M6TmkZero s_n ∧ s_n.scratch.tarjan_reach = trc2 ∧
                                          (FullMem c s_n ⋆ R) md :=
                                        ⟨s_d, hdw_d, hcv_d, hfl_d, htmk_d, htrc_d, hm_d⟩
                                      exact hJ_step (tl_n, rem_l - 1#64, ()) md hstep_d)
                                    (fun _ hJ87 => by
                                      c0_hsteps! <;> exact hJ87 (_, ()) md rfl))
                                (fun _ hJ_dp => by
                                  c0_hsteps_nogrp
                                  c0_hsplit
                                  · refine m8_call_dense_prop hDP hdw3 hm3
                                      (fun ok4 s4 m4 hdw4 hcv4 hfl4 htmk4 htrc4 hok4 hno4 hm4 => ?_)
                                    c0_hsteps_nogrp
                                    c0_hsplit
                                    · c0_hsteps_nogrp
                                      exact hJ_dp () m4 ⟨s4, hdw4, hcv4.trans (hcv3.trans hcv_l),
                                        by rw [hfl4]; exact Nat.le_trans hfl3 hfl_l,
                                        m8_tmkZero_congr htmk3 hcv4 htmk4,
                                        htrc4.trans (htrc3.trans htrc_l), hm4⟩
                                    · have hokf : ok4 = false := by cases ok4 <;> simp_all
                                      c0_hsteps!
                                      exact hQ 20#64 s4 m4 (m8_denseInv_of_W hdw4)
                                        (hcv4.trans (hcv3.trans hcv_all))
                                        (by rw [hfl4]; exact Nat.le_trans hfl3 hfuel_all)
                                        (m8_tmkZero_congr htmk3 hcv4 htmk4) (Or.inr rfl)
                                        (fun _ => (hno4 hokf).1) hm4
                                  · c0_hsteps_nogrp
                                    exact hJ_dp () m3 ⟨s3, hdw3, hcv3.trans hcv_l,
                                      Nat.le_trans hfl3 hfl_l, htmk3, htrc3.trans htrc_l, hm3⟩))
                          (fun _ hJ_pv => by
                            c0_hsteps_nogrp <;>
                              (refine hJ_pv (_, ()) _ ⟨_, ?_, by assumption⟩
                               rw [List.length_set, hdw_l.1.core_ok.flags_len])))
                  · c0_hsteps_nogrp; exact hJ_ex () ml rfl
                · c0_hsteps_nogrp; exact hJ_ex () ml rfl
              · c0_hsteps_nogrp; exact hJ_ex () ml rfl)))
    (fun _ hJt => by
      c0_hsplit
      · c0_hsteps!; exact hJt (0xFFFFFFFF#64, ()) m2 ⟨by decide, rfl⟩
      · have hle : tlim.toNat ≤ 0xFFFFFFFF := by
          have hnot : ¬ (4294967295 : Nat) < tlim.toNat := hc
          omega
        c0_hsteps!; exact hJt (tlim, ()) m2 ⟨hle, rfl⟩)

/-! ## 7. `m8_sweep_dense_m6_wp` (`1` pass outer driver) -/

theorem m8_sweep_dense_m6_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hSweepVars : M6EnvSpec Γ "full_m6_sweep_vars" m6SweepVarsSpec) :
    ∀ args m Q X, m4SweepDenseSpec args m Q X →
      Func.wp Γ full_sweep_dense_m6_body args m Q X := by
  rintro ⟨h, budget, tlim, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, hm, hQ⟩
  unfold Func.wp full_sweep_dense_m6_body
  have hcap_lt : c.scratch_cap < 2 ^ 64 :=
    Nat.lt_trans c.hscr (by unfold dimacsBound; decide)
  have hcap_toNat : (BitVec.ofNat 64 c.scratch_cap).toNat = c.scratch_cap := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap_lt]
  have hlen := hinv.lengths
  have hcv_le := hlen.core_ok.cur_vars_le
  have hcv_2p64 : s.core.cur_vars < 2 ^ 64 := by
    have := c.hmaxv; unfold dimacsBound at this; omega
  have htmk_len := hlen.scratch_ok.tarjan_mark_len
  c0_hsteps_nogrp
  refine m8_call_max_v_cap hMaxV (cap := BitVec.ofNat 64 c.scratch_cap) ?_
  rw [hcap_toNat]
  c0_hsplit
  · c0_hsteps!
    exact hQ 1#64 s m hinv rfl (Nat.le_refl _) (Or.inl rfl) (fun h => by cases h) hm
  c0_hsplit
  · c0_hsteps!
    exact hQ 1#64 s m hinv rfl (Nat.le_refl _) (Or.inl rfl) (fun h => by cases h) hm
  c0_hsplit
  · c0_hsteps!
    exact hQ 1#64 s m hinv rfl (Nat.le_refl _) (Or.inl rfl) (fun h => by cases h) hm
  c0_hsteps_nogrp
  refine wp_loop_inv (ts := [i64])
    (fun (vi, ()) ml => vi.toNat ≤ s.core.cur_vars ∧ ∃ tmk_l : List (BitVec 32),
      tmk_l.length = 2 * c.max_vars ∧ (∀ v < vi.toNat, tmk_l[v]?.getD 0#32 = 0#32) ∧
      (FullMem c { s with scratch := { s.scratch with tarjan_mark := tmk_l } } ⋆ R) ml)
    (fun (vi, ()) _ => s.core.cur_vars - vi.toNat)
    (fun _ hJ_in => by
      c0_hsteps!
      refine hJ_in (0#64, ()) m ⟨Nat.zero_le _, s.scratch.tarjan_mark, htmk_len,
        fun v hv => by simp at hv, hm⟩)
    (fun _ (vi, ()) ml ⟨hvi_le, tmk_l, htmk_l, hprev, hml⟩ hJ_in => by
      c0_hsplit; rotate_left
      · have hge : s.core.cur_vars ≤ vi.toNat := by
          have h1 : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv_2p64]
          have hnot : ¬ vi.toNat < (BitVec.ofNat 64 s.core.cur_vars).toNat := by
            simpa [BitVec.lt_def] using hc
          omega
        have htmk0 : M6TmkZero { s with scratch := { s.scratch with tarjan_mark := tmk_l } } :=
          fun v hv => hprev v (by dsimp only at hv; omega)
        let s1 : FullState := { s with scratch := { s.scratch with tarjan_mark := tmk_l } }
        have hinv1 : FullDenseInv c F0 s1 :=
          FullSweepVarHelpers.fullDenseInv_with_tmk hinv htmk_l
        c0_hsteps_nogrp
        refine m8_call_sweep_vars hSweepVars hinv1 htmk0 hml
          (fun r s2 m2 hinv2 hcv2 hfuel2 _ hr2 huns2 hm2 => ?_)
        c0_hsplit
        · c0_hsteps!
          exact hQ 20#64 s2 m2 hinv2 hcv2 hfuel2 (Or.inr rfl) (fun _ => huns2 hc) hm2
        · c0_hsteps_nogrp
          refine wp_join_group (ts := [i64])
            (fun (r_out, ()) m_out => (r_out = 1#64 ∨ r_out = 20#64) ∧
              (r_out = 20#64 → F0.Unsat) ∧ m_out = m2)
            (fun _ (r_out, ()) m_out ⟨hro, huns, hmeq⟩ => by
              subst m_out
              c0_hsteps!
              exact hQ r_out s2 m2 hinv2 hcv2 hfuel2 hro huns hm2)
            (fun _ hJ_out => by
              c0_hsteps_nogrp
              c0_hsplit
              · c0_hsteps!
                exact hJ_out (20#64, ()) m2 ⟨Or.inr rfl,
                  fun _ => hinv2.inconsistent_unsat hc, rfl⟩
              · c0_hsteps!
                exact hJ_out (1#64, ()) m2 ⟨Or.inl rfl, fun h => by simp at h, rfl⟩)
      · have hvi_lt : vi.toNat < s.core.cur_vars := by
          have hnot := hc
          rw [Nat.mod_eq_of_lt hcv_2p64] at hnot
          exact hnot
        have hstep := m8_tmk_step (i := vi.toNat) (by rw [htmk_l]; omega) hprev
        have hvi1 : (vi + 1#64).toNat = vi.toNat + 1 := bv64_add1_toNat (by omega)
        c0_hsteps!
        exact hJ_in (vi + 1#64, ()) _
          (by dsimp only; rw [hvi1]; omega)
          ⟨by rw [hvi1]; exact hvi_lt, tmk_l.set vi.toNat 0#32,
            by rw [List.length_set, htmk_l],
            by rw [hvi1]; exact hstep.2, by assumption⟩)

end LeanQbe.T.Examples.Kissat.FullM8SweepV2

end
