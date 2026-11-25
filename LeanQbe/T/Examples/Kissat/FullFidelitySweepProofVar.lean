/-
Copyright (c) 2026 LeanQbe Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanQbe.T.Examples.Kissat.FullFidelitySweep
public import LeanQbe.T.Examples.Kissat.FullM6SweepProofSpec
import LeanQbe.T.Examples.Kissat.FullM8SweepV2ConeProof
import LeanQbe.T.Examples.Kissat.FullM6SweepProofVar1a
import LeanQbe.T.Examples.Kissat.FullM6SweepProofCands
import LeanQbe.T.Examples.Kissat.FullM4SweepProof

/-!
# Kissat Full-Fidelity Sweep — `sim` / `collect_cands` / `sweep_vars` `Func.wp` Proofs

Purely additive parametric `(Γ : Env)` `Func.wp` proofs for the remaining 3 modified functions
in `FullFidelitySweep`:
1. `fid_sweep_sim_wp : m6SweepSimSpec` (`sim_lim = tick_lim >> 2`, up to `16` flip rounds)
2. `fid_collect_cands_wp : m6CollectCandsSpec` (`max_occ = 1024 << comp`, `FL_SWEEP_INR`/`INC` tier)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullFidelitySweep

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full LeanQbe.T.Examples.Kissat.FullM4Sweep
open LeanQbe.T.Examples.Kissat.FullM6Sweep LeanQbe.T.Examples.Kissat.FullM8SweepV2
open Kraken.Bedrock2.Test
open FullArenaTactics K6MemATactics K6PtrTactics
open scoped FullArenaTactics M6SweepTactics K6MemATactics K6PtrTactics

/-! ## 1. Shared Arithmetic, Memory & Call Helpers -/

private theorem bv32_zext_mul4_eq (idx : BitVec 32) :
    idx.setWidth 64 * 4 = BitVec.ofNat 64 (4 * idx.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have hlt : idx.toNat < 2 ^ 32 := idx.isLt
  simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have h4 : (4 : BitVec 64).toNat = 4 := rfl
  rw [h4, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mul_comm]

theorem bv32_add1_toNat {x : BitVec 32} (hx : x.toNat + 1 < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 := by bv_omega

private theorem bv32_lshr1_toNat (x : BitVec 32) :
    (x >>> (1 : Nat)).toNat = x.toNat / 2 := by bv_omega

theorem bv64_add1_toNat {x : BitVec 64} (hx : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by bv_omega

theorem bv64_shl1_toNat {v : BitVec 64} (hv : v.toNat < 2 ^ 31) :
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

theorem bv64_wvec_pos_bv_toNat {v : BitVec 64} (hv : v.toNat < 2 ^ 31) :
    (((v <<< (1 : BitVec 64)) <<< (1 : BitVec 64)) + (1 : BitVec 64)).toNat =
      4 * v.toNat + 1 := by
  have h0 := bv64_shl1_toNat hv
  have h1 : ((v <<< (1 : Nat)) <<< (1 : Nat)).toNat = 4 * v.toNat := by
    simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, h0]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  change (((v <<< (1 : Nat)) <<< (1 : Nat)) + 1#64).toNat = 4 * v.toNat + 1
  rw [BitVec.toNat_add, h1, show (1#64 : BitVec 64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega)]

theorem bv64_wvec_neg_bv_toNat {v : BitVec 64} (hv : v.toNat < 2 ^ 31) :
    ((((v <<< (1 : BitVec 64)) ||| (1 : BitVec 64)) <<< (1 : BitVec 64)) +
      (1 : BitVec 64)).toNat = 4 * v.toNat + 3 := by
  have h0 := bv64_shl1_toNat hv
  have hor : ((v <<< (1 : Nat)) ||| 1#64).toNat = 2 * v.toNat + 1 := by
    rw [BitVec.toNat_or, h0, show (1#64 : BitVec 64).toNat = 1 from rfl]
    exact nat_two_mul_lor_one v.toNat
  have h1 : (((v <<< (1 : Nat)) ||| 1#64) <<< (1 : Nat)).toNat = 4 * v.toNat + 2 := by
    simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hor]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  change ((((v <<< (1 : Nat)) ||| 1#64) <<< (1 : Nat)) + 1#64).toNat = 4 * v.toNat + 3
  rw [BitVec.toNat_add, h1, show (1#64 : BitVec 64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega)]

private theorem k6_mv32_zext (L : K6Layout) :
    BitVec.setWidth 32 (BitVec.ofNat 64 L.maxV) = L.mv32 := by
  have hm := L.hmaxV
  apply BitVec.eq_of_toNat_eq
  unfold K6Layout.mv32
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

theorem maxVars_lt_2p31 (c : FullCfg) : c.max_vars < 2 ^ 31 := by
  have hm := c.hmaxv; unfold dimacsBound at hm; omega

namespace FidVarMemTactics

attribute [scoped bv_c0 high] bv_c0_zext32_64

@[scoped bv_c0 high] theorem bv_ofNat64_zero_toNat : (BitVec.ofNat 64 0).toNat = 0 := rfl

@[scoped bv_c0 high] theorem bv_zext32_11_mul4 :
    (BitVec.setWidth 64 (11#32 : BitVec 32)) * 4 = 44#64 := rfl

@[scoped bv_c0 high] theorem bv_ofNat64_11_mul4 :
    BitVec.ofNat 64 11 * 4 = 44#64 := rfl

@[scoped bv_c0 high] theorem bv_zext32_24_mul4 :
    (BitVec.setWidth 64 (24#32 : BitVec 32)) * 4 = 96#64 := rfl

@[scoped bv_c0 high] theorem bv_ofNat64_24_mul4 :
    BitVec.ofNat 64 24 * 4 = 96#64 := rfl

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

end FidVarMemTactics

open scoped FidVarMemTactics

theorem fid_call_max_v_cap {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    {cap : BitVec 64} {m : Mem 64} {k : Tup Val [i64] → Expr Val Cont rs}
    (hk : wp Γ Q X (k (BitVec.ofNat 64 (k6MaxV cap.toNat), ())) m) :
    wp Γ Q X (Expr.call (as := [i64]) (bs := [i64]) "full_m6_max_v" (Arg.var cap, ()) k) m :=
  wp_call_of_spec _ k (hMaxV (cap, ()) m (fun r m' => wp Γ Q X (k r) m') X hk)

theorem fid_call_dense_prop {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
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

theorem fid_call_collect_cands {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
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

theorem fid_call_sweep_var {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
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

private theorem fid_call_cand_sift {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
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

private theorem fid_call_solve {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
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

private theorem fid_call_refine_sig {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
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

private theorem fid_call_flip_round {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
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
      let s' : FullState :=
        { s with scratch := { s.scratch with rng_state := rng', scratch_buf := scr' } }
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

private theorem fid_k6_slab_exit {c : FullCfg} {L : K6Layout} {s : FullState}
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

theorem fid_denseInv_of_W {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) : FullDenseInv c F0 s :=
  ⟨⟨h.1, ⟨F_cur, h.2.1⟩⟩, h.2.2⟩

private theorem fid_k6Shapes_putHdr_nassump {L : K6Layout} {ks : K6State} (v : BitVec 32)
    (h : ks.ShapesOk L) : (ks.putHdr .nassump v).ShapesOk L :=
  ⟨h.hdrTail_len, h.lvlArr_len, h.rsn_len, h.qprev_len, h.qnext_len, h.qstampArr_len,
   h.trl_len, h.flags_len, h.ana_len, h.kl_len, h.assump_len, h.vals_len, h.whead_len,
   h.wnext_len, h.wblit_len, h.clOff_len, h.clSz_len, h.arena_len⟩

private theorem fid_k6Inv_putHdr_nassump_zero {L : K6Layout} {P : (Nat → Bool) → Prop}
    {ks : K6State} (h : K6Inv L P ks) : K6Inv L P (ks.putHdr .nassump 0#32) :=
  ⟨fid_k6Shapes_putHdr_nassump 0#32 h.shapes,
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

private def FidCandsFrame (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
  (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
    (array (t := i32) c.pWsort s.scratch.wsort ⋆
     array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
     array (t := i32) c.pTarjanMark s.scratch.tarjan_mark) ⋆
    FullScrMetaArrs c s.scratch ⋆ FullScrDynArrs c s.scratch) ⋆
  c.pad

private theorem fullMem_eq_fidCandsFrame (c : FullCfg) (s : FullState) :
    FullMem c s =
      (array (t := i32) c.pTarjanReach s.scratch.tarjan_reach ⋆
        array (t := i32) c.pWorkStk2 s.scratch.work_stk2 ⋆
        FidCandsFrame c s) := by
  unfold FullMem FullScratchArrays FullScrWksArrs FidCandsFrame
  ac_rfl

private theorem fidCands_split_array {a : BitVec 64} {xs : List (BitVec 32)} {n : Nat}
    (hn : n ≤ xs.length) :
    array (t := i32) a xs =
      (array (t := i32) a (xs.take n) ⋆
        array (t := i32) (a + BitVec.ofNat 64 (4 * n)) (xs.drop n)) := by
  have htake : (xs.take n).length = n := List.length_take_of_le hn
  conv => lhs; rw [← List.take_append_drop n xs]
  rw [array_append, htake]
  rfl

private theorem fid_cands_split_mem {p1 p2 : BitVec 64} {xs ws : List (BitVec 32)} {k : Nat}
    {F R : Mem 64 → Prop} {m : Mem 64} (hk : k ≤ xs.length)
    (hm : (array (t := i32) p1 xs ⋆ array (t := i32) p2 ws ⋆ F ⋆ R) m) :
    (array (t := i32) p1 (xs.take k) ⋆ array (t := i32) p2 ws ⋆
      (array (t := i32) (p1 + BitVec.ofNat 64 (4 * k)) (xs.drop k) ⋆ F ⋆ R)) m := by
  rw [fidCands_split_array (a := p1) hk] at hm
  exact sep_ac hm

private theorem fidCands_join_array {a : BitVec 64} {pref suff : List (BitVec 32)}
    {n : Nat} (hp : pref.length = n) :
    (array (t := i32) a pref ⋆ array (t := i32) (a + BitVec.ofNat 64 (4 * n)) suff) =
      array (t := i32) a (pref ++ suff) := by
  rw [array_append, hp]; rfl

theorem fid_tmkZero_congr {s s' : FullState} (h : M6TmkZero s)
    (hcv : s'.core.cur_vars = s.core.cur_vars)
    (ht : s'.scratch.tarjan_mark = s.scratch.tarjan_mark) : M6TmkZero s' := by
  intro v hv; rw [ht]; exact h v (hcv ▸ hv)

theorem fid_lengthsOk_trc_ws2 {c : FullCfg} {s : FullState} (h : s.LengthsOk c)
    {trc' ws2' : List (BitVec 32)} (htrc : trc'.length = 2 * c.max_vars)
    (hws2 : ws2'.length = 2 * c.max_vars) :
    ({ s with scratch := { s.scratch with tarjan_reach := trc', work_stk2 := ws2' } } :
      FullState).LengthsOk c :=
  ⟨h.core_ok, { h.scratch_ok with tarjan_reach_len := htrc, work_stk2_len := hws2 }⟩

theorem fid_denseInvW_set_trc_ws2 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {trc' ws2' : List (BitVec 32)}
    (htrc : trc'.length = 2 * c.max_vars) (hws2 : ws2'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur
      { s with scratch := { s.scratch with tarjan_reach := trc', work_stk2 := ws2' } } :=
  ⟨fid_lengthsOk_trc_ws2 h.1 htrc hws2, h.2.1, h.2.2.1, h.2.2.2.1,
   h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem fid_denseInvW_set_trc {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {trc' : List (BitVec 32)}
    (htrc : trc'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur
      { s with scratch := { s.scratch with tarjan_reach := trc' } } :=
  fid_denseInvW_set_trc_ws2 h htrc h.1.scratch_ok.work_stk2_len

theorem fid_denseInvW_set_gu {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {gu' : List (BitVec 32)}
    (hgu : gu'.length = 64) :
    FullDenseInvW c F0 F_cur { s with scratch := { s.scratch with glue_used := gu' } } :=
  ⟨⟨h.1.core_ok, { h.1.scratch_ok with glue_used_len := hgu }⟩, h.2.1, h.2.2.1, h.2.2.2.1,
   h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

theorem fid_denseInvW_set_flags {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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

theorem fid_denseInvW_set_flags_trc {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {flags' trc' : List (BitVec 32)}
    (hfl : flags'.length = c.max_vars) (htrc : trc'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur
      { core := { s.core with flags := flags' },
        scratch := { s.scratch with tarjan_reach := trc' } } :=
  fid_denseInvW_set_trc (fid_denseInvW_set_flags h hfl) htrc

theorem fid_denseInvW_set_flags_gu {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {flags' gu' : List (BitVec 32)}
    (hfl : flags'.length = c.max_vars) (hgu : gu'.length = 64) :
    FullDenseInvW c F0 F_cur
      { core := { s.core with flags := flags' },
        scratch := { s.scratch with glue_used := gu' } } :=
  fid_denseInvW_set_gu (fid_denseInvW_set_flags h hfl) hgu

private theorem fid_denseInvW_set_sim {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s)
    {fuel' rng' : BitVec 64} {sig' : List (BitVec 64)} {scr' : List (BitVec 32)}
    (hsig : sig'.length = c.max_vars) (hscr : scr'.length = c.scratch_cap) :
    FullDenseInvW c F0 F_cur
      { core := { s.core with fuel := fuel' },
        scratch :=
          { s.scratch with rng_state := rng', sim_sig := sig', scratch_buf := scr' } } := by
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

private theorem fid_k6Layout_congr {n m : Nat} (e : n = m) (h1 : k6MinScr ≤ n)
    (h2 : n < dimacsBound) (h1' : k6MinScr ≤ m) (h2' : m < dimacsBound) :
    k6LayoutOfCap n h1 h2 = k6LayoutOfCap m h1' h2' := by
  subst e; rfl

private abbrev fidSimState (s : FullState) (fuel rng : BitVec 64)
    (sig : List (BitVec 64)) (scr : List (BitVec 32)) : FullState :=
  { core := { s.core with fuel := fuel },
    scratch := { s.scratch with rng_state := rng, sim_sig := sig, scratch_buf := scr } }

theorem fid_k11_ptr {c : FullCfg} {L : K6Layout} (hL_len : L.scrLen = c.scratch_cap) :
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

theorem fid_k11_idx {c : FullCfg} {L : K6Layout} (hL_len : L.scrLen = c.scratch_cap) :
    (BitVec.setWidth 64 (BitVec.ofNat 32 (L.k6Base + 11))).toNat < c.scratch_cap := by
  have := c.hscr; rw [← hL_len]; unfold K6Layout.scrLen K6Layout.k6Fixed at *
  have hLkb : L.k6Base + 11 < 2 ^ 32 := by unfold dimacsBound at this; omega
  rw [BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hLkb]; omega),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hLkb]
  omega

theorem fid_k24_ptr {c : FullCfg} {L : K6Layout} (hL_len : L.scrLen = c.scratch_cap) :
    L.kPtr c.pScratchBuf + 24#64 * 4 =
      c.pScratchBuf + BitVec.setWidth 64 (BitVec.ofNat 32 (L.k6Base + 24)) * 4 := by
  have hLkb : L.k6Base + 24 < 2 ^ 32 := by
    have := c.hscr; rw [← hL_len] at this
    unfold K6Layout.scrLen K6Layout.k6Fixed at this; unfold dimacsBound at this; omega
  have hkb_lt : L.k6Base < 2 ^ 32 := by omega
  unfold K6Layout.kPtr; rw [BitVec.add_assoc]; congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt hLkb, Nat.mod_eq_of_lt (by omega : 4 * L.k6Base < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 4 < 2 ^ 64), Nat.mod_eq_of_lt (by omega : 96 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 4 * L.k6Base + 96 < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : (L.k6Base + 24) * 4 < 2 ^ 64)]
  omega

theorem fid_k24_idx {c : FullCfg} {L : K6Layout} (hL_len : L.scrLen = c.scratch_cap) :
    (BitVec.setWidth 64 (BitVec.ofNat 32 (L.k6Base + 24))).toNat < c.scratch_cap := by
  have := c.hscr; rw [← hL_len]; unfold K6Layout.scrLen K6Layout.k6Fixed at *
  have hLkb : L.k6Base + 24 < 2 ^ 32 := by unfold dimacsBound at this; omega
  rw [BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hLkb]; omega),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hLkb]
  omega

private theorem fid_coneOk_of_k6 {F_cur : List (List Nat)} {s : FullState}
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
  have hLeq := fid_k6Layout_congr hscr_eq hge_scr hlt_scr hge_c hlt_c
  have hnv' : (k6StateOfScratch (k6LayoutOfCap s.scratch.scratch_buf.length hge_c hlt_c) scr').nv =
      BitVec.ofNat 32 nv.toNat :=
    hnv.trans (BitVec.eq_of_toNat_eq (by simp)).symm
  refine ⟨hcone.1, by rw [hscr_eq]; exact hcone.2.1, hcone.2.2.1, hcone.2.2.2.1,
    ⟨hge_scr, hlt_scr, hLeq ▸ hK⟩, ⟨hge_scr, hlt_scr, hLeq ▸ hnv'⟩⟩

theorem fid_call_sweep_var_fl_gu {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hSV : M6EnvSpec Γ "full_m6_sweep_var" m6SweepVarSpec)
    {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)} {s : FullState}
    {flags' gu' : List (BitVec 32)} {R : Mem 64 → Prop} {m : Mem 64} {rv : BitVec 32}
    {tlim : BitVec 64} {k : Tup Val [i64] → Expr Val Cont rs}
    (hm : (FullMem c
        { core := { s.core with flags := flags' },
          scratch := { s.scratch with glue_used := gu' } } ⋆ R) m)
    (hdw : FullDenseInvW c F0 F_cur s) (hfl : flags'.length = c.max_vars) (hgu : gu'.length = 64)
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
  fid_call_sweep_var hSV (fid_denseInvW_set_flags_gu hdw hfl hgu) hcap hrv
    (fid_tmkZero_congr htmk rfl rfl) hm hk

theorem fid_gu_idx_lt {gu : List (BitVec 32)} (hgu : gu.length = 64) :
    (BitVec.setWidth 64 (28 : BitVec 32)).toNat < gu.length ∧
    (BitVec.setWidth 64 (29 : BitVec 32)).toNat < gu.length ∧
    (BitVec.setWidth 64 (30 : BitVec 32)).toNat < gu.length ∧
    (28 : BitVec 64).toNat < gu.length ∧
    (29 : BitVec 64).toNat < gu.length ∧
    (30 : BitVec 64).toNat < gu.length := by
  rw [hgu]; decide

/-! ## 2. `fid_sweep_sim_wp` (`sim_lim = tick_lim`) -/

theorem fid_sweep_sim_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hSolve : M6EnvSpec Γ "full_m6_sweep_solve" m6SweepSolveSpec)
    (hRef : M6EnvSpec Γ "full_m6_sweep_refine_sig" m6SweepRefineSigSpec)
    (hFlipR : M6EnvSpec Γ "full_m6_sweep_flip_round" m6SweepFlipRoundSpec) :
    ∀ args m Q X, m6SweepSimSpec args m Q X →
      Func.wp Γ FullFidelitySweep.full_m6_sweep_sim_body args m Q X := by
  rintro ⟨h, nv, tlim, ⟨⟩⟩ m Q X ⟨c, F0, F_cur, s, R, rfl, hdw, hcone, hm, hQ⟩
  unfold Func.wp FullFidelitySweep.full_m6_sweep_sim_body
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
  refine fid_call_max_v_cap hMaxV (cap := BitVec.ofNat 64 c.scratch_cap) ?_
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcap_lt]
  c0_hsplit
  · exfalso
    have := (k6MaxV_bounds hcap).1
    have h0 := congrArg BitVec.toNat
      (hc : (BitVec.ofNat 64 (k6MaxV c.scratch_cap)).setWidth 32 = 0#32)
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
          simpa only [show (1280 : BitVec 32) = 1280#32 from rfl] using
            k6_ptr_base_k6Base L c.pScratchBuf
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
        obtain ⟨hlen0, _hpre0, hks0', hm0⟩ :=
          fid_k6_slab_exit (R := R) hlen_i hL_len (fid_k6Shapes_putHdr_nassump 0#32 hKi.shapes)
            (by assumption)
        have hK0' : K6Inv L (ConeModelSet F_cur s.scratch.work_stk1 nv.toNat)
            (k6StateOfScratch L scr0) := hks0' ▸ fid_k6Inv_putHdr_nassump_zero hKi
        have hcone_nv : ks_0.nv = nv := by
          obtain ⟨_, _, hnv_eq⟩ := hcone.2.2.2.2.2
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
        refine fid_call_solve hSolve hlen0 hL_len hL_mv hK0' hnv0' hm0
          (fun r1 fuel1 rng1 scr1 m1 hlen1 hfuel1 _hpre1 hK1 _htrl1 hnv1 hna1 _has1 _hnq1
            _hr1 hunsat1 hm1 => ?_)
        have hscr1 : scr1.length = c.scratch_cap := hlen1.scratch_ok.scratch_buf_len
        have hfuel1_le : fuel1.toNat ≤ s.core.fuel.toNat := hfuel1
        have hna1_0 : (k6StateOfScratch L scr1).nassump = 0#32 := by
          rw [hna1, hks0']; rfl
        have hscr1_eq : scr1.length = s.scratch.scratch_buf.length :=
          hscr1.trans hlen.scratch_ok.scratch_buf_len.symm
        have hdw1 : FullDenseInvW c F0 F_cur (fidSimState s fuel1 rng1 sig_l scr1) :=
          fid_denseInvW_set_sim hdw hsig_l hscr1
        have hcone1 : M6SweepConeOk F_cur (fidSimState s fuel1 rng1 sig_l scr1) nv.toNat :=
          fid_coneOk_of_k6 hcone hscr1_eq hK1 hnv1
        c0_hsplit
        · have hr1_20 : r1 = 20#64 := hc
          c0_hsteps!
          exact hQ 4294967295#32 fuel1 rng1 sig_l scr1 m1 hdw1 hfuel1_le hcone1
            (fun _ => hunsat_solve scr1 hna1_0 (hunsat1 hr1_20))
            (fun h => absurd rfl h) hm1
        · c0_hsplit
          · c0_hsteps!
            exact hQ 0#32 fuel1 rng1 sig_l scr1 m1 hdw1 hfuel1_le hcone1
              (fun h => by simp at h) (fun _ => by simp) hm1
          · refine fid_call_refine_sig hRef hlen1 hcap
              (by rw [← hL_mv]; exact hnv1 ▸ hK1.clauses.nv_le)
              (Nat.le_trans hnv_le_mv (by omega)) hcone.2.2.2.1 hm1
              (fun sig2 m2 hsig2 hm2 => ?_)
            have hk11_ptr := fid_k11_ptr (c := c) (L := L) hL_len
            have hk11_idx := fid_k11_idx (c := c) (L := L) hL_len
            c0_hsteps_nogrp
            refine wp_join_group (ts := [i32, i32])
              (fun (r_o, _rd_o, ()) mo => r_o.toNat ≤ 64 ∧
                ∃ (rng_o : BitVec 64) (sig_o : List (BitVec 64)) (scr_o : List (BitVec 32)),
                  sig_o.length = c.max_vars ∧ scr_o.length = c.scratch_cap ∧
                  K6Inv L (ConeModelSet F_cur s.scratch.work_stk1 nv.toNat)
                    (k6StateOfScratch L scr_o) ∧
                  (k6StateOfScratch L scr_o).nv = nv ∧
                  (FullMem c (fidSimState s fuel1 rng_o sig_o scr_o) ⋆ R) mo)
              (fun _ (r_o, _rd_o, ()) mo ⟨hr_o_le, rng_o, sig_o, scr_o,
                  hsig_o, hscr_o, hK_o, hnv_o, hm_o⟩ => by
                c0_hsteps!
                exact hQ r_o fuel1 rng_o sig_o scr_o mo
                  (fid_denseInvW_set_sim hdw hsig_o hscr_o) hfuel1_le
                  (fid_coneOk_of_k6 hcone (hscr_o.trans hlen.scratch_ok.scratch_buf_len.symm)
                    hK_o hnv_o)
                  (fun h => False.elim (by rw [h] at hr_o_le; simp at hr_o_le))
                  (fun _ => hr_o_le) hm_o)
              (fun _ hJ_ret => by
                c0_hsteps_nogrp
                refine wp_loop_inv (ts := [i32, i32])
                  (fun (r_l, rd_l, ()) ml =>
                    rd_l.toNat ≤ 16 ∧ r_l.toNat ≤ 64 ∧
                    ∃ (rng_l : BitVec 64) (sig_l' : List (BitVec 64)) (scr_l : List (BitVec 32)),
                      sig_l'.length = c.max_vars ∧ scr_l.length = c.scratch_cap ∧
                      K6Inv L (ConeModelSet F_cur s.scratch.work_stk1 nv.toNat)
                        (k6StateOfScratch L scr_l) ∧
                      (k6StateOfScratch L scr_l).nv = nv ∧
                      (FullMem c (fidSimState s fuel1 rng_l sig_l' scr_l) ⋆ R) ml)
                  (fun (_, rd_l, ()) _ => 16 - rd_l.toNat)
                  (fun _ hJ_rd => by
                    c0_hsteps!
                    exact hJ_rd (1#32, 0#32, ()) m2
                      ⟨by decide, by decide, rng1, sig2, scr1, hsig2, hscr1, hK1, hnv1, hm2⟩)
                  (fun _ (r_l, rd_l, ()) ml ⟨hrd_le, hr_le, rng_l, sig_l', scr_l,
                      hsig_l', hscr_l, hK_l, hnv_l, hm_l⟩ hJ_rd => by
                    let s_l : FullState := fidSimState s fuel1 rng_l sig_l' scr_l
                    have hlen_l : s_l.LengthsOk c :=
                      (fid_denseInvW_set_sim hdw hsig_l' hscr_l).1
                    have hk11_sl : (BitVec.setWidth 64
                        (BitVec.ofNat 32 (L.k6Base + 11))).toNat <
                        s_l.scratch.scratch_buf.length := hscr_l ▸ hk11_idx
                    have h_ret_st :
                        r_l.toNat ≤ 64 ∧ ∃ rng_o sig_o scr_o,
                          sig_o.length = c.max_vars ∧ scr_o.length = c.scratch_cap ∧
                          K6Inv L (ConeModelSet F_cur s.scratch.work_stk1 nv.toNat)
                            (k6StateOfScratch L scr_o) ∧
                          (k6StateOfScratch L scr_o).nv = nv ∧
                          (FullMem c (fidSimState s fuel1 rng_o sig_o scr_o) ⋆ R) ml :=
                      ⟨hr_le, rng_l, sig_l', scr_l, hsig_l', hscr_l, hK_l, hnv_l, hm_l⟩
                    c0_hsplit
                    · have hrd_lt : rd_l.toNat < 16 := hc
                      c0_hsplit
                      · have hr_lt : r_l.toNat < 64 := hc
                        c0_hsteps_nogrp
                        try rw [hk11_ptr]
                        c0_hsteps_nogrp <;> (try exact hJ_ret (r_l, rd_l, ()) ml h_ret_st)
                        refine fid_call_flip_round hFlipR hlen_l hL_len hL_mv hK_l hnv_l
                          hm_l (fun rflip rng_f scr_f m_f hlen_f _hpre_f hK_f hnv_f
                            _hna_f _has_f _hnq_f hm_f => ?_)
                        have hscr_f : scr_f.length = c.scratch_cap :=
                          hlen_f.scratch_ok.scratch_buf_len
                        c0_hsplit
                        · refine fid_call_refine_sig hRef hlen_f hcap
                            (by rw [← hL_mv]; exact hnv_f ▸ hK_f.clauses.nv_le)
                            (Nat.le_trans hnv_le_mv (by omega))
                            hcone.2.2.2.1 hm_f (fun sig_r m_r hsig_r hm_r => ?_)
                          have hr1_p1 : (r_l + 1#32).toNat ≤ 64 := by
                            rw [bv32_add1_toNat (by omega)]; omega
                          have hrd1 : (rd_l + 1#32).toNat = rd_l.toNat + 1 :=
                            bv32_add1_toNat (by omega)
                          c0_hsteps!
                          exact hJ_rd (r_l + 1#32, rd_l + 1#32, ()) m_r
                            (by dsimp only; rw [hrd1]; omega)
                            ⟨by rw [hrd1]; omega, hr1_p1, rng_f, sig_r, scr_f, hsig_r, hscr_f,
                              hK_f, hnv_f, hm_r⟩
                        · c0_hsteps!
                          exact hJ_ret (r_l, rd_l, ()) m_f
                            ⟨hr_le, rng_f, sig_l', scr_f, hsig_l', hscr_f, hK_f, hnv_f, hm_f⟩
                      · c0_hsteps_nogrp
                        exact hJ_ret (r_l, rd_l, ()) ml h_ret_st
                    · c0_hsteps_nogrp
                      exact hJ_ret (r_l, rd_l, ()) ml h_ret_st))
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

/-! ## 3. `fid_collect_cands_wp` (Escalated `max_occ`, Cyclic Cursor) -/

theorem fid_collect_cands_wp (Γ : Env)
    (hSift : M6EnvSpec Γ "full_m6_cand_sift" m6CandSiftSpec) :
    ∀ args m Q X, m6CollectCandsSpec args m Q X →
      Func.wp Γ FullFidelitySweep.full_m6_collect_cands_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  unfold Func.wp FullFidelitySweep.full_m6_collect_cands_body
  have hmx := maxVars_lt_2p31 c
  have hcv_le := hlen.core_ok.cur_vars_le
  have hcv_lt : s.core.cur_vars < 2 ^ 31 := Nat.lt_of_le_of_lt hcv_le hmx
  have hcv_2p64 : s.core.cur_vars < 2 ^ 64 := by omega
  have hfl_len := hlen.core_ok.flags_len
  have hwvec_len := hlen.core_ok.wvec_len
  have htrc_len := hlen.scratch_ok.tarjan_reach_len
  have hws2_len := hlen.scratch_ok.work_stk2_len
  obtain ⟨hgu28, hgu29, hgu30, hgu28', hgu29', hgu30'⟩ :=
    fid_gu_idx_lt hlen.scratch_ok.glue_used_len
  c0_hsteps_nogrp
  c0_hsplit
  · c0_hsteps!
    exact hQ 0#32 s.scratch.tarjan_reach s.scratch.work_stk2 m hlen (Nat.zero_le _)
      (fun _ hi => absurd hi (by simp)) hm
  have hcv_pos : 0 < s.core.cur_vars := by
    have hne : BitVec.ofNat 64 s.core.cur_vars ≠ 0#64 := hc
    rcases Nat.eq_zero_or_pos s.core.cur_vars with h0 | hpos
    · exact absurd (by rw [h0]) hne
    · exact hpos
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i32]) (fun (_comp, ()) mc => mc = m) ?_
    (fun _ hJ_comp => by
      c0_hsplit
      · c0_hsteps!; exact hJ_comp (5#32, ()) m rfl
      · c0_hsteps!; exact hJ_comp (_, ()) m rfl)
  rintro _ ⟨comp, ⟨⟩⟩ mc hmc
  subst mc
  c0_hsteps_nogrp
  refine wp_join_group (ts := [i64]) (fun (cur, ()) mcur => cur.toNat < s.core.cur_vars ∧ mcur = m)
    ?_ (fun _ hJ_cur => by
      c0_hsplit
      · c0_hsteps!; exact hJ_cur (0#64, ()) m ⟨hcv_pos, rfl⟩
      · have hcur_lt : (BitVec.setWidth 64
            (s.scratch.glue_used[(30 : BitVec 64).toNat]'hgu30')).toNat < s.core.cur_vars := by
          have hnot : ¬ (BitVec.ofNat 64 s.core.cur_vars).toNat ≤
              (BitVec.setWidth 64 (s.scratch.glue_used[(30 : BitVec 64).toNat]'hgu30')).toNat := hc
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv_2p64] at hnot
          omega
        c0_hsteps!; exact hJ_cur (_, ()) m ⟨hcur_lt, rfl⟩)
  rintro _ ⟨cur, ⟨⟩⟩ mcur ⟨hcur_lt, hmcur⟩
  subst mcur
  c0_hsteps_nogrp
  refine wp_loop_inv (ts := [i32, i64])
    (fun (nc_l, step_l, ()) ml =>
      step_l.toNat ≤ s.core.cur_vars ∧ nc_l.toNat ≤ step_l.toNat ∧
      ∃ trc_l ws2_l : List (BitVec 32),
        trc_l.length = 2 * c.max_vars ∧ ws2_l.length = 2 * c.max_vars ∧
        (∀ i < nc_l.toNat, (trc_l[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
        (FullMem c { s with scratch := { s.scratch with
          tarjan_reach := trc_l, work_stk2 := ws2_l } } ⋆ R) ml)
    (fun (_, step_l, ()) _ => s.core.cur_vars - step_l.toNat)
    ?_ ?_
  · intro _ hJ_in
    c0_hsteps!
    refine hJ_in (0#32, 0#64, ()) m ⟨Nat.zero_le _, by simp,
      s.scratch.tarjan_reach, s.scratch.work_stk2, htrc_len, hws2_len,
      fun _ hi => absurd (by simp at hi) False.elim, hm⟩
  · rintro _ ⟨nc_l, step_l, ⟨⟩⟩ ml
      ⟨hstep_le, hnc_le, trc_l, ws2_l, htrc_l, hws2_l, hbd_l, hm_l⟩ hJ_in
    have hnc_bd : nc_l.toNat ≤ s.core.cur_vars := Nat.le_trans hnc_le hstep_le
    have hlen_l : ({ s with scratch := { s.scratch with
        tarjan_reach := trc_l, work_stk2 := ws2_l } } : FullState).LengthsOk c :=
      fid_lengthsOk_trc_ws2 hlen htrc_l hws2_l
    c0_hsplit; rotate_left
    · c0_hsplit
      · c0_hsteps!
        exact hQ nc_l trc_l ws2_l ml hlen_l hnc_bd hbd_l hm_l
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
            ⟨by rw [hnc_half]; exact Nat.le_refl _, trc_l, htrc_l, hbd_l, hm_l⟩
        · rintro _ ⟨st_s, ⟨⟩⟩ ms ⟨hst_le, trc_s, htrc_s, hbd_s, hm_s⟩ hJs
          c0_hsplit; rotate_left
          · c0_hsteps_nogrp
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
              · c0_hsteps!
                exact hQ nc_l trc_e ws2_l me (fid_lengthsOk_trc_ws2 hlen htrc_e hws2_l)
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
                rw [fullMem_eq_fidCandsFrame] at hm_e
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
                refine fid_call_cand_sift hSift 0#32 (end_s - 1#32) h0_lt_end1
                  (by rw [htake_len]; exact Nat.le_refl _) (by omega)
                  (by rw [hws2_l]; omega) hsw_bd_end
                  (R := array (t := i32) (c.pTarjanReach + BitVec.ofNat 64 (4 * k))
                    (trc_sw.drop k) ⋆ FidCandsFrame c s ⋆ (R ⋆ emp))
                  (fid_cands_split_mem (R := R ⋆ emp) hk_le (sep_ac (by assumption)))
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
                have hjoin_arr := fidCands_join_array (a := c.pTarjanReach)
                  (suff := trc_sw.drop k) hlen_pk
                have hm_joined : (FullMem c { s with scratch := { s.scratch with
                    tarjan_reach := trc', work_stk2 := ws2_l } } ⋆ R) m' := by
                  rw [fullMem_eq_fidCandsFrame]
                  change (array (t := i32) c.pTarjanReach (trc_p ++ trc_sw.drop k) ⋆
                    array (t := i32) c.pWorkStk2 ws2_l ⋆ FidCandsFrame c s) ⋆ R $ m'
                  rw [← hjoin_arr]
                  exact sep_ac hm'
                c0_hsteps!
                exact hJe (end_s - 1#32, ()) m' (by dsimp only; omega)
                  ⟨by rw [hend1]; omega, trc', htrc'_len, hbd'_all, hm_joined⟩
          · have hst_pos : 0 < st_s.toNat := hc
            have hst_sub : (st_s - 1#32).toNat = st_s.toNat - 1 := by bv_omega
            have hst_lt : (st_s - 1#32).toNat < nc_l.toNat := by omega
            rw [fullMem_eq_fidCandsFrame] at hm_s
            have hm_split : (array (t := i32) c.pTarjanReach trc_s ⋆
                array (t := i32) c.pWorkStk2 ws2_l ⋆ (FidCandsFrame c s ⋆ R)) ms := sep_ac hm_s
            c0_hsteps_nogrp
            refine fid_call_cand_sift hSift (st_s - 1#32) nc_l hst_lt
              (by rw [htrc_s]; omega) (by omega) (by rw [hws2_l]; omega) hbd_s hm_split
              (fun trc' m' hlen' hbd' hm' => ?_)
            c0_hsteps!
            have hm_re : (FullMem c { s with scratch := { s.scratch with
                tarjan_reach := trc', work_stk2 := ws2_l } } ⋆ R) m' := by
              rw [fullMem_eq_fidCandsFrame]; exact sep_ac hm'
            exact hJs (st_s - 1#32, ()) m' (by dsimp only; omega)
              ⟨by rw [hst_sub]; omega, trc', hlen'.trans htrc_s, hbd', hm_re⟩
    · have hstep_lt : step_l.toNat < s.core.cur_vars := by
        have hlt : step_l.toNat < s.core.cur_vars % 2 ^ 64 := hc
        rwa [Nat.mod_eq_of_lt hcv_2p64] at hlt
      have hstep1 : (step_l + 1#64).toNat = step_l.toNat + 1 := bv64_add1_toNat (by omega)
      c0_hsteps_nogrp
      refine wp_join_group (ts := [i64]) (fun (v_l, ()) mv => v_l.toNat < s.core.cur_vars ∧ mv = ml)
        ?_ (fun _ hJv => by
          have hsum : (cur + step_l).toNat = cur.toNat + step_l.toNat := by bv_omega
          c0_hsplit
          · have hge : s.core.cur_vars ≤ (cur + step_l).toNat := by
              have h1 : (BitVec.ofNat 64 s.core.cur_vars).toNat ≤ (cur + step_l).toNat := hc
              rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv_2p64] at h1
            have hsub : ((cur + step_l) - BitVec.ofNat 64 s.core.cur_vars).toNat <
                s.core.cur_vars := by bv_omega
            c0_hsteps!; exact hJv (_, ()) ml ⟨hsub, rfl⟩
          · have hlt : (cur + step_l).toNat < s.core.cur_vars := by
              have hnot : ¬ (BitVec.ofNat 64 s.core.cur_vars).toNat ≤ (cur + step_l).toNat := hc
              rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv_2p64] at hnot; omega
            c0_hsteps!; exact hJv (_, ()) ml ⟨hlt, rfl⟩)
      rintro _ ⟨v_l, ⟨⟩⟩ mv ⟨hv_lt, hmv⟩
      subst mv
      refine wp_join_group (ts := [i32])
        (fun (nc', ()) mj => nc'.toNat ≤ step_l.toNat + 1 ∧
          ∃ trc' ws2' : List (BitVec 32), trc'.length = 2 * c.max_vars ∧
            ws2'.length = 2 * c.max_vars ∧
            (∀ i < nc'.toNat, (trc'[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
            (FullMem c { s with scratch := { s.scratch with
              tarjan_reach := trc', work_stk2 := ws2' } } ⋆ R) mj)
        (fun _ (nc', ()) mj ⟨hnc', trc', ws2', htrc', hws2', hbd', hm'⟩ => by
          c0_hsteps!
          exact hJ_in (nc', step_l + 1#64, ()) mj (by dsimp only; rw [hstep1]; omega)
            ⟨by rw [hstep1]; exact hstep_lt, by rw [hstep1]; exact hnc', trc', ws2', htrc', hws2',
              hbd', hm'⟩)
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
            trc_l, ws2_l, htrc_l, hws2_l, hbd_l, hm_l⟩
          refine wp_join_group (ts := [i32])
            (fun (nc', ()) mj => nc'.toNat ≤ step_l.toNat + 1 ∧
              ∃ trc' ws2' : List (BitVec 32), trc'.length = 2 * c.max_vars ∧
                ws2'.length = 2 * c.max_vars ∧
                (∀ i < nc'.toNat, (trc'[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
                (FullMem c { s with scratch := { s.scratch with
                  tarjan_reach := trc', work_stk2 := ws2' } } ⋆ R) mj)
            (fun _ (nc', ()) mj hinv_j => by
              c0_hsteps_nogrp; exact hJ_v (nc', ()) mj hinv_j)
            (fun _ hJ2 => by
              have h_skip_p : nc_l.toNat ≤ step_l.toNat + 1 ∧
                  ∃ trc' ws2' : List (BitVec 32), trc'.length = 2 * c.max_vars ∧
                    ws2'.length = 2 * c.max_vars ∧
                    (∀ i < nc_l.toNat, (trc'[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
                    (FullMem c { s with scratch := { s.scratch with
                      tarjan_reach := trc', work_stk2 := ws2' } } ⋆ R) ml :=
                ⟨Nat.le_succ_of_le hnc_le, trc_l, ws2_l, htrc_l, hws2_l, hbd_l, hm_l⟩
              c0_hsteps_nogrp <;> try exact hJ2 (nc_l, ()) ml h_skip_p
              have hnc1 : (nc_l + 1#32).toNat = nc_l.toNat + 1 := bv32_add1_toNat (by omega)
              have hv_ws2 : v_l.toNat < ws2_l.length := by rw [hws2_l]; omega
              have hnc_trc : (nc_l.setWidth 64).toNat < trc_l.length := by
                rw [htrc_l, BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]; omega
              refine wp_join_group (ts := [i32]) (fun (_, ()) mp => mp = ml)
                (fun _ (d32_0, ()) mp hmp => by
                  subst mp
                  c0_hsteps_nogrp
                  refine wp_join_group (ts := [i32]) (fun (_, ()) mq => mq = ml)
                    (fun _ (sc, ()) mq hmq => by
                      subst mq
                      have hm_f := hm_l
                      rw [fullMem_eq_fidCandsFrame] at hm_f
                      c0_hsteps_nogrp
                      have hws2_s : (ws2_l.set v_l.toNat sc).length = 2 * c.max_vars := by
                        simp [hws2_l]
                      have htrc_s : (trc_l.set (nc_l.setWidth 64).toNat
                          (BitVec.setWidth 32 v_l)).length = 2 * c.max_vars := by
                        simp [htrc_l]
                      have hnc_trc0 : nc_l.toNat < trc_l.length := by rw [htrc_l]; omega
                      have hbd_s : ∀ i < (nc_l + 1#32).toNat,
                          ((trc_l.set (nc_l.setWidth 64).toNat (BitVec.setWidth 32 v_l))[i]?.getD
                            0#32).toNat < s.core.cur_vars := fun i hi => by
                        rw [hnc1] at hi
                        rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                        by_cases hie : i = nc_l.toNat
                        · subst hie
                          rw [List.getElem?_set_self hnc_trc0, Option.getD_some,
                            BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                          exact hv_lt
                        · rw [List.getElem?_set_ne (Ne.symm hie)]
                          exact hbd_l i (by omega)
                      refine hJ2 (nc_l + 1#32, ()) _
                        ⟨by rw [hnc1]; omega, _, _, htrc_s, hws2_s, hbd_s, ?_⟩
                      rw [fullMem_eq_fidCandsFrame]; exact sep_ac (by assumption))
                    (fun _ hJ_tier => by
                      c0_hsplit
                      · refine wp_join_group (ts := [i32]) (fun (_, ()) m_t => m_t = ml)
                          (fun _ (_t, ()) m_t hm_t => by
                            c0_hsteps!; exact hJ_tier (_, ()) m_t hm_t)
                          (fun _ hJt => by
                            c0_hsplit
                            · c0_hsteps!; exact hJt (_, ()) ml rfl
                            · c0_hsteps!; exact hJt (_, ()) ml rfl)
                      · c0_hsteps!; exact hJ_tier (_, ()) ml rfl))
                (fun _ hJd32 => by
                  c0_hsplit
                  · c0_hsteps!; exact hJd32 (_, ()) ml rfl
                  · c0_hsteps!; exact hJd32 (_, ()) ml rfl)))

end LeanQbe.T.Examples.Kissat.FullFidelitySweep

end
