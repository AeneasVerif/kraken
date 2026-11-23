module

public import LeanQbe.T.Examples.Kissat.FullM6SweepProofSpec

/-!
# Kissat `D-Full` M6 — Candidate Selection & Outer Variable-Loop Proofs (`3` fns)

Parametric `(Γ : Env)` `Func.wp` proofs for the 3 candidate-selection and outer variable-loop
functions in `FullM6Sweep`:
1. `full_m6_cand_sift_wp` (`m6CandSiftSpec`)
2. `full_m6_collect_cands_wp` (`m6CollectCandsSpec`)
3. `full_m6_sweep_vars_wp` (`m6SweepVarsSpec`)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.Examples.Kissat.FullM6Sweep

open Std Std.Sat Std.ExtHashMap
open LeanQbe.T LeanQbe.T.C0HeadStep LeanQbe.T.ProofUtil
open LeanQbe.T.Examples.LratBytes LeanQbe.T.Examples.Kissat
open LeanQbe.T.Examples.Kissat.Full LeanQbe.T.Examples.Kissat.FullM4Sweep
open Kraken.Bedrock2.Test
open FullArenaTactics
open scoped FullArenaTactics
local elab "c0_hfast" : tactic =>
  LeanQbe.T.C0HeadStep.headSteps { pruneJnz := false } 10000

/-! ## 1. Pure BitVector, `array` Focusing, `FullMem` Framing, & Call Helpers -/

private theorem bv32_zext_mul4_eq (idx : BitVec 32) :
    idx.setWidth 64 * 4 = BitVec.ofNat 64 (4 * idx.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have hlt : idx.toNat < 2 ^ 32 := idx.isLt
  simp only [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  have h4 : (4 : BitVec 64).toNat = 4 := rfl
  rw [h4, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega), Nat.mul_comm]

private theorem bv32_shl1_toNat (r : BitVec 32) (hr : 2 * r.toNat < 2 ^ 32) :
    (r <<< (1 : Nat)).toNat = 2 * r.toNat := by
  simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [Nat.mul_comm, Nat.mod_eq_of_lt (by omega)]

private theorem bv32_shl1_add1_toNat (r : BitVec 32) (hr : 2 * r.toNat + 1 < 2 ^ 32) :
    ((r <<< (1 : Nat)) + 1#32).toNat = 2 * r.toNat + 1 := by
  have hsh := bv32_shl1_toNat r (by omega)
  rw [BitVec.toNat_add, hsh, show (1#32 : BitVec 32).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega)]

private theorem bv32_add1_toNat {x : BitVec 32} (hx : x.toNat + 1 < 2 ^ 32) :
    (x + 1#32).toNat = x.toNat + 1 := by bv_omega

private theorem bv32_sub1_toNat {x : BitVec 32} (hx : 0 < x.toNat) :
    (x - 1#32).toNat = x.toNat - 1 := by bv_omega

private theorem bv32_lshr1_toNat (x : BitVec 32) :
    (x >>> (1 : Nat)).toNat = x.toNat / 2 := by bv_omega

private theorem bv64_add1_toNat {x : BitVec 64} (hx : x.toNat + 1 < 2 ^ 64) :
    (x + 1#64).toNat = x.toNat + 1 := by bv_omega

private theorem bv64_shl1_toNat {v : BitVec 64} (hv : v.toNat < 2 ^ 31) :
    (v <<< (1 : Nat)).toNat = 2 * v.toNat := by
  simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [Nat.mul_comm, Nat.mod_eq_of_lt (by omega)]

private theorem bv64_wvec_pos_toNat {v : BitVec 64} (hv : v.toNat < 2 ^ 31) :
    (((v <<< (1 : Nat)) <<< (1 : Nat)) + 1#64).toNat = 4 * v.toNat + 1 := by
  have h0 := bv64_shl1_toNat hv
  have h1 : ((v <<< (1 : Nat)) <<< (1 : Nat)).toNat = 4 * v.toNat := by
    simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, h0]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  rw [BitVec.toNat_add, h1, show (1#64 : BitVec 64).toNat = 1 from rfl,
    Nat.mod_eq_of_lt (by omega)]

private theorem nat_two_mul_lor_one (n : Nat) : 2 * n ||| 1 = 2 * n + 1 := by
  apply Nat.eq_of_testBit_eq
  intro k
  cases k with
  | zero => simp [Nat.testBit_zero]
  | succ k =>
    rw [Nat.testBit_or, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ]
    rw [show 1 / 2 = 0 from rfl, show (2 * n) / 2 = n from by omega,
      show (2 * n + 1) / 2 = n from by omega, Nat.zero_testBit, Bool.or_false]

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

namespace CandsMemTactics

attribute [scoped bv_c0 high] bv_c0_zext32_64

@[scoped bv_c0 high] theorem bv_ofNat64_zero_toNat : (BitVec.ofNat 64 0).toNat = 0 := rfl

@[scoped bv_c0 high] theorem bv_zext32_11_mul4 :
    (BitVec.setWidth 64 (11#32 : BitVec 32)) * 4 = 44#64 := rfl

@[scoped bv_c0 high] theorem bv_ofNat64_11_mul4 :
    BitVec.ofNat 64 11 * 4 = 44#64 := rfl

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

end CandsMemTactics

open scoped CandsMemTactics

private def FullCandsFrame (c : FullCfg) (s : FullState) : Mem 64 → Prop :=
  dimacsState c.hdr (BitVec.ofNat 64 c.mv) (BitVec.ofNat 64 c.nc) s.core.d_cur s.core.d_val ⋆
  array64 (c.hdr + 32) (Full.hdrTailWords c s) ⋆ FullCoreArrays c s.core ⋆
  (FullScrByteArrs c s.scratch ⋆ FullScrU32A c s.scratch ⋆
    (array (t := i32) c.pWsort s.scratch.wsort ⋆
     array (t := i32) c.pWorkStk1 s.scratch.work_stk1 ⋆
     array (t := i32) c.pTarjanMark s.scratch.tarjan_mark) ⋆
    FullScrMetaArrs c s.scratch ⋆ FullScrDynArrs c s.scratch) ⋆
  c.pad

private theorem fullCandsFrame_irrel (c : FullCfg) (s : FullState)
    (trc' ws2' : List (BitVec 32)) :
    FullCandsFrame c
      { s with scratch := { s.scratch with tarjan_reach := trc', work_stk2 := ws2' } } =
      FullCandsFrame c s := rfl

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

private theorem fullCands_join_array {a : BitVec 64} {pref suff : List (BitVec 32)}
    {n : Nat} (hp : pref.length = n) :
    (array (t := i32) a pref ⋆ array (t := i32) (a + BitVec.ofNat 64 (4 * n)) suff) =
      array (t := i32) a (pref ++ suff) := by
  rw [array_append, hp]; rfl

private theorem m6_tmkZero_congr {s s' : FullState} (h : M6TmkZero s)
    (hcv : s'.core.cur_vars = s.core.cur_vars)
    (ht : s'.scratch.tarjan_mark = s.scratch.tarjan_mark) : M6TmkZero s' := by
  intro v hv; rw [ht]; exact h v (hcv ▸ hv)

private theorem m6_lengthsOk_trc_ws2 {c : FullCfg} {s : FullState} (h : s.LengthsOk c)
    {trc' ws2' : List (BitVec 32)} (htrc : trc'.length = 2 * c.max_vars)
    (hws2 : ws2'.length = 2 * c.max_vars) :
    ({ s with scratch := { s.scratch with tarjan_reach := trc', work_stk2 := ws2' } } :
      FullState).LengthsOk c :=
  ⟨h.core_ok, { h.scratch_ok with tarjan_reach_len := htrc, work_stk2_len := hws2 }⟩

private theorem m6_denseInvW_set_trc_ws2 {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
    {s : FullState} (h : FullDenseInvW c F0 F_cur s) {trc' ws2' : List (BitVec 32)}
    (htrc : trc'.length = 2 * c.max_vars) (hws2 : ws2'.length = 2 * c.max_vars) :
    FullDenseInvW c F0 F_cur
      { s with scratch := { s.scratch with tarjan_reach := trc', work_stk2 := ws2' } } :=
  ⟨m6_lengthsOk_trc_ws2 h.1 htrc hws2, h.2.1, h.2.2.1, h.2.2.2.1,
   h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

private theorem m6_denseInvW_set_flags {c : FullCfg} {F0 : CNF Nat} {F_cur : List (List Nat)}
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

private theorem m6_call_max_v {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    {cap : BitVec 64} {m : Mem 64} {k : Tup Val [i64] → Expr Val Cont rs}
    (hk : wp Γ Q X (k (BitVec.ofNat 64 (k6MaxV cap.toNat), ())) m) :
    wp Γ Q X (Expr.call (as := [i64]) (bs := [i64]) "full_m6_max_v" (Arg.var cap, ()) k) m :=
  wp_call_of_spec _ k (hMaxV (cap, ()) m (fun r m' => wp Γ Q X (k r) m') X hk)

private theorem m6_call_dense_prop {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
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

private theorem m6_call_collect_cands {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
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

private theorem m6_call_sweep_var {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
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

private theorem m6_call_sweep_var_fl {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
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
  m6_call_sweep_var hSV (m6_denseInvW_set_flags hdw hfl) hcap hrv
    (m6_tmkZero_congr htmk rfl rfl) hm hk

private theorem m6_call_cand_sift {Γ : Env} {rs : List Ty} {Q : Post rs} {X : XPost}
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

private theorem list_set_swap_bound {xs : List (BitVec 32)} {r c n bound : Nat}
    (hr : r < n) (hc : c < n) (hn : n ≤ xs.length)
    (hbd : ∀ i < n, (xs[i]?.getD 0#32).toNat < bound) :
    ∀ i < n, (((xs.set r (xs[c]'(by omega))).set c
      (xs[r]'(by omega)))[i]?.getD 0#32).toNat < bound := by
  intro i hi
  by_cases hic : i = c
  · subst hic
    rw [List.getElem?_set_self (by simp; omega), Option.getD_some]
    have := hbd r hr
    rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
  · rw [List.getElem?_set_ne (Ne.symm hic)]
    by_cases hir : i = r
    · subst hir
      rw [List.getElem?_set_self (by omega), Option.getD_some]
      have := hbd c hc
      rwa [List.getElem?_eq_getElem (by omega), Option.getD_some] at this
    · rw [List.getElem?_set_ne (Ne.symm hir)]
      exact hbd i hi

/-! ## 2. `full_m6_cand_sift_wp` (`1/3`) -/

theorem full_m6_cand_sift_wp (Γ : Env) :
    ∀ args m Q X, m6CandSiftSpec args m Q X →
      Func.wp Γ full_m6_cand_sift_body args m Q X := by
  rintro ⟨cands_ptr, deg_ptr, start, n, ⟨⟩⟩ m Q X
    ⟨cands, deg, bound, R, hsn, hnc, hn31, hbd, hclt, hm, hQ⟩
  unfold Func.wp full_m6_cand_sift_body
  c0_hsteps_nogrp
  refine wp_while_break_state
    (α := BitVec 32) (β := BitVec 32)
    (fun b => (b, ()))
    (fun _ mb => ∃ candsL : List (BitVec 32), candsL.length = cands.length ∧
      (∀ i < n.toNat, (candsL[i]?.getD 0#32).toNat < bound) ∧
      (array (t := i32) cands_ptr candsL ⋆ array (t := i32) deg_ptr deg ⋆ R) mb)
    (fun r => (r, ()))
    (fun r => n.toNat - r.toNat)
    (fun r ml => r.toNat < n.toNat ∧ ∃ candsL : List (BitVec 32),
      candsL.length = cands.length ∧
      (∀ i < n.toNat, (candsL[i]?.getD 0#32).toNat < bound) ∧
      (array (t := i32) cands_ptr candsL ⋆ array (t := i32) deg_ptr deg ⋆ R) ml)
    (fun _ _ mb ⟨candsL, hlenL, hbdL, hmL⟩ => by
      c0_hfast
      exact hQ candsL mb hlenL hbdL hmL)
    (fun _ L r ml hB hL ⟨hrn, candsL, hlenL, hbdL, hmL⟩ => by
      c0_hsplit; rotate_left
      · c0_hfast; exact hB r ml ⟨candsL, hlenL, hbdL, hmL⟩
      have hr_shl : (r <<< (1 : Nat)).toNat = 2 * r.toNat := bv32_shl1_toNat r (by omega)
      have hc_eq : ((r <<< (1 : Nat)) + 1#32).toNat = 2 * r.toNat + 1 :=
        bv32_shl1_add1_toNat r (by omega)
      c0_hsplit
      · c0_hfast; exact hB r ml ⟨candsL, hlenL, hbdL, hmL⟩
      have hcn : (r <<< (1 : Nat) + 1#32).toNat < n.toNat := by
        rw [hc_eq]; rw [hr_shl] at hc; bv_omega
      have hc1_eq : ((r <<< (1 : Nat) + 1#32) + 1#32).toNat = 2 * r.toNat + 2 := by
        rw [bv32_add1_toNat (by omega), hc_eq]
      have hdeg_idx : ∀ (i : BitVec 32) (hi : i.toNat < n.toNat),
          (candsL[i.toNat]'(by omega)).toNat < deg.length := fun i hi => by
        have h1 := hbdL i.toNat hi
        rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at h1
        omega
      have hcr_deg := hdeg_idx r hrn
      c0_hsteps_nogrp
      refine wp_join_state1 (fun c' : BitVec 32 => c')
        (fun c' mj => mj = ml ∧ r.toNat < c'.toNat ∧ c'.toNat < n.toNat)
        (fun _ c' mj ⟨hmj, hrc', hc'n⟩ => by
          have hcc'_deg := hdeg_idx c' hc'n
          rw [← hmj] at hmL
          c0_hsplit
          · c0_hfast
            exact hB r mj ⟨candsL, hlenL, hbdL, hmL⟩
          · c0_hfast
            have hswap := list_set_swap_bound hrn hc'n (by omega) hbdL
            refine hL c' _ (by omega) ⟨hc'n, _, by simp [hlenL], hswap, ?_⟩
            simpa [sep_emp] using sep_ac hm)
        (fun _ hJ => by
          c0_hsplit
          · have hc1n : ((r <<< (1 : Nat) + 1#32) + 1#32).toNat < n.toNat := by
              rw [hc1_eq]; rw [hr_shl] at hc; bv_omega
            have hc0_deg := hdeg_idx (r <<< (1 : Nat) + 1#32) hcn
            have hc1_deg := hdeg_idx (r <<< (1 : Nat) + 1#32 + 1#32) hc1n
            c0_hsplit
            · c0_hfast
              exact hJ (r <<< (1 : Nat) + 1#32 + 1#32) ml ⟨rfl, by omega, hc1n⟩
            · c0_hfast
              exact hJ (r <<< (1 : Nat) + 1#32) ml ⟨rfl, by omega, hcn⟩
          · c0_hfast
            exact hJ (r <<< (1 : Nat) + 1#32) ml ⟨rfl, by omega, hcn⟩))
    (fun _ _ _ hL => by
      c0_hfast
      exact hL start m ⟨hsn, cands, rfl, hclt, hm⟩)

/-! ## 3. `full_m6_collect_cands_wp` (`2/3`) -/

theorem full_m6_collect_cands_wp (Γ : Env)
    (hSift : M6EnvSpec Γ "full_m6_cand_sift" m6CandSiftSpec) :
    ∀ args m Q X, m6CollectCandsSpec args m Q X →
      Func.wp Γ full_m6_collect_cands_body args m Q X := by
  rintro ⟨h, ⟨⟩⟩ m Q X ⟨c, s, R, rfl, hlen, hm, hQ⟩
  have hcv_le := hlen.core_ok.cur_vars_le
  have hmx := maxVars_lt_2p31 c
  have hcv_lt64 : s.core.cur_vars < 2 ^ 64 := by omega
  have hcv_mod : (BitVec.ofNat 64 s.core.cur_vars).toNat = s.core.cur_vars := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcv_lt64]
  have hfl_len := hlen.core_ok.flags_len
  have hvals_len := hlen.core_ok.vals_len
  have hwvec_len := hlen.core_ok.wvec_len
  have htrc_len := hlen.scratch_ok.tarjan_reach_len
  have hws2_len := hlen.scratch_ok.work_stk2_len
  unfold Func.wp full_m6_collect_cands_body
  c0_hsplit
  · c0_hfast
    have h0 : (0#32 : BitVec 32).toNat ≤ s.core.cur_vars := Nat.zero_le _
    refine hQ 0#32 s.scratch.tarjan_reach s.scratch.work_stk2 m hlen h0
      (fun _ hi => by simp at hi) hm
  have hcv_pos : 0 < s.core.cur_vars := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hne : BitVec.ofNat 64 s.core.cur_vars ≠ 0#64 := ‹_›
    apply hne; rw [hz]
  c0_hsteps_nogrp
  refine wp_while_state (ts := [i32, i64])
    (α := BitVec 32 × BitVec 64)
    (fun st => (st.1, st.2, ()))
    (fun st => s.core.cur_vars - st.2.toNat)
    (fun st ml => st.1.toNat ≤ st.2.toNat ∧ st.2.toNat ≤ s.core.cur_vars ∧
      ∃ trc ws2, trc.length = 2 * c.max_vars ∧ ws2.length = 2 * c.max_vars ∧
      (∀ i < st.1.toNat, (trc[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
      (FullMem c { s with scratch := { s.scratch with tarjan_reach := trc, work_stk2 := ws2 } }
        ⋆ R) ml)
    (fun _ hJ => by
      c0_hfast
      exact hJ (0#32, 0#64) m ⟨Nat.zero_le _, Nat.zero_le _, s.scratch.tarjan_reach,
        s.scratch.work_stk2, htrc_len, hws2_len, fun _ hi => by simp at hi, hm⟩)
    (fun _ ⟨nc, v⟩ ml ⟨hnc_le, hv_le, trc, ws2, htrcL, hws2L, hbdL, hmL⟩ hJ => by
      dsimp only at hnc_le hv_le hbdL
      let sL : FullState :=
        { s with scratch := { s.scratch with tarjan_reach := trc, work_stk2 := ws2 } }
      have hlenL : sL.LengthsOk c := m6_lengthsOk_trc_ws2 hlen htrcL hws2L
      change (FullMem c sL ⋆ R) ml at hmL
      c0_hsplit
      · have hv_lt : v.toNat < s.core.cur_vars := by rw [← hcv_mod]; exact ‹_›
        have hv1 : (v + 1#64).toNat = v.toNat + 1 := bv64_add1_toNat (by omega)
        have hnc1 : (nc + 1#32).toNat = nc.toNat + 1 := bv32_add1_toNat (by omega)
        have hv_fl : v.toNat < sL.core.flags.length := by dsimp [sL]; omega
        have hv_2v : (v <<< (1 : Nat)).toNat = 2 * v.toNat := bv64_shl1_toNat (by omega)
        have hv_vals : (v <<< (1 : Nat)).toNat < sL.core.vals.length := by
          rw [hv_2v]; dsimp [sL]; omega
        have hv_pos_w : (((v <<< (1 : Nat)) <<< (1 : Nat)) + 1#64).toNat = 4 * v.toNat + 1 :=
          bv64_wvec_pos_toNat (by omega)
        have hv_neg_w :
            ((((v <<< (1 : Nat)) ||| 1#64) <<< (1 : Nat)) + 1#64).toNat = 4 * v.toNat + 3 :=
          bv64_wvec_neg_toNat (by omega)
        have hwp : (((v <<< (1 : Nat)) <<< (1 : Nat)) + 1#64).toNat < sL.core.wvec.length := by
          rw [hv_pos_w]; dsimp [sL]; omega
        have hwn :
            ((((v <<< (1 : Nat)) ||| 1#64) <<< (1 : Nat)) + 1#64).toNat < sL.core.wvec.length := by
          rw [hv_neg_w]; dsimp [sL]; omega
        have hv_ws2 : v.toNat < sL.scratch.work_stk2.length := by dsimp [sL]; omega
        have hnc_trc : nc.toNat < sL.scratch.tarjan_reach.length := by dsimp [sL]; omega
        c0_hsteps_nogrp
        refine wp_join_state1 (fun nc' : BitVec 32 => nc')
          (fun nc' mj => nc'.toNat ≤ v.toNat + 1 ∧
            ∃ trc' ws2', trc'.length = 2 * c.max_vars ∧ ws2'.length = 2 * c.max_vars ∧
            (∀ i < nc'.toNat, (trc'[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
            (FullMem c { s with scratch :=
              { s.scratch with tarjan_reach := trc', work_stk2 := ws2' } } ⋆ R) mj)
          (fun _ nc' mj ⟨h1, trc', ws2', htrc', hws2', hbd', hm'⟩ => by
            c0_hfast
            exact hJ (nc', v + 1#64) mj (by dsimp only; omega)
              ⟨by dsimp only; omega, by dsimp only; omega, trc', ws2', htrc', hws2', hbd', hm'⟩)
          (fun _ hJin => by
            c0_hsplit; rotate_left
            · c0_hfast
              exact hJin nc ml ⟨by omega, trc, ws2, htrcL, hws2L, hbdL, hmL⟩
            c0_hsplit; rotate_left
            · c0_hfast
              exact hJin nc ml ⟨by omega, trc, ws2, htrcL, hws2L, hbdL, hmL⟩
            have hbd_new : ∀ i < (nc + 1#32).toNat,
                ((trc.set nc.toNat (v.setWidth 32))[i]?.getD 0#32).toNat < s.core.cur_vars := by
              intro i hi
              by_cases hinc : i = nc.toNat
              · subst hinc
                rw [List.getElem?_set_self (by dsimp [sL] at hnc_trc; omega), Option.getD_some,
                  BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega)]
                exact hv_lt
              · rw [List.getElem?_set_ne (Ne.symm hinc)]
                exact hbdL i (by omega)
            c0_hfast
            all_goals
              have hm_upd : ∃ deg_v : BitVec 32,
                  (FullMem c { s with scratch := { s.scratch with
                    tarjan_reach := trc.set nc.toNat (v.setWidth 32),
                    work_stk2 := ws2.set v.toNat deg_v } } ⋆ R) m := by
                refine ⟨?_, ?_⟩
                rotate_left
                rw [← bv_c0_zext32_64 (x := nc)]
                dsimp only [sL]
                assumption
              obtain ⟨deg_v, hm_upd'⟩ := hm_upd
              exact hJin (nc + 1#32) m ⟨by omega, trc.set nc.toNat (v.setWidth 32),
                ws2.set v.toNat deg_v, by simp [htrcL], by simp [hws2L], hbd_new, hm_upd'⟩)
      · have hv_eq : v.toNat = s.core.cur_vars := by rw [← hcv_mod] at *; bv_omega
        have hnc_cur : nc.toNat ≤ s.core.cur_vars := by omega
        c0_hsplit
        · c0_hfast
          exact hQ nc trc ws2 ml hlenL hnc_cur hbdL hmL
        have hnc_ge2 : 2 ≤ nc.toNat := by bv_omega
        c0_hsteps_nogrp
        refine wp_while_state1 (t := i32) (α := BitVec 32)
          (fun x => x) (fun x => x.toNat)
          (fun x ml1 => x.toNat ≤ nc.toNat ∧ ∃ trc1, trc1.length = 2 * c.max_vars ∧
            (∀ i < nc.toNat, (trc1[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
            (FullMem c { s with scratch :=
              { s.scratch with tarjan_reach := trc1, work_stk2 := ws2 } } ⋆ R) ml1)
          (fun _ hJs => by
            c0_hfast
            exact hJs (nc >>> 1#32) ml
              ⟨by rw [show nc >>> 1#32 = nc >>> (1 : Nat) from rfl, bv32_lshr1_toNat]; omega,
               trc, htrcL, hbdL, hmL⟩)
          (fun _ s_i ml1 ⟨hsi_le, trc1, htrc1L, hbd1L, hm1⟩ hJs => by
            c0_hsplit
            · have hsi_pos : 0 < s_i.toNat := by bv_omega
              have hsi1 : (s_i - 1#32).toNat = s_i.toNat - 1 := bv32_sub1_toNat hsi_pos
              c0_hsteps_nogrp
              have hm_focus : (array (t := i32) c.pTarjanReach trc1 ⋆
                  array (t := i32) c.pWorkStk2 ws2 ⋆
                  (FullCandsFrame c { s with scratch :=
                    { s.scratch with tarjan_reach := trc1, work_stk2 := ws2 } } ⋆ R)) ml1 := by
                rw [fullMem_eq_candsFrame] at hm1; exact sep_ac hm1
              refine m6_call_cand_sift hSift (bound := s.core.cur_vars) (s_i - 1#32) nc
                (by omega) (by omega) (by omega) (by omega) hbd1L hm_focus
                fun trc2 m2 htrc2L hbd2L hm2 => ?_
              have hm2_full : (FullMem c { s with scratch :=
                  { s.scratch with tarjan_reach := trc2, work_stk2 := ws2 } } ⋆ R) m2 := by
                rw [fullMem_eq_candsFrame, fullCandsFrame_irrel]; exact sep_ac hm2
              c0_hfast
              exact hJs (s_i - 1#32) m2 (by omega)
                ⟨by omega, trc2, by omega, hbd2L, hm2_full⟩
            · c0_hsteps_nogrp
              refine wp_while_state1 (t := i32) (α := BitVec 32)
                (fun x => x) (fun x => x.toNat)
                (fun x ml2 => 1 ≤ x.toNat ∧ x.toNat ≤ nc.toNat ∧ ∃ trc2,
                  trc2.length = 2 * c.max_vars ∧
                  (∀ i < nc.toNat, (trc2[i]?.getD 0#32).toNat < s.core.cur_vars) ∧
                  (FullMem c { s with scratch :=
                    { s.scratch with tarjan_reach := trc2, work_stk2 := ws2 } } ⋆ R) ml2)
                (fun _ hJe => by
                  c0_hfast
                  exact hJe nc ml1 ⟨by omega, Nat.le_refl _, trc1, htrc1L, hbd1L, hm1⟩)
                (fun _ end_v ml2 ⟨hend1, hend_le, trc2, htrc2L, hbd2L, hm2⟩ hJe => by
                  c0_hsplit; rotate_left
                  · c0_hfast
                    exact hQ nc trc2 ws2 ml2 (m6_lengthsOk_trc_ws2 hlen htrc2L hws2L)
                      hnc_cur hbd2L hm2
                  have hend_gt1 : 1 < end_v.toNat := by bv_omega
                  have hend1_eq : (end_v - 1#32).toNat = end_v.toNat - 1 :=
                    bv32_sub1_toNat (by omega)
                  let end' := end_v - 1#32
                  have hend'_eq : end'.toNat = end_v.toNat - 1 := hend1_eq
                  have h0_trc : 0 < trc2.length := by omega
                  have hend'_trc : end'.toNat < trc2.length := by omega
                  have hm2_arr : (array (t := i32) c.pTarjanReach trc2 ⋆
                      (array (t := i32) c.pWorkStk2 ws2 ⋆
                       (FullCandsFrame c { s with scratch :=
                         { s.scratch with tarjan_reach := trc2, work_stk2 := ws2 } } ⋆
                        R))) ml2 := by
                    rw [fullMem_eq_candsFrame] at hm2; exact sep_ac hm2
                  c0_hsteps_nogrp
                  let trc3 := (trc2.set 0 (trc2[end'.toNat]'hend'_trc)).set end'.toNat
                    (trc2[0]'h0_trc)
                  have htrc3L : trc3.length = 2 * c.max_vars := by
                    dsimp only [trc3]; simp [htrc2L]
                  have hbd3L : ∀ i < nc.toNat, (trc3[i]?.getD 0#32).toNat < s.core.cur_vars := by
                    simpa [trc3] using list_set_swap_bound (n := nc.toNat) (by omega)
                      (by omega) (by omega) hbd2L
                  have hm3_split : (array (t := i32) c.pTarjanReach (trc3.take end'.toNat) ⋆
                      array (t := i32) c.pWorkStk2 ws2 ⋆
                      (array (t := i32) (c.pTarjanReach + BitVec.ofNat 64 (4 * end'.toNat))
                        (trc3.drop end'.toNat) ⋆
                       FullCandsFrame c { s with scratch :=
                         { s.scratch with tarjan_reach := trc2, work_stk2 := ws2 } } ⋆
                       R)) m := by
                    have hm_sw : (array (t := i32) c.pTarjanReach trc3 ⋆
                        (array (t := i32) c.pWorkStk2 ws2 ⋆
                         (FullCandsFrame c { s with scratch :=
                           { s.scratch with tarjan_reach := trc2, work_stk2 := ws2 } } ⋆
                          R))) m := by
                      have h1 := hm
                      simp only [bv_c0_zext32_64,
                        CandsMemTactics.bv_ofNat64_zero_toNat] at h1
                      have hend_trc : (end_v - 1).toNat < trc2.length := hend'_trc
                      have hlist :
                          (trc2.set 0 trc2[(end_v - 1).toNat]).set (end_v - 1).toNat
                            trc2[0] = trc3 := by
                        dsimp only [trc3, end']; rfl
                      rwa [hlist] at h1
                    rw [fullCands_split_array (n := end'.toNat) (by omega)] at hm_sw
                    exact sep_ac hm_sw
                  refine m6_call_cand_sift hSift (bound := s.core.cur_vars) 0#32 end'
                    (by rw [show (0#32 : BitVec 32).toNat = 0 from rfl]; omega)
                    (by simp [htrc3L]; omega) (by omega) (by omega)
                    (fun i hi => by
                      rw [List.getElem?_take_of_lt hi]; exact hbd3L i (by omega))
                    hm3_split fun pref' m3 hprefL hbdP hm3' => ?_
                  have hprefL' : pref'.length = end'.toNat := by
                    rw [hprefL, List.length_take_of_le (by omega)]
                  let trc4 := pref' ++ trc3.drop end'.toNat
                  have htrc4L : trc4.length = 2 * c.max_vars := by
                    dsimp only [trc4]; rw [List.length_append, hprefL', List.length_drop, htrc3L]
                    omega
                  have hbd4L : ∀ i < nc.toNat, (trc4[i]?.getD 0#32).toNat < s.core.cur_vars := by
                    intro i hi
                    by_cases hie : i < end'.toNat
                    · dsimp only [trc4]
                      rw [List.getElem?_append_left (by rw [hprefL']; exact hie)]
                      exact hbdP i hie
                    · dsimp only [trc4]
                      rw [List.getElem?_append_right (by rw [hprefL']; omega),
                        hprefL', List.getElem?_drop]
                      have heq : end'.toNat + (i - end'.toNat) = i := by omega
                      rw [heq]; exact hbd3L i hi
                  have hm4 : (FullMem c { s with scratch :=
                      { s.scratch with tarjan_reach := trc4, work_stk2 := ws2 } } ⋆ R) m3 := by
                    have hm3_arr : (array (t := i32) c.pTarjanReach trc4 ⋆
                        array (t := i32) c.pWorkStk2 ws2 ⋆
                        FullCandsFrame c { s with scratch :=
                          { s.scratch with tarjan_reach := trc2, work_stk2 := ws2 } } ⋆
                        R) m3 := by
                      have hm3a : ((array (t := i32) c.pTarjanReach pref' ⋆
                          array (t := i32) (c.pTarjanReach + BitVec.ofNat 64 (4 * end'.toNat))
                            (trc3.drop end'.toNat)) ⋆
                          array (t := i32) c.pWorkStk2 ws2 ⋆
                          FullCandsFrame c { s with scratch :=
                            { s.scratch with tarjan_reach := trc2, work_stk2 := ws2 } } ⋆
                          R) m3 := sep_ac hm3'
                      rwa [fullCands_join_array hprefL'] at hm3a
                    rw [fullMem_eq_candsFrame, fullCandsFrame_irrel]
                    exact sep_ac hm3_arr
                  c0_hfast
                  exact hJe end' m3 (by omega)
                    ⟨by omega, by omega, trc4, htrc4L, hbd4L, hm4⟩)))

/-! ## 4. `full_m6_sweep_vars_wp` (`3/3`) -/

theorem full_m6_sweep_vars_wp (Γ : Env)
    (hMaxV : M6EnvSpec Γ "full_m6_max_v" m6MaxVSpec)
    (hDenseProp : M6EnvSpec Γ "full_m6_dense_prop" m6DensePropSpec)
    (hCollect : M6EnvSpec Γ "full_m6_collect_cands" m6CollectCandsSpec)
    (hSweepVar : M6EnvSpec Γ "full_m6_sweep_var" m6SweepVarSpec) :
    ∀ args m Q X, m6SweepVarsSpec args m Q X →
      Func.wp Γ full_m6_sweep_vars_body args m Q X := by
  rintro ⟨h, budget, tick_lim, ⟨⟩⟩ m Q X ⟨c, F0, s, R, rfl, hinv, htmk, hm, hQ⟩
  obtain ⟨F_cur, hdw⟩ := hinv.exists_witness
  have hlen := hdw.1
  unfold Func.wp full_m6_sweep_vars_body
  c0_hsteps_nogrp
  refine m6_call_max_v hMaxV (cap := BitVec.ofNat 64 c.scratch_cap) ?_
  have hmv_lt32 : k6MaxV (BitVec.ofNat 64 c.scratch_cap).toNat < 2 ^ 32 := k6MaxV_lt_2p32 _
  have hscr_mod : (BitVec.ofNat 64 c.scratch_cap).toNat = c.scratch_cap := by
    have hs := c.hscr; unfold dimacsBound at hs
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  c0_hsplit
  · c0_hfast
    exact hQ 1#64 s m hinv rfl (Nat.le_refl _) htmk (Or.inl rfl) (fun h => by cases h) hm
  c0_hsplit
  · c0_hfast
    exact hQ 1#64 s m hinv rfl (Nat.le_refl _) htmk (Or.inl rfl) (fun h => by cases h) hm
  c0_hsplit
  · c0_hfast
    exact hQ 1#64 s m hinv rfl (Nat.le_refl _) htmk (Or.inl rfl) (fun h => by cases h) hm
  have hcap : k6MinScr ≤ c.scratch_cap := by
    apply Classical.byContradiction
    intro hlt
    have hlt' : c.scratch_cap < k6MinScr := Nat.lt_of_not_le hlt
    have hzero : k6MaxV (BitVec.ofNat 64 c.scratch_cap).toNat = 0 := by
      rw [hscr_mod]; exact k6MaxV_eq_zero hlt'
    have hne0 : (BitVec.ofNat 64 (k6MaxV (BitVec.ofNat 64 c.scratch_cap).toNat)).setWidth 32 ≠
        0#32 := ‹_›
    apply hne0; rw [hzero]; rfl
  obtain ⟨L, hL_len, hL_mv⟩ :
      ∃ L : K6Layout, L.scrLen = c.scratch_cap ∧ L.maxV = k6MaxV c.scratch_cap :=
    ⟨k6LayoutOfCap c.scratch_cap hcap c.hscr, k6LayoutOfCap_scrLen hcap c.hscr, rfl⟩
  have hmv_eq : (BitVec.ofNat 64 (k6MaxV (BitVec.ofNat 64 c.scratch_cap).toNat)).setWidth 32 =
      L.mv32 := by
    rw [hscr_mod, ← hL_mv]; exact k6_mv32_zext L
  have hkptr_c0 : c.pScratchBuf + ((1280 : BitVec 32) +
      ((BitVec.ofNat 64 (k6MaxV (BitVec.ofNat 64 c.scratch_cap).toNat)).setWidth 32 <<<
        (1 : Nat))).setWidth 64 * 4 = L.kPtr c.pScratchBuf := by
    rw [hmv_eq]; exact k6_ptr_base_k6Base L c.pScratchBuf
  c0_hsteps_nogrp
  refine m6_call_dense_prop hDenseProp hdw hm
    fun ok1 s1 m1 hdw1 hcv1 hfl1 htmk1 _ hok1 hno1 hm1 => ?_
  have htmk_s1 : M6TmkZero s1 := m6_tmkZero_congr htmk hcv1 htmk1
  c0_hsplit; rotate_left
  · c0_hfast
    have hok1_f : ok1 = false := by
      first | exact ‹ok1 = false› | exact Bool.eq_false_iff.mpr ‹¬ ok1 = true›
    exact hQ 20#64 s1 m1 hdw1.toDense hcv1 (hfl1 ▸ Nat.le_refl _) htmk_s1 (Or.inr rfl)
      (fun _ => (hno1 hok1_f).1) hm1
  c0_hsteps_nogrp
  refine m6_call_collect_cands hCollect hdw1.1 hm1 fun nc trc2 ws2_2 m2 hlen2 hnc_cv hbd2 hm2 => ?_
  let s2 : FullState :=
    { s1 with scratch := { s1.scratch with tarjan_reach := trc2, work_stk2 := ws2_2 } }
  have hdw2 : FullDenseInvW c F0 F_cur s2 :=
    m6_denseInvW_set_trc_ws2 hdw1 hlen2.scratch_ok.tarjan_reach_len hlen2.scratch_ok.work_stk2_len
  have hcv2 : s2.core.cur_vars = s.core.cur_vars := hcv1
  have hfl2 : s2.core.fuel = s.core.fuel := hfl1
  have htmk2 : M6TmkZero s2 := m6_tmkZero_congr htmk_s1 rfl rfl
  have hnc_lt31 : nc.toNat < 2 ^ 31 := by
    have := hdw2.1.core_ok.cur_vars_le
    have := maxVars_lt_2p31 c
    omega
  c0_hsplit
  · c0_hfast
    exact hQ 1#64 s2 m2 hdw2.toDense hcv2 (hfl2 ▸ Nat.le_refl _) htmk2 (Or.inl rfl)
      (fun h => by cases h) hm2
  c0_hsteps_nogrp
  rw [hkptr_c0]
  refine wp_join_state1 (fun rt : BitVec 64 => rt) (fun _ mj => mj = m2)
    (fun _ rem_ticks0 mj hmj => by
      cases hmj
      c0_hsteps_nogrp
      refine wp_join_state1 (fun pv : BitVec 64 => pv) (fun _ mj' => mj' = m2)
        (fun _ per_v mj' hmj' => by
          cases hmj'
          c0_hsteps_nogrp
          refine wp_while_state (ts := [i64, i32, i64])
            (α := BitVec 64 × BitVec 32 × BitVec 64)
            (fun st => (st.1, st.2.1, st.2.2, ()))
            (fun st => nc.toNat - st.2.1.toNat)
            (fun st ml => st.2.1.toNat ≤ nc.toNat ∧ ∃ sL : FullState,
              FullDenseInvW c F0 F_cur sL ∧ sL.core.cur_vars = s.core.cur_vars ∧
              sL.core.fuel.toNat ≤ s.core.fuel.toNat ∧ M6TmkZero sL ∧
              sL.scratch.tarjan_reach = trc2 ∧ (FullMem c sL ⋆ R) ml)
            (fun _ hJ => by
              c0_hfast
              exact hJ (rem_ticks0, 0#32, budget) m2
                ⟨Nat.zero_le _, s2, hdw2, hcv2, hfl2 ▸ Nat.le_refl _, htmk2, rfl, hm2⟩)
            (fun _ ⟨rem_t, ci, rem_b⟩ ml
                ⟨hci_le, sL, hdwL, hcvL, hflL, htmkL, htrcL, hmL⟩ hJloop => by
              dsimp only at hci_le
              c0_hsteps_nogrp
              refine wp_join0 (P := fun mb => ∃ sB : FullState, FullDenseInvW c F0 F_cur sB ∧
                  sB.core.cur_vars = s.core.cur_vars ∧ sB.core.fuel.toNat ≤ s.core.fuel.toNat ∧
                  M6TmkZero sB ∧ (FullMem c sB ⋆ R) mb)
                (fun _ mb ⟨sB, hdwB, hcvB, hflB, htmkB, hmB⟩ => by
                  c0_hsteps_nogrp
                  c0_hsplit
                  all_goals c0_hfast
                  all_goals (
                    first
                    | exact hQ 1#64 sB mb hdwB.toDense hcvB hflB htmkB (Or.inl rfl)
                        (fun h => by cases h) hmB
                    | exact hQ 20#64 sB mb hdwB.toDense hcvB hflB htmkB (Or.inr rfl)
                        (fun _ => hdwB.toDense.inconsistent_unsat (by bv_omega)) hmB))
                (fun _ hJbrk => by
                  c0_hsplit; rotate_left
                  · c0_hfast; exact hJbrk ml ⟨sL, hdwL, hcvL, hflL, htmkL, hmL⟩
                  c0_hsplit; rotate_left
                  · c0_hfast; exact hJbrk ml ⟨sL, hdwL, hcvL, hflL, htmkL, hmL⟩
                  c0_hsplit; rotate_left
                  · c0_hfast; exact hJbrk ml ⟨sL, hdwL, hcvL, hflL, htmkL, hmL⟩
                  c0_hsplit; rotate_left
                  · c0_hfast; exact hJbrk ml ⟨sL, hdwL, hcvL, hflL, htmkL, hmL⟩
                  c0_hsplit; rotate_left
                  · c0_hfast; exact hJbrk ml ⟨sL, hdwL, hcvL, hflL, htmkL, hmL⟩
                  c0_hsplit; rotate_left
                  · c0_hfast; exact hJbrk ml ⟨sL, hdwL, hcvL, hflL, htmkL, hmL⟩
                  have hci_lt : ci.toNat < nc.toNat := ‹_›
                  have hci1 : (ci + 1#32).toNat = ci.toNat + 1 := bv32_add1_toNat (by omega)
                  have hci_trc : ci.toNat < sL.scratch.tarjan_reach.length := by
                    rw [htrcL, hlen2.scratch_ok.tarjan_reach_len]
                    have := hdw2.1.core_ok.cur_vars_le; omega
                  let v := sL.scratch.tarjan_reach[ci.toNat]'hci_trc
                  have hv_lt : v.toNat < sL.core.cur_vars := by
                    have hv_bd := hbd2 ci.toNat hci_lt
                    rw [← htrcL, List.getElem?_eq_getElem hci_trc, Option.getD_some] at hv_bd
                    rw [hcvL, ← hcv1]; exact hv_bd
                  have hv_fl : v.toNat < sL.core.flags.length := by
                    have := hdwL.1.core_ok.flags_len; have := hdwL.1.core_ok.cur_vars_le; omega
                  have hv_shl : (v <<< (1 : Nat)).toNat = 2 * v.toNat := by
                    have := hdwL.1.core_ok.cur_vars_le; have := maxVars_lt_2p31 c
                    simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
                    rw [Nat.mul_comm, Nat.mod_eq_of_lt (by omega)]
                  have hv_vals : ((v <<< (1 : Nat)).setWidth 64).toNat < sL.core.vals.length := by
                    rw [bv_c0_zext32_64, hv_shl, hdwL.1.core_ok.vals_len]
                    have := hdwL.1.core_ok.cur_vars_le; omega
                  c0_hfast
                  all_goals
                    try
                      exact hJloop (rem_t, ci + 1#32, rem_b) ml
                        (by
                          show nc.toNat - (ci + 1#32).toNat < nc.toNat - ci.toNat
                          rw [hci1]; omega)
                        ⟨by show (ci + 1#32).toNat ≤ nc.toNat; omega,
                          sL, hdwL, hcvL, hflL, htmkL, htrcL, hmL⟩
                  all_goals
                    refine m6_call_sweep_var_fl hSweepVar (s := sL) hm hdwL
                      (by simp [hdwL.1.core_ok.flags_len]) hcap
                      (by simpa only [bv_c0_zext32_64] using hv_lt) htmkL
                      fun r_sv sLb mLb hdwLb hcvLb hflLb htmkLb htrcLb hr_sv huns_sv hmLb => ?_
                    c0_hsplit
                    · c0_hfast
                      exact hQ 20#64 sLb mLb hdwLb.toDense (hcvLb.trans hcvL)
                        (Nat.le_trans hflLb hflL) htmkLb (Or.inr rfl)
                        (fun _ => huns_sv (by bv_omega)) hmLb
                    · c0_hsteps_nogrp
                      refine wp_join_state0
                        (α := FullState)
                        (fun sLd mLd => FullDenseInvW c F0 F_cur sLd ∧
                          sLd.core.cur_vars = s.core.cur_vars ∧
                          sLd.core.fuel.toNat ≤ s.core.fuel.toNat ∧ M6TmkZero sLd ∧
                          sLd.scratch.tarjan_reach = trc2 ∧ (FullMem c sLd ⋆ R) mLd) ?_ ?_
                      · intro _ sLd mLd ⟨hdwLd, hcvLd, hflLd, htmkLd, htrcLd, hmLd⟩
                        have hscrLd := hdwLd.1.scratch_ok.scratch_buf_len
                        have hld_ticks := CandsMemTactics.load_k6_ticks hL_len hscrLd hmLd
                        c0_hsteps_nogrp
                        simp only [show (BitVec.ofNat 64 11 * 4 : BitVec 64) = 44#64 from rfl]
                        c0_hsteps_nogrp
                        refine wp_join_state1 (t := i64) (fun rt' : BitVec 64 => rt')
                          (fun _ mj' => mj' = mLd) ?_ ?_
                        · intro _ rem_t' mj' hmj'
                          rw [hmj']
                          c0_hfast
                          exact hJloop (rem_t', ci + 1#32, rem_b - 1#64) mLd
                            (by
                              show nc.toNat - (ci + 1#32).toNat < nc.toNat - ci.toNat
                              rw [hci1]; omega)
                            ⟨by show (ci + 1#32).toNat ≤ nc.toNat; omega,
                              sLd, hdwLd, hcvLd, hflLd, htmkLd, htrcLd, hmLd⟩
                        · intro _ hJrt'
                          c0_hsplit
                          · c0_hfast; exact hJrt' 0#64 mLd rfl
                          · c0_hfast; exact hJrt' _ mLd rfl
                      · intro _ hJdp
                        c0_hsplit; rotate_left
                        · c0_hfast
                          exact hJdp sLb mLb
                            ⟨hdwLb, hcvLb.trans hcvL, Nat.le_trans hflLb hflL, htmkLb,
                             htrcLb.trans htrcL, hmLb⟩
                        c0_hsteps_nogrp
                        refine m6_call_dense_prop hDenseProp hdwLb hmLb
                          fun ok2 sLc mLc hdwLc hcvLc hflLc htmkLc htrcLc hok2 hno2 hmLc => ?_
                        have htmkLc' : M6TmkZero sLc :=
                          m6_tmkZero_congr htmkLb hcvLc htmkLc
                        c0_hsplit; rotate_left
                        · c0_hfast
                          have hok2_f : ok2 = false := by
                            first
                            | exact ‹ok2 = false›
                            | exact Bool.eq_false_iff.mpr ‹¬ ok2 = true›
                          exact hQ 20#64 sLc mLc hdwLc.toDense
                            (hcvLc.trans (hcvLb.trans hcvL))
                            (by rw [hflLc]; exact Nat.le_trans hflLb hflL)
                            htmkLc' (Or.inr rfl) (fun _ => (hno2 hok2_f).1) hmLc
                        · c0_hfast
                          exact hJdp sLc mLc
                            ⟨hdwLc, hcvLc.trans (hcvLb.trans hcvL),
                             by rw [hflLc]; exact Nat.le_trans hflLb hflL,
                             htmkLc', htrcLc.trans (htrcLb.trans htrcL), hmLc⟩)))
          (fun _ hJpv => by
            c0_hsplit
            · c0_hfast; exact hJpv 65536#64 m2 rfl
            · c0_hfast; exact hJpv 16384#64 m2 rfl))
    (fun _ hJrt => by
      c0_hsplit
      · c0_hfast; exact hJrt 0xFFFFFFFF#64 m2 rfl
      · c0_hfast; exact hJrt tick_lim m2 rfl)

end LeanQbe.T.Examples.Kissat.FullM6Sweep
