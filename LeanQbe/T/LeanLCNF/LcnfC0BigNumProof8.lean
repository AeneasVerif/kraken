module

public import LeanQbe.T.LeanLCNF.LcnfC0BigNumProof3
import all Kraken.Mem
import all Kraken.Separation

/-!
# Signed `Int` Mul/Div/Mod Proofs (`lcnf_int_muldiv_wp`, `Milestone R1`, Part 8)
-/

set_option autoImplicit false

public section

namespace LeanQbe.T.LeanLCNF

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil

private theorem bn_int_len_call_wp {Q : Post [i64]} {X : XPost}
    {rt scr a : BitVec 64} {st : RtC0State} {scrLimbs : List (BitVec 64)}
    {val : Int} {objs : List LcnfObj} {R : Mem 64 → Prop} {m : Mem 64}
    (hrep : intRep a val objs)
    (hm : (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m)
    {k : Tup Val [i64] → Expr Val Cont [i64]}
    (hk : wp rtR1Env Q X (k (BitVec.ofNat 64 (limbLenNat val.natAbs), ())) m) :
    wp rtR1Env Q X (.call (as := [i64]) (bs := [i64]) "bn_int_len" (Arg.var a, ()) k) m := by
  refine wp_call_ret1 (as := [i64]) (Arg.var a, ()) k (fun w m' =>
    w = BitVec.ofNat 64 (limbLenNat val.natAbs) ∧ m' = m) ?_ ?_
  · refine rtR1Env_bn_int_len ?_
    dsimp only [bnIntLenSpec, vals, Arg.val]
    exact ⟨val, objs, bigNumRtInv rt st scr scrLimbs ⋆ R, hrep,
      sep_cast_ac hm (by ac_rfl), rfl, rfl⟩
  · rintro w m' ⟨rfl, hm'⟩; subst m'; exact hk

private theorem bn_require_scratch_call_wp {Q : Post [i64]} {X : XPost}
    {rt need scr : BitVec 64}
    {st : RtC0State} {scrLimbs : List (BitVec 64)} {objs : List LcnfObj}
    {R : Mem 64 → Prop} {m : Mem 64}
    (hwf : BigNumRtWf rt st scr scrLimbs) (hneed : need.toNat ≤ scrLimbs.length)
    (hm : (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m)
    {k : Tup Val [i64] → Expr Val Cont [i64]}
    (hk : wp rtR1Env Q X (k (scr, ())) m) :
    wp rtR1Env Q X
      (.call (as := [i64, i64]) (bs := [i64]) "bn_require_scratch"
        (Arg.var rt, Arg.var need, ()) k) m := by
  refine wp_call_ret1 (as := [i64, i64]) (Arg.var rt, Arg.var need, ()) k
    (fun scrP m' => scrP = scr ∧ m' = m) ?_ ?_
  · refine rtR1Env_bn_require_scratch ?_
    dsimp only [bnRequireScratchSpec, vals, Arg.val]
    refine ⟨scr, BitVec.ofNat 64 scrLimbs.length,
      rtC0Inv rt st ⋆ array64 scr scrLimbs ⋆ lcnfHeap objs ⋆ R,
      hwf.2.2.1, ?_, ?_, rfl, rfl⟩
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hwf.2.2.2.2.1]; exact hneed
    · dsimp only [bigNumRtInv] at hm; exact sep_cast_ac hm (by ac_rfl)
  · rintro scrP m' ⟨hscrP, hm'⟩; subst scrP; subst m'; exact hk

private theorem bn_load_int_call_wp {Q : Post [i64]} {X : XPost}
    {a dst : BitVec 64}
    {val : Int} {objs : List LcnfObj} {xs : List (BitVec 64)}
    (F : Mem 64 → Prop) {m : Mem 64}
    (hrep : intRep a val objs) (hlen : xs.length = limbLenNat val.natAbs)
    (hm : (lcnfHeap objs ⋆ array64 dst xs ⋆ F) m)
    {k : Tup Val [i64] → Expr Val Cont [i64]}
    (hk : ∀ xs' m', xs'.length = limbLenNat val.natAbs → limbsVal xs' = val.natAbs →
      (lcnfHeap objs ⋆ array64 dst xs' ⋆ F) m' →
      wp rtR1Env Q X
        (k (((BitVec.ofNat 64 (limbLenNat val.natAbs) <<< 1#64) |||
          (if val < 0 then 1#64 else 0#64)), ())) m') :
    wp rtR1Env Q X
      (.call (as := [i64, i64]) (bs := [i64]) "bn_load_int" (Arg.var a, Arg.var dst, ()) k) m := by
  refine wp_call_ret1 (as := [i64, i64]) (Arg.var a, Arg.var dst, ()) k (fun info m' =>
    ∃ xs',
      info = ((BitVec.ofNat 64 (limbLenNat val.natAbs) <<< 1#64) |||
        (if val < 0 then 1#64 else 0#64)) ∧
      xs'.length = limbLenNat val.natAbs ∧ limbsVal xs' = val.natAbs ∧
      (lcnfHeap objs ⋆ array64 dst xs' ⋆ F) m') ?_ ?_
  · refine rtR1Env_bn_load_int ?_
    dsimp only [bnLoadIntSpec, vals, Arg.val]
    refine ⟨val, objs, xs, F, hrep, by rw [hlen]; exact Nat.le_refl _, hm,
      fun xs' m' hlen' hval' _ hm' => ?_⟩
    have htake : List.take (limbLenNat val.natAbs) xs' = xs' :=
      List.take_of_length_le (by rw [hlen', hlen]; exact Nat.le_refl _)
    rw [htake] at hval'
    exact ⟨xs', rfl, by rw [hlen', hlen], hval', hm'⟩
  · rintro info m' ⟨xs', rfl, hlen', hval', hm'⟩
    exact hk xs' m' hlen' hval' hm'

private theorem bn_int_from_limbs_call_wp {Q : Post [i64]} {X : XPost}
    {rt negW buf : BitVec 64} {n : Nat}
    {st : RtC0State} {xs : List (BitVec 64)} {objs : List LcnfObj}
    (F : Mem 64 → Prop) {m : Mem 64} {z : Int}
    (hn_lt : n < 2 ^ 60) (hn_le : n ≤ xs.length) (hn_max : n ≤ mpzMaxLimbs)
    (hb : st.Bounded48) (htrim : trimLenLoop xs n = n)
    (hval : (if n = 0 then (0 : Int)
      else if negW = 0#64 then (limbsVal (xs.take n) : Int)
      else -(limbsVal (xs.take n) : Int)) = z)
    (halloc : (z < -(2 ^ 62 : Int) ∨ (2 ^ 62 : Int) ≤ z) → canAllocBytes st (16 + 8 * n))
    (hm : (rtC0Inv rt st ⋆ array64 buf xs ⋆ lcnfHeap objs ⋆ F) m)
    {k : Tup Val [i64] → Expr Val Cont [i64]}
    (hk : ∀ res st' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → st'.Bounded48 →
      intRep res z objs' → (∀ o ∈ objs, o ∈ objs') →
      (rtC0Inv rt st' ⋆ array64 buf xs ⋆ lcnfHeap objs' ⋆ F) m' →
      wp rtR1Env Q X (k (res, ())) m') :
    wp rtR1Env Q X (.call (as := [i64, i64, i64, i64]) (bs := [i64]) "bn_int_from_limbs"
      (Arg.var rt, Arg.var negW, Arg.var buf, Arg.var (BitVec.ofNat 64 n), ()) k) m := by
  refine wp_call_ret1 (as := [i64, i64, i64, i64])
    (Arg.var rt, Arg.var negW, Arg.var buf, Arg.var (BitVec.ofNat 64 n), ()) k (fun res m' =>
    ∃ st' objs',
      st'.PreservesMeta st ∧ st'.rem ≤ st.rem ∧ st'.Bounded48 ∧
      intRep res z objs' ∧ (∀ o ∈ objs, o ∈ objs') ∧
      (rtC0Inv rt st' ⋆ array64 buf xs ⋆ lcnfHeap objs' ⋆ F) m') ?_ ?_
  · refine rtR1Env_bn_int_from_limbs ?_
    dsimp only [bnIntFromLimbsSpec, vals, Arg.val]
    have hnbv : (BitVec.ofNat 64 n).toNat = n := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hval' : (if trimLenLoop xs (BitVec.ofNat 64 n).toNat = 0 then (0 : Int)
        else if negW = 0#64 then (limbsVal (xs.take (BitVec.ofNat 64 n).toNat) : Int)
        else -(limbsVal (xs.take (BitVec.ofNat 64 n).toNat) : Int)) = z := by
      rw [hnbv, htrim]; exact hval
    refine ⟨st, xs, objs, F, by rw [hnbv]; exact hn_le, by rw [hnbv]; exact hn_max, hb,
      fun hrz => by rw [hnbv, htrim]; exact halloc (by rwa [hval'] at hrz),
      hm, fun res st' objs' m' hpm hrem hb' hrep' hsm hbg hm' => ?_⟩
    rw [hval'] at hrep' hsm hbg
    have hpres : ∀ o ∈ objs, o ∈ objs' := by
      by_cases hsm_c : -(2 ^ 62 : Int) ≤ z ∧ z < 2 ^ 62
      · rw [hsm hsm_c]; exact fun _ h => h
      · rcases hbg (by omega) with ⟨newObj, _, _, rfl⟩
        exact fun _ h => List.mem_cons_of_mem _ h
    exact ⟨st', objs', hpm, hrem, hb', hrep', hpres, hm'⟩
  · rintro res m' ⟨st', objs', hpm, hrem, hb', hrep', hpres, hm'⟩
    exact hk res st' objs' m' hpm hrem hb' hrep' hpres hm'

private theorem bn_int_from_limbs_pos_call_wp {Q : Post [i64]} {X : XPost}
    {rt buf : BitVec 64} {n : Nat}
    {st : RtC0State} {xs : List (BitVec 64)} {objs : List LcnfObj}
    (F : Mem 64 → Prop) {m : Mem 64} {z : Int}
    (hn_lt : n < 2 ^ 60) (hn_le : n ≤ xs.length) (hn_max : n ≤ mpzMaxLimbs)
    (hb : st.Bounded48) (htrim : trimLenLoop xs n = n)
    (hval : (if n = 0 then (0 : Int)
      else if (0#64 : BitVec 64) = 0#64 then (limbsVal (xs.take n) : Int)
      else -(limbsVal (xs.take n) : Int)) = z)
    (halloc : (z < -(2 ^ 62 : Int) ∨ (2 ^ 62 : Int) ≤ z) → canAllocBytes st (16 + 8 * n))
    (hm : (rtC0Inv rt st ⋆ array64 buf xs ⋆ lcnfHeap objs ⋆ F) m)
    {k : Tup Val [i64] → Expr Val Cont [i64]}
    (hk : ∀ res st' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → st'.Bounded48 →
      intRep res z objs' → (∀ o ∈ objs, o ∈ objs') →
      (rtC0Inv rt st' ⋆ array64 buf xs ⋆ lcnfHeap objs' ⋆ F) m' →
      wp rtR1Env Q X (k (res, ())) m') :
    wp rtR1Env Q X (.call (as := [i64, i64, i64, i64]) (bs := [i64]) "bn_int_from_limbs"
      (Arg.var rt, Arg.imm 0, Arg.var buf, Arg.var (BitVec.ofNat 64 n), ()) k) m := by
  refine wp_call_ret1 (as := [i64, i64, i64, i64])
    (Arg.var rt, Arg.imm 0, Arg.var buf, Arg.var (BitVec.ofNat 64 n), ()) k (fun res m' =>
    ∃ st' objs',
      st'.PreservesMeta st ∧ st'.rem ≤ st.rem ∧ st'.Bounded48 ∧
      intRep res z objs' ∧ (∀ o ∈ objs, o ∈ objs') ∧
      (rtC0Inv rt st' ⋆ array64 buf xs ⋆ lcnfHeap objs' ⋆ F) m') ?_ ?_
  · refine rtR1Env_bn_int_from_limbs ?_
    dsimp only [bnIntFromLimbsSpec, vals, Arg.val]
    have hnbv : (BitVec.ofNat 64 n).toNat = n := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hval' : (if trimLenLoop xs (BitVec.ofNat 64 n).toNat = 0 then (0 : Int)
        else if (0 : BitVec 64) = 0#64 then (limbsVal (xs.take (BitVec.ofNat 64 n).toNat) : Int)
        else -(limbsVal (xs.take (BitVec.ofNat 64 n).toNat) : Int)) = z := by
      rw [hnbv, htrim]; exact hval
    refine ⟨st, xs, objs, F, by rw [hnbv]; exact hn_le, by rw [hnbv]; exact hn_max, hb,
      fun hrz => by rw [hnbv, htrim]; exact halloc (by rwa [hval'] at hrz),
      hm, fun res st' objs' m' hpm hrem hb' hrep' hsm hbg hm' => ?_⟩
    rw [hval'] at hrep' hsm hbg
    have hpres : ∀ o ∈ objs, o ∈ objs' := by
      by_cases hsm_c : -(2 ^ 62 : Int) ≤ z ∧ z < 2 ^ 62
      · rw [hsm hsm_c]; exact fun _ h => h
      · rcases hbg (by omega) with ⟨newObj, _, _, rfl⟩
        exact fun _ h => List.mem_cons_of_mem _ h
    exact ⟨st', objs', hpm, hrem, hb', hrep', hpres, hm'⟩
  · rintro res m' ⟨st', objs', hpm, hrem, hb', hrep', hpres, hm'⟩
    exact hk res st' objs' m' hpm hrem hb' hrep' hpres hm'

private theorem bv64_need_muldiv (na nb : Nat) (hna : na < 2 ^ 60) (hnb : nb < 2 ^ 60) :
    ((2 : BitVec 64) * (BitVec.ofNat 64 na + BitVec.ofNat 64 nb) +
      BitVec.ofNat 64 (max na nb) + (2 : BitVec 64)).toNat =
      2 * (na + nb) + max na nb + 2 := by
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat,
    show BitVec.toNat (2 : BitVec 64) = 2 by decide,
    Nat.mod_eq_of_lt (by omega : na < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : nb < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : na + nb < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : max na nb < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 2 * (na + nb) < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 2 * (na + nb) + max na nb < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : 2 * (na + nb) + max na nb + 2 < 2 ^ 64)]

private theorem muldiv_max_jnz {na nb : Nat} (hna : na < 2 ^ 60) (hnb : nb < 2 ^ 60)
    (m : Mem 64) (J : Cont [i64])
    (hJ : ∀ xs m', xs = (BitVec.ofNat 64 (max na nb), ()) ∧ m' = m → J xs m') :
    ∀ {Q : Post [i64]} {X : XPost},
      wp rtR1Env Q X
        (Expr.let_
          ({ sig := [i64, i64], code := OpCode.ugt i64,
             args := (Arg.var (BitVec.ofNat 64 na), Arg.var (BitVec.ofNat 64 nb), ()) } :
            Op Val [Ty.bool])
          fun t => Expr.jnz (Arg.var t.1)
            (Expr.jump J (Arg.var (BitVec.ofNat 64 na), ()))
            (Expr.jump J (Arg.var (BitVec.ofNat 64 nb), ()))) m := by
  intro Q X; c0_let_simp
  by_cases hgt : nb < na
  · have hugt : BitVec.ofNat 64 nb < BitVec.ofNat 64 na := by
      change (BitVec.ofNat 64 nb).toNat < (BitVec.ofNat 64 na).toNat
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; exact hgt
    refine jnz_true (by simpa [BitVec.ult] using hugt) ?_; rw [wp_jump]
    exact hJ (BitVec.ofNat 64 na, ()) m ⟨by rw [Nat.max_eq_left (by omega)], rfl⟩
  · have hnugt : ¬(BitVec.ofNat 64 nb < BitVec.ofNat 64 na) := by
      change ¬((BitVec.ofNat 64 nb).toNat < (BitVec.ofNat 64 na).toNat)
      simp only [BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; exact hgt
    refine jnz_false (by simpa [BitVec.ult] using hnugt) ?_; rw [wp_jump]
    exact hJ (BitVec.ofNat 64 nb, ()) m ⟨by rw [Nat.max_eq_right (by omega)], rfl⟩

private theorem muldiv_split_mem {rt scr : BitVec 64} {st : RtC0State}
    {scrLimbs : List (BitVec 64)} {objs : List LcnfObj} {R : Mem 64 → Prop} {m : Mem 64}
    (na nb : Nat) (hscrLen : 2 * (na + nb) + max na nb + 2 ≤ scrLimbs.length)
    (hm : (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m) :
    (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
      array64 scr (List.take na scrLimbs) ⋆
      array64 (scr + BitVec.ofNat 64 (8 * na)) (List.take nb (List.drop na scrLimbs)) ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb)))
        (List.take na (List.take (na + nb) (List.drop (na + nb) scrLimbs))) ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb)) + BitVec.ofNat 64 (8 * na))
        (List.drop na (List.take (na + nb) (List.drop (na + nb) scrLimbs))) ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb + (na + nb))))
        (List.drop (na + nb + (na + nb)) scrLimbs) ⋆ lcnfHeap objs ⋆ R) m := by
  have hs4 := array64_split4 scr scrLimbs na nb (na + nb) (by omega)
  have hqr_eq := array64_split2 (scr + BitVec.ofNat 64 (8 * (na + nb)))
    (List.take (na + nb) (List.drop (na + nb) scrLimbs)) na (by simp; omega)
  dsimp only [bigNumRtInv] at hm
  rw [hs4, hqr_eq] at hm
  exact sep_cast_ac hm (by ac_rfl)

private theorem muldiv_join_mem {rt scr : BitVec 64} {st st' : RtC0State}
    {scrLimbs xsA' xsB' xsQ' xsR' xsOut' : List (BitVec 64)}
    {objs' : List LcnfObj} {R : Mem 64 → Prop} {m' : Mem 64}
    {na nb : Nat} (hwf : BigNumRtWf rt st scr scrLimbs) (hb' : st'.Bounded48)
    (hscrLen : 2 * (na + nb) + max na nb + 2 ≤ scrLimbs.length)
    (hA : xsA'.length = na) (hB : xsB'.length = nb)
    (hQ : xsQ'.length = na) (hR : xsR'.length = nb)
    (hOut : xsOut'.length = (List.drop (na + nb + (na + nb)) scrLimbs).length)
    (hm' : (rtC0Inv rt st' ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
      array64 scr xsA' ⋆ array64 (scr + BitVec.ofNat 64 (8 * na)) xsB' ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb))) xsQ' ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb)) + BitVec.ofNat 64 (8 * na)) xsR' ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb + (na + nb)))) xsOut' ⋆
      lcnfHeap objs' ⋆ R) m') :
    let sl' := xsA' ++ xsB' ++ (xsQ' ++ xsR') ++ xsOut'
    BigNumRtWf rt st' scr sl' ∧
    (bigNumRtInv rt st' scr sl' ⋆ lcnfHeap objs' ⋆ R) m' := by
  dsimp only
  have hqr_j := array64_join2 (scr + BitVec.ofNat 64 (8 * (na + nb))) xsQ' xsR' na hQ
  have h4_j := array64_join4 scr xsA' xsB' (xsQ' ++ xsR') xsOut' na nb (na + nb)
    hA hB (by simp [hQ, hR])
  have htot : (xsA' ++ xsB' ++ (xsQ' ++ xsR') ++ xsOut').length = scrLimbs.length := by
    simp [hA, hB, hQ, hR, hOut]; omega
  refine ⟨BigNumRtWf.with_state_len hwf hb' htot, ?_⟩
  dsimp only [bigNumRtInv]; rw [htot, ← h4_j, ← hqr_j]
  exact sep_cast_ac hm' (by ac_rfl)

private theorem bv64_bne_lit {a b : BitVec 64} (h : a.toNat ≠ b.toNat) : (a == b) = false := by
  simp only [beq_eq_false_iff_ne, ne_eq]; intro heq; subst heq; exact h rfl

private theorem bv64_beq_lit {a b : BitVec 64} (h : a.toNat = b.toNat) : (a == b) = true := by
  simp only [beq_iff_eq]; exact BitVec.eq_of_toNat_eq h

private theorem muldiv_mem_q {rt scr lenW : BitVec 64} {st : RtC0State}
    {xsA xsB xsQ xsR xsOut : List (BitVec 64)} {objs : List LcnfObj}
    {R : Mem 64 → Prop} {na nb : Nat} {m : Mem 64} :
    (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) lenW ⋆ array64 scr xsA ⋆
      array64 (scr + BitVec.ofNat 64 (8 * na)) xsB ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb))) xsQ ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb)) + BitVec.ofNat 64 (8 * na)) xsR ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb + (na + nb)))) xsOut ⋆
      lcnfHeap objs ⋆ R) m ↔
    (rtC0Inv rt st ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb))) xsQ ⋆ lcnfHeap objs ⋆
      (cell64 (rt + 33672#64) scr ⋆ cell64 (rt + 33680#64) lenW ⋆ array64 scr xsA ⋆
        array64 (scr + BitVec.ofNat 64 (8 * na)) xsB ⋆
        array64 (scr + BitVec.ofNat 64 (8 * (na + nb)) + BitVec.ofNat 64 (8 * na)) xsR ⋆
        array64 (scr + BitVec.ofNat 64 (8 * (na + nb + (na + nb)))) xsOut ⋆ R)) m :=
  ⟨fun h => sep_cast_ac h (by ac_rfl), fun h => sep_cast_ac h (by ac_rfl)⟩

private theorem muldiv_mem_r {rt scr lenW : BitVec 64} {st : RtC0State}
    {xsA xsB xsQ xsR xsOut : List (BitVec 64)} {objs : List LcnfObj}
    {R : Mem 64 → Prop} {na nb : Nat} {m : Mem 64} :
    (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) lenW ⋆ array64 scr xsA ⋆
      array64 (scr + BitVec.ofNat 64 (8 * na)) xsB ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb))) xsQ ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb)) + BitVec.ofNat 64 (8 * na)) xsR ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb + (na + nb)))) xsOut ⋆
      lcnfHeap objs ⋆ R) m ↔
    (rtC0Inv rt st ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb)) + BitVec.ofNat 64 (8 * na)) xsR ⋆
      lcnfHeap objs ⋆
      (cell64 (rt + 33672#64) scr ⋆ cell64 (rt + 33680#64) lenW ⋆ array64 scr xsA ⋆
        array64 (scr + BitVec.ofNat 64 (8 * na)) xsB ⋆
        array64 (scr + BitVec.ofNat 64 (8 * (na + nb))) xsQ ⋆
        array64 (scr + BitVec.ofNat 64 (8 * (na + nb + (na + nb)))) xsOut ⋆ R)) m :=
  ⟨fun h => sep_cast_ac h (by ac_rfl), fun h => sep_cast_ac h (by ac_rfl)⟩

private theorem muldiv_mem_out {rt scr lenW : BitVec 64} {st : RtC0State}
    {xsA xsB xsQ xsR xsOut : List (BitVec 64)} {objs : List LcnfObj}
    {R : Mem 64 → Prop} {na nb : Nat} {m : Mem 64} :
    (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) lenW ⋆ array64 scr xsA ⋆
      array64 (scr + BitVec.ofNat 64 (8 * na)) xsB ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb))) xsQ ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb)) + BitVec.ofNat 64 (8 * na)) xsR ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb + (na + nb)))) xsOut ⋆
      lcnfHeap objs ⋆ R) m ↔
    (rtC0Inv rt st ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb + (na + nb)))) xsOut ⋆
      lcnfHeap objs ⋆
      (cell64 (rt + 33672#64) scr ⋆ cell64 (rt + 33680#64) lenW ⋆ array64 scr xsA ⋆
        array64 (scr + BitVec.ofNat 64 (8 * na)) xsB ⋆
        array64 (scr + BitVec.ofNat 64 (8 * (na + nb))) xsQ ⋆
        array64 (scr + BitVec.ofNat 64 (8 * (na + nb)) + BitVec.ofNat 64 (8 * na)) xsR ⋆ R)) m :=
  ⟨fun h => sep_cast_ac h (by ac_rfl), fun h => sep_cast_ac h (by ac_rfl)⟩

private theorem muldiv_mem_add1 {rt scr lenW : BitVec 64} {st : RtC0State}
    {xsA xsB xsQ xsR xsOut : List (BitVec 64)} {objs : List LcnfObj}
    {R : Mem 64 → Prop} {na nb : Nat} {m : Mem 64} :
    (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) lenW ⋆ array64 scr xsA ⋆
      array64 (scr + BitVec.ofNat 64 (8 * na)) xsB ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb))) xsQ ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb)) + BitVec.ofNat 64 (8 * na)) xsR ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb + (na + nb)))) xsOut ⋆
      lcnfHeap objs ⋆ R) m ↔
    (array64 (scr + BitVec.ofNat 64 (8 * (na + nb))) xsQ ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb + (na + nb)))) xsOut ⋆
      (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆ cell64 (rt + 33680#64) lenW ⋆
        array64 scr xsA ⋆ array64 (scr + BitVec.ofNat 64 (8 * na)) xsB ⋆
        array64 (scr + BitVec.ofNat 64 (8 * (na + nb)) + BitVec.ofNat 64 (8 * na)) xsR ⋆
        lcnfHeap objs ⋆ R)) m :=
  ⟨fun h => sep_cast_ac h (by ac_rfl), fun h => sep_cast_ac h (by ac_rfl)⟩

private theorem muldiv_mem_sub {rt scr lenW : BitVec 64} {st : RtC0State}
    {xsA xsB xsQ xsR xsOut : List (BitVec 64)} {objs : List LcnfObj}
    {R : Mem 64 → Prop} {na nb : Nat} {m : Mem 64} :
    (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) lenW ⋆ array64 scr xsA ⋆
      array64 (scr + BitVec.ofNat 64 (8 * na)) xsB ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb))) xsQ ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb)) + BitVec.ofNat 64 (8 * na)) xsR ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb + (na + nb)))) xsOut ⋆
      lcnfHeap objs ⋆ R) m ↔
    (array64 (scr + BitVec.ofNat 64 (8 * na)) xsB ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb)) + BitVec.ofNat 64 (8 * na)) xsR ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb + (na + nb)))) xsOut ⋆
      (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆ cell64 (rt + 33680#64) lenW ⋆
        array64 scr xsA ⋆ array64 (scr + BitVec.ofNat 64 (8 * (na + nb))) xsQ ⋆
        lcnfHeap objs ⋆ R)) m :=
  ⟨fun h => sep_cast_ac h (by ac_rfl), fun h => sep_cast_ac h (by ac_rfl)⟩

private theorem muldiv_ret_var_wp {Q : Post [i64]} {X : XPost}
    {rt scr negW buf : BitVec 64} {n na nb : Nat}
    {st : RtC0State} {scrLimbs xs xsA' xsB' xsQ' xsR' xsOut' : List (BitVec 64)}
    {objs : List LcnfObj} {F R : Mem 64 → Prop} {m : Mem 64} {z : Int}
    (hwf : BigNumRtWf rt st scr scrLimbs)
    (hscrLen : 2 * (na + nb) + max na nb + 2 ≤ scrLimbs.length)
    (hA : xsA'.length = na) (hB : xsB'.length = nb)
    (hQ_l : xsQ'.length = na) (hR_l : xsR'.length = nb)
    (hOut_l : xsOut'.length = (List.drop (na + nb + (na + nb)) scrLimbs).length)
    (hn_lt : n < 2 ^ 60) (hn_le : n ≤ xs.length) (hn_max : n ≤ mpzMaxLimbs)
    (htrim : trimLenLoop xs n = n)
    (hval : (if n = 0 then (0 : Int)
      else if negW = 0#64 then (limbsVal (xs.take n) : Int)
      else -(limbsVal (xs.take n) : Int)) = z)
    (halloc : (z < -(2 ^ 62 : Int) ∨ (2 ^ 62 : Int) ≤ z) → canAllocBytes st (16 + 8 * n))
    (hm : (rtC0Inv rt st ⋆ array64 buf xs ⋆ lcnfHeap objs ⋆ F) m)
    (hback : ∀ st' objs' m',
      (rtC0Inv rt st' ⋆ array64 buf xs ⋆ lcnfHeap objs' ⋆ F) m' →
      (rtC0Inv rt st' ⋆ cell64 (rt + 33672#64) scr ⋆
        cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
        array64 scr xsA' ⋆ array64 (scr + BitVec.ofNat 64 (8 * na)) xsB' ⋆
        array64 (scr + BitVec.ofNat 64 (8 * (na + nb))) xsQ' ⋆
        array64 (scr + BitVec.ofNat 64 (8 * (na + nb)) + BitVec.ofNat 64 (8 * na)) xsR' ⋆
        array64 (scr + BitVec.ofNat 64 (8 * (na + nb + (na + nb)))) xsOut' ⋆
        lcnfHeap objs' ⋆ R) m')
    (hQ : ∀ res st' scrLimbs' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
      intRep res z objs' → (∀ o ∈ objs, o ∈ objs') →
      (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m')
    {k : Tup Val [i64] → Expr Val Cont [i64]}
    (hk_ret : ∀ res m', Q (res, ()) m' → wp rtR1Env Q X (k (res, ())) m') :
    wp rtR1Env Q X (.call (as := [i64, i64, i64, i64]) (bs := [i64]) "bn_int_from_limbs"
      (Arg.var rt, Arg.var negW, Arg.var buf, Arg.var (BitVec.ofNat 64 n), ()) k) m := by
  refine bn_int_from_limbs_call_wp F hn_lt hn_le hn_max hwf.1 htrim hval halloc hm ?_
  intro res st' objs' m' hpm hrem hb' hrepZ hpres hm'
  have hjm := muldiv_join_mem (objs' := objs') (R := R) hwf hb' hscrLen hA hB hQ_l hR_l hOut_l
    (hback st' objs' m' hm')
  exact hk_ret res m' (hQ res st' _ objs' m' hpm hrem hjm.1 hrepZ hpres hjm.2)

private theorem muldiv_ret_pos_wp {Q : Post [i64]} {X : XPost}
    {rt scr buf : BitVec 64} {n na nb : Nat}
    {st : RtC0State} {scrLimbs xs xsA' xsB' xsQ' xsR' xsOut' : List (BitVec 64)}
    {objs : List LcnfObj} {F R : Mem 64 → Prop} {m : Mem 64} {z : Int}
    (hwf : BigNumRtWf rt st scr scrLimbs)
    (hscrLen : 2 * (na + nb) + max na nb + 2 ≤ scrLimbs.length)
    (hA : xsA'.length = na) (hB : xsB'.length = nb)
    (hQ_l : xsQ'.length = na) (hR_l : xsR'.length = nb)
    (hOut_l : xsOut'.length = (List.drop (na + nb + (na + nb)) scrLimbs).length)
    (hn_lt : n < 2 ^ 60) (hn_le : n ≤ xs.length) (hn_max : n ≤ mpzMaxLimbs)
    (htrim : trimLenLoop xs n = n)
    (hval : (if n = 0 then (0 : Int)
      else if (0#64 : BitVec 64) = 0#64 then (limbsVal (xs.take n) : Int)
      else -(limbsVal (xs.take n) : Int)) = z)
    (halloc : (z < -(2 ^ 62 : Int) ∨ (2 ^ 62 : Int) ≤ z) → canAllocBytes st (16 + 8 * n))
    (hm : (rtC0Inv rt st ⋆ array64 buf xs ⋆ lcnfHeap objs ⋆ F) m)
    (hback : ∀ st' objs' m',
      (rtC0Inv rt st' ⋆ array64 buf xs ⋆ lcnfHeap objs' ⋆ F) m' →
      (rtC0Inv rt st' ⋆ cell64 (rt + 33672#64) scr ⋆
        cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
        array64 scr xsA' ⋆ array64 (scr + BitVec.ofNat 64 (8 * na)) xsB' ⋆
        array64 (scr + BitVec.ofNat 64 (8 * (na + nb))) xsQ' ⋆
        array64 (scr + BitVec.ofNat 64 (8 * (na + nb)) + BitVec.ofNat 64 (8 * na)) xsR' ⋆
        array64 (scr + BitVec.ofNat 64 (8 * (na + nb + (na + nb)))) xsOut' ⋆
        lcnfHeap objs' ⋆ R) m')
    (hQ : ∀ res st' scrLimbs' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
      intRep res z objs' → (∀ o ∈ objs, o ∈ objs') →
      (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m')
    {k : Tup Val [i64] → Expr Val Cont [i64]}
    (hk_ret : ∀ res m', Q (res, ()) m' → wp rtR1Env Q X (k (res, ())) m') :
    wp rtR1Env Q X (.call (as := [i64, i64, i64, i64]) (bs := [i64]) "bn_int_from_limbs"
      (Arg.var rt, Arg.imm 0, Arg.var buf, Arg.var (BitVec.ofNat 64 n), ()) k) m := by
  refine bn_int_from_limbs_pos_call_wp F hn_lt hn_le hn_max hwf.1 htrim hval halloc hm ?_
  intro res st' objs' m' hpm hrem hb' hrepZ hpres hm'
  have hjm := muldiv_join_mem (objs' := objs') (R := R) hwf hb' hscrLen hA hB hQ_l hR_l hOut_l
    (hback st' objs' m' hm')
  exact hk_ret res m' (hQ res st' _ objs' m' hpm hrem hjm.1 hrepZ hpres hjm.2)

private theorem lcnf_int_mul_wp
    {rt op a b : BitVec 64} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hop6 : op.toNat = 6) (hspec : lcnfIntMulDivSpec (rt, op, a, b, ()) m Q X) :
    Func.wp rtR1Env lcnf_int_muldiv.body (rt, op, a, b, ()) m Q X := by
  rcases hspec with ⟨st, scr, scrLimbs, objs, aVal, bVal, R,
    hwf, hrepA, hrepB, _, hscrLen, htnMax, hallocZ, hm, hQ⟩
  change wp rtR1Env Q X (lcnf_int_muldiv_body Val Cont (rt, op, a, b, ())) m
  dsimp only [lcnf_int_muldiv_body]
  let na := limbLenNat aVal.natAbs
  let nb := limbLenNat bVal.natAbs
  let z := intMulDivRes op.toNat aVal bVal
  let tn := limbLenNat z.natAbs
  have hmpz33 : mpzMaxLimbs = 33554429 := rfl
  have hna_le : na ≤ mpzMaxLimbs := limbLenNat_le_max_of_intRep hrepA
  have hnb_le : nb ≤ mpzMaxLimbs := limbLenNat_le_max_of_intRep hrepB
  have hna_lt : na < 2 ^ 60 := by omega
  have hnb_lt : nb < 2 ^ 60 := by omega
  refine bn_int_len_call_wp hrepA hm ?_
  refine bn_int_len_call_wp hrepB hm ?_
  refine wp_join_group (fun _ _ => False) (fun _ _ _ h => h.elim) ?_
  intro _ _; c0_let_simp
  have h33 : (33554429#64 : BitVec 64).toNat = 33554429 := by decide
  have hna_ugt : ¬((33554429#64 : BitVec 64) < BitVec.ofNat 64 na) := by
    change ¬((33554429#64 : BitVec 64).toNat < (BitVec.ofNat 64 na).toNat)
    rw [h33, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact Nat.not_lt_of_le hna_le
  have hnb_ugt : ¬((33554429#64 : BitVec 64) < BitVec.ofNat 64 nb) := by
    change ¬((33554429#64 : BitVec 64).toNat < (BitVec.ofNat 64 nb).toNat)
    rw [h33, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact Nat.not_lt_of_le hnb_le
  refine jnz_false (by simpa [BitVec.ult] using hna_ugt) ?_; c0_let_simp
  refine jnz_false (by simpa [BitVec.ult] using hnb_ugt) ?_
  refine wp_join_group (fun xs m3 => xs = (BitVec.ofNat 64 (max na nb), ()) ∧ m3 = m)
    ?_ (fun J hJ => muldiv_max_jnz hna_lt hnb_lt m J hJ)
  rintro J ⟨maxnW, ⟨⟩⟩ m3 ⟨hmaxW, hm3⟩
  injection hmaxW with hmaxW'; subst maxnW; subst m3
  rw [Blocks.get.eq_1]; c0_let_simp
  refine bn_require_scratch_call_wp hwf
    (by rw [bv64_need_muldiv na nb hna_lt hnb_lt]; exact hscrLen) hm ?_
  c0_let_simp
  rw [bv64_mul8_add (by omega : na < 2 ^ 60)]
  let xsA := List.take na scrLimbs
  let xsB := List.take nb (List.drop na scrLimbs)
  let xsQR := List.take (na + nb) (List.drop (na + nb) scrLimbs)
  let xsQ := List.take na xsQR
  let xsR := List.drop na xsQR
  let xsOut := List.drop (na + nb + (na + nb)) scrLimbs
  let bufB := scr + BitVec.ofNat 64 (8 * na)
  let bufQ := scr + BitVec.ofNat 64 (8 * (na + nb))
  let bufR := bufQ + BitVec.ofNat 64 (8 * na)
  let bufOut := scr + BitVec.ofNat 64 (8 * (na + nb + (na + nb)))
  have hna_len : xsA.length = na := by simp [xsA]; omega
  have hnb_len : xsB.length = nb := by simp [xsB]; omega
  have hqr_len : xsQR.length = na + nb := by simp [xsQR]; omega
  have hq_len : xsQ.length = na := by simp [xsQ, hqr_len]
  have hr_len : xsR.length = nb := by simp [xsR, hqr_len]
  have hm_spl := muldiv_split_mem na nb hscrLen hm
  refine bn_load_int_call_wp
    (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
      array64 (scr + BitVec.ofNat 64 (8 * na)) xsB ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb))) xsQ ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb)) + BitVec.ofNat 64 (8 * na)) xsR ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb + (na + nb)))) xsOut ⋆ R)
    hrepA hna_len (sep_cast_ac hm_spl (by dsimp only [xsA, xsB, xsQR, xsQ, xsR, xsOut]; ac_rfl)) ?_
  intro xsA' m4 hlenA' hvalA' hm4
  refine bn_load_int_call_wp
    (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
      array64 scr xsA' ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb))) xsQ ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb)) + BitVec.ofNat 64 (8 * na)) xsR ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb + (na + nb)))) xsOut ⋆ R)
    hrepB hnb_len (sep_cast_ac hm4 (by (try dsimp only [bufB, bufQ, bufR, bufOut]); ac_rfl)) ?_
  intro xsB' m5 hlenB' hvalB' hm5
  c0_let_simp
  have hA_bits := info_lshr1_and1 (len := na)
    (negBit := if aVal < 0 then 1#64 else 0#64) (by omega)
    (by by_cases h : aVal < 0 <;> simp [h])
  have hB_bits := info_lshr1_and1 (len := nb)
    (negBit := if bVal < 0 then 1#64 else 0#64) (by omega)
    (by by_cases h : bVal < 0 <;> simp [h])
  rw [hA_bits.1, hA_bits.2, hB_bits.1, hB_bits.2]
  let negA : BitVec 64 := if aVal < 0 then 1#64 else 0#64
  let negB : BitVec 64 := if bVal < 0 then 1#64 else 0#64
  have heq6 : (op == 6#64) = true := by
    simp [beq_iff_eq]; exact BitVec.eq_of_toNat_eq (by simpa using hop6)
  refine jnz_true heq6 ?_; c0_let_simp
  have hz6 : z = aVal * bVal := by simp [z, intMulDivRes, hop6]
  by_cases hna0 : na = 0
  · refine jnz_true (by simp [hna0]) ?_; rw [wp_ret]; dsimp only [vals, Arg.val]
    have ha0 : aVal = 0 := by have := limbLenNat_pos_iff (n := aVal.natAbs); omega
    have hz0 : z = 0 := by simp [hz6, ha0]
    have hjm := muldiv_join_mem (objs' := objs) (R :=
      R) hwf hwf.1 hscrLen hlenA' hlenB' hq_len hr_len rfl
      (sep_cast_ac hm5 (by dsimp only [na, nb, xsOut, bufB, bufQ, bufR, bufOut]; ac_rfl))
    exact hQ 1#64 st _ objs m5 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      (Nat.le_refl _) hjm.1 (by change intRep 1#64 z objs; rw [hz0]; simp [intRep])
      (fun _ h => h) hjm.2
  · have hna_bv : (BitVec.ofNat 64 na).toNat = na := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hnb_bv : (BitVec.ofNat 64 nb).toNat = nb := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hne_na0 : (BitVec.ofNat 64 na == 0#64) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro h
      have ht := congrArg BitVec.toNat h; rw [hna_bv] at ht; exact hna0 ht
    refine jnz_false hne_na0 ?_; c0_let_simp
    by_cases hnb0 : nb = 0
    · refine jnz_true (by simp [hnb0]) ?_; rw [wp_ret]; dsimp only [vals, Arg.val]
      have hb0 : bVal = 0 := by have := limbLenNat_pos_iff (n := bVal.natAbs); omega
      have hz0 : z = 0 := by simp [hz6, hb0]
      have hjm := muldiv_join_mem (objs' := objs) (R :=
        R) hwf hwf.1 hscrLen hlenA' hlenB' hq_len hr_len rfl
        (sep_cast_ac hm5 (by dsimp only [na, nb, xsOut, bufB, bufQ, bufR, bufOut]; ac_rfl))
      exact hQ 1#64 st _ objs m5 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        (Nat.le_refl _) hjm.1 (by change intRep 1#64 z objs; rw [hz0]; simp [intRep])
        (fun _ h => h) hjm.2
    · have hne_nb0 : (BitVec.ofNat 64 nb == 0#64) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; intro h
        have ht := congrArg BitVec.toNat h; rw [hnb_bv] at ht; exact hnb0 ht
      refine jnz_false hne_nb0 ?_; c0_let_simp
      have ha_nz : aVal ≠ 0 := by intro h0; subst h0; simp [na, limbLenNat] at hna0
      have hb_nz : bVal ≠ 0 := by intro h0; subst h0; simp [nb, limbLenNat] at hnb0
      rw [← BitVec.ofNat_add na nb, bv64_mul8_add (by omega : na + nb < 2 ^ 60)]
      have htakeA : List.take na xsA' = xsA' := List.take_of_length_le
        (by rw [hlenA']; exact Nat.le_refl _)
      have htakeB : List.take nb xsB' = xsB' := List.take_of_length_le
        (by rw [hlenB']; exact Nat.le_refl _)
      refine wp_call_ret1 _ _ (fun rnW m6 =>
        ∃ xsQ' xsR' xsOut',
          rnW = BitVec.ofNat 64 tn ∧
          xsQ'.length = na ∧ xsR'.length = nb ∧ xsOut'.length = xsOut.length ∧
          limbsVal (List.take tn (xsQ' ++ xsR')) = z.natAbs ∧
          (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
            cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
            array64 scr xsA' ⋆ array64 bufB xsB' ⋆ array64 bufQ xsQ' ⋆
            array64 bufR xsR' ⋆ array64 bufOut xsOut' ⋆ lcnfHeap objs ⋆ R) m6) ?_ ?_
      · refine rtR1Env_bn_mul ?_
        dsimp only [bnMulSpec, vals, Arg.val]
        have haddr_out : bufQ + BitVec.ofNat 64 (8 * (na + nb)) = bufOut := by
          simp only [bufQ, bufOut, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
        have hqr_out : array64 bufQ (xsQ ++ xsR ++ xsOut) =
            array64 bufQ xsQ ⋆ array64 bufR xsR ⋆ array64 bufOut xsOut := by
          have hj1 := array64_join2 bufQ xsQ xsR na hq_len
          have hj2 := array64_join2 bufQ (xsQ ++ xsR) xsOut (na + nb) (by simp [hq_len, hr_len])
          rw [haddr_out] at hj2; rw [← hj2, ← hj1]
        have hm5_mul : (array64 scr xsA' ⋆ array64 bufB xsB' ⋆
            array64 bufQ (xsQ ++ xsR ++ xsOut) ⋆
            (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
              cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
              lcnfHeap objs ⋆ R)) m5 := by
          rw [hqr_out]
          exact sep_cast_ac hm5 (by (try dsimp only [bufB, bufQ, bufR, bufOut]); ac_rfl)
        refine ⟨xsA', xsB', xsQ ++ xsR ++ xsOut, _,
          by rw [hna_bv, hlenA']; exact Nat.le_refl _,
          by rw [hnb_bv, hlenB']; exact Nat.le_refl _,
          by rw [hna_bv, hnb_bv]; simp [hq_len, hr_len],
          by rw [hna_bv, hnb_bv]; omega, hm5_mul,
          fun outXs' m6 hlenO' _ hvalO hm6 => ?_⟩
        rw [hna_bv, hnb_bv, htakeA, htakeB, hvalA', hvalB'] at hvalO ⊢
        have hz_abs : aVal.natAbs * bVal.natAbs = z.natAbs := by rw [hz6, Int.natAbs_mul]
        rw [hz_abs] at hvalO ⊢
        have hsplit1 := array64_split2 bufQ outXs' (na + nb) (by rw [hlenO']; simp [hq_len, hr_len])
        have hq_take_l : (List.take (na + nb) outXs').length = na + nb := by
          simp; rw [hlenO']; simp [hq_len, hr_len]
        have hsplit2 := array64_split2 bufQ (List.take (na + nb) outXs') na
          (by rw [hq_take_l]; omega)
        let xsQ' := List.take na (List.take (na + nb) outXs')
        let xsR' := List.drop na (List.take (na + nb) outXs')
        let xsOut' := List.drop (na + nb) outXs'
        have htn_le_mul : tn ≤ na + nb := by
          change limbLenNat z.natAbs ≤ na + nb
          rw [← hz_abs]
          exact limbLenNat_mul_le aVal.natAbs bVal.natAbs
        have htake_eq : List.take tn (xsQ' ++ xsR') = List.take tn outXs' := by
          rw [show xsQ' ++ xsR' = List.take (na + nb) outXs' from List.take_append_drop na _,
            List.take_take, Nat.min_eq_left htn_le_mul]
        refine ⟨xsQ', xsR', xsOut', rfl, by simp [xsQ', hq_take_l],
          by simp [xsR', hq_take_l], by simp [xsOut', hlenO', hq_len, hr_len]; omega,
          by rw [htake_eq]; exact hvalO, ?_⟩
        rw [hsplit1, hsplit2, haddr_out] at hm6
        exact sep_cast_ac hm6 (by (try dsimp only [bufB, bufQ, bufR, bufOut]); ac_rfl)
      · rintro rnW m6 ⟨xsQ', xsR', xsOut', rfl, hq'_l, hr'_l, ho'_l, hvalO', hm6⟩
        c0_let_simp
        have htn_lt : tn < 2 ^ 60 := by
          change limbLenNat z.natAbs < 2 ^ 60; dsimp only [z]; omega
        have htn_le_qr : tn ≤ (xsQ' ++ xsR').length := by
          have hz_abs : z.natAbs = aVal.natAbs * bVal.natAbs := by rw [hz6, Int.natAbs_mul]
          have h1 : tn ≤ na + nb := by
            change limbLenNat z.natAbs ≤ _; rw [hz_abs]; exact limbLenNat_mul_le _ _
          simp [hq'_l, hr'_l]; omega
        have htrimO : trimLenLoop (xsQ' ++ xsR') tn = tn := by
          rw [← limbLenNat_trimLenLoop htn_le_qr, hvalO']
        have hval_mul : (if tn = 0 then (0 : Int)
            else if (negA ^^^ negB) = 0#64 then (limbsVal ((xsQ' ++ xsR').take tn) : Int)
            else -(limbsVal ((xsQ' ++ xsR').take tn) : Int)) = z := by
          rw [hvalO']
          have hnz : tn ≠ 0 := by
            intro h0; exact (Int.mul_ne_zero ha_nz hb_nz)
              (by rw [← hz6]; have := limbLenNat_pos_iff (n := z.natAbs); omega)
          simp only [hnz, ↓reduceIte, hz6]
          by_cases ha_n : aVal < 0 <;> by_cases hb_n : bVal < 0 <;>
            simp only [negA, negB, ha_n, hb_n, ↓reduceIte]
          · have hpos : 0 < z := by rw [hz6]; exact Int.mul_pos_of_neg_of_neg ha_n hb_n
            have hxor : (1#64 ^^^ 1#64 : BitVec 64) = 0#64 := by decide
            simp only [hxor, ↓reduceIte]; omega
          · have hneg : z < 0 := by rw [hz6]; exact Int.mul_neg_of_neg_of_pos ha_n (by omega)
            have hxor : (1#64 ^^^ 0#64 : BitVec 64) ≠ 0#64 := by decide
            simp only [hxor, ↓reduceIte]; omega
          · have hneg : z < 0 := by rw [hz6]; exact Int.mul_neg_of_pos_of_neg (by omega) hb_n
            have hxor : (0#64 ^^^ 1#64 : BitVec 64) ≠ 0#64 := by decide
            simp only [hxor, ↓reduceIte]; omega
          · have hpos : 0 < z := by rw [hz6]; exact Int.mul_pos (by omega) (by omega)
            have hxor : (0#64 ^^^ 0#64 : BitVec 64) = 0#64 := by decide
            simp only [hxor, ↓reduceIte]; omega
        have hm6_qr : (rtC0Inv rt st ⋆ array64 bufQ (xsQ' ++ xsR') ⋆ lcnfHeap objs ⋆
            (cell64 (rt + 33672#64) scr ⋆ cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
              array64 scr xsA' ⋆ array64 bufB xsB' ⋆ array64 bufOut xsOut' ⋆ R)) m6 := by
          rw [← array64_join2 bufQ xsQ' xsR' na hq'_l]
          exact sep_cast_ac hm6 (by (try dsimp only [bufB, bufQ, bufR, bufOut]); ac_rfl)
        refine bn_int_from_limbs_call_wp
          (cell64 (rt + 33672#64) scr ⋆ cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
            array64 scr xsA' ⋆ array64 bufB xsB' ⋆ array64 bufOut xsOut' ⋆ R)
          htn_lt htn_le_qr htnMax hwf.1 htrimO
          hval_mul hallocZ hm6_qr ?_
        intro res st' objs' m' hpm hrem hb' hrepZ hpres hm'
        rw [wp_ret]; dsimp only [vals, Arg.val]
        rw [← array64_join2 bufQ xsQ' xsR' na hq'_l] at hm'
        have hjm := muldiv_join_mem (objs' := objs') (R :=
          R) hwf hb' hscrLen hlenA' hlenB' hq'_l hr'_l ho'_l
          (sep_cast_ac hm' (by dsimp only [na, nb, bufB, bufQ, bufR, bufOut]; ac_rfl))
        exact hQ res st' _ objs' m' hpm hrem hjm.1 hrepZ hpres hjm.2

private theorem lcnf_int_divmod_b0_wp
    {rt op a b : BitVec 64} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hop_dm : op.toNat = 7 ∨ op.toNat = 8 ∨ op.toNat = 14 ∨ op.toNat = 15)
    {st : RtC0State} {scr : BitVec 64} {scrLimbs : List (BitVec 64)}
    {objs : List LcnfObj} {aVal : Int} {R : Mem 64 → Prop}
    (hwf : BigNumRtWf rt st scr scrLimbs) (hrepA : intRep a aVal objs) (hrepB : intRep b 0 objs)
    (hscrLen : 2 * (limbLenNat aVal.natAbs + limbLenNat (0 : Int).natAbs) +
      max (limbLenNat aVal.natAbs) (limbLenNat (0 : Int).natAbs) + 2 ≤ scrLimbs.length)
    (hallocZ :
      let z := intMulDivRes op.toNat aVal 0
      (z < -(2 ^ 62 : Int) ∨ (2 ^ 62 : Int) ≤ z) → canAllocBytes st (16 + 8 * limbLenNat z.natAbs))
    (hm : (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m)
    (hQ : ∀ res st' scrLimbs' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
      intRep res (intMulDivRes op.toNat aVal 0) objs' → (∀ o ∈ objs, o ∈ objs') →
      (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m') :
    Func.wp rtR1Env lcnf_int_muldiv.body (rt, op, a, b, ()) m Q X := by
  change wp rtR1Env Q X (lcnf_int_muldiv_body Val Cont (rt, op, a, b, ())) m
  dsimp only [lcnf_int_muldiv_body]
  let na := limbLenNat aVal.natAbs
  let nb := limbLenNat (0 : Int).natAbs
  let z := intMulDivRes op.toNat aVal 0
  have hmpz33 : mpzMaxLimbs = 33554429 := rfl
  have hna_le : na ≤ mpzMaxLimbs := limbLenNat_le_max_of_intRep hrepA
  have hnb0 : nb = 0 := by simp [nb, limbLenNat]
  have hna_lt : na < 2 ^ 60 := by omega
  have hnb_lt : nb < 2 ^ 60 := by omega
  refine bn_int_len_call_wp hrepA hm ?_
  refine bn_int_len_call_wp hrepB hm ?_
  refine wp_join_group (fun _ _ => False) (fun _ _ _ h => h.elim) ?_
  intro _ _; c0_let_simp
  have h33 : (33554429#64 : BitVec 64).toNat = 33554429 := by decide
  have hna_ugt : ¬((33554429#64 : BitVec 64) < BitVec.ofNat 64 na) := by
    change ¬((33554429#64 : BitVec 64).toNat < (BitVec.ofNat 64 na).toNat)
    rw [h33, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact Nat.not_lt_of_le hna_le
  refine jnz_false (by simpa [BitVec.ult] using hna_ugt) ?_; c0_let_simp
  refine jnz_false (by simp [BitVec.ult, limbLenNat]) ?_
  refine wp_join_group (fun xs m3 => xs = (BitVec.ofNat 64 (max na nb), ()) ∧ m3 = m)
    ?_ (fun J hJ => muldiv_max_jnz hna_lt hnb_lt m J hJ)
  rintro J ⟨maxnW, ⟨⟩⟩ m3 ⟨hmaxW, hm3⟩
  injection hmaxW with hmaxW'; subst maxnW; subst m3
  rw [Blocks.get.eq_1]; c0_let_simp
  refine bn_require_scratch_call_wp hwf
    (by rw [bv64_need_muldiv na nb hna_lt hnb_lt]; exact hscrLen) hm ?_
  c0_let_simp
  rw [bv64_mul8_add (by omega : na < 2 ^ 60)]
  let xsA := List.take na scrLimbs
  let xsB := List.take nb (List.drop na scrLimbs)
  let xsQR := List.take (na + nb) (List.drop (na + nb) scrLimbs)
  let xsQ := List.take na xsQR
  let xsR := List.drop na xsQR
  let xsOut := List.drop (na + nb + (na + nb)) scrLimbs
  have hna_len : xsA.length = na := by simp [xsA]; omega
  have hnb_len : xsB.length = nb := by simp [xsB]; omega
  have hqr_len : xsQR.length = na + nb := by simp [xsQR]; omega
  have hq_len : xsQ.length = na := by simp [xsQ, hqr_len]
  have hr_len : xsR.length = nb := by simp [xsR, hqr_len]
  have hm_spl := muldiv_split_mem na nb hscrLen hm
  refine bn_load_int_call_wp
    (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
      array64 (scr + BitVec.ofNat 64 (8 * na)) xsB ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb))) xsQ ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb)) + BitVec.ofNat 64 (8 * na)) xsR ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb + (na + nb)))) xsOut ⋆ R)
    hrepA hna_len (sep_cast_ac hm_spl (by ac_rfl)) ?_
  intro xsA' m4 hlenA' hvalA' hm4
  refine bn_load_int_call_wp
    (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
      array64 scr xsA' ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb))) xsQ ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb)) + BitVec.ofNat 64 (8 * na)) xsR ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb + (na + nb)))) xsOut ⋆ R)
    hrepB hnb_len (sep_cast_ac hm4 (by ac_rfl)) ?_
  intro xsB' m5 hlenB' _ hm5
  c0_let_simp
  have hA_bits := info_lshr1_and1 (len := na)
    (negBit := if aVal < 0 then 1#64 else 0#64) (by omega)
    (by by_cases h : aVal < 0 <;> simp [h])
  have hB_bits := info_lshr1_and1 (len := nb)
    (negBit := if (0 : Int) < 0 then 1#64 else 0#64) (by omega) (by decide)
  rw [hA_bits.1, hA_bits.2, hB_bits.1, hB_bits.2]
  have hne6 : (op == 6#64) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 6); subst h
    decide
  refine jnz_false hne6 ?_; c0_let_simp
  refine jnz_true (by simp [hnb0]) ?_; c0_let_simp
  by_cases hop714 : op.toNat = 7 ∨ op.toNat = 14
  · rcases hop714 with h7 | h14
    · have heq7 : (op == 7#64) = true := by
        simp [beq_iff_eq]; exact BitVec.eq_of_toNat_eq (by simpa using h7)
      refine jnz_true heq7 ?_; rw [wp_ret]; dsimp only [vals, Arg.val]
      have hz0 : z = 0 := by
        simp only [z, intMulDivRes, h7, show (7 : Nat) ≠ 6 by decide, ↓reduceIte]
        exact Int.ediv_zero aVal
      have hjm := muldiv_join_mem (objs' := objs) (R :=
        R) hwf hwf.1 hscrLen hlenA' hlenB' hq_len hr_len rfl
        (sep_cast_ac hm5 (by dsimp only [na, nb, xsOut]; ac_rfl))
      exact hQ 1#64 st _ objs m5 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        (Nat.le_refl _) hjm.1 (by change intRep 1#64 z objs; rw [hz0]; simp [intRep])
        (fun _ h => h) hjm.2
    · have hne7 : (op == 7#64) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 7); subst h
        decide
      have heq14 : (op == 14#64) = true := by
        simp [beq_iff_eq]; exact BitVec.eq_of_toNat_eq (by simpa using h14)
      refine jnz_false hne7 ?_; c0_let_simp; refine jnz_true heq14 ?_; rw [wp_ret]
      dsimp only [vals, Arg.val]
      have hz0 : z = 0 := by simp [z, intMulDivRes, h14, Int.tdiv_zero]
      have hjm := muldiv_join_mem (objs' := objs) (R :=
        R) hwf hwf.1 hscrLen hlenA' hlenB' hq_len hr_len rfl
        (sep_cast_ac hm5 (by dsimp only [na, nb, xsOut]; ac_rfl))
      exact hQ 1#64 st _ objs m5 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        (Nat.le_refl _) hjm.1 (by change intRep 1#64 z objs; rw [hz0]; simp [intRep])
        (fun _ h => h) hjm.2
  · have hne7 : (op == 7#64) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply hop714; left; subst h; decide
    have hne14 : (op == 14#64) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply hop714; right; subst h; decide
    refine jnz_false hne7 ?_; c0_let_simp; refine jnz_false hne14 ?_
    have hza : z = aVal := by
      rcases hop_dm with h7 | h8 | h14 | h15
      · exact False.elim (hop714 (Or.inl h7))
      · simp only [z, intMulDivRes, h8, show (8 : Nat) ≠ 6 by decide,
          show (8 : Nat) ≠ 7 by decide, ↓reduceIte]; exact Int.emod_zero aVal
      · exact False.elim (hop714 (Or.inr h14))
      · simp [z, intMulDivRes, h15, Int.tmod_zero]
    have htakeA : List.take na xsA' = xsA' := List.take_of_length_le
      (by rw [hlenA']; exact Nat.le_refl _)
    have htrimA : trimLenLoop xsA' na = na := by
      rw [← limbLenNat_trimLenLoop (by rw [hlenA']; exact Nat.le_refl _), htakeA, hvalA']
    have hval_a : (if na = 0 then (0 : Int)
        else if (if aVal < 0 then 1#64 else 0#64) = 0#64 then (limbsVal (xsA'.take na) : Int)
        else -(limbsVal (xsA'.take na) : Int)) = z := by
      rw [htakeA, hvalA', hza]
      by_cases hna0 : na = 0
      · have ha0 : aVal = 0 := by have := limbLenNat_pos_iff (n := aVal.natAbs); omega
        simp [hna0, ha0]
      · simp only [hna0, ↓reduceIte]; by_cases han : aVal < 0 <;> simp [han] <;> omega
    refine bn_int_from_limbs_call_wp
      (cell64 (rt + 33672#64) scr ⋆ cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
        array64 (scr + BitVec.ofNat 64 (8 * na)) xsB' ⋆
        array64 (scr + BitVec.ofNat 64 (8 * (na + nb))) xsQ ⋆
        array64 (scr + BitVec.ofNat 64 (8 * (na + nb)) + BitVec.ofNat 64 (8 * na)) xsR ⋆
        array64 (scr + BitVec.ofNat 64 (8 * (na + nb + (na + nb)))) xsOut ⋆ R)
      hna_lt (by rw [hlenA']; exact Nat.le_refl _)
      hna_le hwf.1 htrimA hval_a
      (fun hrz => by rw [show na = limbLenNat z.natAbs by rw [hza]]; exact hallocZ hrz)
      (sep_cast_ac hm5 (by ac_rfl)) ?_
    intro res st' objs' m' hpm hrem hb' hrepZ hpres hm'
    rw [wp_ret]; dsimp only [vals, Arg.val]
    have hjm := muldiv_join_mem (objs' := objs') (R :=
      R) hwf hb' hscrLen hlenA' hlenB' hq_len hr_len rfl
      (sep_cast_ac hm' (by dsimp only [na, nb, xsOut]; ac_rfl))
    exact hQ res st' _ objs' m' hpm hrem hjm.1 hrepZ hpres hjm.2

private theorem divmod_branch_qr_wp {Q : Post [i64]} {X : XPost}
    {rt scr : BitVec 64} {st : RtC0State} {scrLimbs : List (BitVec 64)}
    {objs : List LcnfObj} {aVal bVal : Int} {R : Mem 64 → Prop} {m5 : Mem 64}
    {xsA' xsB' xsQ xsR xsOut : List (BitVec 64)}
    (hb_nz : bVal ≠ 0)
    (hna_lt : limbLenNat aVal.natAbs < 2 ^ 60) (hnb_lt : limbLenNat bVal.natAbs < 2 ^ 60)
    (hlenA' : xsA'.length = limbLenNat aVal.natAbs) (hvalA' : limbsVal xsA' = aVal.natAbs)
    (hlenB' : xsB'.length = limbLenNat bVal.natAbs) (hvalB' : limbsVal xsB' = bVal.natAbs)
    (hq_len : xsQ.length = limbLenNat aVal.natAbs) (hr_len : xsR.length = limbLenNat bVal.natAbs)
    (hm5 :
      (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
        cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
        array64 scr xsA' ⋆
        array64 (scr + BitVec.ofNat 64 (8 * limbLenNat aVal.natAbs)) xsB' ⋆
        array64 (scr + BitVec.ofNat 64 (8 * (limbLenNat aVal.natAbs +
          limbLenNat bVal.natAbs))) xsQ ⋆
        array64 (scr + BitVec.ofNat 64 (8 * (limbLenNat aVal.natAbs + limbLenNat bVal.natAbs)) +
          BitVec.ofNat 64 (8 * limbLenNat aVal.natAbs)) xsR ⋆
        array64 (scr + BitVec.ofNat 64 (8 * (limbLenNat aVal.natAbs + limbLenNat bVal.natAbs +
          (limbLenNat aVal.natAbs + limbLenNat bVal.natAbs)))) xsOut ⋆ lcnfHeap objs ⋆ R) m5)
    (J : Cont [i64, i64])
    (hJ : ∀ xs m6,
      (∃ xsQ' xsR',
        xs = (BitVec.ofNat 64 (limbLenNat (aVal.natAbs / bVal.natAbs)),
              BitVec.ofNat 64 (limbLenNat (aVal.natAbs % bVal.natAbs)), ()) ∧
        xsQ'.length = limbLenNat aVal.natAbs ∧ xsR'.length = limbLenNat bVal.natAbs ∧
        limbsVal (List.take (limbLenNat (aVal.natAbs / bVal.natAbs)) xsQ') =
          aVal.natAbs / bVal.natAbs ∧
        limbsVal (List.take (limbLenNat (aVal.natAbs % bVal.natAbs)) xsR') =
          aVal.natAbs % bVal.natAbs ∧
        (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
          cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
          array64 scr xsA' ⋆
          array64 (scr + BitVec.ofNat 64 (8 * limbLenNat aVal.natAbs)) xsB' ⋆
          array64 (scr + BitVec.ofNat 64 (8 * (limbLenNat aVal.natAbs +
            limbLenNat bVal.natAbs))) xsQ' ⋆
          array64 (scr + BitVec.ofNat 64 (8 * (limbLenNat aVal.natAbs + limbLenNat bVal.natAbs)) +
            BitVec.ofNat 64 (8 * limbLenNat aVal.natAbs)) xsR' ⋆
          array64 (scr + BitVec.ofNat 64 (8 * (limbLenNat aVal.natAbs + limbLenNat bVal.natAbs +
            (limbLenNat aVal.natAbs + limbLenNat bVal.natAbs)))) xsOut ⋆ lcnfHeap objs ⋆ R) m6) →
      J xs m6) :
    let na := limbLenNat aVal.natAbs
    let nb := limbLenNat bVal.natAbs
    let bufB := scr + BitVec.ofNat 64 (8 * na)
    let bufQ := scr + BitVec.ofNat 64 (8 * (na + nb))
    let bufR := bufQ + BitVec.ofNat 64 (8 * na)
    wp rtR1Env Q X
      (Expr.jnz (Arg.var (BitVec.slt (cmpResult64 aVal.natAbs bVal.natAbs) 0#64))
        (Expr.call (as := [i64, i64, i64]) (bs := []) "bn_copy"
          (Arg.var bufR, Arg.var scr, Arg.var (BitVec.ofNat 64 na), ())
          fun _ => Expr.jump J (Arg.imm 0, Arg.var (BitVec.ofNat 64 na), ()))
        (Expr.call (as := [i64, i64, i64, i64, i64, i64]) (bs := []) "bn_divmod"
          (Arg.var scr, Arg.var (BitVec.ofNat 64 na), Arg.var bufB, Arg.var (BitVec.ofNat 64 nb),
            Arg.var bufQ, Arg.var bufR, ())
          fun _ => Expr.call (as := [i64, i64]) (bs := [i64]) "bn_trim"
            (Arg.var bufQ, Arg.var (BitVec.ofNat 64 na), ())
            fun r1 => Expr.call (as := [i64, i64]) (bs := [i64]) "bn_trim"
              (Arg.var bufR, Arg.var (BitVec.ofNat 64 nb), ())
              fun r2 => Expr.jump J (Arg.var r1.1, Arg.var r2.1, ()))) m5 := by
  dsimp only
  let na := limbLenNat aVal.natAbs
  let nb := limbLenNat bVal.natAbs
  let Qnat := aVal.natAbs / bVal.natAbs
  let Rnat := aVal.natAbs % bVal.natAbs
  let qn := limbLenNat Qnat
  let rn := limbLenNat Rnat
  let bufB := scr + BitVec.ofNat 64 (8 * na)
  let bufQ := scr + BitVec.ofNat 64 (8 * (na + nb))
  let bufR := bufQ + BitVec.ofNat 64 (8 * na)
  let bufOut := scr + BitVec.ofNat 64 (8 * (na + nb + (na + nb)))
  have hna_bv : (BitVec.ofNat 64 na).toNat = na := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hnb_bv : (BitVec.ofNat 64 nb).toNat = nb := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have htakeA : List.take na xsA' = xsA' := List.take_of_length_le
    (by rw [hlenA']; exact Nat.le_refl _)
  have htakeB : List.take nb xsB' = xsB' := List.take_of_length_le
    (by rw [hlenB']; exact Nat.le_refl _)
  by_cases hlt_ab : aVal.natAbs < bVal.natAbs
  · have hslt : BitVec.slt (cmpResult64 aVal.natAbs bVal.natAbs) 0#64 = true := by
      simp [cmpResult64, hlt_ab, BitVec.slt]
    refine jnz_true hslt ?_
    have hna_le_nb : na ≤ nb := limbLenNat_mono (by omega)
    refine wp_call_ret0 _ _ (fun _ m7 =>
      (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
        cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
        array64 scr xsA' ⋆ array64 bufB xsB' ⋆ array64 bufQ xsQ ⋆
        array64 bufR (List.take na xsA' ++ List.drop na xsR) ⋆
        array64 bufOut xsOut ⋆ lcnfHeap objs ⋆ R) m7) ?_ ?_
    · refine rtR1Env_bn_copy ?_
      dsimp only [bnCopySpec, vals, Arg.val]
      refine ⟨xsR, xsA',
        rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
          cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
          array64 bufB xsB' ⋆ array64 bufQ xsQ ⋆ array64 bufOut xsOut ⋆ lcnfHeap objs ⋆ R,
        by rw [hna_bv, hr_len]; exact hna_le_nb,
        by rw [hna_bv, hlenA']; exact Nat.le_refl _,
        sep_cast_ac hm5 (by (try dsimp only [bufB, bufQ, bufR, bufOut]); ac_rfl), fun m7 hm7 => ?_⟩
      rw [hna_bv] at hm7
      exact sep_cast_ac hm7 (by (try dsimp only [bufB, bufQ, bufR, bufOut]); ac_rfl)
    · rintro ⟨⟩ m7 hm7
      rw [wp_jump]; dsimp only [vals, Arg.val]
      have hq0 : qn = 0 := by simp [qn, Qnat, Nat.div_eq_of_lt hlt_ab, limbLenNat]
      have hr_na : rn = na := by simp [rn, Rnat, Nat.mod_eq_of_lt hlt_ab, na]
      have hlen_r' : (List.take na xsA' ++ List.drop na xsR).length = nb := by
        simp [hlenA', hr_len]; omega
      have htake_r' : limbsVal (List.take rn (List.take na xsA' ++ List.drop na xsR)) = Rnat := by
        rw [hr_na, htakeA, List.take_append_of_le_length (by rw [hlenA']; exact Nat.le_refl _),
          htakeA, hvalA']
        simp [Rnat, Nat.mod_eq_of_lt hlt_ab]
      exact hJ (0#64, BitVec.ofNat 64 na, ()) m7
        ⟨xsQ, List.take na xsA' ++ List.drop na xsR,
          by change (0#64, BitVec.ofNat 64 na, ()) = (BitVec.ofNat 64 qn, BitVec.ofNat 64 rn, ())
             rw [hq0, hr_na], hq_len, hlen_r',
          by change limbsVal (List.take qn xsQ) = Qnat
             rw [hq0]; simp [Qnat, Nat.div_eq_of_lt hlt_ab],
          htake_r', hm7⟩
  · have hle_ba : bVal.natAbs ≤ aVal.natAbs := by omega
    have hnslt : BitVec.slt (cmpResult64 aVal.natAbs bVal.natAbs) 0#64 = false := by
      by_cases hgt : bVal.natAbs < aVal.natAbs
      · simp only [cmpResult64, hlt_ab, hgt, ↓reduceIte, BitVec.slt]; decide
      · simp only [cmpResult64, hlt_ab, hgt, ↓reduceIte, BitVec.slt]; decide
    refine jnz_false hnslt ?_
    have hna_pos : 0 < na := limbLenNat_pos_iff.mpr (by omega)
    have hnb_pos : 0 < nb := limbLenNat_pos_iff.mpr (by omega)
    have htrimB : trimLenLoop xsB' nb = nb := by
      rw [← limbLenNat_trimLenLoop (by rw [hlenB']; exact Nat.le_refl _), htakeB, hvalB']
    have hlastB : xsB'[nb - 1]! ≠ 0#64 := by
      have hne_b : xsB' ≠ [] := by intro h; rw [h] at hlenB'; simp at hlenB'; omega
      have hg := getLast_take_ne_zero xsB' nb (by rw [htrimB]; exact hnb_pos)
        (by rw [hlenB']; exact Nat.le_refl _)
      rw [htrimB, htakeB, list_getLast!_eq_getLast xsB' hne_b, List.getLast_eq_getElem hne_b] at hg
      have hidx : xsB'[nb - 1]! = xsB'[xsB'.length - 1]'(by omega) := by
        rw [getElem!_pos xsB' (nb - 1) (by omega)]; congr 1; omega
      rw [hidx]; exact hg
    refine wp_call_ret0 _ _ (fun _ m7 =>
      ∃ xsQ' xsR',
        xsQ'.length = na ∧ xsR'.length = nb ∧
        limbsVal (List.take na xsQ') = Qnat ∧ limbsVal (List.take nb xsR') = Rnat ∧
        (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
          cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
          array64 scr xsA' ⋆ array64 bufB xsB' ⋆ array64 bufQ xsQ' ⋆
          array64 bufR xsR' ⋆ array64 bufOut xsOut ⋆ lcnfHeap objs ⋆ R) m7) ?_ ?_
    · refine rtR1Env_bn_divmod ?_
      dsimp only [bnDivModSpec, vals, Arg.val]
      refine ⟨xsA', xsB', xsQ, xsR,
        rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
          cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
          array64 bufOut xsOut ⋆ lcnfHeap objs ⋆ R,
        by rw [hna_bv]; exact hna_pos, by rw [hnb_bv]; exact hnb_pos,
        by rw [hna_bv, hlenA']; exact Nat.le_refl _,
        by rw [hnb_bv, hlenB']; exact Nat.le_refl _,
        by rw [hna_bv, hq_len]; exact Nat.le_refl _,
        by rw [hnb_bv, hr_len]; exact Nat.le_refl _,
        by rw [hnb_bv]; exact hlastB,
        sep_cast_ac hm5 (by dsimp only [na, nb, bufB, bufQ, bufR, bufOut]; ac_rfl),
        fun xsQ' xsR' m7 hq'_l hr'_l hvalQ' hvalR' hm7 => ?_⟩
      rw [hna_bv, hnb_bv, htakeA, htakeB, hvalA', hvalB'] at hvalQ' hvalR'
      exact ⟨xsQ', xsR', by rw [hq'_l, hq_len], by rw [hr'_l, hr_len],
        hvalQ', hvalR', sep_cast_ac hm7 (by dsimp only [na, nb, bufB, bufQ, bufR, bufOut]; ac_rfl)⟩
    · rintro ⟨⟩ m7 ⟨xsQ', xsR', hq'_l, hr'_l, hvalQ', hvalR', hm7⟩
      refine wp_call_ret1 _ _ (fun qW m8 => qW = BitVec.ofNat 64 qn ∧ m8 = m7) ?_ ?_
      · refine rtR1Env_bn_trim ?_
        dsimp only [bnTrimSpec, vals, Arg.val]
        refine ⟨xsQ',
          rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
            cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
            array64 scr xsA' ⋆ array64 bufB xsB' ⋆ array64 bufR xsR' ⋆
            array64 bufOut xsOut ⋆ lcnfHeap objs ⋆ R,
          by rw [hna_bv, hq'_l]; exact Nat.le_refl _,
          sep_cast_ac hm7 (by dsimp only [na, nb, bufB, bufQ, bufR, bufOut]; ac_rfl), ?_⟩
        rw [hna_bv, ← limbLenNat_trimLenLoop (by rw [hq'_l]; exact Nat.le_refl _), hvalQ']
        exact ⟨rfl, rfl⟩
      · rintro qW m8 ⟨rfl, hm8⟩; subst m8
        refine wp_call_ret1 _ _ (fun rW m9 => rW = BitVec.ofNat 64 rn ∧ m9 = m7) ?_ ?_
        · refine rtR1Env_bn_trim ?_
          dsimp only [bnTrimSpec, vals, Arg.val]
          refine ⟨xsR',
            rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
              cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
              array64 scr xsA' ⋆ array64 bufB xsB' ⋆ array64 bufQ xsQ' ⋆
              array64 bufOut xsOut ⋆ lcnfHeap objs ⋆ R,
            by rw [hnb_bv, hr'_l]; exact Nat.le_refl _,
            sep_cast_ac hm7 (by (try dsimp only [bufB, bufQ, bufR, bufOut]); ac_rfl), ?_⟩
          rw [hnb_bv, ← limbLenNat_trimLenLoop (by rw [hr'_l]; exact Nat.le_refl _), hvalR']
          exact ⟨rfl, rfl⟩
        · rintro rW m9 ⟨rfl, hm9⟩; subst m9
          rw [wp_jump]; dsimp only [vals, Arg.val]
          have htrimQ : trimLenLoop xsQ' na = qn := by
            rw [← limbLenNat_trimLenLoop (by rw [hq'_l]; exact Nat.le_refl _), hvalQ']
          have htrimR : trimLenLoop xsR' nb = rn := by
            rw [← limbLenNat_trimLenLoop (by rw [hr'_l]; exact Nat.le_refl _), hvalR']
          have hvalQ_t : limbsVal (List.take qn xsQ') = Qnat := by
            rw [← htrimQ, limbsVal_trimLenLoop xsQ' na (by rw [hq'_l]; exact Nat.le_refl _), hvalQ']
          have hvalR_t : limbsVal (List.take rn xsR') = Rnat := by
            rw [← htrimR, limbsVal_trimLenLoop xsR' nb (by rw [hr'_l]; exact Nat.le_refl _), hvalR']
          exact hJ (BitVec.ofNat 64 qn, BitVec.ofNat 64 rn, ()) m7
            ⟨xsQ', xsR', rfl, hq'_l, hr'_l, hvalQ_t, hvalR_t, hm7⟩

private theorem muldiv_bn_cmp_call_wp {Q : Post [i64]} {X : XPost}
    {a b : BitVec 64} {na nb : Nat} {aVal bVal : Nat}
    {xsA xsB : List (BitVec 64)} (F : Mem 64 → Prop) {m : Mem 64}
    (hna_lt : na < 2 ^ 60) (hnb_lt : nb < 2 ^ 60)
    (hA : xsA.length = na) (hvA : limbsVal xsA = aVal)
    (hB : xsB.length = nb) (hvB : limbsVal xsB = bVal)
    (hm : (array64 a xsA ⋆ array64 b xsB ⋆ F) m)
    {k : Tup Val [i64] → Expr Val Cont [i64]}
    (hk : wp rtR1Env Q X (k (cmpResult64 aVal bVal, ())) m) :
    wp rtR1Env Q X
      (.call (as := [i64, i64, i64, i64]) (bs := [i64]) "bn_cmp"
        (Arg.var a, Arg.var (BitVec.ofNat 64 na),
         Arg.var b, Arg.var (BitVec.ofNat 64 nb), ()) k) m := by
  refine wp_call_ret1 (as := [i64, i64, i64, i64]) _ k
    (fun cW m' => cW = cmpResult64 aVal bVal ∧ m' = m) ?_ ?_
  · refine rtR1Env_bn_cmp ?_
    dsimp only [bnCmpSpec, vals, Arg.val]
    have hna_bv : (BitVec.ofNat 64 na).toNat = na := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hnb_bv : (BitVec.ofNat 64 nb).toNat = nb := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine ⟨xsA, xsB, F, by rw [hna_bv, hA]; exact Nat.le_refl _,
      by rw [hnb_bv, hB]; exact Nat.le_refl _, hm, ?_⟩
    rw [hna_bv, hnb_bv, List.take_of_length_le (by rw [hA]; exact Nat.le_refl _),
      List.take_of_length_le (by rw [hB]; exact Nat.le_refl _), hvA, hvB]
    exact ⟨rfl, rfl⟩
  · rintro cW m' ⟨rfl, hm'⟩; subst m'; exact hk

private theorem lcnf_int_divmod_nz_wp
    {rt op a b : BitVec 64} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    (hop_dm : op.toNat = 7 ∨ op.toNat = 8 ∨ op.toNat = 14 ∨ op.toNat = 15)
    {st : RtC0State} {scr : BitVec 64} {scrLimbs : List (BitVec 64)}
    {objs : List LcnfObj} {aVal bVal : Int} {R : Mem 64 → Prop}
    (hb_nz : bVal ≠ 0)
    (hwf : BigNumRtWf rt st scr scrLimbs) (hrepA : intRep a aVal objs) (hrepB : intRep b bVal objs)
    (hscrLen : 2 * (limbLenNat aVal.natAbs + limbLenNat bVal.natAbs) +
      max (limbLenNat aVal.natAbs) (limbLenNat bVal.natAbs) + 2 ≤ scrLimbs.length)
    (htnMax : limbLenNat (intMulDivRes op.toNat aVal bVal).natAbs ≤ mpzMaxLimbs)
    (hallocZ :
      let z := intMulDivRes op.toNat aVal bVal
      (z < -(2 ^ 62 : Int) ∨ (2 ^ 62 : Int) ≤ z) → canAllocBytes st (16 + 8 * limbLenNat z.natAbs))
    (hm : (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m)
    (hQ : ∀ res st' scrLimbs' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
      intRep res (intMulDivRes op.toNat aVal bVal) objs' → (∀ o ∈ objs, o ∈ objs') →
      (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m') :
    Func.wp rtR1Env lcnf_int_muldiv.body (rt, op, a, b, ()) m Q X := by
  change wp rtR1Env Q X (lcnf_int_muldiv_body Val Cont (rt, op, a, b, ())) m
  dsimp only [lcnf_int_muldiv_body]
  let na := limbLenNat aVal.natAbs
  let nb := limbLenNat bVal.natAbs
  let z := intMulDivRes op.toNat aVal bVal
  let tn := limbLenNat z.natAbs
  have hmpz33 : mpzMaxLimbs = 33554429 := rfl
  have hna_le : na ≤ mpzMaxLimbs := limbLenNat_le_max_of_intRep hrepA
  have hnb_le : nb ≤ mpzMaxLimbs := limbLenNat_le_max_of_intRep hrepB
  have hna_lt : na < 2 ^ 60 := by omega
  have hnb_lt : nb < 2 ^ 60 := by omega
  have hnb0 : nb ≠ 0 := Nat.ne_of_gt (limbLenNat_pos_iff.mpr (by omega))
  refine bn_int_len_call_wp hrepA hm ?_
  refine bn_int_len_call_wp hrepB hm ?_
  refine wp_join_group (fun _ _ => False) (fun _ _ _ h => h.elim) ?_
  intro _ _; c0_let_simp
  have h33 : (33554429#64 : BitVec 64).toNat = 33554429 := by decide
  have hna_ugt : ¬((33554429#64 : BitVec 64) < BitVec.ofNat 64 na) := by
    change ¬((33554429#64 : BitVec 64).toNat < (BitVec.ofNat 64 na).toNat)
    rw [h33, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact Nat.not_lt_of_le hna_le
  have hnb_ugt : ¬((33554429#64 : BitVec 64) < BitVec.ofNat 64 nb) := by
    change ¬((33554429#64 : BitVec 64).toNat < (BitVec.ofNat 64 nb).toNat)
    rw [h33, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact Nat.not_lt_of_le hnb_le
  refine jnz_false (by simpa [BitVec.ult] using hna_ugt) ?_; c0_let_simp
  refine jnz_false (by simpa [BitVec.ult] using hnb_ugt) ?_
  refine wp_join_group (fun xs m3 => xs = (BitVec.ofNat 64 (max na nb), ()) ∧ m3 = m)
    ?_ (fun J hJ => muldiv_max_jnz hna_lt hnb_lt m J hJ)
  rintro J ⟨maxnW, ⟨⟩⟩ m3 ⟨hmaxW, hm3⟩
  injection hmaxW with hmaxW'; subst maxnW; subst m3
  rw [Blocks.get.eq_1]; c0_let_simp
  refine bn_require_scratch_call_wp hwf
    (by rw [bv64_need_muldiv na nb hna_lt hnb_lt]; exact hscrLen) hm ?_
  c0_let_simp
  rw [bv64_mul8_add (by omega : na < 2 ^ 60)]
  let xsA := List.take na scrLimbs
  let xsB := List.take nb (List.drop na scrLimbs)
  let xsQR := List.take (na + nb) (List.drop (na + nb) scrLimbs)
  let xsQ := List.take na xsQR
  let xsR := List.drop na xsQR
  let xsOut := List.drop (na + nb + (na + nb)) scrLimbs
  let bufB := scr + BitVec.ofNat 64 (8 * na)
  let bufQ := scr + BitVec.ofNat 64 (8 * (na + nb))
  let bufR := bufQ + BitVec.ofNat 64 (8 * na)
  let bufOut := scr + BitVec.ofNat 64 (8 * (na + nb + (na + nb)))
  have hna_len : xsA.length = na := by simp [xsA]; omega
  have hnb_len : xsB.length = nb := by simp [xsB]; omega
  have hqr_len : xsQR.length = na + nb := by simp [xsQR]; omega
  have hq_len : xsQ.length = na := by simp [xsQ, hqr_len]
  have hr_len : xsR.length = nb := by simp [xsR, hqr_len]
  have hout_len : max na nb + 2 ≤ xsOut.length := by simp [xsOut]; omega
  have hm_spl := muldiv_split_mem na nb hscrLen hm
  refine bn_load_int_call_wp
    (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
      array64 (scr + BitVec.ofNat 64 (8 * na)) xsB ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb))) xsQ ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb)) + BitVec.ofNat 64 (8 * na)) xsR ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb + (na + nb)))) xsOut ⋆ R)
    hrepA hna_len (sep_cast_ac hm_spl (by dsimp only [xsA, xsB, xsQR, xsQ, xsR, xsOut]; ac_rfl)) ?_
  intro xsA' m4 hlenA' hvalA' hm4
  refine bn_load_int_call_wp
    (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
      array64 scr xsA' ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb))) xsQ ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb)) + BitVec.ofNat 64 (8 * na)) xsR ⋆
      array64 (scr + BitVec.ofNat 64 (8 * (na + nb + (na + nb)))) xsOut ⋆ R)
    hrepB hnb_len (sep_cast_ac hm4 (by (try dsimp only [bufB, bufQ, bufR, bufOut]); ac_rfl)) ?_
  intro xsB' m5 hlenB' hvalB' hm5
  c0_let_simp
  have hA_bits := info_lshr1_and1 (len := na)
    (negBit := if aVal < 0 then 1#64 else 0#64) (by omega)
    (by by_cases h : aVal < 0 <;> simp [h])
  have hB_bits := info_lshr1_and1 (len := nb)
    (negBit := if bVal < 0 then 1#64 else 0#64) (by omega)
    (by by_cases h : bVal < 0 <;> simp [h])
  rw [hA_bits.1, hA_bits.2, hB_bits.1, hB_bits.2]
  let negA : BitVec 64 := if aVal < 0 then 1#64 else 0#64
  let negB : BitVec 64 := if bVal < 0 then 1#64 else 0#64
  have hne6 : (op == 6#64) = false := bv64_bne_lit (by
    simp only [BitVec.toNat_ofNat]
    rcases hop_dm with h7 | h8 | h14 | h15 <;> omega)
  have hnb_bv : (BitVec.ofNat 64 nb).toNat = nb := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hne_nb0 : (BitVec.ofNat 64 nb == 0#64) = false := bv64_bne_lit (by
    rw [hnb_bv]; simpa using hnb0)
  refine jnz_false hne6 ?_; c0_let_simp
  refine jnz_false hne_nb0 ?_; c0_let_simp
  rw [← BitVec.ofNat_add na nb, bv64_mul8_add (by omega : na + nb < 2 ^ 60),
    bv64_mul8_add (by omega : na < 2 ^ 60), bv64_mul8_add (by omega : nb < 2 ^ 60)]
  have hbufOut_eq : bufQ + BitVec.ofNat 64 (8 * na) + BitVec.ofNat 64 (8 * nb) = bufOut := by
    simp only [bufQ, bufOut, BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  rw [hbufOut_eq]
  let Qnat := aVal.natAbs / bVal.natAbs
  let Rnat := aVal.natAbs % bVal.natAbs
  let qn := limbLenNat Qnat
  let rn := limbLenNat Rnat
  have hqn_le : qn ≤ na := limbLenNat_mono (Nat.div_le_self _ _)
  have hrn_le : rn ≤ nb := limbLenNat_mono (Nat.le_of_lt (Nat.mod_lt _ (by omega)))
  have hqn_lt : qn < 2 ^ 60 := by omega
  have hrn_lt : rn < 2 ^ 60 := by omega
  refine wp_join_group (fun xs m6 =>
    ∃ xsQ' xsR',
      xs = (BitVec.ofNat 64 qn, BitVec.ofNat 64 rn, ()) ∧
      xsQ'.length = na ∧ xsR'.length = nb ∧
      limbsVal (List.take qn xsQ') = Qnat ∧ limbsVal (List.take rn xsR') = Rnat ∧
      (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
        cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
        array64 scr xsA' ⋆ array64 bufB xsB' ⋆ array64 bufQ xsQ' ⋆
        array64 bufR xsR' ⋆ array64 bufOut xsOut ⋆ lcnfHeap objs ⋆ R) m6)
    ?_ (fun J hJ => by
      refine muldiv_bn_cmp_call_wp
        (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
          cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
          array64 bufQ xsQ ⋆ array64 bufR xsR ⋆ array64 bufOut xsOut ⋆ lcnfHeap objs ⋆ R)
        hna_lt hnb_lt hlenA' hvalA' hlenB' hvalB'
        (sep_cast_ac hm5 (by (try dsimp only [bufB, bufQ, bufR, bufOut]); ac_rfl)) ?_
      c0_let_simp
      exact divmod_branch_qr_wp hb_nz hna_lt hnb_lt hlenA' hvalA' hlenB' hvalB'
        hq_len hr_len (sep_cast_ac hm5
          (by (try dsimp only [bufB, bufQ, bufR, bufOut]); ac_rfl)) J hJ)
  rintro J ⟨qnW, rnW, ⟨⟩⟩ m6 ⟨xsQ', xsR', hqrEq, hq'_l, hr'_l, hvalQ', hvalR', hm6⟩
  injection hqrEq with hqW hrEq; injection hrEq with hrW
  subst hqW; subst hrW; rw [Blocks.get.eq_1]; c0_let_simp
  have hqn_bv : (BitVec.ofNat 64 qn).toNat = qn := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hrn_bv : (BitVec.ofNat 64 rn).toNat = rn := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rcases hop_dm with h7 | h8 | h14 | h15
  · have htrimQ' : trimLenLoop xsQ' qn = qn := by
      rw [← limbLenNat_trimLenLoop (by rw [hq'_l]; omega), hvalQ']
    have hed_em := int_ediv_emod_of_natAbs (a := aVal) (b := bVal) hb_nz
    refine jnz_false (bv64_bne_lit (by simp; omega)) ?_; c0_let_simp
    refine jnz_false (bv64_bne_lit (by simp; omega)) ?_; c0_let_simp
    refine jnz_true (bv64_beq_lit (by simpa using h7)) ?_
    have hz7 : z = aVal / bVal := by
      simp only [z, intMulDivRes, h7, show (7 : Nat) ≠ 6 by decide, ↓reduceIte]; rfl
    refine wp_join_group (fun _ m' => (0 ≤ aVal ∨ Rnat = 0) ∧ m' = m6) ?_ ?_
    · rintro _ ⟨⟩ m6' ⟨hcase, hm6'⟩; subst m6'; rw [Blocks.get.eq_1]
      refine wp_join_group (fun xs m' =>
        xs = ((if qn = 0 then 0#64 else negA ^^^ negB), ()) ∧ m' = m6) ?_ ?_
      · rintro _ ⟨negW, ⟨⟩⟩ m6'' ⟨hnegEq, hm6''⟩; subst m6''
        injection hnegEq with hnegW; subst hnegW; rw [Blocks.get.eq_1]
        have hed : aVal / bVal =
            if (decide (aVal < 0) == decide (bVal < 0)) = true then ↑Qnat else -↑Qnat := by
          rcases hcase with hge | hr0
          · exact hed_em.2.2.1 hge
          · rcases Int.lt_or_le aVal 0 with han | hge
            · exact hed_em.1 han hr0
            · exact hed_em.2.2.1 hge
        have hz_abs_q : z.natAbs = Qnat := by
          rw [hz7, hed]; by_cases ha_n : aVal < 0 <;> by_cases hb_n : bVal < 0 <;> simp [ha_n, hb_n]
        have hval7a : (if qn = 0 then (0 : Int)
            else if (if qn = 0 then 0#64 else negA ^^^ negB) = 0#64 then
              (limbsVal (xsQ'.take qn) : Int)
            else -(limbsVal (xsQ'.take qn) : Int)) = z := by
          rw [hvalQ', hz7, hed]
          by_cases hq0 : Qnat = 0
          · have hqn0 : qn = 0 := by simp [qn, Qnat, hq0, limbLenNat]
            simp [hqn0, Qnat, hq0]
          · have hqn_nz : qn ≠ 0 := by
              have := (limbLenNat_pos_iff (n := Qnat)).mpr (by omega); omega
            simp only [hqn_nz, ↓reduceIte, Qnat]
            by_cases ha_n : aVal < 0 <;> by_cases hb_n : bVal < 0 <;>
              simp [negA, negB, ha_n, hb_n]
        exact muldiv_ret_var_wp hwf hscrLen hlenA' hlenB' hq'_l hr'_l rfl
          hqn_lt (by rw [hq'_l]; exact hqn_le) (Nat.le_trans hqn_le hna_le) htrimQ' hval7a
          (fun hrz => by rw [show qn = limbLenNat z.natAbs by rw [hz_abs_q]]; exact hallocZ hrz)
          (muldiv_mem_q.mp hm6) (fun _ _ _ h => muldiv_mem_q.mpr h) hQ
          (fun _ _ h => by rw [wp_ret]; dsimp only [vals, Arg.val]; exact h)
      · intro J2 hJ2; c0_let_simp
        by_cases hqn0 : qn = 0
        · refine jnz_true (by simp [hqn0]) ?_; rw [wp_jump]
          exact hJ2 (0#64, ()) m6 ⟨by simp [hqn0], rfl⟩
        · refine jnz_false (bv64_bne_lit (by rw [hqn_bv]; simpa using hqn0)) ?_; c0_let_simp
          exact hJ2 (negA ^^^ negB, ()) m6 ⟨by simp [hqn0], rfl⟩
    · intro J1 hJ1; c0_let_simp
      by_cases ha_n : aVal < 0
      · have hne : negA ≠ 0#64 := by simp [negA, ha_n]
        refine jnz_true (by simp only [bne_iff_ne, ne_eq]; exact hne) ?_; c0_let_simp
        by_cases hr0 : Rnat = 0
        · have hrn0 : rn = 0 := by simp [rn, Rnat, hr0, limbLenNat]
          refine jnz_false (by simp [hrn0]) ?_; rw [wp_jump]
          exact hJ1 () m6 ⟨Or.inr hr0, rfl⟩
        · have hrn_nz : rn ≠ 0 := by
            have := (limbLenNat_pos_iff (n := Rnat)).mpr (by omega); omega
          have hne_r : BitVec.ofNat 64 rn ≠ 0#64 := by
            intro h; have ht := congrArg BitVec.toNat h
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht; exact hrn_nz ht
          refine jnz_true (by simp only [bne_iff_ne, ne_eq]; exact hne_r) ?_
          have hadd_len : qn + 1 ≤ xsOut.length := by omega
          refine wp_call_ret1 _ _ (fun qn1W m7 =>
            ∃ xsOut',
              qn1W = BitVec.ofNat 64 (limbLenNat (Qnat + 1)) ∧
              xsOut'.length = xsOut.length ∧
              limbsVal (List.take (limbLenNat (Qnat + 1)) xsOut') = Qnat + 1 ∧
              (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
                cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
                array64 scr xsA' ⋆ array64 bufB xsB' ⋆ array64 bufQ xsQ' ⋆
                array64 bufR xsR' ⋆ array64 bufOut xsOut' ⋆ lcnfHeap objs ⋆ R) m7) ?_ ?_
          · refine rtR1Env_bn_add_one ?_
            dsimp only [bnAddOneSpec, vals, Arg.val]
            refine ⟨xsQ', xsOut, _,
              by rw [hqn_bv, hq'_l]; exact hqn_le,
              by rw [hqn_bv]; exact hadd_len, by rw [hqn_bv]; omega,
              muldiv_mem_add1.mp hm6, fun xsOut' m7 hlenO' _ hvalO' hm7 => ?_⟩
            rw [hqn_bv, hvalQ'] at hvalO' ⊢
            exact ⟨xsOut', rfl, hlenO', hvalO', muldiv_mem_add1.mpr hm7⟩
          · rintro qn1W m7 ⟨xsOut', rfl, ho'_l, hvalO', hm7⟩
            c0_let_simp
            have hed_nz := hed_em.2.1 ha_n hr0
            have hq_c : (aVal.natAbs : Int) / (bVal.natAbs : Int) = (Qnat : Int) := rfl
            have hz_abs : Qnat + 1 = z.natAbs := by
              rw [hz7, hed_nz]
              by_cases hb_n : bVal < 0 <;> simp [ha_n, hb_n, hq_c] <;> omega
            have htn_eq : limbLenNat (Qnat + 1) = tn := by simp [tn, hz_abs]
            have htn_lt : tn < 2 ^ 60 := by
              change limbLenNat z.natAbs < 2 ^ 60; dsimp only [z]; omega
            have htn_le_out : tn ≤ xsOut'.length := by
              have hm1 : limbLenNat (Qnat + 1) ≤ qn + 1 := limbLenNat_add_one_le Qnat; omega
            rw [htn_eq] at hvalO' ⊢
            have htrimO : trimLenLoop xsOut' tn = tn := by
              rw [← limbLenNat_trimLenLoop htn_le_out, hvalO', htn_eq]
            have hval7b : (if tn = 0 then (0 : Int)
                else if (negA ^^^ negB) = 0#64 then (limbsVal (xsOut'.take tn) : Int)
                else -(limbsVal (xsOut'.take tn) : Int)) = z := by
              rw [hvalO', hz7, hed_nz]
              have htn_nz : tn ≠ 0 := by
                have := (limbLenNat_pos_iff (n := Qnat + 1)).mpr (by omega); omega
              simp only [htn_nz, ↓reduceIte]
              by_cases hb_n : bVal < 0 <;> simp [negA, negB, ha_n, hb_n, hq_c]
            exact muldiv_ret_var_wp hwf hscrLen hlenA' hlenB' hq'_l hr'_l ho'_l
              htn_lt htn_le_out htnMax htrimO hval7b hallocZ
              (muldiv_mem_out.mp hm7) (fun _ _ _ h => muldiv_mem_out.mpr h) hQ
              (fun _ _ h => by rw [wp_ret]; dsimp only [vals, Arg.val]; exact h)
      · have heq : negA = 0#64 := by simp [negA, ha_n]
        refine jnz_false (by simp only [bne_eq_false_iff_eq]; exact heq) ?_; rw [wp_jump]
        exact hJ1 () m6 ⟨Or.inl (by omega), rfl⟩
  · have htrimR' : trimLenLoop xsR' rn = rn := by
      rw [← limbLenNat_trimLenLoop (by rw [hr'_l]; omega), hvalR']
    have hed_em := int_ediv_emod_of_natAbs (a := aVal) (b := bVal) hb_nz
    refine jnz_false (bv64_bne_lit (by simp; omega)) ?_; c0_let_simp
    refine jnz_false (bv64_bne_lit (by simp; omega)) ?_; c0_let_simp
    refine jnz_false (bv64_bne_lit (by simp; omega)) ?_
    have hz8 : z = aVal % bVal := by
      simp only [z, intMulDivRes, h8, show (8 : Nat) ≠ 6 by decide,
        show (8 : Nat) ≠ 7 by decide, ↓reduceIte]; rfl
    refine wp_join_group (fun _ m' => (0 ≤ aVal ∨ Rnat = 0) ∧ m' = m6) ?_ ?_
    · rintro _ ⟨⟩ m6' ⟨hcase, hm6'⟩; subst m6'; rw [Blocks.get.eq_1]
      have hz_eq_r : z = (Rnat : Int) := by
        rw [hz8]
        rcases hcase with hge | hr0
        · exact hed_em.2.2.2.1 hge
        · rcases Int.lt_or_le aVal 0 with han | hge
          · rw [hed_em.2.2.2.2.1 han hr0, hr0]; rfl
          · exact hed_em.2.2.2.1 hge
      have hval8a : (if rn = 0 then (0 : Int)
          else if (0#64 : BitVec 64) = 0#64 then (limbsVal (xsR'.take rn) : Int)
          else -(limbsVal (xsR'.take rn) : Int)) = z := by
        rw [hvalR', hz_eq_r]
        by_cases hrn0 : rn = 0
        · have hr0 : Rnat = 0 := by have := limbLenNat_pos_iff (n := Rnat); omega
          simp [hrn0, hr0]
        · simp [hrn0]
      exact muldiv_ret_pos_wp hwf hscrLen hlenA' hlenB' hq'_l hr'_l rfl
        hrn_lt (by rw [hr'_l]; exact hrn_le) (Nat.le_trans hrn_le hnb_le) htrimR' hval8a
        (fun hrz => by rw [show rn = limbLenNat z.natAbs by rw [hz_eq_r]; rfl]; exact hallocZ hrz)
        (muldiv_mem_r.mp hm6) (fun _ _ _ h => muldiv_mem_r.mpr h) hQ
        (fun _ _ h => by rw [wp_ret]; dsimp only [vals, Arg.val]; exact h)
    · intro J1 hJ1; c0_let_simp
      by_cases ha_n : aVal < 0
      · have hne : negA ≠ 0#64 := by simp [negA, ha_n]
        refine jnz_false (by simp only [beq_eq_false_iff_ne, ne_eq]; exact hne) ?_; c0_let_simp
        by_cases hr0 : Rnat = 0
        · have hrn0 : rn = 0 := by simp [rn, Rnat, hr0, limbLenNat]
          refine jnz_true (by simp [hrn0]) ?_; rw [wp_jump]
          exact hJ1 () m6 ⟨Or.inr hr0, rfl⟩
        · have hrn_nz : rn ≠ 0 := by
            have := (limbLenNat_pos_iff (n := Rnat)).mpr (by omega); omega
          refine jnz_false (bv64_bne_lit (by rw [hrn_bv]; simpa using hrn_nz)) ?_
          have hR_lt_B : Rnat < bVal.natAbs := Nat.mod_lt _ (by omega)
          have htakeB : List.take nb xsB' = xsB' := List.take_of_length_le
            (by rw [hlenB']; exact Nat.le_refl _)
          refine wp_call_ret1 _ _ (fun rn1W m7 =>
            ∃ xsOut',
              rn1W = BitVec.ofNat 64 (limbLenNat (bVal.natAbs - Rnat)) ∧
              xsOut'.length = xsOut.length ∧
              limbsVal (List.take (limbLenNat (bVal.natAbs - Rnat)) xsOut') = bVal.natAbs - Rnat ∧
              (rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
                cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
                array64 scr xsA' ⋆ array64 bufB xsB' ⋆ array64 bufQ xsQ' ⋆
                array64 bufR xsR' ⋆ array64 bufOut xsOut' ⋆ lcnfHeap objs ⋆ R) m7) ?_ ?_
          · refine rtR1Env_bn_sub ?_
            dsimp only [bnSubSpec, vals, Arg.val]
            refine ⟨xsB', xsR', xsOut, _,
              by rw [hnb_bv, hlenB']; exact Nat.le_refl _,
              by rw [hrn_bv, hr'_l]; exact hrn_le,
              by rw [hnb_bv]; omega,
              by rw [hnb_bv, hrn_bv, htakeB, hvalB', hvalR']; omega,
              muldiv_mem_sub.mp hm6, fun xsOut' m7 hlenO' _ hvalO' hm7 => ?_⟩
            rw [hnb_bv, hrn_bv, htakeB, hvalB', hvalR'] at hvalO' ⊢
            exact ⟨xsOut', rfl, hlenO', hvalO', muldiv_mem_sub.mpr hm7⟩
          · rintro rn1W m7 ⟨xsOut', rfl, ho'_l, hvalO', hm7⟩
            have hed_nz := hed_em.2.2.2.2.2 ha_n hr0
            have hz_abs : bVal.natAbs - Rnat = z.natAbs := by rw [hz8, hed_nz]; omega
            have htn_eq : limbLenNat (bVal.natAbs - Rnat) = tn := by simp [tn, hz_abs]
            have htn_lt : tn < 2 ^ 60 := by
              change limbLenNat z.natAbs < 2 ^ 60; dsimp only [z]; omega
            have htn_le_out : tn ≤ xsOut'.length := by
              have hm1 : tn ≤ nb := by rw [← htn_eq]; exact limbLenNat_mono (Nat.sub_le _ _)
              omega
            rw [htn_eq] at hvalO' ⊢
            have htrimO : trimLenLoop xsOut' tn = tn := by
              rw [← limbLenNat_trimLenLoop htn_le_out, hvalO', htn_eq]
            have hval8b : (if tn = 0 then (0 : Int)
                else if (0#64 : BitVec 64) = 0#64 then (limbsVal (xsOut'.take tn) : Int)
                else -(limbsVal (xsOut'.take tn) : Int)) = z := by
              rw [hvalO', hz8, hed_nz]
              have htn_nz : tn ≠ 0 := by
                have := (limbLenNat_pos_iff (n := bVal.natAbs - Rnat)).mpr (by omega); omega
              simp [htn_nz, Rnat]
            exact muldiv_ret_pos_wp hwf hscrLen hlenA' hlenB' hq'_l hr'_l ho'_l
              htn_lt htn_le_out htnMax htrimO hval8b hallocZ
              (muldiv_mem_out.mp hm7) (fun _ _ _ h => muldiv_mem_out.mpr h) hQ
              (fun _ _ h => by rw [wp_ret]; dsimp only [vals, Arg.val]; exact h)
      · have heq : negA = 0#64 := by simp [negA, ha_n]
        refine jnz_true (by simp only [beq_iff_eq]; exact heq) ?_; rw [wp_jump]
        exact hJ1 () m6 ⟨Or.inl (by omega), rfl⟩
  · have htd_tm := int_tdiv_tmod_of_natAbs aVal bVal
    refine jnz_true (bv64_beq_lit (by simpa using h14)) ?_
    have hz14 : z = aVal.tdiv bVal := by simp [z, intMulDivRes, h14]
    have htrimQ' : trimLenLoop xsQ' qn = qn := by
      rw [← limbLenNat_trimLenLoop (by rw [hq'_l]; omega), hvalQ']
    refine wp_join_group (fun xs m' =>
      xs = ((if qn = 0 then 0#64 else negA ^^^ negB), ()) ∧ m' = m6) ?_ ?_
    · rintro _ ⟨negW, ⟨⟩⟩ m6' ⟨hnegEq, hm6'⟩; subst m6'
      injection hnegEq with hnegW; subst hnegW; rw [Blocks.get.eq_1]
      have hz_abs_q : z.natAbs = Qnat := by
        rw [hz14, htd_tm.1]
        have hq_c : (aVal.natAbs : Int) / (bVal.natAbs : Int) = (Qnat : Int) := rfl
        by_cases hq0 : Qnat = 0
        · simp [Qnat, hq0]
        · have hq0' : aVal.natAbs / bVal.natAbs ≠ 0 := hq0
          simp only [hq0', ↓reduceIte]
          by_cases ha_n : aVal < 0 <;> by_cases hb_n : bVal < 0 <;>
            simp [ha_n, hb_n, hq_c]
      have hval14 : (if qn = 0 then (0 : Int)
          else if (if qn = 0 then 0#64 else negA ^^^ negB) = 0#64 then
            (limbsVal (xsQ'.take qn) : Int)
          else -(limbsVal (xsQ'.take qn) : Int)) = z := by
        rw [hvalQ', hz14, htd_tm.1]
        by_cases hq0 : Qnat = 0
        · have hqn0 : qn = 0 := by simp [qn, Qnat, hq0, limbLenNat]
          simp [hqn0, Qnat, hq0]
        · have hqn_nz : qn ≠ 0 := by
            have := (limbLenNat_pos_iff (n := Qnat)).mpr (by omega); omega
          simp only [hqn_nz, ↓reduceIte, Qnat, hq0]
          by_cases ha_n : aVal < 0 <;> by_cases hb_n : bVal < 0 <;>
            simp [negA, negB, ha_n, hb_n]
      exact muldiv_ret_var_wp hwf hscrLen hlenA' hlenB' hq'_l hr'_l rfl
        hqn_lt (by rw [hq'_l]; exact hqn_le) (Nat.le_trans hqn_le hna_le) htrimQ' hval14
        (fun hrz => by rw [show qn = limbLenNat z.natAbs by rw [hz_abs_q]]; exact hallocZ hrz)
        (muldiv_mem_q.mp hm6) (fun _ _ _ h => muldiv_mem_q.mpr h) hQ
        (fun _ _ h => by rw [wp_ret]; dsimp only [vals, Arg.val]; exact h)
    · intro J1 hJ1; c0_let_simp
      by_cases hqn0 : qn = 0
      · refine jnz_true (by simp [hqn0]) ?_; rw [wp_jump]
        exact hJ1 (0#64, ()) m6 ⟨by simp [hqn0], rfl⟩
      · refine jnz_false (bv64_bne_lit (by rw [hqn_bv]; simpa using hqn0)) ?_; c0_let_simp
        exact hJ1 (negA ^^^ negB, ()) m6 ⟨by simp [hqn0], rfl⟩
  · have htd_tm := int_tdiv_tmod_of_natAbs aVal bVal
    refine jnz_false (bv64_bne_lit (by simp; omega)) ?_; c0_let_simp
    refine jnz_true (bv64_beq_lit (by simpa using h15)) ?_
    have hz15 : z = aVal.tmod bVal := by simp [z, intMulDivRes, h15]
    have htrimR' : trimLenLoop xsR' rn = rn := by
      rw [← limbLenNat_trimLenLoop (by rw [hr'_l]; omega), hvalR']
    refine wp_join_group (fun xs m' =>
      xs = ((if rn = 0 then 0#64 else negA), ()) ∧ m' = m6) ?_ ?_
    · rintro _ ⟨negW, ⟨⟩⟩ m6' ⟨hnegEq, hm6'⟩; subst m6'
      injection hnegEq with hnegW; subst hnegW; rw [Blocks.get.eq_1]
      have hz_abs_r : z.natAbs = Rnat := by
        rw [hz15, htd_tm.2]
        have hr_c : (aVal.natAbs : Int) % (bVal.natAbs : Int) = (Rnat : Int) := rfl
        by_cases hr0 : Rnat = 0
        · simp [Rnat, hr0]
        · have hr0' : aVal.natAbs % bVal.natAbs ≠ 0 := hr0
          simp only [hr0', ↓reduceIte]
          by_cases ha_n : aVal < 0 <;> simp [ha_n, hr_c]
      have hval15 : (if rn = 0 then (0 : Int)
          else if (if rn = 0 then 0#64 else negA) = 0#64 then
            (limbsVal (xsR'.take rn) : Int)
          else -(limbsVal (xsR'.take rn) : Int)) = z := by
        rw [hvalR', hz15, htd_tm.2]
        by_cases hr0 : Rnat = 0
        · have hrn0 : rn = 0 := by simp [rn, Rnat, hr0, limbLenNat]
          simp [hrn0, Rnat, hr0]
        · have hrn_nz : rn ≠ 0 := by
            have := (limbLenNat_pos_iff (n := Rnat)).mpr (by omega); omega
          simp only [hrn_nz, ↓reduceIte, Rnat, hr0, negA]
          by_cases ha_n : aVal < 0 <;> simp [ha_n]
      exact muldiv_ret_var_wp hwf hscrLen hlenA' hlenB' hq'_l hr'_l rfl
        hrn_lt (by rw [hr'_l]; exact hrn_le) (Nat.le_trans hrn_le hnb_le) htrimR' hval15
        (fun hrz => by rw [show rn = limbLenNat z.natAbs by rw [hz_abs_r]]; exact hallocZ hrz)
        (muldiv_mem_r.mp hm6) (fun _ _ _ h => muldiv_mem_r.mpr h) hQ
        (fun _ _ h => by rw [wp_ret]; dsimp only [vals, Arg.val]; exact h)
    · intro J1 hJ1; c0_let_simp
      by_cases hrn0 : rn = 0
      · refine jnz_true (by simp [hrn0]) ?_; rw [wp_jump]
        exact hJ1 (0#64, ()) m6 ⟨by simp [hrn0], rfl⟩
      · refine jnz_false (bv64_bne_lit (by rw [hrn_bv]; simpa using hrn0)) ?_; rw [wp_jump]
        exact hJ1 (negA, ()) m6 ⟨by simp [hrn0], rfl⟩

theorem lcnf_int_muldiv_wp :
    ∀ xs m Q X, lcnfIntMulDivSpec xs m Q X → Func.wp rtR1Env lcnf_int_muldiv.body xs m Q X := by
  rintro ⟨rt, op, a, b, ⟨⟩⟩ m Q X hspec
  by_cases hop6 : op.toNat = 6
  · exact lcnf_int_mul_wp hop6 hspec
  · rcases hspec with ⟨st, scr, scrLimbs, objs, aVal, bVal, R,
      hwf, hrepA, hrepB, hopMem, hscrLen, htnMax, hallocZ, hm, hQ⟩
    have hop_dm : op.toNat = 7 ∨ op.toNat = 8 ∨ op.toNat = 14 ∨ op.toNat = 15 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hopMem
      rcases hopMem with h | h | h | h | h <;> first | exact False.elim (hop6 h) | omega
    by_cases hb0 : bVal = 0
    · subst hb0
      exact lcnf_int_divmod_b0_wp hop_dm hwf hrepA hrepB hscrLen hallocZ hm hQ
    · exact lcnf_int_divmod_nz_wp hop_dm hb0 hwf hrepA hrepB hscrLen htnMax hallocZ hm hQ

end LeanQbe.T.LeanLCNF
