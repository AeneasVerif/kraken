module

public import LeanQbe.T.LeanLCNF.LcnfC0BigNumProof3
import all Kraken.Mem
import all Kraken.Separation

/-!
# Signed `Int` Add/Sub/Cmp Proofs (`lcnf_int_addsub_cmp_wp`, `Milestone R1`, Part 7)
-/

set_option autoImplicit false

@[expose] public section

namespace LeanQbe.T.LeanLCNF

open Std Std.ExtHashMap
open LeanQbe.T
open LeanQbe.T.C0Step
open LeanQbe.T.ProofUtil
open BigNumRt

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
      BigNumRt.rtC0Inv rt st ⋆ array64 scr scrLimbs ⋆ lcnfHeap objs ⋆ R,
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
    (hm : (BigNumRt.rtC0Inv rt st ⋆ array64 buf xs ⋆ lcnfHeap objs ⋆ F) m)
    {k : Tup Val [i64] → Expr Val Cont [i64]}
    (hk : ∀ res st' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → st'.Bounded48 →
      intRep res z objs' → (∀ o ∈ objs, o ∈ objs') →
      (BigNumRt.rtC0Inv rt st' ⋆ array64 buf xs ⋆ lcnfHeap objs' ⋆ F) m' →
      wp rtR1Env Q X (k (res, ())) m') :
    wp rtR1Env Q X (.call (as := [i64, i64, i64, i64]) (bs := [i64]) "bn_int_from_limbs"
      (Arg.var rt, Arg.var negW, Arg.var buf, Arg.var (BitVec.ofNat 64 n), ()) k) m := by
  refine wp_call_ret1 (as := [i64, i64, i64, i64])
    (Arg.var rt, Arg.var negW, Arg.var buf, Arg.var (BitVec.ofNat 64 n), ()) k (fun res m' =>
    ∃ st' objs',
      st'.PreservesMeta st ∧ st'.rem ≤ st.rem ∧ st'.Bounded48 ∧
      intRep res z objs' ∧ (∀ o ∈ objs, o ∈ objs') ∧
      (BigNumRt.rtC0Inv rt st' ⋆ array64 buf xs ⋆ lcnfHeap objs' ⋆ F) m') ?_ ?_
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

private theorem bv64_need_addsub (na nb : Nat) (hna : na < 2 ^ 60) (hnb : nb < 2 ^ 60) :
    (BitVec.ofNat 64 na + BitVec.ofNat 64 nb +
      BitVec.ofNat 64 (max na nb) + (1 : BitVec 64)).toNat =
      na + nb + max na nb + 1 := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
    show BitVec.toNat (1 : BitVec 64) = 1 by decide,
    Nat.mod_eq_of_lt (by omega : na < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : nb < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : max na nb < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : na + nb < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : na + nb + max na nb < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : na + nb + max na nb + 1 < 2 ^ 64)]

private theorem addsub_max_jnz {na nb : Nat} (hna : na < 2 ^ 60) (hnb : nb < 2 ^ 60)
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

private theorem lcnf_int_addsub_same_wp
    {rt op a b : BitVec 64} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    {st : RtC0State} {scr : BitVec 64} {scrLimbs : List (BitVec 64)}
    {objs : List LcnfObj} {aVal bVal : Int} {R : Mem 64 → Prop}
    (hwf : BigNumRtWf rt st scr scrLimbs) (hrepA : intRep a aVal objs) (hrepB : intRep b bVal objs)
    (hscrLen : limbLenNat aVal.natAbs + limbLenNat bVal.natAbs +
      max (limbLenNat aVal.natAbs) (limbLenNat bVal.natAbs) + 1 ≤ scrLimbs.length)
    (hop45 : op.toNat ∈ [4, 5])
    (hArithPre :
      let z := if op.toNat = 4 then aVal + bVal else aVal - bVal
      let tn := limbLenNat z.natAbs
      tn ≤ mpzMaxLimbs ∧
      ((z < -(2 ^ 62 : Int) ∨ (2 ^ 62 : Int) ≤ z) → canAllocBytes st (16 + 8 * tn)))
    (hcase : aVal = 0 ∨ bVal = 0 ∨
      ((aVal < 0) ↔ ((if op.toNat = 4 then bVal else -bVal) < 0)))
    (hm : (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m)
    (hQ : ∀ res st' scrLimbs' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
      (if op.toNat = 4 then intRep res (aVal + bVal) objs' ∧ (∀ o ∈ objs, o ∈ objs')
       else intRep res (aVal - bVal) objs' ∧ (∀ o ∈ objs, o ∈ objs')) →
      (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m') :
    Func.wp rtR1Env lcnf_int_addsub_cmp.body (rt, op, a, b, ()) m Q X := by
  change wp rtR1Env Q X (lcnf_int_addsub_cmp_body Val Cont (rt, op, a, b, ())) m
  dsimp only [lcnf_int_addsub_cmp_body]
  let na := limbLenNat aVal.natAbs
  let nb := limbLenNat bVal.natAbs
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
    ?_ (fun J hJ => addsub_max_jnz hna_lt hnb_lt m J hJ)
  rintro J ⟨maxnW, ⟨⟩⟩ m3 ⟨hmaxW, hm3⟩
  injection hmaxW with hmaxW'; subst maxnW; subst m3
  rw [Blocks.get.eq_1]; c0_let_simp
  refine bn_require_scratch_call_wp hwf
    (by rw [bv64_need_addsub na nb hna_lt hnb_lt]; exact hscrLen) hm ?_
  c0_let_simp
  let xsA := List.take na scrLimbs
  let xsB := List.take nb (List.drop na scrLimbs)
  let xsOut := List.drop (na + nb) scrLimbs
  have hna_len : xsA.length = na := by simp [xsA]; omega
  have hnb_len : xsB.length = nb := by simp [xsB]; omega
  have hxsOut_len : max na nb + 1 ≤ xsOut.length := by simp [xsOut]; omega
  have hadd_nab : BitVec.ofNat 64 na + BitVec.ofNat 64 nb = BitVec.ofNat 64 (na + nb) :=
    (BitVec.ofNat_add na nb).symm
  rw [bv64_mul8_add (by omega : na < 2 ^ 60), hadd_nab,
    bv64_mul8_add (by omega : na + nb < 2 ^ 60)]
  let bufB := scr + BitVec.ofNat 64 (8 * na)
  let bufOut := scr + BitVec.ofNat 64 (8 * (na + nb))
  have hm_spl : (BigNumRt.rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
      array64 scr xsA ⋆ array64 bufB xsB ⋆ array64 bufOut xsOut ⋆ lcnfHeap objs ⋆ R) m := by
    have hs3 := array64_split3 scr scrLimbs na nb (by omega)
    dsimp only [bigNumRtInv] at hm; rw [hs3] at hm
    exact sep_cast_ac hm (by dsimp only [bufB, bufOut]; ac_rfl)
  refine bn_load_int_call_wp
    (BigNumRt.rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
      array64 bufB xsB ⋆ array64 bufOut xsOut ⋆ R)
    hrepA hna_len (sep_cast_ac hm_spl (by (try dsimp only [bufB, bufOut]); ac_rfl)) ?_
  intro xsA' m4 hlenA' hvalA' hm4
  refine bn_load_int_call_wp
    (BigNumRt.rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
      array64 scr xsA' ⋆ array64 bufOut xsOut ⋆ R)
    hrepB hnb_len (sep_cast_ac hm4 (by (try dsimp only [bufB, bufOut]); ac_rfl)) ?_
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
  refine wp_join_group (fun _ m6 => m6 = m5) ?_ ?_
  · rintro J_as ⟨⟩ m6 hm6; subst m6; rw [Blocks.get.eq_1]
    refine wp_join_group (fun xs m7 =>
      m7 = m5 ∧ xs = ((if op.toNat = 5 ∧ 0 < nb then 1#64 - negB else negB), ())) ?_ ?_
    · rintro J_nb ⟨negBeffW, ⟨⟩⟩ m7 ⟨hm7, hnegBeffEq⟩
      subst m7; injection hnegBeffEq with hnegBeffW; subst hnegBeffW
      rw [Blocks.get.eq_1]
      let bEff : Int := if op.toNat = 4 then bVal else -bVal
      let z : Int := aVal + bEff
      have hz_eq : z = (if op.toNat = 4 then aVal + bVal else aVal - bVal) := by
        by_cases h4 : op.toNat = 4 <;> simp [z, bEff, h4]; omega
      rcases hArithPre with ⟨htnMax, hallocZ⟩
      rw [← hz_eq] at htnMax hallocZ
      have hnb_eff : limbLenNat bEff.natAbs = nb := by
        by_cases h4 : op.toNat = 4 <;> simp [bEff, h4, nb]
      have hnegBeff_sign : (if op.toNat = 5 ∧ 0 < nb then 1#64 - negB else negB) =
          if bEff < 0 then 1#64 else 0#64 := by
        by_cases h4 : op.toNat = 4
        · simp [bEff, h4, negB]
        · have h5 : op.toNat = 5 := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hop45; omega
          simp only [bEff, h5, show (5 : Nat) ≠ 4 by decide, ↓reduceIte, true_and, negB]
          by_cases hnb0 : 0 < nb
          · have hb_nz : bVal ≠ 0 := by intro h0; subst h0; simp [nb, limbLenNat] at hnb0
            simp only [hnb0, ↓reduceIte]
            by_cases hbneg : bVal < 0
            · simp only [hbneg, show ¬(-bVal < 0) by omega, ↓reduceIte]; decide
            · simp only [hbneg, show -bVal < 0 by omega, ↓reduceIte]; decide
          · have hb0 : bVal = 0 := by have := limbLenNat_pos_iff (n := bVal.natAbs); omega
            subst hb0; simp [hnb0]
      have hPost_z : ∀ res st' xsOut' objs' m',
          st'.PreservesMeta st → st'.rem ≤ st.rem → st'.Bounded48 →
          xsOut'.length = xsOut.length → intRep res z objs' → (∀ o ∈ objs, o ∈ objs') →
          (BigNumRt.rtC0Inv rt st' ⋆ cell64 (rt + 33672#64) scr ⋆
            cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
            array64 scr xsA' ⋆ array64 bufB xsB' ⋆ array64 bufOut xsOut' ⋆
            lcnfHeap objs' ⋆ R) m' → Q (res, ()) m' := by
        intro res st' xsOut' objs' m' hpm hrem hb' hlenOut' hrepZ hpres hm'
        have hjoin_eq := array64_join3 scr xsA' xsB' xsOut' na nb hlenA' hlenB'
        have htot_len : (xsA' ++ xsB' ++ xsOut').length = scrLimbs.length := by
          simp [hlenA', hlenB', hlenOut', xsOut]; omega
        have hwf' := BigNumRtWf.with_state_len hwf hb' htot_len
        have hm_out : (bigNumRtInv rt st' scr (xsA' ++ xsB' ++ xsOut') ⋆ lcnfHeap objs' ⋆
          R) m' := by
          dsimp only [bigNumRtInv]; rw [htot_len, ← hjoin_eq]
          exact sep_cast_ac hm' (by dsimp only [bufB, bufOut]; ac_rfl)
        by_cases h4 : op.toNat = 4
        · have hz4 : z = aVal + bVal := by rw [hz_eq]; simp [h4]
          exact hQ res st' (xsA' ++ xsB' ++ xsOut') objs' m' hpm hrem hwf'
            (by simp only [h4, ↓reduceIte]; exact ⟨by rw [← hz4]; exact hrepZ, hpres⟩) hm_out
        · have hz5 : z = aVal - bVal := by rw [hz_eq]; simp [h4]
          exact hQ res st' (xsA' ++ xsB' ++ xsOut') objs' m' hpm hrem hwf'
            (by simp only [h4, ↓reduceIte]; exact ⟨by rw [← hz5]; exact hrepZ, hpres⟩) hm_out
      have htakeA : List.take na xsA' = xsA' := List.take_of_length_le
        (by rw [hlenA']; exact Nat.le_refl _)
      have htakeB : List.take nb xsB' = xsB' := List.take_of_length_le
        (by rw [hlenB']; exact Nat.le_refl _)
      c0_let_simp
      by_cases hna0 : na = 0
      · refine jnz_true (by simp [hna0]) ?_
        have ha0 : aVal = 0 := by have := limbLenNat_pos_iff (n := aVal.natAbs); omega
        have hz_b : z = bEff := by simp [z, ha0]
        have htrimB : trimLenLoop xsB' nb = nb := by
          rw [← limbLenNat_trimLenLoop (by rw [hlenB']; exact Nat.le_refl _), htakeB, hvalB']
        have hval_b : (if nb = 0 then (0 : Int)
            else if (if op.toNat = 5 ∧ 0 < nb then 1#64 - negB else negB) = 0#64 then
              (limbsVal (xsB'.take nb) : Int)
            else -(limbsVal (xsB'.take nb) : Int)) = z := by
          rw [htakeB, hvalB', hnegBeff_sign, hz_b]
          by_cases hnb0 : nb = 0
          · have hb0 : bEff = 0 := by have := limbLenNat_pos_iff (n := bEff.natAbs); omega
            simp [hnb0, hb0]
          · simp only [hnb0, ↓reduceIte]; by_cases hbn : bEff < 0 <;> simp [hbn] <;> omega
        refine bn_int_from_limbs_call_wp
          (cell64 (rt + 33672#64) scr ⋆ cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
            array64 scr xsA' ⋆ array64 bufOut xsOut ⋆ R)
          hnb_lt (by rw [hlenB']; exact Nat.le_refl _)
          hnb_le hwf.1 htrimB hval_b
          (fun hrz =>
            by rw [show nb = limbLenNat z.natAbs by rw [hz_b, hnb_eff]]; exact hallocZ hrz)
          (sep_cast_ac hm5 (by (try dsimp only [bufB, bufOut]); ac_rfl)) ?_
        intro res st' objs' m' hpm hrem hb' hrepZ hpres hm'
        rw [wp_ret]; dsimp only [vals, Arg.val]
        exact hPost_z res st' xsOut objs' m' hpm hrem hb' rfl hrepZ hpres
          (sep_cast_ac hm' (by (try dsimp only [bufB, bufOut]); ac_rfl))
      · have hne_na0 : (BitVec.ofNat 64 na == 0#64) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; intro h
          have ht := congrArg BitVec.toNat h
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht; exact hna0 ht
        refine jnz_false hne_na0 ?_; c0_let_simp
        have ha_nz : aVal ≠ 0 := by intro h0; subst h0; simp [na, limbLenNat] at hna0
        by_cases hnb0 : nb = 0
        · refine jnz_true (by simp [hnb0]) ?_
          have hb0 : bEff = 0 := by have := limbLenNat_pos_iff (n := bEff.natAbs); omega
          have hz_a : z = aVal := by simp [z, hb0]
          have htrimA : trimLenLoop xsA' na = na := by
            rw [← limbLenNat_trimLenLoop (by rw [hlenA']; exact Nat.le_refl _), htakeA, hvalA']
          have hval_a : (if na = 0 then (0 : Int)
              else if negA = 0#64 then (limbsVal (xsA'.take na) : Int)
              else -(limbsVal (xsA'.take na) : Int)) = z := by
            rw [htakeA, hvalA', hz_a]; simp only [hna0, ↓reduceIte, negA]
            by_cases han : aVal < 0 <;> simp [han] <;> omega
          refine bn_int_from_limbs_call_wp
            (cell64 (rt + 33672#64) scr ⋆ cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
              array64 bufB xsB' ⋆ array64 bufOut xsOut ⋆ R)
            hna_lt (by rw [hlenA']; exact Nat.le_refl _)
            hna_le hwf.1 htrimA hval_a
            (fun hrz => by rw [show na = limbLenNat z.natAbs by rw [hz_a]]; exact hallocZ hrz)
            (sep_cast_ac hm5 (by (try dsimp only [bufB, bufOut]); ac_rfl)) ?_
          intro res st' objs' m' hpm hrem hb' hrepZ hpres hm'
          rw [wp_ret]; dsimp only [vals, Arg.val]
          exact hPost_z res st' xsOut objs' m' hpm hrem hb' rfl hrepZ hpres
            (sep_cast_ac hm' (by (try dsimp only [bufB, bufOut]); ac_rfl))
        · have hne_nb0 : (BitVec.ofNat 64 nb == 0#64) = false := by
            simp only [beq_eq_false_iff_ne, ne_eq]; intro h
            have ht := congrArg BitVec.toNat h
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht; exact hnb0 ht
          refine jnz_false hne_nb0 ?_; c0_let_simp
          have hb_nz : bEff ≠ 0 := by
            intro h0; have := limbLenNat_pos_iff (n := bEff.natAbs); omega
          have hsame_iff : (aVal < 0) ↔ (bEff < 0) := by
            rcases hcase with h0 | h0 | hs
            · exact False.elim (ha_nz h0)
            · exfalso; subst h0; simp [nb, limbLenNat] at hnb0
            · exact hs
          have hsame : negA = if op.toNat = 5 ∧ 0 < nb then 1#64 - negB else negB := by
            rw [hnegBeff_sign]; dsimp only [negA]
            by_cases han : aVal < 0
            · simp [han, hsame_iff.mp han]
            · have hbn : ¬(bEff < 0) := fun h => han (hsame_iff.mpr h)
              simp [han, hbn]
          refine jnz_true (by simp only [beq_iff_eq]; exact hsame) ?_
          have heff_same := int_add_same_sign ha_nz hb_nz rfl hnegBeff_sign hsame
          have hna_bv : (BitVec.ofNat 64 na).toNat = na := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          have hnb_bv : (BitVec.ofNat 64 nb).toNat = nb := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
          refine wp_call_ret1 _ _ (fun rnW m6 =>
            ∃ xsOut',
              rnW = BitVec.ofNat 64 (limbLenNat z.natAbs) ∧
              xsOut'.length = xsOut.length ∧
              limbsVal (List.take (limbLenNat z.natAbs) xsOut') = z.natAbs ∧
              (BigNumRt.rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
                cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
                array64 scr xsA' ⋆ array64 bufB xsB' ⋆ array64 bufOut xsOut' ⋆
                lcnfHeap objs ⋆ R) m6) ?_ ?_
          · refine rtR1Env_bn_add ?_
            dsimp only [bnAddSpec, vals, Arg.val]
            refine ⟨xsA', xsB', xsOut,
              BigNumRt.rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
                cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
                lcnfHeap objs ⋆ R,
              by rw [hna_bv, hlenA']; exact Nat.le_refl _,
              by rw [hnb_bv, hlenB']; exact Nat.le_refl _,
              by rw [hna_bv, hnb_bv]; exact hxsOut_len,
              by rw [hna_bv, hnb_bv]; omega,
              sep_cast_ac hm5 (by (try dsimp only [bufB, bufOut]); ac_rfl),
              fun outXs' m6 hlenO' _ hvalO hm6 => ?_⟩
            rw [hna_bv, hnb_bv, htakeA, htakeB, hvalA', hvalB'] at hvalO ⊢
            have hsum_abs : aVal.natAbs + bVal.natAbs = z.natAbs := by
              have hb_abs : bEff.natAbs = bVal.natAbs := by
                by_cases h4 : op.toNat = 4 <;> simp [bEff, h4]
              omega
            rw [hsum_abs] at hvalO ⊢
            exact ⟨outXs', rfl, hlenO', hvalO, sep_cast_ac hm6
              (by (try dsimp only [bufB, bufOut]); ac_rfl)⟩
          · rintro rnW m6 ⟨xsOut', rfl, hlenOut', hvalOut', hm6⟩
            have htn_lt : limbLenNat z.natAbs < 2 ^ 60 := by omega
            have htn_le_out : limbLenNat z.natAbs ≤ xsOut'.length := by
              have hle : z.natAbs ≤ aVal.natAbs + bVal.natAbs := by omega
              have h1 := Nat.le_trans (limbLenNat_mono hle)
                (limbLenNat_add_le aVal.natAbs bVal.natAbs)
              omega
            have htrimO : trimLenLoop xsOut' (limbLenNat z.natAbs) = limbLenNat z.natAbs := by
              rw [← limbLenNat_trimLenLoop htn_le_out, hvalOut']
            have hval_z : (if limbLenNat z.natAbs = 0 then (0 : Int)
                else if negA = 0#64 then (limbsVal (xsOut'.take (limbLenNat z.natAbs)) : Int)
                else -(limbsVal (xsOut'.take (limbLenNat z.natAbs)) : Int)) = z := by
              rw [hvalOut']
              have hnz : limbLenNat z.natAbs ≠ 0 := by
                intro h0; exact heff_same.2.1 (by have := limbLenNat_pos_iff (n := z.natAbs); omega)
              simp only [hnz, ↓reduceIte, negA]
              by_cases han : aVal < 0
              · have hzn : z < 0 := heff_same.2.2.mpr (by simp [han])
                simp [han]; omega
              · have hzn : ¬(z < 0) := by
                  intro h; have h1 := heff_same.2.2.mp h; simp [han] at h1
                simp [han]; omega
            refine bn_int_from_limbs_call_wp
              (cell64 (rt + 33672#64) scr ⋆
                cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
                array64 scr xsA' ⋆ array64 bufB xsB' ⋆ R)
              htn_lt htn_le_out htnMax hwf.1 htrimO
              hval_z hallocZ (sep_cast_ac hm6 (by (try dsimp only [bufB, bufOut]); ac_rfl)) ?_
            intro res st' objs' m' hpm hrem hb' hrepZ hpres hm'
            rw [wp_ret]; dsimp only [vals, Arg.val]
            exact hPost_z res st' xsOut' objs' m' hpm hrem hb' hlenOut' hrepZ hpres
              (sep_cast_ac hm' (by (try dsimp only [bufB, bufOut]); ac_rfl))
    · intro J_nb hJ_nb; c0_let_simp
      by_cases h5 : op.toNat = 5
      · have heq5 : (op == 5#64) = true := by
          simp only [beq_iff_eq]; exact BitVec.eq_of_toNat_eq (by simpa using h5)
        refine jnz_true heq5 ?_; c0_let_simp
        by_cases hnb0 : 0 < nb
        · have hlt0 : BitVec.ult 0#64 (BitVec.ofNat 64 nb) = true := by
            simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]
            rw [Nat.mod_eq_of_lt (by omega : 0 < 2 ^ 64),
              Nat.mod_eq_of_lt (by omega : nb < 2 ^ 64)]; exact hnb0
          refine jnz_true hlt0 ?_; c0_let_simp
          exact hJ_nb (1#64 - negB, ()) m5 ⟨rfl, by simp [h5, hnb0]⟩
        · have hnlt0 : BitVec.ult 0#64 (BitVec.ofNat 64 nb) = false := by
            simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_false_iff_not]
            rw [Nat.mod_eq_of_lt (by omega : 0 < 2 ^ 64),
              Nat.mod_eq_of_lt (by omega : nb < 2 ^ 64)]; exact hnb0
          refine jnz_false hnlt0 ?_; rw [wp_jump]
          exact hJ_nb (negB, ()) m5 ⟨rfl, by simp [h5, hnb0]⟩
      · have hne5 : (op == 5#64) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply h5; subst h; decide
        refine jnz_false hne5 ?_; rw [wp_jump]
        exact hJ_nb (negB, ()) m5 ⟨rfl, by simp [h5]⟩
  · intro J_as hJ_as; c0_let_simp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop45
    rcases hop45 with h4 | h5
    · have heq4 : (op == 4#64) = true := by
        simp only [beq_iff_eq]; exact BitVec.eq_of_toNat_eq (by simpa using h4)
      refine jnz_true heq4 ?_; rw [wp_jump]; exact hJ_as () m5 rfl
    · have hne4 : (op == 4#64) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 4); subst h
        decide
      have heq5 : (op == 5#64) = true := by
        simp only [beq_iff_eq]; exact BitVec.eq_of_toNat_eq (by simpa using h5)
      refine jnz_false hne4 ?_; c0_let_simp
      refine jnz_true heq5 ?_; rw [wp_jump]; exact hJ_as () m5 rfl

private theorem lcnf_int_addsub_opp_wp
    {rt op a b : BitVec 64} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    {st : RtC0State} {scr : BitVec 64} {scrLimbs : List (BitVec 64)}
    {objs : List LcnfObj} {aVal bVal : Int} {R : Mem 64 → Prop}
    (hwf : BigNumRtWf rt st scr scrLimbs) (hrepA : intRep a aVal objs) (hrepB : intRep b bVal objs)
    (hscrLen : limbLenNat aVal.natAbs + limbLenNat bVal.natAbs +
      max (limbLenNat aVal.natAbs) (limbLenNat bVal.natAbs) + 1 ≤ scrLimbs.length)
    (hop45 : op.toNat ∈ [4, 5])
    (hArithPre :
      let z := if op.toNat = 4 then aVal + bVal else aVal - bVal
      let tn := limbLenNat z.natAbs
      tn ≤ mpzMaxLimbs ∧
      ((z < -(2 ^ 62 : Int) ∨ (2 ^ 62 : Int) ≤ z) → canAllocBytes st (16 + 8 * tn)))
    (ha_nz : aVal ≠ 0) (hb_nz0 : bVal ≠ 0)
    (hopp : ¬((aVal < 0) ↔ ((if op.toNat = 4 then bVal else -bVal) < 0)))
    (hm : (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m)
    (hQ : ∀ res st' scrLimbs' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
      (if op.toNat = 4 then intRep res (aVal + bVal) objs' ∧ (∀ o ∈ objs, o ∈ objs')
       else intRep res (aVal - bVal) objs' ∧ (∀ o ∈ objs, o ∈ objs')) →
      (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m') :
    Func.wp rtR1Env lcnf_int_addsub_cmp.body (rt, op, a, b, ()) m Q X := by
  change wp rtR1Env Q X (lcnf_int_addsub_cmp_body Val Cont (rt, op, a, b, ())) m
  dsimp only [lcnf_int_addsub_cmp_body]
  let na := limbLenNat aVal.natAbs
  let nb := limbLenNat bVal.natAbs
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
    ?_ (fun J hJ => addsub_max_jnz hna_lt hnb_lt m J hJ)
  rintro J ⟨maxnW, ⟨⟩⟩ m3 ⟨hmaxW, hm3⟩
  injection hmaxW with hmaxW'; subst maxnW; subst m3
  rw [Blocks.get.eq_1]; c0_let_simp
  refine bn_require_scratch_call_wp hwf
    (by rw [bv64_need_addsub na nb hna_lt hnb_lt]; exact hscrLen) hm ?_
  c0_let_simp
  let xsA := List.take na scrLimbs
  let xsB := List.take nb (List.drop na scrLimbs)
  let xsOut := List.drop (na + nb) scrLimbs
  have hna_len : xsA.length = na := by simp [xsA]; omega
  have hnb_len : xsB.length = nb := by simp [xsB]; omega
  have hxsOut_len : max na nb + 1 ≤ xsOut.length := by simp [xsOut]; omega
  have hadd_nab : BitVec.ofNat 64 na + BitVec.ofNat 64 nb = BitVec.ofNat 64 (na + nb) :=
    (BitVec.ofNat_add na nb).symm
  rw [bv64_mul8_add (by omega : na < 2 ^ 60), hadd_nab,
    bv64_mul8_add (by omega : na + nb < 2 ^ 60)]
  let bufB := scr + BitVec.ofNat 64 (8 * na)
  let bufOut := scr + BitVec.ofNat 64 (8 * (na + nb))
  have hm_spl : (BigNumRt.rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
      array64 scr xsA ⋆ array64 bufB xsB ⋆ array64 bufOut xsOut ⋆ lcnfHeap objs ⋆ R) m := by
    have hs3 := array64_split3 scr scrLimbs na nb (by omega)
    dsimp only [bigNumRtInv] at hm; rw [hs3] at hm
    exact sep_cast_ac hm (by dsimp only [bufB, bufOut]; ac_rfl)
  refine bn_load_int_call_wp
    (BigNumRt.rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
      array64 bufB xsB ⋆ array64 bufOut xsOut ⋆ R)
    hrepA hna_len (sep_cast_ac hm_spl (by (try dsimp only [bufB, bufOut]); ac_rfl)) ?_
  intro xsA' m4 hlenA' hvalA' hm4
  refine bn_load_int_call_wp
    (BigNumRt.rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
      array64 scr xsA' ⋆ array64 bufOut xsOut ⋆ R)
    hrepB hnb_len (sep_cast_ac hm4 (by (try dsimp only [bufB, bufOut]); ac_rfl)) ?_
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
  refine wp_join_group (fun _ m6 => m6 = m5) ?_ ?_
  · rintro J_as ⟨⟩ m6 hm6; subst m6; rw [Blocks.get.eq_1]
    refine wp_join_group (fun xs m7 =>
      m7 = m5 ∧ xs = ((if op.toNat = 5 ∧ 0 < nb then 1#64 - negB else negB), ())) ?_ ?_
    · rintro J_nb ⟨negBeffW, ⟨⟩⟩ m7 ⟨hm7, hnegBeffEq⟩
      subst m7; injection hnegBeffEq with hnegBeffW; subst hnegBeffW
      rw [Blocks.get.eq_1]
      let bEff : Int := if op.toNat = 4 then bVal else -bVal
      let z : Int := aVal + bEff
      have hz_eq : z = (if op.toNat = 4 then aVal + bVal else aVal - bVal) := by
        by_cases h4 : op.toNat = 4 <;> simp [z, bEff, h4]; omega
      rcases hArithPre with ⟨htnMax, hallocZ⟩
      rw [← hz_eq] at htnMax hallocZ
      have hna0 : na ≠ 0 := Nat.ne_of_gt (limbLenNat_pos_iff.mpr (by omega))
      have hnb0 : nb ≠ 0 := Nat.ne_of_gt (limbLenNat_pos_iff.mpr (by omega))
      have hb_nz : bEff ≠ 0 := by by_cases h4 : op.toNat = 4 <;> simp [bEff, h4] <;> omega
      have hb_abs : bEff.natAbs = bVal.natAbs := by
        by_cases h4 : op.toNat = 4 <;> simp [bEff, h4]
      have hnegBeff_sign : (if op.toNat = 5 ∧ 0 < nb then 1#64 - negB else negB) =
          if bEff < 0 then 1#64 else 0#64 := by
        by_cases h4 : op.toNat = 4
        · simp [bEff, h4, negB]
        · have h5 : op.toNat = 5 := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hop45; omega
          have hnbp : 0 < nb := by omega
          simp only [bEff, h5, show (5 : Nat) ≠ 4 by decide, hnbp, ↓reduceIte, true_and, negB]
          by_cases hbneg : bVal < 0
          · simp only [hbneg, show ¬(-bVal < 0) by omega, ↓reduceIte]; decide
          · simp only [hbneg, show -bVal < 0 by omega, ↓reduceIte]; decide
      have hdiff : negA ≠ if op.toNat = 5 ∧ 0 < nb then 1#64 - negB else negB := by
        rw [hnegBeff_sign]; dsimp only [negA]
        by_cases han : aVal < 0 <;> by_cases hbn : bEff < 0 <;>
          simp only [han, hbn, ↓reduceIte]
        · exact False.elim (hopp ⟨fun _ => hbn, fun _ => han⟩)
        · decide
        · decide
        · exact False.elim (hopp ⟨fun h => False.elim (han h), fun h => False.elim (hbn h)⟩)
      have hPost_z : ∀ res st' xsOut' objs' m',
          st'.PreservesMeta st → st'.rem ≤ st.rem → st'.Bounded48 →
          xsOut'.length = xsOut.length → intRep res z objs' → (∀ o ∈ objs, o ∈ objs') →
          (BigNumRt.rtC0Inv rt st' ⋆ cell64 (rt + 33672#64) scr ⋆
            cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
            array64 scr xsA' ⋆ array64 bufB xsB' ⋆ array64 bufOut xsOut' ⋆
            lcnfHeap objs' ⋆ R) m' → Q (res, ()) m' := by
        intro res st' xsOut' objs' m' hpm hrem hb' hlenOut' hrepZ hpres hm'
        have hjoin_eq := array64_join3 scr xsA' xsB' xsOut' na nb hlenA' hlenB'
        have htot_len : (xsA' ++ xsB' ++ xsOut').length = scrLimbs.length := by
          simp [hlenA', hlenB', hlenOut', xsOut]; omega
        have hwf' := BigNumRtWf.with_state_len hwf hb' htot_len
        have hm_out : (bigNumRtInv rt st' scr (xsA' ++ xsB' ++ xsOut') ⋆ lcnfHeap objs' ⋆
          R) m' := by
          dsimp only [bigNumRtInv]; rw [htot_len, ← hjoin_eq]
          exact sep_cast_ac hm' (by dsimp only [bufB, bufOut]; ac_rfl)
        by_cases h4 : op.toNat = 4
        · have hz4 : z = aVal + bVal := by rw [hz_eq]; simp [h4]
          exact hQ res st' (xsA' ++ xsB' ++ xsOut') objs' m' hpm hrem hwf'
            (by simp only [h4, ↓reduceIte]; exact ⟨by rw [← hz4]; exact hrepZ, hpres⟩) hm_out
        · have hz5 : z = aVal - bVal := by rw [hz_eq]; simp [h4]
          exact hQ res st' (xsA' ++ xsB' ++ xsOut') objs' m' hpm hrem hwf'
            (by simp only [h4, ↓reduceIte]; exact ⟨by rw [← hz5]; exact hrepZ, hpres⟩) hm_out
      have hna_bv : (BitVec.ofNat 64 na).toNat = na := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hnb_bv : (BitVec.ofNat 64 nb).toNat = nb := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have htakeA : List.take na xsA' = xsA' := List.take_of_length_le
        (by rw [hlenA']; exact Nat.le_refl _)
      have htakeB : List.take nb xsB' = xsB' := List.take_of_length_le
        (by rw [hlenB']; exact Nat.le_refl _)
      have hne_na0 : (BitVec.ofNat 64 na == 0#64) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; intro h
        have ht := congrArg BitVec.toNat h; rw [hna_bv] at ht; exact hna0 ht
      have hne_nb0 : (BitVec.ofNat 64 nb == 0#64) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; intro h
        have ht := congrArg BitVec.toNat h; rw [hnb_bv] at ht; exact hnb0 ht
      c0_let_simp
      refine jnz_false hne_na0 ?_; c0_let_simp
      refine jnz_false hne_nb0 ?_; c0_let_simp
      refine jnz_false (by simp only [beq_eq_false_iff_ne, ne_eq]; exact hdiff) ?_
      refine wp_call_ret1 _ _ (fun cW m6 =>
        cW = cmpResult64 aVal.natAbs bVal.natAbs ∧ m6 = m5) ?_ ?_
      · refine rtR1Env_bn_cmp ?_
        dsimp only [bnCmpSpec, vals, Arg.val]
        refine ⟨xsA', xsB',
          BigNumRt.rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
            cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
            array64 bufOut xsOut ⋆ lcnfHeap objs ⋆ R,
          by rw [hna_bv, hlenA']; exact Nat.le_refl _,
          by rw [hnb_bv, hlenB']; exact Nat.le_refl _,
          sep_cast_ac hm5 (by (try dsimp only [bufB, bufOut]); ac_rfl), ?_⟩
        rw [hna_bv, hnb_bv, htakeA, htakeB, hvalA', hvalB']; exact ⟨rfl, rfl⟩
      · rintro cW m6 ⟨rfl, hm6⟩; subst m6; c0_let_simp
        by_cases hcmp0 : aVal.natAbs = bVal.natAbs
        · refine jnz_true (by simp [cmpResult64, hcmp0]) ?_
          rw [wp_ret]; dsimp only [vals, Arg.val]
          have hz0 : z = 0 := by
            have : (aVal < 0) ↔ ¬(bEff < 0) := by
              by_cases ha0 : aVal < 0 <;> by_cases hb0 : bEff < 0 <;>
                simp [bEff, ha0, hb0] at hopp ⊢
            omega
          exact hPost_z 1#64 st xsOut objs m5 ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
            (Nat.le_refl _) hwf.1 rfl (by rw [hz0]; simp [intRep]) (fun _ h => h)
            (sep_cast_ac hm5 (by dsimp only [bufB, bufOut]; ac_rfl))
        · have hnec : (cmpResult64 aVal.natAbs bVal.natAbs == 0#64) = false := by
            simp only [beq_eq_false_iff_ne, ne_eq, cmpResult64]
            by_cases hlt : aVal.natAbs < bVal.natAbs
            · simp only [hlt, ↓reduceIte]; decide
            · have hgt' : bVal.natAbs < aVal.natAbs := by omega
              simp only [hlt, hgt', ↓reduceIte]; decide
          refine jnz_false hnec ?_; c0_let_simp
          by_cases hgt : bVal.natAbs < aVal.natAbs
          · have hsgt : BitVec.slt 0#64 (cmpResult64 aVal.natAbs bVal.natAbs) = true := by
              have h1 : ¬(aVal.natAbs < bVal.natAbs) := by omega
              simp only [cmpResult64, h1, hgt, ↓reduceIte]; decide
            refine jnz_true hsgt ?_
            have heff_gt := int_add_opp_sign_gt ha_nz hb_nz rfl hnegBeff_sign hdiff (by omega)
            refine wp_call_ret1 _ _ (fun rnW m6 =>
              ∃ xsOut',
                rnW = BitVec.ofNat 64 (limbLenNat z.natAbs) ∧
                xsOut'.length = xsOut.length ∧
                limbsVal (List.take (limbLenNat z.natAbs) xsOut') = z.natAbs ∧
                (BigNumRt.rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
                  cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
                  array64 scr xsA' ⋆ array64 bufB xsB' ⋆ array64 bufOut xsOut' ⋆
                  lcnfHeap objs ⋆ R) m6) ?_ ?_
            · refine rtR1Env_bn_sub ?_
              dsimp only [bnSubSpec, vals, Arg.val]
              refine ⟨xsA', xsB', xsOut,
                BigNumRt.rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
                  cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
                  lcnfHeap objs ⋆ R,
                by rw [hna_bv, hlenA']; exact Nat.le_refl _,
                by rw [hnb_bv, hlenB']; exact Nat.le_refl _,
                by rw [hna_bv]; omega,
                by rw [hna_bv, hnb_bv, htakeA, htakeB, hvalA', hvalB']; omega,
                sep_cast_ac hm5 (by (try dsimp only [bufB, bufOut]); ac_rfl),
                fun outXs' m6 hlenO' _ hvalO hm6 => ?_⟩
              rw [hna_bv, hnb_bv, htakeA, htakeB, hvalA', hvalB'] at hvalO ⊢
              have hsub_abs : aVal.natAbs - bVal.natAbs = z.natAbs := by omega
              rw [hsub_abs] at hvalO ⊢
              exact ⟨outXs', rfl, hlenO', hvalO, sep_cast_ac hm6
                (by (try dsimp only [bufB, bufOut]); ac_rfl)⟩
            · rintro rnW m6 ⟨xsOut', rfl, hlenOut', hvalOut', hm6⟩
              have htn_lt : limbLenNat z.natAbs < 2 ^ 60 := by omega
              have htn_le_out : limbLenNat z.natAbs ≤ xsOut'.length := by
                have h1 := limbLenNat_mono (a := z.natAbs) (b := aVal.natAbs) (by omega); omega
              have htrimO : trimLenLoop xsOut' (limbLenNat z.natAbs) = limbLenNat z.natAbs := by
                rw [← limbLenNat_trimLenLoop htn_le_out, hvalOut']
              have hval_z : (if limbLenNat z.natAbs = 0 then (0 : Int)
                  else if negA = 0#64 then (limbsVal (xsOut'.take (limbLenNat z.natAbs)) : Int)
                  else -(limbsVal (xsOut'.take (limbLenNat z.natAbs)) : Int)) = z := by
                rw [hvalOut']
                have hnz : limbLenNat z.natAbs ≠ 0 := by
                  intro h0; exact heff_gt.2.1 (by have := limbLenNat_pos_iff (n := z.natAbs); omega)
                simp only [hnz, ↓reduceIte, negA]
                by_cases han : aVal < 0
                · have hzn : z < 0 := heff_gt.2.2.mpr (by simp [han])
                  simp [han]; omega
                · have hzn : ¬(z < 0) := by
                    intro h; have h1 := heff_gt.2.2.mp h; simp [han] at h1
                  simp [han]; omega
              refine bn_int_from_limbs_call_wp
                (cell64 (rt + 33672#64) scr ⋆
                  cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
                  array64 scr xsA' ⋆ array64 bufB xsB' ⋆ R)
                htn_lt htn_le_out htnMax hwf.1 htrimO
                hval_z hallocZ (sep_cast_ac hm6 (by (try dsimp only [bufB, bufOut]); ac_rfl)) ?_
              intro res st' objs' m' hpm hrem hb' hrepZ hpres hm'
              rw [wp_ret]; dsimp only [vals, Arg.val]
              exact hPost_z res st' xsOut' objs' m' hpm hrem hb' hlenOut' hrepZ hpres
                (sep_cast_ac hm' (by (try dsimp only [bufB, bufOut]); ac_rfl))
          · have hlt : aVal.natAbs < bVal.natAbs := by omega
            have hnsgt : BitVec.slt 0#64 (cmpResult64 aVal.natAbs bVal.natAbs) = false := by
              simp [cmpResult64, hlt, BitVec.slt]
            refine jnz_false hnsgt ?_
            have heff_lt := int_add_opp_sign_gt hb_nz ha_nz hnegBeff_sign rfl
              (Ne.symm hdiff) (by omega)
            have hz_sym : bEff + aVal = z := by omega
            rw [hz_sym] at heff_lt
            refine wp_call_ret1 _ _ (fun rnW m6 =>
              ∃ xsOut',
                rnW = BitVec.ofNat 64 (limbLenNat z.natAbs) ∧
                xsOut'.length = xsOut.length ∧
                limbsVal (List.take (limbLenNat z.natAbs) xsOut') = z.natAbs ∧
                (BigNumRt.rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
                  cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
                  array64 scr xsA' ⋆ array64 bufB xsB' ⋆ array64 bufOut xsOut' ⋆
                  lcnfHeap objs ⋆ R) m6) ?_ ?_
            · refine rtR1Env_bn_sub ?_
              dsimp only [bnSubSpec, vals, Arg.val]
              refine ⟨xsB', xsA', xsOut,
                BigNumRt.rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
                  cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
                  lcnfHeap objs ⋆ R,
                by rw [hnb_bv, hlenB']; exact Nat.le_refl _,
                by rw [hna_bv, hlenA']; exact Nat.le_refl _,
                by rw [hnb_bv]; omega,
                by rw [hna_bv, hnb_bv, htakeA, htakeB, hvalA', hvalB']; omega,
                sep_cast_ac hm5 (by (try dsimp only [bufB, bufOut]); ac_rfl),
                fun outXs' m6 hlenO' _ hvalO hm6 => ?_⟩
              rw [hna_bv, hnb_bv, htakeA, htakeB, hvalA', hvalB'] at hvalO ⊢
              have hsub_abs : bVal.natAbs - aVal.natAbs = z.natAbs := by omega
              rw [hsub_abs] at hvalO ⊢
              exact ⟨outXs', rfl, hlenO', hvalO, sep_cast_ac hm6
                (by (try dsimp only [bufB, bufOut]); ac_rfl)⟩
            · rintro rnW m6 ⟨xsOut', rfl, hlenOut', hvalOut', hm6⟩
              have htn_lt : limbLenNat z.natAbs < 2 ^ 60 := by omega
              have htn_le_out : limbLenNat z.natAbs ≤ xsOut'.length := by
                have h1 := limbLenNat_mono (a := z.natAbs) (b := bVal.natAbs) (by omega); omega
              have htrimO : trimLenLoop xsOut' (limbLenNat z.natAbs) = limbLenNat z.natAbs := by
                rw [← limbLenNat_trimLenLoop htn_le_out, hvalOut']
              have hval_z : (if limbLenNat z.natAbs = 0 then (0 : Int)
                  else if (if op.toNat = 5 ∧ 0 < nb then 1#64 - negB else negB) = 0#64 then
                    (limbsVal (xsOut'.take (limbLenNat z.natAbs)) : Int)
                  else -(limbsVal (xsOut'.take (limbLenNat z.natAbs)) : Int)) = z := by
                rw [hvalOut', hnegBeff_sign]
                have hnz : limbLenNat z.natAbs ≠ 0 := by
                  intro h0; exact heff_lt.2.1 (by have := limbLenNat_pos_iff (n := z.natAbs); omega)
                simp only [hnz, ↓reduceIte]
                by_cases hbn : bEff < 0
                · have hzn : z < 0 := heff_lt.2.2.mpr (by rw [hnegBeff_sign]; simp [hbn])
                  simp [hbn]; omega
                · have hzn : ¬(z < 0) := by
                    intro h; have h1 := heff_lt.2.2.mp h; rw [hnegBeff_sign] at h1; simp [hbn] at h1
                  simp [hbn]; omega
              refine bn_int_from_limbs_call_wp
                (cell64 (rt + 33672#64) scr ⋆
                  cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
                  array64 scr xsA' ⋆ array64 bufB xsB' ⋆ R)
                htn_lt htn_le_out htnMax hwf.1 htrimO
                hval_z hallocZ (sep_cast_ac hm6 (by (try dsimp only [bufB, bufOut]); ac_rfl)) ?_
              intro res st' objs' m' hpm hrem hb' hrepZ hpres hm'
              rw [wp_ret]; dsimp only [vals, Arg.val]
              exact hPost_z res st' xsOut' objs' m' hpm hrem hb' hlenOut' hrepZ hpres
                (sep_cast_ac hm' (by (try dsimp only [bufB, bufOut]); ac_rfl))
    · intro J_nb hJ_nb; c0_let_simp
      by_cases h5 : op.toNat = 5
      · have heq5 : (op == 5#64) = true := by
          simp only [beq_iff_eq]; exact BitVec.eq_of_toNat_eq (by simpa using h5)
        refine jnz_true heq5 ?_; c0_let_simp
        have hnbp : 0 < nb := limbLenNat_pos_iff.mpr (by omega)
        have hlt0 : BitVec.ult 0#64 (BitVec.ofNat 64 nb) = true := by
          simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_true_eq]
          rw [Nat.mod_eq_of_lt (by omega : 0 < 2 ^ 64),
            Nat.mod_eq_of_lt (by omega : nb < 2 ^ 64)]; exact hnbp
        refine jnz_true hlt0 ?_; c0_let_simp
        exact hJ_nb (1#64 - negB, ()) m5 ⟨rfl, by simp [h5, hnbp]⟩
      · have hne5 : (op == 5#64) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply h5; subst h; decide
        refine jnz_false hne5 ?_; rw [wp_jump]
        exact hJ_nb (negB, ()) m5 ⟨rfl, by simp [h5]⟩
  · intro J_as hJ_as; c0_let_simp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hop45
    rcases hop45 with h4 | h5
    · have heq4 : (op == 4#64) = true := by
        simp only [beq_iff_eq]; exact BitVec.eq_of_toNat_eq (by simpa using h4)
      refine jnz_true heq4 ?_; rw [wp_jump]; exact hJ_as () m5 rfl
    · have hne4 : (op == 4#64) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 4); subst h
        decide
      have heq5 : (op == 5#64) = true := by
        simp only [beq_iff_eq]; exact BitVec.eq_of_toNat_eq (by simpa using h5)
      refine jnz_false hne4 ?_; c0_let_simp
      refine jnz_true heq5 ?_; rw [wp_jump]; exact hJ_as () m5 rfl

private theorem lcnf_int_cmp_wp
    {rt op a b : BitVec 64} {m : Mem 64} {Q : Post [i64]} {X : XPost}
    {st : RtC0State} {scr : BitVec 64} {scrLimbs : List (BitVec 64)}
    {objs : List LcnfObj} {aVal bVal : Int} {R : Mem 64 → Prop}
    (hwf : BigNumRtWf rt st scr scrLimbs) (hrepA : intRep a aVal objs) (hrepB : intRep b bVal objs)
    (hscrLen : limbLenNat aVal.natAbs + limbLenNat bVal.natAbs +
      max (limbLenNat aVal.natAbs) (limbLenNat bVal.natAbs) + 1 ≤ scrLimbs.length)
    (hopCmp : op.toNat = 10 ∨ op.toNat = 11 ∨ op.toNat = 12)
    (hm : (bigNumRtInv rt st scr scrLimbs ⋆ lcnfHeap objs ⋆ R) m)
    (hQ : ∀ res st' scrLimbs' objs' m',
      st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
      (if op.toNat = 10 then res = (if aVal = bVal then 1#64 else 0#64) ∧ objs' = objs
       else if op.toNat = 11 then res = (if aVal < bVal then 1#64 else 0#64) ∧ objs' = objs
       else res = (if aVal ≤ bVal then 1#64 else 0#64) ∧ objs' = objs) →
      (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m') :
    Func.wp rtR1Env lcnf_int_addsub_cmp.body (rt, op, a, b, ()) m Q X := by
  change wp rtR1Env Q X (lcnf_int_addsub_cmp_body Val Cont (rt, op, a, b, ())) m
  dsimp only [lcnf_int_addsub_cmp_body]
  let na := limbLenNat aVal.natAbs
  let nb := limbLenNat bVal.natAbs
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
    ?_ (fun J hJ => addsub_max_jnz hna_lt hnb_lt m J hJ)
  rintro J ⟨maxnW, ⟨⟩⟩ m3 ⟨hmaxW, hm3⟩
  injection hmaxW with hmaxW'; subst maxnW; subst m3
  rw [Blocks.get.eq_1]; c0_let_simp
  refine bn_require_scratch_call_wp hwf
    (by rw [bv64_need_addsub na nb hna_lt hnb_lt]; exact hscrLen) hm ?_
  c0_let_simp
  let xsA := List.take na scrLimbs
  let xsB := List.take nb (List.drop na scrLimbs)
  let xsOut := List.drop (na + nb) scrLimbs
  have hna_len : xsA.length = na := by simp [xsA]; omega
  have hnb_len : xsB.length = nb := by simp [xsB]; omega
  have hadd_nab : BitVec.ofNat 64 na + BitVec.ofNat 64 nb = BitVec.ofNat 64 (na + nb) :=
    (BitVec.ofNat_add na nb).symm
  rw [bv64_mul8_add (by omega : na < 2 ^ 60), hadd_nab,
    bv64_mul8_add (by omega : na + nb < 2 ^ 60)]
  let bufB := scr + BitVec.ofNat 64 (8 * na)
  let bufOut := scr + BitVec.ofNat 64 (8 * (na + nb))
  have hm_spl : (BigNumRt.rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
      array64 scr xsA ⋆ array64 bufB xsB ⋆ array64 bufOut xsOut ⋆ lcnfHeap objs ⋆ R) m := by
    have hs3 := array64_split3 scr scrLimbs na nb (by omega)
    dsimp only [bigNumRtInv] at hm; rw [hs3] at hm
    exact sep_cast_ac hm (by dsimp only [bufB, bufOut]; ac_rfl)
  refine bn_load_int_call_wp
    (BigNumRt.rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
      array64 bufB xsB ⋆ array64 bufOut xsOut ⋆ R)
    hrepA hna_len (sep_cast_ac hm_spl (by (try dsimp only [bufB, bufOut]); ac_rfl)) ?_
  intro xsA' m4 hlenA' hvalA' hm4
  refine bn_load_int_call_wp
    (BigNumRt.rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
      cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
      array64 scr xsA' ⋆ array64 bufOut xsOut ⋆ R)
    hrepB hnb_len (sep_cast_ac hm4 (by (try dsimp only [bufB, bufOut]); ac_rfl)) ?_
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
  refine wp_join_group (fun _ _ => False) (fun _ _ _ h => h.elim) ?_
  intro _ _; c0_let_simp
  have hne4 : (op == 4#64) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 4); subst h
    decide
  have hne5 : (op == 5#64) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply (by omega : op.toNat ≠ 5); subst h
    decide
  refine jnz_false hne4 ?_; c0_let_simp; refine jnz_false hne5 ?_; c0_let_simp
  have hjoin_eq := array64_join3 scr xsA' xsB' xsOut na nb hlenA' hlenB'
  have htot_len : (xsA' ++ xsB' ++ xsOut).length = scrLimbs.length := by
    simp [hlenA', hlenB', xsOut]; omega
  have hwf' := BigNumRtWf.with_state_len hwf hwf.1 htot_len
  have hm5_full : (bigNumRtInv rt st scr (xsA' ++ xsB' ++ xsOut) ⋆ lcnfHeap objs ⋆ R) m5 := by
    dsimp only [bigNumRtInv]; rw [htot_len, ← hjoin_eq]
    exact sep_cast_ac hm5 (by dsimp only [bufB, bufOut]; ac_rfl)
  refine wp_join_group (fun xs m6 => xs = (cmpResult64Int aVal bVal, ()) ∧ m6 = m5) ?_ ?_
  · rintro J_cmp ⟨cmpW, ⟨⟩⟩ m6 ⟨hcEq, hm6⟩
    subst m6; injection hcEq with hcmpW; subst hcmpW
    rw [Blocks.get.eq_1]; c0_let_simp
    have finishCmp := fun (res : BitVec 64)
        (hres : if op.toNat = 10 then res = (if aVal = bVal then 1#64 else 0#64) ∧ objs = objs
          else if op.toNat = 11 then res = (if aVal < bVal then 1#64 else 0#64) ∧ objs = objs
          else res = (if aVal ≤ bVal then 1#64 else 0#64) ∧ objs = objs) =>
      hQ res st (xsA' ++ xsB' ++ xsOut) objs m5
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (Nat.le_refl _) hwf' hres hm5_full
    by_cases h10 : op.toNat = 10
    · have heq10 : (op == 10#64) = true := by
        simp only [beq_iff_eq]; exact BitVec.eq_of_toNat_eq (by simpa using h10)
      refine jnz_true heq10 ?_
      refine wp_join_group (fun xs m7 =>
        xs = ((if aVal = bVal then 1#64 else 0#64), ()) ∧ m7 = m5) ?_ ?_
      · rintro _ ⟨w10, ⟨⟩⟩ m7 ⟨hw10, hm7⟩
        subst m7; injection hw10 with hw10'; subst w10
        rw [Blocks.get.eq_1, wp_ret]; dsimp only [vals, Arg.val]
        exact finishCmp _ (by simp [h10])
      · intro J1 hJ1; c0_let_simp
        by_cases heq_ab : aVal = bVal
        · refine jnz_true (by simp [cmpResult64Int, heq_ab]) ?_; rw [wp_jump]
          exact hJ1 (1#64, ()) m5 ⟨by simp [heq_ab], rfl⟩
        · have hne_c : (cmpResult64Int aVal bVal == 0#64) = false := by
            simp only [beq_eq_false_iff_ne, ne_eq, cmpResult64Int]
            by_cases hlt : aVal < bVal
            · simp only [hlt, ↓reduceIte]; decide
            · simp only [hlt, heq_ab, ↓reduceIte]; decide
          refine jnz_false hne_c ?_; rw [wp_jump]
          exact hJ1 (0#64, ()) m5 ⟨by simp [heq_ab], rfl⟩
    · have hne10 : (op == 10#64) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply h10; subst h; decide
      refine jnz_false hne10 ?_; c0_let_simp
      by_cases h11 : op.toNat = 11
      · have heq11 : (op == 11#64) = true := by
          simp only [beq_iff_eq]; exact BitVec.eq_of_toNat_eq (by simpa using h11)
        refine jnz_true heq11 ?_
        refine wp_join_group (fun xs m7 =>
          xs = ((if aVal < bVal then 1#64 else 0#64), ()) ∧ m7 = m5) ?_ ?_
        · rintro _ ⟨w11, ⟨⟩⟩ m7 ⟨hw11, hm7⟩
          subst m7; injection hw11 with hw11'; subst w11
          rw [Blocks.get.eq_1, wp_ret]; dsimp only [vals, Arg.val]
          exact finishCmp _ (by simp [h11])
        · intro J1 hJ1; c0_let_simp
          by_cases hlt_ab : aVal < bVal
          · have hslt : BitVec.slt (cmpResult64Int aVal bVal) 0#64 = true := by
              simp [cmpResult64Int, hlt_ab, BitVec.slt]
            refine jnz_true hslt ?_; rw [wp_jump]
            exact hJ1 (1#64, ()) m5 ⟨by simp [hlt_ab], rfl⟩
          · have hnslt : BitVec.slt (cmpResult64Int aVal bVal) 0#64 = false := by
              simp only [cmpResult64Int, hlt_ab, ↓reduceIte, BitVec.slt]
              by_cases heq_ab : aVal = bVal
              · simp only [heq_ab, ↓reduceIte]; decide
              · simp only [heq_ab, ↓reduceIte]; decide
            refine jnz_false hnslt ?_; rw [wp_jump]
            exact hJ1 (0#64, ()) m5 ⟨by simp [hlt_ab], rfl⟩
      · have h12 : op.toNat = 12 := by omega
        have hne11 : (op == 11#64) = false := by
          simp only [beq_eq_false_iff_ne, ne_eq]; intro h; apply h11; subst h; decide
        refine jnz_false hne11 ?_
        refine wp_join_group (fun xs m7 =>
          xs = ((if aVal ≤ bVal then 1#64 else 0#64), ()) ∧ m7 = m5) ?_ ?_
        · rintro _ ⟨w12, ⟨⟩⟩ m7 ⟨hw12, hm7⟩
          subst m7; injection hw12 with hw12'; subst w12
          rw [Blocks.get.eq_1, wp_ret]; dsimp only [vals, Arg.val]
          exact finishCmp _ (by simp [h12])
        · intro J1 hJ1; c0_let_simp
          by_cases hle_ab : aVal ≤ bVal
          · have hsle : BitVec.sle (cmpResult64Int aVal bVal) 0#64 = true := by
              by_cases hlt : aVal < bVal
              · simp [cmpResult64Int, hlt, BitVec.sle]
              · have heq_ab : aVal = bVal := by omega
                simp [cmpResult64Int, heq_ab, BitVec.sle]
            refine jnz_true hsle ?_; rw [wp_jump]
            exact hJ1 (1#64, ()) m5 ⟨by simp [hle_ab], rfl⟩
          · have hnsle : BitVec.sle (cmpResult64Int aVal bVal) 0#64 = false := by
              have h1 : ¬(aVal < bVal) := by omega
              have h2 : aVal ≠ bVal := by omega
              simp [cmpResult64Int, h1, h2, BitVec.sle]
            refine jnz_false hnsle ?_; rw [wp_jump]
            exact hJ1 (0#64, ()) m5 ⟨by simp [hle_ab], rfl⟩
  · intro J_cmp hJ_cmp; c0_let_simp
    by_cases hdiff : negA ≠ negB
    · refine jnz_true (by simp only [bne_iff_ne, ne_eq]; exact hdiff) ?_
      refine wp_join_group (fun xs m6 =>
        xs = ((if negA ≠ 0#64 then -(1#32) else 1#32), ()) ∧ m6 = m5) ?_ ?_
      · rintro _ ⟨w32, ⟨⟩⟩ m6 ⟨hw32, hm6⟩
        subst m6; injection hw32 with hw32'; subst w32
        rw [Blocks.get.eq_1]; c0_let_simp
        by_cases han : negA = 0#64
        · have ha0 : ¬(aVal < 0) := by intro h; simp [negA, h] at han
          have hb0 : bVal < 0 := by
            by_cases hb0' : bVal < 0
            · exact hb0'
            · simp [negA, negB, han, hb0'] at hdiff
          have hc : BitVec.signExtend 64 (if negA ≠ 0#64 then -(1#32) else 1#32) =
              cmpResult64Int aVal bVal := by
            simp only [han, ne_eq, not_true_eq_false, ↓reduceIte, cmpResult64Int,
              show ¬(aVal < bVal) by omega, show aVal ≠ bVal by omega]; decide
          rw [hc]; exact hJ_cmp (cmpResult64Int aVal bVal, ()) m5 ⟨rfl, rfl⟩
        · have ha0 : aVal < 0 := by
            by_cases ha0' : aVal < 0
            · exact ha0'
            · simp [negA, ha0'] at han
          have hnb0 : ¬(bVal < 0) := by intro hb0; simp [negA, negB, ha0, hb0] at hdiff
          have hc : BitVec.signExtend 64 (if negA ≠ 0#64 then -(1#32) else 1#32) =
              cmpResult64Int aVal bVal := by
            simp only [han, ne_eq, not_false_eq_true, ↓reduceIte, cmpResult64Int,
              show aVal < bVal by omega]; decide
          rw [hc]; exact hJ_cmp (cmpResult64Int aVal bVal, ()) m5 ⟨rfl, rfl⟩
      · intro J1 hJ1; c0_let_simp
        by_cases hna0' : negA ≠ 0#64
        · refine jnz_true (by simp only [bne_iff_ne, ne_eq]; exact hna0') ?_; c0_let_simp
          exact hJ1 (-1#32, ()) m5 ⟨by simp [hna0'], rfl⟩
        · have heq0 : negA = 0#64 := by
            by_cases h : negA = 0#64; exact h; exact False.elim (hna0' h)
          refine jnz_false (by simp only [bne_eq_false_iff_eq]; exact heq0) ?_; rw [wp_jump]
          exact hJ1 (1#32, ()) m5 ⟨by simp [heq0], rfl⟩
    · have heq_s : negA = negB := by
        by_cases h : negA = negB; exact h; exact False.elim (hdiff h)
      refine jnz_false (by simp only [bne_eq_false_iff_eq]; exact heq_s) ?_
      have hna_bv : (BitVec.ofNat 64 na).toNat = na := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hnb_bv : (BitVec.ofNat 64 nb).toNat = nb := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have htakeA : List.take na xsA' = xsA' := List.take_of_length_le
        (by rw [hlenA']; exact Nat.le_refl _)
      have htakeB : List.take nb xsB' = xsB' := List.take_of_length_le
        (by rw [hlenB']; exact Nat.le_refl _)
      refine wp_call_ret1 _ _ (fun cW m6 =>
        cW = cmpResult64 aVal.natAbs bVal.natAbs ∧ m6 = m5) ?_ ?_
      · refine rtR1Env_bn_cmp ?_
        dsimp only [bnCmpSpec, vals, Arg.val]
        refine ⟨xsA', xsB',
          BigNumRt.rtC0Inv rt st ⋆ cell64 (rt + 33672#64) scr ⋆
            cell64 (rt + 33680#64) (BitVec.ofNat 64 scrLimbs.length) ⋆
            array64 bufOut xsOut ⋆ lcnfHeap objs ⋆ R,
          by rw [hna_bv, hlenA']; exact Nat.le_refl _,
          by rw [hnb_bv, hlenB']; exact Nat.le_refl _,
          sep_cast_ac hm5 (by (try dsimp only [bufB, bufOut]); ac_rfl), ?_⟩
        rw [hna_bv, hnb_bv, htakeA, htakeB, hvalA', hvalB']; exact ⟨rfl, rfl⟩
      · rintro cW m6 ⟨rfl, hm6⟩; subst m6
        refine wp_join_group (fun xs m7 => xs = (cmpResult64Int aVal bVal, ()) ∧ m7 = m5) ?_ ?_
        · rintro _ ⟨w, ⟨⟩⟩ m7 ⟨hw, hm7⟩
          subst m7; injection hw with hw'; subst w
          rw [Blocks.get.eq_1, wp_jump]
          exact hJ_cmp (cmpResult64Int aVal bVal, ()) m5 ⟨rfl, rfl⟩
        · intro J1 hJ1; c0_let_simp
          have hcmp := cmpResult64Int_of_same_sign (a := aVal) (b := bVal)
            (negA := negA) (negB := negB) rfl rfl heq_s
          by_cases hna0' : negA ≠ 0#64
          · refine jnz_true (by simp only [bne_iff_ne, ne_eq]; exact hna0') ?_; c0_let_simp
            have hcmp1 : -cmpResult64 aVal.natAbs bVal.natAbs = cmpResult64Int aVal bVal := by
              split at hcmp
              · exact hcmp
              · exfalso
                have hneg1 : negA = 1#64 := by
                  by_cases h : aVal < 0 <;> simp [negA, h] at hna0' ⊢
                simp_all
            rw [hcmp1]; exact hJ1 (cmpResult64Int aVal bVal, ()) m5 ⟨rfl, rfl⟩
          · have heq0 : negA = 0#64 := by
              by_cases h : negA = 0#64; exact h; exact False.elim (hna0' h)
            refine jnz_false (by simp only [bne_eq_false_iff_eq]; exact heq0) ?_; rw [wp_jump]
            have hcmp0 : cmpResult64 aVal.natAbs bVal.natAbs = cmpResult64Int aVal bVal := by
              split at hcmp
              · exfalso; simp_all
              · exact hcmp
            rw [hcmp0]; exact hJ1 (cmpResult64Int aVal bVal, ()) m5 ⟨rfl, rfl⟩

theorem lcnf_int_addsub_cmp_wp :
    ∀ xs m Q X, lcnfIntAddSubCmpSpec xs m Q X →
      Func.wp rtR1Env lcnf_int_addsub_cmp.body xs m Q X := by
  rintro ⟨rt, op, a, b, ⟨⟩⟩ m Q X ⟨st, scr, scrLimbs, objs, aVal, bVal, R,
      hwf, hrepA, hrepB, hscrLen, hopMem, hArithPre, hm, hQ⟩
  by_cases hop45 : op.toNat ∈ [4, 5]
  · have hQ45 : ∀ res st' scrLimbs' objs' m',
        st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
        (if op.toNat = 4 then intRep res (aVal + bVal) objs' ∧ (∀ o ∈ objs, o ∈ objs')
         else intRep res (aVal - bVal) objs' ∧ (∀ o ∈ objs, o ∈ objs')) →
        (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m' := by
      intro res st' sl' objs' m' hpm hrem hwf' hres hm'
      refine hQ res st' sl' objs' m' hpm hrem hwf' ?_ hm'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hop45
      rcases hop45 with h4 | h5
      · simpa [h4] using hres
      · simp only [h5, show (5 : Nat) ≠ 4 by decide, ↓reduceIte] at hres ⊢
        exact hres
    by_cases hsame : aVal = 0 ∨ bVal = 0 ∨
        ((aVal < 0) ↔ ((if op.toNat = 4 then bVal else -bVal) < 0))
    · exact lcnf_int_addsub_same_wp hwf hrepA hrepB hscrLen hop45 (hArithPre hop45) hsame hm hQ45
    · exact lcnf_int_addsub_opp_wp hwf hrepA hrepB hscrLen hop45 (hArithPre hop45)
        (fun h => hsame (Or.inl h)) (fun h => hsame (Or.inr (Or.inl h)))
        (fun h => hsame (Or.inr (Or.inr h))) hm hQ45
  · have hopCmp : op.toNat = 10 ∨ op.toNat = 11 ∨ op.toNat = 12 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hopMem hop45
      rcases hopMem with h | h | h | h | h <;> first | exact False.elim (hop45 (by omega)) | omega
    have hQcmp : ∀ res st' scrLimbs' objs' m',
        st'.PreservesMeta st → st'.rem ≤ st.rem → BigNumRtWf rt st' scr scrLimbs' →
        (if op.toNat = 10 then res = (if aVal = bVal then 1#64 else 0#64) ∧ objs' = objs
         else if op.toNat = 11 then res = (if aVal < bVal then 1#64 else 0#64) ∧ objs' = objs
         else res = (if aVal ≤ bVal then 1#64 else 0#64) ∧ objs' = objs) →
        (bigNumRtInv rt st' scr scrLimbs' ⋆ lcnfHeap objs' ⋆ R) m' → Q (res, ()) m' := by
      intro res st' sl' objs' m' hpm hrem hwf' hres hm'
      have hne4 : op.toNat ≠ 4 := by omega
      have hne5 : op.toNat ≠ 5 := by omega
      exact hQ res st' sl' objs' m' hpm hrem hwf'
        (by simpa only [hne4, hne5, ↓reduceIte] using hres) hm'
    exact lcnf_int_cmp_wp hwf hrepA hrepB hscrLen hopCmp hm hQcmp

end LeanQbe.T.LeanLCNF
