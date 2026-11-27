module

public import LeanQbe.T.LeanLCNF.Sem.PerceusPrims1

/-!
# Perceus Tier-P → Tier-H Soundness: Read-Only & Unified Primitives (`PerceusPrims`)

Completes safe primitive simulation for read-only container/string/tag primitives,
`outOfBounds._redArg`, and unified `primP_sim`:
- `primReadOnly_sim`
- `outOfBounds_sim`
- `primP_sim`
-/

set_option autoImplicit false

namespace LeanQbe.T.LeanLCNF.Sem

open LeanQbe.T
open LeanQbe.T.LeanLCNF

public section

private def argNonScFlag (ctx : RcCtx) : LcArg → Bool
  | .erased => true
  | .var x => match ctx.get? x with | some v => !v.ty.isScalar | none => false

private theorem uintWidth_prefixes {s : String} {w : Nat} (hw : uintWidth? s = some w) :
    s = "UInt8" ∨ s = "UInt16" ∨ s = "UInt32" ∨ s = "UInt64" ∨ s = "USize" := by
  unfold uintWidth? at hw; split at hw <;> simp at hw
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

private theorem propagateMark_valRep {rf : RcFrame} {σ : HState}
    (hvar : ∀ v ∈ rf.ctx.vars, VarInv v rf σ.objs)
    {as : List LcArg} {aLast : LcArg} {pvLast : PVal} {wLast : Word} {retTy : LcTy}
    (hlast : as.getLast? = some aLast)
    (ha_ns : argNonScFlag rf.ctx aLast = true)
    (hlive : aLast = .erased ∨ ∃ z v, aLast = .var z ∧ rf.ctx.get? z = some v ∧ v.isLive = true)
    (hep : rf.envP.evalArg aLast = some pvLast) (heh : rf.envH.evalArgOwn aLast = some wLast)
    (hrt_rc : retTy.needsRc = true)
    (hpm : retTy = LcTy.tobject ∨
      ∃ y vy, as.getLast? = some (LcArg.var y) ∧ rf.ctx.get? y = some vy ∧ vy.ty = LcTy.object) :
    ValRep retTy pvLast wLast σ.objs := by
  have hrt_ns : retTy.isScalar = false := by revert hrt_rc; cases retTy <;> decide
  have hrt_w : retTy.width = 64 := by revert hrt_rc; cases retTy <;> decide
  have hrt_nt : retTy ≠ LcTy.tagged := fun h => by rw [h] at hrt_rc; revert hrt_rc; decide
  rcases argNonSc_info_of hvar ha_ns hlive hep heh with
    ⟨rfl, rfl, rfl, hrep⟩ | ⟨z, vz, rfl, hgz, hns, _, hrep⟩
  · rcases hpm with rfl | ⟨_, _, hq, _⟩
    · exact hrep
    · rw [hlast] at hq; cases hq
  · have hns_z : vz.ty.isScalar = false := Bool.eq_false_iff.mpr hns
    have hw_z : vz.ty.width = 64 := by revert hns_z; cases vz.ty <;> decide
    rcases hpm with rfl | ⟨y, vy, hq, hgy, hvy⟩
    · exact valRep_cast hrep (hns_z.trans hrt_ns.symm) (hw_z.trans hrt_w.symm)
        (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
    · rw [hlast] at hq; cases hq; rw [hgz] at hgy; cases hgy
      exact valRep_cast hrep (hns_z.trans hrt_ns.symm) (hw_z.trans hrt_w.symm)
        (fun _ => hvy) (fun h => absurd h hrt_nt)

private theorem valRep_needsRc_word_ty {ty : LcTy} {pv : PVal} {w : Word}
    {objs : List LcnfObj} (hrc : ty.needsRc = true) (hrep : ValRep ty pv w objs) :
    w.1 = i64 := by
  have hns : ty.isScalar = false := by revert hrc; cases ty <;> decide
  unfold ValRep at hrep
  simp only [hns, Bool.false_eq_true, ↓reduceIte] at hrep
  rcases hrep with ⟨bv, rfl, _⟩
  rfl

private def tagNatSafe : PVal → Prop
  | .nat n => n < 2 ^ 63
  | .bits bw _ => bw < 64
  | .ctor c _ _ => c < 2 ^ 63
  | .erased => True
  | _ => False

private theorem getObjTagNat_step {σ : HState} {v : PVal} {w : Word} {tyv retTy : LcTy}
    (hns : ¬tyv.isScalar) (hrep : ValRep tyv v w σ.objs)
    (hrt : (retTy == LcTy.tobject || retTy == LcTy.tagged) = true)
    (hsafe : tagNatSafe v)
    {nv : Nat} (htag : v.tag? = some nv)
    {K : HPost}
    (hk : ∀ {rw : Word}, ValRep retTy (PVal.nat nv) rw σ.objs →
      (¬retTy.isScalar → ∃ bv, rw = Word.i64 bv ∧ bv &&& 1#64 ≠ 0#64) → K rw σ) :
    match w.toBV64? with
    | some x =>
      if x &&& 1#64 ≠ 0#64 then K (Word.i64 x) σ
      else ∃ o, o ∈ σ.objs ∧ o.addr = x ∧ o.Wf ∧
        K (Word.i64 (BitVec.ofNat 64 o.tag <<< 1 ||| 1#64)) σ
    | none => False := by
  unfold ValRep at hrep
  simp only [Bool.eq_false_iff.mpr hns, Bool.false_eq_true, ↓reduceIte] at hrep
  rcases hrep with ⟨bv, hw, hobj, _, _⟩
  rw [hw]; simp only [Word.toBV64?, Word.i64]
  cases v with
  | nat n =>
    simp only [tagNatSafe] at hsafe
    simp only [PVal.tag?, Option.some.injEq] at htag; subst htag
    rw [ObjRep.eq_3, natRepR0_small hsafe] at hobj; rw [hobj]
    rw [ite_eq_left (boxNat_and1_ne_zero n)]
    have hrv := retValRep_small_nat hrt hsafe (objs := σ.objs)
    exact hk hrv.1 hrv.2
  | bits m b =>
    simp only [tagNatSafe] at hsafe
    simp only [PVal.tag?, Option.some.injEq] at htag; subst htag
    rw [ObjRep.eq_2] at hobj
    rcases hobj with ⟨_, hbv⟩ | ⟨hm64, _⟩
    · have hb_lt : b.toNat < 2 ^ 63 :=
        Nat.lt_of_lt_of_le b.isLt (Nat.pow_le_pow_right (by omega) (by omega))
      rw [hbv, bv64_tagged_bits_eq_ofNat hsafe]
      rw [ite_eq_left (boxNat_and1_ne_zero b.toNat)]
      have hrv := retValRep_small_nat hrt hb_lt (objs := σ.objs)
      exact hk hrv.1 hrv.2
    · omega
  | erased =>
    simp only [PVal.tag?, Option.some.injEq] at htag; subst htag
    rw [ObjRep.eq_1] at hobj; rw [hobj]
    rw [ite_eq_left (by decide)]
    have hrv := retValRep_small_nat hrt (show 0 < 2 ^ 63 by decide) (objs := σ.objs)
    exact hk hrv.1 hrv.2
  | ctor c fields scal =>
    simp only [tagNatSafe] at hsafe
    simp only [PVal.tag?, Option.some.injEq] at htag; subst htag
    rw [ObjRep.eq_4] at hobj
    rcases hobj with ⟨_, _, _, hbv⟩ | ⟨_, o, ho, hoa, howf, hotag, _, _, _⟩
    · rw [hbv]
      rw [ite_eq_left (boxNat_and1_ne_zero c)]
      have hrv := retValRep_small_nat hrt hsafe (objs := σ.objs)
      exact hk hrv.1 hrv.2
    · have hev : ¬(bv &&& 1#64 ≠ 0#64) := fun h => h (hoa ▸ obj_addr_and1_zero howf)
      simp only [hev, ↓reduceIte]
      refine ⟨o, ho, hoa, howf, ?_⟩
      have htag_eq : BitVec.ofNat 64 o.tag <<< 1 ||| 1#64 = BitVec.ofNat 64 (2 * c + 1) := by
        rw [hotag, bv64_tagged_ofNat64]
        simp [BitVec.toNat_ofNat]
      rw [htag_eq]
      have hrv := retValRep_small_nat hrt hsafe (objs := σ.objs)
      exact hk hrv.1 hrv.2
  | str _ | arr _ | barr _ | int _ | clo _ _ _ => simp [PVal.tag?] at htag

private theorem baGet_word_eq (bs : List UInt8) {idx : Nat} (hi : idx < 2 ^ 63) :
    BitVec.setWidth 8 (baGetVal bs (BitVec.ofNat 64 (2 * idx + 1)) 0#64) =
      BitVec.ofNat 8 (bs.getD idx 0).toNat := by
  dsimp only [baGetVal]
  rw [ite_eq_right (by decide), ite_eq_left (boxNat_and1_ne_zero idx), boxNat_rshift1_toNat hi]
  by_cases h : idx < bs.length
  · rw [dite_eq_left h, List.getD, List.getElem?_eq_getElem h, Option.getD_some]
    apply BitVec.eq_of_toNat_eq
    simp
  · rw [dite_eq_right h, List.getD, List.getElem?_eq_none (Nat.le_of_not_lt h),
      Option.getD_none, UInt8.toNat_zero]
    rfl

private theorem primByteArrayReadOnly_sim {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hvar : ∀ v ∈ rf.ctx.vars, VarInv v rf σ.objs)
    {name op : String} {as : List LcArg} {pvs : List PVal} {ws : List Word} {retTy : LcTy}
    (hsp : splitDot name = ["ByteArray", op])
    (hop : op = "size" ∨ op = "usize" ∨ op = "get!" ∨ op = "get" ∨ op = "propagateMark")
    (hwf : perceusPrimWf name as.length = true)
    (hretwf : perceusPrimRetWf name retTy = true)
    (has_all : as.all (argNonScFlag rf.ctx) = true)
    (hlive : ∀ a ∈ as, a = .erased ∨ ∃ z v, a = .var z ∧ rf.ctx.get? z = some v ∧ v.isLive = true)
    (hpvs : rf.envP.evalArgs as = some pvs) (hws : rf.envH.evalArgsOwn as = some ws)
    (hsafe : primResSafe name pvs) {pv_res : PVal} (hprim : primP name pvs = some pv_res)
    (hpm : (name == "Array.propagateMark" || name == "ByteArray.propagateMark" ||
        name == "String.propagateMark") = true →
      retTy = LcTy.tobject ∨
        ∃ y vy, as.getLast? = some (LcArg.var y) ∧ rf.ctx.get? y = some vy ∧ vy.ty = LcTy.object)
    {K : HPost} {X : HXPost}
    (hk : ∀ {rw : Word}, ValRep retTy pv_res rw σ.objs →
      (if name == "Array.get!InternalBorrowed" then
         ∃ o_src bv, as[2]? = some (LcArg.var o_src) ∧ rw = Word.i64 bv ∧
           ∃ arrObj pv_arr w_arr, rf.envH o_src = some (pv_arr, w_arr) ∧
             w_arr = Word.i64 arrObj.addr ∧ arrObj ∈ σ.objs ∧
             (bv &&& 1#64 = 0#64 → bv ∈ arrObj.childFields)
       else if (name == "Array.propagateMark" || name == "ByteArray.propagateMark" ||
           name == "String.propagateMark") = true then ws.getLast? = some rw
       else (¬retTy.isScalar → ∃ bv, rw = Word.i64 bv ∧ bv &&& 1#64 ≠ 0#64)) →
      K rw σ)
    (hk_plain : ∀ {s_eq : List String}, splitDot name = s_eq →
      s_eq ≠ ["Array", "get!InternalBorrowed"] →
      s_eq ≠ ["Array", "propagateMark"] ∧ s_eq ≠ ["ByteArray", "propagateMark"] ∧
        s_eq ≠ ["String", "propagateMark"] →
      ∀ {rw : Word}, ValRep retTy pv_res rw σ.objs →
      (¬retTy.isScalar → ∃ bv, rw = Word.i64 bv ∧ bv &&& 1#64 ≠ 0#64) → K rw σ) :
    HPrim.wp rt name ws K X σ := by
  rcases hop with rfl | rfl | rfl | rfl | rfl
  · have hlen : as.length = 1 := by
      have := hwf; rw [perceusPrimWf, hsp] at this; rcases as with _ | ⟨_, _ | _⟩ <;> simp at this ⊢
    rcases as with _ | ⟨a0, _ | _⟩ <;> simp at hlen
    obtain ⟨p0, w0, rfl, rfl, h0p, h0h⟩ := evalArgs_len_one hpvs hws
    cases p0 with
    | barr bs =>
      simp only [primP, hsp, primByteArrayP, Option.some.injEq] at hprim; subst hprim
      rcases argNonSc_info_of hvar ((List.all_eq_true.mp has_all) a0 (by simp))
          (hlive a0 (by simp)) h0p h0h with ⟨_, hc, _, _⟩ | ⟨z, vz, _, _, hns, _, hrep⟩
      · cases hc
      · unfold ValRep at hrep
        simp only [Bool.eq_false_iff.mpr hns, Bool.false_eq_true, ↓reduceIte] at hrep
        rcases hrep with ⟨ba, rfl, hobj, _, _⟩
        rw [ObjRep.eq_7] at hobj
        rcases hobj with ⟨baObj, hba, haddr, _, hcan, hsc⟩
        have hlen_ba : baObj.arrSize = bs.length := hsc ▸ hcan.2.2.2.2.2.2.1
        have hlt63 : bs.length < 2 ^ 63 := by
          have := hcan.2.2.2.2.2.2.2.1; have := hcan.2.2.2.2.2.2.2.2
          simp only [baMaxCap] at *; omega
        have htag : BitVec.ofNat 64 baObj.arrSize <<< 1 ||| 1#64 =
            BitVec.ofNat 64 (2 * bs.length + 1) := by
          rw [bv64_tagged_ofNat64, hlen_ba]; simp [BitVec.toNat_ofNat]
        simp only [HPrim.wp, hsp, HByteArrayPrimWp, Word.toBV64?, Word.i64]
        refine ⟨baObj, hba, haddr, hcan, ?_⟩
        rw [htag]
        have hrt : (retTy == LcTy.tobject || retTy == LcTy.tagged) = true := by
          simpa [perceusPrimRetWf, hsp] using hretwf
        have hrv := retValRep_small_nat hrt hlt63 (objs := σ.objs)
        exact hk_plain hsp (by decide) ⟨by decide, by decide, by decide⟩ hrv.1 hrv.2
    | erased | nat _ | bits _ _ | str _ | ctor _ _ _ | arr _ | int _ | clo _ _ _ =>
      simp only [primP, hsp] at hprim; change none = some pv_res at hprim; cases hprim
  · have hlen : as.length = 1 := by
      have := hwf; rw [perceusPrimWf, hsp] at this; rcases as with _ | ⟨_, _ | _⟩ <;> simp at this ⊢
    rcases as with _ | ⟨a0, _ | _⟩ <;> simp at hlen
    obtain ⟨p0, w0, rfl, rfl, h0p, h0h⟩ := evalArgs_len_one hpvs hws
    cases p0 with
    | barr bs =>
      simp only [primP, hsp, primByteArrayP, Option.some.injEq] at hprim; subst hprim
      rcases argNonSc_info_of hvar ((List.all_eq_true.mp has_all) a0 (by simp))
          (hlive a0 (by simp)) h0p h0h with ⟨_, hc, _, _⟩ | ⟨z, vz, _, _, hns, _, hrep⟩
      · cases hc
      · unfold ValRep at hrep
        simp only [Bool.eq_false_iff.mpr hns, Bool.false_eq_true, ↓reduceIte] at hrep
        rcases hrep with ⟨ba, rfl, hobj, _, _⟩
        rw [ObjRep.eq_7] at hobj
        rcases hobj with ⟨baObj, hba, haddr, _, hcan, hsc⟩
        have hlen_ba : baObj.arrSize = bs.length := hsc ▸ hcan.2.2.2.2.2.2.1
        simp only [HPrim.wp, hsp, HByteArrayPrimWp, Word.toBV64?, Word.i64]
        refine ⟨baObj, hba, haddr, hcan, ?_⟩
        rw [hlen_ba]
        have hrt_sc : retTy.isScalar = true ∧ retTy.width = 64 := by
          have := hretwf; simp only [perceusPrimRetWf, hsp, Bool.or_eq_true, lcTy_beq_iff] at this
          rcases this with rfl | rfl <;> exact ⟨rfl, rfl⟩
        have hrv := retValRep_bits hrt_sc (BitVec.ofNat 64 bs.length) σ.objs
        exact hk_plain hsp (by decide) ⟨by decide, by decide, by decide⟩ hrv.1 hrv.2
    | erased | nat _ | bits _ _ | str _ | ctor _ _ _ | arr _ | int _ | clo _ _ _ =>
      simp only [primP, hsp] at hprim; change none = some pv_res at hprim; cases hprim
  · have hlen : as.length = 2 := by
      have := hwf; rw [perceusPrimWf, hsp] at this
      rcases as with _ | ⟨_, _ | ⟨_, _ | _⟩⟩ <;> simp at this ⊢
    rcases as with _ | ⟨a0, _ | ⟨a1, _ | _⟩⟩ <;> simp at hlen
    obtain ⟨p0, p1, w0, w1, rfl, rfl, h0p, h1p, h0h, h1h⟩ := evalArgs_len_two hpvs hws
    cases p0 with
    | barr bs =>
      cases p1 with
      | nat idx =>
        simp only [primP, hsp, primByteArrayP, Option.some.injEq] at hprim; subst hprim
        simp only [primResSafe, hsp] at hsafe
        rcases argNonSc_info_of hvar ((List.all_eq_true.mp has_all) a0 (by simp))
            (hlive a0 (by simp)) h0p h0h with ⟨_, hc, _, _⟩ | ⟨z, vz, _, _, hns0, _, hrep0⟩
        · cases hc
        · obtain ⟨ty1, hns1, hrep1⟩ := argNonSc_rep_of hvar
            ((List.all_eq_true.mp has_all) a1 (by simp)) (hlive a1 (by simp)) h1p h1h
          rw [valRep_nat_small_word hns1 hsafe hrep1]
          unfold ValRep at hrep0
          simp only [Bool.eq_false_iff.mpr hns0, Bool.false_eq_true, ↓reduceIte] at hrep0
          rcases hrep0 with ⟨ba, rfl, hobj, _, _⟩
          rw [ObjRep.eq_7] at hobj
          rcases hobj with ⟨baObj, hba, haddr, _, hcan, hsc⟩
          simp only [HPrim.wp, hsp, HByteArrayPrimWp, Word.toBV64?, Word.i64]
          refine ⟨baObj, hba, haddr, hcan, ?_⟩
          rw [hsc, baGet_word_eq bs hsafe]
          have hrt : retTy = LcTy.uint8 := by
            have := hretwf; simp only [perceusPrimRetWf, hsp, lcTy_beq_iff] at this; exact this
          subst hrt
          have hrv := retValRep_bits (retTy := .uint8) (w := 8) ⟨rfl, rfl⟩
            (BitVec.ofNat 8 (bs.getD idx 0).toNat) σ.objs
          exact hk_plain hsp (by decide) ⟨by decide, by decide, by decide⟩ hrv.1 hrv.2
      | erased | bits _ _ | str _ | ctor _ _ _ | arr _ | barr _ | int _ | clo _ _ _ =>
        simp only [primP, hsp] at hprim; change none = some pv_res at hprim; cases hprim
    | erased | nat _ | bits _ _ | str _ | ctor _ _ _ | arr _ | int _ | clo _ _ _ =>
      simp only [primP, hsp] at hprim; change none = some pv_res at hprim; cases hprim
  · have hlen : as.length = 3 := by
      have := hwf; rw [perceusPrimWf, hsp] at this
      rcases as with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | _⟩⟩⟩ <;> simp at this ⊢
    rcases as with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | _⟩⟩⟩ <;> simp at hlen
    obtain ⟨p0, p1, p2, w0, w1, w2, rfl, rfl, h0p, h1p, _, h0h, h1h, _⟩ :=
      evalArgs_len_three hpvs hws
    cases p0 with
    | barr bs =>
      cases p1 with
      | nat idx =>
        simp only [primP, hsp, primByteArrayP, Option.some.injEq] at hprim; subst hprim
        simp only [primResSafe, hsp] at hsafe
        rcases argNonSc_info_of hvar ((List.all_eq_true.mp has_all) a0 (by simp))
            (hlive a0 (by simp)) h0p h0h with ⟨_, hc, _, _⟩ | ⟨z, vz, _, _, hns0, _, hrep0⟩
        · cases hc
        · obtain ⟨ty1, hns1, hrep1⟩ := argNonSc_rep_of hvar
            ((List.all_eq_true.mp has_all) a1 (by simp)) (hlive a1 (by simp)) h1p h1h
          rw [valRep_nat_small_word hns1 hsafe hrep1]
          unfold ValRep at hrep0
          simp only [Bool.eq_false_iff.mpr hns0, Bool.false_eq_true, ↓reduceIte] at hrep0
          rcases hrep0 with ⟨ba, rfl, hobj, _, _⟩
          rw [ObjRep.eq_7] at hobj
          rcases hobj with ⟨baObj, hba, haddr, _, hcan, hsc⟩
          simp only [HPrim.wp, hsp, HByteArrayPrimWp, Word.toBV64?, Word.i64]
          refine ⟨baObj, hba, haddr, hcan, ?_⟩
          rw [hsc, baGet_word_eq bs hsafe]
          have hrt : retTy = LcTy.uint8 := by
            have := hretwf; simp only [perceusPrimRetWf, hsp, lcTy_beq_iff] at this; exact this
          subst hrt
          have hrv := retValRep_bits (retTy := .uint8) (w := 8) ⟨rfl, rfl⟩
            (BitVec.ofNat 8 (bs.getD idx 0).toNat) σ.objs
          exact hk_plain hsp (by decide) ⟨by decide, by decide, by decide⟩ hrv.1 hrv.2
      | erased | bits _ _ | str _ | ctor _ _ _ | arr _ | barr _ | int _ | clo _ _ _ =>
        simp only [primP, hsp] at hprim; change none = some pv_res at hprim; cases hprim
    | erased | nat _ | bits _ _ | str _ | ctor _ _ _ | arr _ | int _ | clo _ _ _ =>
      simp only [primP, hsp] at hprim; change none = some pv_res at hprim; cases hprim
  · have hlen : as.length = 2 := by
      have := hwf; rw [perceusPrimWf, hsp] at this
      rcases as with _ | ⟨_, _ | ⟨_, _ | _⟩⟩ <;> simp at this ⊢
    rcases as with _ | ⟨a0, _ | ⟨a1, _ | _⟩⟩ <;> simp at hlen
    obtain ⟨p0, p1, w0, w1, rfl, rfl, _, h1p, _, h1h⟩ := evalArgs_len_two hpvs hws
    simp only [primP, hsp, primByteArrayP, Option.some.injEq] at hprim; subst hprim
    simp only [HPrim.wp, hsp, HByteArrayPrimWp]
    have hrt_rc : retTy.needsRc = true := by simpa [perceusPrimRetWf, hsp] using hretwf
    have hname : name = "ByteArray.propagateMark" := splitDot_inj (hsp.trans (by decide))
    have hrep_r := propagateMark_valRep hvar (aLast := a1) rfl
      ((List.all_eq_true.mp has_all) a1 (by simp)) (hlive a1 (by simp)) h1p h1h hrt_rc
      (hpm (by simp [hname]))
    exact ⟨valRep_needsRc_word_ty hrt_rc hrep_r, hk hrep_r (by simp [hname])⟩

private theorem primStringReadOnly_sim {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hvar : ∀ v ∈ rf.ctx.vars, VarInv v rf σ.objs)
    {name : String} {rest : List String} {as : List LcArg}
    {pvs : List PVal} {ws : List Word} {retTy : LcTy}
    (hsp : splitDot name = "String" :: rest)
    (hrest : rest = ["length"] ∨ rest = ["Internal", "length"] ∨
      rest = ["utf8ByteSize"] ∨ rest = ["propagateMark"])
    (hwf : perceusPrimWf name as.length = true)
    (hretwf : perceusPrimRetWf name retTy = true)
    (has_all : as.all (argNonScFlag rf.ctx) = true)
    (hlive : ∀ a ∈ as, a = .erased ∨ ∃ z v, a = .var z ∧ rf.ctx.get? z = some v ∧ v.isLive = true)
    (hpvs : rf.envP.evalArgs as = some pvs) (hws : rf.envH.evalArgsOwn as = some ws)
    (hsafe : primResSafe name pvs) {pv_res : PVal} (hprim : primP name pvs = some pv_res)
    (hpm : (name == "Array.propagateMark" || name == "ByteArray.propagateMark" ||
        name == "String.propagateMark") = true →
      retTy = LcTy.tobject ∨
        ∃ y vy, as.getLast? = some (LcArg.var y) ∧ rf.ctx.get? y = some vy ∧ vy.ty = LcTy.object)
    {K : HPost} {X : HXPost}
    (hk : ∀ {rw : Word}, ValRep retTy pv_res rw σ.objs →
      (if name == "Array.get!InternalBorrowed" then
         ∃ o_src bv, as[2]? = some (LcArg.var o_src) ∧ rw = Word.i64 bv ∧
           ∃ arrObj pv_arr w_arr, rf.envH o_src = some (pv_arr, w_arr) ∧
             w_arr = Word.i64 arrObj.addr ∧ arrObj ∈ σ.objs ∧
             (bv &&& 1#64 = 0#64 → bv ∈ arrObj.childFields)
       else if (name == "Array.propagateMark" || name == "ByteArray.propagateMark" ||
           name == "String.propagateMark") = true then ws.getLast? = some rw
       else (¬retTy.isScalar → ∃ bv, rw = Word.i64 bv ∧ bv &&& 1#64 ≠ 0#64)) →
      K rw σ)
    (hk_plain : ∀ {s_eq : List String}, splitDot name = s_eq →
      s_eq ≠ ["Array", "get!InternalBorrowed"] →
      s_eq ≠ ["Array", "propagateMark"] ∧ s_eq ≠ ["ByteArray", "propagateMark"] ∧
        s_eq ≠ ["String", "propagateMark"] →
      ∀ {rw : Word}, ValRep retTy pv_res rw σ.objs →
      (¬retTy.isScalar → ∃ bv, rw = Word.i64 bv ∧ bv &&& 1#64 ≠ 0#64) → K rw σ) :
    HPrim.wp rt name ws K X σ := by
  rcases hrest with rfl | rfl | rfl | rfl
  · have hlen : as.length = 1 := by
      have := hwf; rw [perceusPrimWf, hsp] at this; rcases as with _ | ⟨_, _ | _⟩ <;> simp at this ⊢
    rcases as with _ | ⟨a0, _ | _⟩ <;> simp at hlen
    obtain ⟨p0, w0, rfl, rfl, h0p, h0h⟩ := evalArgs_len_one hpvs hws
    cases p0 with
    | str s =>
      have hp' : primP name [PVal.str s] = some (PVal.nat s.length) := by
        simp only [primP, hsp]; rfl
      rw [hp', Option.some.injEq] at hprim; subst hprim
      simp only [primResSafe, hsp] at hsafe
      rcases argNonSc_info_of hvar ((List.all_eq_true.mp has_all) a0 (by simp))
          (hlive a0 (by simp)) h0p h0h with ⟨_, hc, _, _⟩ | ⟨z, vz, _, _, hns, _, hrep⟩
      · cases hc
      · unfold ValRep at hrep
        simp only [Bool.eq_false_iff.mpr hns, Bool.false_eq_true, ↓reduceIte] at hrep
        rcases hrep with ⟨sp, rfl, hobj, _, _⟩
        rw [ObjRep.eq_5] at hobj
        rcases hobj with ⟨sObj, hs_m, haddr, _, hcan, _, hsl⟩
        have htag : BitVec.ofNat 64 sObj.strLen <<< 1 ||| 1#64 =
            BitVec.ofNat 64 (2 * s.length + 1) := by
          rw [bv64_tagged_ofNat64, hsl]; simp [BitVec.toNat_ofNat]
        simp only [HPrim.wp, hsp, HStringPrimWp, Word.toBV64?, Word.i64]
        refine ⟨sObj, hs_m, haddr, hcan, ?_⟩
        rw [htag]
        have hrt : (retTy == LcTy.tobject || retTy == LcTy.tagged) = true := by
          simpa [perceusPrimRetWf, hsp] using hretwf
        have hrv := retValRep_small_nat hrt hsafe (objs := σ.objs)
        exact hk_plain hsp (by decide) ⟨by decide, by decide, by decide⟩ hrv.1 hrv.2
    | erased | nat _ | bits _ _ | ctor _ _ _ | arr _ | barr _ | int _ | clo _ _ _ =>
      simp only [primP, hsp] at hprim; change none = some pv_res at hprim; cases hprim
  · have hlen : as.length = 1 := by
      have := hwf; rw [perceusPrimWf, hsp] at this; rcases as with _ | ⟨_, _ | _⟩ <;> simp at this ⊢
    rcases as with _ | ⟨a0, _ | _⟩ <;> simp at hlen
    obtain ⟨p0, w0, rfl, rfl, h0p, h0h⟩ := evalArgs_len_one hpvs hws
    cases p0 with
    | str s =>
      have hp' : primP name [PVal.str s] = some (PVal.nat s.length) := by
        simp only [primP, hsp]; rfl
      rw [hp', Option.some.injEq] at hprim; subst hprim
      simp only [primResSafe, hsp] at hsafe
      rcases argNonSc_info_of hvar ((List.all_eq_true.mp has_all) a0 (by simp))
          (hlive a0 (by simp)) h0p h0h with ⟨_, hc, _, _⟩ | ⟨z, vz, _, _, hns, _, hrep⟩
      · cases hc
      · unfold ValRep at hrep
        simp only [Bool.eq_false_iff.mpr hns, Bool.false_eq_true, ↓reduceIte] at hrep
        rcases hrep with ⟨sp, rfl, hobj, _, _⟩
        rw [ObjRep.eq_5] at hobj
        rcases hobj with ⟨sObj, hs_m, haddr, _, hcan, _, hsl⟩
        have htag : BitVec.ofNat 64 sObj.strLen <<< 1 ||| 1#64 =
            BitVec.ofNat 64 (2 * s.length + 1) := by
          rw [bv64_tagged_ofNat64, hsl]; simp [BitVec.toNat_ofNat]
        simp only [HPrim.wp, hsp, HStringPrimWp, Word.toBV64?, Word.i64]
        refine ⟨sObj, hs_m, haddr, hcan, ?_⟩
        rw [htag]
        have hrt : (retTy == LcTy.tobject || retTy == LcTy.tagged) = true := by
          simpa [perceusPrimRetWf, hsp] using hretwf
        have hrv := retValRep_small_nat hrt hsafe (objs := σ.objs)
        exact hk_plain hsp (by decide) ⟨by decide, by decide, by decide⟩ hrv.1 hrv.2
    | erased | nat _ | bits _ _ | ctor _ _ _ | arr _ | barr _ | int _ | clo _ _ _ =>
      simp only [primP, hsp] at hprim; change none = some pv_res at hprim; cases hprim
  · have hlen : as.length = 1 := by
      have := hwf; rw [perceusPrimWf, hsp] at this; rcases as with _ | ⟨_, _ | _⟩ <;> simp at this ⊢
    rcases as with _ | ⟨a0, _ | _⟩ <;> simp at hlen
    obtain ⟨p0, w0, rfl, rfl, h0p, h0h⟩ := evalArgs_len_one hpvs hws
    cases p0 with
    | str s =>
      have hp' : primP name [PVal.str s] = some (PVal.nat s.utf8ByteSize) := by
        simp only [primP, hsp]; rfl
      rw [hp', Option.some.injEq] at hprim; subst hprim
      simp only [primResSafe, hsp] at hsafe
      rcases argNonSc_info_of hvar ((List.all_eq_true.mp has_all) a0 (by simp))
          (hlive a0 (by simp)) h0p h0h with ⟨_, hc, _, _⟩ | ⟨z, vz, _, _, hns, _, hrep⟩
      · cases hc
      · unfold ValRep at hrep
        simp only [Bool.eq_false_iff.mpr hns, Bool.false_eq_true, ↓reduceIte] at hrep
        rcases hrep with ⟨sp, rfl, hobj, _, _⟩
        rw [ObjRep.eq_5] at hobj
        rcases hobj with ⟨sObj, hs_m, haddr, _, hcan, hpay, _⟩
        have hsz : sObj.arrSize - 1 = s.utf8ByteSize := by
          have h1 : (strPayload sObj).length = sObj.arrSize - 1 := by
            simp [strPayload, List.length_dropLast, hcan.2.2.2.2.2.2.2.2.2.1]
          rw [← h1, hpay, string_toUTF8_toList_length]
        have htag : BitVec.ofNat 64 (sObj.arrSize - 1) <<< 1 ||| 1#64 =
            BitVec.ofNat 64 (2 * s.utf8ByteSize + 1) := by
          rw [bv64_tagged_ofNat64, hsz]; simp [BitVec.toNat_ofNat]
        simp only [HPrim.wp, hsp, HStringPrimWp, Word.toBV64?, Word.i64]
        refine ⟨sObj, hs_m, haddr, hcan, ?_⟩
        rw [htag]
        have hrt : (retTy == LcTy.tobject || retTy == LcTy.tagged) = true := by
          simpa [perceusPrimRetWf, hsp] using hretwf
        have hrv := retValRep_small_nat hrt hsafe (objs := σ.objs)
        exact hk_plain hsp (by decide) ⟨by decide, by decide, by decide⟩ hrv.1 hrv.2
    | erased | nat _ | bits _ _ | ctor _ _ _ | arr _ | barr _ | int _ | clo _ _ _ =>
      simp only [primP, hsp] at hprim; change none = some pv_res at hprim; cases hprim
  · have hlen : as.length = 2 := by
      have := hwf; rw [perceusPrimWf, hsp] at this
      rcases as with _ | ⟨_, _ | ⟨_, _ | _⟩⟩ <;> simp at this ⊢
    rcases as with _ | ⟨a0, _ | ⟨a1, _ | _⟩⟩ <;> simp at hlen
    obtain ⟨p0, p1, w0, w1, rfl, rfl, _, h1p, _, h1h⟩ := evalArgs_len_two hpvs hws
    have hp' : primP name [p0, p1] = some p1 := by simp only [primP, hsp]; rfl
    rw [hp', Option.some.injEq] at hprim; subst hprim
    simp only [HPrim.wp, hsp, HStringPrimWp]
    have hrt_rc : retTy.needsRc = true := by simpa [perceusPrimRetWf, hsp] using hretwf
    have hname : name = "String.propagateMark" := splitDot_inj (hsp.trans (by decide))
    have hrep_r := propagateMark_valRep hvar (aLast := a1) rfl
      ((List.all_eq_true.mp has_all) a1 (by simp)) (hlive a1 (by simp)) h1p h1h hrt_rc
      (hpm (by simp [hname]))
    exact ⟨valRep_needsRc_word_ty hrt_rc hrep_r, hk hrep_r (by simp [hname])⟩

theorem primReadOnly_sim {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hvar : ∀ v ∈ rf.ctx.vars, VarInv v rf σ.objs)
    (hwf_objs : ∀ o ∈ σ.objs, o.Wf)
    {name : String} {as : List LcArg} {pvs : List PVal} {ws : List Word} {retTy : LcTy}
    (hwf : perceusPrimWf name as.length = true)
    (hretwf : perceusPrimRetWf name retTy = true)
    (hargswf : perceusPrimArgsWf rf.ctx name as = true)
    (hlive : ∀ a ∈ as, a = .erased ∨ ∃ z v, a = .var z ∧ rf.ctx.get? z = some v ∧ v.isLive = true)
    (hpvs : rf.envP.evalArgs as = some pvs) (hws : rf.envH.evalArgsOwn as = some ws)
    (hsafe : primResSafe name pvs) {pv_res : PVal} (hprim : primP name pvs = some pv_res)
    (hpm : (name == "Array.propagateMark" || name == "ByteArray.propagateMark" ||
        name == "String.propagateMark") = true →
      retTy = LcTy.tobject ∨
        ∃ y vy, as.getLast? = some (LcArg.var y) ∧ rf.ctx.get? y = some vy ∧ vy.ty = LcTy.object)
    (hnot_nat_uint :
      (∀ op, splitDot name ≠ ["Nat", op]) ∧
      (∀ ty op, splitDot name = [ty, op] → uintWidth? ty = none))
    {K : HPost} {X : HXPost}
    (hk : ∀ {rw : Word}, ValRep retTy pv_res rw σ.objs →
      (if name == "Array.get!InternalBorrowed" then
         ∃ o_src bv, as[2]? = some (LcArg.var o_src) ∧ rw = Word.i64 bv ∧
           ∃ arrObj pv_arr w_arr, rf.envH o_src = some (pv_arr, w_arr) ∧
             w_arr = Word.i64 arrObj.addr ∧ arrObj ∈ σ.objs ∧
             (bv &&& 1#64 = 0#64 → bv ∈ arrObj.childFields)
       else if (name == "Array.propagateMark" || name == "ByteArray.propagateMark" ||
           name == "String.propagateMark") = true then ws.getLast? = some rw
       else (¬retTy.isScalar → ∃ bv, rw = Word.i64 bv ∧ bv &&& 1#64 ≠ 0#64)) →
      K rw σ) :
    HPrim.wp rt name ws K X σ := by
  have has_all : as.all (fun a => match a with
      | .erased => true
      | .var x => match rf.ctx.get? x with | some v => !v.ty.isScalar | none => false) = true := by
    have := hargswf; unfold perceusPrimArgsWf at this
    split at this
    · rename_i ty op a heq
      split at this
      · rename_i w hw
        exact absurd hw (by rw [hnot_nat_uint.2 ty op heq]; exact fun h => by cases h)
      · exact this
    · rename_i ty op a b heq
      split at this
      · rename_i w hw
        exact absurd hw (by rw [hnot_nat_uint.2 ty op heq]; exact fun h => by cases h)
      · exact this
    · exact this
  have hro :
      (∃ op, splitDot name = ["Array", op] ∧
        (op = "size" ∨ op = "usize" ∨ op = "get!InternalBorrowed" ∨ op = "propagateMark")) ∨
      (∃ op, splitDot name = ["ByteArray", op] ∧
        (op = "size" ∨ op = "usize" ∨ op = "get!" ∨ op = "get" ∨ op = "propagateMark")) ∨
      (∃ rest, splitDot name = "String" :: rest ∧
        (rest = ["length"] ∨ rest = ["Internal", "length"] ∨
         rest = ["utf8ByteSize"] ∨ rest = ["propagateMark"])) ∨
      splitDot name = ["System", "Platform", "getNumBits"] ∨
      splitDot name = ["getObjTagNat"] := by
    have h1 := hnot_nat_uint.1
    have h2 := hnot_nat_uint.2
    have hw := hwf; unfold perceusPrimWf at hw
    split at hw
    · rename_i op heq; exact absurd heq (h1 op)
    · rename_i op heq; rw [heq]
      split at hw <;> simp at hw
      · exact Or.inl ⟨"size", rfl, Or.inl rfl⟩
      · exact Or.inl ⟨"usize", rfl, Or.inr (Or.inl rfl)⟩
      · exact Or.inl ⟨"get!InternalBorrowed", rfl, Or.inr (Or.inr (Or.inl rfl))⟩
      · exact Or.inl ⟨"propagateMark", rfl, Or.inr (Or.inr (Or.inr rfl))⟩
    · rename_i op heq; rw [heq]
      split at hw <;> simp at hw
      · exact Or.inr (Or.inl ⟨"size", rfl, Or.inl rfl⟩)
      · exact Or.inr (Or.inl ⟨"usize", rfl, Or.inr (Or.inl rfl)⟩)
      · exact Or.inr (Or.inl ⟨"get!", rfl, Or.inr (Or.inr (Or.inl rfl))⟩)
      · exact Or.inr (Or.inl ⟨"get", rfl, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩)
      · exact Or.inr (Or.inl ⟨"propagateMark", rfl, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩)
    · rename_i rest heq; rw [heq]
      split at hw <;> simp at hw
      · exact Or.inr (Or.inr (Or.inl ⟨["length"], rfl, Or.inl rfl⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨["Internal", "length"], rfl, Or.inr (Or.inl rfl)⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨["utf8ByteSize"], rfl, Or.inr (Or.inr (Or.inl rfl))⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨["propagateMark"], rfl, Or.inr (Or.inr (Or.inr rfl))⟩))
    · rename_i heq; exact Or.inr (Or.inr (Or.inr (Or.inl heq)))
    · rename_i heq; exact Or.inr (Or.inr (Or.inr (Or.inr heq)))
    · rename_i heq; simp [primP, heq, uintWidth?] at hprim
    · have hu := h2 _ _ ‹_›; rw [hu] at hw; cases hw
    · cases hw
  have hk_plain : ∀ {s_eq : List String} (hsp : splitDot name = s_eq)
      (hnp : s_eq ≠ ["Array", "get!InternalBorrowed"])
      (hnpm : s_eq ≠ ["Array", "propagateMark"] ∧ s_eq ≠ ["ByteArray", "propagateMark"] ∧
        s_eq ≠ ["String", "propagateMark"])
      {rw : Word}, ValRep retTy pv_res rw σ.objs →
      (¬retTy.isScalar → ∃ bv, rw = Word.i64 bv ∧ bv &&& 1#64 ≠ 0#64) → K rw σ := by
    intro s_eq hsp hnp hnpm rw hr hodd
    have h1 : (name == "Array.get!InternalBorrowed") = false := beq_false_of_ne fun h => by
      have : splitDot name = splitDot "Array.get!InternalBorrowed" := by rw [h]
      rw [hsp] at this; exact hnp (by simpa [splitDot, splitDot.go] using this)
    have h2 : (name == "Array.propagateMark" || name == "ByteArray.propagateMark" ||
        name == "String.propagateMark") = false := by
      rw [Bool.eq_false_iff]; intro hm
      simp only [Bool.or_eq_true, beq_iff_eq] at hm
      rcases hm with (rfl | rfl) | rfl
      · exact hnpm.1 (by simpa [splitDot, splitDot.go] using hsp.symm)
      · exact hnpm.2.1 (by simpa [splitDot, splitDot.go] using hsp.symm)
      · exact hnpm.2.2 (by simpa [splitDot, splitDot.go] using hsp.symm)
    exact hk hr (by
      simp only [h1, h2]
      exact fun hs => hodd hs)
  rcases hro with ⟨op, hsp, hop⟩ | ⟨op, hsp, hop⟩ | ⟨rest, hsp, hrest⟩ | hsp | hsp
  · rcases hop with rfl | rfl | rfl | rfl
    · have hlen : as.length = 2 := by
        have := hwf; rw [perceusPrimWf, hsp] at this
        rcases as with _ | ⟨_, _ | ⟨_, _ | _⟩⟩ <;> simp at this ⊢
      rcases as with _ | ⟨a0, _ | ⟨a1, _ | _⟩⟩ <;> simp at hlen
      obtain ⟨p0, p1, w0, w1, rfl, rfl, _, h1p, _, h1h⟩ := evalArgs_len_two hpvs hws
      cases p1 with
      | arr xs =>
        simp only [primP, hsp, primArrayP, Option.some.injEq] at hprim; subst hprim
        rcases argNonSc_info_of hvar ((List.all_eq_true.mp has_all) a1 (by simp))
            (hlive a1 (by simp)) h1p h1h with ⟨_, hc, _, _⟩ | ⟨z, vz, _, _, hns, _, hrep⟩
        · cases hc
        · unfold ValRep at hrep
          simp only [Bool.eq_false_iff.mpr hns, Bool.false_eq_true, ↓reduceIte] at hrep
          rcases hrep with ⟨arr, rfl, hobj, _, _⟩
          rw [ObjRep.eq_6] at hobj
          rcases hobj with ⟨arrObj, harr, haddr, _, hcan, hfrep⟩
          have hfl := objFieldsRep_length hfrep
          have hlt63 : xs.length < 2 ^ 63 := by
            have := hcan.2.2.2.2.2.2.1; have := hcan.2.2.2.2.2.2.2
            simp only [arrMaxCap] at *; omega
          have htag : BitVec.ofNat 64 arrObj.fields.length <<< 1 ||| 1#64 =
              BitVec.ofNat 64 (2 * xs.length + 1) := by
            rw [bv64_tagged_ofNat64, hfl]; simp [BitVec.toNat_ofNat]
          simp only [HPrim.wp, hsp, HArrayPrimWp, Word.toBV64?, Word.i64]
          refine ⟨arrObj, harr, haddr, hcan, ?_⟩
          rw [htag]
          have hrt : (retTy == LcTy.tobject || retTy == LcTy.tagged) = true := by
            simpa [perceusPrimRetWf, hsp] using hretwf
          have hrv := retValRep_small_nat hrt hlt63 (objs := σ.objs)
          exact hk_plain hsp (by decide) ⟨by decide, by decide, by decide⟩ hrv.1 hrv.2
      | erased | nat _ | bits _ _ | str _ | ctor _ _ _ | barr _ | int _ | clo _ _ _ =>
        simp [primP, hsp, primArrayP] at hprim
    · have hlen : as.length = 2 := by
        have := hwf; rw [perceusPrimWf, hsp] at this
        rcases as with _ | ⟨_, _ | ⟨_, _ | _⟩⟩ <;> simp at this ⊢
      rcases as with _ | ⟨a0, _ | ⟨a1, _ | _⟩⟩ <;> simp at hlen
      obtain ⟨p0, p1, w0, w1, rfl, rfl, _, h1p, _, h1h⟩ := evalArgs_len_two hpvs hws
      cases p1 with
      | arr xs =>
        simp only [primP, hsp, primArrayP, Option.some.injEq] at hprim; subst hprim
        rcases argNonSc_info_of hvar ((List.all_eq_true.mp has_all) a1 (by simp))
            (hlive a1 (by simp)) h1p h1h with ⟨_, hc, _, _⟩ | ⟨z, vz, _, _, hns, _, hrep⟩
        · cases hc
        · unfold ValRep at hrep
          simp only [Bool.eq_false_iff.mpr hns, Bool.false_eq_true, ↓reduceIte] at hrep
          rcases hrep with ⟨arr, rfl, hobj, _, _⟩
          rw [ObjRep.eq_6] at hobj
          rcases hobj with ⟨arrObj, harr, haddr, _, hcan, hfrep⟩
          have hfl := objFieldsRep_length hfrep
          simp only [HPrim.wp, hsp, HArrayPrimWp, Word.toBV64?, Word.i64]
          refine ⟨arrObj, harr, haddr, hcan, ?_⟩
          rw [← hfl]
          have hrt_sc : retTy.isScalar = true ∧ retTy.width = 64 := by
            have := hretwf; simp only [perceusPrimRetWf, hsp, Bool.or_eq_true, lcTy_beq_iff] at this
            rcases this with rfl | rfl <;> exact ⟨rfl, rfl⟩
          have hrv := retValRep_bits hrt_sc (BitVec.ofNat 64 xs.length) σ.objs
          exact hk_plain hsp (by decide) ⟨by decide, by decide, by decide⟩ hrv.1 hrv.2
      | erased | nat _ | bits _ _ | str _ | ctor _ _ _ | barr _ | int _ | clo _ _ _ =>
        simp [primP, hsp, primArrayP] at hprim
    · have hlen : as.length = 4 := by
        have := hwf; rw [perceusPrimWf, hsp] at this
        rcases as with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | _⟩⟩⟩⟩ <;> simp at this ⊢
      rcases as with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | _⟩⟩⟩⟩ <;> simp at hlen
      obtain ⟨p0, pdv, p2, p3, w0, wdv, w2, w3, rfl, rfl, _, h1p, h2p, h3p, _, h1h, h2h, h3h⟩ :=
        evalArgs_len_four hpvs hws
      cases p2 with
      | arr xs =>
        cases p3 with
        | nat idx =>
          simp only [primP, hsp, primArrayP, Option.some.injEq] at hprim; subst hprim
          simp only [primResSafe, hsp] at hsafe
          rcases argNonSc_info_of hvar ((List.all_eq_true.mp has_all) a2 (by simp))
              (hlive a2 (by simp)) h2p h2h with ⟨_, hc, _, _⟩ | ⟨z, vz, rfl, _, hns2, henh2, hrep2⟩
          · cases hc
          · obtain ⟨ty3, hns3, hrep3⟩ := argNonSc_rep_of hvar
              ((List.all_eq_true.mp has_all) a3 (by simp)) (hlive a3 (by simp)) h3p h3h
            rw [valRep_nat_small_word hns3 hsafe.1 hrep3]
            unfold ValRep at hrep2
            simp only [Bool.eq_false_iff.mpr hns2, Bool.false_eq_true, ↓reduceIte] at hrep2
            rcases hrep2 with ⟨arr, rfl, hobj, _, _⟩
            rw [ObjRep.eq_6] at hobj
            rcases hobj with ⟨arrObj, harr, haddr, _, hcan, hfrep⟩
            have hfl := objFieldsRep_length hfrep
            have hidx_f : idx < arrObj.fields.length := by omega
            have hodd := boxNat_and1_ne_zero idx
            have hrs := boxNat_rshift1_toNat hsafe.1
            obtain ⟨ty1, hns1, hrep1⟩ := argNonSc_rep_of hvar
              ((List.all_eq_true.mp has_all) a1 (by simp)) (hlive a1 (by simp)) h1p h1h
            unfold ValRep at hrep1
            simp only [Bool.eq_false_iff.mpr hns1, Bool.false_eq_true, ↓reduceIte] at hrep1
            rcases hrep1 with ⟨bvd, rfl, _⟩
            simp only [HPrim.wp, hsp, HArrayPrimWp, Word.toBV64?, Word.i64]
            refine ⟨arrObj, harr, haddr, hcan, hwf_objs, ?_⟩
            rw [ite_eq_left hodd, hrs, dite_eq_left hidx_f]
            have hrt : retTy = LcTy.tobject := by
              have := hretwf; simp only [perceusPrimRetWf, hsp, lcTy_beq_iff] at this; exact this
            subst hrt
            have hgetd : xs.getD idx pdv = xs[idx] := by
              simp [List.getD, List.getElem?_eq_getElem hsafe.2]
            rw [hgetd] at hk
            have hrep_res : ValRep LcTy.tobject xs[idx] (Word.i64 arrObj.fields[idx]) σ.objs := by
              unfold ValRep; simp only [LcTy.isScalar, Bool.false_eq_true, ↓reduceIte]
              exact ⟨arrObj.fields[idx], rfl, objFieldsRep_getElem hfrep hsafe.2 hidx_f,
                (fun h => by cases h), (fun h => by cases h)⟩
            have hch : arrObj.fields[idx] ∈ arrObj.childFields := by
              simp only [LcnfObj.childFields, hcan.2.2.2.2.2.1, or_true, ↓reduceIte]
              exact List.getElem_mem hidx_f
            have hname : name = "Array.get!InternalBorrowed" :=
              splitDot_inj (hsp.trans (by decide))
            exact hk hrep_res (by
              simp only [hname, beq_self_eq_true, ↓reduceIte]
              exact ⟨z, arrObj.fields[idx], rfl, rfl, arrObj, vz.ty, Word.i64 arr,
                henh2, congrArg Word.i64 haddr.symm, harr, fun _ => hch⟩)
        | erased | bits _ _ | str _ | ctor _ _ _ | arr _ | barr _ | int _ | clo _ _ _ =>
          simp [primP, hsp, primArrayP] at hprim
      | erased | nat _ | bits _ _ | str _ | ctor _ _ _ | barr _ | int _ | clo _ _ _ =>
        simp [primP, hsp, primArrayP] at hprim
    · have hlen : as.length = 4 := by
        have := hwf; rw [perceusPrimWf, hsp] at this
        rcases as with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | _⟩⟩⟩⟩ <;> simp at this ⊢
      rcases as with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | _⟩⟩⟩⟩ <;> simp at hlen
      obtain ⟨p0, p1, p2, p3, w0, w1, w2, w3, rfl, rfl, _, _, _, h3p, _, _, _, h3h⟩ :=
        evalArgs_len_four hpvs hws
      simp only [primP, hsp, primArrayP, Option.some.injEq] at hprim; subst hprim
      simp only [HPrim.wp, hsp, HArrayPrimWp]
      have hrt_rc : retTy.needsRc = true := by simpa [perceusPrimRetWf, hsp] using hretwf
      have hname : name = "Array.propagateMark" := splitDot_inj (hsp.trans (by decide))
      have hrep_r := propagateMark_valRep hvar (aLast := a3) rfl
        ((List.all_eq_true.mp has_all) a3 (by simp)) (hlive a3 (by simp)) h3p h3h hrt_rc
        (hpm (by simp [hname]))
      exact ⟨valRep_needsRc_word_ty hrt_rc hrep_r, hk hrep_r (by simp [hname])⟩
  · exact primByteArrayReadOnly_sim hvar hsp hop hwf hretwf has_all hlive hpvs hws hsafe hprim hpm
      hk hk_plain
  · exact primStringReadOnly_sim hvar hsp hrest hwf hretwf has_all hlive hpvs hws hsafe hprim hpm
      hk hk_plain
  · have hlen : as.length = 0 := by
      have := hwf; rw [perceusPrimWf, hsp] at this; rcases as with _ | _ <;> simp at this ⊢
    rcases as with _ | _ <;> simp at hlen
    simp only [PValEnv.evalArgs, Option.some.injEq] at hpvs; subst hpvs
    simp only [HValEnv.evalArgsOwn, Option.some.injEq] at hws; subst hws
    simp only [primP, hsp, Option.some.injEq] at hprim; subst hprim
    simp only [HPrim.wp, hsp]
    have hrt : (retTy == LcTy.tobject || retTy == LcTy.tagged) = true := by
      simpa [perceusPrimRetWf, hsp] using hretwf
    have hrv := retValRep_small_nat hrt (show 64 < 2 ^ 63 by decide) (objs := σ.objs)
    exact hk_plain hsp (by decide) ⟨by decide, by decide, by decide⟩ hrv.1 hrv.2
  · have hlen12 : as.length = 1 ∨ as.length = 2 := by
      have := hwf; rw [perceusPrimWf, hsp] at this
      rcases as with _ | ⟨_, _ | ⟨_, _ | _⟩⟩ <;> simp at this ⊢
    have hrt : (retTy == LcTy.tobject || retTy == LcTy.tagged) = true := by
      simpa [perceusPrimRetWf, hsp] using hretwf
    rcases hlen12 with hlen | hlen
    · rcases as with _ | ⟨a0, _ | _⟩ <;> simp at hlen
      obtain ⟨p0, w0, rfl, rfl, h0p, h0h⟩ := evalArgs_len_one hpvs hws
      simp only [primP, hsp, Option.map_eq_some_iff] at hprim
      rcases hprim with ⟨nv, htag, rfl⟩
      simp only [primResSafe, hsp] at hsafe
      obtain ⟨ty0, hns0, hrep0⟩ := argNonSc_rep_of hvar
        ((List.all_eq_true.mp has_all) a0 List.mem_cons_self)
        (hlive a0 List.mem_cons_self) h0p h0h
      simp only [HPrim.wp, hsp, Option.bind_some]
      exact getObjTagNat_step hns0 hrep0 hrt hsafe htag fun hr ho =>
        hk_plain hsp (by decide) ⟨by decide, by decide, by decide⟩ hr ho
    · rcases as with _ | ⟨a0, _ | ⟨a1, _ | _⟩⟩ <;> simp at hlen
      obtain ⟨p0, p1, w0, w1, rfl, rfl, _, h1p, _, h1h⟩ := evalArgs_len_two hpvs hws
      simp only [primP, hsp, Option.map_eq_some_iff] at hprim
      rcases hprim with ⟨nv, htag, rfl⟩
      simp only [primResSafe, hsp] at hsafe
      obtain ⟨ty1, hns1, hrep1⟩ := argNonSc_rep_of hvar
        ((List.all_eq_true.mp has_all) a1 (by simp)) (hlive a1 (by simp)) h1p h1h
      simp only [HPrim.wp, hsp, Option.bind_some]
      exact getObjTagNat_step hns1 hrep1 hrt hsafe htag fun hr ho =>
        hk_plain hsp (by decide) ⟨by decide, by decide, by decide⟩ hr ho

theorem outOfBounds_sim {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hvar : ∀ v ∈ rf.ctx.vars, VarInv v rf σ.objs)
    {as : List LcArg} {pvs : List PVal} {ws : List Word}
    (hwf : perceusPrimWf "outOfBounds._redArg" as.length = true)
    (hargswf : perceusPrimArgsWf rf.ctx "outOfBounds._redArg" as = true)
    (hlive : ∀ a ∈ as, a = .erased ∨ ∃ z v, a = .var z ∧ rf.ctx.get? z = some v ∧ v.isLive = true)
    (_hpvs : rf.envP.evalArgs as = some pvs) (hws : rf.envH.evalArgsOwn as = some ws)
    {K : HPost} {X : HXPost} (hx : X panicOobCode σ) :
    HPrim.wp rt "outOfBounds._redArg" ws K X σ := by
  have hlen : as.length = 1 := by
    have := hwf; revert this; rcases as with _ | ⟨_, _ | _⟩ <;>
      simp [perceusPrimWf, splitDot, splitDot.go]
  rcases as with _ | ⟨a, _ | _⟩ <;> simp at hlen
  simp only [HValEnv.evalArgsOwn] at hws
  cases h1h : rf.envH.evalArgOwn a with
  | none => simp [h1h] at hws
  | some wa =>
    simp only [h1h, Option.some.injEq] at hws; subst hws
    have hbv : wa.toBV64?.isSome = true := by
      cases a with
      | erased => simp only [HValEnv.evalArgOwn] at h1h; cases h1h; rfl
      | var z =>
        cases hgz : rf.ctx.get? z with
        | none => simp [perceusPrimArgsWf, splitDot, splitDot.go, uintWidth?, hgz] at hargswf
        | some vz =>
          have hnsf : vz.ty.isScalar = false := by
            simpa [perceusPrimArgsWf, splitDot, splitDot.go, uintWidth?, hgz] using hargswf
          have hzl : vz.isLive = true := by
            rcases hlive (.var z) List.mem_cons_self with h | ⟨z', v', hq, hg', hl'⟩
            · cases h
            · cases hq; rw [hgz] at hg'; cases hg'; exact hl'
          obtain ⟨_, w', _, heh', hrep', _⟩ := hvar vz (RcCtx.get?_mem hgz).1 hzl
          rw [(RcCtx.get?_mem hgz).2] at heh'
          simp only [HValEnv.evalArgOwn, heh'] at h1h; cases h1h
          unfold ValRep at hrep'
          simp only [hnsf, Bool.false_eq_true, ↓reduceIte] at hrep'
          rcases hrep' with ⟨bv, rfl, _⟩; rfl
    have hsd : splitDot "outOfBounds._redArg" = ["outOfBounds", "_redArg"] := by decide
    simp only [HPrim.wp, hsd, hbv, ↓reduceIte]; exact hx

theorem primP_sim {rt : BitVec 64} {rf : RcFrame} {σ : HState}
    (hvar : ∀ v ∈ rf.ctx.vars, VarInv v rf σ.objs)
    (hwf_objs : ∀ o ∈ σ.objs, o.Wf)
    {name : String} {as : List LcArg} {pvs : List PVal} {ws : List Word} {retTy : LcTy}
    (hwf : perceusPrimWf name as.length = true)
    (hretwf : perceusPrimRetWf name retTy = true)
    (hargswf : perceusPrimArgsWf rf.ctx name as = true)
    (hlive : ∀ a ∈ as, a = .erased ∨ ∃ z v, a = .var z ∧ rf.ctx.get? z = some v ∧ v.isLive = true)
    (hpvs : rf.envP.evalArgs as = some pvs) (hws : rf.envH.evalArgsOwn as = some ws)
    (hsafe : primResSafe name pvs) {pv_res : PVal} (hprim : primP name pvs = some pv_res)
    (hpm : (name == "Array.propagateMark" || name == "ByteArray.propagateMark" ||
        name == "String.propagateMark") = true →
      retTy = LcTy.tobject ∨
        ∃ y vy, as.getLast? = some (LcArg.var y) ∧ rf.ctx.get? y = some vy ∧ vy.ty = LcTy.object)
    {K : HPost} {X : HXPost}
    (hk : ∀ {rw : Word}, ValRep retTy pv_res rw σ.objs →
      (if name == "Array.get!InternalBorrowed" then
         ∃ o_src bv, as[2]? = some (LcArg.var o_src) ∧ rw = Word.i64 bv ∧
           ∃ arrObj pv_arr w_arr, rf.envH o_src = some (pv_arr, w_arr) ∧
             w_arr = Word.i64 arrObj.addr ∧ arrObj ∈ σ.objs ∧
             (bv &&& 1#64 = 0#64 → bv ∈ arrObj.childFields)
       else if (name == "Array.propagateMark" || name == "ByteArray.propagateMark" ||
           name == "String.propagateMark") = true then ws.getLast? = some rw
       else (¬retTy.isScalar → ∃ bv, rw = Word.i64 bv ∧ bv &&& 1#64 ≠ 0#64)) →
      K rw σ) :
    HPrim.wp rt name ws K X σ := by
  have hk_plain : ∀ (hnp : name ≠ "Array.get!InternalBorrowed")
      (hnpm : ¬(name == "Array.propagateMark" || name == "ByteArray.propagateMark" ||
        name == "String.propagateMark") = true) {rw : Word},
      ValRep retTy pv_res rw σ.objs →
      (¬retTy.isScalar → ∃ bv, rw = Word.i64 bv ∧ bv &&& 1#64 ≠ 0#64) → K rw σ := by
    intro hnp hnpm rw hr hodd
    exact hk hr (by
      simp only [beq_false_of_ne hnp, Bool.eq_false_iff.mpr hnpm]
      exact fun hs => hodd hs)
  cases hsp : splitDot name with
  | nil => simp [perceusPrimWf, hsp] at hwf
  | cons s0 rs0 =>
    cases rs0 with
    | nil =>
      exact primReadOnly_sim hvar hwf_objs hwf hretwf hargswf hlive hpvs hws hsafe hprim hpm
        ⟨(fun op heq => by rw [hsp] at heq; cases heq),
         (fun ty op heq => by rw [hsp] at heq; cases heq)⟩ hk
    | cons r1 rs1 =>
      cases rs1 with
      | nil =>
        by_cases hnat : s0 = "Nat"
        · subst hnat
          simp only [primP, hsp] at hprim; simp only [HPrim.wp, hsp]
          refine primNatP_sim_fast hvar hsp hwf hretwf hargswf hlive hpvs hws hsafe hprim ?_
          exact hk_plain (fun h => by rw [h] at hsp; simp [splitDot, splitDot.go] at hsp)
            (fun h => by
              simp only [Bool.or_eq_true, beq_iff_eq] at h
              rcases h with (rfl | rfl) | rfl <;> simp [splitDot, splitDot.go] at hsp)
        · cases hw : uintWidth? s0 with
          | some w =>
            have hne : ∀ (t : String), uintWidth? t = none → s0 ≠ t := fun t ht h => by
              rw [h, ht] at hw; cases hw
            have hnat := hne "Nat" rfl
            have harr := hne "Array" rfl
            have hstr := hne "String" rfl
            have hba := hne "ByteArray" rfl
            have hfl := hne "Float" rfl
            have hch := hne "Char" rfl
            have hint := hne "Int" rfl
            have hi64 := hne "Int64" rfl
            have hoob := hne "outOfBounds" rfl
            have hprim_u : primUintP w r1 pvs = some pv_res := by
              simp only [primP, hsp] at hprim
              split at hprim <;> simp_all
            have huwp : HUintPrimWp rt w r1 ws K σ → HPrim.wp rt name ws K X σ := by
              intro h; simp only [HPrim.wp, hsp]; split <;> simp_all
            refine huwp
              (primUintP_sim hvar hsp hw hwf hretwf hargswf hlive hpvs hws hsafe hprim_u ?_)
            exact hk_plain
              (fun h => by
                rw [h] at hsp
                have hh : ["Array", "get!InternalBorrowed"] = [s0, r1] := by
                  simpa [splitDot, splitDot.go] using hsp
                cases hh; exact harr rfl)
              (fun h => by
                simp only [Bool.or_eq_true, beq_iff_eq] at h
                rcases h with (rfl | rfl) | rfl
                · have hh : ["Array", "propagateMark"] = [s0, r1] := by
                    simpa [splitDot, splitDot.go] using hsp
                  cases hh; exact harr rfl
                · have hh : ["ByteArray", "propagateMark"] = [s0, r1] := by
                    simpa [splitDot, splitDot.go] using hsp
                  cases hh; exact hba rfl
                · have hh : ["String", "propagateMark"] = [s0, r1] := by
                    simpa [splitDot, splitDot.go] using hsp
                  cases hh; exact hstr rfl)
          | none =>
            exact primReadOnly_sim hvar hwf_objs hwf hretwf hargswf hlive hpvs hws hsafe hprim hpm
              ⟨(fun op heq => by rw [hsp] at heq; cases heq; exact hnat rfl),
               (fun ty op heq => by rw [hsp] at heq; cases heq; exact hw)⟩ hk
      | cons r2 rs2 =>
        exact primReadOnly_sim hvar hwf_objs hwf hretwf hargswf hlive hpvs hws hsafe hprim hpm
          ⟨(fun op heq => by rw [hsp] at heq; cases heq),
           (fun ty op heq => by rw [hsp] at heq; cases heq)⟩ hk

end

end LeanQbe.T.LeanLCNF.Sem
